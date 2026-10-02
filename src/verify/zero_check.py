"""Solver-free certificates for the unweighted QuotientOrZero/zero gadget.

Certificates propose syntax matches; check_certificate revalidates input hashes,
the actual equations, witness maps, and bounds. Results cover local constraints
only, never stateful IO or whole-circuit equivalence. See ZERO-CHECK.md.

The pattern, with S = sum(a_i) and T = sum(a_i * v_i), is:

    Before: (1 - cmp) * a_i = 0 for each limb, and T - cmp = 0.
    After:  (1 - cmp) * S = 0, and f * S - cmp = 0.
            The new helper f has recipe QuotientOrZero(cmp, S).

Here a_i are the shared inputs, v_i are the old helpers ("markers"), and
cmp is the selector expression: either a shared column or one minus it.
Bounds must make S = 0 imply that every a_i is zero; arbitrary field values
could cancel. The checker proves each direction with an explicit helper
choice: f := QuotientOrZero(cmp, S) going forward, and every v_i := f backward.

The flow is: find a possible gadget, independently check its certificate,
then attach the checked claims to the caller's remaining obligations.
"""

import json
from copy import deepcopy
from dataclasses import asdict, replace
from hashlib import sha256

from ..lens.loader import machine_of
from .cheap_obligations import cheap_sweep
from .collapsed_witness import add_collapsed_witnesses
from .polynomial_normalization import (
    FIELD_PRIME,
    UnsupportedPolynomial,
    polynomial_key,
)
from .witness_mapping import build_mapping, collect_definitions, live_columns, expression_columns

CONTRACT = "reference-recv-bytes-v1"
SCHEMA = "zero-check-v1"
MAX_LIMBS = 64


class InvalidCertificate(ValueError):
    """A proposed certificate does not justify its claims."""


def fingerprint(value):
    return sha256(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def _sum(expressions):
    # Build an expression in the dump's nested-list syntax, rather than
    # evaluating it. _zero and _weighted build the left sides of zero equations.
    result = 0
    for expr in expressions:
        result = [result, "+", expr]
    return result


def _zero(cmp, expr):
    return [[1, "-", cmp], "*", expr]


def _weighted(limbs, markers, cmp):
    return [_sum([[a, "*", v] for a, v in zip(limbs, markers, strict=True)]), "-", cmp]


def _selector(expr):
    """Return the shared column and polarity for c or 1-c, modulo p."""
    names = expression_columns(expr)
    if len(names) == 1:
        name, = names
        key = polynomial_key(expr)
        if key == polynomial_key(name):
            return name, 'ordinary'
        if key == polynomial_key([1, '-', name]):
            return name, 'opposite'
    raise InvalidCertificate('Expected selector c or 1-c')


def _constant(expr):
    # Normalization can expose constants hidden in expressions like x - x + 8.
    # An empty polynomial is zero; a lone empty monomial is a nonzero constant.
    key = polynomial_key(expr)
    if not key:
        return 0
    if len(key) == 1 and key[0][0] == ():
        return key[0][1]
    return None


def _at(items, index):
    _require(type(index) is int and 0 <= index < len(items), "Invalid source index")
    return items[index]


def _equation(items, index, expected):
    # Compare polynomial values, so expansion and term order do not matter.
    # This does not accept arbitrary scalar multiples of the expected equation.
    _require(
        polynomial_key(_at(items, index)) == polynomial_key(expected),
        f"Equation mismatch at constraint {index}",
    )


def _bound_from_row(bus, column, argument, *, allow_recv_bytes, omit_recv_byte_columns=()):
    """Recognized semantics only; no symbolic guards or inferred assumptions."""
    mult = _constant(bus["mult"])
    args = bus["args"]
    value = _at(args, argument)
    _require(
        polynomial_key(value) == polynomial_key(column),
        "Bound is for another expression",
    )
    if bus["id"] == 3 and len(args) == 2 and argument == 0:
        # A supported active range row [value, width] bounds the canonical
        # field value by 2**width - 1. A symbolic gate cannot promise this always.
        width = _constant(args[1])
        _require(
            mult is not None and mult != 0, "Range row is not unconditionally active"
        )
        _require(width is not None and 0 <= width <= 25, "Unsupported range width")
        return (1 << width) - 1, "openvm-variable-range", None
    if bus["id"] == 1 and len(args) == 7 and 2 <= argument <= 5:
        # Memory payloads count as bytes only under the caller's explicit
        # contract. The row identifies the payload; it does not prove byte-ness.
        # A receive has multiplicity -1, represented as p - 1 in this field.
        _require(allow_recv_bytes, "Receive-byte contract was not authorized")
        _require(column not in omit_recv_byte_columns, 'Receive-byte bound explicitly omitted')
        _require(mult == FIELD_PRIME - 1, "Memory row is not an unconditional receive")
        return 255, CONTRACT, CONTRACT
    raise InvalidCertificate("Unsupported bound source")


def _find_bound(reference, column, allow_recv_bytes, omit_recv_byte_columns=()):
    # Look on the premise side of this proof direction. A bound on the side
    # we are trying to prove would be circular justification.
    choices = []
    for index, bus in enumerate(machine_of(reference).get("bus_interactions", [])):
        arguments = [0] if bus["id"] == 3 else range(2, 6) if bus["id"] == 1 else []
        for argument in arguments:
            try:
                upper, rule, assumption = _bound_from_row(
                    bus, column, argument, allow_recv_bytes=allow_recv_bytes,
                    omit_recv_byte_columns=omit_recv_byte_columns
                )
            except (InvalidCertificate, UnsupportedPolynomial):
                continue
            choices.append(
                {
                    "column": column,
                    "bus": index,
                    "argument": argument,
                    "upper": upper,
                    "rule": rule,
                    "assumption": assumption,
                }
            )
    # Prefer circuit commitments over external assumptions, then tighter bounds.
    return (
        min(choices, key=lambda b: (b["assumption"] is not None, b["upper"], b["bus"]))
        if choices
        else None
    )


def _check_bounds(reference, limbs, evidence, allow_recv_bytes, omit_recv_byte_columns=()):
    _require(
        isinstance(evidence, list) and len(evidence) == len(limbs), "Invalid bound list"
    )
    upper_sum, assumptions = 0, []
    complete = True
    for column, bound in zip(limbs, evidence, strict=True):
        if bound is None:
            complete = False
            continue
        _require(
            isinstance(bound, dict)
            and set(bound)
            == {"column", "bus", "argument", "upper", "rule", "assumption"},
            "Invalid bound record",
        )
        _require(bound["column"] == column, "Bound column mismatch")
        # Re-read the actual row: the certificate's upper bound and assumption
        # labels are claims to verify, not facts we can take on trust.
        bus = _at(machine_of(reference).get("bus_interactions", []), bound["bus"])
        upper, rule, assumption = _bound_from_row(
            bus, column, bound["argument"], allow_recv_bytes=allow_recv_bytes,
            omit_recv_byte_columns=omit_recv_byte_columns
        )
        _require(
            type(bound["upper"]) is int
            and (bound["upper"], bound["rule"], bound["assumption"])
            == (upper, rule, assumption),
            "Bound metadata mismatch",
        )
        upper_sum += upper
        if assumption:
            assumptions.append(bound)
    # Every canonical limb is nonnegative. If their largest possible sum is
    # below p, a zero field sum cannot hide a nonzero integer multiple of p.
    # One missing bound is enough to make that argument unavailable.
    return complete and upper_sum < FIELD_PRIME, upper_sum, assumptions


def _keys(constraints):
    """Index each supported polynomial by its first constraint position."""
    out = {}
    for index, expr in enumerate(constraints):
        try:
            out.setdefault(polynomial_key(expr), index)
        except UnsupportedPolynomial:
            continue
    return out


def propose_certificates(before, after, mapping, direction, *, allow_recv_bytes=False,
                         omit_recv_byte_columns=()):
    """Find possible gadgets and record enough evidence to check them later.

    Start from a new quotient helper, read its denominator to identify the
    limbs, then find the matching zero and weighted equations. A certificate
    records their positions and variable roles, plus any available bounds.
    This search never proves an obligation; check_certificate does that work.
    """
    _require(direction in ("completeness", "soundness"), "Unknown direction")
    bm, am = machine_of(before), machine_of(after)
    bk = ak = None  # Build polynomial indices only for a plausible introduced helper.
    definitions = collect_definitions(am.get("derived_columns", []))
    # Before/After always mean optimizer order. Reference/candidate mean the
    # premise/goal sides of the current proof, so they swap for soundness.
    # In either direction we want helpers introduced by the optimization.
    introduced = (
        mapping.candidate_columns - mapping.reference_columns
        if direction == "completeness"
        else mapping.reference_columns - mapping.candidate_columns
    )
    reference = before if direction == "completeness" else after
    proposals = []
    for definition, record in enumerate(am.get("derived_columns", [])):
        _, f, recipe = record
        # Use the recipe as a search hint. Restrict the search to a new helper
        # with one unambiguous QuotientOrZero definition.
        if (
            f not in introduced
            or len(definitions[f]) != 1
            or not isinstance(recipe, dict)
            or set(recipe) != {"QuotientOrZero"}
        ):
            continue
        if (
            not isinstance(recipe["QuotientOrZero"], list)
            or len(recipe["QuotientOrZero"]) != 2
        ):
            continue
        cmp, denominator = recipe["QuotientOrZero"]
        try:
            _selector(cmp)
            sk = polynomial_key(denominator)
            # A key consists of (monomial, coefficient) pairs. Requiring one
            # variable per monomial and coefficient 1 gives S = a0 + a1 + ...,
            # with distinct limbs and no constants, weights, or products.
            if not 2 <= len(sk) <= MAX_LIMBS or any(
                len(term) != 1 or coefficient != 1 for term, coefficient in sk
            ):
                continue
            limbs = [term[0] for term, _ in sk]
            if bk is None:
                bk, ak = _keys(bm["constraints"]), _keys(am["constraints"])
            # Find After's f*S-cmp and (1-cmp)*S, and Before's (1-cmp)*a_i.
            # Looking up polynomial keys also finds expanded/reordered forms.
            new_weighted = ak.get(polynomial_key([[f, "*", _sum(limbs)], "-", cmp]))
            new_zero = ak.get(polynomial_key(_zero(cmp, _sum(limbs))))
            old_zero = [bk.get(polynomial_key(_zero(cmp, a))) for a in limbs]
            if new_weighted is None or new_zero is None or None in old_zero:
                continue
            for key, old_weighted in bk.items():
                # We do not know the old helpers yet. Try each old equation:
                # adding cmp to T-cmp should leave exactly one a_i*v_i term
                # per limb. The other factor in each term is its marker v_i.
                terms = dict(polynomial_key([bm['constraints'][old_weighted], '+', cmp]))
                if len(terms) != len(limbs):
                    continue
                markers = []
                for a in limbs:
                    matching = [
                        term
                        for term, coefficient in terms.items()
                        if coefficient == 1 and len(term) == 2 and term.count(a) == 1
                    ]
                    if len(matching) != 1:
                        break
                    markers.append(next(v for v in matching[0] if v != a))
                if len(markers) != len(limbs):
                    continue
                # Keep source positions for independent replay. Hashes bind
                # the proposal to these inputs and this particular witness map.
                # Missing bounds remain None; they are never invented here.
                proposals.append(
                    {
                        "schema": SCHEMA,
                        "field": FIELD_PRIME,
                        "direction": direction,
                        "before": fingerprint(before),
                        "after": fingerprint(after),
                        "mapping": fingerprint(mapping.witnesses),
                        "limbs": limbs,
                        "markers": markers,
                        "cmp": cmp,
                        "f": f,
                        "definition": definition,
                        "old_weighted": old_weighted,
                        "old_zero": old_zero,
                        "new_weighted": new_weighted,
                        "new_zero": new_zero,
                        "bounds": [
                            _find_bound(reference, a, allow_recv_bytes, omit_recv_byte_columns) for a in limbs
                        ],
                    }
                )
        except (UnsupportedPolynomial, InvalidCertificate):
            # An unsupported expression or exhausted polynomial budget means
            # this search found no usable proposal, not that the gadget is valid.
            continue
    return proposals


def check_certificate(before, after, mapping, certificate, *, allow_recv_bytes=False,
                      require_complete_gadget=False, omit_recv_byte_columns=()):
    """Recheck a proposed certificate; return ONLY individually justified claims.

    No calls to the recognizer. Missing/no-wrap bounds leave the conditional
    rules unavailable, while unconditional polynomial rules may still apply.
    Authorization for external assumptions comes from the caller, not the file.
    """
    c = certificate
    # Here c is the certificate dictionary; cmp below is the gadget selector.
    _require(
        isinstance(c, dict)
        and set(c)
        == {
            "schema",
            "field",
            "direction",
            "before",
            "after",
            "mapping",
            "limbs",
            "markers",
            "cmp",
            "f",
            "definition",
            "old_weighted",
            "old_zero",
            "new_weighted",
            "new_zero",
            "bounds",
        },
        "Invalid certificate schema",
    )
    _require(
        c["schema"] == SCHEMA and type(c["field"]) is int and c["field"] == FIELD_PRIME,
        "Unsupported schema or field",
    )
    _require(c["direction"] in ("completeness", "soundness"), "Unknown direction")
    # A certificate from a different dump or helper mapping cannot be replayed
    # against these inputs, even if its constraint indices happen to exist.
    _require(
        c["before"] == fingerprint(before) and c["after"] == fingerprint(after),
        "Input hash mismatch",
    )
    _require(c["mapping"] == fingerprint(mapping.witnesses), "Mapping hash mismatch")
    forward = c["direction"] == "completeness"
    ref, cand = (before, after) if forward else (after, before)
    _require(
        mapping.total
        and mapping.reference_columns == live_columns(ref)
        and mapping.candidate_columns == live_columns(cand),
        "Invalid mapping domain",
    )
    a, v, cmp, f = c["limbs"], c["markers"], c["cmp"], c["f"]
    selector, polarity = _selector(cmp)
    _require(
        isinstance(a, list)
        and isinstance(v, list)
        and 2 <= len(a) <= MAX_LIMBS
        and len(a) == len(v),
        "Invalid gadget arity",
    )
    roles = a + v + [selector, f]
    # The proof assumes distinct roles: inputs cannot double as helpers, the
    # old helpers disappear, and the new helper was not already present.
    _require(
        all(isinstance(n, str) and "@" in n for n in roles)
        and len(set(roles)) == len(roles),
        "Variable roles must be distinct columns",
    )
    before_live, after_live = live_columns(before), live_columns(after)
    _require(set(a + [selector]) <= before_live & after_live, "Shared columns missing")
    _require(
        set(v) <= before_live - after_live and f in after_live - before_live,
        "Expected removed markers and introduced quotient column",
    )
    bm, am = machine_of(before), machine_of(after)
    # Check the recipe's shape separately from its polynomial arguments.
    # polynomial_key does not evaluate QuotientOrZero or justify division.
    defs = collect_definitions(am.get("derived_columns", []))
    record = _at(am.get("derived_columns", []), c["definition"])
    _require(record[1] == f and len(defs[f]) == 1, "Ambiguous quotient definition")
    recipe = record[2]
    _require(
        isinstance(recipe, dict)
        and set(recipe) == {"QuotientOrZero"}
        and isinstance(recipe["QuotientOrZero"], list)
        and len(recipe["QuotientOrZero"]) == 2,
        "Expected QuotientOrZero recipe",
    )
    numerator, denominator = recipe["QuotientOrZero"]
    _require(
        polynomial_key(numerator) == polynomial_key(cmp)
        and polynomial_key(denominator) == polynomial_key(_sum(a)),
        "Wrong quotient recipe",
    )
    _require(
        isinstance(c["old_zero"], list) and len(c["old_zero"]) == len(a),
        "Invalid zero equation list",
    )
    # Recheck every claimed equation directly, without rerunning the search.
    for limb, index in zip(a, c["old_zero"], strict=True):
        _equation(bm["constraints"], index, _zero(cmp, limb))
    _equation(bm["constraints"], c["old_weighted"], _weighted(a, v, cmp))
    _equation(am["constraints"], c["new_zero"], _zero(cmp, _sum(a)))
    _equation(am["constraints"], c["new_weighted"], [[f, "*", _sum(a)], "-", cmp])
    # The theorem keeps the inputs and selector fixed. It only chooses values
    # for the destination's helpers, using the caller's existing witness map.
    for shared in a + [selector]:
        _require(
            polynomial_key(mapping.witnesses[shared]) == polynomial_key(shared),
            "Gadget requires identity mapping of shared columns",
        )
    if forward:
        # Before -> After: construct the new helper as QuotientOrZero(cmp, S).
        witness = mapping.witnesses[f]
        _require(
            isinstance(witness, dict)
            and set(witness) == {"QuotientOrZero"}
            and isinstance(witness["QuotientOrZero"], list)
            and len(witness["QuotientOrZero"]) == 2,
            "Wrong forward witness",
        )
        n, d = witness["QuotientOrZero"]
        _require(
            polynomial_key(n) == polynomial_key(cmp)
            and polynomial_key(d) == polynomial_key(_sum(a)),
            "Wrong forward witness arguments",
        )
    else:
        # After -> Before: reconstruct every removed helper with the same f.
        for marker in v:
            _require(
                polynomial_key(mapping.witnesses[marker]) == polynomial_key(f),
                "Wrong reverse witness",
            )

    bounded, upper_sum, assumptions = _check_bounds(
        ref, a, c["bounds"], allow_recv_bytes, omit_recv_byte_columns
    )
    # M4b requires the whole gadget and its no-wrap side condition. Metadata
    # recipes are hints, not commitments; count occurrences in constraints and
    # bus fields, including multiplicities, but not dead recipe records.
    exclusive = all(not (expression_columns(e) & set(v))
                    for i, e in enumerate(bm['constraints']) if i != c['old_weighted'])
    exclusive = exclusive and all(
        not (expression_columns(e) & set(v))
        for b in bm.get('bus_interactions', []) for e in [b['mult'], *b['args']])
    if require_complete_gadget and (not bounded or not exclusive):
        # M4b accepts the complete gadget or leaves it for later checking.
        # Legacy M3 may still use individual identities when bounds are missing.
        return {'claims': [], 'no_cancellation': bounded, 'upper_sum': upper_sum,
                'bound_reason': 'M4b requires no-wrap bounds and exclusive markers',
                'exclusive_markers': exclusive, 'theorems': []}
    claims = []

    def claim(index, rule, conditional=False):
        # Only rules that need bounds inherit their external assumptions.
        # Direct range evidence can justify such a rule with no assumptions.
        claims.append(
            {
                "kind": "algebraic",
                "index": index,
                "rule": rule,
                "assumptions": deepcopy(assumptions) if conditional else [],
            }
        )

    if forward:
        # Summing the old zero equations gives the new zero equation.
        _require(
            polynomial_key(_sum([bm["constraints"][i] for i in c["old_zero"]]))
            == polynomial_key(am["constraints"][c["new_zero"]]),
            "Sum identity failed",
        )
        claim(c["new_zero"], "sum-individual-zero-equations")
        if bounded:
            # If S is nonzero, the quotient gives f*S = cmp. If S is zero,
            # the bounds force every a_i to zero; T-cmp = 0 then forces cmp = 0.
            # QuotientOrZero returns zero in that case, so f*S = cmp still holds.
            claim(c["new_weighted"], "quotient-product-with-no-cancellation", True)
    else:
        # Substitute v_i := f into the old weighted equation. Distributing
        # f across the sum must give exactly After's f*S-cmp polynomial.
        _require(
            polynomial_key(bm["constraints"][c["old_weighted"]], mapping.witnesses)
            == polynomial_key(am["constraints"][c["new_weighted"]]),
            "Collapse identity failed",
        )
        claim(c["old_weighted"], "uniform-witness-polynomial-identity")
        if bounded:
            # From (1-cmp)*S = 0, either cmp = 1 (each old product is zero)
            # or S = 0 (the bounds force every limb to zero). Neither branch
            # needs a separate Booleanity assumption for cmp.
            for index in c["old_zero"]:
                claim(index, "split-zero-sum-with-no-cancellation", True)
    # Record the corresponding theorem names for traceability. This Python
    # checker does not invoke Lean when accepting a certificate.
    theorems = ['IsZeroGadget.after_of_before_derived' if forward
                else 'IsZeroGadget.before_of_after_skolem',
                'IsZeroGadget.noWrap_of_val_sum_lt'] if bounded else []
    if theorems and polarity == 'opposite':
        theorems += ['IsZeroGadget.before_neg_polarity', 'IsZeroGadget.after_neg_polarity']
    return {
        "claims": claims,
        "no_cancellation": bounded,
        "upper_sum": upper_sum,
        "exclusive_markers": exclusive,
        "theorems": theorems,
        "bound_reason": None
        if bounded
        else "Missing bounds or upper sum is not below the field prime",
    }


def syntactic_sweep(
    before, after, direction, substitutions=(), *, allow_recv_bytes=False
):
    """M2/M3 plus independently checked gadget rules, with explicit residuals."""
    _require(direction in ("completeness", "soundness"), "Unknown direction")
    ref, cand = (before, after) if direction == "completeness" else (after, before)
    # First choose witnesses, including a possible uniform marker collapse.
    # A total mapping supplies values to try; it does not prove their equations.
    mapping, proposals = add_collapsed_witnesses(
        ref, cand, build_mapping(ref, cand, substitutions)
    )
    base = {
        "direction": direction,
        "field": FIELD_PRIME,
        "solver_calls": 0,
        "scope": "local algebraic and stateless obligations; no IO or general derived-definition audit",
        "inputs": {"before": fingerprint(before), "after": fingerprint(after)},
        "authorized_contracts": [CONTRACT] if allow_recv_bytes else [],
        "mapping": {
            "total": mapping.total,
            "witnesses": mapping.witnesses,
            "sources": mapping.sources,
            "unresolved": mapping.unresolved,
        },
        "mapping_proposals": proposals,
        "omitted_stateful": {
            "reference": sum(
                b["id"] in (0, 1) for b in machine_of(ref).get("bus_interactions", [])
            ),
            "candidate": sum(
                b["id"] in (0, 1) for b in machine_of(cand).get("bus_interactions", [])
            ),
        },
    }
    if not mapping.total:
        # Without all witnesses we cannot enumerate the mapped obligations.
        # None means unknown, whereas an empty residual list would mean closed.
        return base | {
            "status": "unmapped",
            "initial_residuals": None,
            "residuals": None,
            "certificates": [],
            "obligations": [],
        }
    obligations = cheap_sweep(ref, cand, mapping)
    # Preserve the baseline so the report shows exactly what this checker adds.
    initial = [(o.kind, o.index) for o in obligations if o.status == "residual"]
    obligations, evidence = discharge_zero_checks(
        before,
        after,
        mapping,
        direction,
        obligations,
        allow_recv_bytes=allow_recv_bytes,
    )
    residuals = [(o.kind, o.index) for o in obligations if o.status == "residual"]
    status = (
        "residual"
        if residuals
        else "conditional-local-closed"
        if evidence["assumptions"]
        else "local-closed"
    )
    return (
        base
        | evidence
        | {
            "status": status,
            "initial_residuals": initial,
            "residuals": residuals,
            "obligations": [asdict(o) for o in obligations],
        }
    )


def discharge_zero_checks(
    before, after, mapping, direction, obligations, *, allow_recv_bytes=False,
    require_complete_gadget=False, omit_recv_byte_columns=()
):
    """Shared post-M3 discharge using the caller's mapping, never rebuilding it.

    Internal adapter: obligations must come from cheap_sweep for these inputs
    and mapping. Returns a new list; retains per-obligation certificate evidence.
    """
    obligations = list(obligations)
    certificates, checked, rejected = [], {}, []
    # Gadget rules only discharge algebraic residuals. Avoid scanning recipes
    # when there is no remaining obligation they could help with.
    if not any(o.kind == "algebraic" and o.status == "residual" for o in obligations):
        return obligations, {
            "certificates": [],
            "proof_uses": [],
            "assumptions": [],
            "rejected_proposals": [],
        }
    for cert in propose_certificates(
        before, after, mapping, direction, allow_recv_bytes=allow_recv_bytes,
        omit_recv_byte_columns=omit_recv_byte_columns
    ):
        try:
            result = check_certificate(
                before, after, mapping, cert, allow_recv_bytes=allow_recv_bytes,
                require_complete_gadget=require_complete_gadget,
                omit_recv_byte_columns=omit_recv_byte_columns
            )
        except (InvalidCertificate, UnsupportedPolynomial) as error:
            rejected.append(str(error))
            continue
        cid = len(certificates)
        certificates.append({"certificate": cert, "checked": result})
        # A claim names a specific obligation. If several certificates justify
        # it, keeping the first checked one is enough to attach a proof.
        for claim in result["claims"]:
            checked.setdefault((claim["kind"], claim["index"]), (cid, claim))
    used, assumptions = [], []
    for index, obligation in enumerate(obligations):
        proof = checked.get((obligation.kind, obligation.index))
        # Leave unrelated goals and earlier proofs intact, including definition
        # goals. Finding one valid gadget does not close the rest of the circuit.
        if obligation.status != "residual" or proof is None:
            continue
        cid, claim = proof
        obligations[index] = replace(
            obligation,
            status="discharged",
            reason=claim["rule"],
            proof=deepcopy(
                {"certificate": certificates[cid]["certificate"], "claim": claim,
                 "theorems": certificates[cid]['checked']['theorems'],
                 "require_complete_gadget": require_complete_gadget}
            ),
        )
        used.append(
            {"kind": obligation.kind, "index": obligation.index, "certificate": cid}
        )
        for assumption in claim["assumptions"]:
            # Report assumptions used by actual discharges, not every bound
            # found while searching for possible gadgets.
            if assumption not in assumptions:
                assumptions.append(assumption)
    return obligations, {
        "certificates": certificates,
        "proof_uses": used,
        "assumptions": assumptions,
        "rejected_proposals": rejected,
    }
