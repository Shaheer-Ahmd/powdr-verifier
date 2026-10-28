"""Step B: one obligation per candidate constraint or stateless interaction.

For a candidate constraint c the obligation is c[w]: it must follow from the
reference side's constraints and byte ranges. The rungs, cheapest first:

  trivial    - c[w] is identically zero (canonical key is empty)
  identical  - c[w] has the same canonical key as a reference constraint
  normalize / nowrap-split - PolySolver proves it
  undecided  - nothing applied; left for the SMT rungs (not built yet)

A stateless bus interaction (a lookup) is the fact "mult != 0 => args in
table", where the table is an uninterpreted predicate. Its obligation I[w]:

  trivial    - mult[w] is zero, so the lookup asserts nothing
  identical  - the reference has an interaction with the same bus, mult and
               args (lens's _bus_exact_key), so it already asserts this fact
  evaluated  - every argument is a constant (under the mapping and the solved
               equations) and the tuple is a table row (tables.is_row); the
               only rung that uses what a table contains. PcLookup is not
               evaluated (not trusted)
  congruence - a reference interaction J on the same bus with PolySolver
               proving mult_I = mult_J and arg_I,k = arg_J,k for every k: by
               congruence, J's fact gives I's. J is proposed by an index on
               PolySolver's normal forms (untrusted search); only the
               implies_equal verdicts decide

Results are cached by canonical key. A direction is verified only if no
obligation is undecided. Stateful buses (memory, execution bridge) are not
checked yet, so "verified" is not yet "equivalent".
"""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field, replace

from src.lens.canon import CanonError, canon_value, canon_zero
from src.lens.diff import _bus_exact_key
from src.polysolver import (
    BABYBEAR,
    Expr,
    Implied,
    Opaque,
    PolySolver,
    UndefinedVariable,
    VarTable,
    poly,
    variables,
)

from .adapter import HINT_TAG
from .circuit import Circuit, interaction_columns, substitute, substitute_interaction
from .mapping import Mapping
from .tables import is_row

PC_LOOKUP = 2  # its table is the program: never evaluated (not trusted)

# Rungs that prove an obligation; anything else is "undecided".
DISCHARGED = (
    "trivial",
    "identical",
    "normalize",
    "nowrap-split",
    "evaluated",
    "congruence",
)


@dataclass(frozen=True)
class Obligation:
    """The verdict for one candidate constraint or interaction under the mapping."""

    # "<label>:c<i>" (constraint), "<label>:b<i>" (i-th stateless interaction),
    # or "<column>:def<i>" for an extra definition.
    name: str
    rung: str  # one of DISCHARGED, or "undecided"
    detail: str = ""  # premises used, or why it is undecided
    cached: bool = False  # answered from an identical earlier obligation
    # Undecided only: a short, fixed category (see REASONS).
    reason: str = ""
    # True if c mentions a column defined by the mapping, so c[w] differs from c.
    via_mapping: bool = False
    kind: str = "constraint"  # or "bus" for a stateless bus interaction
    # Canonical key of c[w] (or I[w]); None if an opaque or unmapped column
    # kept the canonical rungs from writing it out. For grouping in reports.
    key: tuple | None = field(default=None, compare=False, repr=False)


# Why an obligation can stay undecided. Fixed strings, so reports can group them.
REASONS = {
    "unmapped column": "mentions a column the mapping could not define",
    "mapping gap": "mentions a column that is neither shared nor defined",
    "opaque QuotientOrZero": "needs the meaning of a QuotientOrZero column",
    "opaque IfEqZero": "needs the meaning of an IfEqZero column",
    "opaque other": "needs the meaning of a non-polynomial derived column",
    "opaque extra definition": "a second, non-polynomial definition of a column",
    "near miss: range missing": "rule S fits, but a summand has no range",
    "near miss: sum may wrap": "rule S fits, but the ranges are too wide",
    "nonzero constant": "c[w] is a nonzero constant: only contradictory premises imply it",
    "expansion limit": "too many terms to expand",
    "bus-only columns": "mentions a column the reference constrains only via"
    " bus interactions; likely needs bus facts (Step C)",
    "linear, no match": "linear; may follow from a combination of reference"
    " constraints (elimination rule not built)",
    "nonlinear, no match": "nonlinear; needs several premises or SMT",
    # Stateless bus interactions (canonical rungs only, so far).
    "lookup-only column": "mentions a candidate column used only by lookups, with"
    " no definition (e.g. a dropped range check); needs table semantics",
    "bus: no same-mult reference": "no reference interaction on this bus has the"
    " same multiplicity",
    "bus: args differ": "reference interactions with this bus and multiplicity"
    " exist, but none has the same args",
    "bus: not canonical": "lens could not canonicalize the interaction",
    "bus: constant args not a row": "every argument is a constant and the tuple is"
    " not a table row: a real failure if the multiplicity can be nonzero",
    "bus: pc_lookup not trusted": "a program-counter lookup with constant"
    " arguments; its table is the program, which the redesign does not evaluate",
}


@dataclass
class Report:
    """All obligations of one step in one direction."""

    direction: str
    mapping: Mapping
    obligations: list[Obligation] = field(default_factory=list)
    premises_expanded: int = 0  # premise keys PolySolver computed (rule N)
    premises_split: int = 0  # premises PolySolver split into factors (rule S)
    hints_accepted: int = 0  # solved equations PolySolver checked and kept
    hints_agreed: int = 0  # of those, equal to a value x already had (a pin): no substitution
    hints_rejected: int = 0  # hints whose check failed (not used)
    constants_solved: int = 0  # variables pinned by a premise x - c (derive)
    pinned: int = 0  # variables pinned otherwise: booleanity, groups, selectors (derive)
    pinned_after_hints: int = 0  # of both, those pinned by the run after the hints
    case_splits: int = 0  # groups rule C searched (derive)
    case_split_nodes: int = 0  # values it tried
    case_split_capped: int = 0  # groups or searches it gave up on (over a cap)
    case_split_ms: int = 0  # its own time
    # powdr's hints, in the order tried: (column, accepted, agreed with x's
    # value, rule or reject kind, note, form of t: hint_form).
    hints: list[tuple[str, bool, bool, str, str, str | None]] = field(default_factory=list)

    @property
    def verified(self) -> bool:
        """Every obligation discharged and every column mapped (stateful buses not checked)."""
        return (
            all(o.rung in DISCHARGED for o in self.obligations)
            and not self.mapping.unmapped
        )

    def counts(self, kind: str | None = None) -> Counter:
        """Counts by rung, for one kind of obligation or all of them."""
        return Counter(o.rung for o in self.obligations if kind in (None, o.kind))

    def categories(self) -> Counter:
        """Counts by (kind, rung, subcategory)."""
        return Counter(category(o) for o in self.obligations)


def category(o: Obligation) -> tuple[str, str, str]:
    """(kind, rung, subcategory): the undecided reason, or whether the mapping was used."""
    if o.rung == "undecided":
        return o.kind, o.rung, o.reason
    if o.rung == "trivial":
        return o.kind, o.rung, ""
    return o.kind, o.rung, "via mapping" if o.via_mapping else "direct"


def sweep(
    direction: str,
    ref: Circuit,
    cand: Circuit,
    mapping: Mapping,
    solver: PolySolver,
    hints: list[tuple[str, Expr]] = (),
) -> Report:
    """Check every candidate constraint against the reference under ``mapping``.

    ``hints`` are the ones the solver was given, for their forms in the report.
    """
    report = Report(direction, mapping)
    defs = solver.make_defs(mapping.defs)
    # Polynomial definitions can be written into c to get c[w] for the
    # canonical rungs. Opaque or unmapped columns cannot, so they skip to PolySolver.
    poly_defs = {c: d for c, d in mapping.defs.items() if not isinstance(d, Opaque)}
    blocked = mapping.unmapped | {
        c for c, d in mapping.defs.items() if isinstance(d, Opaque)
    }
    # Canonical keys of the reference constraints, for the "identical" rung.
    ref_keys = {_key(c) for c in ref.constraints} - {None}
    # Reference columns that no reference constraint mentions: only buses touch them.
    in_constraints = (
        set().union(*map(variables, ref.constraints)) if ref.constraints else set()
    )
    bus_only = ref.columns - in_constraints
    cache: dict = {}  # canonical key of c[w] -> its verdict

    def check(name: str, c: Expr) -> Obligation:
        """Run one obligation up the ladder, cheapest rung first."""
        cols = variables(c)
        mapped = bool(cols & mapping.defs.keys())
        # No witness for some column: nothing to prove it with.
        if cols & mapping.unmapped:
            missing = ", ".join(sorted(cols & mapping.unmapped))
            return Obligation(
                name, "undecided", f"unmapped: {missing}", reason="unmapped column"
            )
        key = None
        if not cols & blocked:  # canonical rungs need c[w] written out
            key = _key(substitute(c, poly_defs))
            # Rung 0: the same obligation was already decided in this step.
            if key is not None and key in cache:
                return replace(cache[key], name=name, cached=True, via_mapping=mapped)
            # Rung 1: c[w] is identically zero, e.g. a leftover literal 0.
            if key == ():
                return _remember(cache, key, Obligation(name, "trivial"))
            # Rung 2: the reference has this very constraint (up to spelling).
            if key in ref_keys:
                ob = Obligation(name, "identical", via_mapping=mapped)
                return _remember(cache, key, ob)
        # PolySolver rung. It takes c and the definitions, not c[w]: it
        # expands the definitions itself and also handles opaque columns.
        try:
            v = solver.implies(c, defs)
        except UndefinedVariable as exc:
            return Obligation(
                name, "undecided", str(exc), reason="mapping gap", key=key
            )
        if isinstance(v, Implied):
            detail = ", ".join(
                v.premises
                + tuple(f"range {r}" for r in v.ranges)
                + tuple(f"solved {t}" for t in v.solved)
            )
            ob = Obligation(name, v.rule, detail, via_mapping=mapped)
            return _remember(cache, key, ob)
        # Undecided: record why, so reports can group these.
        reason = _reason(v.kind, cols, mapping)
        if reason == "no single premise":
            reason = _no_match_reason(substitute(c, poly_defs), bus_only)
        ob = Obligation(name, "undecided", v.note, reason=reason, via_mapping=mapped)
        return _remember(cache, key, ob)

    # Reference lookups, for the bus "identical" rung, and their (bus, mult)
    # pairs, to tell "args differ" from "no same-mult reference" when undecided.
    ref_bus_keys, ref_bus_mults = set(), set()
    for r in ref.stateless:
        try:
            ref_bus_keys.add(_bus_exact_key(r))
            ref_bus_mults.add((r["id"], canon_value(r["mult"])))
        except CanonError:
            pass  # cannot be matched; costs completeness only
    bus_cache: dict = {}  # canonical key of I[w] -> its verdict
    # Untrusted index for the congruence rung: reference lookups by their normal
    # form under the solved equations. It only proposes a J; implies_equal decides.
    ref_index: dict = {}
    for j, r in enumerate(ref.stateless):
        k = _normal_key(solver, r)
        if k is not None:
            ref_index.setdefault(k, (j, r))

    def check_bus(name: str, bi: dict) -> Obligation:
        """Discharge one stateless interaction by canonical matching."""
        cols = interaction_columns(bi)
        mapped = bool(cols & mapping.defs.keys())
        missing = cols & mapping.unmapped
        if missing:
            lookup_only = all(
                mapping.unmapped_reason.get(c) == "lookup-only" for c in missing
            )
            reason = "lookup-only column" if lookup_only else "unmapped column"
            detail = "unmapped: " + ", ".join(sorted(missing))
            return Obligation(name, "undecided", detail, reason=reason, kind="bus")
        # Opaque columns cannot be written into I, so there is no I[w] to match.
        opaque = cols & blocked
        if opaque:
            detail = "opaque: " + ", ".join(sorted(opaque))
            reason = _reason("opaque", cols, mapping)
            return Obligation(name, "undecided", detail, reason=reason, kind="bus")
        bw = substitute_interaction(bi, poly_defs)
        try:
            key, mult = _bus_exact_key(bw), canon_value(bw["mult"])
        except CanonError as exc:
            return Obligation(
                name, "undecided", str(exc), reason="bus: not canonical", kind="bus"
            )
        # Rung 0: the same interaction was already decided in this step.
        if key in bus_cache:
            return replace(bus_cache[key], name=name, cached=True, via_mapping=mapped)
        if mult == ():
            # Rung 1: multiplicity 0, so the lookup asserts nothing.
            ob = Obligation(name, "trivial", "multiplicity is 0", kind="bus")
        elif key in ref_bus_keys:
            # Rung 2: the reference asserts this very fact (same bus, mult, args).
            ob = Obligation(name, "identical", via_mapping=mapped, kind="bus")
        else:
            ob = _by_tables_or_congruence(name, bi, defs, solver, ref, ref_index, mapped)
            if ob is None:
                same_mult = (bw["id"], mult) in ref_bus_mults
                reason = (
                    "bus: args differ" if same_mult else "bus: no same-mult reference"
                )
                ob = Obligation(
                    name,
                    "undecided",
                    f"bus {bw['id']}",
                    reason=reason,
                    via_mapping=mapped,
                    kind="bus",
                )
        ob = replace(ob, key=key)
        bus_cache[key] = ob
        return ob

    for i, c in enumerate(cand.constraints):
        report.obligations.append(check(f"{cand.label}:c{i}", c))
    for i, bi in enumerate(cand.stateless):
        report.obligations.append(check_bus(f"{cand.label}:b{i}", bi))
    
    report.premises_expanded = solver.premises_expanded
    report.premises_split = solver.premises_split
    report.constants_solved = solver.constants_solved
    report.pinned = solver.pinned
    report.pinned_after_hints = sum(solver.derive_pins[1:])
    report.case_splits = solver.case_splits
    report.case_split_nodes = solver.case_split_nodes
    report.case_split_capped = solver.case_split_capped
    report.case_split_ms = round(solver.case_split_seconds * 1000)
    report.hints_accepted = solver.solved_accepted
    report.hints_rejected = solver.solved_rejected
    forms = {x: hint_form(t) for x, t in hints}
    report.hints = [
        (
            tag.removeprefix(HINT_TAG),
            isinstance(v, Implied),
            agreed,
            v.rule if isinstance(v, Implied) else v.kind,
            "" if isinstance(v, Implied) else v.note,
            forms.get(tag.removeprefix(HINT_TAG)),
        )
        for tag, v, agreed in solver.solved_log
        if tag.startswith(HINT_TAG)
    ]
    report.hints_agreed = sum(h[2] for h in report.hints)
    return report


def hint_form(t: Expr) -> str:
    """The form of a hint's value t; y is a column, a and c are constants.

    t is expanded as written, without the solved equations, so a hint's form
    is the same in every run.

    "c" (x := 5), "y" (x := y), "y + c" (x := y - 4), "a*y + c" (x := 256*y),
    "linear" (two or more columns, x := y + 256*z) or "nonlinear".
    """
    table = VarTable()
    try:
        t = poly.expand(t, lambda n: poly.var_poly(table.var(n)), BABYBEAR)
    except poly.ExpansionLimit:  # thousands of terms: never linear in practice
        return "nonlinear"
    monos = [m for m in t if m]
    if not monos:
        return "c"
    if any(poly.degree(m) > 1 for m in monos):
        return "nonlinear"
    if len(monos) > 1:
        return "linear"
    if t[monos[0]] != 1:
        return "a*y + c"
    return "y + c" if () in t else "y"


def _normal_key(solver: PolySolver, bi: dict, defs=None) -> tuple | None:
    """(bus, mult, args) in PolySolver's normal form, for the untrusted index."""
    nf = [
        solver.normal_form(e, defs) if defs is not None else solver.normal_form(e)
        for e in [bi["mult"], *bi["args"]]
    ]
    if any(x is None for x in nf):
        return None
    return (bi["id"], nf[0], tuple(nf[1:]))


def _constant(nf: tuple) -> int | None:
    """The value of a normal form with no variables, else None."""
    if not nf:
        return 0
    if len(nf) == 1 and nf[0][0] == ():
        return nf[0][1]
    return None


def _by_tables_or_congruence(
    name: str,
    bi: dict,
    defs,
    solver: PolySolver,
    ref: Circuit,
    ref_index: dict,
    mapped: bool,
) -> Obligation | None:
    """The evaluated and congruence rungs for one lookup; None if neither applies."""
    key = _normal_key(solver, bi, defs)
    if key is None:
        return None
    bus, _, args = key
    values = [_constant(a) for a in args]
    constant = all(v is not None for v in values)
    if constant and bus != PC_LOOKUP:
        # Rung 3: constant arguments. Decide by the table, whatever the mult is:
        # a row makes "mult != 0 => row" true outright. PcLookup is never
        # evaluated (its table is the program); congruence below needs no table.
        row = is_row(bus, values)
        if row:
            return Obligation(name, "evaluated", f"bus {bus} row {values}",
                              via_mapping=mapped, kind="bus")
        if row is False:
            return Obligation(
                name, "undecided", f"bus {bus} {values}",
                reason="bus: constant args not a row", via_mapping=mapped, kind="bus",
            )
    # Rung 4: congruence with a reference lookup J proposed by the index.
    ob = _congruence(name, bi, defs, solver, ref, ref_index.get(key), mapped)
    if ob is None and constant and bus == PC_LOOKUP:
        return Obligation(
            name, "undecided", "pc_lookup", reason="bus: pc_lookup not trusted",
            via_mapping=mapped, kind="bus",
        )
    return ob


def _congruence(name, bi, defs, solver, ref, found, mapped) -> Obligation | None:
    """I follows from the proposed J if PolySolver proves mult and every arg equal."""
    if found is None:
        return None
    j, J = found
    used = set()
    for x, y in zip([bi["mult"], *bi["args"]], [J["mult"], *J["args"]]):
        v = solver.implies_equal(x, y, defs)
        if not isinstance(v, Implied):
            return None
        used.update(v.premises)
        used.update(f"solved {t}" for t in v.solved)
    detail = ", ".join([f"{ref.label}:b{j}", *sorted(used)])
    return Obligation(name, "congruence", detail, via_mapping=mapped, kind="bus")


# PolySolver's Unknown.kind -> our reason label. "no single premise" is a
# placeholder that ``_no_match_reason`` refines.
_KIND_REASON = {
    "expansion-limit": "expansion limit",
    "nonzero-constant": "nonzero constant",
    "nowrap-missing-range": "near miss: range missing",
    "nowrap-bound": "near miss: sum may wrap",
    "no-match": "no single premise",
}


def _reason(kind: str, cols: set[str], mapping: Mapping) -> str:
    """Turn PolySolver's Unknown.kind into one of REASONS."""
    if kind != "opaque":
        return _KIND_REASON[kind]
    # Name the kind of recipe hiding behind the opaque column(s).
    kinds = set()
    for c in cols:
        d = mapping.defs.get(c)
        if isinstance(d, Opaque) and isinstance(d.content, dict):
            kinds |= set(d.content)
    if kinds == {"QuotientOrZero"}:
        return "opaque QuotientOrZero"
    if kinds == {"IfEqZero"}:
        return "opaque IfEqZero"
    return "opaque other"


def _no_match_reason(cw: Expr, bus_only: set[str]) -> str:
    """Split "no single premise" by checkable facts about c[w]."""
    # A column only the buses constrain has no algebraic premise to come from.
    if variables(cw) & bus_only:
        return "bus-only columns"
    # Otherwise tell linear from nonlinear: a linear one could follow from a
    # combination of premises, which a future elimination rule would find.
    try:
        p = poly.expand(cw, lambda n: poly.var_poly(n), BABYBEAR)
    except poly.ExpansionLimit:
        return "nonlinear, no match"
    linear = all(poly.degree(m) <= 1 for m in p)
    return "linear, no match" if linear else "nonlinear, no match"


def _key(e: Expr):
    """lens's canonical key of ``e = 0``, or None if lens rejects the expression."""
    try:
        return canon_zero(e)
    except CanonError:
        return None


def _remember(cache: dict, key, ob: Obligation) -> Obligation:
    """Cache a verdict under its key (when there is one) and return it."""
    ob = replace(ob, key=key)
    if key is not None:
        cache[key] = ob
    return ob
