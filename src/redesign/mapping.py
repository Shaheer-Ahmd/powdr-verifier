"""Step A: the mapping w from candidate columns to terms over reference columns.

Sources, in priority order:
  1. same name     - the column exists on the reference side: maps to itself
  2. derived       - the candidate's own ``derived_columns`` recipe
  3. substitution  - ``_substitutions.json``, composed down to reference columns
  4. witness       - soundness only: read off a merged constraint, or one shared
                     term found by search
  5. lookup-only   - soundness only: a constant for a column that only lookups
                     mention: 0, else the root of a lookup argument
  6. zero          - soundness only: 0 for a group the witness search could
                     not map, kept if PolySolver then proves its constraints

In soundness a derived recipe PolySolver cannot read (IfEqZero, QuotientOrZero)
is skipped, so the column goes on to sources 3 to 6.

Any mapping is sound: a poor choice can only make an obligation unprovable,
never prove a wrong pass (``flip_quant``). So the heuristics here are free to
be heuristic. Same-name columns are declared in the solver and need no entry.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from src.polysolver import (
    Defs,
    Expr,
    Implied,
    InvalidDefs,
    Opaque,
    PolySolver,
    find_uniform_witness,
    find_witness,
    variables,
)

from .circuit import (
    STATELESS_BUSES,
    Circuit,
    interaction_columns,
    recipe_columns,
    substitute,
)
from .tables import bound, lookup_holds


class MissingDefinition(Exception):
    """A new After column has no definition (completeness); powdr should export one."""


@dataclass
class Mapping:
    """The witness w for one direction, plus what we learned building it."""

    # Candidate-only column -> its term over reference columns.
    defs: dict[str, Expr | Opaque] = field(default_factory=dict)
    # Column -> which source defined it: "derived", "substitution", "witness",
    # "zero witness", "lookup-only zero" or "lookup-only root".
    source: dict[str, str] = field(default_factory=dict)
    # Columns no source could define; their obligations stay undecided.
    unmapped: set[str] = field(default_factory=set)
    # Why each unmapped column is unmapped: "witness search failed" or "lookup-only".
    unmapped_reason: dict[str, str] = field(default_factory=dict)
    # Each witness found: (the columns that share it, the term).
    witnesses: list[tuple[list[str], Expr]] = field(default_factory=list)
    # Extra definitions of a derived column beyond the first: (column, rhs) to check.
    extra: list[tuple[str, Expr | Opaque]] = field(default_factory=list)


def completeness_mapping(
    before: Circuit, after: Circuit, subs: dict[str, Expr]
) -> Mapping:
    """w: After columns -> terms over Before columns. Raises if a column has no source."""
    m = Mapping()
    # Only After-only columns need a definition; shared ones map to themselves.
    for col in _needed(after, before):
        if not _from_derived(m, col, after) and not _from_subs(m, col, subs, before):
            m.unmapped.add(col)
    # powdr exports a definition for every column it adds, so a gap here is a
    # broken dump, not something to search for.
    if m.unmapped:
        raise MissingDefinition(", ".join(sorted(m.unmapped)))
    return m


def soundness_mapping(
    after: Circuit, before: Circuit, subs: dict[str, Expr], solver: PolySolver
) -> Mapping:
    """w': Before columns -> terms over After columns. ``solver`` holds After's premises."""
    m = Mapping()
    # Before-only columns: try the recorded sources first.
    left = [
        col
        for col in _needed(before, after)
        if not _from_derived(m, col, before, skip_opaque=True)
        and not _from_subs(m, col, subs, after)
    ]
    # A column used only by lookups (no constraint mentions it) has nothing for
    # the witness search to check against. Typically it is a free column whose
    # range check the pass dropped. Its value is ours to choose, so propose
    # constants (_lookup_only_value) and keep the first one under which every
    # lookup that mentions the column holds outright.
    in_constraints = _constraint_columns(before)  # all candidate columns in algebraic constraints
    lookup_only = [col for col in left if col not in in_constraints]
    interactions = _interactions_by_column(before, lookup_only)
    defs = solver.make_defs(m.defs) if lookup_only else None
    for col in lookup_only:
        found = _lookup_only_value(col, interactions[col], solver, defs)
        if found is None:
            m.unmapped.add(col)
            m.unmapped_reason[col] = "lookup-only"
            continue
        value, defs = found
        m.defs[col] = value
        m.source[col] = "lookup-only zero" if value == 0 else "lookup-only root"
    left = [col for col in left if col in in_constraints]
    # What is left was merged away with no hint (e.g. the is-zero inverse
    # markers). Each group of such columns gets its own witness.
    for group in _groups(left, before.constraints):
        targets = [c for c in before.constraints if variables(c) & group]
        shortlist = _shortlist(after, before, targets)  # After-only columns, e.g. free_var
        # First: read inv_i := f or f * x_i off After's f * (x_1' + ... + x_n') + c.
        w = find_witness(solver, m.defs, group, targets, shortlist)
        # if w is None: # we don't need the fallback - `find_witness` covers `find_uniform_witness``
        #     # Fallback: one After column for all of them (e.g. a renamed column).
        #     r = find_uniform_witness(solver, m.defs, group, targets, shortlist)
        #     w = None if r is None else dict.fromkeys(group, r)
        source = "witness"
        if w is None:
            # Last: 0 for every column, e.g. markers whose only constraint is
            # booleanity (their recipe is an IfEqZero we do not read).
            w, source = _zero_witness(solver, m.defs, group, targets), "zero witness"
        if w is None:
            m.unmapped |= group  # reported, never guessed
            for col in group:
                m.unmapped_reason[col] = "witness search failed"
            continue
        m.defs.update(w)
        for col in group:
            m.source[col] = source
        # Report one entry per distinct term: in the linear case all inv_i share
        # f (one entry), in the squared case each has its own f * x_i.
        shared: dict[str, tuple[list[str], Expr]] = {}  # repr(term) -> (columns, term)
        for col in sorted(group):
            shared.setdefault(repr(w[col]), ([], w[col]))[0].append(col)
        m.witnesses += shared.values()
    return m


def _interactions_by_column(c: Circuit, cols: list[str]) -> dict[str, list[dict]]:
    """For each of ``cols``, the interactions of ``c`` that mention it (one pass)."""
    out: dict[str, list[dict]] = {col: [] for col in cols}
    if not cols:
        return out
    for bi in c.bus_interactions:
        for col in interaction_columns(bi) & out.keys():
            out[col].append(bi)
    return out


def _lookup_only_value(
    col: str, interactions: list[dict], solver: PolySolver, defs: Defs
) -> tuple[int, Defs] | None:
    """A constant for the lookup-only column ``col``, with ``defs`` extended by it, or None.

    Candidates, in order: 0, then for each lookup argument that mentions the
    column the value that makes that argument 0 (PolySolver.linear_root),
    tightest table bound first (tables.bound). 0 is a row of every range
    table, so meeting the tightest check exactly leaves the slack to the wider
    ones: in the timestamp gadget [low, 17], [(gap - low) / 2^17, 12] the root
    low = gap is the honest split. The first candidate under which every
    lookup holds (tables.lookup_holds) is kept. The order is a heuristic; the
    sweep evaluates every lookup again. A stateful use declines: its value is
    not ours to choose from the tables alone.
    """
    if not interactions or any(bi["id"] not in STATELESS_BUSES for bi in interactions):
        return None
    roots = []
    for bi in interactions:
        for k, arg in enumerate(bi["args"]):
            if col in variables(arg):
                root = solver.linear_root(arg, col, defs)
                if root is not None:
                    b = bound(bi, k)
                    roots.append((b is None, b or 0, root))
    for value in dict.fromkeys([0, *(r for _, _, r in sorted(roots))]):
        extended = solver.extend_defs(defs, col, value)
        if all(lookup_holds(solver, bi, extended) for bi in interactions):
            return value, extended
    return None


def _needed(cand: Circuit, ref: Circuit) -> list[str]:
    """Candidate columns the obligations mention that the reference lacks.

    Obligations are the candidate's constraints and its stateless interactions.
    """
    cols = _constraint_columns(cand)
    for bi in cand.stateless:
        cols |= interaction_columns(bi)
    return sorted(cols - ref.columns)


def _constraint_columns(c: Circuit) -> set[str]:
    return (
        set().union(*(variables(e) for e in c.constraints)) if c.constraints else set()
    )


def _zero_witness(
    solver: PolySolver, base_w: dict, group: set[str], targets: list[Expr]
) -> dict[str, Expr] | None:
    """0 for every column of ``group``, if PolySolver then proves every target; else None."""
    w = dict.fromkeys(group, 0)
    try:
        defs = solver.make_defs({**base_w, **w})
    except InvalidDefs:
        return None
    if all(isinstance(solver.implies(t, defs), Implied) for t in targets):
        return w
    return None


def _from_derived(m: Mapping, col: str, cand: Circuit, skip_opaque: bool = False) -> bool:
    """Define ``col`` by its ``derived_columns`` recipe, if it has one.

    ``skip_opaque`` (soundness) ignores the recipes PolySolver cannot read.
    There the witness is ours to choose, and an opaque one proves nothing, so
    the column goes on to the other sources: a constant for a lookup-only
    column, the witness search, then 0. Completeness keeps the recipe: it is
    what After's prover runs.
    """
    recipes = cand.derived.get(col)
    if not recipes:
        return False
    defs = [_recipe_def(r) for r in recipes]
    if skip_opaque:
        defs = [d for d in defs if not isinstance(d, Opaque)]
        if not defs:
            return False
    m.defs[col], m.source[col] = defs[0], "derived"
    m.extra += [(col, d) for d in defs[1:]]  # pick one; the rest become obligations
    return True


def _recipe_def(recipe: dict) -> Expr | Opaque:
    """A recipe as a definition PolySolver accepts.

    Constants are polynomials. QuotientOrZero and IfEqZero are not, so they
    become Opaque: still a valid witness, but PolySolver never looks inside.
    """
    if set(recipe) == {"Constant"}:
        return recipe["Constant"]
    return Opaque(recipe)


def _from_subs(m: Mapping, col: str, subs: dict[str, Expr], ref: Circuit) -> bool:
    """Define ``col`` from the substitutions file, if it resolves to ref columns."""
    rhs = _compose(col, subs, ref, set())
    if rhs is None:
        return False
    m.defs[col], m.source[col] = rhs, "substitution"
    return True


def _compose(
    col: str, subs: dict[str, Expr], ref: Circuit, seen: set[str]
) -> Expr | None:
    """Follow substitutions until only reference columns remain, or give up.

    The file covers the whole pipeline, so a replacement can mention a column
    that was itself eliminated later (x -> y, y -> z). We chase such chains;
    ``seen`` stops a cycle from looping forever.
    """
    if col in seen or col not in subs:
        return None
    rhs = subs[col]
    inner = {}
    # Resolve every column of the replacement the reference doesn't have.
    for v in variables(rhs) - ref.columns:
        sub = _compose(v, subs, ref, seen | {col})
        if sub is None:
            return None
        inner[v] = sub
    return substitute(rhs, inner)


def _groups(cols: list[str], constraints: list[Expr]) -> list[set[str]]:
    """Split unknown columns into groups that share a constraint (union-find).

    One block can contain several merged gadgets, each needing its own
    witness. Columns that appear together in a constraint belong to the same
    gadget, so they share one search.
    """
    parent = {c: c for c in cols}

    def find(c: str) -> str:
        # Walk up to the group's root, shortening the path as we go.
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c

    # Merge all unknowns that occur in the same constraint.
    for e in constraints:
        hit = [c for c in variables(e) if c in parent]
        for c in hit[1:]:
            parent[find(c)] = find(hit[0])
    groups: dict[str, set[str]] = {}
    for c in cols:
        groups.setdefault(find(c), set()).add(c)
    return list(groups.values())


def _shortlist(ref: Circuit, cand: Circuit, targets: list[Expr]) -> list[str]:
    """Reference columns the candidate lacks; those whose recipe touches the targets first."""
    # A merged column is usually replaced by a column the pass added.
    new = sorted(ref.columns - cand.columns)
    touched = set().union(*(variables(t) for t in targets)) if targets else set()

    # The added column's recipe is a strong hint: free_var_123 is defined from
    # cmp and the limbs, the same columns the inverse markers' constraint uses.
    def related(col: str) -> bool:
        return any(recipe_columns(r) & touched for r in ref.derived.get(col, []))

    # Order only affects speed: every candidate is checked by implies anyway.
    return sorted(new, key=lambda c: not related(c))
