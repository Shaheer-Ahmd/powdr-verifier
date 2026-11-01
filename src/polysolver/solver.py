"""PolySolver: decides  P and R and Defs |= (q = 0)  over F_p. Sound, incomplete.

The answer to a query q is ``Implied`` (with what it rests on) or
``Unknown``; there is no "not implied". The solver knows nothing about
circuits: only variables, polynomials, ranges and definitions.

The store:
- P: premises, polynomials each read as "= 0" (add_premise). Trusted.
- R: ranges lo <= x <= hi on the integer representative of x (add_range).
  Trusted.
- Dom: per variable, lo <= x <= hi and optionally a finite set of values,
  with tags naming the premises, ranges and solved equations it rests on.
- Sol: solved equations x = t, from a checked equation (add_solved) or
  from a domain with one value (a pin). t never mentions a solved variable, and x
  is replaced by t in the premises (as the rules read them) and in queries.
- Defs: definitions of fresh variables, passed with a query. No premise
  mentions them, so they need no check.

Invariant I: every assignment over F_p that satisfies P and R satisfies
every fact in Dom and Sol. Hence every premise, as rewritten under Sol,
holds in every model, and so does every Implied verdict. Each rule below
keeps I using only facts already in the store, so the rules may fire in any
order and at any time: scheduling changes what is found and what it costs,
never soundness.

Rules that add to the store, each a local implication:
- D (domain): a premise that mentions only x, each of whose top-level
  factors is a nonzero constant or a*x + b, gives x in {-b/a}: F_p has no
  zero divisors. So x - c pins x, and x(x - 1) gives {0, 1}.
- O (one-hot), on a premise whose variables are all in [0, 1]:
  - group part: the premise reads x_1 + ... + x_n - c with c in {0, 1}.
    The integer sum is in [0, n] and n < p, so it is c: with c = 0 every
    x_i is 0, a single x_1 is c, and otherwise exactly one x_i is 1 (the
    premise is a group).
  - selector part: a premise w_0 + sum w_x * x over members of a group
    reads w_0 + w_j for the member j that is 1. Every member whose weight
    (0 if absent) is not -w_0 is 0; if one member is left, it is 1.
- C (case split): premises Q over variables that each have a set of three
  values. Every model, restricted to the variables of Q, is a solution of Q
  over those sets, so x = v holds if every solution has x = v
  (enumeration.fixed_values). Leaving premises out of Q loses completeness
  only.
- Collapse: a domain with one value v gives x = v, which goes into Sol.
- Checked equation: x = t (add_solved) goes into Sol only once rule N or S
  proves x - t.
A contradiction (an empty domain, no group member left that can be 1, C
with no solution) means P and R have no model, so anything follows. The
policy is to use nothing (C's are counted).

Rules that answer a query, q rewritten under Sol and Defs, cheapest first:
- N (normalize): q has the same zero key as a premise, so they differ by a
  nonzero factor.
- S (no-wrap split): a premise G * (c1*a1 + ... + cn*an) with ranged a_i
  whose weighted sum cannot reach p implies G * a_j = 0 for every j.

The contract that keeps each rule local:
- D, O and C change the store only through _narrow_domain, with tags
  naming every premise and domain they read (_premise_tags, _domain_tags).
  O's group index only says where its selector part should look, and that
  part re-reads the group.
- _substitute is called only for pins (_substitute_pins) and for
  checked equations (_check_solved).

Triggers, which are scheduling only:
- add_premise: D on a premise that mentions one variable as written.
- propagate(), a work list (_run_queue): D and O on every premise whose
  reading changed: added, rewritten by a substitution, or with a variable
  newly in [0, 1] or in a new group.
- add_solved: if N and S leave x - t Unknown and x is unsolved with a set
  of three values, C searches x's group once; if that pins anything, the
  work list runs and x - t is checked again. The caller picks the
  equations and their order.

Termination: domains only shrink and a variable is substituted at most
once, so the work list runs empty. C runs at most once per add_solved call,
within CASE_SPLIT_GROUP_CAP cases and CASE_SPLIT_NODE_CAP values tried.
"""

from __future__ import annotations

import time
from collections import defaultdict, deque
from collections.abc import Iterable
from dataclasses import dataclass, field, replace
from typing import NamedTuple

from . import poly as P
from .defs import NO_DEFS, Defs, InvalidDefs, Opaque
from .enumeration import GaveUp, NoSolution, fixed_values
from .expr import Expr, product_factors, variables
from .table import Var, VarTable

BABYBEAR = 2013265921
# Rule C gives up on a group with more cases than this, or a search that tries
# more values. keccak's largest group has 243 cases (five variables).
CASE_SPLIT_GROUP_CAP = 4096
CASE_SPLIT_NODE_CAP = 100_000


class UndefinedVariable(LookupError):
    """A variable is neither declared nor defined: a caller error."""


@dataclass(frozen=True)
class Implied:
    rule: str  # "trivial" | "normalize" | "nowrap-split"
    premises: tuple[str, ...] = ()  # tags of the premises used
    ranges: tuple[str, ...] = ()  # variables whose ranges were used
    defs: tuple[str, ...] = ()  # defined variables that occur in q
    # Tags of the solved equations that rewrote q or the premises used. Each
    # was itself checked when it was added (and may rest on earlier ones); a
    # pin (a collapsed range) contributes the tags of the premises behind it.
    solved: tuple[str, ...] = ()


@dataclass(frozen=True)
class Unknown:
    note: str  # why each rule declined, for triage
    # Machine-readable reason: "opaque", "expansion-limit", "nonzero-constant",
    # "no-match", or a near miss of rule S: "nowrap-missing-range", "nowrap-bound".
    kind: str = "no-match"


Verdict = Implied | Unknown


class _Domain(NamedTuple):
    """What is known of a variable: lo <= x <= hi, and x is one of ``values`` if given."""

    lo: int
    hi: int
    values: frozenset[int] | None  # a finite set; lo and hi are then its min and max
    tags: list[str]  # the premises and ranges it rests on


@dataclass
class _Premise:
    """One premise, kept as given. Its expansion is computed only when needed."""

    tag: str  # the caller's name for it, reported back in verdicts
    expr: Expr  # the expression exactly as given
    vars: frozenset = frozenset()  # its variables as written
    # Everything below is derived from expr under the solved equations, and
    # recomputed when they change (version differs from the solver's).
    version: int = 0
    key: P.Key | None = None  # zero key; None until computed, or if too big
    expanded: bool = False  # True once we tried to compute the key
    kvars: set | None = None  # the variables of key
    # The top-level factors as written, their expansions (filled in only as
    # needed), and which ones are sums (rule S). The factors and their
    # variables are syntax, so they never go stale.
    factors: list | None = None  # the expressions of the top-level * chain
    factor_vars: list | None = None  # the variables of each factor, as written
    written_vars: set | None = None  # all of them
    polys: dict = field(default_factory=dict)  # factor position -> Poly (or None)
    sums: list | None = None  # [(factor position, Poly)] for the linear sums


class PolySolver:
    """Premises and ranges only grow; an Implied verdict therefore stays valid."""

    def __init__(
        self,
        table: VarTable,
        declared: Iterable[str],
        p: int = BABYBEAR,
        max_terms: int = P.MAX_TERMS,
        constants: bool = True,
        one_hot: bool = True,
        case_split: bool = True,
    ):
        self.table = table
        self.p = p
        self.max_terms = max_terms
        # Switches: rule D's pins from x - c (constants), rule D's sets of
        # several values and rule O (one_hot), add_solved's rule C (case_split).
        self._use_constants, self._use_one_hot = constants, one_hot
        self._use_case_split = case_split
        self.declared: frozenset[Var] = frozenset(table.var(n) for n in declared)
        self._premises: list[_Premise] = []
        # Premise index for rule N: variable -> ids of the premises that mention it.
        # Built from the syntax alone, so adding a premise costs no expansion.
        self._by_var: dict[Var, list[int]] = defaultdict(list)
        self._domains: dict[Var, _Domain] = {}
        # Verdict caches, keyed by the query's zero key. Implied stays true as
        # premises grow; Unknown may not, so that cache is cleared on every add.
        self._implied: dict[P.Key, Implied] = {}
        self._unknown: dict[P.Key, Unknown] = {}
        # Solved equations x = t (add_solved). t is kept fully reduced: it never
        # mentions a solved variable, so one lookup replaces x for good.
        self._solved: dict[Var, P.Poly] = {}
        self._solved_tag: dict[Var, tuple[str, ...]] = {}
        # Variable -> solved variables whose t mentions it (for back-substitution
        # and for finding premises that mention a variable only through t).
        # May list a few extra after cancellations; that costs only time.
        self._occurs_in: dict[Var, set[Var]] = defaultdict(set)
        self._solved_version = 0  # bumped on every substitution; stales premise caches
        # Rule O: variable -> the groups (premise ids) it is a member of.
        self._group_index: dict[Var, set[int]] = defaultdict(set)
        self._new_pins: list[Var] = []  # domains with one value, not yet substituted
        self._pinned_by_constant: set[Var] = set()  # pinned by rule D from x - c
        # propagate()'s work list while it runs; between runs, what the next one
        # must look at (new premises, and those that ranges or solved
        # equations changed).
        self._queue: deque[int] | None = None
        self._queued: set[int] = set()
        self._pending: set[int] = set()
        self.premises_expanded = 0  # premise keys computed (rule N)
        self.premises_split = 0  # premises split into factors (rule S)
        self.solved_accepted = 0  # add_solved calls accepted (also values equal to a pin)
        self.solved_agreed = 0  # of those, x already had that value: nothing changed
        self.solved_rejected = 0  # add_solved calls whose check failed
        self.constants_solved = 0  # variables pinned by a premise x - c
        self.pinned = 0  # variables pinned otherwise (a collapsed domain)
        self.propagate_pins: list[int] = []  # variables pinned by each propagate() call
        self.case_splits = 0  # groups rule C searched
        self.case_split_nodes = 0  # values it tried, over all its searches
        self.case_split_capped = 0  # groups or searches over the caps
        self.case_split_unsat = 0  # searches with no fit: the premises contradict each other
        self.case_split_seconds = 0.0  # its own time
        # (tag, verdict, agreed with x's value) per add_solved call
        self.solved_log: list[tuple[str, Verdict, bool]] = []

    # ------------------------------------------------------------ inputs

    def add_premise(self, e: Expr, tag: str) -> None:
        """Assert ``e = 0``. Trusted: the caller vouches for it.

        A premise that mentions one variable x as written gives x's domain at
        once (rule D). propagate() reads it again, as it reads any premise:
        one with more variables can mention only x after a pin.
        """
        vs = self._declared_vars(e, "premise")
        idx = len(self._premises)
        prem = _Premise(tag, e, frozenset(vs))
        self._premises.append(prem)
        # Index by the variables as written. Rules N and S expand a premise
        # only when a query first needs it.
        for v in vs:
            self._by_var[v].append(idx)
        self._pending.add(idx)  # for the next propagate()
        self._unknown.clear()  # an earlier Unknown might now be provable
        if len(prem.vars) == 1 and vs[0] not in self._solved:
            self._rule_d(idx, vs[0])
            self._substitute_pins()

    def add_range(self, x: str, lo: int, hi: int, tag: str) -> None:
        """Assert ``lo <= x <= hi``; a second range on x intersects with the first.

        If the bounds meet, x is replaced by that value from now on.
        """
        if not 0 <= lo <= hi < self.p:
            raise ValueError(f"bad range [{lo}, {hi}] for {x}")
        (v,) = self._declared_vars(x, "range")
        self._narrow_domain(v, lo, hi, [tag])
        self._substitute_pins()

    def add_solved(self, x: str, t: Expr, tag: str) -> Verdict:
        """Check that ``x = t`` is implied; if so, replace x by t from now on.

        x must be declared. The check is an ordinary query of x - t against
        the current state. On Implied, x is replaced by t in the premises (as
        the rules see them), in earlier solved equations and in all later
        queries. On Unknown the equation is rejected, which costs
        completeness only. If x is already solved (e.g. pinned by propagate),
        the query compares its value with t, and an Implied verdict changes
        nothing. If the check is Unknown and x has a set of three values,
        rule C searches x's group once; if that pins anything, the work list
        runs and x = t is checked again (C's pins stay either way). An
        Implied verdict names the solved equations that rewrote x - t, so an
        equation that agrees with a pin from C names the premises behind it.
        Every verdict goes into ``solved_log``, with whether it agreed with a
        value x already had.
        """
        agreed = self.solved_agreed
        verdict = self._add_solved(x, t, tag)
        self.solved_log.append((tag, verdict, self.solved_agreed > agreed))
        return verdict

    def _add_solved(self, x: str, t: Expr, tag: str) -> Verdict:
        (xv,) = self._declared_vars(x, "solved variable")
        self._declared_vars(t, "solved value")
        verdict = self._check_solved(xv, t, tag)
        if (
            isinstance(verdict, Unknown)
            and self._use_case_split
            and xv not in self._solved
            and self._three_valued(xv)
            and self._rule_c(xv)
        ):
            self._substitute_pins()
            self._run_queue()
            verdict = self._check_solved(xv, t, tag)  # a comparison, if x is pinned now
        if isinstance(verdict, Unknown):
            self.solved_rejected += 1
        return verdict

    def _check_solved(self, xv: Var, t: Expr, tag: str) -> Verdict:
        """Rules N and S on x - t; if Implied and x is unsolved, replace x by t."""
        x = self.table.name(xv)
        try:
            rhs = P.expand(t, self._plain, self.p, self.max_terms)
        except P.ExpansionLimit:
            return Unknown("expansion limit", "expansion-limit")
        # The solved equations that rewrote x - t, as implies reports them for q.
        rewrote = [xv, *(self._var(n) for n in variables(t))]
        if xv in self._solved:
            k = P.zkey(P.add(self._solved[xv], rhs, self.p, -1), self.p)
            verdict = self._decide(k)
            if not isinstance(verdict, Implied):
                return Unknown(f"{x} is already solved", "already-solved")
            self.solved_accepted += 1
            self.solved_agreed += 1
            return self._with_solved_tags(verdict, rewrote)
        # t must not mention x, or "replace x by t" would not remove x.
        if xv in P.variables_of(rhs):
            return Unknown(f"{x} occurs in its own value", "not-solved")
        k = P.zkey(P.add(P.var_poly(xv), rhs, self.p, -1), self.p)
        verdict = self._decide(k)
        if not isinstance(verdict, Implied):
            return verdict
        verdict = self._with_solved_tags(verdict, rewrote)  # before x is solved
        try:
            self._substitute(xv, rhs, (tag,))
        except P.ExpansionLimit:
            return Unknown("expansion limit (back-substitution)", "expansion-limit")
        self.solved_accepted += 1
        return verdict

    def _with_solved_tags(self, verdict: Implied, vs: Iterable[Var]) -> Implied:
        """``verdict``, also naming the solved equations of the variables ``vs``."""
        solved = set(verdict.solved) | set(self._solved_tags(vs))
        return replace(verdict, solved=tuple(sorted(solved)))

    def _substitute(self, xv: Var, rhs: P.Poly, tags: tuple[str, ...]) -> None:
        """Replace x by rhs from now on; rhs is fully reduced and does not mention x.

        Earlier solved values that mention x get x replaced too, so every value
        stays free of solved variables. They are all computed before anything
        changes, so an expansion limit leaves no trace. The premises that
        mention x read differently now, so propagate() looks at them again.
        """
        # Taken before x is replaced: afterwards _occurs_in no longer lists it.
        again = self._coi_premise_ids(xv)

        def by_rhs(v: Var) -> P.Poly | None:
            return rhs if v == xv else None

        updated = {
            y: P.substitute(self._solved[y], by_rhs, self.p, self.max_terms)
            for y in self._occurs_in.get(xv, ())
        }
        self._occurs_in.pop(xv, None)
        for y, value in updated.items():
            self._solved[y] = value
            for v in P.variables_of(value):
                self._occurs_in[v].add(y)
        self._solved[xv] = rhs
        self._solved_tag[xv] = tags
        for v in P.variables_of(rhs):
            self._occurs_in[v].add(xv)
        self._solved_version += 1  # premise keys and splits are now stale
        self._unknown.clear()  # an earlier Unknown might now be provable
        self._enqueue(again)

    def _narrow_domain(
        self,
        v: Var,
        lo: int,
        hi: int,
        tags: list[str],
        values: frozenset[int] | None = None,
    ) -> bool:
        """Intersect v's domain with [lo, hi] and ``values``; True if that narrowed it.

        The rules D, O and C change the store only through this, and
        ``tags`` names what they read.
        An empty intersection means the premises contradict each other; the
        domain is then left as it was. When one value is left, v is queued for
        _substitute_pins (the listener).
        """
        old = self._domains.get(v)
        if old is not None:
            # Both hold, so v lies in their intersection.
            lo, hi, tags = max(lo, old.lo), min(hi, old.hi), old.tags + tags
            if old.values is not None:
                values = old.values if values is None else old.values & values
        if values is not None:
            values = frozenset(x for x in values if lo <= x <= hi)
            if values:
                lo, hi = min(values), max(values)
        if lo > hi or values == frozenset():
            return False
        if old is not None and (lo, hi, values) == old[:3]:
            return False
        self._domains[v] = _Domain(lo, hi, values, list(tags))
        self._unknown.clear()
        if hi <= 1 and (old is None or old.hi > 1):
            self._requeue_premises_of([v])  # newly in [0, 1]: a premise over v may be a group now
        if lo == hi and v not in self._solved:
            self._new_pins.append(v)
        return True

    def _substitute_pins(self) -> None:
        """Collapse: replace every variable whose domain has one value v by v (I gives x = v)."""
        while self._new_pins:
            v = self._new_pins.pop()
            if v in self._solved:
                continue
            d = self._domains[v]
            self._substitute(v, P.const(d.lo, self.p), tuple(dict.fromkeys(d.tags)))
            if v in self._pinned_by_constant:
                self.constants_solved += 1
            else:
                self.pinned += 1

    def propagate(self) -> int:
        """Apply rules D and O until nothing changes (_run_queue); return how many pinned."""
        before = self.pinned + self.constants_solved
        self._run_queue()
        self.propagate_pins.append(self.pinned + self.constants_solved - before)
        return self.propagate_pins[-1]

    def _run_queue(self) -> None:
        """Run propagate()'s work list until it is empty.

        Every premise is looked at once, then again whenever something it
        depends on changes: one of its variables gets a domain within [0, 1],
        joins a group, or is replaced by its value. Between runs, ranges and
        solved equations queue the premises they change for the next one.
        Domains only shrink and a variable is replaced at most once, so the
        list runs empty, and then no premise can give anything new. A
        premise is expanded only if its variables, as it reads now, could fit
        a rule: one variable (D), or all of them within [0, 1] (O); _vars_now
        says when they are read off the key instead.
        """
        todo, self._pending = sorted(self._pending), set()
        self._queue, self._queued = deque(), set()
        try:
            # One-variable premises first: they hold the x^2 - x that O needs.
            self._enqueue(i for i in todo if len(self._premises[i].vars) == 1)
            self._enqueue(todo)
            while self._queue:
                i = self._queue.popleft()
                self._queued.discard(i)
                self._propagate_premise(i)
                self._substitute_pins()
        finally:
            self._queue = None

    @staticmethod
    def _as_pin(k: P.Key | None) -> tuple[Var, int] | None:
        """(x, value) if the zero key says x = value, else None."""
        if not k:
            return None
        lead, c = k[0]  # monic: the leading term has coefficient 1
        if len(lead) != 1 or lead[0][1] != 1 or c != 1:
            return None
        rest = k[1:]
        if any(m != () for m, _ in rest):
            return None
        value = -rest[0][1] if rest else 0
        return lead[0][0], value

    @property
    def solved_count(self) -> int:
        """Number of solved variables: accepted equations and pins."""
        return len(self._solved)

    def make_defs(self, mapping: dict[str, Expr | Opaque]) -> Defs:
        """Validate definitions (D1 fresh, D2 flat, D3 polynomial or opaque)."""
        polys, opaque = {}, set()
        for name, rhs in mapping.items():
            v = self._var(name)
            if v in self.declared:
                raise InvalidDefs(f"D1: {name} is declared, it cannot be defined")
            if isinstance(rhs, Opaque):
                opaque.add(v)
                continue
            for n in variables(rhs):  # raises UnsupportedExpr outside the grammar
                if self._var(n) not in self.declared:  # also rules out chains
                    raise InvalidDefs(f"D2: {name} := ... mentions undeclared {n}")
            # Stored as written: implies applies the solved equations on use,
            # so the Defs stay valid when more equations are solved later.
            try:
                polys[v] = P.expand(rhs, self._as_written, self.p, self.max_terms)
            except P.ExpansionLimit:
                polys[v] = None  # queries through v report the limit
        return Defs(polys, frozenset(opaque), id(self.table))

    # ------------------------------------------------------------ query

    def implies(self, q: Expr, defs: Defs = NO_DEFS) -> Verdict:
        """Is ``q = 0`` implied? ``q`` itself is never modified."""
        if defs is not NO_DEFS and defs.owner != id(self.table):
            raise ValueError("defs were made by a solver with another table")
        names = variables(q)
        # Sort q's non-declared variables into defined (used) and opaque ones;
        # anything else is a caller error.
        used, opaque = [], []
        for n in sorted(names):
            v = self._var(n)
            if v in self.declared:
                continue
            if not defs.defines(v):
                raise UndefinedVariable(f"{n} is neither declared nor defined")
            (opaque if v in defs.opaque else used).append(n)
        if opaque:
            return Unknown(f"opaque: {', '.join(opaque)}", "opaque")

        try:
            k = P.zkey(P.expand(q, self._expander(defs), self.p, self.max_terms), self.p)
        except P.ExpansionLimit:
            return Unknown("expansion limit", "expansion-limit")

        # Queries with the same key are the same question; answer once.
        verdict = self._implied.get(k) or self._unknown.get(k)
        if verdict is None:
            verdict = self._decide(k)
            (self._implied if isinstance(verdict, Implied) else self._unknown)[k] = (
                verdict
            )
        if isinstance(verdict, Implied):
            # The cached verdict is shared; report this query's own definitions
            # and the solved equations that rewrote q (directly or via a Def).
            mine = self._solved_tags(self._q_vars(names, defs))
            solved = tuple(sorted(set(verdict.solved) | set(mine)))
            return Implied(
                verdict.rule, verdict.premises, verdict.ranges, tuple(used), solved
            )
        return verdict

    def implies_equal(self, a: Expr, b: Expr, defs: Defs = NO_DEFS) -> Verdict:
        """Is ``a = b`` implied, as values in F_p? The same question as implies(a - b)."""
        return self.implies([a, "-", b], defs)

    def normal_form(
        self, e: Expr, defs: Defs = NO_DEFS, free: Iterable[str] = ()
    ) -> tuple | None:
        """``e`` expanded under the Defs and the solved equations, as a hashable value.

        For proposing candidates only (e.g. an index of lookups): two expressions
        with the same normal form are equal, but a caller that relies on it must
        still ask implies or implies_equal, so that every verdict comes from the
        rules. Names in ``free`` stay plain variables (e.g. the unknowns of a
        witness search). None if ``e`` mentions an opaque or unknown variable,
        or is too big.
        """
        free = set(free)
        for n in variables(e):
            if n in free:
                continue  # no value of its own: expands to itself
            try:
                v = self._var(n)
            except UndefinedVariable:
                return None
            if not (v in self.declared or v in defs.polys):
                return None
        try:
            return tuple(sorted(P.expand(e, self._expander(defs), self.p, self.max_terms).items()))
        except P.ExpansionLimit:
            return None

    def premises_mentioning(self, name: str) -> list[Expr]:
        """The premises, as written, that mention the variable ``name``.

        For a caller that looks for a shape in the written form (e.g. the
        witness search reading f * (x_1' + ... + x_n') + c); not expanded.
        """
        return [self._premises[i].expr for i in self._by_var.get(self._var(name), [])]

    def _expander(self, defs: Defs):
        """Expansion lookup: Defs (reduced on use), then the solved equations."""

        def lookup(n: str) -> P.Poly:
            v = self._var(n)
            if v in defs.polys:
                if defs.polys[v] is None:
                    raise P.ExpansionLimit
                return self._apply_solved(defs.polys[v])
            return self._plain(n)

        return lookup

    def _q_vars(self, names: set[str], defs: Defs) -> set[Var]:
        """Declared variables of q, including those inside the Defs it uses."""
        out = set()
        for n in names:
            v = self._var(n)
            if v in self.declared:
                out.add(v)
            elif defs.polys.get(v):
                out |= P.variables_of(defs.polys[v])
        return out

    def _decide(self, k: P.Key) -> Verdict:
        """Try the rules in order, cheapest first; the first Implied wins."""
        declined = []
        for rule in (self._rule_n, self._rule_s):
            v = rule(k)
            if isinstance(v, Implied):
                return v
            declined.append(v)
        # Report the most specific reason any rule gave.
        kind = next((v.kind for v in declined if v.kind != "no-match"), "no-match")
        return Unknown("; ".join(v.note for v in declined), kind)

    # ------------------------------------------------------------ rule N

    def _rule_n(self, k: P.Key) -> Verdict:
        """Rule N: q has the same zero key as some premise."""
        if k == P.ZERO:
            return Implied("trivial")
        if P.is_constant(k):
            return Unknown("N: nonzero constant", "nonzero-constant")
        # A premise with key k mentions every variable of k, directly or through
        # a solved value (_coi_premise_ids): looking up one of them is enough.
        # Pick the rarest one, so we expand as few premises as possible.
        v = min(P.key_vars(k), key=lambda x: len(self._coi_premise_ids(x)))
        for i in self._coi_premise_ids(v):
            if self._premise_key(i) == k:
                prem = self._premises[i]
                return Implied(
                    "normalize", (prem.tag,), solved=self._solved_tags_of(prem.expr)
                )
        return Unknown("N: no premise with this normal form")

    def _coi_premise_ids(self, v: Var) -> list[int]:
        """Premises whose key (under the solved equations) can mention v.

        Expansion only removes variables, so such a premise mentions v as
        written, or mentions a solved y whose value mentions v. Solved values
        are fully reduced, so one level of _occurs_in is enough.
        """
        ids = self._by_var.get(v, [])
        via = self._occurs_in.get(v)
        if not via:
            return ids
        out = set(ids)
        for y in via:
            out.update(self._by_var.get(y, ()))
        return sorted(out)

    def _drop_stale(self, prem: _Premise) -> _Premise:
        """Drop the premise's derived data if solved equations changed since."""
        if prem.version != self._solved_version:
            prem.version = self._solved_version
            prem.key, prem.expanded, prem.kvars = None, False, None
            prem.polys, prem.sums = {}, None
        return prem

    def _premise_key(self, i: int) -> P.Key | None:
        """The premise's zero key, expanded on first use and then cached."""
        prem = self._drop_stale(self._premises[i])
        if not prem.expanded:
            prem.expanded = True
            self.premises_expanded += 1
            try:
                prem.key = P.zkey(
                    P.expand(prem.expr, self._plain, self.p, self.max_terms), self.p
                )
            except P.ExpansionLimit:
                prem.key = None  # too big: this premise never matches
        return prem.key

    def _vars_from_key(self, i: int) -> set[Var]:
        """The variables of the premise's key; empty if it has none or is too big."""
        prem = self._drop_stale(self._premises[i])
        if prem.kvars is None:
            k = self._premise_key(i)
            prem.kvars = P.key_vars(k) if k else set()
        return prem.kvars

    def _premise_factors(self, i: int) -> list:
        """The premise's top-level factors as written, computed once."""
        prem = self._premises[i]
        if prem.factors is None:
            prem.factors = product_factors(prem.expr)
            prem.factor_vars = [
                {self._var(n) for n in variables(f)} for f in prem.factors
            ]
            prem.written_vars = set().union(*prem.factor_vars)
        return prem.factors

    # ------------------------------------------------------------ rule S

    def _premise_sums(self, i: int) -> list:
        """The premise's top-level factors that are sums c1*a1 + ... + cn*an.

        Computed on first use and cached, so only premises that rule S actually
        looks at are ever split. Each factor is fully expanded, so a factor that
        becomes a sum only after cancellation (x*y - x*y + a + b) is still found.
        """
        prem = self._drop_stale(self._premises[i])
        if prem.sums is None:
            self.premises_split += 1
            self._premise_factors(i)
            prem.sums = []
            for fi in range(len(prem.factors)):
                # Expansion never adds variables, so fewer than 2 means never a sum.
                if len(prem.factor_vars[fi]) < 2:
                    continue
                poly = self._factor_poly(prem, fi)
                # Linear with no constant: every term is one variable to the power 1.
                if (
                    poly
                    and len(poly) >= 2
                    and all(len(m) == 1 and m[0][1] == 1 for m in poly)
                ):
                    prem.sums.append((fi, poly))
        return prem.sums

    def _factor_poly(self, prem: _Premise, fi: int) -> P.Poly | None:
        """Expansion of one factor, cached; None if it is too big."""
        if fi not in prem.polys:
            try:
                prem.polys[fi] = P.expand(
                    prem.factors[fi], self._plain, self.p, self.max_terms
                )
            except P.ExpansionLimit:
                prem.polys[fi] = None
        return prem.polys[fi]

    def _rule_s(self, k: P.Key) -> Verdict:
        """Rule S: q is G * a, where some premise is G * (sum containing a).

        If no summand can wrap past p, G * sum = 0 forces G * a = 0 for every
        summand a. Only ranged variables of q can play the role of a.
        """
        notes, kind = [], "no-match"
        for a in sorted(P.key_vars(k)):
            if a not in self._domains:  # an unranged a can never pass the bound
                continue
            # A premise whose sum contains a mentions a, directly or through a
            # solved value, so _coi_premise_ids finds every candidate (as in rule N).
            for idx in self._coi_premise_ids(a):
                sums = self._premise_sums(idx)
                prem = self._premises[idx]
                for fi, s in sums:
                    if ((a, 1),) not in s:
                        continue
                    g = self._other_factors_times(prem, fi, a)
                    # The shape must match q (up to a constant factor) first.
                    if g is None or P.zkey(g, self.p) != k:
                        continue
                    # The shape matches; only the no-wrap condition is left.
                    why = self._no_wrap(s)
                    if why:
                        kind, msg = why
                        notes.append(f"{prem.tag}: {msg}")
                        continue
                    # Report every summand: all their ranges were used.
                    ranged = sorted(self.table.name(v) for ((v, _),) in s)
                    return Implied(
                        "nowrap-split",
                        (prem.tag,),
                        tuple(ranged),
                        solved=self._solved_tags_of(prem.expr),
                    )
        return Unknown(
            "S: " + ("; ".join(notes) if notes else "no ranged sum premise"), kind
        )

    def _other_factors_times(self, prem: _Premise, fi: int, a: Var) -> P.Poly | None:
        """G * a, where G is the product of the premise's factors other than ``fi``."""
        g = P.var_poly(a)
        try:
            for j in range(len(prem.factors)):
                if j != fi:
                    f = self._factor_poly(prem, j)
                    if f is None:
                        return None
                    g = P.mul(g, f, self.p, self.max_terms)
        except P.ExpansionLimit:
            return None
        return g

    def _no_wrap(self, s: P.Poly) -> tuple[str, str] | None:
        """(kind, message) saying why the sum ``s`` might wrap past p, or None."""
        # Every summand needs an upper bound, or the sum could be anything.
        missing = [self.table.name(v) for ((v, _),) in s if v not in self._domains]
        if missing:
            return "nowrap-missing-range", f"no range for {', '.join(sorted(missing))}"
        # With 0 <= a_i <= hi_i the integer sum is at most sum c_i * hi_i. If that
        # stays below p, "sum = 0 mod p" means the integer sum is 0, so each a_i = 0.
        # Any unit multiple k*s has the same zeros, so one k whose bound fits is
        # enough. Making s monic alone can hide a small sum: 2a + 3b becomes
        # a + (3/2)b, and 3/2 is huge in F_p. So try s as written, -s, and s made
        # monic in each of its terms, and keep the smallest bound.
        scales = {1, self.p - 1} | {pow(c, self.p - 2, self.p) for c in s.values()}
        bound = min(
            sum(c * k % self.p * self._domains[v].hi for ((v, _),), c in s.items())
            for k in scales
        )
        if bound >= self.p:
            return "nowrap-bound", f"sum of c_i * hi_i is {bound} >= p"
        return None

    # ------------------------------------------------------------ rules D and O

    def _propagate_premise(self, i: int) -> None:
        """Read premise i under the solved equations, and apply rule D or rule O."""
        vs = self._vars_now(i)
        if len(vs) == 1:
            self._rule_d(i, *vs)
        elif vs and self._use_one_hot and all(self._in_01(v) for v in vs):
            self._rule_o(i)

    def _rule_o(self, i: int) -> None:
        """Rule O on premise i, whose variables are all in [0, 1]: group part, then selector part.

        Group part: the premise reads x_1 + ... + x_n - c with unit weights
        and c in {0, 1}. Side condition: n < p, true as a key has at most
        max_terms terms; so the integer sum, in [0, n], is c. Conclusion:
        with c = 0 every x_i is 0; with n = 1, x_1 = 1; otherwise exactly one
        x_i is 1, and the premise is recorded as a group for the selector
        part. Tags: the premise and the members' domains.
        """
        lin = self._linear(self._premise_key(i))
        if lin is None or not lin[0]:
            return
        w, c0 = lin
        if self._is_group(w, c0):
            tags = self._premise_tags(i) + self._domain_tags(w)
            if c0 == 0:  # no member is on
                for x in w:
                    self._narrow_domain(x, 0, 0, tags)
            elif len(w) == 1:  # the one member left is on
                (x,) = w
                self._narrow_domain(x, 1, 1, tags)
            else:
                # Every member, also one a solved equation has swapped in
                # since the last look.
                new = [x for x in w if i not in self._group_index[x]]
                for x in new:
                    self._group_index[x].add(i)
                self._requeue_premises_of(new)  # their selectors can use this group now
        self._rule_o_selector(i, w, c0)

    def _vars_now(self, i: int) -> set[Var]:
        """The variables premise i mentions under the solved equations.

        Read off the syntax, unless a solved variable can have removed one: a
        gate solved to 0 removes what it gates (f*y with f := 0), and a solved
        value can cancel a variable (y + x - a - 3 with x := a). Then they
        are read off the premise's key.
        """
        for v in self._premises[i].vars:
            value = self._solved.get(v)
            if value is not None and (not value or any(value)):  # 0, or not a constant
                return self._vars_from_key(i)
        return self._vars_from_syntax(i)

    def _rule_d(self, i: int, x: Var) -> None:
        """Rule D: premise i, under the solved equations, mentions only x.

        Premise: each top-level factor, as written and reduced under the
        solved equations, is a nonzero constant or a*x + b; failing that, the
        key is x - c or x^2 - x. Conclusion: x is one of the roots. Side
        condition: none, as F_p has no zero divisors. Tags: the premise and
        the solved equations that rewrite it. The constants and one_hot
        switches say which conclusions are used.
        """
        roots = self._factor_roots(i, x)
        if roots is None:
            # Not linear factors as written (x*x - x, or a cancellation): the key.
            k = self._premise_key(i)
            pin = self._as_pin(k)
            if pin is not None and pin[0] == x:
                roots = (pin[1] % self.p,)
            elif self._boolean_var(k) == x:
                roots = (0, 1)
            else:
                return
        # With constants off, one value is still used for a variable in
        # [0, 1]: that is what rule O decided from such a premise.
        if len(roots) == 1:
            if not (self._use_constants or self._use_one_hot and self._in_01(x)):
                return
        elif not self._use_one_hot:
            return
        values = frozenset(roots)
        tags = self._premise_tags(i)
        if self._narrow_domain(x, min(values), max(values), tags, values) and len(roots) == 1:
            self._pinned_by_constant.add(x)  # counted as a constant, not a one-hot pin

    def _factor_roots(self, i: int, x: Var) -> tuple[int, ...] | None:
        """The roots -b/a if each factor of premise i is a nonzero constant or a*x + b."""
        self._premise_factors(i)
        prem = self._drop_stale(self._premises[i])
        # From the syntax first: a factor that mentions another unsolved
        # variable still does after solving (short of a cancellation).
        for vs in prem.factor_vars:
            if any(y != x and y not in self._solved for y in vs):
                return None
        lin = ((x, 1),)
        roots = set()
        for fi in range(len(prem.factors)):
            f = self._factor_poly(prem, fi)
            if not f:
                return None  # 0, so the premise says nothing (or too big)
            if f.keys() <= {()}:
                continue  # a nonzero constant
            if not f.keys() <= {(), lin}:
                return None
            roots.add(-f.get((), 0) * pow(f[lin], self.p - 2, self.p) % self.p)
        return tuple(sorted(roots)) or None  # no linear factor: never 0

    def _rule_o_selector(self, i: int, w: dict[Var, int], c0: int) -> None:
        """Rule O, selector part: premise i reads c0 + sum w_x * x over members of a group.

        Premises: i, and a group g, re-read now (unit weights, sum 1, every
        member in [0, 1]), with every variable of i a member. Exactly one
        member j is 1 and the rest are 0, so i reads c0 + w_j = 0.
        Conclusion: every member whose weight (0 if absent) is not -c0 is 0;
        if one member is left, it is 1. None left: the premises contradict
        each other, and nothing is used. Tags: i, g and the members' domains.
        """
        groups = set.intersection(*(self._group_index.get(x, set()) for x in w))
        for g in sorted(groups - {i}):
            # Re-read the group: pins since it was found may have changed it.
            group = self._linear(self._premise_key(g))
            if group is None or group[1] != self.p - 1 or not self._is_group(*group):
                continue
            members = group[0]
            if not w.keys() <= members.keys():
                continue
            on = [x for x in members if w.get(x, 0) == -c0 % self.p]
            if not on:
                continue  # the premises contradict each other: use nothing
            tags = self._premise_tags(i) + self._premise_tags(g)
            tags += self._domain_tags(members)
            for x in members:
                if x not in on:
                    self._narrow_domain(x, 0, 0, tags)
            if len(on) == 1:
                self._narrow_domain(on[0], 1, 1, tags)

    def _is_group(self, w: dict[Var, int], c0: int) -> bool:
        """Unit weights, constant 0 or -1 (a sum of 0 or 1), every member in [0, 1]."""
        return (
            set(w.values()) == {1}
            and c0 in (0, self.p - 1)
            and all(self._in_01(x) for x in w)
        )

    def _in_01(self, v: Var) -> bool:
        return v in self._domains and self._domains[v].hi <= 1

    def _premise_tags(self, i: int) -> list[str]:
        """Premise i's tag and those of the solved equations that rewrite it."""
        prem = self._premises[i]
        return [prem.tag, *self._solved_tags(prem.vars)]

    def _domain_tags(self, vs: Iterable[Var]) -> list[str]:
        return [t for v in vs for t in self._domains[v].tags]

    def _boolean_var(self, k: P.Key | None) -> Var | None:
        """x if the key is x^2 - x, else None."""
        if not k or len(k) != 2 or len(k[0][0]) != 1:
            return None
        x, e = k[0][0][0]
        return x if e == 2 and k == ((((x, 2),), 1), (((x, 1),), self.p - 1)) else None

    @staticmethod
    def _linear(k: P.Key | None) -> tuple[dict[Var, int], int] | None:
        """({x: c_x}, c_0) if the key is c_0 + sum c_x * x, else None."""
        if not k:
            return None
        coeffs, c0 = {}, 0
        for m, c in k:
            if m == ():
                c0 = c
            elif len(m) == 1 and m[0][1] == 1:
                coeffs[m[0][0]] = c
            else:
                return None
        return coeffs, c0

    def _vars_from_syntax(self, i: int) -> set[Var]:
        """The variables premise i can mention under the solved equations."""
        out = set()
        for v in self._premises[i].vars:
            value = self._solved.get(v)
            if value is None:
                out.add(v)
            else:
                out |= P.variables_of(value)
        return out

    # ------------------------------------------------------------ rule C

    def _three_valued(self, v: Var) -> bool:
        """v's domain is a set of exactly three values: the only ones rule C splits on."""
        d = self._domains.get(v)
        return d is not None and d.values is not None and len(d.values) == 3

    def _rule_c(self, x: Var) -> bool:
        """Rule C: pin each variable of x's group that has one value in every solution.

        Premises: the coupling premises Q, as rewritten, and the sets of
        their variables. Every model, restricted to the variables of Q, is a
        solution of Q over those sets, and fixed_values gives x = v only if
        every solution has x = v. Conclusion: x = v, tagged with Q and the
        sets. No solution: the premises contradict each other; counted, and
        nothing is used. True if it pinned any; they wait in _new_pins to
        be substituted.
        """
        start = time.perf_counter()
        try:
            group = self._rule_c_group(x)
            if group is None:
                return False
            dom, coupling = group
            self.case_splits += 1
            # Ties in the search order go by name: Var ids depend on the order
            # columns were interned.
            domains = {w: tuple(dom[w]) for w in sorted(dom, key=self.table.name)}
            keys = [self._premise_key(i) for i in coupling]
            found = fixed_values(keys, domains, self.p, CASE_SPLIT_NODE_CAP)
            self.case_split_nodes += found.nodes
            if isinstance(found, NoSolution):
                self.case_split_unsat += 1  # counted, and nothing is used
                return False
            if isinstance(found, GaveUp):
                self.case_split_capped += 1  # what was proved before stays proved
            tags = [t for i in coupling for t in self._premise_tags(i)]
            tags += self._domain_tags(domains)
            pinned = False
            for w, v in found.values.items():
                pinned |= self._narrow_domain(w, v, v, tags, frozenset((v,)))
            return pinned
        finally:
            self.case_split_seconds += time.perf_counter() - start

    def _rule_c_group(self, x: Var) -> tuple[dict, list[int]] | None:
        """Rule C's scan: (each variable's set of values, coupling premise ids) for x.

        A coupling premise mentions, under the solved equations, two or more
        variables, each with a set of three values; x's group is what such
        premises reach from x. C is sound for any subset of the premises;
        the whole group matters for completeness only. None if there is no
        coupling premise, or more than CASE_SPLIT_GROUP_CAP cases.
        """
        dom = {x: sorted(self._domains[x].values)}
        cases = len(dom[x])
        coupling: list[int] = []
        seen: set[int] = set()  # taken or not, each premise is looked at once
        todo = [x]
        while todo:
            for i in self._coi_premise_ids(todo.pop()):
                if i in seen:
                    continue
                seen.add(i)
                # The syntax first, so a flag that gates many data premises
                # does not expand them all.
                if not all(self._three_valued(v) for v in self._vars_now(i)):
                    continue
                vs = self._vars_from_key(i)
                if len(vs) < 2 or not all(self._three_valued(v) for v in vs):
                    continue  # a domain premise, or one that cancelled down
                coupling.append(i)
                for w in vs - dom.keys():
                    dom[w] = sorted(self._domains[w].values)
                    cases *= len(dom[w])
                    todo.append(w)
                if cases > CASE_SPLIT_GROUP_CAP:
                    self.case_split_capped += 1
                    return None
        return (dom, coupling) if coupling else None

    # ------------------------------------------------------------ work list

    def _enqueue(self, ids: Iterable[int]) -> None:
        """Queue premises for propagate(); outside it, keep them for the next call."""
        if self._queue is None:
            self._pending.update(ids)
            return
        for i in ids:
            if i not in self._queued:
                self._queued.add(i)
                self._queue.append(i)

    def _requeue_premises_of(self, vs: Iterable[Var]) -> None:
        """Queue every premise that mentions one of ``vs`` (see _enqueue)."""
        for v in vs:
            self._enqueue(self._coi_premise_ids(v))

    # ------------------------------------------------------------ helpers

    def _var(self, name: str) -> Var:
        """The Var of a name; a fresh variable's name is a caller error."""
        try:
            return self.table.var(name)
        except KeyError as exc:
            raise UndefinedVariable(str(exc)) from None

    def _plain(self, name: str) -> P.Poly:
        """Lookup for expanding: a name is its variable, or its solved value."""
        v = self._var(name)
        if v in self._solved:
            return self._solved[v]
        return P.var_poly(v)

    def _as_written(self, name: str) -> P.Poly:
        """Lookup that ignores the solved equations: a name is its variable."""
        return P.var_poly(self._var(name))

    def _apply_solved(self, a: P.Poly) -> P.Poly:
        """``a`` with every solved variable replaced by its value."""
        if not self._solved:
            return a
        return P.substitute(a, self._solved.get, self.p, self.max_terms)

    def _solved_tags(self, vs) -> tuple[str, ...]:
        return tuple(
            sorted({t for v in vs if v in self._solved for t in self._solved_tag[v]})
        )

    def _solved_tags_of(self, e: Expr) -> tuple[str, ...]:
        """Tags of the solved equations that rewrite the expression ``e``."""
        if not self._solved:
            return ()
        return self._solved_tags(self._var(n) for n in variables(e))

    def _declared_vars(self, e: Expr, what: str) -> list[Var]:
        """The Vars of ``e``; all must be declared (premises and ranges only)."""
        out = []
        for n in variables(e):
            v = self._var(n)
            if v not in self.declared:
                raise UndefinedVariable(f"{what} mentions undeclared {n}")
            out.append(v)
        return out
