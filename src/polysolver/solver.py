"""PolySolver: decides  P and R and Defs |= (q = 0)  over F_p. Sound, incomplete.

- P: premises, polynomials each read as "= 0".
- R: ranges lo <= x <= hi on the integer representative of a variable.
- Defs: definitions for variables that are not declared.
- Solved: equations x = t for declared x, each checked when added (add_solved).

The answer is ``Implied`` (with a reason) or ``Unknown``. There is no
"not implied": Unknown only means no rule applied.

Solved equations. A premise is trusted; a solved equation is not: add_solved
first checks that x = t follows from what is already known, exactly as a
query would be checked. Only then is x replaced by t, in the premises (as
the rules see them) and in every later query. The caller picks which
equations to try and in what order (e.g. the substitutions powdr recorded);
the solver only checks them. Defs differ: they name fresh variables, so they
need no check, and no premise can mention them.

The solver finds equations by itself only when the caller asks, in two ways.
solve_constants: a premise that, under the solved equations, mentions one
variable linearly pins it; each such equation goes through add_solved.
solve_one_hot: ranges derived from the premises (below). A range whose bounds
meet (lo = hi), derived or given, says x = lo; it follows from trusted
premises and ranges, so x is replaced by lo at once, without a check.

One-hot pass (solve_one_hot). Each step is sound on its own:
- B: a premise that reduces to x^2 - x gives 0 <= x <= 1 (F_p has no zero
  divisors).
- G: a premise x_1 + ... + x_n - c with c in {0, 1} and every x_i in [0, 1].
  As n < p, the integer sum is c: with c = 0 every x_i is 0, a single member
  is c, and otherwise exactly one x_i is 1 (a group).
- Sel: a linear premise w_0 + sum w_x * x over members of one group comes to
  w_0 + w_j for the member j that is 1, so w_j = -w_0. Every member whose
  weight (0 if absent) differs is 0; if only one member is left, it is 1.

Rules, cheapest first:
- N (normalize): q has the same zero key as one premise.
- S (no-wrap split): a premise G * (c1*a1 + ... + cn*an) with ranged a_i whose
  weighted sum cannot wrap past p implies G * a_j = 0 for every j.

The solver knows nothing about circuits: only variables, polynomials,
ranges and definitions.
"""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Iterable
from dataclasses import dataclass, field

from . import poly as P
from .defs import NO_DEFS, Defs, InvalidDefs, Opaque
from .expr import Expr, product_factors, variables
from .table import Var, VarTable

BABYBEAR = 2013265921


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
    # Rule S's view, computed on first use: the top-level factors as written,
    # their expansions (filled in only as needed), and which ones are sums.
    factors: list | None = None  # the expressions of the top-level * chain
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
    ):
        self.table = table
        self.p = p
        self.max_terms = max_terms
        self.declared: frozenset[Var] = frozenset(table.var(n) for n in declared)
        self._premises: list[_Premise] = []
        # Premise index for rule N: variable -> ids of the premises that mention it.
        # Built from the syntax alone, so adding a premise costs no expansion.
        self._by_var: dict[Var, list[int]] = defaultdict(list)
        self._ranges: dict[Var, tuple[int, int, list[str]]] = {}  # v -> (lo, hi, tags)
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
        self._version = 0  # bumped on every substitution; stales premise caches
        # One-hot pass: the premises that are groups, and variable -> its groups.
        self._groups: set[int] = set()
        self._group_index: dict[Var, set[int]] = defaultdict(set)
        self._collapsed: list[Var] = []  # ranges with lo = hi, not yet substituted
        # solve_one_hot's work list, only while it runs.
        self._queue: deque[int] | None = None
        self._queued: set[int] = set()
        self.premises_expanded = 0  # premise keys computed (rule N)
        self.premises_split = 0  # premises split into factors (rule S)
        self.solved_accepted = 0  # add_solved calls accepted (also values equal to a pin)
        self.solved_rejected = 0  # add_solved calls whose check failed
        self.constants_solved = 0  # equations added by solve_constants
        self.pinned = 0  # variables replaced because their range collapsed
        self.solved_log: list[tuple[str, Verdict]] = []  # (tag, verdict) per add_solved call

    # ------------------------------------------------------------ inputs

    def add_premise(self, e: Expr, tag: str) -> None:
        """Assert ``e = 0``. Trusted: the caller vouches for it."""
        vs = self._declared_vars(e, "premise")
        idx = len(self._premises)
        prem = _Premise(tag, e, frozenset(vs))
        self._premises.append(prem)
        # Index by the variables as written. Nothing is expanded here: rule N
        # and rule S expand a premise only when a query first needs it.
        for v in vs:
            self._by_var[v].append(idx)
        self._unknown.clear()  # an earlier Unknown might now be provable

    def add_range(self, x: str, lo: int, hi: int, tag: str) -> None:
        """Assert ``lo <= x <= hi``; a second range on x intersects with the first.

        If the bounds meet, x is replaced by that value from now on.
        """
        if not 0 <= lo <= hi < self.p:
            raise ValueError(f"bad range [{lo}, {hi}] for {x}")
        (v,) = self._declared_vars(x, "range")
        self._reduce_range(v, lo, hi, [tag])
        self._substitute_collapsed()

    def add_solved(self, x: str, t: Expr, tag: str) -> Verdict:
        """Check that ``x = t`` is implied; if so, replace x by t from now on.

        x must be declared. The check is an ordinary query of x - t against
        the current state. On Implied, x is replaced by t in the premises (as
        the rules see them), in earlier solved equations and in all later
        queries. On Unknown nothing changes: the equation is rejected, which
        costs completeness only. If x is already solved (e.g. pinned by
        solve_one_hot), the query compares its value with t, and an Implied
        verdict also changes nothing. Every verdict goes into ``solved_log``.
        """
        verdict = self._add_solved(x, t, tag)
        self.solved_log.append((tag, verdict))
        return verdict

    def _add_solved(self, x: str, t: Expr, tag: str) -> Verdict:
        (xv,) = self._declared_vars(x, "solved variable")
        self._declared_vars(t, "solved value")
        try:
            rhs = P.expand(t, self._plain, self.p, self.max_terms)
        except P.ExpansionLimit:
            return self._reject("expansion limit", "expansion-limit")
        if xv in self._solved:
            k = P.zkey(P.add(self._solved[xv], rhs, self.p, -1), self.p)
            verdict = self._decide(k)
            if not isinstance(verdict, Implied):
                return self._reject(f"{x} is already solved", "already-solved")
            self.solved_accepted += 1
            return verdict
        # t must not mention x, or "replace x by t" would not remove x.
        if xv in P.variables_of(rhs):
            return self._reject(f"{x} occurs in its own value", "not-solved")
        k = P.zkey(P.add(P.var_poly(xv), rhs, self.p, -1), self.p)
        verdict = self._decide(k)
        if not isinstance(verdict, Implied):
            return self._reject(verdict.note, verdict.kind)
        try:
            self._substitute(xv, rhs, (tag,))
        except P.ExpansionLimit:
            return self._reject("expansion limit (back-substitution)", "expansion-limit")
        self.solved_accepted += 1
        return verdict

    def _substitute(self, xv: Var, rhs: P.Poly, tags: tuple[str, ...]) -> None:
        """Replace x by rhs from now on; rhs is fully reduced and does not mention x.

        Earlier solved values that mention x get x replaced too, so every value
        stays free of solved variables. They are all computed before anything
        changes, so an expansion limit leaves no trace.
        """

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
        self._version += 1  # premise keys and splits are now stale
        self._unknown.clear()  # an earlier Unknown might now be provable

    def _reduce_range(self, v: Var, lo: int, hi: int, tags: list[str]) -> bool:
        """Intersect v's range with [lo, hi]; True if that narrowed it.

        An empty intersection means the premises contradict each other; the
        range is then left as it was. When the bounds meet, v is queued for
        _substitute_collapsed (the listener).
        """
        old_hi = None
        if v in self._ranges:
            # Both ranges hold, so v lies in their intersection.
            old_lo, old_hi, old_tags = self._ranges[v]
            new_lo, new_hi = max(lo, old_lo), min(hi, old_hi)
            if new_lo > new_hi or (new_lo, new_hi) == (old_lo, old_hi):
                return False
            lo, hi, tags = new_lo, new_hi, old_tags + tags
        self._ranges[v] = (lo, hi, list(tags))
        self._unknown.clear()
        if hi <= 1 and (old_hi is None or old_hi > 1):
            self._requeue_vars([v])  # newly in [0, 1]: a premise over v may be a group now
        if lo == hi and v not in self._solved:
            self._collapsed.append(v)
        return True

    def _substitute_collapsed(self) -> None:
        """Replace every variable whose range collapsed to one value by that value."""
        while self._collapsed:
            v = self._collapsed.pop()
            if v in self._solved:
                continue
            lo, _, tags = self._ranges[v]
            # Taken before v is replaced: afterwards _occurs_in no longer lists it.
            again = self._mentioning(v) if self._queue is not None else ()
            self._substitute(v, P.const(lo, self.p), tuple(dict.fromkeys(tags)))
            self.pinned += 1
            self._enqueue(again)

    def solve_constants(self) -> int:
        """Solve every premise that pins one variable to a constant; return how many.

        A premise that, under the solved equations, is c*x + k (one variable,
        degree 1, c a nonzero constant) gives x := -k/c. Each new constant can
        turn more premises into such pins (pc1 - pc0 - 4 once pc0 is known), so
        the premises that mention x are looked at again, until none gives a new
        one. Like z3's solve-eqs restricted to constant values, but only when the
        caller asks. Every equation goes through add_solved, so it is checked
        like any other; the premise it came from is its tag.
        """
        added = 0
        todo = list(range(len(self._premises)))
        queued = set(todo)
        while todo:
            i = todo.pop()
            queued.discard(i)
            pin = self._as_pin(self._premise_key(i))
            if pin is None:
                continue
            xv, value = pin
            x = self.table.name(xv)
            # Look again at what mentions x, computed before x is replaced.
            again = self._mentioning(xv)
            if isinstance(self.add_solved(x, value, tag=self._premises[i].tag), Implied):
                added += 1
                self.constants_solved += 1
                for j in again:
                    if j not in queued:
                        queued.add(j)
                        todo.append(j)
        return added

    def solve_one_hot(self) -> int:
        """Derive ranges by steps B, G and Sel (module docstring); return how many pinned.

        A work list: every premise is looked at once, then again whenever
        something it depends on changes: one of its variables gets a range
        within [0, 1], joins a group, or is replaced by its value. Ranges only
        shrink and a variable is replaced at most once, so the list runs empty,
        and then no premise can give anything new. A premise is expanded only
        if its variables, as it reads now, could fit a step: one variable (B),
        or all of them within [0, 1] (G, Sel). Expansion never adds variables,
        so only a cancellation can hide a step from this screen.
        """
        before = self.pinned
        n = len(self._premises)
        self._queue, self._queued = deque(), set()
        try:
            # One-variable premises first: they hold the x^2 - x that G needs.
            self._enqueue(i for i in range(n) if len(self._premises[i].vars) == 1)
            self._enqueue(range(n))
            while self._queue:
                i = self._queue.popleft()
                self._queued.discard(i)
                self._one_hot_step(i)
                self._substitute_collapsed()
        finally:
            self._queue = None
        return self.pinned - before

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

    def _reject(self, note: str, kind: str) -> Unknown:
        self.solved_rejected += 1
        return Unknown(note, kind)

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
                return self._reduce(defs.polys[v])
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
        # a solved value (_mentioning): looking up one of them is enough.
        # Pick the rarest one, so we expand as few premises as possible.
        v = min(P.key_vars(k), key=lambda x: len(self._mentioning(x)))
        for i in self._mentioning(v):
            if self._premise_key(i) == k:
                prem = self._premises[i]
                return Implied(
                    "normalize", (prem.tag,), solved=self._solved_tags_of(prem.expr)
                )
        return Unknown("N: no premise with this normal form")

    def _mentioning(self, v: Var) -> list[int]:
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

    def _fresh(self, prem: _Premise) -> _Premise:
        """Drop the premise's derived data if solved equations changed since."""
        if prem.version != self._version:
            prem.version = self._version
            prem.key, prem.expanded = None, False
            prem.factors, prem.polys, prem.sums = None, {}, None
        return prem

    def _premise_key(self, i: int) -> P.Key | None:
        """The premise's zero key, expanded on first use and then cached."""
        prem = self._fresh(self._premises[i])
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

    # ------------------------------------------------------------ rule S

    def _premise_sums(self, i: int) -> list:
        """The premise's top-level factors that are sums c1*a1 + ... + cn*an.

        Computed on first use and cached, so only premises that rule S actually
        looks at are ever split. Each factor is fully expanded, so a factor that
        becomes a sum only after cancellation (x*y - x*y + a + b) is still found.
        """
        prem = self._fresh(self._premises[i])
        if prem.sums is None:
            self.premises_split += 1
            prem.factors = product_factors(prem.expr)
            prem.sums = []
            for fi, f in enumerate(prem.factors):
                # Expansion never adds variables, so fewer than 2 means never a sum.
                if len(variables(f)) < 2:
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
            if a not in self._ranges:  # an unranged a can never pass the bound
                continue
            # A premise whose sum contains a mentions a, directly or through a
            # solved value, so _mentioning finds every candidate (as in rule N).
            for idx in self._mentioning(a):
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
        missing = [self.table.name(v) for ((v, _),) in s if v not in self._ranges]
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
            sum(c * k % self.p * self._ranges[v][1] for ((v, _),), c in s.items())
            for k in scales
        )
        if bound >= self.p:
            return "nowrap-bound", f"sum of c_i * hi_i is {bound} >= p"
        return None

    # ------------------------------------------------------------ one-hot pass

    def _one_hot_step(self, i: int) -> None:
        """Steps B, G and Sel for premise i, as it reads under the solved equations."""
        vs = self._current_vars(i)
        if not vs or (len(vs) > 1 and not all(self._in_01(v) for v in vs)):
            return
        k = self._premise_key(i)
        x = self._boolean_var(k)
        if x is not None:
            self._reduce_range(x, 0, 1, self._premise_tags(i))
            return
        lin = self._linear(k)
        if lin is None or not lin[0]:
            return
        w, c0 = lin
        if self._is_group(w, c0):
            tags = self._premise_tags(i) + self._range_tags(w)
            if c0 == 0:  # no member is on
                for x in w:
                    self._reduce_range(x, 0, 0, tags)
            elif len(w) == 1:  # the one member left is on
                (x,) = w
                self._reduce_range(x, 1, 1, tags)
            elif i not in self._groups:
                self._groups.add(i)
                for x in w:
                    self._group_index[x].add(i)
                self._requeue_vars(w)  # their selectors can use this group now
        self._narrow_by_selector(i, w, c0)

    def _narrow_by_selector(self, i: int, w: dict[Var, int], c0: int) -> None:
        """Step Sel: premise i, c0 + sum w_x * x, over the members of a group."""
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
            tags += self._range_tags(members)
            for x in members:
                if x not in on:
                    self._reduce_range(x, 0, 0, tags)
            if len(on) == 1:
                self._reduce_range(on[0], 1, 1, tags)

    def _is_group(self, w: dict[Var, int], c0: int) -> bool:
        """Unit weights, constant 0 or -1 (a sum of 0 or 1), every member in [0, 1]."""
        return (
            set(w.values()) == {1}
            and c0 in (0, self.p - 1)
            and all(self._in_01(x) for x in w)
        )

    def _in_01(self, v: Var) -> bool:
        return v in self._ranges and self._ranges[v][1] <= 1

    def _premise_tags(self, i: int) -> list[str]:
        """Premise i's tag and those of the solved equations that rewrite it."""
        prem = self._premises[i]
        return [prem.tag, *self._solved_tags(prem.vars)]

    def _range_tags(self, vs: Iterable[Var]) -> list[str]:
        return [t for v in vs for t in self._ranges[v][2]]

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

    def _current_vars(self, i: int) -> set[Var]:
        """The variables premise i can mention under the solved equations."""
        out = set()
        for v in self._premises[i].vars:
            value = self._solved.get(v)
            if value is None:
                out.add(v)
            else:
                out |= P.variables_of(value)
        return out

    def _enqueue(self, ids: Iterable[int]) -> None:
        """Queue premises for solve_one_hot; nothing outside it."""
        if self._queue is None:
            return
        for i in ids:
            if i not in self._queued:
                self._queued.add(i)
                self._queue.append(i)

    def _requeue_vars(self, vs: Iterable[Var]) -> None:
        """Queue every premise that mentions one of ``vs``; nothing outside solve_one_hot."""
        if self._queue is None:
            return
        for v in vs:
            self._enqueue(self._mentioning(v))

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

    def _reduce(self, a: P.Poly) -> P.Poly:
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
