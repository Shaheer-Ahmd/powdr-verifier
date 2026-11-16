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
    The integer sum is in [0, n] and n < p (the constructor requires
    max_terms < p), so it is c: with c = 0 every x_i is 0, a single x_1 is
    c, and otherwise exactly one x_i is 1 (the premise is a group).
  - selector part: a premise w_0 + sum w_x * x over members of a group
    reads w_0 + w_j for the member j that is 1. Every member whose weight
    (0 if absent) is not -w_0 is 0; if one member is left, it is 1.
- C (case split): premises Q over variables that each have a finite set of
  values. Every model, restricted to the variables of Q, is a solution of Q
  over those sets, so x = v holds if every solution has x = v
  (enumeration.fixed_values). Leaving premises out of Q loses completeness
  only.
- S' (no-wrap pins): rule S below with G = 1, for the terms a domain can
  hold. A premise over ranged variables that reads as a sum of non-negative
  terms whose integer value cannot reach p gives a_i = 0 for each linear
  term, and x = -t/w for each square (w*x + t)^2 over one variable.
- Collapse: a domain with one value v gives x = v, which goes into Sol.
- Checked equation: x = t (add_solved) goes into Sol only once rule N or S
  proves x - t.
A contradiction (an empty domain, no group member left that can be 1, C
with no solution) means P and R have no model, so anything follows. The
policy is to use nothing (C's are counted).

Rules that answer a query, q rewritten under Sol and Defs, cheapest first:
- N (normalize): q has the same zero key as a premise, so they differ by a
  nonzero factor.
- S (no-wrap split): a premise G * (sum c_i*a_i + sum c_j*L_j^2), each L_j
  an affine form w.x + t, over ranged variables. With every c as its
  representative in [1, p) and every w and t as a signed integer, each term
  is a non-negative integer. If their sum cannot reach p (_no_wrap_terms),
  then where G != 0 the sum is 0, so every term is: the premise implies
  G * a_i = 0 and G * L_j = 0.
- L (sum), the reverse of S, with no side condition: q is written
  G * (t_1 + ... + t_n), and N or S proves G * t_j for every j. Then q, their
  sum, is 0.
- Quotients: q mentions f := Quotient(n, d), which is n / d if d != 0 and 0
  otherwise. Each f is resolved in the solver at hand: if d = 0 is implied,
  f = 0; if d is a unit (a nonzero constant, or in the nonzero index), rule U.
- Q (quotient split): some f is neither. Every model has d = 0 or d != 0,
  so q is asked again in two forks: one with the premise d = 0, one with d
  in the nonzero index. q Implied in both gives q. Each fork resolves f and
  splits on any other open quotient itself (at most QUOTIENT_CAP deep).
- U (unit cancel): every f is resolved and d is a unit for some. Such an f
  is n * inv(d), an inverse atom (poly.py). clear_denominators, given the
  nonzero index, clears it by multiplying q by d (only for a d in the
  index; without it nothing is cleared): if q = q1 * f + q0, the key is that of
  d * q = q1 * n + q0 * d. Implied gives d * q = 0, and q = 0 as d != 0 and
  F_p has no zero divisors. An inverse atom may occur only to the first
  power. If some e in the nonzero index has e = 0 implied, the fork has no
  model, and any query with a quotient holds there ("trivial").

The fork for an assumption a = 0 or a != 0 (_assuming) is a child solver
holding a slice of this one's store (premises near the query, the solved
equations they mention, the domains of their variables, the nonzero index)
plus the assumption: the premise a, or a in the nonzero index. Every copied
fact holds in every model of P and R (I), so every model of P and R with
the assumption is a model of the fork's inputs, and a fork verdict holds
there. In a fork, I reads: every model of P, R and the fork's assumptions.
Any slice is sound; a smaller one loses completeness only. Fork verdicts
serve one query and never enter this solver's caches.

The contract that keeps each rule local:
- D, O and C change the store only through _narrow_domain, with tags
  naming every premise and domain they read (_premise_tags, _domain_tags).
  O's group index only says where its selector part should look, and that
  part re-reads the group.
- _substitute is called only for pins (_substitute_pins) and for
  checked equations (_check_solved). An equation between several variables
  (a_i = b_i from a sum of squares) is therefore never a rule's conclusion:
  it is proposed, and rule S checks it like any other.

Triggers, which are scheduling only:
- add_premise: D on a premise that mentions one variable as written.
- The work list (_run_queue), run by propagate() and add_solved_all. It
  holds premises and equations, and empties the premises before each
  equation check:
  - premises: D, O and S' on every premise whose reading changed: added,
    rewritten by a substitution, or with a variable newly ranged, newly in
    [0, 1] or in a new group.
  - equations: checked by N and S, lowest index first. If x - t is Unknown
    and x is unsolved with a set of case_split_trigger values (a policy:
    the caller's, 3 by default), C searches x's group;
    if that pins anything, the equation is checked again after the pins
    (without C). A rejected equation waits on its variables and the
    premises that mention them. A substitution or a narrowed domain
    there puts it back on the list. The caller picks the equations and
    their order.

Termination: domains only shrink and a variable is substituted at most
once, so there are finitely many changes. Each one puts a waiting
equation back at most once, and an accepted one is done, so the work list
runs empty. C runs at most once per check, within CASE_SPLIT_GROUP_CAP
cases and CASE_SPLIT_NODE_CAP values tried.
"""

from __future__ import annotations

import heapq
import time
from collections import defaultdict, deque
from collections.abc import Iterable
from dataclasses import dataclass, field, replace
from typing import NamedTuple

from . import poly as P
from .defs import NO_DEFS, Defs, InvalidDefs, Opaque, Quotient
from .enumeration import GaveUp, NoSolution, fixed_values
from .expr import Expr, product_factors, sum_terms, variables
from .table import Var, VarTable

BABYBEAR = 2013265921
# Rule C gives up on a group with more cases than this, or a search that tries
# more values. keccak's largest group has 243 cases (five variables).
CASE_SPLIT_GROUP_CAP = 4096
CASE_SPLIT_NODE_CAP = 100_000
# Rule Q's fork takes the premises within this many hops of the query's
# variables, and declines over the cap. Any slice is sound.
FORK_HOPS = 1
FORK_PREMISE_CAP = 200
# Rule Q splits on each quotient's denominator: at most 2^cap cases.
QUOTIENT_CAP = 3


class UndefinedVariable(LookupError):
    """A variable is neither declared nor defined: a caller error."""


@dataclass(frozen=True)
class Implied:
    rule: str  # "trivial" | "normalize" | "nowrap-split" | "sum" | "quotient-split" | "unit-cancel"
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
    # "no-match", a near miss of rule S: "nowrap-missing-range", "nowrap-bound",
    # or "quotient": rule Q applied and one of its two cases was not proved.
    kind: str = "no-match"


Verdict = Implied | Unknown


class _Zero(NamedTuple):
    """A quotient's denominator d with d = 0 implied: f = 0."""

    verdict: Implied


class _Unit(NamedTuple):
    """A quotient's denominator d known nonzero: f = n / d (rule U).

    ``key`` is d's zero key as found in the nonzero index and ``tag`` the
    assumption's; both None for a nonzero constant.
    """

    key: P.Key | None
    tag: str | None


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


@dataclass
class _Equation:
    """One x = t of an add_solved_all call, while the work list runs."""

    x: Var
    t: Expr
    tag: str
    written: frozenset  # x and the variables of t, as written
    verdict: Verdict | None = None  # the latest check's
    agreed: bool = False  # accepted, and x already had that value
    rejected: bool = False  # some check was Unknown
    skip_c: bool = False  # C pinned for the last check: the next one goes without C
    # What it waits on while rejected: variables and premise ids.
    wait_vars: frozenset = frozenset()
    wait_premises: frozenset = frozenset()


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
        case_split_trigger: int = 3,
        nowrap_pins: bool = True,
    ):
        # Rule O's group part needs n < p for a sum of n variables. A key has
        # at most max_terms terms, so this makes it hold.
        if max_terms >= p:
            raise ValueError(f"max_terms ({max_terms}) must be below p ({p})")
        if case_split_trigger < 2:
            raise ValueError(f"case_split_trigger ({case_split_trigger}) must be at least 2")
        self.table = table
        self.p = p
        self.max_terms = max_terms
        # Switches: rule D's pins from x - c (constants), rule D's sets of
        # several values and rule O (one_hot), add_solved's rule C (case_split).
        self._use_constants, self._use_one_hot = constants, one_hot
        self._use_case_split = case_split
        self._use_nowrap_pins = nowrap_pins  # rule S'
        # Rule C's policy: which equations start a search (x has a set of
        # this many values). The search itself takes any finite sets.
        self.case_split_trigger = case_split_trigger
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
        # The work list's premises while it runs; between runs, what the next
        # one must look at (new premises, and those that ranges and pins changed).
        self._queue: deque[int] | None = None
        self._queued: set[int] = set()
        self._pending: set[int] = set()
        # Its equations, during an add_solved_all call: a heap of the indices
        # to check, and the rejected ones, indexed by what they wait on.
        self._eqs: list[_Equation] = []
        self._eq_ready: list[int] = []
        self._eq_queued: set[int] = set()
        self._waiting: set[int] = set()
        self._waiting_on_var: dict[Var, set[int]] = defaultdict(set)
        self._waiting_on_premise: dict[int, set[int]] = defaultdict(set)
        self.premises_expanded = 0  # premise keys computed (rule N)
        self.premises_split = 0  # premises split into factors (rule S)
        self.solved_accepted = 0  # equations accepted (also values equal to a pin)
        self.solved_agreed = 0  # of those, x already had that value: nothing changed
        self.solved_rejected = 0  # equations whose last check failed
        self.solved_rechecks = 0  # checks of an equation put back after a reject
        self.solved_on_retry = 0  # of the accepted, those rejected first
        self.constants_solved = 0  # variables pinned by a premise x - c
        self.pinned = 0  # variables pinned otherwise (a collapsed domain)
        self.propagate_pins: list[int] = []  # variables pinned by each propagate() call
        self.case_splits = 0  # groups rule C searched
        self.case_split_nodes = 0  # values it tried, over all its searches
        self.case_split_capped = 0  # groups or searches over the caps
        self.case_split_unsat = 0  # searches with no fit: the premises contradict each other
        self.case_split_seconds = 0.0  # its own time
        self.nowrap_pins = 0  # variables rule S' pinned
        self.forks = 0  # child solvers made for rule Q
        # Inverse atoms (poly.py): I -> the monic polynomial D it is the
        # inverse of, and D's zero key -> I. A definition only: it says
        # nothing about D being nonzero (that is the nonzero index). No
        # premise, solved value or domain mentions an atom. Shared with forks.
        self._inverse_of: dict[Var, P.Poly] = {}
        self._atom_for: dict[P.Key, Var] = {}
        # Polynomials assumed nonzero (rule Q's d != 0 fork), with the
        # assumption's tag: rule U reads them. Empty outside a fork.
        self._nonzero: list[tuple[P.Poly, str]] = []
        self._q_depth = 0  # how many rule Q forks deep this solver is
        # (tag, last verdict, agreed with x's value) per equation, in call order
        self.solved_log: list[tuple[str, Verdict, bool]] = []

    # ------------------------------------------------------------ inputs

    def add_premise(self, e: Expr, tag: str) -> None:
        """Assert ``e = 0``. Trusted: the caller vouches for it.

        A premise that mentions one variable x as written gives x's domain at
        once (rule D). The work list reads it again, as it reads any premise:
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
        self._pending.add(idx)  # for the next work-list run
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
        """add_solved_all with the one equation ``x = t``."""
        return self.add_solved_all([(x, t, tag)])[0]

    def add_solved_all(self, eqs: Iterable[tuple[str, Expr, str]]) -> list[Verdict]:
        """Check each ``x = t`` (given as ``(x, t, tag)``); replace x by t once implied.

        Each x must be declared. A check is an ordinary query of x - t
        against the current state, run by the work list after its premises
        are done, lowest index first. On Implied, x is replaced by t in the
        premises (as the rules see them), in earlier solved equations and in
        all later queries, and D and O look at the premises that changed. If
        x is already solved (e.g. pinned), the query compares its value with
        t, and an Implied verdict changes nothing. If the check is Unknown
        and x has a set of case_split_trigger values, rule C searches x's
        group (any variables with finite sets, within the cap); if that
        pins anything, x = t is checked again (C's pins stay either way). An
        equation still Unknown waits, and is checked again when one of its
        variables, or a premise that mentions one, is rewritten or has a
        domain narrowed; in this call only. Rejected in the end costs
        completeness only. An Implied verdict names the solved equations that
        rewrote x - t, so an equation that agrees with a pin from C names the
        premises behind it. Returns the last verdict of each, in order, and
        logs them in ``solved_log`` with whether x already had that value.
        """
        batch = []
        for x, t, tag in eqs:
            (xv,) = self._declared_vars(x, "solved variable")
            vs = self._declared_vars(t, "solved value")
            batch.append(_Equation(xv, t, tag, frozenset((xv, *vs))))
        self._eqs = batch
        self._eq_ready = list(range(len(batch)))  # sorted, so already a heap
        self._eq_queued = set(self._eq_ready)
        try:
            self._run_queue()
        finally:
            self._eqs, self._eq_ready, self._eq_queued = [], [], set()
            self._waiting.clear()
            self._waiting_on_var.clear()
            self._waiting_on_premise.clear()
        for e in batch:
            if isinstance(e.verdict, Unknown):
                self.solved_rejected += 1
            self.solved_log.append((e.tag, e.verdict, e.agreed))
        return [e.verdict for e in batch]

    def _check_equation(self, j: int) -> None:
        """One check of equation j, for the work list: accept it, or let it wait."""
        e = self._eqs[j]
        if e.rejected:
            self.solved_rechecks += 1
        agreed = self.solved_agreed
        verdict = self._check_solved(e.x, e.t, e.tag)
        if (
            isinstance(verdict, Unknown)
            and not e.skip_c
            and self._use_case_split
            and e.x not in self._solved
            and self._starts_search(e.x)
            and self._rule_c(e.x)
        ):
            # Check again once C's pins are substituted and their premises read.
            e.skip_c = True
            self._ready(j)
            return
        e.skip_c = False
        e.verdict = verdict
        if isinstance(verdict, Implied):
            e.agreed = self.solved_agreed > agreed
            self.solved_on_retry += e.rejected
            return
        e.rejected = True
        self._wait(j)

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
        mention x read differently now, so the work list looks at them again,
        and at the waiting equations that read them or x.
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
        self._wake(again, (xv,))

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
        elif old is None and self._use_nowrap_pins:
            self._requeue_premises_of([v])  # newly ranged: a sum over v may not wrap now
        if self._waiting:  # rules S and C read domains
            self._wake(self._coi_premise_ids(v), (v,))
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
        """Run the work list until it is empty: premises first, then one equation.

        Every premise is looked at once, then again whenever something it
        depends on changes: one of its variables gets a domain within [0, 1],
        joins a group, or is replaced by its value. Between runs, new
        premises, ranges and their pins queue the premises they change for
        the next one.
        Domains only shrink and a variable is replaced at most once, so the
        premises run out, and then none can give anything new. A premise is
        expanded only if its variables, as it reads now, could fit a rule:
        one variable (D), or all of them within [0, 1] (O); _vars_now says
        when they are read off the key instead.

        Only then is the next equation of add_solved_all checked, so each
        check sees what D and O made of every earlier one.
        """
        todo, self._pending = sorted(self._pending), set()
        self._queue, self._queued = deque(), set()
        try:
            # One-variable premises first: they hold the x^2 - x that O needs.
            self._enqueue(i for i in todo if len(self._premises[i].vars) == 1)
            self._enqueue(todo)
            while True:
                while self._queue:
                    i = self._queue.popleft()
                    self._queued.discard(i)
                    self._propagate_premise(i)
                    self._substitute_pins()
                if not self._eq_ready:
                    break
                j = heapq.heappop(self._eq_ready)
                self._eq_queued.discard(j)
                self._check_equation(j)
                self._substitute_pins()  # rule C's
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

    def make_defs(self, mapping: dict[str, Expr | Opaque | Quotient]) -> Defs:
        """Validate definitions (D1 fresh, D2 flat, D3 polynomial, quotient or opaque)."""
        polys, opaque, quotients = {}, set(), {}

        def as_written(name: str, rhs: Expr) -> P.Poly | None:
            for n in variables(rhs):  # raises UnsupportedExpr outside the grammar
                if self._var(n) not in self.declared:  # also rules out chains
                    raise InvalidDefs(f"D2: {name} := ... mentions undeclared {n}")
            # Stored as written: implies applies the solved equations on use,
            # so the Defs stay valid when more equations are solved later.
            try:
                return P.expand(rhs, self._as_written, self.p, self.max_terms)
            except P.ExpansionLimit:
                return None  # queries through the variable report the limit

        for name, rhs in mapping.items():
            v = self._var(name)
            if v in self.declared:
                raise InvalidDefs(f"D1: {name} is declared, it cannot be defined")
            if isinstance(rhs, Opaque):
                opaque.add(v)
            elif isinstance(rhs, Quotient):
                n, d = as_written(name, rhs.n), as_written(name, rhs.d)
                quotients[v] = None if n is None or d is None else (n, d)
            else:
                polys[v] = as_written(name, rhs)
        return Defs(polys, frozenset(opaque), id(self.table), quotients)

    def extend_defs(self, defs: Defs, name: str, rhs: Expr | Opaque | Quotient) -> Defs:
        """``defs`` with ``name := rhs`` added (or replaced), validated like make_defs.

        Only the new right-hand side is expanded, so a caller trying several
        values for one variable does not pay for the rest each time.
        """
        one = self.make_defs({name: rhs})
        if defs is NO_DEFS:
            return one
        if defs.owner != id(self.table):
            raise ValueError("defs were made by a solver with another table")
        v = self._var(name)
        polys = {x: t for x, t in defs.polys.items() if x != v}
        polys.update(one.polys)
        quotients = {x: t for x, t in defs.quotients.items() if x != v}
        quotients.update(one.quotients)
        return Defs(polys, (defs.opaque - {v}) | one.opaque, defs.owner, quotients)

    # ------------------------------------------------------------ query

    def implies(self, q: Expr, defs: Defs = NO_DEFS) -> Verdict:
        """Is ``q = 0`` implied? ``q`` itself is never modified."""
        if defs is not NO_DEFS and defs.owner != id(self.table):
            raise ValueError("defs were made by a solver with another table")
        names = variables(q)
        # Sort q's non-declared variables into defined (used), quotient and
        # opaque ones; anything else is a caller error.
        used, opaque, quotients = [], [], []
        for n in sorted(names):
            v = self._var(n)
            if v in self.declared:
                continue
            if not defs.defines(v):
                raise UndefinedVariable(f"{n} is neither declared nor defined")
            kind = opaque if v in defs.opaque else quotients if v in defs.quotients else used
            kind.append(n)
        if opaque:
            return Unknown(f"opaque: {', '.join(opaque)}", "opaque")
        if quotients:
            return self._rule_quotients(q, defs, quotients, used, names)

        try:
            k = P.zkey(P.expand(q, self._expander(defs), self.p, self.max_terms), self.p)
        except P.ExpansionLimit:
            return Unknown("expansion limit", "expansion-limit")

        # Queries with the same key are the same question; answer once.
        verdict = self._implied.get(k) or self._unknown.get(k)
        if verdict is None:
            verdict = self._decide(k)
            if isinstance(verdict, Unknown):
                # Rule L reads q as written. Its verdict is about q's zeros, so
                # it serves every query with this key.
                by_sum = self._rule_l(q, defs)
                if isinstance(by_sum, Implied):
                    verdict = by_sum
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

    def linear_root(self, e: Expr, x: str, defs: Defs = NO_DEFS) -> int | None:
        """The value of ``x`` that makes ``e`` zero, if ``e`` reads a*x + c with a != 0.

        ``e`` is read under the Defs and the solved equations, with ``x`` a
        plain variable; a and c must be constants. For proposing candidates
        only, like normal_form: a caller that uses the value must still have
        it checked.
        """
        nf = self.normal_form(e, defs, free=[x])
        if nf is None:
            return None
        lin = ((self._var(x), 1),)
        a = c = 0
        for m, k in nf:
            if m == ():
                c = k
            elif m == lin:
                a = k
            else:
                return None
        if not a:
            return None
        return -c * pow(a, self.p - 2, self.p) % self.p

    def interval(
        self, e: Expr, defs: Defs = NO_DEFS
    ) -> tuple[int, int, tuple[str, ...]] | None:
        """(lo, hi, ranged variables) with 0 <= lo <= e's representative <= hi < p, or None.

        ``e`` is read under the Defs and the solved equations. It must then be
        affine, c + sum w_i * x_i, with every x_i ranged. Reading each w_i and
        c as a signed integer, the integer sum lies in [lo, hi]; if that is
        within [0, p), the sum does not wrap, so it is e's representative.
        """
        nf = self.normal_form(e, defs)
        if nf is None:
            return None
        p = self.p

        def signed(c: int) -> int:
            return c - p if c > p // 2 else c

        lo = hi = 0
        used = []
        for m, k in nf:
            k = signed(k)
            if m == ():
                lo += k
                hi += k
                continue
            if len(m) != 1 or m[0][1] != 1:
                return None  # not affine
            v = m[0][0]
            d = self._domains.get(v)
            if d is None:
                return None
            lo += k * (d.lo if k > 0 else d.hi)
            hi += k * (d.hi if k > 0 else d.lo)
            used.append(self.table.name(v))
        if lo < 0 or hi >= p:
            return None
        return lo, hi, tuple(used)

    def premises_mentioning(self, name: str) -> list[Expr]:
        """The premises, as written, that mention the variable ``name``.

        For a caller that looks for a shape in the written form (e.g. the
        witness search reading f * (x_1' + ... + x_n') + c); not expanded.
        """
        return [self._premises[i].expr for i in self._by_var.get(self._var(name), [])]

    def _expander(self, defs: Defs, free: frozenset = frozenset()):
        """Expansion lookup: Defs (reduced on use), then the solved equations.

        A Var in ``free`` stays a plain variable (rule Q's quotient).
        """

        def lookup(n: str) -> P.Poly:
            v = self._var(n)
            if v in free:
                return P.var_poly(v)
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

    def _decide_cached(self, k: P.Key) -> Verdict:
        """_decide through the verdict caches (for the parts of rules L and Q)."""
        verdict = self._implied.get(k) or self._unknown.get(k)
        if verdict is None:
            verdict = self._decide(k)
            (self._implied if isinstance(verdict, Implied) else self._unknown)[k] = verdict
        return verdict

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
        """The premise's top-level factors that read as a sum of non-negative terms.

        Each is (factor position, {a_i: c_i}, squares): the factor is
        sum c_i * a_i + sum c_j * L_j^2 with L_j affine (_nonneg_terms), and
        has two terms or more, or a square. Computed on first use and cached,
        so only premises that rule S actually looks at are ever split. Each
        factor is fully expanded, so a factor that becomes a sum only after
        cancellation (x*y - x*y + a + b) is still found.
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
                terms = self._nonneg_terms(poly) if poly else None
                if terms is not None and (terms[1] or len(terms[0]) >= 2):
                    prem.sums.append((fi, *terms))
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
        """Rule S: q is G * T, where some premise is G * (a sum with the term T).

        The sum reads sum c_i * a_i + sum c_j * L_j^2 over ranged variables,
        and T is an a_i or an L_j. If the integer value of the sum cannot
        reach p (_no_wrap_terms), then in a model with G != 0 the sum is 0
        mod p, hence 0, hence every term is 0: a_i = 0 and L_j = 0. In a
        model with G = 0, G * T is 0 anyway. Only ranged variables of q can
        occur in T.
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
                for fi, linear, squares in sums:
                    term = self._term_with(a, linear, squares)
                    if term is None:
                        continue
                    g = self._other_factors_times(prem, fi, term)
                    # The shape must match q (up to a constant factor) first.
                    if g is None or P.zkey(g, self.p) != k:
                        continue
                    # The shape matches; only the no-wrap condition is left.
                    why = self._no_wrap_terms(linear, squares)
                    if why:
                        kind, msg = why
                        notes.append(f"{prem.tag}: {msg}")
                        continue
                    # Report every variable of the sum: all their ranges were used.
                    ranged = sorted(self.table.name(v) for v in self._term_vars(linear, squares))
                    return Implied(
                        "nowrap-split",
                        (prem.tag,),
                        tuple(ranged),
                        solved=self._solved_tags_of(prem.expr),
                    )
        return Unknown(
            "S: " + ("; ".join(notes) if notes else "no ranged sum premise"), kind
        )

    @staticmethod
    def _term_with(a: Var, linear: dict, squares: list) -> P.Poly | None:
        """The term of the sum that mentions a: a itself, or the affine form L_j."""
        if a in linear:
            return P.var_poly(a)
        for _, w, t in squares:
            if a in w:
                form = {((v, 1),): c for v, c in w.items()}
                if t:
                    form[()] = t
                return form
        return None

    @staticmethod
    def _term_vars(linear: dict, squares: list) -> set[Var]:
        return set(linear).union(*(w for _, w, _ in squares))

    def _other_factors_times(self, prem: _Premise, fi: int, term: P.Poly) -> P.Poly | None:
        """G * term, where G is the product of the premise's factors other than ``fi``."""
        g = term
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

    # ------------------------------------------------------------ rule L

    def _rule_l(self, q: Expr, defs: Defs) -> Verdict:
        """Rule L: q is written G * (t_1 + ... + t_n), and every G * t_j is implied.

        The reverse of rule S: there one premise G * sum gives each G * a_j
        (needing ranges); here the G * t_j, each proved by N or S, give
        G * sum. No side condition: q = sum of the G * t_j, and each is 0 in
        every model. Read off q's top-level factors as written; G is the
        product of the other factors, under the Defs and the solved equations.
        """
        factors = product_factors(q)
        if len(factors) < 2:
            return Unknown("L: not a product")
        lookup = self._expander(defs)
        try:
            polys = [P.expand(f, lookup, self.p, self.max_terms) for f in factors]
            for fi, f in enumerate(factors):
                terms = sum_terms(f)
                if len(terms) < 2:
                    continue
                g = P.const(1, self.p)
                for j, other in enumerate(polys):
                    if j != fi:
                        g = P.mul(g, other, self.p, self.max_terms)
                parts = []
                for sign, t in terms:
                    part = P.mul(g, P.expand(t, lookup, self.p, self.max_terms), self.p, self.max_terms)
                    v = self._decide_cached(P.zkey(part, self.p))
                    if not isinstance(v, Implied):
                        break
                    parts.append(v)
                else:
                    return self._merged("sum", parts)
        except P.ExpansionLimit:
            return Unknown("L: expansion limit", "expansion-limit")
        return Unknown("L: no factor is a sum of implied terms")

    @staticmethod
    def _merged(rule: str, parts: Iterable[Implied], premises: Iterable[str] = ()) -> Implied:
        """One verdict resting on everything ``parts`` rest on (and ``premises``)."""
        parts = list(parts)
        return Implied(
            rule,
            tuple(sorted({t for v in parts for t in v.premises} | set(premises))),
            tuple(sorted({t for v in parts for t in v.ranges})),
            solved=tuple(sorted({t for v in parts for t in v.solved})),
        )

    # ------------------------------------------------------------ rule Q

    def _rule_quotients(
        self, q: Expr, defs: Defs, quotients: list[str], used: list[str], names: set[str]
    ) -> Verdict:
        """q mentions quotients f := Quotient(n, d): resolve each f, or split (rule Q).

        Each f is read in this solver (with n and d under the solved equations):
        - zero: d = 0 is implied, so f = 0. In the fork for d = 0, rule N
          finds the assumption itself.
        - unit: d is a nonzero constant or in the nonzero index, so f = n / d
          (rule U).
        - open: neither. Rule Q splits on the first open f's d (two forks,
          each asked q again), so every f is resolved in some fork.
        Nothing is cached: the verdict depends on the definitions, not only
        on q's key.
        """
        if len(quotients) > QUOTIENT_CAP:
            return Unknown(
                f"Q: {len(quotients)} quotients, over the cap of {QUOTIENT_CAP}", "opaque"
            )
        fs = [self._var(n) for n in quotients]
        if any(defs.quotients[f] is None for f in fs):
            return Unknown("expansion limit", "expansion-limit")
        try:
            qp = P.expand(q, self._expander(defs, frozenset(fs)), self.p, self.max_terms)
            nds = [tuple(self._apply_solved(x) for x in defs.quotients[f]) for f in fs]
        except P.ExpansionLimit:
            return Unknown("expansion limit", "expansion-limit")
        vacuous = self._nonzero_contradicted()
        if vacuous is not None:  # no model is in this fork: anything holds
            return replace(vacuous, defs=tuple(sorted([*used, *quotients])))
        # One decision per quotient (_classify), and it is final: rule Q
        # runs on an open f, and rule U gets exactly the facts it found.
        sub: dict[Var, P.Poly] = {}
        zeros: list[Implied] = []  # the verdicts d = 0 of the zero quotients
        units: dict[P.Key, str] = {}  # the nonzero facts the units rest on
        opened = None
        for fname, f, (n, d) in zip(quotients, fs, nds):
            c = self._classify(d)
            if isinstance(c, _Zero):
                sub[f] = {}
                zeros.append(c.verdict)
            elif isinstance(c, _Unit):
                try:
                    sub[f] = P.mul(n, self._inverse(d), self.p, self.max_terms)
                except P.ExpansionLimit:
                    return Unknown("expansion limit", "expansion-limit")
                if c.key is not None:
                    units[c.key] = c.tag
            elif opened is None:
                opened = (fname, d)
        if opened is not None:
            verdict = self._rule_q(q, defs, names, *opened, nds)
        else:
            verdict = self._rule_u(qp, sub, zeros, units)
        if isinstance(verdict, Unknown):
            return verdict
        # n and d were read under the solved equations too.
        written = set().union(*(P.variables_of(x) for f in fs for x in defs.quotients[f]))
        mine = set(self._solved_tags(self._q_vars(names, defs) | written))
        return replace(
            verdict,
            defs=tuple(sorted([*used, *quotients])),
            solved=tuple(sorted(set(verdict.solved) | mine)),
        )

    def _rule_q(
        self, q: Expr, defs: Defs, names: set[str], fname: str, d: P.Poly, nds: list
    ) -> Verdict:
        """Rule Q: split on f's denominator d: q Implied in both forks gives q.

        One fork assumes d != 0 (nonzero index), the other d = 0 (a premise);
        every model of this solver is a model of one of them. Each fork is
        asked q again, so it resolves f (zero or unit) and splits on any
        other open quotient itself, at most QUOTIENT_CAP forks deep.
        """
        if self._q_depth >= QUOTIENT_CAP:
            return Unknown(f"Q: forks nested over the cap of {QUOTIENT_CAP}", "opaque")
        seeds = self._q_vars(names, defs)
        for n2, d2 in nds:
            seeds |= P.variables_of(n2) | P.variables_of(d2)
        parts, assumed = [], []
        for nonzero, case in ((True, "!= 0"), (False, "= 0")):
            tag = f"assume {fname}'s denominator {case}"
            fork = self._assuming(d, seeds & self.declared, tag, nonzero=nonzero)
            if fork is None:
                return Unknown(f"Q: case {fname}'s denominator {case}: fork over the cap", "quotient")
            v = fork.implies(q, defs)
            if not isinstance(v, Implied):
                # A decline inside the fork stays a decline; else the case failed.
                kind = v.kind if v.kind in ("opaque", "expansion-limit") else "quotient"
                return Unknown(f"Q: case {fname}'s denominator {case}: {v.note}", kind)
            parts.append(v)
            assumed.append(tag)
        return self._merged("quotient-split", parts, assumed)

    def _rule_u(
        self, qp: P.Poly, sub: dict, zeros: list[Implied], units: dict[P.Key, str]
    ) -> Verdict:
        """Rule U (unit cancel): every quotient is resolved; decide q.

        A unit f is n * inv(d). ``units`` holds the nonzero facts _classify
        found for them (zero key -> tag), and only those: clear_denominators
        clears inv(d) for a d among them, multiplying q by d, which keeps
        q's zeros because d != 0. A zero f is 0, resting on its verdict
        d = 0. With no unit this is rules N and S on q with every f = 0.
        """
        try:
            a = self._apply_solved(P.substitute(qp, sub.get, self.p, self.max_terms))
            atoms = P.variables_of(a) & self._inverse_of.keys()
            # As this solver reads them: a fork may have solved more since.
            inverse_of = {i: self._apply_solved(self._inverse_of[i]) for i in atoms}
            cleared = P.clear_denominators(a, inverse_of, units, self.p, self.max_terms)
        except P.ExpansionLimit:
            return Unknown("expansion limit", "expansion-limit")
        if cleared is None:
            return Unknown("U: an inverse occurs squared", "opaque")
        a, used = cleared
        left = P.variables_of(a) & atoms
        if left:
            names = ", ".join(sorted(self.table.name(i) for i in left))
            return Unknown(f"U: {names}: inverse of a polynomial not known nonzero", "quotient")
        v = self._decide_cached(P.zkey(a, self.p))
        if not isinstance(v, Implied):
            return Unknown(f"U: {v.note}", "quotient")
        rule = "unit-cancel" if used else v.rule
        return self._merged(rule, [v, *zeros], {units[k] for k in used})

    def _nonzero_contradicted(self) -> Implied | None:
        """Some e assumed nonzero has e = 0 implied: then this fork has no model.

        The verdict rests on e = 0 and the assumption's tag.
        """
        for e, tag in self._nonzero:
            try:
                k = P.zkey(self._apply_solved(e), self.p)
            except P.ExpansionLimit:
                continue
            v = self._decide_cached(k)
            if isinstance(v, Implied):
                v = self._with_solved_tags(v, P.variables_of(e))
                return replace(self._merged("trivial", [v], (tag,)), solved=v.solved)
        return None

    def _nonzero_keys(self) -> dict[P.Key, str]:
        """The nonzero index as it reads now: zero key -> the assumption's tag.

        Each entry is read under the solved equations (the fork may have
        solved more since the assumption).
        """
        out: dict[P.Key, str] = {}
        for e, tag in self._nonzero:
            try:
                k = P.zkey(self._apply_solved(e), self.p)
            except P.ExpansionLimit:
                continue
            if k != P.ZERO:
                out.setdefault(k, tag)
        return out

    def _classify(self, d: P.Poly) -> _Zero | _Unit | None:
        """What this solver knows of a denominator d (under Sol); None if nothing.

        The one place that decides between rule Q (None: open) and rule U.
        Zero first: a d both zero and assumed nonzero is caught before
        (_nonzero_contradicted).
        """
        k = P.zkey(d, self.p)
        zero = self._decide_cached(k)
        if isinstance(zero, Implied):
            return _Zero(zero)
        if P.is_constant(k):  # nonzero: no atom, nothing to clear
            return _Unit(None, None)
        tag = self._nonzero_keys().get(k)
        return None if tag is None else _Unit(k, tag)

    def _inverse(self, d: P.Poly) -> P.Poly:
        """``1 / d``: a constant if d is one, else c * I for the inverse atom I of D.

        d = c * D with D monic; I is shared by every d with the same zero
        key. Only a name: I * D = 1 is used only where D is known nonzero
        (rule U, through the nonzero index).
        """
        k = P.zkey(d, self.p)
        c_inv = pow(P.lead_coeff(d), self.p - 2, self.p)
        if P.is_constant(k):
            return P.const(c_inv, self.p)
        atom = self._atom_for.get(k)
        if atom is None:
            atom = self.table.fresh("inv")
            self._atom_for[k] = atom
            self._inverse_of[atom] = dict(k)
        return P.scale(P.var_poly(atom), c_inv, self.p)

    def _assuming(
        self, a: P.Poly, seeds: set[Var], tag: str, nonzero: bool = False
    ) -> PolySolver | None:
        """The fork for the assumption ``a = 0`` (or ``a != 0``): a child solver, or None over the cap.

        It gets, on the same table: the premises within FORK_HOPS of
        ``seeds`` (as written, with their tags), the solved equations those
        premises mention, the domains of the variables involved, this
        solver's nonzero index, and the assumption under ``tag``: the
        premise ``a``, or with ``nonzero`` the entry ``a`` in the nonzero
        index. Then its work list runs, and for ``a = 0`` the equations read
        off ``a``'s squares are checked (add_solved_all). Every copied
        fact holds in every model of this solver (invariant I), so every
        such model with the assumption is a model of the fork's inputs:
        what the fork proves holds in all of them. Leaving facts out is
        sound. A contradiction in the fork means no model has the
        assumption; nothing is made of that.
        """
        ids: set[int] = set()
        frontier, seen = set(seeds), set()
        for _ in range(FORK_HOPS):
            new = {i for v in frontier - seen for i in self._coi_premise_ids(v)} - ids
            seen |= frontier
            ids |= new
            if len(ids) > FORK_PREMISE_CAP:
                return None
            frontier = set()
            for i in new:
                frontier |= self._vars_under_solved(self._premises[i].vars)
        self.forks += 1
        child = PolySolver(
            self.table,
            (),
            self.p,
            self.max_terms,
            self._use_constants,
            self._use_one_hot,
            self._use_case_split,
            self.case_split_trigger,
            self._use_nowrap_pins,
        )
        child.declared = self.declared
        child._inverse_of, child._atom_for = self._inverse_of, self._atom_for
        child._nonzero = list(self._nonzero)
        child._q_depth = self._q_depth + 1
        involved = set(seeds)
        for i in ids:
            for v in self._premises[i].vars:
                value = self._solved.get(v)
                if value is None:
                    involved.add(v)
                elif v not in child._solved:
                    child._solved[v] = value
                    child._solved_tag[v] = self._solved_tag[v]
                    for u in P.variables_of(value):
                        child._occurs_in[u].add(v)
                        involved.add(u)
        for v in involved:
            if v in self._domains:
                child._domains[v] = self._domains[v]
        for i in sorted(ids):
            child.add_premise(self._premises[i].expr, self._premises[i].tag)
        if nonzero:
            child._nonzero.append((a, tag))
            child.propagate()
            return child
        child.add_premise(self._poly_expr(a), tag)
        child.propagate()
        # The assumption may be a sum of squares, e.g. sum (a_i - b_i)^2. Its
        # equations a_i = b_i are proposed like any hint, and rule S checks them.
        proposed = child._square_equations(len(child._premises) - 1, tag)
        if proposed:
            child.add_solved_all(proposed)
        return child

    def _poly_expr(self, a: P.Poly) -> Expr:
        """A polynomial written back as an expression over names."""
        out: Expr = 0
        for m, c in sorted(a.items()):
            term: Expr = c
            for v, e in m:
                for _ in range(e):
                    term = [term, "*", self.table.name(v)]
            out = term if out == 0 and not isinstance(out, list) else [out, "+", term]
        return out

    # ------------------------------------------------------------ rules D, O and S'

    def _propagate_premise(self, i: int) -> None:
        """Read premise i under the solved equations, and apply rule D, or O and S'."""
        vs = self._vars_now(i)
        if len(vs) == 1:
            self._rule_d(i, *vs)
            return
        if vs and self._use_one_hot and all(self._in_01(v) for v in vs):
            self._rule_o(i)
        if vs and self._use_nowrap_pins and all(v in self._domains for v in vs):
            self._rule_s_pins(i)

    def _rule_s_pins(self, i: int) -> None:
        """Rule S' on premise i, whose variables are all ranged: pin the one-variable terms.

        Premise: i reads  sum_i c_i * a_i  +  sum_j c_j * L_j^2  with no
        other term (_nonneg_terms), and its integer value cannot reach p
        (_no_wrap_terms). As in rule S with G = 1, every term is then 0.
        Conclusions, through _narrow_domain only: a_i = 0, and x = -t/w for
        an L_j = w*x + t over one variable. An L_j over several variables is
        an equation, which no domain holds: rule S proves it as a query, and
        it enters Sol only as a checked equation (see _square_equations).
        Tags: the premise and the domains of all its variables.
        """
        k = self._premise_key(i)
        terms = self._nonneg_terms(dict(k)) if k else None
        if terms is None:
            return
        linear, squares = terms
        if not squares and len(linear) < 2:
            return  # one variable: rule D's
        if self._no_wrap_terms(linear, squares):
            return
        tags = self._premise_tags(i) + self._domain_tags(sorted(self._term_vars(linear, squares)))
        for v in linear:
            self.nowrap_pins += self._narrow_domain(v, 0, 0, tags)
        for _, w, t in squares:
            if len(w) == 1:
                ((x, wx),) = w.items()
                value = -t * pow(wx, self.p - 2, self.p) % self.p
                self.nowrap_pins += self._narrow_domain(x, value, value, tags, frozenset((value,)))

    def _square_equations(self, i: int, tag: str) -> list[tuple[str, Expr, str]]:
        """Candidate equations x = t from premise i's squares over several variables.

        For each L_j = w.x + t of the premise's reading, L_j solved for one
        variable. Proposals only, for add_solved_all: each is used only once
        rule S proves x - t, which is where the no-wrap bound is checked.
        """
        k = self._premise_key(i)
        terms = self._nonneg_terms(dict(k)) if k else None
        out = []
        for _, w, t in terms[1] if terms else ():
            if len(w) < 2:
                continue
            x = max(w, key=self.table.name)
            inv = pow(w[x], self.p - 2, self.p)
            rhs = P.const(-t * inv, self.p)
            for v, c in w.items():
                if v != x:
                    rhs[((v, 1),)] = -c * inv % self.p
            name = self.table.name(x)
            out.append((name, self._poly_expr(rhs), f"{tag}: {name}"))
        return out

    def _nonneg_terms(self, a: P.Poly) -> tuple[dict, list] | None:
        """Read ``a`` as  sum c_i * a_i + sum c_j * (w_j . x + t_j)^2, or None.

        Returns ({a_i: c_i}, [(pivot coefficients {x: c_j for that pivot}, w_j, t_j)]):
        field values only; which integers represent them is _no_wrap_terms's
        business. The variables joined by a product x*y form one square, and
        a variable in no degree-2 term is a linear term. Each square is
        checked coefficient by coefficient, so the reading is exact:
        c * (w.x + t)^2 = c * sum w_x w_y x y + 2 c t * sum w_x x + c t^2,
        with w normalised to 1 at a pivot. The constant term must be the sum
        of the c_j * t_j^2. A square is returned once per pivot (c and w
        differ by the pivot's weight), for the bound to pick from.
        """
        p = self.p
        diag: dict[Var, int] = {}
        cross: dict[frozenset, int] = {}
        lin: dict[Var, int] = {}
        c0 = 0
        for m, c in a.items():
            if m == ():
                c0 = c
            elif len(m) == 1 and m[0][1] == 1:
                lin[m[0][0]] = c
            elif len(m) == 1 and m[0][1] == 2:
                diag[m[0][0]] = c
            elif len(m) == 2 and m[0][1] == m[1][1] == 1:
                cross[frozenset((m[0][0], m[1][0]))] = c
            else:
                return None
        # Components of the variables that occur in degree-2 terms.
        comp = {v: v for v in diag}
        for pair in cross:
            if not pair <= diag.keys():
                return None  # x*y without x^2 and y^2: no square

        def find(v: Var) -> Var:
            while comp[v] != v:
                comp[v] = comp[comp[v]]
                v = comp[v]
            return v

        for pair in cross:
            x, y = pair
            comp[find(x)] = find(y)
        groups: dict[Var, list[Var]] = defaultdict(list)
        for v in diag:
            groups[find(v)].append(v)
        half = pow(2, p - 2, p)
        squares, const = [], 0
        for members in groups.values():
            readings = {}
            for u in members:  # u as the pivot: w_u = 1, c = the coefficient of u^2
                c = diag[u]
                c_inv = pow(c, p - 2, p)
                w = {u: 1}
                for v in members:
                    if v != u:
                        w[v] = cross.get(frozenset((u, v)), 0) * half * c_inv % p
                t = lin.get(u, 0) * half * c_inv % p
                ok = all(diag[v] == c * w[v] * w[v] % p for v in members)
                ok = ok and all(lin.get(v, 0) == 2 * c * t * w[v] % p for v in members)
                ok = ok and all(
                    cross.get(frozenset((x, y)), 0) == 2 * c * w[x] * w[y] % p
                    for j, x in enumerate(members)
                    for y in members[j + 1 :]
                )
                if not ok:
                    return None
                readings[u] = (c, w, t)
            c, w, t = readings[members[0]]
            const = (const + c * t * t) % p
            squares.append((readings, w, t))
        if const != c0:
            return None
        linear = {v: c for v, c in lin.items() if v not in diag}
        return linear, squares

    def _no_wrap_terms(self, linear: dict, squares: list) -> tuple[str, str] | None:
        """(kind, message) saying why the sum of the terms might reach p, or None.

        Every variable needs a range, or the sum could be anything. Then, for
        some unit multiple k (any k*s has the same zeros): a linear term
        counts (k * c_i mod p) * hi_i, and a square, for its best pivot,
        (k * c mod p) * M^2, where M is the largest |w.x + t| over the ranges
        with w and t as signed integers in (-p/2, p/2). These integers are
        congruent to the field values, so the integer sum is congruent to k
        times the sum, and each of its terms is non-negative. If the total
        stays below p, "sum = 0 mod p" means the integer sum is 0, so every
        term is 0. Making the sum monic alone can hide a small one: 2a + 3b
        becomes a + (3/2)b, and 3/2 is huge in F_p. So k is tried among 1,
        -1 and the inverse of each coefficient, and the smallest total kept.
        """
        p = self.p
        missing = [
            self.table.name(v)
            for v in self._term_vars(linear, squares)
            if v not in self._domains
        ]
        if missing:
            return "nowrap-missing-range", f"no range for {', '.join(sorted(missing))}"

        def signed(c: int) -> int:
            return c - p if c > p // 2 else c

        sized = []  # per square: [(c, M^2)] per pivot
        for readings, _, _ in squares:
            options = []
            for c, w, t in readings.values():
                lo = hi = signed(t)
                for v, wv in w.items():
                    d, wv = self._domains[v], signed(wv)
                    lo += wv * (d.lo if wv > 0 else d.hi)
                    hi += wv * (d.hi if wv > 0 else d.lo)
                options.append((c, max(abs(lo), abs(hi)) ** 2))
            sized.append(options)
        coeffs = list(linear.values()) + [c for options in sized for c, _ in options]
        bound = min(
            sum(c * k % p * self._domains[v].hi for v, c in linear.items())
            + sum(min(c * k % p * m2 for c, m2 in options) for options in sized)
            for k in {1, p - 1} | {pow(c, p - 2, p) for c in coeffs}
        )
        if bound >= p:
            return "nowrap-bound", f"the sum can reach {bound} >= p"
        return None

    def _rule_o(self, i: int) -> None:
        """Rule O on premise i, whose variables are all in [0, 1]: group part, then selector part.

        Group part: the premise reads x_1 + ... + x_n - c with unit weights
        and c in {0, 1}. Side condition: n < p, true as a key has at most
        max_terms terms and the constructor requires max_terms < p; so the
        integer sum, in [0, n], is c. Conclusion: with c = 0 every x_i is 0;
        with n = 1, x_1 = 1; otherwise exactly one x_i is 1, and the premise
        is recorded as a group for the selector part. Tags: the premise and
        the members' domains.
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
        return self._vars_under_solved(self._premises[i].vars)

    def _vars_under_solved(self, vs: Iterable[Var]) -> set[Var]:
        """``vs``, with each solved variable replaced by the variables of its value."""
        out = set()
        for v in vs:
            value = self._solved.get(v)
            if value is None:
                out.add(v)
            else:
                out |= P.variables_of(value)
        return out

    # ------------------------------------------------------------ rule C

    def _starts_search(self, x: Var) -> bool:
        """The policy: an equation about x starts a search if x has case_split_trigger values."""
        d = self._domains.get(x)
        return d is not None and d.values is not None and len(d.values) == self.case_split_trigger

    def _finite(self, v: Var) -> bool:
        """v's domain is a finite set of values: v can be in a group."""
        d = self._domains.get(v)
        return d is not None and d.values is not None

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
        variables, each with a finite set of values (of any size: which x
        starts a search is the policy's, not the group's); x's group is what
        such premises reach from x. C is sound for any subset of the
        premises; the whole group matters for completeness only. None if
        there is no coupling premise, or more than CASE_SPLIT_GROUP_CAP cases.
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
                if not all(self._finite(v) for v in self._vars_now(i)):
                    continue
                vs = self._vars_from_key(i)
                if len(vs) < 2 or not all(self._finite(v) for v in vs):
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
        """Queue premises for the work list; outside a run, keep them for the next one."""
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

    def _ready(self, j: int) -> None:
        """Queue equation j for a check."""
        if j not in self._eq_queued:
            self._eq_queued.add(j)
            heapq.heappush(self._eq_ready, j)

    def _wait(self, j: int) -> None:
        """Equation j was rejected: wait on its variables and the premises that mention them."""
        e = self._eqs[j]
        vs = frozenset(self._vars_under_solved(e.written))
        ids = frozenset(i for v in vs for i in self._coi_premise_ids(v))
        e.wait_vars, e.wait_premises = vs, ids
        self._waiting.add(j)
        for v in vs:
            self._waiting_on_var[v].add(j)
        for i in ids:
            self._waiting_on_premise[i].add(j)

    def _wake(self, ids: Iterable[int], vs: Iterable[Var]) -> None:
        """Queue the waiting equations that read a premise in ``ids`` or a variable in ``vs``."""
        if not self._waiting:
            return
        woken = set()
        for i in ids:
            woken.update(self._waiting_on_premise.get(i, ()))
        for v in vs:
            woken.update(self._waiting_on_var.get(v, ()))
        for j in woken:
            e = self._eqs[j]
            self._waiting.discard(j)
            for v in e.wait_vars:
                self._waiting_on_var[v].discard(j)
            for i in e.wait_premises:
                self._waiting_on_premise[i].discard(j)
            self._ready(j)

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
