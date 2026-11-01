"""fixed_values against a plain enumeration of every assignment."""
import itertools
import random

import pytest

from src.polysolver.enumeration import Fixed, GaveUp, NoSolution, fixed_values

P = 2013265921  # BabyBear
HALF = (P + 1) // 2  # 1/2 in F_p
CAP = 100_000


def value(q, a):
    """q at the assignment a (a dict)."""
    total = 0
    for m, c in q:
        for x, e in m:
            c = c * pow(a[x], e, P) % P
        total += c
    return total % P


def lin(c0=0, **w):
    """c0 + sum w_x * x, as (monomial, coeff) pairs."""
    terms = [(((x, 1),), c % P) for x, c in w.items()]
    return tuple(terms + ([((), c0 % P)] if c0 % P else []))


def brute(polys, domains):
    """What fixed_values should say, from every assignment."""
    names = list(domains)
    sols = [
        dict(zip(names, vs))
        for vs in itertools.product(*domains.values())
        if all(value(q, dict(zip(names, vs))) == 0 for q in polys)
    ]
    if not sols:
        return NoSolution
    return {x: sols[0][x] for x in names if all(s[x] == sols[0][x] for s in sols)}


def random_instance(rng):
    """2 to 5 variables with three values each, and 1 to 3 small polynomials.

    Most instances have a solution planted: each polynomial's constant is
    chosen so that one assignment is a zero.
    """
    names = [f"x{i}" for i in range(rng.randint(2, 5))]
    pool = [(0, 1, 2), (0, HALF, 1), (0, 1, P - 1)]
    domains = {
        x: rng.choice(pool) if rng.random() < 0.7 else tuple(rng.sample(range(8), 3))
        for x in names
    }
    planted = {x: rng.choice(domains[x]) for x in names}
    polys = []
    for _ in range(rng.randint(1, 3)):
        terms = {}
        for _ in range(rng.randint(1, 3)):
            vs = rng.sample(names, rng.randint(1, 2))
            m = tuple(sorted((x, rng.randint(1, 2)) for x in vs))
            terms[m] = rng.choice([1, 2, 3, P - 1, P - 2])
        if rng.random() < 0.8:
            c = -value(terms.items(), planted) % P
        else:
            c = rng.randint(0, 4)
        if c:
            terms[()] = (terms.get((), 0) + c) % P
        polys.append(tuple(terms.items()))
    return polys, domains


def test_random_instances_match_a_full_enumeration():
    rng = random.Random(20261101)
    seen = {"fixed": 0, "none": 0, "some": 0}
    for _ in range(400):
        polys, domains = random_instance(rng)
        want = brute(polys, domains)
        got = fixed_values(polys, domains, P, CAP)
        if want is NoSolution:
            assert isinstance(got, NoSolution)
            seen["none"] += 1
            continue
        assert isinstance(got, Fixed) and got.values == want
        seen["fixed" if len(want) == len(domains) else "some"] += 1
        # The answer is a property of the solutions, not of the search order.
        names = list(domains)
        rng.shuffle(names)
        shuffled = {x: domains[x] for x in names}
        again = fixed_values(rng.sample(polys, len(polys)), shuffled, P, CAP)
        assert again.values == got.values
    # Each outcome occurs: a unique solution, none, and some fixed but not all.
    assert all(n > 20 for n in seen.values()), seen


def test_any_three_values():
    # a = b and a + b = 1: only a = b = 1/2, which {0, 1, 2} does not have.
    polys = [lin(a=1, b=-1), lin(-1, a=1, b=1)]
    assert isinstance(fixed_values(polys, {"a": (0, 1, 2), "b": (0, 1, 2)}, P, CAP), NoSolution)
    got = fixed_values(polys, {"a": (0, HALF, 1), "b": (0, HALF, 1)}, P, CAP)
    assert got == Fixed({"a": HALF, "b": HALF}, got.nodes)


def test_constants_and_missing_domains():
    assert isinstance(fixed_values([lin(5)], {"a": (0, 1, 2)}, P, CAP), NoSolution)
    assert fixed_values([lin()], {}, P, CAP).values == {}  # the zero polynomial holds
    assert fixed_values([], {"a": (3,)}, P, CAP).values == {"a": 3}  # free, one value
    with pytest.raises(ValueError):
        fixed_values([lin(a=1)], {}, P, CAP)


def test_gave_up_keeps_what_it_proved():
    # a = 2 and c = 1; b and d are free. The order is a, c, b, d. Two fits take
    # 8 values, proving a takes 2 more, and c needs more than the budget of 10.
    polys = [lin(-2, a=1), lin(-1, c=1)]
    domains = {x: (0, 1, 2) for x in "abcd"}
    assert fixed_values(polys, domains, P, CAP).values == {"a": 2, "c": 1}
    got = fixed_values(polys, domains, P, 10)
    assert isinstance(got, GaveUp) and got.values == {"a": 2}
