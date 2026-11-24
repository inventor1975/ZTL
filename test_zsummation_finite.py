# -*- coding: utf-8 -*-
"""zsummation's finite sums: the closed forms against direct summation (exact Fractions)."""
import random
import sys
from fractions import Fraction

import zsummation as zs

checks = fails = 0


def ok(cond, what):
    global checks, fails
    checks += 1
    if not cond:
        fails += 1
        print("FAIL", what)


def direct(p, r, lo, hi):
    r = Fraction(r)
    return sum((zs._peval(p, i) * (r ** i if not (r == 0 and i == 0) else 1) for i in range(lo, hi + 1)), Fraction(0))


# 1. known closed forms
ok(zs.faulhaber({1: 1}) == {1: Fraction(1, 2), 2: Fraction(1, 2)}, "Σ i = m(m+1)/2")
ok(zs.faulhaber({0: 1}) == {0: 1, 1: 1}, "Σ 1 = m + 1")
ok(zs.faulhaber({3: 1}) == {2: Fraction(1, 4), 3: Fraction(1, 2), 4: Fraction(1, 4)}, "Σ i³ = (m(m+1)/2)²")
ok(zs.finite_value({1: 1}, 1, 0, 100) == 5050, "Gauss 5050")
ok(zs.finite_value({0: 1}, 2, 0, 9) == 1023, "Σ_{i<10} 2^i")
ok(zs.finite_value({1: 1}, 1, 5, 4) == 0, "empty interval: hi = lo − 1")
ok(zs.finite_value({1: 1}, 1, 5, 1) == 0, "empty interval: hi < lo − 1")
for P in ({1: 1}, {2: 3, 0: -1}, {4: Fraction(1, 7)}):
    ok(zs._peval(zs.faulhaber(P), -1) == 0, f"F(-1) = 0 for {P}")
# 2. random polynomials, ratios and bounds — closed form == direct sum
rng = random.Random(20261125)
for _ in range(600):
    deg = rng.randint(0, 5)
    p = {k: Fraction(rng.randint(-9, 9), rng.randint(1, 4)) for k in range(deg + 1)}
    r = rng.choice([1, 1, 2, -1, Fraction(1, 2), Fraction(-2, 3), 3, 0])
    lo = rng.randint(0 if r == 0 else -6, 6)
    hi = lo + rng.randint(-3, 12)
    ok(zs.finite_value(p, r, lo, hi) == direct(p, r, lo, hi), f"P={p} r={r} [{lo},{hi}]")
# 3. the telescoping identity of Q itself
for _ in range(100):
    p = {k: Fraction(rng.randint(-5, 5)) for k in range(rng.randint(0, 4) + 1)}
    r = rng.choice([2, -1, Fraction(1, 3), Fraction(5, 2)])
    q = zs.geo_q(p, r)
    i = rng.randint(-5, 5)
    ok(zs._peval(q, i) - r * zs._peval(q, i + 1) == zs._peval(p, i), f"Q(i) − rQ(i+1) = P(i): {p} {r}")

print(f"test_zsummation_finite: {checks - fails}/{checks}")
sys.exit(1 if fails else 0)
