# -*- coding: utf-8 -*-
"""test_zsummation — the summation method as a dirty parameter (zsummation.py, 2026-11-25), checked both ways.

    python3 test_zsummation.py

1. ζ(−j), η(−j) against mpmath for j = 0..14; the classic table: 1+2+3+… (zeta −1/12, Mathlib 0, limit/Abel/Cesàro
   none), Grandi (1/2 by Abel, Cesàro, zeta), 1−2+3−… (1/4 by Abel and zeta, none by (C,1)), 1+1+1+… (zeta −1/2).
2. THE ZERO IN FRONT (the article): 1+2+3+… and 0+1+2+3+… get −1/12 and 5/12 under zeta — the method is not stable;
   every other method gives both the same (or none).
3. The other side, numerically: for random alternating polynomials, the Abel value matches Σ (−1)^n P(n) x^n at
   x = 1 − 10^−4 (summed in mpmath) to within the O(1 − x) error; for (C,1) on constants, the means of the partial sums."""
import random
import sys
from fractions import Fraction as F

import mpmath

import zsummation as S

mpmath.mp.dps = 30
FAILS, N = [], [0]


def check(cond, what):
    N[0] += 1
    if not cond:
        FAILS.append(what)
        print("FAIL", what)


for j in range(15):
    check(abs(mpmath.mpf(S.zeta_neg(j).numerator) / S.zeta_neg(j).denominator - mpmath.zeta(-j)) < 1e-20, f"zeta(-{j})")
    check(abs(mpmath.mpf(S.eta_neg(j).numerator) / S.eta_neg(j).denominator - mpmath.altzeta(-j)) < 1e-20, f"eta(-{j})")

T = S.table({0: 1, 1: 1}, False)                         # 1 + 2 + 3 + …
check(T == {"limit": None, "mathlib": 0, "abel": None, "cesaro": None, "zeta": F(-1, 12)}, f"1+2+3+…: {T}")
T = S.table({0: 1}, True)                                # 1 − 1 + 1 − …
check(T == {"limit": None, "mathlib": 0, "abel": F(1, 2), "cesaro": F(1, 2), "zeta": F(1, 2)}, f"Grandi: {T}")
T = S.table({0: 1, 1: 1}, True)                          # 1 − 2 + 3 − …
check(T == {"limit": None, "mathlib": 0, "abel": F(1, 4), "cesaro": None, "zeta": F(1, 4)}, f"1-2+3-…: {T}")
check(S.value({0: 1}, False, "zeta") == F(-1, 2), "1+1+1+… = zeta(0)")
check(S.value({}, False, "limit") == 0 and S.value({}, True, "zeta") == 0, "the zero series is 0 under every method")

# 2. the zero in front
one, zero_front = S.table({0: 1, 1: 1}, False), S.table({1: 1}, False)
check(one["zeta"] == F(-1, 12) and zero_front["zeta"] == F(5, 12), "zeta: 1+2+3+… = -1/12, 0+1+2+… = 5/12")
check(all(one[m] == zero_front[m] for m in S.METHODS if m != "zeta"), "the other methods are unmoved by the zero")

# 3. numerically, the other side
rnd = random.Random(20261125)
x = mpmath.mpf(1) - mpmath.mpf(10) ** -4
for _ in range(12):
    p = {k: F(rnd.randint(-3, 3)) for k in range(rnd.randint(0, 2) + 1)}
    v = S.value(p, True, "abel")
    approx = mpmath.nsum(lambda n: (-1) ** int(n) * sum(float(c) * n ** k for k, c in p.items()) * x ** n, [0, mpmath.inf])
    scale = 1 + sum(abs(float(c)) for c in p.values())
    check(abs(approx - (mpmath.mpf(v.numerator) / v.denominator)) < 0.05 * scale, f"Abel of alternating {p}: {v} vs {approx}")
c = F(3)
parts = [c * (1 if n % 2 == 0 else 0) for n in range(4000)]   # partial sums of 3 − 3 + 3 − …: 3, 0, 3, 0, …
check(abs(sum(parts) / len(parts) - S.value({0: c}, True, "cesaro")) < F(1, 100), "Cesàro of 3 − 3 + 3 − …")

# 4. GEOMETRIC: Σ P(n) r^n (Lean Workbook's series) — against mpmath where it converges; Euler's 1 + 2 + 4 + … = −1
for p, r in [({0: 1}, F(1, 2)), ({1: 1}, F(1, 2)), ({1: 1}, F(1, 3)), ({2: 1}, F(1, 2)), ({0: 1, 1: 1}, F(1, 10)),
             ({0: 3, 2: -1}, F(-2, 5)), ({3: 1}, F(1, 4))]:
    v = S.value_geo(p, r, "limit")
    true = mpmath.nsum(lambda n: sum(float(c) * n ** k for k, c in p.items()) * mpmath.mpf(r.numerator) / r.denominator ** 1
                       * 0 + sum(float(c) * n ** k for k, c in p.items()) * (mpmath.mpf(r.numerator) / r.denominator) ** n,
                       [0, mpmath.inf])
    check(abs(mpmath.mpf(v.numerator) / v.denominator - true) < 1e-15, f"Σ {p} ({r})^n = {v} vs {true}")
    check(all(S.value_geo(p, r, m) == v for m in S.METHODS), f"|r| < 1: every method agrees on {p}, {r}")
T = {m: S.value_geo({0: 1}, 2, m) for m in S.METHODS}
check(T == {"limit": None, "mathlib": 0, "abel": None, "cesaro": None, "zeta": -1}, f"1 + 2 + 4 + …: {T}")
check(S.value_geo({0: 1}, -1, "abel") == F(1, 2) and S.value_geo({0: 1, 1: 1}, 1, "zeta") == F(-1, 12),
      "r = ±1 falls back to the power-series case")
check(S.value_geo({0: 5}, 0, "limit") == 5, "r = 0: only the n = 0 term (0^0 = 1)")

print(f"SUMMATION GREEN — {N[0]} checks" if not FAILS else f"test_zsummation: {len(FAILS)} failures of {N[0]}")
sys.exit(1 if FAILS else 0)
