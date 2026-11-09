# -*- coding: utf-8 -*-
"""Stand: zseries — Bessel J0, J1 and Kelvin ber, bei (and derivatives) on the numeric floor, and nested integrals
(2026-11-09, the curator: «Добавь в ядро Бессель и интегралы»).

Every bracket must hold the TRUE value (mpmath at 40 digits, not scipy: scipy's ber/bei at |x| > 10 are off by ~1e-10
relative — MEASURED, our brackets held mpmath's value and not scipy's). Both sides of every judged claim: a bound just
outside the true range must NOT be earned. MUTATION: a bracket shifted by one grid step past the truth is caught.
"""
import random
import sys
from fractions import Fraction as F

import mpmath

import zseries as S
import znumjudge as ZJ

mpmath.mp.dps = 40
ok = fail = 0


def check(cond, what):
    global ok, fail
    if cond:
        ok += 1; print("  ok  ", what)
    else:
        fail += 1; print("  FAIL", what)


def fl(q):
    return mpmath.mpf(q.numerator) / q.denominator


MP = {"besselj0": lambda x: mpmath.besselj(0, x), "besselj1": lambda x: mpmath.besselj(1, x),
      "ber": lambda x: mpmath.ber(0, x), "bei": lambda x: mpmath.bei(0, x),
      "berp": lambda x: mpmath.diff(lambda u: mpmath.ber(0, u), x),
      "beip": lambda x: mpmath.diff(lambda u: mpmath.bei(0, u), x),
      "besselj1_d1": lambda x: mpmath.diff(lambda u: mpmath.besselj(1, u), x),
      "ber_d2": lambda x: mpmath.diff(lambda u: mpmath.ber(0, u), x, 2)}

print("1. points and intervals hold the true value (mpmath, 40 digits)")
rng = random.Random(20261109)
pm = im = 0
for name, f in MP.items():
    for _ in range(12):
        x = F(rng.uniform(-14, 14)).limit_denominator(10 ** 6)
        lo, hi = S.point(name, x)
        pm += not (fl(lo) <= f(fl(x)) <= fl(hi))
        a0 = F(rng.uniform(-14, 14)).limit_denominator(10 ** 4)
        a1 = a0 + F(rng.uniform(0.0001, 0.3)).limit_denominator(10 ** 4)
        I = S.interval(name, (a0, a1))
        vs = [f(fl(a0 + (a1 - a0) * F(i, 30))) for i in range(31)]
        im += not (fl(I[0]) <= min(vs) and max(vs) <= fl(I[1]))
check(pm == 0, f"{len(MP) * 12} point brackets, misses {pm}")
check(im == 0, f"{len(MP) * 12} interval enclosures (31 samples each), misses {im}")
check(S.point("besselj0", 0) == (1, 1) and S.point("besselj1", 0) == (0, 0) and S.point("besselj1_d1", 0) == (F(1, 2), F(1, 2)),
      "at 0: J0 = 1, J1 = 0, J1' = 1/2 exactly")

print("2. MUTATION: a bracket moved past the truth is caught by the same comparison")
lo, hi = S.point("besselj0", F(2))
v = MP["besselj0"](2)
check(not (fl(hi - (hi - lo) - F(1, 2 ** 40)) <= v <= fl(lo - F(1, 2 ** 40))), "J0(2)'s bracket shifted below the truth fails the check")

print("3. the judge, both sides")
def disp(claim, sheet=""):
    qs = ZJ.parse_quantities(sheet)[0] if sheet else {}
    return ZJ.judge_sheet_claim(claim, qs, {})["disposition"]
check(disp("besselj0(x) >= 0.166", "x=[1.9,2.1] earned") == "EARNED", "J0 over [1.9, 2.1] >= 0.166 (min 0.16661)")
check(disp("besselj0(x) >= 0.167", "x=[1.9,2.1] earned") != "EARNED", "  the other side: >= 0.167 not earned")
check(disp("besselj0(x) <= 0.2819", "x=[1.9,2.1] earned") == "EARNED", "J0 over [1.9, 2.1] <= 0.2819 (max 0.28182)")
check(disp("besselj0(x) <= 0.2818", "x=[1.9,2.1] earned") != "EARNED", "  the other side: <= 0.2818 not earned")
check(disp("ber(x) >= 0.299", "x=[2.5,2.6] earned") == "EARNED" and disp("ber(x) >= 0.301", "x=[2.5,2.6] earned") != "EARNED",
      "ber over [2.5, 2.6] (true 0.30009 .. 0.39997, mpmath): >= 0.299 earned, >= 0.301 not")
check(disp("ber(x) <= 0.4001", "x=[2.5,2.6] earned") == "EARNED" and disp("ber(x) <= 0.3999", "x=[2.5,2.6] earned") != "EARNED",
      "  and the top: <= 0.4001 earned, <= 0.3999 not")

print("4. nested integrals with constant inner limits — both sides; moving inner limits refused")
check(disp("integral(integral(s*u, s, 0, 1), u, 0, 1) >= 0.2499") == "EARNED"
      and disp("integral(integral(s*u, s, 0, 1), u, 0, 1) >= 0.2501") == "REFUTED", "∫∫ s·u = 1/4")
try:
    disp("integral(integral(s, s, 0, u), u, 0, 1) >= 0")
    check(False, "moving inner limits should be refused")
except ValueError as e:
    check("limits move with" in str(e), "moving inner limits: refused, said")

print(f"\n{ok} ok, {fail} fail")
print("ZSERIES GREEN" if fail == 0 else "ZSERIES RED")
sys.exit(1 if fail else 0)
