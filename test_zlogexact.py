# -*- coding: utf-8 -*-
"""test_zlogexact — exact logarithms of rationals on the numeric floor (zlogexact.py, 2026-11-24), both sides.

    python3 test_zlogexact.py

1. Equalities the bracket never forced are decided: ln 64 / ln 8 = 2, log_8 64 + log_4 64 = 5, ln 2 + ln 3 = ln 6.
2. The other side: what is NOT equal is refuted — ln 2 = 1, ln 2 + 1 = ln 5 (Hermite: e^q transcendental), ln 3/ln 2 = 3/2.
3. Brute force against mpmath at 60 digits: for random rationals, every decided comparison of sums of logarithms agrees
   with the true value; and ln(a) + ln(b) = ln(ab) is EARNED for every pair.
4. Nothing else moved: ln of a negative is still E; a quantity that is not pinned still reads by the interval path."""
import random
import sys
from fractions import Fraction as F

import mpmath

from znumjudge import judge_sheet_claim, parse_quantities

mpmath.mp.dps = 60
FAILS, N = [], [0]


def disp(claim, sheet=""):
    q, m = parse_quantities(sheet) if sheet else ({}, {})
    return judge_sheet_claim(claim, q, m)["disposition"]


def check(cond, what):
    N[0] += 1
    if not cond:
        FAILS.append(what)
        print("FAIL", what)


for c, want in [("ln(64) / ln(8) == 2", "EARNED"), ("ln(64) / ln(8) + ln(64) / ln(4) == 5", "EARNED"),
                ("ln(2) + ln(3) == ln(6)", "EARNED"), ("log10(1000) == 3", "EARNED"), ("ln(1) == 0", "EARNED"),
                ("ln(1/8) / ln(2) == 0 - 3", "EARNED"),
                ("ln(2) == 1", "REFUTED"), ("ln(2) + 1 == ln(5)", "REFUTED"), ("ln(3) / ln(2) == 3/2", "REFUTED"),
                ("ln(64) / ln(8) == 3", "REFUTED"), ("ln(0-1) < 5", "E")]:
    check(disp(c) == want, f"{c} -> {want}")
check(disp("ln(x) <= 1", "x=[1,2] earned:a") == "EARNED", "an unpinned quantity still reads by the interval path")
check(disp("ifpos(a, ln(a), ifpos(0 - a, ln(0 - a), 0)) / ln(8) + ln(b*b) / ln(4) == 5",
           "a=-64 earned:p, b=8 earned:p") == "EARNED", "aime_1984_p5's first hypothesis in Lean's reading at (-64, 8)")

rnd = random.Random(20261124)


def rq():
    return F(rnd.randint(1, 60), rnd.randint(1, 12))


for _ in range(150):
    a, b = rq(), rq()
    check(disp(f"ln({a}) + ln({b}) == ln({a * b})") == "EARNED", f"ln({a}) + ln({b}) = ln({a * b})")
    x, y, z, k = rq(), rq(), rq(), F(rnd.randint(-3, 3))
    for sign, op in (("<", lambda u, v: u < v), ("<=", lambda u, v: u <= v), ("==", lambda u, v: u == v)):
        d = disp(f"ln({x}) + {k} * ln({y}) {sign} ln({z})")
        if d in ("EARNED", "REFUTED"):
            lhs = mpmath.log(mpmath.mpf(x.numerator) / x.denominator) + int(k) * mpmath.log(mpmath.mpf(y.numerator) / y.denominator)
            rhs = mpmath.log(mpmath.mpf(z.numerator) / z.denominator)
            truth = op(lhs, rhs) if sign != "==" else abs(lhs - rhs) < mpmath.mpf(10) ** -50
            check(truth == (d == "EARNED"), f"ln({x}) + {k} ln({y}) {sign} ln({z}): {d}")

print(f"LOGEXACT GREEN — {N[0]} checks" if not FAILS else f"test_zlogexact: {len(FAILS)} failures of {N[0]}")
sys.exit(1 if FAILS else 0)
