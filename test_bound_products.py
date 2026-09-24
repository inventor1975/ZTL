# -*- coding: utf-8 -*-
"""
test_bound_products — 0 times an infinite end is 0, and nothing is nan.

MEASURED 2026-09-24: the interval product took Python's 0 * inf = nan, and
min/max over a list holding nan depend on its order; [-inf,0]·[0,1] came out
(nan, nan), so a*b <= 0 was Z where it is T. No verdict was false (nan makes
every comparison Z); forced verdicts were lost. The ends of an interval are
limits, never attained, and 0 times any real is 0.
Guards: no nan anywhere on a grid of intervals with infinite ends; every
product of sampled points lies inside the computed interval; the instances.
Run: python3 test_bound_products.py  ->  BOUND PRODUCTS GREEN
"""
import itertools
import math
import sys
from fractions import Fraction

import znum
from znum import INF, EARNED, qty

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


ENDS = [-INF, Fraction(-2), Fraction(-1), Fraction(0), Fraction(1), Fraction(2), INF]
BOXES = [(lo, hi) for lo, hi in itertools.product(ENDS, ENDS)
         if lo <= hi and not (lo == hi and lo in (INF, -INF))]


def points(box):
    lo, hi = box
    a = lo if lo != -INF else Fraction(-10 ** 6)
    b = hi if hi != INF else Fraction(10 ** 6)
    return {a, b, (a + b) / 2}


for a, b in itertools.product(BOXES, BOXES):
    lo, hi = znum._iv_mul(a, b)
    check(not (isinstance(lo, float) and math.isnan(lo)) and
          not (isinstance(hi, float) and math.isnan(hi)), f"nan in {a}·{b} = ({lo}, {hi})")
    for x, y in itertools.product(points(a), points(b)):
        check(lo <= x * y <= hi, f"{x}·{y} = {x * y} outside {a}·{b} = ({lo}, {hi})")

q = {"a": qty(-INF, 0, EARNED, "g"), "b": qty(0, 1, EARNED, "g")}
check(znum.compare("le", ("mul", "a", "b"), 0, q)[0] == "T", "a in [-inf,0], b in [0,1]: a*b <= 0 is T")
check(znum._iv_mul((Fraction(0), Fraction(0)), (-INF, INF)) == (0, 0), "[0,0]·[-inf,inf] = [0,0]")
print(f"BOUND PRODUCTS GREEN — {CHECKS} checks over {len(BOXES) ** 2} interval pairs, no nan")
