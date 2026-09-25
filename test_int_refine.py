# -*- coding: utf-8 -*-
"""
test_int_refine — integer-typed quantities are read on the integers.

Until 2026-09-25 a comparison over `int` quantities was decided on the
CONTINUOUS box: `x == 1 - x` on [0, 1000] came back OPEN because 1/2 solves
it, and `x <= x * x` OPEN because x*x dips under x between 0 and 1. Neither
reading exists for an integer. MEASURED on a dataset of bounded-integer claims
with enumerated gold (ztl-private/datasets/bounded-int-claims): 1 364 of
69 696 claims with bounds up to ±1000 were OPEN though the integers decide
them — never a wrong verdict, an abstention. Forecast frozen before the change:
inventory/probes/FORECAST-INTEGER-REFINE-2026-09-25.md.

The refinement (znum._int_refine) runs only where compare says Z and decides
only by exact integer arithmetic over the whole box — never by listing it, so
a box of ±10^9 is pinned here and must be as fast as ±1. Pinned too:
  - the three shapes it decides (one name; one name linear; bilinear ==),
  - what it must leave OPEN (x*x == x on [0, 1000]: two integer roots in a
    box of 1001 integers; x*x < x*y coupled),
  - a continuous quantity is NOT touched (x == 1 - x stays OPEN there),
  - soundness against brute force on random small boxes: no wrong T/F.
Fails before the change: the first check is OPEN on the old judge.
Run: python3 test_int_refine.py  ->  INT REFINE GREEN
"""
import itertools
import random
import time
from fractions import Fraction as Q

import znum

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        raise SystemExit(f"FAIL: {what}")


def I(lo, hi):
    return znum.qty(lo, hi, discrete="int")


def v(kind, e1, e2, qs):
    return znum.compare(kind, e1, e2, qs)[0]


X = {"x": I(0, 1000)}
# (1) one free name
check(v("eq", "x", ("sub", 1, "x"), X) == "F", "x == 1 - x on [0,1000]: no integer 1/2")
check(v("le", "x", ("mul", "x", "x"), X) == "T", "x <= x*x on the integers of [0,1000]")
check(v("eq", ("add", 2, 1), ("mul", "x", 2), {"x": I(1, 3)}) == "F", "2x == 3 has no integer x")
check(v("eq", ("mul", "x", "x"), "x", {"x": I(0, 1)}) == "T", "x*x == x holds at both integers 0 and 1")
check(v("eq", ("mul", "x", "x"), "x", X) == "Z", "x*x == x on [0,1000] holds at 0,1 only: OPEN")
check(v("eq", ("mul", "x", "x"), 2, {"x": I(-5, 5)}) == "F", "x*x == 2: sqrt 2 is not an integer")
# (2) two names, one only linear
check(v("eq", ("mul", "y", "y"), ("mul", "x", 2), {"x": I(1, 1), "y": I(1, 3)}) == "F",
      "y*y == 2 after pinning x: no integer")
check(v("eq", ("mul", "x", "x"), ("add", 2, "y"), {"x": I(-1000, 1000), "y": I(0, 1)}) == "F",
      "x*x - 2 in {0,1}: neither 2 nor 3 is a square")
check(v("eq", ("mul", "y", "y"), ("mul", 2, "x"), {"x": I(0, 1000), "y": I(-1000, 1000)}) == "Z",
      "y*y == 2x: y = 2, x = 2 solves it")
# (3) bilinear ==
check(v("eq", 1, ("mul", "x", "y"), {"x": I(0, 1000), "y": I(2, 1000)}) == "F", "x*y == 1 with y >= 2")
check(v("eq", ("add", "y", 1), ("mul", "x", "y"), {"x": I(0, 1000), "y": I(2, 1000)}) == "F",
      "y + 1 == x*y: y(x-1) = 1 impossible with y >= 2")
check(v("eq", 6, ("mul", "x", "y"), {"x": I(-10, 10), "y": I(-10, 10)}) == "Z", "x*y == 6: 2*3")
# left OPEN on purpose
check(v("lt", ("mul", "x", "x"), ("mul", "x", "y"), {"x": I(-2, 2), "y": I(0, 1)}) == "Z",
      "x*x < x*y: coupled, out of scope, stays OPEN")
# a continuous quantity is untouched
check(v("eq", "x", ("sub", 1, "x"), {"x": znum.qty(0, 1000)}) == "Z", "rational x = 1/2 solves it: OPEN")
# no listing: a box of ±10^9 decides at once
t = time.time()
BIG = {"x": I(-10 ** 9, 10 ** 9), "y": I(2, 10 ** 9)}
check(v("eq", "x", ("sub", 1, "x"), BIG) == "F", "x == 1 - x on ±10^9")
check(v("eq", 1, ("mul", "x", "y"), BIG) == "F", "x*y == 1 on a ±10^9 box")
check(v("le", "x", ("mul", "x", "x"), BIG) == "T", "x <= x*x on ±10^9 integers")
check(time.time() - t < 2.0, "±10^9 must not be enumerated")

# soundness against brute force, random small boxes (seeded)
rnd = random.Random(20260925)
CONST = [Q(k) for k in range(-4, 5)] + [Q(1, 2)]
def expr(d, names):
    if d == 0 or rnd.random() < 0.3:
        return rnd.choice(names) if rnd.random() < 0.6 else rnd.choice(CONST)
    return (rnd.choice(["add", "sub", "mul", "mul"]), expr(d - 1, names), expr(d - 1, names))
def val(e, nu):
    if isinstance(e, str): return Q(nu[e])
    if not isinstance(e, tuple): return Q(e)
    a, b = val(e[1], nu), val(e[2], nu)
    return a + b if e[0] == "add" else a - b if e[0] == "sub" else a * b
REL = {"le": lambda a, b: a <= b, "lt": lambda a, b: a < b, "eq": lambda a, b: a == b}
for _ in range(3000):
    names = ["x", "y"][:rnd.choice([1, 2])]
    box = {n: (lambda lo: (lo, lo + rnd.choice([0, 1, 3, 12])))(rnd.randint(-15, 15)) for n in names}
    e1, e2, k = expr(2, names), expr(2, names), rnd.choice(list(REL))
    got = v(k, e1, e2, {n: I(*b) for n, b in box.items()})
    seen = {REL[k](val(e1, dict(zip(names, pt))), val(e2, dict(zip(names, pt))))
            for pt in itertools.product(*[range(box[n][0], box[n][1] + 1) for n in names])}
    gold = "T" if seen == {True} else "F" if seen == {False} else "Z"
    check(got not in ("T", "F") or got == gold, f"WRONG {k} {e1} {e2} {box}: {got} vs {gold}")

print(f"INT REFINE GREEN ({CHECKS} checks)")
