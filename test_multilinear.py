# -*- coding: utf-8 -*-
"""
test_multilinear — names that multiply each other are read at the corners.

Where names multiply each other (x*y - x), neither the linear nor the
parabola reading applies, and the separate interval arithmetic reads x
twice: MEASURED 2026-09-24, x*y - x over x in [0,1], y in [0,2] came out
[-1, 2], so x*y - x <= 1 was Z; it is x·(y - 1), in [-1, 1], and the claim is
T. A multilinear polynomial (every name at most to the first power) is
linear in each name with the others fixed, so over a box its extremes sit
at the corners. A `sample` keeps a key per occurrence: s*s stays decorrelated.
Guards: SOUND on an exhaustive integer pool with three names; REFINES (never
overturns the separate reading); the instances; fails on the floor before.
Run: python3 test_multilinear.py  ->  MULTILINEAR GREEN
"""
import itertools
import sys
from fractions import Fraction

import znum
from znum import qty, EARNED

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def value(e, nu):
    if isinstance(e, (int, Fraction)):
        return Fraction(e)
    if isinstance(e, str):
        return Fraction(nu[e])
    op, a, b = e
    a, b = value(a, nu), value(b, nu)
    return {"add": a + b, "sub": a - b, "mul": a * b}[op]


def separate(kind, r1, r2):
    if kind == "le":
        return "T" if r1[1] <= r2[0] else ("F" if r1[0] > r2[1] else "Z")
    if kind == "lt":
        return "T" if r1[1] < r2[0] else ("F" if r1[0] >= r2[1] else "Z")
    d = znum._iv_sub(r1, r2)
    return "T" if d == (0, 0) else ("F" if d[0] > 0 or d[1] < 0 else "Z")


REL = {"le": lambda a, b: a <= b, "lt": lambda a, b: a < b, "eq": lambda a, b: a == b}
XY, XZ, YZ = ("mul", "x", "y"), ("mul", "x", "z"), ("mul", "y", "z")
EXPRS = [("sub", XY, "x"), ("add", XY, YZ), ("sub", ("add", XY, XZ), YZ), ("mul", XY, "z"),
         ("sub", XY, ("mul", "y", "x")), ("add", ("mul", 2, XY), ("mul", -3, "z")), "x", 1, -2]
pool = decided = refined = 0
for ix, iy, iz in itertools.product([(-2, 1), (0, 2), (1, 1)], repeat=3):
    q = {"x": qty(*ix, EARNED, "g", discrete="int"), "y": qty(*iy, EARNED, "g", discrete="int"),
         "z": qty(*iz, EARNED, "g", discrete="int")}
    nus = [{"x": a, "y": b, "z": c} for a in range(ix[0], ix[1] + 1)
           for b in range(iy[0], iy[1] + 1) for c in range(iz[0], iz[1] + 1)]
    for e1, e2 in itertools.product(EXPRS, repeat=2):
        r1, r2 = znum._ev(e1, q)[0], znum._ev(e2, q)[0]
        for kind, rel in REL.items():
            pool += 1
            v = znum.compare(kind, e1, e2, q)[0]
            truths = {rel(value(e1, nu), value(e2, nu)) for nu in nus}
            if v == "T":
                check(truths == {True}, f"UNSOUND T: {kind} {e1} {e2} on {ix},{iy},{iz}")
            if v == "F":
                check(truths == {False}, f"UNSOUND F: {kind} {e1} {e2} on {ix},{iy},{iz}")
            decided += v in ("T", "F")
            if r1 is not None and r2 is not None:
                old = separate(kind, r1, r2)
                if old in ("T", "F"):
                    check(v == old, f"OVERTURNED {old}->{v}: {kind} {e1} {e2}")
                elif v in ("T", "F"):
                    refined += 1
check(refined > 0, f"the corner reading decides claims the separate bounds could not ({refined})")

q = {"x": qty(0, 1, EARNED, "g"), "y": qty(0, 2, EARNED, "g")}
check(znum.compare("le", ("sub", XY, "x"), 1, q)[0] == "T", "x*y - x <= 1 over [0,1]x[0,2] is T")
check(znum.compare("lt", ("sub", XY, "x"), 1, q)[0] == "Z", "x*y - x < 1 is Z (it is 1 at a corner)")
check(znum.compare("eq", XY, ("mul", "y", "x"), q)[0] == "T", "x*y == y*x for numbers")
s = {"s": qty(1, 3, EARNED, "g", sample=True)}
check(znum.compare("eq", ("mul", "s", "s"), ("mul", "s", "s"), s)[0] == "Z", "a sample stays decorrelated")
print(f"MULTILINEAR GREEN — {CHECKS} checks; pool of {pool} claims, {decided} decided, "
      f"{refined} decided that the separate bounds left open, 0 unsound, 0 overturned")
