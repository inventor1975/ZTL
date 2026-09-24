# -*- coding: utf-8 -*-
"""
test_numeric_names — a NAME is ONE NUMBER across the whole claim.

Decided by the curator on 2026-09-24, in two steps:
  (1) for numbers m - m = 0; m - m != 0 only for a `sample`, where each
      occurrence is a separate act of measurement;
  (2) `==` over numbers is arithmetic, so `m == m` is true. The ZTL table
      (Z <-> Z = F) belongs to the logical connective, not to numbers:
      «в логике не бывает m==m, а бывает m nxor m».
The judge used to bound each side of a comparison separately; the solver
read the difference of the sides. This stand holds them to one meaning.

It also guards two defects the same day's audit found on the live service:
  * `1/inf` was the float 0.0, which the floor took for an infinity: it
    printed as -∞ and refuted `k == 0/d` for an int k that can be 0;
  * an interval with a negative bound, `[-1,1]`, could not be read at all.

Guards: the instances; SOUND against the decided semantics (one value per
name for the whole claim) on an enumerated integer pool; REFINES — whenever
the separate bounds already decide, the joint reading agrees — on an integer
pool and on a pool with infinities. Fails on the floor before the decision.
Run: python3 test_numeric_names.py  ->  NUMERIC NAMES GREEN
"""
import itertools
import sys
from fractions import Fraction

import znum
import znumjudge

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


INF = znum.INF
qi = {"m": znum.qty(0, 9, discrete="int"), "x": znum.qty(0, 10)}
check(znum.compare("eq", "m", "m", qi)[0] == "T", "m == m: one number")
check(znum.compare("eq", ("sub", "m", "m"), 0, qi)[0] == "T", "m - m == 0: one number")
check(znum.compare("le", "x", ("add", "x", 1), qi)[0] == "T", "x <= x + 1")
check(znum.compare("lt", "x", "x", qi)[0] == "F", "x < x is false")
check(znum.compare("eq", ("add", "x", "x"), ("mul", 2, "x"), qi)[0] == "T", "x + x == 2*x")
check(znum.compare("le", "x", ("add", "m", 1), qi)[0] == "Z", "different names stay undecided")
qs = {"s": znum.qty(0, 9, discrete="int", sample=True)}
check(znum.compare("eq", "s", "s", qs)[0] == "Z", "a sample: two acts, two numbers")
check(znum.compare("eq", ("sub", "s", "s"), 0, qs)[0] == "Z", "a sample: s - s is not 0")
qp = {"m": znum.qty(5, 5, discrete="int")}
check(znum.compare("eq", "m", "m", qp)[0] == "T", "a pinned number")
qu = {"m": znum.qty(-INF, INF)}
check(znum.compare("eq", ("sub", "m", "m"), 0, qu)[0] == "T", "m - m == 0 even unbounded (no 0*inf)")
qc = {"stone": znum.qty(-INF, INF), "capacity": znum.qty(INF, INF)}
check(znum.compare("lt", "capacity", "stone", qc)[0] == "F", "the stone against an unlimited capacity stays refuted")
qz = {"k": znum.qty(0, 1, discrete="int"), "n": znum.qty(0, 0, znum.EARNED, "doc"), "d": znum.qty(2, INF)}
check(znum.compare("eq", "k", ("div", "n", "d"), qz)[0] == "Z", "k == 0/d is not refuted: k can be 0")
lo = znum.ev(("div", 1, "d"), qz)[0][0]
check(lo == 0 and not isinstance(lo, float) and znum.fmt(lo) == "0", "1/inf is an exact zero, printed 0")
qn, _ = znumjudge.parse_quantities("t=[-1,1] earned:doc")
try:
    readable = znumjudge.judge_sheet_claim("t == [-1,1] | t <= 5", qn, {})["disposition"] != "E"
except ValueError:                     # the old reader died on the minus inside [ ]
    readable = False
check(readable, "an interval with a negative bound is readable")

LEAVES = ["x", "y", 1, 2]
EXPRS = LEAVES + [(op, a, b) for op in ("add", "sub", "mul") for a in LEAVES for b in LEAVES]
REL = {"le": lambda a, b: a <= b, "lt": lambda a, b: a < b, "eq": lambda a, b: a == b}


def val(e, nu):
    if isinstance(e, str):
        return Fraction(nu[e])
    if not isinstance(e, tuple):
        return Fraction(e)
    a, b = val(e[1], nu), val(e[2], nu)
    return {"add": a + b, "sub": a - b, "mul": a * b}[e[0]]


def separate(kind, r1, r2):
    if kind == "le":
        return "T" if r1[1] <= r2[0] else ("F" if r1[0] > r2[1] else "Z")
    if kind == "lt":
        return "T" if r1[1] < r2[0] else ("F" if r1[0] >= r2[1] else "Z")
    d = znum._iv_sub(r1, r2)
    return "T" if d == (0, 0) else ("F" if d[0] > 0 or d[1] < 0 else "Z")


pool = lies = overturned = 0
for ix, iy in itertools.product([(0, 1), (-2, 2), (2, 2)], repeat=2):
    q = {"x": znum.qty(*ix, discrete="int"), "y": znum.qty(*iy, discrete="int")}
    nus = [{"x": a, "y": b} for a in range(ix[0], ix[1] + 1) for b in range(iy[0], iy[1] + 1)]
    for e1, e2 in itertools.product(EXPRS, repeat=2):
        r1, r2 = znum._ev(e1, q)[0], znum._ev(e2, q)[0]
        for kind, rel in REL.items():
            pool += 1
            v = znum.compare(kind, e1, e2, q)[0]
            seen = {rel(val(e1, nu), val(e2, nu)) for nu in nus}          # one value per name
            if (v == "T" and seen != {True}) or (v == "F" and seen != {False}):
                lies += 1
            old = separate(kind, r1, r2)
            if old in ("T", "F") and v != old:
                overturned += 1
check(lies == 0, f"SOUND on {pool} claims ({lies} verdicts the semantics does not force)")
check(overturned == 0, f"REFINES on {pool} claims ({overturned} overturned)")

BOUNDS = [(-INF, INF), (INF, INF), (0, INF), (-INF, 0), (1, 3)]
LIN = ["x", "y", 1, ("add", "x", "y"), ("sub", "x", "y"), ("sub", "x", "x"), ("add", "x", 1)]
inf_pool = inf_overturned = 0
for bx, by in itertools.product(BOUNDS, repeat=2):
    q = {"x": znum.qty(*bx), "y": znum.qty(*by)}
    for e1, e2 in itertools.product(LIN, repeat=2):
        r1, r2 = znum._ev(e1, q)[0], znum._ev(e2, q)[0]
        for kind in REL:
            inf_pool += 1
            old = separate(kind, r1, r2)
            if old in ("T", "F") and znum.compare(kind, e1, e2, q)[0] != old:
                inf_overturned += 1
check(inf_overturned == 0, f"REFINES with infinities on {inf_pool} claims ({inf_overturned} overturned)")

print(f"NUMERIC NAMES GREEN — {CHECKS} checks, pool of {pool} claims: 0 unforced, 0 overturned")
