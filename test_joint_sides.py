# -*- coding: utf-8 -*-
"""
test_joint_sides — the two sides of a numeric comparison are read TOGETHER.

Until 2026-09-24 `znum.compare` bounded each side separately, so a name on
both sides lost co-reference: `m == m` came back Z while `m - m == 0` came
back T. Measured before the fix (lab, 120,384 integer claims): 10,122 of the
37,860 linear claims with a shared name were left Z although the coherent
semantics forces them; after it, 616, with not one flipped verdict and not
one false one. Forecast frozen first: inventory/probes/FORECAST-NUMERIC-ALGORITHM-2026-09-24.md

What this stand guards:
  1. the instances that were wrong stay right;
  2. SOUND: on an enumerated integer pool no T/F contradicts the coherent
     semantics (one value per name);
  3. REFINES: whenever the old separate bounds already decide, the joint
     reading agrees — the fix can only turn Z into a verdict, never overturn.
Run: python3 test_joint_sides.py  ->  JOINT SIDES GREEN
"""
import itertools
import sys
from fractions import Fraction

import znum

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


# 1. the instances
qi = {"m": znum.qty(0, 9, discrete="int"), "x": znum.qty(0, 10)}
check(znum.compare("eq", "m", "m", qi)[0] == "T", "m == m is forced true")
check(znum.compare("eq", ("sub", "m", "m"), 0, qi)[0] == "T", "m - m == 0 stays true")
check(znum.compare("le", "x", ("add", "x", 1), qi)[0] == "T", "x <= x + 1 is forced true")
check(znum.compare("lt", "x", "x", qi)[0] == "F", "x < x is forced false")
check(znum.compare("lt", ("add", "x", 1), "x", qi)[0] == "F", "x + 1 < x is forced false")
check(znum.compare("le", "x", ("add", "m", 1), qi)[0] == "Z", "different names stay undecided")
qu = {"m": znum.qty(-znum.INF, znum.INF)}
check(znum.compare("eq", "m", "m", qu)[0] == "T", "m == m even unbounded")
check(znum.compare("eq", ("sub", "m", "m"), 0, qu)[0] == "T", "m - m == 0 even unbounded (no 0*inf)")
check(not znum.bounds_bearing("eq", "m", "m", {"m": znum.qty(0, 9)}, "m"),
      "m == m does not ride on m's bounds")
qs = {"s": znum.qty(0, 9, sample=True)}
check(znum.compare("eq", "s", "s", qs)[0] == "Z", "a SAMPLE is still read per occurrence")

# 2 and 3. an enumerated integer pool
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
    qs = {"x": znum.qty(*ix, discrete="int"), "y": znum.qty(*iy, discrete="int")}
    nus = [{"x": a, "y": b} for a in range(ix[0], ix[1] + 1) for b in range(iy[0], iy[1] + 1)]
    for e1, e2 in itertools.product(EXPRS, repeat=2):
        r1, r2 = znum._ev(e1, qs)[0], znum._ev(e2, qs)[0]
        for kind, rel in REL.items():
            pool += 1
            v = znum.compare(kind, e1, e2, qs)[0]
            seen = {rel(val(e1, nu), val(e2, nu)) for nu in nus}
            if (v == "T" and seen != {True}) or (v == "F" and seen != {False}):
                lies += 1
            old = separate(kind, r1, r2)
            if old in ("T", "F") and v != old:
                overturned += 1
check(lies == 0, f"SOUND on {pool} claims ({lies} false verdicts)")

# 4. infinities: a quantity pinned AT +inf, unbounded and half-bounded ones.
# Found by the full regression (dilemmas/omnipotence.py) after the first
# version of the fix: inf + -inf made the joint difference nan and the stone
# against an unlimited capacity came back OPEN instead of REFUTED. There is
# no finite enumeration here, so the guard is REFINES alone.
INF = znum.INF
qc = {"stone": znum.qty(-INF, INF), "capacity": znum.qty(INF, INF)}
check(znum.compare("lt", "capacity", "stone", qc)[0] == "F",
      "a stone heavier than an unlimited capacity stays refuted")
BOUNDS = [(-INF, INF), (INF, INF), (0, INF), (-INF, 0), (1, 3)]
LIN = ["x", "y", 1, ("add", "x", "y"), ("sub", "x", "y"), ("sub", "x", "x"), ("add", "x", 1)]
inf_pool = inf_overturned = 0
for bx, by in itertools.product(BOUNDS, repeat=2):
    qq = {"x": znum.qty(*bx), "y": znum.qty(*by)}
    for e1, e2 in itertools.product(LIN, repeat=2):
        r1, r2 = znum._ev(e1, qq)[0], znum._ev(e2, qq)[0]
        for kind in REL:
            inf_pool += 1
            old_v = separate(kind, r1, r2)
            if old_v in ("T", "F") and znum.compare(kind, e1, e2, qq)[0] != old_v:
                inf_overturned += 1
check(inf_overturned == 0, f"REFINES with infinities on {inf_pool} claims ({inf_overturned} overturned)")
check(overturned == 0, f"REFINES on {pool} claims ({overturned} overturned)")

print(f"JOINT SIDES GREEN — {CHECKS} checks, pool of {pool} claims: 0 false, 0 overturned")
