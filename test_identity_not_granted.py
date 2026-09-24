# -*- coding: utf-8 -*-
"""
test_identity_not_granted — `m == m` is NOT a truth while `m` is unverified.

ZTL does not grant identity on credit (`V.ax_xnor_ZZ : zxnor Z Z = F` —
self-identity is not certified). On the numeric floor a name co-refers
WITHIN a term (2026-08-11: `m - m` is 0, `x + x` is `2x`), but the two sides
of a comparison are two readings, and identifying them is exactly the
identity ZTL refuses to grant unverified. This is what `lean/ZNumCoherent.lean`
defines (`ForcedEQ m a b := ∀ x y, CReads m a x → CReads m b y → x = y`).

Why the stand exists: on 2026-09-24 the assistant took the classical prior
for the reference semantics (one assignment for both sides), called 10,122
correct refusals "misses", "fixed" them and deployed the fix; the curator
caught it the same hour ("m==m — это False ... если m не проверен"), and it
was reverted. This stand fails on that version at its first check.

Guards: the instances; SOUND against the semantics above on an enumerated
integer pool (each side read coherently, the sides independently).
Run: python3 test_identity_not_granted.py  ->  IDENTITY NOT GRANTED GREEN
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


qi = {"m": znum.qty(0, 9, discrete="int"), "x": znum.qty(0, 10)}
check(znum.compare("eq", "m", "m", qi)[0] != "T", "m == m is not granted while m is unverified")
check(znum.compare("le", "x", ("add", "x", 1), qi)[0] != "T", "x <= x + 1 is not granted either")
check(znum.compare("eq", ("sub", "m", "m"), 0, qi)[0] == "T", "m - m == 0: a name co-refers WITHIN a term")
qp = {"m": znum.qty(5, 5, discrete="int")}
check(znum.compare("eq", "m", "m", qp)[0] == "T", "verified to a point, identity is exhibited")
INF = znum.INF
qc = {"stone": znum.qty(-INF, INF), "capacity": znum.qty(INF, INF)}
check(znum.compare("lt", "capacity", "stone", qc)[0] == "F", "the stone against an unlimited capacity stays refuted")

LEAVES = ["x", "y", 1, 2]
EXPRS = LEAVES + [(op, a, b) for op in ("add", "sub", "mul") for a in LEAVES for b in LEAVES]


def val(e, nu):
    if isinstance(e, str):
        return Fraction(nu[e])
    if not isinstance(e, tuple):
        return Fraction(e)
    a, b = val(e[1], nu), val(e[2], nu)
    return {"add": a + b, "sub": a - b, "mul": a * b}[e[0]]


pool = lies = 0
for ix, iy in itertools.product([(0, 1), (-2, 2), (2, 2)], repeat=2):
    qs = {"x": znum.qty(*ix, discrete="int"), "y": znum.qty(*iy, discrete="int")}
    nus = [{"x": a, "y": b} for a in range(ix[0], ix[1] + 1) for b in range(iy[0], iy[1] + 1)]
    for e1, e2 in itertools.product(EXPRS, repeat=2):
        left, right = {val(e1, nu) for nu in nus}, {val(e2, nu) for nu in nus}   # each side on its own
        forced = {
            "le": ("T" if max(left) <= min(right) else "F" if min(left) > max(right) else "Z"),
            "lt": ("T" if max(left) < min(right) else "F" if min(left) >= max(right) else "Z"),
            "eq": ("T" if len(left) == len(right) == 1 and left == right else "F" if not (left & right) else "Z"),
        }
        for kind, sem in forced.items():
            pool += 1
            v = znum.compare(kind, e1, e2, qs)[0]
            if v in ("T", "F") and v != sem:
                lies += 1
check(lies == 0, f"SOUND on {pool} claims ({lies} verdicts the semantics does not force)")

print(f"IDENTITY NOT GRANTED GREEN — {CHECKS} checks, pool of {pool} claims: 0 unforced verdicts")
