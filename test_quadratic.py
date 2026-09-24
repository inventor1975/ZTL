# -*- coding: utf-8 -*-
"""
test_quadratic — a name that multiplies itself is still one number.

The curator's question, 2026-09-24: "X*X-2X+5=0 — will it solve it?"
MEASURED on the live studio that day: `x*x - 2*x + 5 == 0` over the reals,
and even `(x-1)*(x-1) + 4 == 0`, came back OPEN, x in x*x being read as two
independent numbers; with x = ? the solver answered OPEN "measure x". The
truth is REFUTED: (x-1)^2 + 4 >= 4, the discriminant is 4 - 20 = -16.

Two readings, one degree above the linear ones:
  * the judge reads the difference of the sides as a sum of parabolas, one
    per name, and takes its exact range (ends and vertex);
  * the solver finds the roots of a parabola in one unknown from the
    discriminant: D < 0 refutes, D = 0 pins, D > 0 keeps BOTH roots
    (the curator: «корня-то два») and judges the claim at each.

Systems too: with each power of a name its own column, elimination is exact
linear algebra and a row left in one name is solved (the curator's plot,
"area == s*s & area - 2*s + 5 == 0", is REFUTED).
Guards: the instances; SOUND on an exhaustive integer pool (T holds at
every point of the box, F at none); REFINES (where the separate bounds
decided, the new reading agrees); the solver's roots satisfy their equation
exactly and no integer root is missed. Fails on the floor before the change.
Run: python3 test_quadratic.py  ->  QUADRATIC GREEN
"""
import itertools
import sys
from fractions import Fraction

import znum
import zfl

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def run(rows, claim):
    return zfl.run({"rows": rows, "claim": claim})


def unknown(name="x", **kw):
    return dict({"name": name, "means": "the number sought", "status": "unverified",
                 "value": "?"}, **kw)


def measured(value, name="X"):
    return {"name": name, "means": "a measured number", "status": "verified",
            "ground": "doc-1", "value": value}


def numeric(r):
    check(r["ok"], f"the run answered: {r.get('issues')}")
    return r["report"]["numeric"]


# 1. the judge, x measured
for value, claim, want in [
        ("[-inf,inf]", "X*X-2*X+5==0", "REFUTED"),
        ("[-inf,inf]", "(X-1)*(X-1)+4==0", "REFUTED"),
        ("[0,9]", "X*X-2*X+5==0", "REFUTED"),
        ("[-inf,inf]", "X*X-2*X+5>0", "EARNED"),
        ("[-inf,inf]", "X*X-2*X+5>=4", "EARNED"),
        ("[-inf,inf]", "X*X-2*X+5>=5", "OPEN"),
        ("[0,9]", "X*X==4", "OPEN"),
        ("[-inf,inf]", "X*X>=0", "EARNED"),
        ("[3,9]", "X*X-5*X+6>0", "OPEN"),      # (X-2)(X-3) is 0 at X = 3
        ("[3,9]", "X*X-5*X+6>=0", "EARNED"),
]:
    got = numeric(run([measured(value)], claim))["disposition"]
    check(got == want, f"X in {value}: {claim} -> {got}, want {want}")

# 2. the solver, x = ?
for claim, kw, want, roots in [
        ("x*x - 2*x + 5 == 0", {}, "REFUTED", None),
        ("x*x - 2*x + 5 = 0", {}, "REFUTED", None),
        ("(x-1)*(x-1) + 4 == 0", {}, "REFUTED", None),
        ("x*x == 4", {}, "EARNED", ["-2", "2"]),
        ("x*x - 5*x + 6 = 0", {}, "EARNED", ["2", "3"]),
        ("x*x == 2", {}, "OPEN", ["≈-1.41421356237", "≈1.41421356237"]),
        ("x*x == 2", {"scale": "int"}, "REFUTED", None),
]:
    n = numeric(run([unknown(**kw)], claim))
    check(n["disposition"] == want, f"x = ?: {claim} {kw} -> {n['disposition']}, want {want}")
    got = (n["solved"].get("x") or {}).get("roots")
    check(got == roots, f"x = ?: {claim} {kw}: roots {got}, want {roots}")
    if want == "REFUTED":
        check(not n.get("missing"), f"{claim}: a refuted question asks for no more facts")
for claim, value in [("x*x == 4 & x > 0", "2"), ("x*x - 2*x + 1 == 0", "1"), ("2*x + 3 == 7", "2")]:
    n = numeric(run([unknown()], claim))
    sx = n["solved"]["x"]
    check(n["disposition"] == "EARNED" and sx["pinned"] and sx["lo"] == value,
          f"x = ?: {claim} -> {n['disposition']} {sx}")
check(numeric(run([unknown()], "x*x == 4"))["solved"]["x"]["prov"] == "earned",
      "two exact roots derived from constants are earned, like an eliminated value")

# 3. SOUND on an exhaustive integer pool, and REFINES against the separate bounds
REL = {"le": lambda a, b: a <= b, "lt": lambda a, b: a < b, "eq": lambda a, b: a == b}


def separate(kind, r1, r2):
    if kind == "le":
        return "T" if r1[1] <= r2[0] else ("F" if r1[0] > r2[1] else "Z")
    if kind == "lt":
        return "T" if r1[1] < r2[0] else ("F" if r1[0] >= r2[1] else "Z")
    d = znum._iv_sub(r1, r2)
    return "T" if d == (0, 0) else ("F" if d[0] > 0 or d[1] < 0 else "Z")


def value(e, nu):
    if isinstance(e, (int, Fraction)):
        return Fraction(e)
    if isinstance(e, str):
        return Fraction(nu[e])
    op, a, b = e
    a, b = value(a, nu), value(b, nu)
    return {"add": a + b, "sub": a - b, "mul": a * b}[op]


X2, Y2 = ("mul", "x", "x"), ("mul", "y", "y")
EXPRS = [X2, ("sub", X2, ("mul", 2, "x")), ("add", ("sub", X2, ("mul", 4, "x")), 3),
         ("mul", ("sub", "x", 1), ("add", "x", 2)), ("sub", ("mul", 3, "x"), X2),
         ("add", X2, Y2), ("sub", X2, "y"), ("add", ("mul", "x", ("sub", 1, "x")), "y"),
         ("sub", ("mul", 2, Y2), ("mul", 3, "y")), "x", 0, 5, -3]
pool = decided = refined = 0
for ix, iy in itertools.product([(-3, 3), (0, 4), (-5, -1), (2, 2)], repeat=2):
    q = {"x": znum.qty(*ix, discrete="int"), "y": znum.qty(*iy, discrete="int")}
    nus = [{"x": a, "y": b} for a in range(ix[0], ix[1] + 1) for b in range(iy[0], iy[1] + 1)]
    for e1, e2 in itertools.product(EXPRS, repeat=2):
        r1, r2 = znum._ev(e1, q)[0], znum._ev(e2, q)[0]
        for kind, rel in REL.items():
            pool += 1
            v = znum.compare(kind, e1, e2, q)[0]
            truths = {rel(value(e1, nu), value(e2, nu)) for nu in nus}
            if v == "T":
                check(truths == {True}, f"UNSOUND T: {kind} {e1} {e2} on {ix},{iy}")
            if v == "F":
                check(truths == {False}, f"UNSOUND F: {kind} {e1} {e2} on {ix},{iy}")
            if v in ("T", "F"):
                decided += 1
            if r1 is not None and r2 is not None:
                old = separate(kind, r1, r2)
                if old in ("T", "F"):
                    check(v == old, f"OVERTURNED {old}->{v}: {kind} {e1} {e2} on {ix},{iy}")
                elif v in ("T", "F"):
                    refined += 1
check(refined > 0, f"the parabola reading decides claims the separate bounds could not ({refined})")

# 4. the solver: exact roots satisfy their equation; no integer root is missed
for a, b, c in itertools.product([1, -1, 2, -3], [-5, -2, 0, 3], [-6, -1, 0, 4, 5]):
    claim = f"{a}*x*x + {b}*x + {c} == 0"
    d = b * b - 4 * a * c
    n = numeric(run([unknown()], claim))
    if d < 0:
        check(n["disposition"] == "REFUTED", f"{claim}: D = {d} < 0 must refute, got {n['disposition']}")
        continue
    sx = n["solved"].get("x") or {}
    got = sx.get("roots") or ([sx["lo"]] if sx.get("pinned") else [])
    check(len(got) == (1 if d == 0 else 2), f"{claim}: D = {d}, roots {got}")
    for t in got:
        if not t.startswith("≈"):
            r = Fraction(t)
            check(a * r * r + b * r + c == 0, f"{claim}: {t} is not a root")
    ni = numeric(run([unknown(scale="int")], claim))
    ints = [r for r in range(-50, 51) if a * r * r + b * r + c == 0]
    si = ni["solved"].get("x") or {}
    got_i = sorted(int(t) for t in (si.get("roots") or ([si["lo"]] if si.get("pinned") else [])))
    if ints:
        check(got_i == ints, f"{claim} over the integers: {got_i}, want {ints}")
    else:
        check(ni["disposition"] == "REFUTED", f"{claim} over the integers: no root, got {ni['disposition']}")

# 5. systems: each power of a name its own column (the curator's plot, 2026-09-24:
#    "the area minus twice the side plus 5 is zero" came back as two rows)
for rows, claim in [([unknown("s"), unknown("area")], "(area == s*s) & (area - 2*s + 5 == 0)"),
                    ([unknown("side"), unknown("A")], "A == side*side & A - 2*side + 5 == 0")]:
    n = numeric(run(rows, claim))
    check(n["disposition"] == "REFUTED" and not n.get("missing"), f"the plot {claim!r} -> {n['disposition']}")
n = numeric(run([unknown("s"), unknown("area")], "area == s*s & area - 5*s + 6 == 0"))
check(n["solved"]["s"].get("roots") == ["2", "3"] and n["solved"]["area"].get("roots") == ["4", "9"],
      f"a system with two roots pairs them: {n['solved']}")
# unknowns derived from unknowns ride credit, exactly as the linear system's do
lin = numeric(run([unknown("x"), unknown("y")], "x + y == 10 & x - y == 2"))["disposition"]
check(n["disposition"] == lin, f"the system's disposition {n['disposition']} is the linear system's {lin}")
for a, b, c, d, e in itertools.product([1, 2], [-3, 0, 1], [-4, 0, 5], [-2, 1], [-6, 0, 3]):
    claim = f"u == {a}*s*s + {b}*s + {c} & u + {d}*s + {e} == 0"
    # substitute: a s² + (b + d) s + (c + e) = 0
    A, B, C = a, b + d, c + e
    D = B * B - 4 * A * C
    n = numeric(run([unknown("s"), unknown("u")], claim))
    if D < 0:
        check(n["disposition"] == "REFUTED", f"{claim}: no real s (D = {D}), got {n['disposition']}")
        continue
    sx = n["solved"].get("s") or {}
    got = sx.get("roots") or ([sx["lo"]] if sx.get("pinned") else [])
    check(len(got) == (1 if D == 0 else 2), f"{claim}: D = {D}, s = {got}")
    for t in got:
        if not t.startswith("≈"):
            r = Fraction(t)
            check(A * r * r + B * r + C == 0, f"{claim}: s = {t} does not solve the system")

# 6. the root of a known number is a constant when it is exact (MEASURED
#    2026-09-24: a live model's table computing the discriminant stopped at
#    OPEN, sqrtD == sqrt(disc) unread though disc was known)
names = ["a", "b", "c", "disc", "sqrtD", "x1", "x2", "x"]
table = ("a == 1 & b == -5 & c == 6 & disc == b*b - 4*a*c & sqrtD == sqrt(disc) & "
         "x1 == (-b + sqrtD) / (2*a) & x2 == (-b - sqrtD) / (2*a) & x == x1")
n = numeric(run([unknown(nm) for nm in names], table))
sv = {k: v["lo"] for k, v in n["solved"].items() if v["pinned"]}
check(n["disposition"] == "EARNED" and sv.get("sqrtD") == "1" and sv.get("x") == "3"
      and sv.get("x2") == "2", f"the discriminant table is followed to the root: {n['disposition']} {sv}")
n = numeric(run([unknown("r")], "r == sqrt(9) + 1"))
check(n["disposition"] == "EARNED" and n["solved"]["r"]["lo"] == "4", f"sqrt(9) + 1 is 4: {n}")
n = numeric(run([unknown("r")], "r == sqrt(2)"))
check(n["disposition"] == "OPEN", f"sqrt(2) is not a constant of the rational floor: {n['disposition']}")

# 7. one of several equalities of one unknown is a set of roots (the curator's
#    word, 2026-09-24: "read x == 2 | x == 3 as its roots"); anything else in
#    the disjunction and it narrows nothing, as before
for claim, want, roots in [("x == 2 | x == 3", "EARNED", ["2", "3"]),
                           ("x*x == 4 | x == 5", "EARNED", ["-2", "2", "5"]),
                           ("(x == 2 | x == 3) & x > 7", "REFUTED", None),
                           ("x == 2 | x > 5", "OPEN", None)]:
    n = numeric(run([unknown()], claim))
    got = (n["solved"].get("x") or {}).get("roots")
    check(n["disposition"] == want and got == roots, f"{claim}: {n['disposition']} {got}, want {want} {roots}")
n = numeric(run([unknown()], "(x == 2 | x == 3) & x > 2"))
check(n["disposition"] == "EARNED" and n["solved"]["x"]["lo"] == "3", f"(x == 2 | x == 3) & x > 2 is x = 3: {n}")
n = numeric(run([unknown(nm) for nm in names], table.replace("& x == x1", "& (x == x1 | x == x2)")))
check(n["disposition"] == "EARNED" and n["solved"]["x"].get("roots") == ["2", "3"],
      f"the model's table with (x == x1 | x == x2) reaches x = 2 or 3: {n['disposition']} {n['solved'].get('x')}")

print(f"QUADRATIC GREEN — {CHECKS} checks; pool of {pool} claims, {decided} decided, "
      f"{refined} decided that the separate bounds left open, 0 unsound, 0 overturned")
