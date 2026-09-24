# -*- coding: utf-8 -*-
"""
test_higher_degree — one name to a higher degree: critical points and Sturm.

MEASURED 2026-09-24: beyond the parabola a polynomial in one name fell back
to separate interval arithmetic — x*x*x - 6*x*x + 11*x - 6 == 0 with x = ?
was OPEN though its roots are 1, 2 and 3. Now the judge takes the range of a
polynomial of degree >= 3 over the box from its ends and its critical points
(roots of the derivative, isolated by Sturm in exact rationals, an irrational
one bounded by interval Horner over its clamp), and the solver takes its real
roots: rational ones exact, a quadratic factor left over exactly (p + q·√d),
the rest clamped (x*x*x == 2 stays OPEN, ≈1.25992104989: a cubic irrational is
not held exactly — said, not hidden).
Guards: SOUND on an exhaustive integer pool; REFINES the separate reading;
roots of random products (x - r1)(x - r2)... found exactly; every clamp
brackets a sign change of the square-free part; no root means REFUTED.
Run: python3 test_higher_degree.py  ->  HIGHER DEGREE GREEN
"""
import itertools
import random
import sys
from fractions import Fraction

import znum
import zfl
from znum import qty, EARNED

CHECKS = 0


def check(cond, what):
    global CHECKS
    CHECKS += 1
    if not cond:
        print("FAIL:", what)
        sys.exit(1)


def value(e, x):
    if isinstance(e, (int, Fraction)):
        return Fraction(e)
    if isinstance(e, str):
        return Fraction(x)
    op, a, b = e
    a, b = value(a, x), value(b, x)
    return {"add": a + b, "sub": a - b, "mul": a * b}[op]


def separate(kind, r1, r2):
    if kind == "le":
        return "T" if r1[1] <= r2[0] else ("F" if r1[0] > r2[1] else "Z")
    if kind == "lt":
        return "T" if r1[1] < r2[0] else ("F" if r1[0] >= r2[1] else "Z")
    d = znum._iv_sub(r1, r2)
    return "T" if d == (0, 0) else ("F" if d[0] > 0 or d[1] < 0 else "Z")


X2 = ("mul", "x", "x")
X3 = ("mul", X2, "x")
X4 = ("mul", X3, "x")
EXPRS = [X3, ("sub", X3, ("mul", 3, "x")), ("add", ("sub", X3, ("mul", 6, X2)), ("add", ("mul", 11, "x"), -6)),
         ("sub", X4, ("mul", 5, X2)), ("add", ("sub", X4, ("mul", 2, X2)), 2), ("sub", X3, X2), 0, 4, -2]
REL = {"le": lambda a, b: a <= b, "lt": lambda a, b: a < b, "eq": lambda a, b: a == b}
pool = decided = refined = 0
for box in [(-3, 3), (0, 3), (-2, 0), (1, 2), (2, 2)]:
    q = {"x": qty(*box, EARNED, "g", discrete="int")}
    xs = range(box[0], box[1] + 1)
    for e1, e2 in itertools.product(EXPRS, repeat=2):
        r1, r2 = znum._ev(e1, q)[0], znum._ev(e2, q)[0]
        for kind, rel in REL.items():
            pool += 1
            v = znum.compare(kind, e1, e2, q)[0]
            truths = {rel(value(e1, x), value(e2, x)) for x in xs}
            if v == "T":
                check(truths == {True}, f"UNSOUND T: {kind} {e1} {e2} on {box}")
            if v == "F":
                check(truths == {False}, f"UNSOUND F: {kind} {e1} {e2} on {box}")
            decided += v in ("T", "F")
            if r1 is not None and r2 is not None:
                old = separate(kind, r1, r2)
                if old in ("T", "F"):
                    check(v == old, f"OVERTURNED {old}->{v}: {kind} {e1} {e2} on {box}")
                elif v in ("T", "F"):
                    refined += 1
check(refined > 0, f"critical points decide claims the separate bounds could not ({refined})")


def unknown():
    return {"name": "x", "means": "the number sought", "status": "unverified", "value": "?"}


def poly_text(coeffs):
    terms = []
    for k, c in enumerate(coeffs):
        if c == 0:
            continue
        mono = "*".join(["x"] * k)
        terms.append(f"({c})" + (f"*{mono}" if mono else ""))
    return " + ".join(terms) or "0"


rng = random.Random(20260924)
for _ in range(60):
    roots = sorted(set(Fraction(rng.randint(-6, 6), rng.choice([1, 1, 2, 3])) for _ in range(rng.randint(3, 4))))
    coeffs = [Fraction(1)]
    for r in roots:
        coeffs = znum._pmul(coeffs, [-r, Fraction(1)])
    lcm = 1
    for c in coeffs:
        lcm = lcm * c.denominator // __import__("math").gcd(lcm, c.denominator)
    ints = [int(c * lcm) for c in coeffs]
    n = zfl.run({"rows": [unknown()], "claim": poly_text(ints) + " == 0"})["report"]["numeric"]
    got = (n["solved"].get("x") or {}).get("roots") or ([n["solved"]["x"]["lo"]] if n["solved"].get("x", {}).get("pinned") else [])
    check(n["disposition"] == "EARNED" and got == [str(r) for r in roots],
          f"roots of {poly_text(ints)}: {n['disposition']} {got}, want {[str(r) for r in roots]}")
for _ in range(60):
    coeffs = [Fraction(rng.randint(-9, 9)) for _ in range(rng.randint(4, 6))]
    if coeffs[-1] == 0:
        coeffs[-1] = Fraction(1)
    rs = znum._real_roots(coeffs)
    sq = znum._sturm(coeffs)[0]
    for l, h in rs:
        if l == h:
            check(znum._peval(coeffs, l) == 0, f"{coeffs}: {l} is not a root")
        else:
            check(znum._peval(sq, l) * znum._peval(sq, h) < 0, f"{coeffs}: no sign change in [{l}, {h}]")
    grid = [Fraction(k, 4) for k in range(-80, 81)]
    changes = sum(1 for a, b in zip(grid, grid[1:]) if znum._peval(sq, a) * znum._peval(sq, b) < 0
                  or znum._peval(sq, b) == 0)
    check(len(rs) >= changes, f"{coeffs}: {len(rs)} roots found, the grid sees {changes}")

for claim, want, roots in [("x*x*x - 6*x*x + 11*x - 6 == 0", "EARNED", ["1", "2", "3"]),
                           ("(x*x - 2)*(x - 1) == 0", "EARNED", ["-√2", "1", "√2"]),
                           ("x*x*x*x + 1 == 0", "REFUTED", None),
                           ("x*x*x == 2", "OPEN", ["≈1.25992104989"])]:
    n = zfl.run({"rows": [unknown()], "claim": claim})["report"]["numeric"]
    check(n["disposition"] == want and (n["solved"].get("x") or {}).get("roots") == roots,
          f"{claim}: {n['disposition']} {(n['solved'].get('x') or {}).get('roots')}")
q = {"x": qty(0, 3, EARNED, "g")}
check(znum.compare("le", -2, ("sub", X3, ("mul", 3, "x")), q)[0] == "T", "x^3 - 3x >= -2 on [0,3] (minimum -2 at x = 1)")
check(znum.compare("lt", -2, ("sub", X3, ("mul", 3, "x")), q)[0] == "Z", "x^3 - 3x > -2 on [0,3] is Z (equal at x = 1)")
print(f"HIGHER DEGREE GREEN — {CHECKS} checks; pool of {pool} claims, {decided} decided, "
      f"{refined} decided that the separate bounds left open, 0 unsound, 0 overturned")
