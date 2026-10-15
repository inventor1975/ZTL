# -*- coding: utf-8 -*-
"""
Stand for zlin.py: a bound on one unknown of a linear system A(p) x = b(p) over a box of p, proved by a brought
certificate, checked by the kernel exactly and without a budget.

The certificates come from a SEARCHER written in this file (floats for R and x~, the kernel's own sign reads to choose
the pins, a split of the widest piece when nothing pins) — the kind that lives outside the kernel. The kernel does not
trust it: every claim is also decided by a different route — every corner of the box solved exactly in fractions
(the extremes of a monotone unknown sit at corners; where it is not monotone the corners only bound it from inside).

Checks:
  1. a resistor ladder, 3 unknowns, 7 tolerances: the max and the min over all 128 exact corners are PROVED with no
     slack; a bound a billionth inside is refused, the same certificate included;
  2. MUTATIONS refused: a flipped sign, a zero R, an exact leaf on a piece that is not a point, a split outside the
     piece, a pin with no signs, a grid out of range;
  3. 60 seeded random 3x3 systems, each coefficient a + c*p with p boxed: the searcher's certificate at the exact
     corner maximum is accepted where found, and NO certificate passes a bound below that maximum;
  4. MUTATION of the kernel: every coefficient read at the piece's centre (a lying reading) — a false bound slips
     through, so this stand sees a lying kernel;
  5. a ladder of 12 unknowns (25 tolerances; beyond Cramer's 6): the exact worst case found and proved.
Run: python3 test_zlin.py
"""
import itertools
import random
import sys
from fractions import Fraction as F

import zlin as Z
from znumjudge import parse_quantities

FAILS, CHECKS = [], [0]


def check(cond, what):
    CHECKS[0] += 1
    if not cond:
        FAILS.append(what)
        print("  FAIL", what)
    else:
        print("  ok  ", what)


def sheet(boxes, unknowns):
    parts = [f"{n}=[{lo},{hi}] credit" for n, (lo, hi) in boxes.items()] + [f"{u}=? credit" for u in unknowns]
    return parse_quantities(", ".join(parts))[0]


def exact_solve(A, b, qs, point):
    """x at a point, exactly (the kernel's own elimination is not used: a different route)."""
    n = len(A)
    pc = {nm: (v, v) for nm, v in point.items()}
    M = [[Z._read(e, qs, pc)[0] for e in A[i]] + [Z._read(b[i], qs, pc)[0]] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c] / M[c][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[i][n] / M[i][i] for i in range(n)]


def finv(M):
    n = len(M)
    cols = [Z._fsolve(M, [1.0 if i == j else 0.0 for i in range(n)]) for j in range(n)]
    return [[cols[j][i] for j in range(n)] for i in range(n)]


def search(laws, unknowns, qs, target, op, bound, budget=400, bits=128):
    """-> a certificate (a tree under {"grid", "tree"}) or None."""
    A, b = Z.system(laws, unknowns, qs)
    k = unknowns.index(target)
    names = sorted({n for row in A for e in row for n in Z.ZC._names(e)} | {n for e in b for n in Z.ZC._names(e)})
    up = op == "<="
    spent = [0]
    q = lambda v: F(int(round(v * Z.G)), Z.G)

    def go(piece, depth):
        spent[0] += 1
        if spent[0] > budget or depth > 60:
            raise StopIteration
        wide = [n for n in names if piece[n][0] != piece[n][1]]
        if not wide:
            xk = Z._solve_point(A, b, qs, piece, k)
            if (xk <= bound) if up else (xk >= bound):
                return {"leaf": "exact"}
            raise StopIteration                     # a point beyond the bound: no certificate exists
        mid = {n: ((lo + hi) / 2, (lo + hi) / 2) for n, (lo, hi) in piece.items()}
        Am = [[float(Z._read(e, qs, mid)[0]) for e in row] for row in A]
        bm = [float(Z._read(e, qs, mid)[0]) for e in b]
        Rm = finv(Am)
        xm = [sum(Rm[i][j] * bm[j] for j in range(len(bm))) for i in range(len(bm))]
        R = [[q(v) for v in row] for row in Rm]
        xt = [q(v) for v in xm]
        Rs, xs = [[str(v) for v in row] for row in R], [str(v) for v in xt]
        Ai, bi = Z._imatrix(A, qs, piece), [Z._read(e, qs, piece) for e in b]
        par = Z._param(A, b, qs, piece)
        try:
            X = Z._enclose(Ai, bi, R, xt, 0, par)[2]
            if (X[k][1] <= bound) if up else (X[k][0] >= bound):
                return {"leaf": "enclose", "R": Rs, "x": xs}
            reads = Z._dread(A, b, wide, k, qs, piece, R, xt, Ai, bi, 0, par)
        except Z.LinError:
            reads = {}
        signs = {n: ("+" if d[0] >= 0 else "-") for n, d in reads.items()
                 if not isinstance(d, str) and (d[0] >= 0 or d[1] <= 0)}
        if signs:
            to = {n: (piece[n][1] if (s == "+") == up else piece[n][0]) for n, s in signs.items()}
            return {"leaf": "pin", "signs": signs, "R": Rs, "x": xs,
                    "then": go(dict(piece, **{n: (v, v) for n, v in to.items()}), depth + 1)}
        nm = max(wide, key=lambda n: piece[n][1] - piece[n][0])
        lo, hi = piece[nm]
        at = (lo + hi) / 2
        return {"split": nm, "at": str(at), "lo": go(dict(piece, **{nm: (lo, at)}), depth + 1),
                "hi": go(dict(piece, **{nm: (at, hi)}), depth + 1)}

    piece0 = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    try:
        with Z.grid(bits):
            return {"grid": bits, "tree": go(piece0, 0)}
    except (StopIteration, Z.LinError):
        return None


def ladder(n, tol=F(1, 100)):
    boxes = {"Vs": (10 * (1 - tol), 10 * (1 + tol))}
    laws = []
    for i in range(n):
        for nm, v in ((f"R{i}", 100 + 10 * i), (f"G{i}", 200 + 10 * i)):
            boxes[nm] = (v * (1 - tol), v * (1 + tol))
    for i in range(n):
        left = "Vs" if i == 0 else f"u{i - 1}"
        right = f" + (u{i} - u{i + 1})/R{i + 1}" if i + 1 < n else ""
        laws.append(f"(({left}) - u{i})/R{i} == u{i}/G{i}{right}")
    return boxes, laws, [f"u{i}" for i in range(n)]


def corners(boxes, laws, unknowns, k):
    qs = sheet(boxes, unknowns)
    A, b = Z.system(laws, unknowns, qs)
    names = sorted(boxes)
    return [exact_solve(A, b, qs, dict(zip(names, c)))[k] for c in itertools.product(*[boxes[n] for n in names])]


print("1. a ladder of 3 unknowns, 7 tolerances: the exact extremes, no slack")
boxes, laws, un = ladder(3)
qs = sheet(boxes, un)
vals = corners(boxes, laws, un, 2)
hi, lo = max(vals), min(vals)
c_hi = search(laws, un, qs, "u2", "<=", hi)
check(c_hi is not None and Z.check(laws, un, qs, "u2", "<=", hi, c_hi)[0], "u2 <= the max of 128 exact corners: PROVED")
c_lo = search(laws, un, qs, "u2", ">=", lo)
check(c_lo is not None and Z.check(laws, un, qs, "u2", ">=", lo, c_lo)[0], "u2 >= the min of 128 exact corners: PROVED")
below = hi * (1 - F(1, 10 ** 9))
check(search(laws, un, qs, "u2", "<=", below) is None, "a billionth below the max: the searcher finds no certificate")
check(not Z.check(laws, un, qs, "u2", "<=", below, c_hi)[0], "a billionth below the max: the max's certificate refused")

print("2. mutations of an accepted certificate")


def first_pin(c):
    t = c["tree"]
    while t.get("leaf") != "pin" and "split" in t:
        t = t["lo"]
    return t if t.get("leaf") == "pin" else None


import copy
m = copy.deepcopy(c_hi)
p = first_pin(m)
check(p is not None, "the certificate has a pin leaf")
if p is not None:
    nm = next(iter(p["signs"]))
    p["signs"][nm] = "-" if p["signs"][nm] == "+" else "+"
    check(not Z.check(laws, un, qs, "u2", "<=", hi, m)[0], f"a flipped sign ({nm}): refused")
    m = copy.deepcopy(c_hi)
    first_pin(m)["R"] = [["0"] * 3 for _ in range(3)]
    check(not Z.check(laws, un, qs, "u2", "<=", hi, m)[0], "a zero R: refused (beta >= 1)")
    m = copy.deepcopy(c_hi)
    first_pin(m)["signs"] = {}
    check(not Z.check(laws, un, qs, "u2", "<=", hi, m)[0], "a pin with no signs: refused")
check(not Z.check(laws, un, qs, "u2", "<=", hi, {"leaf": "exact"})[0], "an exact leaf on the whole box: refused")
check(not Z.check(laws, un, qs, "u2", "<=", hi, {"split": "R0", "at": "1000", "lo": c_hi["tree"], "hi": c_hi["tree"]})[0],
      "a split outside the piece: refused")
check(not Z.check(laws, un, qs, "u2", "<=", hi, {"grid": 8, "tree": c_hi["tree"]})[0], "a grid of 8 bits: refused")

print("3. 60 random 3x3 systems: accepted where found, never below the corner maximum")
rnd = random.Random(20261015)
found = false_pass = 0
for t in range(60):
    boxes = {f"p{i}": (F(rnd.randint(1, 4)), F(rnd.randint(5, 8))) for i in range(3)}
    un = ["x0", "x1", "x2"]
    laws = []
    for i in range(3):
        terms = []
        for j in range(3):
            a = rnd.randint(-3, 3) if i != j else rnd.randint(30, 40)
            c = rnd.choice([0, 1, -1]) if i != j else 1
            coef = f"({a} + {c}*p{(i + j) % 3})" if c else f"({a})"
            terms.append(f"{coef}*{un[j]}")
        laws.append(" + ".join(terms) + f" == {rnd.randint(1, 9)} + p{i}")
    vals = corners(boxes, laws, un, 0)
    mx = max(vals)
    qs = sheet(boxes, un)
    c = search(laws, un, qs, "x0", "<=", mx)
    if c is not None and Z.check(laws, un, qs, "x0", "<=", mx, c)[0]:
        found += 1
    lower = mx - abs(mx) * F(1, 10 ** 6) - F(1, 10 ** 12)
    c2 = search(laws, un, qs, "x0", "<=", lower)
    if c2 is not None and Z.check(laws, un, qs, "x0", "<=", lower, c2)[0]:
        false_pass += 1
check(found >= 45, f"certificates at the exact corner maximum accepted: {found} of 60")
check(false_pass == 0, f"a bound below the corner maximum never passes: {false_pass} of 60 did")

print("4. a lying kernel (every coefficient read at the centre) — this stand must see it")
boxes, laws, un = ladder(3)
qs = sheet(boxes, un)
vals = corners(boxes, laws, un, 2)
nom = exact_solve(*Z.system(laws, un, qs), qs, {n: (lo + hi) / 2 for n, (lo, hi) in boxes.items()})[2]
real_read = Z._read


def lying_read(node, qs_, piece):
    mid = {n: ((lo + hi) / 2, (lo + hi) / 2) for n, (lo, hi) in piece.items()}
    return real_read(node, qs_, mid)


Z._read = lying_read
try:
    c_lie = search(laws, un, qs, "u2", "<=", nom * (1 + F(1, 10 ** 6)))
    lied = c_lie is not None and Z.check(laws, un, qs, "u2", "<=", nom * (1 + F(1, 10 ** 6)), c_lie)[0]
finally:
    Z._read = real_read
check(lied and max(vals) > nom * (1 + F(1, 10 ** 6)),
      "with readings collapsed to the centre a bound just above the NOMINAL passes, though corners exceed it")
check(c_lie is None or not Z.check(laws, un, qs, "u2", "<=", nom * (1 + F(1, 10 ** 6)), c_lie)[0],
      "the true kernel refuses that certificate")

print("5. a ladder of 12 unknowns, 25 tolerances (beyond Cramer's 6): the exact worst case")
boxes, laws, un = ladder(12)
qs = sheet(boxes, un)
A, b = Z.system(laws, un, qs)
names = sorted(boxes)
bound = exact_solve(A, b, qs, {n: (lo + hi) / 2 for n, (lo, hi) in boxes.items()})[11]
for _ in range(30):                              # descent: a failing corner's value is the next bound
    c = search(laws, un, qs, "u11", "<=", bound, budget=200)
    if c is not None:
        break
    with Z.grid(128):
        # the corner the signs point to, read by the kernel's own sign rule at the centre
        pc = {n: (lo, hi) for n, (lo, hi) in boxes.items()}
        mid = {n: ((lo + hi) / 2, (lo + hi) / 2) for n, (lo, hi) in pc.items()}
        Am = [[float(Z._read(e, qs, mid)[0]) for e in row] for row in A]
        Rm = finv(Am)
        bm = [float(Z._read(e, qs, mid)[0]) for e in b]
        xm = [sum(Rm[i][j] * bm[j] for j in range(12)) for i in range(12)]
        R = [[F(int(round(v * Z.G)), Z.G) for v in row] for row in Rm]
        xt = [F(int(round(v * Z.G)), Z.G) for v in xm]
        d = Z._dread(A, b, names, 11, qs, pc, R, xt, Z._imatrix(A, qs, pc), [Z._read(e, qs, pc) for e in b], 0,
                     Z._param(A, b, qs, pc))
    corner = {n: (boxes[n][1] if not isinstance(d[n], str) and d[n][0] >= 0 else boxes[n][0]) for n in names}
    bound = max(bound, exact_solve(A, b, qs, corner)[11])
check(c is not None and Z.check(laws, un, qs, "u11", "<=", bound, c)[0],
      f"u11 <= {float(bound):.6g} (the corner the signs point to, solved exactly): PROVED with no slack")

if FAILS:
    print(f"ZLIN RED: {len(FAILS)} of {CHECKS[0]} checks fail")
    sys.exit(1)
print(f"ZLIN GREEN ({CHECKS[0]} checks)")
