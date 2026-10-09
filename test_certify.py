# -*- coding: utf-8 -*-
"""
Stand for zcertify.py: a bound over a box, proved by a brought certificate, checked
by the kernel exactly and without a budget.

The certificates here come from a SEARCHER written in this file (branch and bound:
try "monotone" by the derivative's reading, else "interval", else split the widest
side in half) — the kind of searcher that lives outside the kernel. The kernel does
not trust it: every accepted certificate is checked against exact fractions at the
corners and at random interior points of the box (a different route than the
kernel's interval and derivative readings).

Checks:
  1. the divider: Vout = V*R2/(R1+R2) <= 3.1 is certified by one monotone leaf, and
     <= 3 is refused (the true maximum 121/40 is above it), naming the corner;
  2. a NON-monotone case that needs splitting: x*(1-x) <= 1/4 on [0,1], certified
     by a split at 1/2; the bare interval leaf is refused;
  3. 400 seeded random expressions (+ - * / sqrt, 1..4 names): the searcher's
     certificate for a bound at the sampled maximum plus a margin is ACCEPTED, and
     every corner and 30 interior points lie on the right side (sound);
  4. MUTATIONS of accepted certificates must be REFUSED: a flipped sign, a subtree
     dropped, a split point moved outside its piece, the bound tightened below the
     sampled maximum (no certificate may pass a false claim), an unknown leaf;
     a flipped sign is accepted only where the derivative reads exactly [0, 0];
  5. MUTATION of the kernel: with every interval reading collapsed to its midpoint,
     check 4's false bounds must slip through — the stand sees a lying kernel.
  6. SYSTEMS: 120 random 2x2/3x3 linear systems with boxed coefficients — the kernel's
     own Cramer solution equals Gauss elimination at every sample point, exactly;
     certificates accepted, false bounds refused; the load power as a circuit; a
     determinant crossing zero, a non-square system, a product of unknowns: refused;
     MUTATION: a determinant with wrong signs is caught.
  (sqrt shapes are sampled in floats; the margin is 1%, far above the rounding.)

Run:  python3 test_certify.py   -> CERTIFY GREEN
"""
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcertify as ZC                               # noqa: E402
from znumjudge import _parse_arith, parse_quantities  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def fs(x):
    return f"{x.numerator}/{x.denominator}"


def setup(expr_text, boxes):
    sheet = ", ".join(f"{n}=[{fs(a)},{fs(b)}] credit" for n, (a, b) in boxes.items())
    qs = parse_quantities(sheet)[0]
    return _parse_arith(expr_text, qs), qs


# ---- the searcher (OUTSIDE the kernel: it may be wrong, the kernel checks) ----
def search(expr, qs, op, bound, depth=14):
    names = sorted(n for n in ZC._names(expr) if n in qs)
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}

    def go(piece, d):
        signs = {}
        for n, (lo, hi) in piece.items():
            if lo == hi:
                continue
            r = ZC._reading(ZC.derivative(expr, n), qs, piece)
            if r is None:
                signs = None; break
            if r[0] >= 0:
                signs[n] = "+"
            elif r[1] <= 0:
                signs[n] = "-"
            else:
                signs = None; break
        if signs is not None:
            leaf = {"leaf": "monotone", "signs": signs}
            if ZC.check(expr, dict(qs, **{n: dict(qs[n], lo=a, hi=b) for n, (a, b) in piece.items()}),
                        op, bound, leaf)[0]:
                return leaf
        leaf = {"leaf": "interval"}
        r = ZC._reading(expr, qs, piece)
        if r is not None and (r[1] <= bound if op == "<=" else r[0] >= bound):
            return leaf
        if d == 0:
            return None
        n = max(piece, key=lambda k: piece[k][1] - piece[k][0])
        lo, hi = piece[n]
        if lo == hi:
            return None
        at = (lo + hi) / 2
        a = go(dict(piece, **{n: (lo, at)}), d - 1)
        if a is None:
            return None
        b = go(dict(piece, **{n: (at, hi)}), d - 1)
        if b is None:
            return None
        return {"split": n, "at": fs(at), "lo": a, "hi": b}

    return go(box, depth)


# 1. the divider
B = {"V": (F(9, 2), F(11, 2)), "R1": (F(9), F(11)), "R2": (F(9), F(11))}
e, qs = setup("V*R2/(R1+R2)", B)
mono = {"leaf": "monotone", "signs": {"V": "+", "R1": "-", "R2": "+"}}
r_ok = ZC.check(e, qs, "<=", F(31, 10), mono)
r_no = ZC.check(e, qs, "<=", F(3), mono)
check("divider: Vout <= 3.1 by one monotone leaf; <= 3 refused at the corner 121/40",
      r_ok == (True, 1) and not r_no[0] and "121/40" in r_no[1], str((r_ok, r_no)))
r_s = ZC.check(e, qs, "<=", F(31, 10), {"leaf": "monotone", "signs": {"V": "+", "R1": "+", "R2": "+"}})
check("divider: a wrong sign (R1 +) is refused by the kernel's own derivative", not r_s[0] and "d/dR1" in r_s[1], str(r_s))

# 2. non-monotone: a split is needed
e2, qs2 = setup("x*(1 - x)", {"x": (F(0), F(1))})
cert2 = {"split": "x", "at": "1/2", "lo": {"leaf": "monotone", "signs": {"x": "+"}},
         "hi": {"leaf": "monotone", "signs": {"x": "-"}}}
check("x*(1-x) <= 1/4 on [0,1]: certified by a split at 1/2 (two pieces)",
      ZC.check(e2, qs2, "<=", F(1, 4), cert2) == (True, 2), str(ZC.check(e2, qs2, "<=", F(1, 4), cert2)))
check("x*(1-x) <= 1/4: the bare interval leaf is refused (reading [-1, 1])",
      not ZC.check(e2, qs2, "<=", F(1, 4), {"leaf": "interval"})[0])
check("x*(1-x) <= 1/5 is refused under the same certificate (the corner 1/2 gives 1/4)",
      not ZC.check(e2, qs2, "<=", F(1, 5), cert2)[0])


# 3. random expressions
SHAPES = ["{a}*{b} - {c}", "{a}/({b} + {c})", "{a}*{a} - {b}*{c}", "({a} - {b})*({b} - {c})",
          "sqrt({a}) + {b}*{c}", "{a}*{b}/{c} - {a}", "1/{a} + 1/{b} - {c}*{a}",
          "({a} + {b})*({a} - {c})*{b}"]


def random_case(rng):
    k = rng.randint(1, 4)
    names = [f"p{i}" for i in range(k)]
    boxes = {}
    for n in names:
        a = F(rng.randint(1, 30), rng.randint(1, 4))        # positive boxes: / and sqrt defined
        boxes[n] = (a, a + F(rng.randint(1, 20), rng.randint(1, 4)))
    text = rng.choice(SHAPES).format(a=rng.choice(names), b=rng.choice(names), c=rng.choice(names))
    return names, boxes, text


def value(text, at):
    def sqrt(x):
        return x ** 0.5          # float only for the sample check of sqrt shapes
    return eval(text, {"sqrt": sqrt}, dict(at))


def samples(names, boxes, rng, n=30):
    pts = [dict(zip(names, c)) for c in itertools.product(*[boxes[m] for m in names])]
    pts += [{m: a + (b - a) * F(rng.randint(0, 1000), 1000) for m, (a, b) in boxes.items()} for _ in range(n)]
    return pts


def run_random(n=400, seed=17):
    rng = random.Random(seed)
    found = []          # (expr, qs, op, bound, cert, false_bound)
    bad = []
    for i in range(n):
        names, boxes, text = random_case(rng)
        e, qs = setup(text, boxes)
        pts = samples(names, boxes, rng)
        vals = [value(text, p) for p in pts]
        op = rng.choice(["<=", ">="])
        top = max(vals) if op == "<=" else min(vals)
        margin = F(1, 100) * (1 + abs(F(top)))
        bound = F(top) + margin if op == "<=" else F(top) - margin
        bound = F(round(bound * 1000), 1000) + (F(1, 1000) if op == "<=" else -F(1, 1000))
        cert = search(e, qs, op, bound)
        if cert is None:
            continue                                 # the searcher found nothing: nothing brought
        res = ZC.check(e, qs, op, bound, cert)
        if not res[0]:
            bad.append((i, text, "own searcher's certificate refused", res[1])); continue
        if any((v > bound if op == "<=" else v < bound) for v in vals):
            bad.append((i, text, "ACCEPTED A FALSE BOUND")); continue
        false_bound = F(top) - margin if op == "<=" else F(top) + margin
        found.append((text, e, qs, op, bound, cert, false_bound))
    return found, bad


found, bad = run_random()
check(f"400 random expressions: {len(found)} certificates found and accepted, every corner and "
      f"interior sample on the right side (sound)", not bad and len(found) >= 300, str(bad[:2]))


# 4. mutations of accepted certificates
def leaves(cert, path=()):
    if "split" in cert:
        yield from leaves(cert["lo"], path + ("lo",))
        yield from leaves(cert["hi"], path + ("hi",))
    else:
        yield path, cert


def at_path(cert, path):
    for p in path:
        cert = cert[p]
    return cert


def mutated(cert, rng):
    import copy
    out = []
    c = copy.deepcopy(cert)                          # a flipped sign on a monotone leaf
    mons = [(p, l) for p, l in leaves(c) if l.get("leaf") == "monotone" and l["signs"]]
    if mons:
        p, l = rng.choice(mons)
        n = rng.choice(sorted(l["signs"]))
        l["signs"][n] = "-" if l["signs"][n] == "+" else "+"
        out.append(("flipped sign", c))
    if "split" in cert:                              # a subtree dropped / the point outside
        c = copy.deepcopy(cert); c["hi"] = None
        out.append(("subtree dropped", c))
        c = copy.deepcopy(cert); c["at"] = "1000000"
        out.append(("split point outside", c))
    c = copy.deepcopy(cert)
    p, l = next(leaves(c)); l.clear(); l["leaf"] = "trust me"
    out.append(("unknown leaf", c))
    return out


def run_mutations(found, seed=23):
    rng = random.Random(seed)
    slipped, tried, false_slipped, false_tried = [], 0, [], 0
    for text, e, qs, op, bound, cert, false_bound in found:
        for name, c in mutated(cert, rng):
            if name == "flipped sign":
                continue                     # judged on its own below, piece by piece
            res = ZC.check(e, qs, op, bound, c)
            tried += 1
            if res[0]:
                slipped.append((text, name))
        false_tried += 1
        if ZC.check(e, qs, op, false_bound, cert)[0]:
            false_slipped.append(text)
    return slipped, tried, false_slipped, false_tried


slipped, tried, false_slipped, false_tried = run_mutations(found)
check(f"{tried} structural mutations: none accepted", not slipped, str(slipped[:3]))
check(f"{false_tried} FALSE bounds (below the sampled maximum) under the accepted certificates: none accepted",
      not false_slipped, str(false_slipped[:3]))
# a flipped sign may be accepted only where both signs are true: the derivative's reading
# on that piece is exactly [0, 0] (e.g. (p1 - p1)*p0) — checked on the piece itself
def piece_of(qs, names, cert, path):
    piece = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    node = cert
    for p in path:
        n, at = node["split"], F(node["at"])
        lo, hi = piece[n]
        piece[n] = (lo, at) if p == "lo" else (at, hi)
        node = node[p]
    return piece


import copy  # noqa: E402
flip_bad, flip_ok, flip_tried = [], 0, 0
for t, e, qs, op, b, c, _ in found:
    names = sorted(n for n in ZC._names(e) if n in qs)
    for path, leaf in leaves(c):
        if leaf.get("leaf") != "monotone":
            continue
        for n in sorted(leaf["signs"]):
            m = copy.deepcopy(c)
            lf = at_path(m, path)
            lf["signs"][n] = "-" if lf["signs"][n] == "+" else "+"
            flip_tried += 1
            if ZC.check(e, qs, op, b, m)[0]:
                r = ZC._reading(ZC.derivative(e, n), qs, piece_of(qs, names, c, path))
                if r == (0, 0):
                    flip_ok += 1
                else:
                    flip_bad.append((t, n, r))
check(f"{flip_tried} flipped signs: accepted only where the derivative reads exactly [0, 0] "
      f"({flip_ok} such, e.g. (p1 - p1)*p0; 0 others)", not flip_bad, str(flip_bad[:3]))

# 5. kernel mutation: a derivative reading collapsed to a point must let false claims through
real = ZC._reading


def shrunk(e, qs, piece):
    r = real(e, qs, piece)
    if r is None:
        return r
    mid = (r[0] + r[1]) / 2
    return (mid, mid)                                   # every reading collapsed to its midpoint


ZC._reading = shrunk
caught = 0
for text, e, qs, op, bound, cert, false_bound in found[:120]:
    if ZC.check(e, qs, op, false_bound, {"leaf": "interval"})[0]:
        caught += 1
ZC._reading = real
check(f"MUTATION: with every reading collapsed to its midpoint, the false bounds pass ({caught} of 120) — "
      f"the stand sees a lying kernel", caught > 0, "mutation survived")


# 6. A QUANTITY SOLVED FROM A SYSTEM: the kernel solves it itself (Cramer), then checks
print("6. systems: the kernel's own solution")


def gauss(rows, unknowns, env):
    """Exact solution at one point — a different route than the kernel's Cramer."""
    A = [[r[u](env) for u in unknowns] + [r[1](env)] for r in rows]
    n = len(unknowns)
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c] / A[c][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return {u: A[i][-1] / A[i][i] for i, u in enumerate(unknowns)}


def random_system(rng):
    n = rng.randint(2, 3)
    unk = [f"u{i}" for i in range(n)]
    names = [f"p{i}" for i in range(rng.randint(1, 3))]
    boxes = {}
    for m in names:
        a = F(rng.randint(2, 20), rng.randint(1, 3))
        boxes[m] = (a, a + F(rng.randint(1, 6), rng.randint(2, 4)))
    laws, rows = [], []
    for i in range(n):          # diagonally dominant: positive boxes on the diagonal, small off it
        terms, coef = [], {}
        for j, u in enumerate(unk):
            if i == j:
                m = rng.choice(names); k = rng.randint(n + 2, n + 6)
                terms.append(f"({k} + {m})*{u}")
                coef[u] = (lambda k, m: lambda env: k + env[m])(k, m)
            elif rng.random() < 0.7:
                c = F(rng.choice([-1, 1]), rng.randint(2, 4))
                terms.append(f"({fs(c)})*{u}")
                coef[u] = (lambda c: lambda env: c)(c)
            else:
                coef[u] = lambda env: F(0)
        m = rng.choice(names); k = rng.randint(1, 5)
        laws.append(" + ".join(terms) + f" == {k}*{m}")
        coef[1] = (lambda k, m: lambda env: k * env[m])(k, m)
        rows.append(coef)
    target = rng.choice(["{a}*{b}", "{a} - {b}*{p}", "{a}*{a} + {p}", "{a}/{p} - {b}"]).format(
        a=rng.choice(unk), b=rng.choice(unk), p=rng.choice(names))
    return unk, names, boxes, laws, rows, target


def sheet_of(boxes, unk):
    return ", ".join(f"{m}=[{fs(a)},{fs(b)}] credit" for m, (a, b) in boxes.items()) + \
        ", " + ", ".join(f"{u}=? credit" for u in unk)


def run_systems(n=120, seed=31):
    rng = random.Random(seed)
    bad, found, mism = [], [], []
    for i in range(n):
        unk, names, boxes, laws, rows, target = random_system(rng)
        qs = parse_quantities(sheet_of(boxes, unk))[0]
        sol = ZC.solve_system(laws, unk, qs)
        e = ZC._subst(_parse_arith(target, qs), sol)
        pts = samples(names, boxes, rng, n=15)
        vals = []
        for p in pts:
            g = gauss(rows, unk, p)
            exact = eval(target, {}, dict(p, **g))
            k = ZC._reading(e, qs, {m: (p[m], p[m]) for m in names})
            if k is None or k != (exact, exact):
                mism.append((i, target, p)); break
            vals.append(exact)
        else:
            top = max(vals)
            bound = top + (abs(top) + 1) / 50
            cert = search(e, qs, "<=", bound)
            if cert is None:
                continue
            res = ZC.check_system(target, laws, unk, qs, "<=", bound, cert)
            if not res[0]:
                bad.append((i, "refused its own", res[1])); continue
            false = ZC.check_system(target, laws, unk, qs, "<=", top - (abs(top) + 1) / 50, cert)
            if false[0]:
                bad.append((i, "ACCEPTED A FALSE BOUND")); continue
            found.append(i)
    return bad, found, mism


bad, found, mism = run_systems()
check(f"120 random 2x2/3x3 systems: the kernel's solved expression equals Gauss elimination at every sample "
      f"point (exact); {len(found)} certificates accepted, false bounds refused", not bad and not mism and len(found) >= 90,
      str((bad[:2], mism[:2], len(found))))

qs9 = parse_quantities("V=5 credit, RL=[1,100] credit, Rs=[1089/100,1111/100] credit, I=? credit, VL=? credit")[0]
laws9 = ["V - VL == I*Rs", "VL == I*RL"]
e9 = ZC._subst(_parse_arith("VL*I", qs9), ZC.solve_system(laws9, ["I", "VL"], qs9))
c9 = search(e9, qs9, "<=", F(3, 5))
check("load power as a circuit (P = VL*I from the loop) <= 0.6 W: accepted; <= 0.57 refused (the peak is 0.5739)",
      ZC.check_system("VL*I", laws9, ["I", "VL"], qs9, "<=", F(3, 5), c9)[0]
      and not ZC.check_system("VL*I", laws9, ["I", "VL"], qs9, "<=", F(57, 100), c9)[0])
qs_s = parse_quantities("a=[1,3] credit, b=[1,3] credit, x=? credit, y=? credit")[0]
r_s = ZC.check_system("x", ["a*x + y == 1", "x + (1/b)*y == 2"], ["x", "y"], qs_s, "<=", F(100), {"leaf": "interval"})
check("a determinant that crosses zero on the box (a - b): refused, no value claimed", not r_s[0], str(r_s))
check("not square (two equalities, three unknowns): refused aloud",
      "not a square system" in ZC.check_system("x", ["x + y == 1", "y + z == 2"], ["x", "y", "z"],
                                               parse_quantities("x=? credit, y=? credit, z=? credit")[0],
                                               "<=", F(1), {"leaf": "interval"})[1])
check("a product of two unknowns in a law: refused aloud (not a linear system)",
      "not a linear system" in ZC.check_system("x", ["x*y == 1", "y == 2"], ["x", "y"],
                                               parse_quantities("x=? credit, y=? credit")[0],
                                               "<=", F(1), {"leaf": "interval"})[1])
real_det = ZC._det


def bad_det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    out = ZC.ZERO
    for j in range(n):
        term = ZC._mul(M[0][j], bad_det([row[:j] + row[j + 1:] for row in M[1:]]))
        out = ZC._add(out, term)          # every sign +: a wrong determinant
    return out


ZC._det = bad_det
_, _, mism_m = run_systems(n=30, seed=37)
ZC._det = real_det
check("MUTATION: a determinant with every cofactor sign + is caught by the Gauss comparison", len(mism_m) > 0)

print(f"certify: {ok} ok, {fail} failed")
print("CERTIFY GREEN" if fail == 0 else "CERTIFY RED")
