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


# 7. IMPLICIT QUANTITIES (third tranche, 2026-10-11): U a root of g(U, x) = 0, moving with the box
def setup_i(expr_text, g_texts, boxes, uboxes):
    allb = dict(boxes, **uboxes)
    sheet = ", ".join(f"{n}=[{fs(a)},{fs(b)}] credit" for n, (a, b) in allb.items())
    qs = parse_quantities(sheet)[0]
    return _parse_arith(expr_text, qs), {u: _parse_arith(t, qs) for u, t in g_texts.items()}, qs


def bracket_i(g, u, qs, piece, steps=40):
    """The test's own bisection (outside the kernel): [a, b] with g(a) <= 0 <= g(b) over the piece
    (g increasing in u assumed by the test's families; the kernel checks)."""
    lo0, hi0 = qs[u]["lo"], qs[u]["hi"]

    def side(v):
        r = ZC._reading(g, qs, dict(piece, **{u: (v, v)}))
        return 0 if r is None else (-1 if r[1] <= 0 else (1 if r[0] >= 0 else 0))
    lo, hi = lo0, hi0
    for _ in range(steps):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if side(m) == -1 else (lo, m)
    a = lo
    lo, hi = a, hi0
    for _ in range(steps):
        m = (lo + hi) / 2
        lo, hi = (lo, m) if side(m) == 1 else (m, hi)
    return a, hi


def search_i(expr, gs, qs, op, bound, depth=10):
    names = sorted(n for n in set(ZC._names(expr)).union(*[ZC._names(g) for g in gs.values()])
                   if n in qs and n not in gs)
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}

    def go(piece, d):
        br = {u: bracket_i(g, u, qs, piece, 16) for u, g in gs.items()}
        rp = dict(piece, **br)
        roots = {u: [fs(a), fs(b)] for u, (a, b) in br.items()}
        signs = {}
        for n, (lo, hi) in piece.items():
            if lo == hi:
                continue
            r = ZC._reading(ZC._total_derivative(expr, n, gs), qs, rp)
            if r is None or r[0] < 0 < r[1]:
                signs = None; break
            signs[n] = "+" if r[0] >= 0 else "-"
        if signs is not None:
            corner = {n: ((piece[n][1] if (signs.get(n) == "+") == (op == "<=") else piece[n][0]),) * 2
                      for n in piece}
            cr = {u: [fs(a), fs(b)] for u, (a, b) in
                  ((u, bracket_i(g, u, qs, corner)) for u, g in gs.items())}
            leaf = {"leaf": "monotone", "signs": signs, "roots": roots, "corner_roots": cr}
            sub = dict(qs, **{n: dict(qs[n], lo=a, hi=b) for n, (a, b) in piece.items()})
            if ZC.check(expr, sub, op, bound, leaf, implicit=gs)[0]:
                return leaf
        r = ZC._reading(expr, qs, rp)
        if r is not None and (r[1] <= bound if op == "<=" else r[0] >= bound):
            return {"leaf": "interval", "roots": roots}
        if d == 0:
            return None
        n = max(piece, key=lambda k: piece[k][1] - piece[k][0])
        lo, hi = piece[n]
        at = (lo + hi) / 2
        a = go(dict(piece, **{n: (lo, at)}), d - 1)
        b = go(dict(piece, **{n: (at, hi)}), d - 1) if a is not None else None
        return None if b is None else {"split": n, "at": fs(at), "lo": a, "hi": b}

    return go(box, depth)


def root_f(gf, lo, hi):
    for _ in range(80):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if gf(m) < 0 else (lo, m)
    return (lo + hi) / 2


# 7a. the anode of blind test 4 (c02): Es = Ea - I*R, I*R + beta*log10(I/Ip) = Ea - Vp
CB = {"Ea": (F(3, 2), F(8, 5)), "beta": (F(12, 100), F(18, 100)), "Ip": (F(12, 1000), F(60, 1000))}
ec, gc, qc = setup_i("Ea - I*(1069/1000)", {"I": "I*(1069/1000) - (Ea - 85/100 - beta*log10(I/Ip))"},
                     CB, {"I": (F(1, 100), F(1))})
ct = search_i(ec, gc, qc, "<=", F(118, 100))
rc = ZC.check(ec, qc, "<=", F(118, 100), ct, implicit=gc) if ct else (False, "no certificate")
check("implicit (c02): Es <= 1.18 with the current a root that moves with Ea, beta, Ip — certified", rc[0], str(rc))
fals = search_i(ec, gc, qc, "<=", F(113, 100))
check("implicit (c02): Es <= 1.13 (true max 1.1313 at Ea=1.6, beta=0.18, Ip=0.012) — no certificate passes",
      fals is None or not ZC.check(ec, qc, "<=", F(113, 100), fals, implicit=gc)[0])
free = search(ec, qc, "<=", F(118, 100))
check("implicit (c02): the SAME bound with I as a free box is not certified (the correlation J6 lost)",
      free is None or not ZC.check(ec, qc, "<=", F(118, 100), free)[0])

# 7b. mutations of an accepted implicit certificate
def leaves(t):
    return [t] if "leaf" in t else leaves(t["lo"]) + leaves(t["hi"])


def mutated(t, f):
    import copy
    t = copy.deepcopy(t)
    f(leaves(t))
    return t


def shift_roots(ls):
    for lf in ls:
        if "roots" in lf:
            a, b = (F(x) for x in lf["roots"]["I"])
            lf["roots"]["I"] = [fs(b + (b - a) + F(1, 10 ** 6)), fs(b + 2 * (b - a) + F(1, 10 ** 5))]
            return


def drop_corner(ls):
    for lf in ls:
        if lf["leaf"] == "monotone":
            lf.pop("corner_roots"); return


def flip(ls):
    for lf in ls:
        if lf["leaf"] == "monotone":
            n = sorted(lf["signs"])[0]
            lf["signs"][n] = "-" if lf["signs"][n] == "+" else "+"; return


def out_of_range(ls):
    for lf in ls:
        if "roots" in lf:
            lf["roots"]["I"] = ["0", lf["roots"]["I"][1]]; return


for name, f in (("a bracket moved off the root", shift_roots), ("a monotone leaf without its corner bracket",
                drop_corner), ("a flipped total-derivative sign", flip), ("a bracket outside U's range", out_of_range)):
    if ct and any(lf["leaf"] == "monotone" for lf in leaves(ct)) or name in ("a bracket moved off the root",
                                                                            "a bracket outside U's range"):
        r = ZC.check(ec, qc, "<=", F(118, 100), mutated(ct, f), implicit=gc)
        check(f"implicit MUTATION refused: {name}", not r[0], str(r))
# two roots in the range: dg/dU crosses zero -> no bracket claims uniqueness
e2i, g2i, q2i = setup_i("U + x", {"U": "U*U - x"}, {"x": (F(1), F(2))}, {"U": (F(-2), F(2))})
r2 = ZC.check(e2i, g2i and e2i, q2i, "<=", F(3), {"leaf": "interval", "roots": {"U": ["1", "2"]}}, implicit=g2i) \
    if False else ZC.check(e2i, q2i, "<=", F(3), {"leaf": "interval", "roots": {"U": ["1", "2"]}}, implicit=g2i)
check("implicit: two roots in U's range (U = ±sqrt(x)) — a bracket around one is refused (dg/dU crosses 0)",
      not r2[0] and "strict sign" in r2[1], str(r2))
r2b = ZC.check(e2i, q2i, "<=", F(4), {"leaf": "interval"}, implicit=g2i)
check("implicit: with NO bracket U is read over its whole range — sound for every root (U + x <= 4 holds)", r2b[0], str(r2b))
r2c = ZC.check(e2i, q2i, "<=", F(3), {"leaf": "interval"}, implicit=g2i)
check("implicit: ... and U + x <= 3 refused (U = sqrt(2) at x = 2 gives 3.41)", not r2c[0], str(r2c))

# 7c. random implicit cases: certified bounds hold at corners and random interior points (true roots in floats)
import math
FAM = [("U*{k} + {c}*exp(U) - ({a}*x + y)", lambda U, x, y, k, c, a: U * k + c * math.exp(U) - (a * x + y)),
       ("U*U*U + {k}*U - ({a}*x - y)", lambda U, x, y, k, c, a: U ** 3 + k * U - (a * x - y)),
       ("U*{k} + {c}*ln(U + 3) - x*y", lambda U, x, y, k, c, a: U * k + c * math.log(U + 3) - x * y)]
EXPRS = [("x - U*{c}", lambda U, x, y, c: x - U * c), ("U*x + y", lambda U, x, y, c: U * x + y),
         ("x*y - U*U", lambda U, x, y, c: x * y - U * U), ("y/(U + 3) + x", lambda U, x, y, c: y / (U + 3) + x)]
rng = random.Random(41)
acc = sound_bad = refused_false = tried_false = 0
for i in range(60):
    gt, gf = FAM[i % 3]
    et, ef = EXPRS[(i // 3) % 4]
    k, c, a = F(rng.randint(5, 30), 10), F(rng.randint(1, 10), 10), F(rng.randint(5, 20), 10)
    bx = {"x": (F(rng.randint(1, 5), 10), F(rng.randint(6, 12), 10)), "y": (F(rng.randint(1, 5), 10), F(rng.randint(6, 12), 10))}
    gtext = gt.format(k=fs(k), c=fs(c), a=fs(a))
    gfun = lambda U, x, y: gf(U, x, y, float(k), float(c), float(a))
    efun = lambda U, x, y: ef(U, x, y, float(c))
    e7, g7, q7 = setup_i(et.format(c=fs(c)), {"U": gtext}, bx, {"U": (F(-2), F(2))})
    pts = [(x, y) for x in bx["x"] for y in bx["y"]] + \
        [(float(bx["x"][0]) + rng.random() * float(bx["x"][1] - bx["x"][0]),
          float(bx["y"][0]) + rng.random() * float(bx["y"][1] - bx["y"][0])) for _ in range(40)]
    vals = []
    for x, y in pts:
        x, y = float(x), float(y)
        if gfun(-2, x, y) >= 0 or gfun(2, x, y) <= 0:
            vals = None; break
        vals.append(efun(root_f(lambda u: gfun(u, x, y), -2.0, 2.0), x, y))
    if vals is None:
        continue
    top = max(vals)
    bound = F(top + 0.02 * (abs(top) + 1)).limit_denominator(10 ** 6)
    cert = search_i(e7, g7, q7, "<=", bound, depth=6)
    if cert and ZC.check(e7, q7, "<=", bound, cert, implicit=g7)[0]:
        acc += 1
        if any(v > float(bound) + 1e-9 for v in vals):
            sound_bad += 1
    low = F(top - 0.02 * (abs(top) + 1)).limit_denominator(10 ** 6)
    tried_false += 1
    cf = search_i(e7, g7, q7, "<=", low, depth=6)
    if cf is None or not ZC.check(e7, q7, "<=", low, cf, implicit=g7)[0]:
        refused_false += 1
check(f"implicit random: {acc} certified bounds, every sampled true value below them", acc >= 30 and sound_bad == 0,
      f"accepted {acc}, violated {sound_bad}")
check(f"implicit random: {refused_false}/{tried_false} bounds BELOW a sampled true value refused",
      refused_false == tried_false and tried_false > 30)

# 7d. MUTATION of the kernel: the total derivative replaced by the partial one (dU/dx forgotten)
eM, gM, qM = setup_i("x - U", {"U": "U - 2*x"}, {"x": (F(1), F(2))}, {"U": (F(0), F(5))})   # U = 2x: x - U = -x
lyingcert = {"leaf": "monotone", "signs": {"x": "+"}, "roots": {"U": ["2", "4"]}, "corner_roots": {"U": ["4", "4"]}}
honest = ZC.check(eM, qM, "<=", F(-2), lyingcert, implicit=gM)
real_td = ZC._total_derivative
ZC._total_derivative = lambda e, n, imp: ZC.derivative(e, n)
lying = ZC.check(eM, qM, "<=", F(-2), lyingcert, implicit=gM)
ZC._total_derivative = real_td
check("MUTATION: x - U <= -2 with U = 2x (true max -1 at x = 1) — refused by the kernel; passes once dU/dx is "
      "forgotten (the stand sees a lying kernel)", not honest[0] and lying[0], str((honest, lying)))


# 8. CASES (2026-10-11): min / max / ifpos read one choice at a time, each choice's condition kept (weak duality),
#    shared affine symbols — the universal stand's blind test 5, c09 (a coverage margin exactly 0 over regions)
print("\n8. cases: branches read by choice")
qc = parse_quantities("B=[1795,1796] credit, I=[1000,3000] credit, u=[1/2,1] credit, cap=[400,400] credit")[0]
ec = _parse_arith("B + min(cap, max(0, I/u - B)) - I/u + max(0, I/u - B - cap)", qc)     # = max(B - I/u, 0) >= 0
p_dec = {"I": (F(1800), F(1900)), "u": (F(9, 10), F(1))}             # all branches decided: exactly 0
p_str = {"I": (F(1790), F(1800)), "u": (F(99, 100), F(1))}           # the switch I/u = B inside the piece
r_dec, r_str = ZC._reading(ec, qc, p_dec), ZC._reading(ec, qc, p_str)
ZC.CASES = False
o_dec, o_str = ZC._reading(ec, qc, p_dec), ZC._reading(ec, qc, p_str)
ZC.CASES = True
check("coverage B + F + S - N: [0, 0] where every branch is decided (plain + affine: +-312), lower end exactly 0 "
      "where the switch crosses the piece (plain: -23)", r_dec == (0, 0) and r_str[0] == 0 and o_dec[0] < 0 and o_str[0] < 0,
      str((r_dec, r_str, o_dec, o_str)))
import itertools as _it
rng8 = random.Random(31)


def _gen8(d):
    if d == 0 or rng8.random() < 0.2:
        return rng8.choice(["x", "y", "z", str(rng8.randint(1, 4))])
    k = rng8.random(); a, b = _gen8(d - 1), _gen8(d - 1)
    if k < 0.2: return f"min({a}, {b})"
    if k < 0.4: return f"max({a}, {b})"
    if k < 0.5: return f"ifpos({_gen8(d - 1)}, {a}, {b})"
    if k < 0.65: return f"({a} + {b})"
    if k < 0.8: return f"({a} - {b})"
    if k < 0.9: return f"({a}*{b})"
    return f"({a}/(1 + {b}*{b}))"


unsound = tested8 = tighter8 = 0
for _ in range(600):
    txt = _gen8(5)
    box = {}
    for v in "xyz":
        a, b = sorted([F(rng8.randint(-20, 20), rng8.randint(1, 3)), F(rng8.randint(-20, 20), rng8.randint(1, 3))])
        box[v] = (a, b if b > a else a + 1)
    q8 = parse_quantities(", ".join(f"{v}=[{fs(a)},{fs(b)}] credit" for v, (a, b) in box.items()))[0]
    try:
        e8 = _parse_arith(txt, q8)
    except Exception:
        continue
    ZC.CASES = False; r0 = ZC._reading(e8, q8, box)
    ZC.CASES = True; r1 = ZC._reading(e8, q8, box)
    if r0 is None or r1 is None:
        continue
    tested8 += 1; tighter8 += (r1[1] - r1[0]) < (r0[1] - r0[0])
    pts = [dict(zip("xyz", c)) for c in _it.product(*[box[v] for v in "xyz"])]
    pts += [{v: box[v][0] + (box[v][1] - box[v][0]) * F(rng8.randint(0, 64), 64) for v in "xyz"} for _ in range(20)]
    ZC.CASES = False
    for pt in pts:
        val = ZC._reading(e8, q8, {v: (x, x) for v, x in pt.items()})
        if val is not None and not (r1[0] <= val[0] and val[1] <= r1[1]):
            unsound += 1; break
    ZC.CASES = True
check(f"cases, random: {tested8} expressions with min/max/ifpos/products/quotients — every corner and 20 inner "
      f"points inside the case reading ({tighter8} tighter than the plain one)", unsound == 0 and tested8 > 300 and tighter8 > 30,
      f"unsound {unsound}")
# MUTATION: a kernel that drops a case's condition (no weak duality) must lose the zero margin across the switch
_real_dual = ZC._dual_low
ZC._dual_low = lambda f, gs: (_real_dual(f, [])[0], False)
r_mut = ZC._reading(ec, qc, p_str)
ZC._dual_low = _real_dual
check("MUTATION: with each case's condition dropped the switching piece reads below 0 — the conditions carry it",
      r_mut[0] < 0, str(r_mut))

print(f"certify: {ok} ok, {fail} failed")
print("CERTIFY GREEN" if fail == 0 else "CERTIFY RED")
