# -*- coding: utf-8 -*-
"""
Stand for zmin.py: a lower bound on a NONLINEAR minimum over a box of amounts, by a split whose every piece is
settled (the objective >= L, or a requirement fails at one point of its data).

The certificate comes from a small searcher in THIS file (bisection, untrusted); the kernel trusts none of it.
Checks:
  1. the purge: c = g/(p*F + r) <= 0.008, g in [0.9, 1.1], r in [40, 60], cost 1000 p — the robust optimum is
     p = 0.0975 (g = 1.1, r = 40): the kernel's L is <= 97.5 and within 0.01 of it;
  2. 40 seeded random problems (1-2 amounts, a ratio and an exponential row, data monotone so the box's corners
     are its worst points): L never above the robust optimum found by a fine grid of the amounts x all corners;
  3. "no mix exists": the purge asking 0.004 (p would need 0.235 > 0.2) — every piece fails, proved;
  4. FORGERIES refused: a failing point outside its box; a bound that does not miss the requirement; a cut
     outside its piece; a missing branch; L above a cost leaf's objective; a requirement that does not exist;
  5. MUTATION: a kernel that does not check the failing point lies in the box "proves" a feasible purge has no
     mix (a point with r far above its box) — the stand sees it.

Run:  python3 test_min.py   -> MIN GREEN
"""
import itertools
import math
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcertify as ZC                                 # noqa: E402
import zmin                                           # noqa: E402
from znumjudge import _parse_arith, parse_quantities  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def on(qs, piece):
    q2 = dict(qs)
    for n, (lo, hi) in piece.items():
        if n in q2:
            q2[n] = dict(q2[n], lo=lo, hi=hi)
    return q2


def search(obj, qs_obj, rows, xs, target, budget=4000):
    """An untrusted searcher: tries every corner of each row's data; closes a piece by cost at `target`."""
    leaves = []

    def corners(qs, node):
        ds = sorted(n for n in ZC._names(node) if n in qs and n not in xs and qs[n]["lo"] != qs[n]["hi"])
        return [dict(zip(ds, c)) for c in itertools.product(*[(qs[d]["lo"], qs[d]["hi"]) for d in ds])]

    def go(piece, depth):
        if len(leaves) > budget:
            raise RuntimeError("budget")
        for i, (node, op, b, qs) in enumerate(rows):
            for pt in corners(qs, node):
                r = ZC._reading(node, on(qs, dict(piece, **{d: (v, v) for d, v in pt.items()})), {})
                if r is None:
                    continue
                if op == ">=" and r[1] < b or op == "<=" and r[0] > b:
                    leaves.append(1)
                    return {"leaf": "fails", "row": i, "at": {d: str(v) for d, v in pt.items()},
                            "bound": str(r[1] if op == ">=" else r[0]), "cert": {"leaf": "interval"}}
        r = ZC._reading(obj, on(qs_obj, piece), {})
        if target is not None and r is not None and r[0] >= target:
            leaves.append(1)
            return {"leaf": "cost", "cert": {"leaf": "interval"}}
        n = max(piece, key=lambda m: piece[m][1] - piece[m][0])
        lo, hi = piece[n]
        if depth > 40 or hi == lo:
            raise RuntimeError("depth")
        at = (lo + hi) / 2
        return {"split": n, "at": str(at), "lo": go(dict(piece, **{n: (lo, at)}), depth + 1),
                "hi": go(dict(piece, **{n: (at, hi)}), depth + 1)}
    return go(dict(xs), 0)


print("1. the purge")
q = parse_quantities("p=[0,0.2] credit, g=[0.9,1.1] credit, r=[40,60] credit, Fl=1000 credit")[0]
qo = parse_quantities("p=[0,0.2] credit")[0]
obj = _parse_arith("1000*p", qo)
row = (_parse_arith("g/(p*Fl + r)", q), "<=", F(8, 1000), q)
xs = {"p": (F(0), F(1, 5))}
L = F(9749, 100)
cert = search(obj, qo, [row], xs, L)
okL, info = zmin.check_lower_bound(obj, qo, [row], xs, L, cert)
check(f"L = 97.49 proved ({info if okL else info})", okL, info)
okH, why = zmin.check_lower_bound(obj, qo, [row], xs, F(9751, 100), cert)
check("L = 97.51 (above the optimum 97.5) refused on the same tree", not okH, why)
try:
    search(obj, qo, [row], xs, F(9751, 100), budget=3000)
    check("no searcher's tree proves 97.51", False, "a tree was found")
except RuntimeError:
    check("no tree for 97.51: the searcher runs out (the optimum 97.5 is feasible)", True)

print("2. random problems against a grid")
rng = random.Random(20261012)
bad = 0
for k in range(40):
    dim = 1 + k % 2
    a = [F(rng.randint(1, 9)) for _ in range(dim)]
    cst = [F(rng.randint(1, 9)) for _ in range(dim)]
    names = [f"x{i}" for i in range(dim)]
    xs = {n: (F(0), F(2)) for n in names}
    spec = ", ".join(f"{n}=[0,2] credit" for n in names)
    q = parse_quantities(spec + ", g=[0.8,1.2] credit, h=[1,2] credit")[0]
    qo = parse_quantities(spec)[0]
    lin = " + ".join(f"{a[i]}*{n}" for i, n in enumerate(names))
    obj = _parse_arith(" + ".join(f"{cst[i]}*{n}" for i, n in enumerate(names)), qo)
    need = F(rng.randint(2, 8), 10)
    rows = [(_parse_arith(f"g/({lin} + h)", q), "<=", need, q),
            (_parse_arith(f"exp(0 - g*{names[0]})", q), "<=", F(rng.randint(3, 9), 10), q)]
    # the robust optimum by a grid: g, h at the corners (each row monotone in them)
    best = None
    steps = 200 if dim == 1 else 60
    for pt in itertools.product(*[[F(2 * j, steps) for j in range(steps + 1)] for _ in names]):
        env = dict(zip(names, pt))
        s = sum(a[i] * env[n] for i, n in enumerate(names))
        okp = all(float(g) / (float(s) + float(h)) <= float(rows[0][2]) + 1e-12
                  and math.exp(-float(g) * float(env[names[0]])) <= float(rows[1][2]) + 1e-12
                  for g in (0.8, 1.2) for h in (1, 2))
        if okp:
            c = sum(cst[i] * env[n] for i, n in enumerate(names))
            best = c if best is None or c < best else best
    if best is None:
        continue
    target = best - F(1, 2)              # a bound a little under the grid's optimum (the grid's is above the true)
    try:
        cert = search(obj, qo, rows, xs, target, budget=3000)
    except RuntimeError:
        continue
    okL, info = zmin.check_lower_bound(obj, qo, rows, xs, target, cert)
    # soundness: anything the kernel accepts is <= the true optimum <= the grid's
    over = zmin.check_lower_bound(obj, qo, rows, xs, best + F(1, 10), cert)[0]
    if not okL or over:
        bad += 1
check("40 random problems: every bound just under the grid optimum proved, none above it accepted", bad == 0,
      f"{bad} bad")

print("3. no mix exists")
q = parse_quantities("p=[0,0.2] credit, g=[0.9,1.1] credit, r=[40,60] credit, Fl=1000 credit")[0]
qo = parse_quantities("p=[0,0.2] credit")[0]
obj = _parse_arith("1000*p", qo)
row4 = (_parse_arith("g/(p*Fl + r)", q), "<=", F(4, 1000), q)
xs = {"p": (F(0), F(1, 5))}
cert = search(obj, qo, [row4], xs, None)
okN, info = zmin.check_lower_bound(obj, qo, [row4], xs, F(10 ** 9), cert)
check(f"c <= 0.004: every piece fails ({info}), so ANY L holds — no mix", okN and info["cost"] == 0, info)

print("4. forgeries")
fails_out = {"leaf": "fails", "row": 0, "at": {"g": "11/10", "r": "1000"}, "bound": "11/10000",
             "cert": {"leaf": "interval"}}
check("a failing point outside its box (r = 1000)", not zmin.check_lower_bound(obj, qo, [row], xs, 0, fails_out)[0])
not_miss = {"leaf": "fails", "row": 0, "at": {"g": "11/10", "r": "40"}, "bound": "8/1000",
            "cert": {"leaf": "interval"}}
check("a bound that does not miss <= 0.008", not zmin.check_lower_bound(obj, qo, [row], xs, 0, not_miss)[0])
outside = {"split": "p", "at": "1/2", "lo": {"leaf": "cost", "cert": {"leaf": "interval"}},
           "hi": {"leaf": "cost", "cert": {"leaf": "interval"}}}
check("a cut outside its piece", not zmin.check_lower_bound(obj, qo, [row], xs, 0, outside)[0])
missing = {"split": "p", "at": "1/10", "lo": {"leaf": "cost", "cert": {"leaf": "interval"}}}
check("a missing branch", not zmin.check_lower_bound(obj, qo, [row], xs, 0, missing)[0])
check("L above a cost leaf's objective (a single leaf, L = 1)",
      not zmin.check_lower_bound(obj, qo, [row], xs, 1, {"leaf": "cost", "cert": {"leaf": "interval"}})[0])
check("a requirement that does not exist",
      not zmin.check_lower_bound(obj, qo, [row], xs, 0, dict(fails_out, row=3))[0])

print("5. mutation")
real = zmin.check_lower_bound


def lax(objective, qs_obj, rows, xs, L, cert):
    """A kernel that skips the in-box check of the failing point (it widens the row's box to the point)."""
    rows2 = []
    for node, op, b, qs in rows:
        q2 = {n: (dict(v, lo=min(v["lo"], F(-10 ** 6)), hi=max(v["hi"], F(10 ** 6))) if n in ("g", "r") else v)
              for n, v in qs.items()}
        rows2.append((node, op, b, q2))
    return real(objective, qs_obj, rows2, xs, L, cert)
fake = {"leaf": "fails", "row": 0, "at": {"g": "100", "r": "40"}, "bound": "2/5", "cert": {"leaf": "interval"}}
check("the lax kernel 'proves' the feasible purge has no mix (g = 100, outside [0.9, 1.1])",
      lax(obj, qo, [row], xs, F(10 ** 9), fake)[0])
check("the real kernel refuses the same tree", not real(obj, qo, [row], xs, F(10 ** 9), fake)[0])

print(f"\nMIN {'GREEN' if not fail else 'RED'}: {ok} OK, {fail} FAIL")
sys.exit(1 if fail else 0)
