# -*- coding: utf-8 -*-
"""
Stand for zlp.py: a lower bound on a linear optimum over a box of uncertain coefficients, by weak duality.

The multipliers come from an LP solver OUTSIDE (scipy's HiGHS, floats, rationalised); the kernel trusts none of
it. Checks:
  1. the two-ingredient diet: L = 70/27 exactly, the robust optimum;
  2. 60 seeded random robust LPs (2-6 variables, 2-6 constraints, +-10 % coefficients): the kernel's L is never
     above the objective at the solver's (robustly feasible) optimum, and within 1e-6 of it — sound and tight;
  3. ANY multipliers give a sound bound: 60 random non-negative y, L <= the optimum every time;
  4. FORGERIES refused: a negative multiplier; a point outside its box; one multiplier too few; a product of two
     choices (not affine) in a constraint or in the objective;
  5. MUTATION: a kernel that reads the box at its most favourable end (max, not min) claims L above the
     optimum on the diet — the stand sees it.
  6. FARKAS (2026-10-10): "no mix exists" proved — the diet asking 0.5 protein (at most 0.44 is possible): the
     kernel's box-maximum of sum y*h is below zero; 40 seeded random robust LPs the solver calls infeasible get
     a certificate from the phase-1 LP's multipliers; on every FEASIBLE random LP no multipliers (solver's or
     random) give one; forgeries (all-zero y, a negative y) refused; the reversed-product mutation "proves" a
     feasible diet infeasible — seen.

Run:  python3 test_lp.py   -> LP GREEN
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np                                    # noqa: E402
from scipy.optimize import linprog                    # noqa: E402

import zlp                                            # noqa: E402
from znumjudge import _parse_arith, parse_quantities  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


print("1. the diet")
q = parse_quantities("a=[0,1] credit, b=[0,1] credit, pa=[0.09,0.11] credit, pb=[0.36,0.44] credit")[0]
qn = parse_quantities("a=[0,1] credit, b=[0,1] credit")[0]
obj = _parse_arith("2*a + 3*b", qn)
cons = [(_parse_arith("pa*a + pb*b", q), ">=", F(1, 4)), (_parse_arith("a + b", q), ">=", 1),
        (_parse_arith("a + b", q), "<=", 1)]
xs = {"a": (F(0), F(1)), "b": (F(0), F(1))}
pts = [{"pa": F(9, 100), "pb": F(36, 100)}, None, None]
r = zlp.lower_bound(obj, qn, cons, q, xs, [F(100, 27), F(5, 3), 0], pts)
check("L = 70/27, the robust optimum, exactly", r == (True, F(70, 27)), r)

print("2. random robust LPs")
rnd = random.Random(20261010)
sound = tight = n = 0
for k in range(60):
    nv, nc = rnd.randint(2, 6), rnd.randint(2, 6)
    vs = [f"x{i}" for i in range(nv)]
    cost = [F(rnd.randint(1, 20)) for _ in vs]
    nom = [[F(rnd.randint(1, 30), 10) for _ in vs] for _ in range(nc)]
    rhs = [F(rnd.randint(5, 20), 10) for _ in range(nc)]
    params, qtext = [], []
    for i in range(nc):
        for j in range(nv):
            a = nom[i][j]
            qtext.append(f"c{i}_{j}=[{a * F(9, 10)},{a * F(11, 10)}] credit")
    xt = [f"{v}=[0,3] credit" for v in vs]
    qc = parse_quantities(", ".join(xt + qtext))[0]
    qo = parse_quantities(", ".join(xt))[0]
    objn = _parse_arith(" + ".join(f"{c}*{v}" for c, v in zip(cost, vs)), qo)
    consn = [(_parse_arith(" + ".join(f"c{i}_{j}*{v}" for j, v in enumerate(vs)), qc), ">=", rhs[i]) for i in range(nc)]
    A = [[-float(nom[i][j] * F(9, 10)) for j in range(nv)] for i in range(nc)]
    res = linprog([float(c) for c in cost], A_ub=A, b_ub=[-float(b) for b in rhs], bounds=[(0, 3)] * nv, method="highs")
    if not res.success:
        continue
    n += 1
    ys = [F(-m).limit_denominator(10 ** 9) for m in res.ineqlin.marginals]
    points = [{f"c{i}_{j}": nom[i][j] * F(9, 10) for j in range(nv)} for i in range(nc)]
    good, L = zlp.lower_bound(objn, qo, consn, qc, {v: (F(0), F(3)) for v in vs}, ys, points)
    sound += good and float(L) <= res.fun + 1e-9
    tight += good and float(L) >= res.fun - 1e-6
    # 3. any multipliers: sound
    if k < 60:
        yr = [F(rnd.randint(0, 50), 10) for _ in range(nc)]
        g2, L2 = zlp.lower_bound(objn, qo, consn, qc, {v: (F(0), F(3)) for v in vs}, yr, points)
        sound += 0 if (g2 and float(L2) <= res.fun + 1e-9) else -1000
check(f"{n} solvable LPs: the kernel's L never above the optimum (with the solver's y and with random y)",
      n > 40 and sound == n, (sound, n))
check(f"{n} solvable LPs: L within 1e-6 of the optimum with the solver's multipliers (tight)", tight == n, (tight, n))

print("4. forgeries")
check("a negative multiplier: refused", not zlp.lower_bound(obj, qn, cons, q, xs, [F(-1), F(5, 3), 0], pts)[0])
check("a point outside its box: refused",
      not zlp.lower_bound(obj, qn, cons, q, xs, [F(100, 27), F(5, 3), 0], [{"pa": F(8, 100), "pb": F(36, 100)}, None, None])[0])
check("one multiplier too few: refused", not zlp.lower_bound(obj, qn, cons, q, xs, [F(1), F(1)], pts)[0])
check("a product of two choices in a constraint: refused (not affine)",
      not zlp.lower_bound(obj, qn, cons[:2] + [(_parse_arith("a*b", q), "<=", 1)], q, xs, [F(1), F(1), F(1)])[0])
check("a product in the objective: refused", not zlp.lower_bound(_parse_arith("a*b", qn), qn, cons, q, xs, [0, 0, 0])[0])

print("5. mutation: the box read at its MOST favourable end (max instead of min)")
real_mul = zlp._mul_iv
zlp._mul_iv = lambda u, v: tuple(reversed(real_mul(u, v)))
try:
    g, L = zlp.lower_bound(obj, qn, cons, q, xs, [0, 0, 0], pts)     # y = 0: the honest kernel gives L = 0
finally:
    zlp._mul_iv = real_mul
check("the lying kernel claims L above the robust optimum 70/27 (with y = 0, where the honest L is 0) — the "
      "stand sees it", g and L > F(70, 27) and zlp.lower_bound(obj, qn, cons, q, xs, [0, 0, 0], pts) == (True, 0), L)

print("6. Farkas: no mix exists")
cons_bad = [(_parse_arith("pa*a + pb*b", q), ">=", F(1, 2)), (_parse_arith("a + b", q), ">=", 1),
            (_parse_arith("a + b", q), "<=", 1)]
pts_bad = [{"pa": F(9, 100), "pb": F(36, 100)}, None, None]
r = zlp.infeasible(cons_bad, q, xs, [1, 0, F(36, 100)], pts_bad)
check("protein 0.5 asked, 0.44 at most: infeasible, the box-maximum of sum y*h = -7/50", r == (True, F(-7, 50)), r)
r2 = zlp.infeasible(cons_bad, q, xs, [1, 0, F(36, 100)])
check("without points the coefficients are read over the whole box: here still proved (max 0.44 < 0.5)",
      r2[0], r2)
check("all-zero multipliers: refused", not zlp.infeasible(cons_bad, q, xs, [0, 0, 0], pts_bad)[0])
check("a negative multiplier: refused", not zlp.infeasible(cons_bad, q, xs, [1, -1, 1], pts_bad)[0])
check("the FEASIBLE diet (0.25): the same multipliers prove nothing",
      not zlp.infeasible(cons, q, xs, [1, 0, F(36, 100)], pts)[0])


def phase1(A, b, box):
    """min t: A x - t <= b; the multipliers of the rows (sum 1) are a Farkas certificate when t* > 0."""
    nv = len(A[0])
    res = linprog([0.0] * nv + [1.0], A_ub=[row + [-1.0] for row in A], b_ub=b,
                  bounds=box + [(None, None)], method="highs")
    return res.fun, [F(max(0.0, -m)).limit_denominator(10 ** 9) for m in res.ineqlin.marginals]


rnd = random.Random(1010)
proved = infeasible_n = feas_n = feas_false = 0
for k in range(400):
    nv, nc = rnd.randint(2, 5), rnd.randint(2, 6)
    vs = [f"x{i}" for i in range(nv)]
    nom = [[F(rnd.randint(1, 30), 10) for _ in vs] for _ in range(nc)]
    rhs = [F(rnd.randint(5, 60), 10) for _ in range(nc)]
    ops = [rnd.choice([">=", "<="]) for _ in range(nc)]
    qtext = [f"c{i}_{j}=[{nom[i][j] * F(9, 10)},{nom[i][j] * F(11, 10)}] credit" for i in range(nc) for j in range(nv)]
    xt = [f"{v}=[0,1] credit" for v in vs]
    qc = parse_quantities(", ".join(xt + qtext))[0]
    consn = [(_parse_arith(" + ".join(f"c{i}_{j}*{v}" for j, v in enumerate(vs)), qc), ops[i], rhs[i])
             for i in range(nc)]
    # robust rows (x >= 0): ">=" at the low coefficients, "<=" at the high ones
    end = [F(9, 10) if ops[i] == ">=" else F(11, 10) for i in range(nc)]
    A = [[(-1 if ops[i] == ">=" else 1) * float(nom[i][j] * end[i]) for j in range(nv)] for i in range(nc)]
    bb = [(-1 if ops[i] == ">=" else 1) * float(rhs[i]) for i in range(nc)]
    tstar, ys = phase1(A, bb, [(0, 1)] * nv)
    points = [{f"c{i}_{j}": nom[i][j] * end[i] for j in range(nv)} for i in range(nc)]
    xsr = {v: (F(0), F(1)) for v in vs}
    if tstar > 1e-6 and infeasible_n < 40:
        infeasible_n += 1
        proved += zlp.infeasible(consn, qc, xsr, ys, points)[0]
    elif tstar < -1e-6 and feas_n < 40:
        feas_n += 1
        feas_false += zlp.infeasible(consn, qc, xsr, ys, points)[0] if any(ys) else 0
        yr = [F(rnd.randint(0, 50), 10) for _ in range(nc)]
        feas_false += zlp.infeasible(consn, qc, xsr, yr, points)[0] if any(yr) else 0
check(f"{infeasible_n} random robust LPs the solver calls infeasible: ZTL accepts the phase-1 certificate on all",
      infeasible_n == 40 and proved == 40, (proved, infeasible_n))
check(f"{feas_n} FEASIBLE random LPs: no multipliers (solver's or random) give a certificate",
      feas_n == 40 and feas_false == 0, (feas_false, feas_n))

zlp._mul_iv = lambda u, v: tuple(reversed(real_mul(u, v)))
try:
    gm = zlp.infeasible(cons, q, xs, [1, 0, F(36, 100)], pts)
finally:
    zlp._mul_iv = real_mul
check("mutation (the box read at its favourable end): the lying kernel 'proves' the feasible diet has no mix — "
      "and the honest one refuses the same certificate", gm[0] and not zlp.infeasible(cons, q, xs, [1, 0, F(36, 100)], pts)[0], gm)

print(f"\n{ok} ok, {fail} fail")
print("LP GREEN" if fail == 0 else "LP RED")
sys.exit(1 if fail else 0)
