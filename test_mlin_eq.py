# -*- coding: utf-8 -*-
"""
Stand for `_mlin_eq` (znumsolve.py): a name defined by a MULTILINEAR expression of
boxed quantities is narrowed to that expression's exact range over the boxes.

Why (2026-10-09, the universal stand's probe tasks, gap Z2): tau == R*C,
Tj == Ta + P*(Rjc + Rcs + Rsa), V == N*(Vcell - I*r) stayed at (-inf, inf).

Expected ranges are computed by a DIFFERENT route than the solver's: the
expression is evaluated as Python on exact fractions at every corner of the box
(the solver reads it through `_mlin` terms), and random INTERIOR points are
checked to lie inside — so agreement is not the solver agreeing with itself.

Checks:
  1. the three probe shapes: exact ranges, the log names the step;
  2. 300 seeded random multilinear expressions (2..5 names, sums of products,
     signed coefficients, shared names): the narrowed range equals the corner
     hull exactly, and 30 interior points each lie inside it;
  3. OUTSIDE the class — a name squared (x == R*R), a division by a box
     (x == 1/R): NOT narrowed by this step (still unbounded), no false claim;
  4. a defined name with its own box narrower than the expression's range keeps
     the intersection; disjoint boxes empty the name (REFUTED, not a wrong value);
  5. MUTATION: with `_ev_mlin` shrinking its range by 1%, check 2 must FAIL;
  6. `_iv_eq` (gap Z1): a name defined by a NON-multilinear expression (a name
     squared, a division by a box) is narrowed by the interval reading — SOUND:
     200 seeded random expressions, every corner and 30 interior points inside
     the narrowed range; logged as an interval reading, never as exact;
     the power of a divider (P1 == I*I*R1 after the system bounds I) is bounded;
  7. MUTATION: with `_ev` shrinking its range by 1%, check 6 must FAIL.

Run:  python3 test_mlin_eq.py   -> MLIN EQ GREEN
"""
import itertools
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import znumsolve                                   # noqa: E402
from znumjudge import parse_quantities            # noqa: E402
from znumsolve import solve_claim                 # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def narrowed(claim, sheet, name):
    r = solve_claim(claim, *parse_quantities(sheet))
    q = r["narrowed"][name]
    return q["lo"], q["hi"], r["log"], q


def fs(x):
    return f"{x.numerator}/{x.denominator}"


# 1. the three probe shapes
lo, hi, log, _ = narrowed("(tau == R*C)", "R=[99/10,101/10] credit, C=[19/2,21/2] credit, tau=? credit", "tau")
check("tau == R*C: [94.05, 106.05] exactly, by the multilinear step",
      (lo, hi) == (F(1881, 20), F(2121, 20)) and any("multilinear, exact at the corners" in l for l in log), str((lo, hi, log)))
lo, hi, log, _ = narrowed("(Tj == Ta + P*(Rjc + Rcs + Rsa))",
                          "Ta=[20,45] credit, P=[18,22] credit, Rjc=[2/5,3/5] credit, Rcs=[2/5,3/5] credit, "
                          "Rsa=[9/5,11/5] credit, Tj=? credit", "Tj")
check("Tj == Ta + P*(Rjc + Rcs + Rsa): [66.8, 119.8] exactly", (lo, hi) == (F(334, 5), F(599, 5)), str((lo, hi)))
lo, hi, log, _ = narrowed("(V == N*(Vc - I*r))",
                          "N=7 earned:design, Vc=[16/5,21/5] credit, I=[1/2,5] credit, r=[7/200,13/200] credit, V=? credit", "V")
check("V == N*(Vc - I*r): [161/8, 11711/400] exactly", (lo, hi) == (F(161, 8), F(11711, 400)), str((lo, hi)))


# 2. random multilinear expressions against the corner hull and interior points
def random_case(rng):
    k = rng.randint(2, 5)
    names = [f"p{i}" for i in range(k)]
    boxes = {}
    for n in names:
        a = F(rng.randint(-20, 20), rng.randint(1, 5))
        w = F(rng.randint(1, 20), rng.randint(1, 5))
        boxes[n] = (a, a + w)
    terms = []
    for _ in range(rng.randint(1, 4)):
        size = rng.randint(1, min(3, k))
        terms.append((F(rng.randint(-9, 9) or 1, rng.randint(1, 4)), rng.sample(names, size)))
    expr = " + ".join(f"({fs(c)})*" + "*".join(m) for c, m in terms)
    return names, boxes, terms, expr


def value(terms, at):
    v = F(0)
    for c, m in terms:
        t = c
        for n in m:
            t *= at[n]
        v += t
    return v


def run_random(n=300, seed=7):
    rng = random.Random(seed)
    bad = []
    for i in range(n):
        names, boxes, terms, expr = random_case(rng)
        sheet = ", ".join(f"{nm}=[{fs(a)},{fs(b)}] credit" for nm, (a, b) in boxes.items()) + ", y=? credit"
        lo, hi, log, _ = narrowed(f"(y == {expr})", sheet, "y")
        vals = [value(terms, dict(zip(names, c))) for c in itertools.product(*[boxes[nm] for nm in names])]
        if (lo, hi) != (min(vals), max(vals)):
            bad.append((i, expr, (lo, hi), (min(vals), max(vals))))
            continue
        for _ in range(30):
            at = {nm: a + (b - a) * F(rng.randint(0, 1000), 1000) for nm, (a, b) in boxes.items()}
            if not (lo <= value(terms, at) <= hi):
                bad.append((i, expr, "interior point outside"))
                break
    return bad


bad = run_random()
check("300 random multilinear expressions: range == corner hull exactly, 9000 interior points inside",
      not bad, str(bad[:2]))

# 3. outside the multilinear class: not narrowed by THAT step (the interval reading takes it, check 6)
lo, hi, log, _ = narrowed("(x == R*R)", "R=[1,2] credit, x=? credit", "x")
check("x == R*R (a name squared): not claimed exact by the multilinear step; read as an interval [1, 4]",
      not any("multilinear" in l for l in log) and (lo, hi) == (1, 4) and any("interval reading" in l for l in log), str((lo, hi, log)))
lo, hi, log, _ = narrowed("(x == 1/R)", "R=[1,2] credit, x=? credit", "x")
check("x == 1/R (division by a box): not claimed exact; read as an interval [1/2, 1]",
      not any("multilinear" in l for l in log) and (lo, hi) == (F(1, 2), 1), str((lo, hi, log)))

# 4. own box intersected; disjoint -> empty
lo, hi, log, _ = narrowed("(tau == R*C)", "R=[99/10,101/10] credit, C=[19/2,21/2] credit, tau=[100,200] credit", "tau")
check("a defined name's own box is intersected: [100, 106.05]", (lo, hi) == (F(100), F(2121, 20)), str((lo, hi)))
_, _, log, q = narrowed("(tau == R*C)", "R=[99/10,101/10] credit, C=[19/2,21/2] credit, tau=[200,300] credit", "tau")
check("disjoint boxes empty the name (no solution), not a wrong value", bool(q.get("empty")), str(q))

# 5. mutation: a shrunk range must be caught by check 2
real = znumsolve._ev_mlin


def shrunk(expr, qs):
    got = real(expr, qs)
    if got is None:
        return None
    (lo, hi), *rest = got
    d = (hi - lo) / 100
    return ((lo + d, hi - d), *rest)


znumsolve._ev_mlin = shrunk
bad_m = run_random(n=40, seed=11)
znumsolve._ev_mlin = real
check("MUTATION: a 1% shrunk range is caught by the corner/interior check", len(bad_m) > 0, "mutation survived")

# 6. _iv_eq: sound on non-multilinear expressions
def random_nonlinear(rng):
    k = rng.randint(1, 3)
    names = [f"q{i}" for i in range(k)]
    boxes = {}
    for n in names:
        a = F(rng.randint(1, 20), rng.randint(1, 5))          # positive boxes: divisions are defined
        boxes[n] = (a, a + F(rng.randint(1, 20), rng.randint(1, 5)))
    shapes = [lambda a, b: f"{a}*{a}*{b}", lambda a, b: f"1/({a} + {b})", lambda a, b: f"{a}*{a} - {b}",
              lambda a, b: f"{a}/{b} + {b}*{b}", lambda a, b: f"({a} - {b})*({a} + {b})*{a}"]
    a, b = rng.choice(names), rng.choice(names)
    return names, boxes, rng.choice(shapes)(a, b)


def run_nonlinear(n=200, seed=5):
    rng = random.Random(seed)
    bad = []
    for i in range(n):
        names, boxes, expr = random_nonlinear(rng)
        sheet = ", ".join(f"{nm}=[{fs(a)},{fs(b)}] credit" for nm, (a, b) in boxes.items()) + ", y=? credit"
        lo, hi, log, _ = narrowed(f"(y == {expr})", sheet, "y")
        if any("multilinear" in l and l.startswith("y ->") for l in log) and "*" in expr and \
                any(expr.count(nm + "*" + nm) for nm in names):
            bad.append((i, expr, "a squared name claimed multilinear"))
            continue
        pts = [dict(zip(names, c)) for c in itertools.product(*[boxes[nm] for nm in names])]
        pts += [{nm: a + (b - a) * F(rng.randint(0, 1000), 1000) for nm, (a, b) in boxes.items()} for _ in range(30)]
        for at in pts:
            v = eval(expr, {}, {k: F(v) for k, v in at.items()})
            if not (lo <= v <= hi):
                bad.append((i, expr, (lo, hi), v))
                break
    return bad


bad = run_nonlinear()
check("_iv_eq: 200 random non-multilinear expressions, every corner and 6000 interior points inside (sound)",
      not bad, str(bad[:2]))
lo, hi, log, q = narrowed("(Vin - Vout == I*R1) & (Vout == I*R2) & (P1 == I*I*R1)",
                          "Vin=5 earned:psu, R1=[99/10,101/10] credit, R2=[99/10,101/10] credit, I=? credit, "
                          "Vout=? credit, P1=? credit", "P1")
check("divider power P1 == I*I*R1: bounded [12375/20402, 12625/19602], logged as an interval reading",
      (lo, hi) == (F(12375, 20402), F(12625, 19602)) and any("interval reading" in l and l.startswith("P1") for l in log),
      str((lo, hi)))

# 6b. a SYSTEM is not a definition: the cycle that blew fractions past 4300 digits stays with the
#     system readings (u == s*s - 3*s & u - 2*s + 3 == 0: s in {1, 3}, u in {-1, 3})
r = solve_claim("(u == s*s - 3*s) & (u - 2*s + 3 == 0)", *parse_quantities("s=? credit, u=? credit"))
check("u == s*s - 3*s & u - 2*s + 3 == 0: no runaway fractions, the new steps stay out of a system",
      not any(("multilinear" in l or "interval reading" in l) for l in r["log"]) and len(str(r["narrowed"])) < 5000,
      str(r["log"])[:300])

# 7. mutation of the interval reading
real_ev = znumsolve._ev


def shrunk_ev(expr, qs):
    got = real_ev(expr, qs)
    iv = got[0]
    if iv is None:
        return got
    lo, hi = iv
    d = (hi - lo) / 100
    return ((lo + d, hi - d), *got[1:])


znumsolve._ev = shrunk_ev
bad_m = run_nonlinear(n=40, seed=13)
znumsolve._ev = real_ev
check("MUTATION: a 1% shrunk interval reading is caught by the corner/interior check", len(bad_m) > 0, "mutation survived")

print(f"mlin eq: {ok} ok, {fail} failed")
print("MLIN EQ GREEN" if fail == 0 else "MLIN EQ RED")
