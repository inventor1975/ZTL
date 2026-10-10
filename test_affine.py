# -*- coding: utf-8 -*-
"""
Stand for zaffine.py (the affine reading) and for the parameter partitions of zimplicit.py.

Checks:
  1. SOUND: 400 seeded random expressions (+ - * / exp ln sqrt atan pow min), random boxes; every one of 40
     random points per expression lies inside the affine reading; the reading is never wider than the
     plain one after the meet (zcertify._reading);
  2. it HELPS where the dependency is: x*x - 2*x, sqrt(x) - x/3, ln(x*y) - ln(x) read tighter than plainly;
  3. MUTATION: an affine reading with the remainder dropped (err := 0) puts sampled points outside — the
     stand sees it;
  4. PARTITIONS: the oil cooler's law (blind test 2, c01) — the kernel accepts the stand's partition that
     excludes Tho in [62, 72.7]; FORGERIES refused: a leaf whose reading does not exclude 0, a cut outside its
     part, a part missing, a cut on a name not in the box;
  5. the oil cooler, pulled in: Tho within [40.7, 59.2] (the blind author's scipy maximum 58.9 inside).

Run:  python3 test_affine.py   -> AFFINE GREEN
"""
import math
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zaffine as ZA                                 # noqa: E402
import zcertify as ZC                                # noqa: E402
import zimplicit as ZI                               # noqa: E402
import znum                                          # noqa: E402
from znumjudge import _parse_arith, parse_quantities  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def aff(e, q, piece=None):
    return ZA.read(e, q, piece or {}, znum._rat_sqrt, lambda n: ZC._plain(n, q))


print("1. sound on random expressions")
rnd = random.Random(7)


def gen(d):
    if d == 0 or rnd.random() < 0.25:
        return rnd.choice(["x", "y", "z", str(rnd.randint(1, 5)), f"{rnd.randint(1, 9)}/{rnd.randint(2, 9)}"])
    if rnd.random() < 0.5:
        return f"({gen(d - 1)} {rnd.choice(['+', '-', '*', '/'])} {gen(d - 1)})"
    f = rnd.choice(["exp", "ln", "sqrt", "atan", "pow2", "min"])
    a = gen(d - 1)
    if f == "pow2":
        return f"pow({a}, 2)"
    if f == "min":
        return f"min({a}, {gen(d - 1)})"
    if f in ("ln", "sqrt"):
        return f"{f}(({a})*({a}) + 1)"
    if f == "exp":
        return f"exp(({a})/10)"
    return f"{f}({a})"


FNS = {"exp": math.exp, "ln": math.log, "sqrt": math.sqrt, "atan": math.atan, "pow": pow, "min": min}
total = outside = wider = 0
for _ in range(400):
    txt = gen(4)
    box = {"x": F(rnd.randint(-20, 10), 10), "y": F(rnd.randint(1, 20), 10), "z": F(rnd.randint(-5, 5))}
    box = {k: (v, v + F(rnd.randint(1, 30), 10)) for k, v in box.items()}
    q = parse_quantities(", ".join(f"{k}=[{v[0]},{v[1]}] credit" for k, v in box.items()))[0]
    try:
        e = _parse_arith(txt, q)
    except ValueError:
        continue
    pl = ZC._plain(e, q)
    af = aff(e, q)
    if pl is None or af is None or any(isinstance(v, float) for v in pl):
        continue
    total += 1
    meet = ZC._reading(e, q, {})
    wider += meet is not None and (meet[1] - meet[0]) > (pl[1] - pl[0])
    for _ in range(40):
        env = {k: float(v[0]) + rnd.random() * float(v[1] - v[0]) for k, v in box.items()}
        try:
            val = eval(txt, FNS, env)
        except (ZeroDivisionError, ValueError, OverflowError):
            continue
        tol = 1e-9 * max(1.0, abs(val))
        if not (float(af[0]) - tol <= val <= float(af[1]) + tol):
            outside += 1
            print("   outside:", txt, val, [float(a) for a in af])
            break
check(f"{total} random expressions: no sampled point outside the affine reading", total > 300 and outside == 0,
      (total, outside))
check("the meet with the plain reading is never wider than the plain one", wider == 0, wider)

print("2. where the dependency is")
q2 = parse_quantities("x=[1,2] credit, y=[3,4] credit")[0]
for txt, need in (("x*x - 2*x", F(3, 2)), ("sqrt(x) - x/3", F(1, 10)), ("ln(x*y) - ln(x)", F(1))):
    e = _parse_arith(txt, q2)
    r = ZC._reading(e, q2, {})
    check(f"{txt}: read narrower than {float(need)} (plainly {float(ZC._plain(e, q2)[1] - ZC._plain(e, q2)[0]):.3f})",
          r[1] - r[0] <= need, [float(v) for v in r])

print("3. mutation: the remainder dropped")
real_scale = ZA._scale
ZA._scale = lambda x, a, b=F(0), extra=F(0): real_scale(x, a, b, F(0))
seen = False
qm = parse_quantities("x=[0,3] credit")[0]
em = _parse_arith("exp(x) - x", qm)
am = aff(em, qm)
for i in range(301):
    xv = 3 * i / 300
    v = math.exp(xv) - xv
    if not (float(am[0]) <= v <= float(am[1])):
        seen = True
        break
ZA._scale = real_scale
check("with err := 0 the reading of exp(x) - x on [0, 3] misses true values — the stand sees it", seen)

print("4. partitions (the oil cooler, blind test 2 c01)")
OIL = ("mh=[97/50,103/50] credit, Thi=[93,97] credit, mc=[38/25,42/25] credit, Tci=[15,28] credit, "
       "Rf=[1/10000,6/10000] credit, Tho=? credit")
qo = parse_quantities(OIL)[0]
LAW = ("Thi - Tho - (1 - exp(0 - (1/(1/(1050*pow((Thi + Tho)/160, 0.8)*pow(mh/2, 0.5)) + Rf)*7/(mh*2100))"
       "*(1 - mh*2100/(mc*4180))))/(1 - mh*2100/(mc*4180)*exp(0 - (1/(1/(1050*pow((Thi + Tho)/160, 0.8)"
       "*pow(mh/2, 0.5)) + Rf)*7/(mh*2100))*(1 - mh*2100/(mc*4180))))*(mh*2100/(mh*2100))*(Thi - Tci)")
go = _parse_arith(LAW, qo)
names = ["Rf", "Tci", "Thi", "mc", "mh"]
box = {n: (qo[n]["lo"], qo[n]["hi"]) for n in names}
span = (F(62), F(73))
tree = ZI._split_tree(go, "Tho", qo, box, box, span, [3000])
check("a partition excluding Tho in [62, 73] is found and the KERNEL accepts it",
      tree is not None and ZI._check_tree(go, "Tho", qo, box, span, tree))


if tree and not tree.get("leaf"):
    check("forged: a split collapsed into a leaf whose reading does not exclude 0 — refused",
          not ZI._check_tree(go, "Tho", qo, box, span, {"leaf": True}))
    bad_at = dict(tree, at=str(box[tree["param"]][1] + 1))
    check("forged: a cut outside its part — refused", not ZI._check_tree(go, "Tho", qo, box, span, bad_at))
    check("forged: a part missing — refused", not ZI._check_tree(go, "Tho", qo, box, span, dict(tree, parts=tree["parts"][:1])))
    check("forged: a cut on a name not in the box — refused",
          not ZI._check_tree(go, "Tho", qo, box, span, dict(tree, param="nobody")))

print("5. the oil cooler pulled in")
cert = ZI.search_certificate(go, "Tho", qo, ["15", "97"], tighten=8)
res = ZI.check_implicit(go, "Tho", qo, cert)
check("Tho within [40.7, 59.2]: the author's scipy maximum 58.9 inside, the limit 62 cleared",
      res[0] and F(40) < res[1][0] <= F(589, 10) and F(589, 10) <= res[1][1] < F(592, 10),
      [float(v) for v in res[1]] if res[0] else res)

print(f"\n{ok} ok, {fail} fail")
print("AFFINE GREEN" if fail == 0 else "AFFINE RED")
sys.exit(1 if fail else 0)
