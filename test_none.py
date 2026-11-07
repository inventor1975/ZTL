# -*- coding: utf-8 -*-
"""
Stand for zcertify.check_none: "this system of equations has NO solution in the box", proved by a brought
bisection tree whose leaves name an equation that is off zero there. The searcher here is outside the kernel
(bisect, try every equation's interval reading); the kernel trusts nothing it brings.

Checks:
  1. circle x^2+y^2=1 and line x+y=3 on [-2,2]^2: no common point (distance 3/sqrt2 > 1) -> certified;
  2. circle and line x=y DO meet (x=y=±1/sqrt2): the searcher finds no certificate, and a hand-made one
     that claims the meeting piece is REFUSED;
  3. 300 seeded random systems: every accepted certificate is SOUND (at 40 sampled points per leaf some
     named equation is off zero; and if a sampled exact solution exists, no certificate was accepted);
  4. MUTATIONS: 'which' changed to another equation where that one reads through 0, a subtree dropped,
     a split point outside its piece, an unknown leaf, 'which' out of range — all refused;
  5. MUTATION of the kernel: readings collapsed to the midpoint let check 2's false claim through.
  6. BLOW-UPS: x(x-y)=0, y(x+y)=0 meet only at the origin; with the condition x != 0 a chart at the origin
     certifies "no admissible solution" in [-1,1]^2; without the condition the centre check refuses; a wrong
     power, a wrong G, a dropped condition are refused; a system with a second, genuine solution (1/2,1/2)
     gets no certificate even with the origin blown up.
Run:  python3 test_none.py   -> NONE GREEN
"""
import os, random, sys
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcertify as ZC                               # noqa: E402
from znumjudge import _parse_arith, parse_quantities  # noqa: E402

ok = fail = 0
def check(name, cond, why=""):
    global ok, fail
    if cond: ok += 1; print(f"  OK   {name}")
    else: fail += 1; print(f"  FAIL {name} — {why}")

def search(exprs, qs, maxd=14):
    names = sorted(set().union(*[ZC._names(e) for e in exprs]) & set(qs))
    def rec(piece, d):
        for k, e in enumerate(exprs):
            r = ZC._reading(e, qs, piece)
            if r is not None and (r[0] > 0 or r[1] < 0):
                return {"leaf": "nonzero", "which": k}
        if d >= maxd or not names: return None
        n = max(names, key=lambda m: piece[m][1] - piece[m][0])
        lo, hi = piece[n]; at = (lo + hi) / 2
        L = rec(dict(piece, **{n: (lo, at)}), d + 1)
        if L is None: return None
        H = rec(dict(piece, **{n: (at, hi)}), d + 1)
        if H is None: return None
        return {"split": n, "at": f"{at.numerator}/{at.denominator}", "lo": L, "hi": H}
    return rec({n: (qs[n]["lo"], qs[n]["hi"]) for n in names}, 0)

def sys_of(eqs, qtext):
    qs = parse_quantities(qtext)[0]
    return [_parse_arith(s, qs) for s in eqs], qs

print("1. circle and a far line")
E1, Q1 = sys_of(["x*x + y*y - 1", "x + y - 3"], "x=[-2,2] credit, y=[-2,2] credit")
c1 = search(E1, Q1)
check("a certificate is found", c1 is not None)
r = ZC.check_none(E1, Q1, c1) if c1 else (False, "none")
check("the kernel accepts it", r[0], r[1])

print("2. circle and a line through it")
E2, Q2 = sys_of(["x*x + y*y - 1", "x - y"], "x=[-2,2] credit, y=[-2,2] credit")
check("no certificate is found (they meet)", search(E2, Q2, maxd=10) is None)
false_cert = {"leaf": "nonzero", "which": 0}
check("a whole-box 'circle is off zero' leaf is refused", not ZC.check_none(E2, Q2, false_cert)[0])
fake = {"split": "x", "at": "0", "lo": {"leaf": "nonzero", "which": 1}, "hi": {"leaf": "nonzero", "which": 0}}
check("a split claim over the meeting points is refused", not ZC.check_none(E2, Q2, fake)[0])

print("3. random systems: sound")
rng = random.Random(20261107)
def rnd_poly(names):
    terms = []
    for _ in range(rng.randint(1, 3)):
        c = rng.randint(-3, 3) or 1
        mon = "*".join(rng.choice(names) for _ in range(rng.randint(0, 2))) or "1"
        terms.append(f"{c}*{mon}")
    return " + ".join(terms) + f" + {rng.randint(-4, 4)}"
def ev(s, pt):
    return eval(s.replace("^", "**"), {}, dict(pt))
acc = sound = 0; bad = []
for t in range(300):
    names = ["x", "y"][:rng.randint(1, 2)]
    eqs = [rnd_poly(names) for _ in range(rng.randint(1, 3))]
    E, Q = sys_of(eqs, ", ".join(f"{n}=[-2,2] credit" for n in names))
    c = search(E, Q, maxd=8)
    if c is None: continue
    res = ZC.check_none(E, Q, c)
    if not res[0]: bad.append(("searcher cert refused", eqs, res[1])); continue
    acc += 1
    # soundness: at grid points (exact) some equation is nonzero
    good = True
    for i in range(41):
        for j in range(41 if len(names) == 2 else 1):
            pt = {"x": F(-2) + F(i, 10)}
            if len(names) == 2: pt["y"] = F(-2) + F(j, 10)
            if all(ev(s, pt) == 0 for s in eqs): good = False
    sound += good
    if not good: bad.append(("UNSOUND", eqs))
check(f"{acc} accepted certificates, every grid point off the system", acc > 30 and sound == acc and not bad, str(bad[:3]))

print("4. mutations refused")
def mutants(c):
    if "split" in c:
        yield {**c, "lo": {"leaf": "nonzero", "which": 99}}
        yield {k: v for k, v in c.items() if k != "hi"}
        yield {**c, "at": "5"}
        for m in mutants(c["lo"]): yield {**c, "lo": m}
    else:
        yield {"leaf": "nonzero", "which": 1 - c["which"]}
        yield {"leaf": "interval", "which": c["which"]}
ms = list(mutants(c1)); refused = 0
for m in ms:
    if not ZC.check_none(E1, Q1, m)[0]: refused += 1
# a which-swap can be honestly accepted when the other equation is off zero there too; the rest must fail
hard = [m for m in ms if not (m.get("leaf") == "nonzero" and m.get("which") in (0, 1) and "split" not in m)]
check(f"structural mutants refused ({sum(1 for m in hard if not ZC.check_none(E1, Q1, m)[0])}/{len(hard)})",
      all(not ZC.check_none(E1, Q1, m)[0] for m in hard))

print("5. a lying kernel is seen")
orig = ZC._reading
ZC._reading = lambda e, qs, piece, **kw: (lambda r: None if r is None else ((r[0] + r[1]) / 2 + F(1, 10**9),) * 2)(orig(e, qs, piece))
lie = ZC.check_none(E2, Q2, false_cert)[0]
ZC._reading = orig
check("midpoint readings accept the false claim (the stand detects the lie)", lie)

print("6. blow-ups")
def poly_text(p):
    if not p: return "0"
    out = []
    for m, c in p.items():
        mon = "*".join("*".join([n] * k) for n, k in m) or "1"
        out.append(f"({c.numerator}/{c.denominator})*{mon}")
    return " + ".join(out)
def divide_r(e, mp, rn):
    p = ZC.poly(ZC.subst(e, mp))
    if not p: return "0", 0
    m = min(dict(mon).get(rn, 0) for mon in p)
    q = {}
    for mon, c in p.items():
        d = dict(mon); d[rn] = d.get(rn, 0) - m
        if d[rn] == 0: del d[rn]
        q[tuple(sorted(d.items()))] = c
    return poly_text(q), m
def chart_cert(E, N, Q, u, v, a, b, rho, maxd=10):
    C = {"vars": [u, v], "at": [str(a), str(b)], "rho": str(rho)}
    for side, mp in (("X", {u: ("add", F(a), "r"), v: ("add", F(b), ("mul", "r", "s"))}),
                     ("Y", {u: ("add", F(a), ("mul", "r", "s")), v: ("add", F(b), "r")})):
        eq = [divide_r(e, mp, "r") for e in E]; nq = [divide_r(n, mp, "r") for n in N]
        q2 = dict(Q); q2["r"] = dict(Q[u], lo=-F(rho), hi=F(rho)); q2["s"] = dict(Q[u], lo=F(-1), hi=F(1))
        G = [_parse_arith(t, q2) for t, _ in eq]
        T = search(G, q2, maxd)
        if T is None: return None
        C[side] = {"names": ["r", "s"], "eqs": [t for t, _ in eq], "pows": [m for _, m in eq],
                   "neqs": [t for t, _ in nq], "npows": [m for _, m in nq], "tree": T}
    return {"chart": C}
E6, Q6 = sys_of(["x*(x - y)", "y*(x + y)"], "x=[-1,1] credit, y=[-1,1] credit")
N6 = [_parse_arith("x", Q6)]
check("plain bisection cannot close it (the origin solves both)", search(E6, Q6, maxd=10) is None)
c6 = chart_cert(E6, N6, Q6, "x", "y", 0, 0, 1)
check("a blow-up certificate is found", c6 is not None)
r6 = ZC.check_none(E6, Q6, c6, N6) if c6 else (False, "none")
check("the kernel accepts it with the condition x != 0", r6[0], r6[1])
check("without the condition the centre is refused", not ZC.check_none(E6, Q6, c6, [])[0])
bad = {"chart": dict(c6["chart"], X=dict(c6["chart"]["X"], pows=[3, 2]))}
check("a wrong power is refused", not ZC.check_none(E6, Q6, bad, N6)[0])
bad = {"chart": dict(c6["chart"], Y=dict(c6["chart"]["Y"], eqs=["s", "s + 1"]))}
check("a wrong G is refused", not ZC.check_none(E6, Q6, bad, N6)[0])
bad = {"chart": dict(c6["chart"], rho="1/2")}
check("a square smaller than the piece is refused", not ZC.check_none(E6, Q6, bad, N6)[0])
sub = {"chart": dict(c6["chart"], X=dict(c6["chart"]["X"], keep=[0, 1]), Y=dict(c6["chart"]["Y"], keep=[0, 1]))}
check("an explicit full 'keep' is accepted", ZC.check_none(E6, Q6, sub, N6)[0])
one = dict(c6["chart"]["X"], keep=[1], eqs=[c6["chart"]["X"]["eqs"][1]], pows=[c6["chart"]["X"]["pows"][1]])
check("a 'keep' whose part has solutions in the chart is refused", not ZC.check_none(E6, Q6, {"chart": dict(c6["chart"], X=one)}, N6)[0])
check("a 'keep' naming a missing equation is refused",
      not ZC.check_none(E6, Q6, {"chart": dict(c6["chart"], X=dict(c6["chart"]["X"], keep=[0, 7]))}, N6)[0])
E8, Q8 = sys_of(["x - y"], "x=[-1,1] credit, y=[-1,1] credit")
N8z = [_parse_arith("x*y - y*x", Q8)]
check("an identically-zero condition excludes the whole box", ZC.check_none(E8, Q8, {"leaf": "excluded", "cond": 0}, N8z)[0])
N8 = [_parse_arith("x*y - 1", Q8)]
check("a condition that is not identically zero is refused as 'excluded'", not ZC.check_none(E8, Q8, {"leaf": "excluded", "cond": 0}, N8)[0])
check("'excluded' naming no condition is refused", not ZC.check_none(E8, Q8, {"leaf": "excluded", "cond": 3}, N8z)[0])
E7, Q7 = sys_of(["x - y", "(x - 1/2)*(x + y)"], "x=[-1,1] credit, y=[-1,1] credit")
N7 = [_parse_arith("x", Q7)]
c7 = chart_cert(E7, N7, Q7, "x", "y", 0, 0, 1)
check("a genuine solution (1/2,1/2) blocks every certificate", c7 is None or not ZC.check_none(E7, Q7, c7, N7)[0])

print(f"\n{ok} OK, {fail} FAIL")
print("NONE GREEN" if fail == 0 else "NONE RED")
sys.exit(0 if fail == 0 else 1)
