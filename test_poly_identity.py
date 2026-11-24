# -*- coding: utf-8 -*-
"""znum's exact polynomial-identity reading (_mpoly): identities decided, non-identities never decided by it."""
import random
import sys
from fractions import Fraction

import znum
import zsummation as zs
from znumjudge import judge_sheet_claim, parse_quantities

checks = fails = 0


def ok(cond, what):
    global checks, fails
    checks += 1
    if not cond:
        fails += 1
        print("FAIL", what)


QS = "x=[0,inf] earned:hyp, y=[-3,5] earned:hyp, z=[-1,1] earned:hyp, s=[0,1] earned:hyp sample"


def judge(c):
    qs, m = parse_quantities(QS)
    return judge_sheet_claim(c, qs, m)["disposition"]


def ptext(p, x):
    return "(" + " + ".join(f"(({c.numerator}/{c.denominator}) * ({x})**{k})" if k else f"({c.numerator}/{c.denominator})"
                            for k, c in sorted(p.items())) + ")"


# 1. Faulhaber: Σ_{i=0}^{x} i^k as the closed form == the classical formula, k = 1..3; and F(x) − F(x−1) == x^k, k ≤ 8
ok(judge(f"{ptext(zs.faulhaber({1: 1}), 'x')} == (x * (x + 1)) / 2") == "EARNED", "Σ i")
ok(judge(f"{ptext(zs.faulhaber({2: 1}), 'x')} == (x * (x + 1) * (2 * x + 1)) / 6") == "EARNED", "Σ i²")
ok(judge(f"{ptext(zs.faulhaber({3: 1}), 'x')} == ((x * (x + 1)) / 2)**2") == "EARNED", "Σ i³")
for k in range(1, 9):
    F = zs.faulhaber({k: 1})
    ok(judge(f"({ptext(F, 'x')} - {ptext(F, 'x - 1')}) == x**{k}") == "EARNED", f"F(x) − F(x−1) = x^{k}")
# 2. several names; the six comparisons of an identity
ok(judge("(x + y)**2 == x**2 + 2*x*y + y**2") == "EARNED", "binomial square")
ok(judge("(x + y + z)**3 - (x**3 + y**3 + z**3) == 3*(x + y)*(y + z)*(z + x)") == "EARNED", "cube identity")
for op, want in (("==", "EARNED"), ("<=", "EARNED"), (">=", "EARNED"), ("<", "REFUTED"), (">", "REFUTED"),
                 ("!=", "REFUTED")):
    ok(judge(f"(x - y) * (x + y) {op} x**2 - y**2") == want, f"difference of squares {op}")
# 3. what it must NOT decide: a non-zero difference, a division by a variable, a sample
ok(znum._poly_identity(("mul", "x", "x"), ("mul", "x", "y"), parse_quantities(QS)[0]) is None, "x² vs xy")
ok(znum._poly_identity(("div", "x", "x"), 1, parse_quantities(QS)[0]) is None, "x/x is not a polynomial")
ok(znum._poly_identity(("mul", "s", "s"), ("mul", "s", "s"), parse_quantities(QS)[0]) is None, "a sample gives up")
# 4. random: a claimed identity with one coefficient perturbed is never EARNED by == ; unperturbed always is
rng = random.Random(20261125)
names = ["x", "y", "z"]


def rnd_poly(depth):
    if depth == 0 or rng.random() < 0.3:
        return rng.choice(names + [str(rng.randint(-3, 3))])
    a, b = rnd_poly(depth - 1), rnd_poly(depth - 1)
    return f"({a} {rng.choice(['+', '-', '*'])} {b})"


qs0 = parse_quantities(QS)[0]
for _ in range(300):
    t = rnd_poly(4)
    e = znum._mpoly(znum_parse := __import__("znumjudge")._parse_arith(t, {n: {} for n in names}), qs0)
    ok(judge(f"{t} == {t} + 0") == "EARNED", f"{t} == itself")
    if e:
        ok(judge(f"{t} == {t} + 1") != "EARNED", f"{t} == itself + 1")
print(f"test_poly_identity: {checks - fails}/{checks}")
sys.exit(1 if fails else 0)
