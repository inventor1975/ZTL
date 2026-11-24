# -*- coding: utf-8 -*-
"""The 2026-11-25 integer words (gcd lcm fib totient isprime) and floor/ceil: point values against definitions, and
every interval reading CONTAINS every point's value (soundness), with excluded ends."""
import math
import random
import sys
from fractions import Fraction

import zfunc
from zgap import gap
from znumjudge import judge_sheet_claim, parse_quantities

checks = fails = 0


def ok(cond, what):
    global checks, fails
    checks += 1
    if not cond:
        fails += 1
        print("FAIL", what)


def judge(c, qs="x=[0,1] earned:hyp"):
    q, m = parse_quantities(qs)
    return judge_sheet_claim(c, q, m)["disposition"]


# 1. definitions at points
for n in range(0, 60):
    ok(zfunc._totient_pt(n) == sum(1 for k in range(1, n + 1) if math.gcd(k, n) == 1), f"totient({n})")
    ok(zfunc._isprime_pt(n) == (1 if n >= 2 and all(n % d for d in range(2, n)) else 0), f"isprime({n})")
fib = [0, 1]
for _ in range(60):
    fib.append(fib[-1] + fib[-2])
for n in range(60):
    ok(zfunc._fib_pt(n) == fib[n], f"fib({n})")
for c, want in (("gcd(12, 18) == 6", "EARNED"), ("lcm(4, 6) == 12", "EARNED"), ("gcd(0, 0) == 0", "EARNED"),
                ("lcm(0, 5) == 0", "EARNED"), ("gcd(0 - 12, 18) == 6", "EARNED"), ("isprime(91) == 1", "REFUTED"),
                ("isprime(97) == 1", "EARNED"), ("totient(1) == 1", "EARNED"), ("fib(30) == 832040", "EARNED"),
                ("floor(27/10) == 2", "EARNED"), ("floor(0 - 1/2) == (0 - 1)", "EARNED"), ("ceil(1/3) == 1", "EARNED")):
    ok(judge(c) == want, c)
# 2. soundness over integer ranges: the interval holds every point's value
rng = random.Random(20261125)
for _ in range(400):
    a0 = rng.randint(0, 30)
    a = (Fraction(a0), Fraction(a0 + rng.randint(0, 12)))
    b0 = rng.randint(0, 30)
    b = (Fraction(b0), Fraction(b0 + rng.randint(0, 12)))
    for name, f, pt in (("gcd", zfunc.iv_gcd, lambda x, y: math.gcd(x, y)),
                        ("lcm", zfunc.iv_lcm, lambda x, y: x * y // math.gcd(x, y) if x and y else 0)):
        iv = f(a, b)
        if iv is not None:
            ok(all(iv[0] <= pt(x, y) <= iv[1] for x in range(int(a[0]), int(a[1]) + 1)
                   for y in range(int(b[0]), int(b[1]) + 1)), f"{name} {a} {b}")
    for name, f, pt in (("fib", zfunc.iv_fib, zfunc._fib_pt), ("totient", zfunc.iv_totient, zfunc._totient_pt),
                        ("isprime", zfunc.iv_isprime, zfunc._isprime_pt)):
        iv = f(a)
        if iv is not None:
            ok(all(iv[0] <= pt(x) <= iv[1] for x in range(int(a[0]), int(a[1]) + 1)), f"{name} {a}")
# 3. floor / ceil over rational intervals, ends excluded or not
for _ in range(600):
    lo = Fraction(rng.randint(-40, 40), rng.choice([1, 2, 3, 4]))
    hi = lo + Fraction(rng.randint(0, 30), rng.choice([1, 2, 3]))
    lo_x, hi_x = rng.random() < 0.5, rng.random() < 0.5
    if lo == hi and (lo_x or hi_x):
        continue
    x = (gap(lo) if lo_x else lo, gap(hi) if hi_x else hi)
    pts = [lo + (hi - lo) * Fraction(k, 24) for k in range(25)]
    pts = [p for p in pts if (p > lo or not lo_x) and (p < hi or not hi_x)]
    fl, ce = zfunc.iv_floor(x), zfunc.iv_ceil(x)
    ok(all(fl[0] <= math.floor(p) <= fl[1] for p in pts), f"floor {x}")
    ok(all(ce[0] <= math.ceil(p) <= ce[1] for p in pts), f"ceil {x}")
ok(judge("floor(x) == 2", "x=[2,3) earned:hyp") == "EARNED", "floor on [2, 3)")
ok(judge("ceil(x) == 3", "x=(2,3] earned:hyp") == "EARNED", "ceil on (2, 3]")
ok(judge("floor(x) == 2", "x=(2,3] earned:hyp") == "OPEN", "floor on (2, 3] reaches 3")
print(f"INTWORDS MORE GREEN — {checks} checks" if not fails else f"INTWORDS MORE RED: {fails} of {checks}")
sys.exit(1 if fails else 0)
