# -*- coding: utf-8 -*-
"""
Stand for zfunc.py: exp, ln, log10, atan, tan, pow, min, max on the numeric floor.

The reference is mpmath at 60 digits — a different implementation from the series here.
Checks:
  1. POINTS: 400 seeded arguments per function; the true value lies inside every bracket,
     and every bracket is narrow (relative width under 1e-13);
  2. INTERVALS: 300 seeded intervals per function; 25 interior points each (true values at
     60 digits) lie inside the interval bracket — sound over the whole interval;
  3. DOMAINS: ln of a never-positive interval has no readings; one touching 0 is a mark
     (None); tan past 1.5 likewise; a non-integer power of a never-positive base refused;
  4. THE READER: exp(x), pow(a, b), min/max split at the top-level comma; a wrong count
     of arguments is refused aloud;
  5. THE JUDGE: ln(x)*2 <= 1.3864 on x in [1, 2] is forced (ON CREDIT, x on credit);
     <= 1.38 is not (2·ln 2 = 1.3863); a transcendental of a quantity with a unit is E;
  6. CERTIFICATES: x·exp(−x) <= 1/e + 1e-9 on [0, 5] — the peak at x = 1 is INSIDE —
     certified by a split tree the kernel checks; the false bound 0.3678 refused;
     every derivative agrees with a central difference at 40 random points;
  7. MUTATION: with exp's bracket shrunk by 1% of its width plus a hair, check 1 must FAIL.

Run:  python3 test_zfunc.py   -> ZFUNC GREEN
"""
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath                                       # noqa: E402
import zfunc as Z                                   # noqa: E402
import zcertify as ZC                               # noqa: E402
from znumjudge import parse_quantities, _parse_arith   # noqa: E402
from znumsolve import solve_claim                   # noqa: E402

mpmath.mp.dps = 60
ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def mp(x):
    return mpmath.mpf(x.numerator) / x.denominator


FUNCS = [
    ("exp", Z.exp_pt, mpmath.exp, lambda r: F(r.randint(-40000, 40000), r.randint(1, 1000))),
    ("ln", Z.ln_pt, mpmath.log, lambda r: F(r.randint(1, 10 ** 9), r.randint(1, 10 ** 6))),
    ("atan", Z.atan_pt, mpmath.atan, lambda r: F(r.randint(-10 ** 6, 10 ** 6), r.randint(1, 1000))),
    ("tan", Z.tan_pt, mpmath.tan, lambda r: F(r.randint(-1500, 1500), 1000)),
]


def points(n=400, seed=5):
    rng, bad, wide = random.Random(seed), [], []
    for name, f, ref, gen in FUNCS:
        for _ in range(n):
            x = gen(rng)
            lo, hi = f(x)
            t = ref(mp(x))
            if not (mp(lo) <= t <= mp(hi)):
                bad.append((name, x))
            elif t != 0 and (mp(hi) - mp(lo)) / abs(t) > mpmath.mpf("1e-13"):
                wide.append((name, x))
    return bad, wide


print("1. points against mpmath (60 digits)")
bad, wide = points()
check("1600 brackets (exp, ln, atan, tan): the true value inside every one", not bad, str(bad[:3]))
check("and every bracket narrow (relative width < 1e-13)", not wide, str(wide[:3]))
check("pi and ln 2 bracketed", mp(Z.PI[0]) <= mpmath.pi <= mp(Z.PI[1]) and mp(Z.LN2[0]) <= mpmath.log(2) <= mp(Z.LN2[1]))

print("2. intervals: sound over the whole interval")


def intervals(n=300, seed=9):
    rng, bad = random.Random(seed), []
    cases = [("exp", Z.iv_exp, mpmath.exp, lambda: F(rng.randint(-300, 300), 10)),
             ("ln", Z.iv_ln, mpmath.log, lambda: F(rng.randint(1, 10 ** 5), 100)),
             ("log10", Z.iv_log10, mpmath.log10, lambda: F(rng.randint(1, 10 ** 5), 100)),
             ("atan", Z.iv_atan, mpmath.atan, lambda: F(rng.randint(-10 ** 4, 10 ** 4), 100)),
             ("tan", Z.iv_tan, mpmath.tan, lambda: F(rng.randint(-1499, 1499), 1000))]
    for name, f, ref, gen in cases:
        for _ in range(n):
            a, b = sorted((gen(), gen()))
            r = f((a, b))
            for k in range(25):
                x = a + (b - a) * F(k, 24)
                t = ref(mp(x))
                if not (mp(r[0]) <= t <= mp(r[1])):
                    bad.append((name, a, b, x))
                    break
    for _ in range(n):                                   # pow(x, y), x > 0
        a, b = sorted((F(rng.randint(1, 500), 100), F(rng.randint(1, 500), 100)))
        c, d = sorted((F(rng.randint(-300, 300), 100), F(rng.randint(-300, 300), 100)))
        r = Z.iv_pow((a, b), (c, d))
        for k in range(25):
            x, y = a + (b - a) * F(rng.randint(0, 100), 100), c + (d - c) * F(rng.randint(0, 100), 100)
            t = mpmath.power(mp(x), mp(y))
            if not (mp(r[0]) <= t <= mp(r[1])):
                bad.append(("pow", a, b, c, d))
                break
    return bad


bad = intervals()
check("1800 intervals (exp, ln, log10, atan, tan, pow): 25 points each inside the bracket", not bad, str(bad[:3]))
check("integer powers exact: (-2..3)^2 = [0, 9], (-2..3)^3 = [-8, 27], (1..2)^-1 = [1/2, 1]",
      Z.iv_pow((F(-2), F(3)), (F(2), F(2))) == (0, 9) and Z.iv_pow((F(-2), F(3)), (F(3), F(3))) == (-8, 27)
      and Z.iv_pow((F(1), F(2)), (F(-1), F(-1))) == (F(1, 2), 1))
check("min/max exact", Z.iv_min((F(1), F(3)), (F(2), F(5))) == (1, 3) and Z.iv_max((F(1), F(3)), (F(2), F(5))) == (2, 5))

print("3. domains")


def raises(f, *a):
    try:
        f(*a)
        return False
    except Z.NoReadings:
        return True


check("ln of [-1, -1/2]: no readings", raises(Z.iv_ln, (F(-1), F(-1, 2))))
check("ln of [0, 1]: a mark (None), not a value", Z.iv_ln((F(0), F(1))) is None)
check("tan of [1.6, 2]: no readings; of [1, 1.6]: a mark", raises(Z.iv_tan, (F(8, 5), F(2))) and Z.iv_tan((F(1), F(8, 5))) is None)
check("pow of a never-positive base to a non-integer power: refused", raises(Z.iv_pow, (F(-2), F(-1)), (F(1, 2), F(1, 2))))

print("4. the reader")
q = parse_quantities("x=[1,2] credit, y=[0,1] credit")[0]
check("exp(x) + pow(x, y+1)*min(x, 3): the nodes",
      _parse_arith("exp(x) + pow(x, y+1)*min(x, 3)", q) == ("add", ("exp", "x"), ("mul", ("pow", "x", ("add", "y", F(1))), ("min", "x", F(3)))))
try:
    _parse_arith("pow(x)", q); refused = False
except ValueError:
    refused = True
check("pow with one argument: refused aloud", refused)

print("5. the judge")
qs = lambda: parse_quantities("x=[1,2] credit")
check("ln(x)*2 <= 1.3864 on [1, 2]: forced, ON CREDIT (x on credit)", solve_claim("ln(x)*2 <= 1.3864", *qs())["disposition"] == "ON CREDIT")
check("ln(x)*2 <= 1.38: not forced (2 ln 2 = 1.3863)", solve_claim("ln(x)*2 <= 1.38", *qs())["disposition"] == "OPEN")
check("exp(x) >= 2.71: forced", solve_claim("exp(x) >= 2.71", *qs())["disposition"] == "ON CREDIT")
r = solve_claim("exp(L) <= 3", *parse_quantities("L=[1,2] credit m"))
check("exp of a length (unit m): E — a transcendental reads a dimensionless argument", r["disposition"] == "E" or r["disposition"] == "OPEN"
      and any("dimensionless" in str(x) for x in r.get("log", [])), str(r.get("disposition")))

print("6. certificates")
q6 = parse_quantities("x=[0,5] credit")[0]
e6 = _parse_arith("x*exp(0 - x)", q6)


def search(e, qs, op, bound, depth=40):
    names = sorted(n for n in ZC._names(e) if n in qs)
    derivs = {n: ZC.derivative(e, n) for n in names}

    def go(piece, d):
        signs, straddle = {}, False
        for n in names:
            r = ZC._reading(derivs[n], qs, piece)
            if r is not None and r[0] >= 0:
                signs[n] = "+"
            elif r is not None and r[1] <= 0:
                signs[n] = "-"
            else:
                straddle = True
        if not straddle:
            return {"leaf": "monotone", "signs": signs}
        r = ZC._reading(e, qs, piece)
        if r is not None and r[1] <= bound:
            return {"leaf": "interval"}
        if d == 0:
            return {"leaf": "interval"}           # the kernel will refuse it: the search gave up here
        n = names[0]
        lo, hi = piece[n]
        at = (lo + hi) / 2
        return {"split": n, "at": f"{at.numerator}/{at.denominator}",
                "lo": go(dict(piece, **{n: (lo, at)}), d - 1), "hi": go(dict(piece, **{n: (at, hi)}), d - 1)}

    return go({n: (qs[n]["lo"], qs[n]["hi"]) for n in names}, depth)


bound = F(367879442, 10 ** 9)          # 1/e = 0.367879441171... -> 1e-9 above
cert = search(e6, q6, "<=", bound)
res = ZC.check(e6, q6, "<=", bound, cert)
check(f"x·exp(-x) <= 0.367879442 (1/e is 0.3678794411714) on [0, 5], the peak inside: certified ({res[1]} pieces)",
      res[0], str(res))
check("the false bound 0.3678 under the same tree: refused", not ZC.check(e6, q6, "<=", F(3678, 10000), cert)[0])
rng, badd = random.Random(3), []
qd = parse_quantities("x=[1,2] credit, y=[1,3] credit")[0]
for t in ["exp(x*y)", "ln(x+y)", "log10(x*y)", "atan(x/y)", "tan(x/4)", "pow(x, y)", "pow(x, 3)", "x*exp(0-y)"]:
    e = _parse_arith(t, qd)
    for _ in range(5):
        px, py = F(rng.randint(110, 190), 100), F(rng.randint(110, 290), 100)
        for n in "xy":
            d = ZC.derivative(e, n)
            r = ZC._reading(d, qd, {"x": (px, px), "y": (py, py)})
            h = F(1, 10 ** 7)
            f = lambda a, b: mp(ZC._reading(e, qd, {"x": (a, a), "y": (b, b)})[0])
            nd = (f(px + h, py) - f(px - h, py)) / (2 * mp(h)) if n == "x" else (f(px, py + h) - f(px, py - h)) / (2 * mp(h))
            if abs(mp(r[0]) - nd) > mpmath.mpf("1e-6") * (1 + abs(nd)):
                badd.append((t, n, px, py))
check("derivatives of exp, ln, log10, atan, tan, pow agree with a central difference at 40 points", not badd, str(badd[:3]))
try:
    ZC.derivative(_parse_arith("min(x, y)", qd), "x"); nod = False
except ZC.NoDerivative:
    nod = True
check("min/max: no derivative (a monotone leaf refuses them; an interval leaf may still use them)", nod)

print("7. mutation")
real = Z.exp_pt


def shrunk(x):
    lo, hi = real(x)
    d = (hi - lo) / 100 + F(1, 10 ** 30) * (abs(hi) + 1)
    return lo + d, hi - d


Z.exp_pt = shrunk
FUNCS[0] = ("exp", Z.exp_pt, mpmath.exp, FUNCS[0][3])
bad_m, _ = points(n=60, seed=11)
Z.exp_pt = real
FUNCS[0] = ("exp", Z.exp_pt, mpmath.exp, FUNCS[0][3])
check("MUTATION: exp's bracket shrunk by a hair — the mpmath check sees values outside", len(bad_m) > 0)

print(f"zfunc: {ok} ok, {fail} failed")
print("ZFUNC GREEN" if fail == 0 else "ZFUNC RED")
