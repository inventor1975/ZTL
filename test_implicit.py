# -*- coding: utf-8 -*-
"""
Stand for zimplicit.py: a quantity fixed by an implicit law g(q, p) = 0, its range over the
box of p proved by a brought certificate and checked by the kernel.

The certificates come from zimplicit.search_certificate (the search, outside the check). The
stand does not trust either: every accepted range is compared with roots found by a different
route — float bisection at sampled parameter points, or the closed form where there is one.

Checks:
  1. the FAN of the blind test (b02): pmax(1 - Q/Qmax) = K Q^2 — the range equals the closed-form
     roots at the corners (to 1e-12), and the plain enclosure (no corners) contains it;
  2. the PUMP of the blind test (b03): head H0 - a Q^2 against the line z + (f L/D + Km) 8Q^2/(pi^2 g D^4)
     with Swamee-Jain friction f(Q) (log10, Re^0.9) — the coupling the author broke by hand;
     every sampled root lies inside the range;
  3. 150 seeded random laws (a q^3 + b q + c e^{d q} - p, and friends): accepted ranges contain
     every sampled root; where tight, the ends are within 1e-9 of the sampled extremes;
  4. TWO ROOTS (q^2 = p on [-3, 3]): "unique" is refused; the plain enclosure holds both;
  5. FORGERIES must be refused: a "none" piece over a root; a gap; an overlap; a wrong monotone
     sign; a corner bracket with no sign change; the wrong corner; an unbounded parameter;
  6. MUTATION of the kernel: with every reading collapsed to its midpoint, a forged "none" piece
     slips through — the stand sees a lying kernel.

Run:  python3 test_implicit.py   -> IMPLICIT GREEN
"""
import math
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zcertify as ZC                                # noqa: E402
import zimplicit as ZI                               # noqa: E402
from znumjudge import _parse_arith, parse_quantities  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def law(qtext, expr):
    qs = parse_quantities(qtext)[0]
    return qs, _parse_arith(expr, qs)


def float_roots(fn, lo, hi, n=400):
    """Sign changes of fn on a grid, refined by bisection — a route the kernel does not take."""
    out, xs = [], [lo + (hi - lo) * i / n for i in range(n + 1)]
    for a, b in zip(xs, xs[1:]):
        fa, fb = fn(a), fn(b)
        if fa == 0:
            out.append(a)
        elif fa * fb < 0:
            for _ in range(80):
                m = (a + b) / 2
                if fn(a) * fn(m) <= 0:
                    b = m
                else:
                    a = m
            out.append((a + b) / 2)
    return out


def run(qs, g, q, search, **kw):
    cert = ZI.search_certificate(g, q, qs, search, **kw)
    if cert is None:
        return None, None
    return cert, ZI.check_implicit(g, q, qs, cert)


# ------------------------------------------------------------------ 1. the fan
print("1. the fan (blind b02)")
qs, g = law("pmax=[44.16,51.84] credit, Qmax=[0.038,0.042] credit, K=[27200,36800] credit, Q=? credit",
            "pmax*(1 - Q/Qmax) - K*Q*Q")
cert, res = run(qs, g, "Q", ["0", "0.06"])


def fan_root(pm, qm, k):
    b = pm / qm
    return (-b + math.sqrt(b * b + 4 * k * pm)) / (2 * k)


truth = [fan_root(pm, qm, k) for pm in (44.16, 51.84) for qm in (0.038, 0.042) for k in (27200, 36800)]
check("fan: accepted, tight by corners", res[0] and "corner" in res[2], res)
check("fan: the ends equal the closed-form corner roots (1e-12)",
      abs(float(res[1][0]) - min(truth)) < 1e-12 and abs(float(res[1][1]) - max(truth)) < 1e-12,
      (res[1], min(truth), max(truth)))
plain = dict(cert); plain.pop("corners")
r2 = ZI.check_implicit(g, "Q", qs, plain)
check("fan: the plain enclosure contains the tight range",
      r2[0] and r2[1][0] <= res[1][0] and res[1][1] <= r2[1][1], r2)

# ------------------------------------------------------------------ 2. the pump
print("2. the pump (blind b03): Swamee-Jain friction coupled to the flow")
qs, g = law("H0=[38,42] credit, a=[9000,11000] credit, z=[14.5,15.5] credit, L=[118,122] credit, "
            "D=[0.0495,0.0505] credit, Km=[4.5,5.5] credit, eps=[0.000045,0.000055] credit, "
            "nu=[0.00000095,0.00000105] credit, pi=[3.14159265358979,3.14159265358980] credit, "
            "g0=[9.80665,9.80665] credit, Q=? credit",
            "H0 - a*Q*Q - z - (0.25/pow(log10(eps/(3.7*D) + 5.74/pow(4*Q/(pi*D*nu), 0.9)), 2)*L/D + Km)"
            "*8*Q*Q/(pi*pi*g0*pow(D, 4))")
cert, res = run(qs, g, "Q", ["0.001", "0.06"])
check("pump: accepted", res and res[0], res)
if res and res[0]:
    rnd = random.Random(7)
    worst_in = True
    for _ in range(60):
        p = {n: rnd.uniform(float(qs[n]["lo"]), float(qs[n]["hi"])) for n in
             ("H0", "a", "z", "L", "D", "Km", "eps", "nu")}

        def fn(Q, p=p):
            Re = 4 * Q / (math.pi * p["D"] * p["nu"])
            f = 0.25 / math.log10(p["eps"] / (3.7 * p["D"]) + 5.74 / Re ** 0.9) ** 2
            return p["H0"] - p["a"] * Q * Q - p["z"] - (f * p["L"] / p["D"] + p["Km"]) * 8 * Q * Q / (
                math.pi ** 2 * 9.80665 * p["D"] ** 4)
        for r in float_roots(fn, 0.001, 0.06):
            worst_in &= float(res[1][0]) - 1e-12 <= r <= float(res[1][1]) + 1e-12
    check("pump: 60 sampled roots inside the range", worst_in, res[1])
    print(f"       Q in [{float(res[1][0]):.6f}, {float(res[1][1]):.6f}] m3/s — {res[2]}")

# ------------------------------------------------------------------ 3. random laws
print("3. 150 random laws")
rnd = random.Random(20261010)
SHAPES = [
    ("a*q*q*q + b*q - p", lambda v, q: v["a"] * q ** 3 + v["b"] * q - v["p"]),
    ("a*q + c*exp(d*q) - p", lambda v, q: v["a"] * q + v["c"] * math.exp(v["d"] * q) - v["p"]),
    ("a*q - p/(1 + q*q) - b", lambda v, q: v["a"] * q - v["p"] / (1 + q * q) - v["b"]),
    ("atan(a*q) + b*q - p", lambda v, q: math.atan(v["a"] * q) + v["b"] * q - v["p"]),
    ("q*q - p*q + b", lambda v, q: q * q - v["p"] * q + v["b"]),
]
acc = contain = tight_ok = tight_n = refused_fine = 0
for i in range(150):
    text, fn = SHAPES[i % len(SHAPES)]
    names = sorted({"a", "b", "c", "d", "p"} & set(text.replace("q", " ").replace("exp", " ")
                                                     .replace("atan", " ").split()) | {
        n for n in "abcdp" if n in text.replace("exp", "").replace("atan", "")})
    box = {}
    for n in names:
        c = rnd.choice([0.5, 1, 2, 3])
        w = c * rnd.choice([0.02, 0.1, 0.3])
        box[n] = (round(c - w, 3), round(c + w, 3))
    qtext = ", ".join(f"{n}=[{lo},{hi}] credit" for n, (lo, hi) in box.items()) + ", q=? credit"
    qs, g = law(qtext, text)
    cert, res = run(qs, g, "q", ["-4", "4"])
    if not res or not res[0]:
        continue
    acc += 1
    rs = []
    for _ in range(25):
        v = {n: rnd.uniform(*box[n]) for n in box}
        rs += float_roots(lambda x, v=v: fn(v, x), -4, 4)
    for corner in range(1 << len(names)):
        v = {n: box[n][(corner >> j) & 1] for j, n in enumerate(names)}
        rs += float_roots(lambda x, v=v: fn(v, x), -4, 4)
    if res[1] is None:
        contain += not rs
        continue
    lo, hi = float(res[1][0]), float(res[1][1])
    contain += all(lo - 1e-12 <= r <= hi + 1e-12 for r in rs)
    if "corner" in res[2] and rs:
        tight_n += 1
        tight_ok += abs(lo - min(rs)) < 1e-9 and abs(hi - max(rs)) < 1e-9
check(f"random: {acc}/150 accepted (a non-unique shape may still be enclosed)", acc >= 100, acc)
check(f"random: every sampled root inside its accepted range ({contain}/{acc})", contain == acc)
check(f"random: tight ranges match the sampled extremes ({tight_ok}/{tight_n})",
      tight_n >= 40 and tight_ok == tight_n, (tight_ok, tight_n))

# ------------------------------------------------------------------ 4. two roots
print("4. two roots")
qs, g = law("p=[1,4] credit, q=? credit", "q*q - p")
cert, res = run(qs, g, "q", ["-3", "3"])
check("two roots: no 'unique' in the found certificate", res[0] and not cert.get("unique"), cert)
forged = dict(cert, unique=True)
check("two roots: a forged 'unique' refused", not ZI.check_implicit(g, "q", qs, forged)[0])
check("two roots: the enclosure holds both [-2,-1] and [1,2]",
      res[1][0] <= -2 and res[1][1] >= 2, res[1])

# ------------------------------------------------------------------ 5. forgeries
print("5. forgeries")
qs, g = law("pmax=[44.16,51.84] credit, Qmax=[0.038,0.042] credit, K=[27200,36800] credit, Q=? credit",
            "pmax*(1 - Q/Qmax) - K*Q*Q")
cert, _ = run(qs, g, "Q", ["0", "0.06"])


def refused(name, c, qq=qs):
    r = ZI.check_implicit(g, "Q", qq, c)
    check(f"refused: {name}", not r[0], r)


p = cert["pieces"]
refused("a 'none' piece over the root", dict(cert, pieces=[dict(x, kind="none") for x in p]))
refused("a gap", dict(cert, pieces=[p[0], dict(p[1], lo=str(F(p[1]["lo"]) + F(1, 10 ** 6)))] + p[2:]))
refused("an overlap", dict(cert, pieces=[p[0], dict(p[1], lo=str(F(p[1]["lo"]) - F(1, 10 ** 6)))] + p[2:]))
refused("the pieces stop short", dict(cert, pieces=p[:-1]))
refused("a wrong monotone sign", dict(cert, monotone=dict(cert["monotone"], K="+")))
c0 = cert["corners"][0]
refused("a corner bracket with no sign change",
        dict(cert, corners=[dict(c0, hi=c0["lo"], lo=str(F(c0["lo"]) - F(1, 10 ** 9)))] + cert["corners"][1:]))
wrong = dict(c0["at"], pmax=str(qs["pmax"]["hi"] if F(c0["at"]["pmax"]) == qs["pmax"]["lo"] else qs["pmax"]["lo"]))
refused("the wrong corner", dict(cert, corners=[dict(c0, at=wrong)]
                                  + cert["corners"][1:]))
qs_inf = dict(qs, K=dict(qs["K"], hi=float("inf")))
refused("an unbounded parameter", cert, qs_inf)
refused("unreadable", dict(cert, search=["x", "1"]))

# ------------------------------------------------------------------ 5b. min/max in the law
print("5b. a piecewise law (min): no derivative, the plain enclosure only (blind test 2, c11: it raised)")
qs_m, g_m = law("a=[1,2] credit, Q=? credit", "min(10 - Q, 20 - 3*Q) - a*Q")
cert_m = ZI.search_certificate(g_m, "Q", qs_m, ["0", "10"])
r_m = ZI.check_implicit(g_m, "Q", qs_m, cert_m)
check("min: the enclosure holds the true roots 10/3 (a = 2) .. 5 (a = 1)",
      r_m[0] and r_m[1][0] <= F(10, 3) and r_m[1][1] >= 5, r_m)
check("min: a forged 'unique' is refused, not raised", not ZI.check_implicit(g_m, "Q", qs_m, dict(cert_m, unique=True))[0])

# ------------------------------------------------------------------ 6. a lying kernel
print("6. mutation: a kernel whose readings collapse to the midpoint")
real = ZC._reading


def lying(e, qs_, piece):
    mid = {n: ((lo + hi) / 2, (lo + hi) / 2) for n, (lo, hi) in piece.items()}
    return real(e, qs_, mid)


forged = dict(cert, pieces=[{"lo": "0", "hi": "0.06", "kind": "none"}])
ZI._reading = lying
lied = ZI.check_implicit(g, "Q", qs, forged)
ZI._reading = lambda e, q_, pc: real(e, q_, pc)
check("the lying kernel passes the forged 'no root anywhere'", lied[0], lied)
check("the true kernel refuses it", not ZI.check_implicit(g, "Q", qs, forged)[0])

print(f"\n{ok} ok, {fail} fail")
print("IMPLICIT GREEN" if fail == 0 else "IMPLICIT RED")
sys.exit(1 if fail else 0)
