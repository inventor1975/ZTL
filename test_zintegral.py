"""zintegral — a definite integral enclosed by a certificate the kernel checks (2026-10-16).

Known answers: ∫_0^1 e^(-x²) dx = 0.746824132812427025..., ∫_0^1 sin x dx = 1 - cos 1, ∫_0^1 sqrt(x) dx = 2/3 (a
derivative unbounded at 0), ∫_a^1 x^p dx = (1 - a^(p+1))/(p+1) over a box of p (a parameter's range by pins).
Mutations: every wrong certificate is refused by the kernel's own readings.
"""
import sys
from fractions import Fraction as F

import zintegral as ZI
from znumjudge import _parse_arith, parse_quantities

FAILS = []
COUNT = [0]


def check(cond, what):
    COUNT[0] += 1
    print(("  ok   " if cond else "  FAIL ") + what)
    if not cond:
        FAILS.append(what)


def fs(x):
    return f"{x.numerator}/{x.denominator}"


def setup(t, boxes):
    qs = parse_quantities(", ".join(f"{n}=[{fs(a)},{fs(b)}] credit" for n, (a, b) in boxes.items()))[0]
    return _parse_arith(t, qs), qs


TRUE_GAUSS = F("0.7468241328124270253994674361318530053544996868126063290276544989586053")
TRUE_SIN = F("0.459697694131860282599063392557023396267689579382077772329903")   # 1 - cos 1

print("1. e^(-x^2) on [0, 1] to 1e-12")
f, qs = setup("exp(0 - x*x)", {"x": (F(0), F(1))})
c = ZI.search(f, "x", 0, 1, qs, F(1, 10 ** 12))
L, U = c["enclosure"]
check("gave_up" not in c and L <= TRUE_GAUSS <= U and U - L < F(1, 10 ** 12),
      f"proved in [{float(L):.16g}, {float(U):.16g}] ({len(c['leaves'])} pieces), the true value inside, < 1e-12 wide")
cert = {k: c[k] for k in ("points", "leaves")}
check(ZI.proves(f, "x", 0, 1, qs, ">=", F("0.746824132812"), cert)[0]
      and not ZI.proves(f, "x", 0, 1, qs, ">=", F("0.7468241328125"), cert)[0],
      ">= 0.746824132812 proved; >= 0.7468241328125 (above the true value) refused")

print("2. sin x on [0, 1]")
f2, qs2 = setup("sin(x)", {"x": (F(0), F(1))})
c2 = ZI.search(f2, "x", 0, 1, qs2, F(1, 10 ** 12))
check("gave_up" not in c2 and c2["enclosure"][0] <= TRUE_SIN <= c2["enclosure"][1],
      f"1 - cos 1 inside [{float(c2['enclosure'][0]):.16g}, {float(c2['enclosure'][1]):.16g}]")

print("3. sqrt(x) on [0, 1]: f' unbounded at 0 — Taylor leaves refused there, interval/monotone ones carry it")
f3, qs3 = setup("sqrt(x)", {"x": (F(0), F(1))})
# 1e-6: with Taylor coefficients ALONG THE GRAPH 1.1 s (the symbolic derivatives of sqrt to order 6: 228 s, MEASURED)
c3 = ZI.search(f3, "x", 0, 1, qs3, F(1, 10 ** 6))
check("gave_up" not in c3 and c3["enclosure"][0] <= F(2, 3) <= c3["enclosure"][1]
      and c3["enclosure"][1] - c3["enclosure"][0] < F(1, 10 ** 6),
      f"2/3 inside [{float(c3['enclosure'][0]):.12g}, {float(c3['enclosure'][1]):.12g}], {len(c3['leaves'])} pieces")
bad = {"points": ["0/1", "1/1"], "leaves": [{"taylor": 2}]}
check(not ZI.check(f3, "x", 0, 1, qs3, bad)[0], "MUTATION: a Taylor leaf across 0 (f'' unbounded there) refused")

print("4. a parameter: x^p on [1/100, 1], p in [1, 3] — its range by pins")
f4, qs4 = setup("pow(x, p)", {"x": (F(1, 100), F(1)), "p": (F(1), F(3))})
ZI.RULE_PREMISE.clear()
c4 = ZI.search_range(f4, "x", F(1, 100), 1, qs4, F(1, 10 ** 9))
check(not ZI.RULE_PREMISE, f"the pin's sign reached by Lean (lean/ZRangePin, zmonocert along p): premises {ZI.RULE_PREMISE}")
import zmonocert as _ZM
_keep = _ZM.sign_covered
_ZM.sign_covered = lambda *a: "a sign Lean does not reach"
try:
    _g = ZI.check_range(f4, "x", F(1, 100), 1, qs4, c4)
finally:
    _ZM.sign_covered = _keep
check(_g[0] and ZI.RULE_PREMISE.get("range pin: a sign Lean does not reach") == 1,
      f"a pin Lean does not reach is counted, not silent: {ZI.RULE_PREMISE}")
lo_true, hi_true = (1 - F(1, 100) ** 4) / 4, (1 - F(1, 100) ** 2) / 2
check("gave_up" not in c4 and c4["pins"] == {"p": "-"}
      and c4["range"][0] <= lo_true and hi_true <= c4["range"][1]
      and lo_true - c4["range"][0] < F(1, 10 ** 9) and c4["range"][1] - hi_true < F(1, 10 ** 9),
      f"the exact range [(1-1e-8)/4, (1-1e-4)/2] within 1e-9: {[float(v) for v in c4.get('range', (0, 0))]}")
m4 = dict(c4, pins={"p": "+"})
check(not ZI.check_range(f4, "x", F(1, 100), 1, qs4, m4)[0], "MUTATION: a pin with the wrong sign (p +) refused")

print("4b. Taylor coefficients along the graph: f^(k)(x)/k! at a point, k = 0..6, against high-precision derivatives")
import mpmath
import zcertify as ZC
mpmath.mp.dps = 40
_bad, _n = 0, 0
for t, mf in (("exp(0 - x*x)", lambda z: mpmath.exp(-z * z)), ("sqrt(x)", mpmath.sqrt),
              ("sin(x)*ln(x + 1)", lambda z: mpmath.sin(z) * mpmath.log(z + 1)),
              ("pow(x, 3/2)/(1 + x*x)", lambda z: z ** 1.5 / (1 + z * z)), ("atan(x*x)", lambda z: mpmath.atan(z * z)),
              ("tan(x/2)", lambda z: mpmath.tan(z / 2)), ("pow(x + 1, x)", lambda z: (z + 1) ** z)):
    eg, qg = setup(t, {"x": (F(0), F(1))})
    for pt in (F(1, 5), F(1, 2), F(7, 8)):
        cg = ZC.taylor_coeffs(eg, "x", qg, {"x": (pt, pt)}, 6)
        for k in range(7):
            _n += 1
            tv = mpmath.diff(mf, mpmath.mpf(pt.numerator) / pt.denominator, k) / mpmath.factorial(k)
            lo_, hi_ = (mpmath.mpf(v.numerator) / v.denominator for v in cg[k]) if cg else (1, 0)
            _bad += not (lo_ - mpmath.mpf(10) ** -18 <= tv <= hi_ + mpmath.mpf(10) ** -18)
check(_bad == 0 and _n == 147,
      f"Taylor coefficients along the graph hold the true f^(k)/k! (7 functions x 3 points x orders 0..6): {_bad} of {_n} outside")

print("4c. limits that move: ∫_0^T e^(-k x) dx, T in [1, 2], k in [1/2, 1] — the exact range by pins")
import math as _m
qsl = parse_quantities(", ".join(f"{n}=[{fs(a)},{fs(b)}] credit" for n, (a, b) in
                                  {"x": (F(0), F(3)), "T": (F(1), F(2)), "k": (F(1, 2), F(1))}.items()))[0]
fl, Bl = _parse_arith("exp(0 - k*x)", qsl), _parse_arith("T", qsl)
ZI.RULE_PREMISE.clear()
cl = ZI.search_limits_range(fl, "x", F(0), Bl, qsl, F(1, 10 ** 9))
check(not ZI.RULE_PREMISE and not ZI.VALUE_PREMISE,
      f"pins k and T (T moves the limit) reached by Lean (lean/ZLeibniz, zleibcert): premises {ZI.RULE_PREMISE}")
import zleibcert as _ZLB
_box = ZI._limits_box(qsl, {"T", "k"})
_ra, _rb = (F(0), F(0)), ZC._reading(Bl, qsl, _box)
check("t_j" in _ZLB.leibniz_covered(fl, "x", F(0), Bl, qsl, _box, _ra, _rb, {"k": "+", "T": "+"}),
      "MUTATION: the pin on k with the wrong sign fails Lean's t_j (the kernel refuses it too)")
_keepL = _ZLB.leibniz_covered
_ZLB.leibniz_covered = lambda *a: "a t_j Lean does not reach"
ZI.RULE_PREMISE.clear()
try:
    _gl = ZI.check_limits_range(fl, "x", F(0), Bl, qsl, cl)
finally:
    _ZLB.leibniz_covered = _keepL
check(_gl[0] and ZI.RULE_PREMISE == {"dI/dp with moving limits: a t_j Lean does not reach": 1},
      f"a Leibniz pin Lean does not reach is counted, not silent: {ZI.RULE_PREMISE}")
true_lo, true_hi = 1 - _m.exp(-1), (1 - _m.exp(-1)) / F(1, 2)
check("gave_up" not in cl and cl["pins"] == {"k": "-", "T": "+"}
      and abs(float(cl["range"][0]) - true_lo) < 1e-9 and abs(float(cl["range"][1]) - float(true_hi)) < 1e-9,
      f"pins k (-) and T (+); the range [1 - 1/e, 2(1 - 1/e)] within 1e-9: {[float(v) for v in cl.get('range', (0, 0))]}")
cm = dict(cl, pins={"k": "+", "T": "+"})
check(not ZI.check_limits_range(fl, "x", F(0), Bl, qsl, cm)[0], "MUTATION: a limit pin with the wrong sign (k +) refused")
cw = ZI.check_limits(fl, "x", F(0), Bl, qsl, {"core": cl["high"]["core"]})
check(not cw[0], "MUTATION: the high corner's core ([0, 2]) refused for the whole box (its core is [0, 1])")
ZI.RULE_PREMISE.clear()
ct = ZI.search_limits(fl, "x", F(0), Bl, qsl, F(1, 10 ** 6))
check("gave_up" not in ct and not ZI.RULE_PREMISE and not ZI.VALUE_PREMISE,
      f"the whole box (T moving): an enclosure through the tail rule (lean/ZLimits), premises {ZI.RULE_PREMISE}")

print("4d. a double integral over [0,1]^2: e^(-x^2-y^2) = (∫_0^1 e^(-x^2))^2 — a certificate inside a certificate")
qs2d = parse_quantities("x=[0/1,1/1] credit, y=[0/1,1/1] credit")[0]
f2d = _parse_arith("exp(0 - x*x - y*y)", qs2d)
c2d = ZI.search2(f2d, "x", 0, 1, "y", 0, 1, qs2d, F(1, 10 ** 6))
check("gave_up" not in c2d and c2d["enclosure"][0] <= TRUE_GAUSS ** 2 <= c2d["enclosure"][1]
      and c2d["enclosure"][1] - c2d["enclosure"][0] < F(1, 10 ** 6),
      f"(∫e^(-x²))² inside [{float(c2d['enclosure'][0]):.12g}, {float(c2d['enclosure'][1]):.12g}], "
      f"{len(c2d.get('leaves', []))} outer pieces")
m2d = {"points": c2d["points"], "leaves": [dict(c2d["leaves"][0], inner=c2d["leaves"][0]["inner"][:-1])]
       + c2d["leaves"][1:]}
check(not ZI.check2(f2d, "x", 0, 1, "y", 0, 1, qs2d, m2d)[0],
      "MUTATION: an outer Taylor leaf missing its remainder's inner certificate refused")
_in0 = c2d["leaves"][0]["inner"][0]
_short = {"points": _in0["points"][:-1], "leaves": _in0["leaves"][:-1]}
m2e = {"points": c2d["points"], "leaves": [dict(c2d["leaves"][0], inner=[_short] + c2d["leaves"][0]["inner"][1:])]
       + c2d["leaves"][1:]}
check(not ZI.check2(f2d, "x", 0, 1, "y", 0, 1, qs2d, m2e)[0],
      "MUTATION: an inner partition stopping short of y = 1 refused")
# (two outer pieces merged under one piece's inner certificates is NOT wrong: the kernel re-reads every enclosure for
#  the merged piece — sound, only wider; the certificate carries partitions and leaf kinds, never the numbers)

print("5. the partition itself")
pts = c["points"]
lv = c["leaves"]
check(not ZI.check(f, "x", 0, 1, qs, {"points": pts[:-1], "leaves": lv[:-1]})[0], "MUTATION: a partition short of b refused")
check(not ZI.check(f, "x", 0, 1, qs, {"points": [pts[0], pts[2], pts[1]] + pts[3:], "leaves": lv})[0],
      "MUTATION: a partition out of order refused")
check(not ZI.check(f, "x", 0, 1, qs, {"points": pts, "leaves": lv[:-1]})[0], "MUTATION: a leaf missing refused")
check(not ZI.check(f, "x", 0, 1, qs, {"points": ["0/1", "1/1"], "leaves": [{"monotone": "+"}]})[0],
      "MUTATION: a monotone leaf with the wrong sign (e^(-x^2) decreasing on [0, 1]) refused")
check(not ZI.check(f, "x", 0, 1, qs, {"points": ["0/1", "1/1"], "leaves": [{"taylor": 3}]})[0],
      "MUTATION: an odd Taylor order refused")

if FAILS:
    print(f"ZINTEGRAL RED: {len(FAILS)} of {COUNT[0]} checks fail")
    sys.exit(1)
print(f"ZINTEGRAL GREEN ({COUNT[0]} checks)")
