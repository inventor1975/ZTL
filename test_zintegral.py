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
# 1e-4, not tighter: sqrt's symbolic derivatives to order 6 are trees of nested roots, slow to read (MEASURED: 1e-6
# took 228 s to search, 66 s to check; Taylor coefficients along the graph would cut it — not yet)
c3 = ZI.search(f3, "x", 0, 1, qs3, F(1, 10 ** 4))
check("gave_up" not in c3 and c3["enclosure"][0] <= F(2, 3) <= c3["enclosure"][1]
      and c3["enclosure"][1] - c3["enclosure"][0] < F(1, 10 ** 4),
      f"2/3 inside [{float(c3['enclosure'][0]):.12g}, {float(c3['enclosure'][1]):.12g}], {len(c3['leaves'])} pieces")
bad = {"points": ["0/1", "1/1"], "leaves": [{"taylor": 2}]}
check(not ZI.check(f3, "x", 0, 1, qs3, bad)[0], "MUTATION: a Taylor leaf across 0 (f'' unbounded there) refused")

print("4. a parameter: x^p on [1/100, 1], p in [1, 3] — its range by pins")
f4, qs4 = setup("pow(x, p)", {"x": (F(1, 100), F(1)), "p": (F(1), F(3))})
c4 = ZI.search_range(f4, "x", F(1, 100), 1, qs4, F(1, 10 ** 9))
lo_true, hi_true = (1 - F(1, 100) ** 4) / 4, (1 - F(1, 100) ** 2) / 2
check("gave_up" not in c4 and c4["pins"] == {"p": "-"}
      and c4["range"][0] <= lo_true and hi_true <= c4["range"][1]
      and lo_true - c4["range"][0] < F(1, 10 ** 9) and c4["range"][1] - hi_true < F(1, 10 ** 9),
      f"the exact range [(1-1e-8)/4, (1-1e-4)/2] within 1e-9: {[float(v) for v in c4.get('range', (0, 0))]}")
m4 = dict(c4, pins={"p": "+"})
check(not ZI.check_range(f4, "x", F(1, 100), 1, qs4, m4)[0], "MUTATION: a pin with the wrong sign (p +) refused")

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
