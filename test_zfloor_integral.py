"""integral(f, x, a, b) and pi on the numeric floor (2026-10-20) — the judge reads a definite integral in a claim.

The value is zintegral's KERNEL-CHECKED enclosure (the search is untrusted, check() decides), for every value of f's
parameters and of the limits. Known answers: ∫_0^1 e^(-x²) = 0.7468241328..., ∫_0^pi sin = 2, ∫_1^2 1/x = ln 2,
∫_0^T k x dx = k T²/2. Mutations: a bound past the true value is refused; the bound variable may not shadow a row.
"""
import sys

from znumjudge import parse_quantities, judge_sheet_claim, _parse_arith

FAILS = []
COUNT = [0]


def check(cond, what):
    COUNT[0] += 1
    print(("  ok   " if cond else "  FAIL ") + what)
    if not cond:
        FAILS.append(what)


def disp(claim, qtext=""):
    qs = parse_quantities(qtext)[0] if qtext else {}
    return judge_sheet_claim(claim, qs, {})["disposition"]


print("1. fixed limits, no parameters")
check(disp("integral(exp(0 - x*x), x, 0, 1) > 0.7468") == "EARNED", "∫_0^1 e^(-x²) > 0.7468 EARNED")
check(disp("integral(exp(0 - x*x), x, 0, 1) > 0.7469") == "REFUTED", "∫_0^1 e^(-x²) > 0.7469 REFUTED (true 0.74682)")
check(disp("integral(1/x, x, 1, 2) < 0.6932") == "EARNED", "∫_1^2 1/x < 0.6932 EARNED (ln 2 = 0.693147)")
check(disp("integral(1/x, x, 1, 2) < 0.6931") == "REFUTED", "∫_1^2 1/x < 0.6931 REFUTED")
check(disp("integral(x, x, 2, 0) == -2") == "EARNED", "reversed limits: ∫_2^0 x = -2 EARNED")
check(disp("integral(x, x, 1, 1) == 0") == "EARNED", "an empty range: 0")

print("2. pi: a proved bracket")
check(disp("pi > 3.14159265") == "EARNED" and disp("pi < 3.14159266") == "EARNED", "3.14159265 < pi < 3.14159266")
check(disp("pi == 3.14159265") == "REFUTED", "pi is not 3.14159265")
check(disp("integral(sin(x), x, 0, pi) > 1.999999") == "EARNED", "∫_0^pi sin > 1.999999 EARNED")
check(disp("integral(sin(x), x, 0, pi) < 2.000001") == "EARNED", "∫_0^pi sin < 2.000001 EARNED")
check(disp("integral(sin(x), x, 0, pi) == 2") == "OPEN", "∫_0^pi sin == 2 OPEN: pi is a bracket, equality not forced")

print("3. parameters and moving limits, on credit")
q = "k=[1,2] credit, T=[1,1.5] credit"
check(disp("integral(k*x, x, 0, T) <= 3", q) == "ON CREDIT", "k T²/2 <= 2.25 <= 3: earned shape on credit inputs")
check(disp("integral(k*x, x, 0, T) <= 2", q) == "OPEN", "<= 2: true at some readings only — OPEN")
check(disp("integral(k*x, x, 0, T) <= 3", "k=[1,2] earned, T=[1,1.5] earned") == "EARNED", "the same on earned inputs")
check(disp("integral(k*x, x, 0, T) > 3", "k=[1,2] earned, T=[1,1.5] earned") == "REFUTED", "> 3 refuted")

print("4. the bound variable, and what is refused")
try:
    _parse_arith("integral(x, x, 0, 1)", parse_quantities("x=[0,1] credit")[0])
    check(False, "x shadowing a row should be refused")
except ValueError as e:
    check("already a quantity" in str(e), "the bound variable may not shadow a row of the sheet")
try:
    _parse_arith("integral(x, x, 0)", {})
    check(False, "three arguments should be refused")
except ValueError as e:
    check("4 arguments" in str(e), "integral takes four arguments")
try:
    _parse_arith("integral(integral(y, y, 0, x), x, 0, 1)", {})
    check(False, "a nested integral should be refused")
except ValueError as e:
    check("inside an integrand" in str(e), "an integral inside an integrand is refused (name it as its own row)")
check(disp("integral(1/x, x, 0 - 1, 1) > 0") == "OPEN", "1/x across 0: no certificate — the mark, never a guess")

print("5. units: f's unit times x's")
check(disp("integral(P, t, 0, T) <= 7200", "P=[100,200] earned W, T=[0,36] earned s") == "EARNED",
      "∫ P dt over 36 s at <= 200 W is <= 7200 W·s")
check(disp("integral(P, t, 0, T) <= E", "P=[100,200] earned W, T=[0,36] earned s, E=[7200,7200] earned W*s")
      == "EARNED", "against a quantity in W*s: EARNED")
check(disp("integral(P, t, 0, T) <= E", "P=[100,200] earned W, T=[0,36] earned m, E=[7200,7200] earned W*s")
      == "E", "W·m against W·s: E, the units never meet")

print()
if FAILS:
    print(f"ZFLOOR INTEGRAL RED: {len(FAILS)} of {COUNT[0]}")
    sys.exit(1)
print(f"ZFLOOR INTEGRAL GREEN: {COUNT[0]} checks")
