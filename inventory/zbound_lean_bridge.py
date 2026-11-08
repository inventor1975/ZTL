"""A REQUIREMENT OVER A BOX AS A LEAN THEOREM — the bound bridge (tools/zbound2lean.py), checked end to end.

The curator, 2026-11-08: the stand should give proofs, not only certificates. Here:
  * the stand's divider (examples/divider-1pct-req-1pct.json, R1 = R2 = 1 kOhm +-1 %): Vout in [2.475, 2.525] from
    its laws, for every real R1, R2 in the box — a THEOREM (met exactly at the corners: monotone leaves);
  * a requirement with a margin on a three-resistor network (R3 in series) — a THEOREM;
  * a law that is not linear in the unknowns — NOT TRANSLATED (said, not hidden);
  * not dyadic and met exactly at the corners (Vin = 3.3 V, 27 ohm +-1 %): EXACT through the integer box (x = 100·R),
    and 1/10000 past the attained end — no theorem;
  * a target that is an EXPRESSION of the unknowns (the power I*I*R1), attained inside a face — a theorem; past
    it — none;
  * a datum in both N and D (a TCR divider): the cleared form on one Horner polynomial, carried by `identX`;
  * a mortgage, pow(1 + r, 360) inside a division: a theorem on a 400 MB kernel stack; on 8 MB a "kernel limit";
  * NEGATIVE CONTROL: the divider's accepted tree under a false bound (Vout <= 2.5, the true maximum 2.525) — the
    kernel must refuse it.
"""
import os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT); sys.path.insert(0, os.path.join(ROOT, "tools"))
import zbound2lean as ZB  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


DIV = (["Vin - Vout == I*R1", "Vout == I*R2"], ["I", "Vout"],
       "Vin=5 credit, R1=[990,1010] credit, R2=[990,1010] credit, I=? credit, Vout=? credit")
print("1. the stand's divider")
st = ZB.bound_to_lean(*DIV, "Vout", [(">=", "2.475"), ("<=", "2.525")], "ZGenDivider")
check("Vout in [2.475, 2.525] for every R1, R2 in [990, 1010]: a theorem", st["status"] == "theorem", st)
print("2. a network with a margin")
st2 = ZB.bound_to_lean(["Vin - V1 == I*R1", "V1 - Vout == I*R3", "Vout == I*R2"], ["I", "V1", "Vout"],
                       "Vin=12 credit, R1=[1980,2020] credit, R2=[990,1010] credit, R3=[990,1010] credit, "
                       "I=? credit, V1=? credit, Vout=? credit", "Vout", [(">=", "2.9"), ("<=", "3.1")], "ZGenNet3")
check("three resistors: Vout in [2.9, 3.1]: a theorem", st2["status"] == "theorem", st2)
print("3. not linear in the unknowns")
st3 = ZB.bound_to_lean(["V == I*I*R"], ["I", "V"], "R=[1,2] credit, I=? credit, V=? credit", "V", [("<=", "1")], "ZGenNL")
check("V == I*I*R: not translated", st3["status"] == "not translated", st3)
print("4. negative control")
if st.get("trees"):
    bad = ZB.bound_to_lean(*DIV, "Vout", [(">=", "2.475"), ("<=", "2.5")], "ZGenDividerBad", trees=st["trees"])
    check("the accepted tree under Vout <= 2.5 (the maximum is 2.525): the kernel refuses", bad["status"] == "refused", bad)
else:
    check("negative control ran", False, "no trees")
print("5. not dyadic, met exactly at the corners (ztl-stand power-16thW-or-quarterW: 27 ohm +-1 % read `no tree`)")
TIGHT = (["Vin - Vout == I*R1", "Vout == I*R2"], ["I", "Vout"],
         "Vin=3.3 credit, R1=[26.73,27.27] credit, R2=[26.73,27.27] credit, I=? credit, Vout=? credit")
st5 = ZB.bound_to_lean(*TIGHT, "Vout", [(">=", "1.6335"), ("<=", "1.6665")], "ZGenTight")
check("Vin = 3.3, R = 27 +-1 %: Vout in [1.6335, 1.6665] (both ends attained) — a theorem, exact integer box",
      st5["status"] == "theorem" and st5.get("scale") == {"R1": 100, "R2": 100}, st5)
st6 = ZB.bound_to_lean(*TIGHT, "Vout", [("<=", "1.6664")], "ZGenTightBad")
check("the other side: Vout <= 1.6664 (below the attained 1.6665) — no theorem", st6["status"] != "theorem", st6)
print("6. a target that is an EXPRESSION of the unknowns: the power P1 = I*I*R1 (ztl-stand power-16thW-or-quarterW)")
PW = (["Vin - Vout == I*R1", "Vout == I*R2"], ["I", "Vout"],
      "Vin=5 credit, R1=[26.73,27.27] credit, R2=[26.73,27.27] credit, I=? credit, Vout=? credit")
# max of 25·R1/(R1+R2)^2 over the box: 625/2673, on the diagonal R1 = R2 = 26.73 (the slope in R1 changes sign there)
st7 = ZB.bound_to_lean(*PW, "I*I*R1", [("<=", "625/2673")], "ZGenPow")
check("P1 = I*I*R1 <= 625/2673 (attained, not monotone in R1): a theorem", st7["status"] == "theorem", st7)
st8 = ZB.bound_to_lean(*PW, "I*I*R1", [("<=", "624/2673")], "ZGenPowBad")
check("the other side: P1 <= 624/2673 — no theorem", st8["status"] != "theorem", st8)
print("7. a datum in BOTH N and D (ztl-stand tasks/t5: a divider with temperature coefficients, 5 variables)")
TCR = (["Vin - Vout == I*(R1*(1 + a1*(T - 25)))", "Vout == I*(R2*(1 + a2*(T - 25)))"], ["I", "Vout"],
       "Vin=5 credit, T=[0,85] credit, R1=[9900,10100] credit, a1=[-1/40000,1/40000] credit, "
       "R2=[9900,10100] credit, a2=[-1/40000,1/40000] credit, I=? credit, Vout=? credit")
st9 = ZB.bound_to_lean(*TCR, "Vout", [(">=", "2.47"), ("<=", "2.53")], "ZGenTCR")
check("Vout in [2.47, 2.53] over R, a, T: a theorem — the cleared form proved on ONE Horner polynomial, moved by "
      "the kernel's identity test (identX)", st9["status"] == "theorem", st9)
st10 = ZB.bound_to_lean(*TCR, "Vout", [(">=", "2.472")], "ZGenTCRBad")
check("the other side: Vout >= 2.472 (the attained minimum 988515/400006 ~ 2.47125) — no theorem",
      st10["status"] != "theorem", st10)
print("8. a mortgage: pow(1 + r, 360) inside a division (ztl-stand tasks/t14 overflowed the kernel's stack)")
ML = (["S == Inc"], ["S"], "Inc=[5200,5800] credit, P=[275000,290000] credit, c=7/1500 credit, S=? credit")
MT = "35/100*Inc - P*(min(c, 1/12)*pow(1 + min(c, 1/12), 360))/(pow(1 + min(c, 1/12), 360) - 1)"
st11 = ZB.bound_to_lean(*ML, MT, [(">=", "0")], "ZGenMort")
check("slack = 35 % of income − the payment >= 0 (min ~155.17): a theorem (the kernel on a 400 MB stack)",
      st11["status"] == "theorem", st11)
st12 = ZB.bound_to_lean(*ML, MT.replace("min(c, 1/12)", "c"), [(">=", "160")], "ZGenMortBad")
check("the other side: slack >= 160 — no theorem", st12["status"] != "theorem", st12)
_ts, ZB.TSTACK_KB = ZB.TSTACK_KB, 8000
try:
    st13 = ZB.bound_to_lean(*ML, MT, [(">=", "0")], "ZGenMort8")
finally:
    ZB.TSTACK_KB = _ts
check("on the default 8 MB stack the same check is a KERNEL LIMIT, said as such — never reported as refused",
      st13["status"] == "kernel limit", st13)
print(f"\n{ok} ok, {fail} fail")
print("ZBOUND LEAN BRIDGE GREEN" if fail == 0 else "ZBOUND LEAN BRIDGE RED")
sys.exit(1 if fail else 0)
