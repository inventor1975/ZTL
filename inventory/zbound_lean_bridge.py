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
  * no laws at all (a pinned zero before a table), and a 7-unknown ladder by Bareiss (Cramer refuses > 6);
  * a square root, as exp(½·ln u);
  * ON THE LAWS: the theorem for every value of the unknowns satisfying the laws (rows + a cofactor certificate
    checked by the kernel); a certificate off by one is refused;
  * a table (nested ifpos in one variable) read exactly as hinges p0 + sum max(t - t_j, 0)·q_j;
  * NEGATIVE CONTROL: the divider's accepted tree under a false bound (Vout <= 2.5, the true maximum 2.525) — the
    kernel must refuse it.
"""
import os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT); sys.path.insert(0, os.path.join(ROOT, "tools"))
import zbound2lean as ZB  # noqa: E402

DIV = (["Vin - Vout == I*R1", "Vout == I*R2"], ["I", "Vout"],
       "Vin=5 credit, R1=[990,1010] credit, R2=[990,1010] credit, I=? credit, Vout=? credit")
TIGHT = (["Vin - Vout == I*R1", "Vout == I*R2"], ["I", "Vout"],
         "Vin=3.3 credit, R1=[26.73,27.27] credit, R2=[26.73,27.27] credit, I=? credit, Vout=? credit")
PW = (["Vin - Vout == I*R1", "Vout == I*R2"], ["I", "Vout"],
      "Vin=5 credit, R1=[26.73,27.27] credit, R2=[26.73,27.27] credit, I=? credit, Vout=? credit")
TCR = (["Vin - Vout == I*(R1*(1 + a1*(T - 25)))", "Vout == I*(R2*(1 + a2*(T - 25)))"], ["I", "Vout"],
       "Vin=5 credit, T=[0,85] credit, R1=[9900,10100] credit, a1=[-1/40000,1/40000] credit, "
       "R2=[9900,10100] credit, a2=[-1/40000,1/40000] credit, I=? credit, Vout=? credit")
ML = (["S == Inc"], ["S"], "Inc=[5200,5800] credit, P=[275000,290000] credit, c=7/1500 credit, S=? credit")
MT = "35/100*Inc - P*(min(c, 1/12)*pow(1 + min(c, 1/12), 360))/(pow(1 + min(c, 1/12), 360) - 1)"
LAD = (["Vin - V1 == I*R1", "V1 - V2 == I*R2", "V2 - V3 == I*R3", "V3 - V4 == I*R4", "V4 - V5 == I*R5",
        "V5 - V6 == I*R6", "V6 == I*R7"], ["I", "V1", "V2", "V3", "V4", "V5", "V6"],
       "Vin=7 credit, R1=[990,1010] credit, R2=1000 credit, R3=1000 credit, R4=1000 credit, R5=1000 credit, "
       "R6=1000 credit, R7=[990,1010] credit, I=? credit, V1=? credit, V2=? credit, V3=? credit, V4=? credit, "
       "V5=? credit, V6=? credit")
TB = ("ifpos(T - 100, ifpos(T - 200, ifpos(T - 400, ifpos(T - 600, 58/100, 68/100 + (58/100 - 68/100)*(T - 400)/(600 - 400)), "
      "82/100 + (68/100 - 82/100)*(T - 200)/(400 - 200)), 1 + (82/100 - 1)*(T - 100)/(200 - 100)), 1)")

# the independent cases in PARALLEL (the curator 2026-11-09: "он на одном ядре считает?" — it did: ~30 lean
# processes one after another, 45 s); each is its own `lean` process. The cases that switch a global (the 8 MB
# stack, the sabotaged certificate) pass it per call (thread-local); the one that reuses a tree runs after the pool.
from concurrent.futures import ProcessPoolExecutor  # noqa: E402 — PROCESSES: zimplicit is not thread-safe
# (2026-11-09 MEASURED: with threads sin/tan read 'no verdict' at random — 4 fails, then 2; a shared mutable state)
with ProcessPoolExecutor(max_workers=max(2, min(16, (os.cpu_count() or 4) // 2))) as pool:
    _F = {
    "ZGenDivider": pool.submit(ZB.bound_to_lean, *DIV, "Vout", [(">=", "2.475"), ("<=", "2.525")], "ZGenDivider"),
    "ZGenNet3": pool.submit(ZB.bound_to_lean, ["Vin - V1 == I*R1", "V1 - Vout == I*R3", "Vout == I*R2"], ["I", "V1", "Vout"],
                       "Vin=12 credit, R1=[1980,2020] credit, R2=[990,1010] credit, R3=[990,1010] credit, "
                       "I=? credit, V1=? credit, Vout=? credit", "Vout", [(">=", "2.9"), ("<=", "3.1")], "ZGenNet3"),
    "ZGenNL": pool.submit(ZB.bound_to_lean, ["V == I*I*R"], ["I", "V"], "R=[1,2] credit, I=? credit, V=? credit", "V", [("<=", "1")], "ZGenNL"),
    "ZGenTight": pool.submit(ZB.bound_to_lean, *TIGHT, "Vout", [(">=", "1.6335"), ("<=", "1.6665")], "ZGenTight"),
    "ZGenTightBad": pool.submit(ZB.bound_to_lean, *TIGHT, "Vout", [("<=", "1.6664")], "ZGenTightBad"),
    "ZGenPow": pool.submit(ZB.bound_to_lean, *PW, "I*I*R1", [("<=", "625/2673")], "ZGenPow"),
    "ZGenPowBad": pool.submit(ZB.bound_to_lean, *PW, "I*I*R1", [("<=", "624/2673")], "ZGenPowBad"),
    "ZGenTCR": pool.submit(ZB.bound_to_lean, *TCR, "Vout", [(">=", "2.47"), ("<=", "2.53")], "ZGenTCR"),
    "ZGenTCRBad": pool.submit(ZB.bound_to_lean, *TCR, "Vout", [(">=", "2.472")], "ZGenTCRBad"),
    "ZGenMort": pool.submit(ZB.bound_to_lean, *ML, MT, [(">=", "0")], "ZGenMort"),
    "ZGenMortBad": pool.submit(ZB.bound_to_lean, *ML, MT.replace("min(c, 1/12)", "c"), [(">=", "160")], "ZGenMortBad"),
    "ZGenNoLaws": pool.submit(ZB.bound_to_lean, [], [], "P=0 credit, OD=[0.0125,0.0128] credit, w=[0.0015,0.0018] credit",
                        "w - P*OD/(2*w)", [(">=", "0.0015")], "ZGenNoLaws"),
    "ZGenLadder": pool.submit(ZB.bound_to_lean, *LAD, "V6", [(">=", "0.99"), ("<=", "1.01")], "ZGenLadder"),
    "ZGenLadderBad": pool.submit(ZB.bound_to_lean, *LAD, "V6", [("<=", "1.009")], "ZGenLadderBad"),
    "ZGenSqrt": pool.submit(ZB.bound_to_lean, [], [], "s=[90,110] credit, t=[30,40] credit", "sqrt(s*s + 3*t*t)", [("<=", "131")], "ZGenSqrt"),
    "ZGenSqrtB": pool.submit(ZB.bound_to_lean, [], [], "s=[90,110] credit, t=[30,40] credit", "sqrt(s*s + 3*t*t)", [("<=", "129")], "ZGenSqrtB"),
    "ZGenTwoUnk": pool.submit(ZB.bound_to_lean, *PW, "Vout*Vout + I", [("<=", "6.47")], "ZGenTwoUnk"),
    "ZGenTwoUnkB": pool.submit(ZB.bound_to_lean, *PW, "Vout*Vout + I", [("<=", "6.46")], "ZGenTwoUnkB"),
    "ZGenTable": pool.submit(ZB.bound_to_lean, [], [], "T=[150,450] credit, S=[100,110] credit", f"S*{TB}", [(">=", "65.2")], "ZGenTable"),
    "ZGenTableB": pool.submit(ZB.bound_to_lean, [], [], "T=[150,450] credit, S=[100,110] credit", f"S*{TB}", [(">=", "65.6")], "ZGenTableB"),
    }
    _F["ZGenMort8"] = pool.submit(ZB.bound_to_lean, *ML, MT, [(">=", "0")], "ZGenMort8", tstack_kb=8000)
    _F["ZGenDividerMut"] = pool.submit(ZB.bound_to_lean, *DIV, "Vout", [(">=", "2.475"), ("<=", "2.525")],
                                       "ZGenDividerMut", mutant={"cert": True})
    _F["ZGenNoDomain"] = pool.submit(ZB.bound_to_lean, ["T == g + ln(100)/(mu - lam/2)"], ["T"],
                                     "g=[0.005,0.012] credit, mu=[198,242] credit, lam=[1620,1980] credit, T=? credit",
                                     "T", [("<=", "0.15")], "ZGenNoDomain")
    _F["ZGenBlock"] = pool.submit(ZB.bound_to_lean, ["F1 == k*x", "F2 == G*d*d*d*d/(8*D*D*D*n)*y"], ["F1", "F2"],
                                  "k=[9,11] credit, x=[1,2] credit, G=[78,80] credit, d=[3,4] credit, D=[20,30] credit, "
                                  "n=[5,7] credit, y=[1,2] credit, F1=? credit, F2=? credit", "F1", [("<=", "22")],
                                  "ZGenBlock")
    _F["ZGenIfConst"] = pool.submit(ZB.bound_to_lean, [], [], "e=5 credit, x=[1,2] credit",
                                    "x*ifpos(e - 3, 2, 100)", [("<=", "4")], "ZGenIfConst")
    _FQ = "pmax=[44.16,51.84] credit, Qmax=[0.038,0.042] credit, K=[27200,36800] credit"
    _F["ZImplFan"] = pool.submit(ZB.implicit_bound_to_lean, [], [], _FQ, "Q", "Q", "pmax*(1 - Q/Qmax) - K*Q*Q",
                                 ["0", "0.06"], [(">=", "0.02"), ("<=", "0.03")], "ZImplFan")
    _F["ZImplFanB"] = pool.submit(ZB.implicit_bound_to_lean, [], [], _FQ, "Q", "Q", "pmax*(1 - Q/Qmax) - K*Q*Q",
                                  ["0", "0.06"], [("<=", "0.022")], "ZImplFanB")
    _F["ZImplSide"] = pool.submit(ZB.implicit_bound_to_lean, [], [], _FQ, "Q", "Q", "pmax*(1 - Q/Qmax) - K*Q*Q",
                                  ["0", "0.06"], [(">=", "0.0222"), ("<=", "0.0266")], "ZImplSide")
    _F["ZImplSideB"] = pool.submit(ZB.implicit_bound_to_lean, [], [], _FQ, "Q", "Q", "pmax*(1 - Q/Qmax) - K*Q*Q",
                                   ["0", "0.06"], [(">=", "0.023")], "ZImplSideB")
    # the laws in the order Hb, Ha — the unknowns sorted Ha, Hb: a permuted matrix, Cramer's det = −1 (real4/k06)
    _F["ZGenNegDet"] = pool.submit(ZB.bound_to_lean, ["Hb == a + b", "Ha == c*c/(2*g)"], ["Ha", "Hb"],
                                   "a=[1,2] credit, b=[3,4] credit, c=[1,2] credit, g=9.81 credit, Ha=? credit, Hb=? credit",
                                   "pow(Ha + Hb, 1.5)", [("<=", "20")], "ZGenNegDet")
    R = {k: f.result() for k, f in _F.items()}

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


print("1. the stand's divider")
st = R["ZGenDivider"]
check("Vout in [2.475, 2.525] for every R1, R2 in [990, 1010]: a theorem", st["status"] == "theorem", st)
print("2. a network with a margin")
st2 = R["ZGenNet3"]
check("three resistors: Vout in [2.9, 3.1]: a theorem", st2["status"] == "theorem", st2)
print("3. not linear in the unknowns")
st3 = R["ZGenNL"]
check("V == I*I*R: not translated", st3["status"] == "not translated", st3)
print("4. negative control")
if st.get("trees"):
    bad = ZB.bound_to_lean(*DIV, "Vout", [(">=", "2.475"), ("<=", "2.5")], "ZGenDividerBad", trees=st["trees"])
    check("the accepted tree under Vout <= 2.5 (the maximum is 2.525): the kernel refuses", bad["status"] == "refused", bad)
else:
    check("negative control ran", False, "no trees")
print("5. not dyadic, met exactly at the corners (ztl-stand power-16thW-or-quarterW: 27 ohm +-1 % read `no tree`)")
st5 = R["ZGenTight"]
check("Vin = 3.3, R = 27 +-1 %: Vout in [1.6335, 1.6665] (both ends attained) — a theorem, exact integer box",
      st5["status"] == "theorem" and st5.get("scale") == {"R1": 100, "R2": 100}, st5)
st6 = R["ZGenTightBad"]
check("the other side: Vout <= 1.6664 (below the attained 1.6665) — no theorem", st6["status"] != "theorem", st6)
print("6. a target that is an EXPRESSION of the unknowns: the power P1 = I*I*R1 (ztl-stand power-16thW-or-quarterW)")
# max of 25·R1/(R1+R2)^2 over the box: 625/2673, on the diagonal R1 = R2 = 26.73 (the slope in R1 changes sign there)
st7 = R["ZGenPow"]
check("P1 = I*I*R1 <= 625/2673 (attained, not monotone in R1): a theorem", st7["status"] == "theorem", st7)
st8 = R["ZGenPowBad"]
check("the other side: P1 <= 624/2673 — no theorem", st8["status"] != "theorem", st8)
print("7. a datum in BOTH N and D (ztl-stand tasks/t5: a divider with temperature coefficients, 5 variables)")
st9 = R["ZGenTCR"]
check("Vout in [2.47, 2.53] over R, a, T: a theorem — the cleared form proved on ONE Horner polynomial, moved by "
      "the kernel's identity test (identX)", st9["status"] == "theorem", st9)
st10 = R["ZGenTCRBad"]
check("the other side: Vout >= 2.472 (the attained minimum 988515/400006 ~ 2.47125) — no theorem",
      st10["status"] != "theorem", st10)
print("8. a mortgage: pow(1 + r, 360) inside a division (ztl-stand tasks/t14 overflowed the kernel's stack)")
st11 = R["ZGenMort"]
check("slack = 35 % of income − the payment >= 0 (min ~155.17): a theorem (the kernel on a 400 MB stack)",
      st11["status"] == "theorem", st11)
st12 = R["ZGenMortBad"]
check("the other side: slack >= 160 — no theorem", st12["status"] != "theorem", st12)
st13 = R["ZGenMort8"]
check("on the default 8 MB stack the same check is a KERNEL LIMIT, said as such — never reported as refused",
      st13["status"] == "kernel limit", st13)
print("9. no unknowns, and MORE than 6 (ztl-stand real3/s07; the trusses t6/t7 and real4/k05 — Cramer's n! refused)")
st14 = R["ZGenNoLaws"]
check("no laws, P = 0 pinned: w - P*OD/(2w) >= 0.0015 — a theorem (0/u = 0 read exactly)", st14["status"] == "theorem",
      st14)
# V6 = 7·R7/(R1 + 5000 + R7): the extremes at the corners, 7·990/7000 = 0.99 and 7·1010/7000 = 1.01
st15 = R["ZGenLadder"]
check("a 7-unknown ladder: V6 in [0.99, 1.01] (both attained) — a theorem, BAREISS (Cramer refuses > 6)",
      st15["status"] == "theorem", st15)
st16 = R["ZGenLadderBad"]
check("the other side: V6 <= 1.009 — no theorem", st16["status"] != "theorem", st16)
print("10. a square root (ztl-stand real2/s02: the reduced stress sqrt(s^2 + 3 t^2))")
st17 = R["ZGenSqrt"]
check("sqrt(s^2 + 3 t^2) <= 131 on s in [90, 110], t in [30, 40] (max sqrt(16900) = 130): a theorem",
      st17["status"] == "theorem", st17)
st18 = R["ZGenSqrtB"]
check("the other side: <= 129 — no theorem", st18["status"] != "theorem", st18)
print("11. ON THE LAWS (the curator 2026-11-09, B/C): the requirement for EVERY value of the unknowns satisfying them")
check("the divider, the 3-resistor net, the TCR divider, the 7-unknown ladder: each theorem is on the LAWS (rows + a "
      "cofactor certificate checked by identX), not on an eliminated expression",
      all(x.get("about") == "laws" for x in (st, st2, st9, st15)), [x.get("about") for x in (st, st2, st9, st15)])
check("an expression target (the power I*I*R1, not monotone, attained) is ALSO on the laws: D·I = N from the "
      "certificate, the telescoping identity checked, D² > 0", st7.get("about") == "laws" and st7["status"] == "theorem",
      st7.get("about"))
st19 = R["ZGenTwoUnk"]
check("an expression of TWO unknowns, Vout² + I <= 6.47 (max ~6.4682 at a corner), on the laws: a theorem",
      st19["status"] == "theorem" and st19.get("about") == "laws", st19)
st20 = R["ZGenTwoUnkB"]
check("the other side: Vout² + I <= 6.46 — no theorem", st20["status"] != "theorem", st20)
stm = R["ZGenDividerMut"]
check("SABOTAGE: a cofactor certificate off by 1 — the kernel refuses it (the elimination is checked, not trusted)",
      stm["status"] == "refused" and "proved that the proposition" in stm.get("out", ""),
      stm.get("out", "")[:300])
print("12. a TABLE (ztl-stand's table(...) compiles to nested ifpos): read exactly as hinges")
st21 = R["ZGenTable"]
# min over the box: S = 100 at T = 450: 100·(0.68 − 0.1·50/200) = 65.5; >= 65.2 holds
check("S·table(T) >= 65.2 over T in [150, 450] (three knots inside; min 65.5): a theorem through the hinges",
      st21["status"] == "theorem", st21)
st22 = R["ZGenTableB"]
check("the other side: >= 65.6 — no theorem", st22["status"] != "theorem", st22)
print("13. a missing domain law, and the target's own block of laws")
nd = R["ZGenNoDomain"]
check("ln(100)/(mu − lam/2) with mu − lam/2 < 0 on the WHOLE box (ztl-stand tasks/t16b, no domain law): REFUSED, "
      "posOK false said — not a kernel limit", nd["status"] == "refused" and "posOK false" in nd.get("why", ""), nd)
bk = R["ZGenBlock"]
check("F1 = k·x <= 22 next to an unrelated law with denominators: a theorem on the laws of F1's OWN block "
      "(blind/b01's Finst regressed when every row's denominators went into D)",
      bk["status"] == "theorem" and bk.get("about") == "laws" and bk.get("params") == ["k", "x"], bk.get("params"))
ic = R["ZGenIfConst"]
check("ifpos with a condition CONSTANT after the pinned values (e = 5: x·ifpos(e − 3, 2, 100) = 2x <= 4): decided "
      "exactly, a theorem (ztl-stand tasks/t25: a bond's maturity pinned)", ic["status"] == "theorem", ic)
print("14. a requirement on an IMPLICIT root (the zimplicit judge + ZBound, ZBoundPar.bound_at_root)")
im = R["ZImplFan"]
check("the fan's operating point Q (the root of pmax(1 − Q/Qmax) − K·Q² = 0): for every parameter vector the "
      "unique root exists and 0.02 <= Q <= 0.03 — ONE theorem (law_root + the bound)", im["status"] == "theorem", im)
check("the other side: Q <= 0.022 (the root reaches ~0.0265) — no theorem", R["ZImplFanB"]["status"] != "theorem",
      R["ZImplFanB"])
sd = R["ZImplSide"]
check("the ROOT's own side from the law's sign (ZBoundPar.root_ge / root_le): 0.0222 <= Q <= 0.0266 against the "
      "root's range [0.02228, 0.02651] — tighter than the bracket allows a bound to see — a theorem",
      sd["status"] == "theorem" and sd.get("root_side"), sd)
check("the other side: Q >= 0.023 (the root goes down to ~0.02228) — no theorem", R["ZImplSideB"]["status"] != "theorem",
      R["ZImplSideB"])
nd2 = R["ZGenNegDet"]
check("solutions inside a larger, non-rational target (pow(H1 + H2, 1.5) <= 20; Cramer's det is a negative "
      "constant): the denominators made positive (_posden) — a theorem, not a false 'posOK' refusal (real4/k06)",
      nd2["status"] == "theorem", nd2)
print(f"\n{ok} ok, {fail} fail")
print("ZBOUND LEAN BRIDGE GREEN" if fail == 0 else "ZBOUND LEAN BRIDGE RED")
sys.exit(1 if fail else 0)
