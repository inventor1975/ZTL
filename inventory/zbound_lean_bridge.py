"""A REQUIREMENT OVER A BOX AS A LEAN THEOREM — the bound bridge (tools/zbound2lean.py), checked end to end.

The curator, 2026-11-08: the stand should give proofs, not only certificates. Here:
  * the stand's divider (examples/divider-1pct-req-1pct.json, R1 = R2 = 1 kOhm +-1 %): Vout in [2.475, 2.525] from
    its laws, for every real R1, R2 in the box — a THEOREM (met exactly at the corners: monotone leaves);
  * a requirement with a margin on a three-resistor network (R3 in series) — a THEOREM;
  * a law that is not linear in the unknowns — NOT TRANSLATED (said, not hidden);
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
print(f"\n{ok} ok, {fail} fail")
print("ZBOUND LEAN BRIDGE GREEN" if fail == 0 else "ZBOUND LEAN BRIDGE RED")
sys.exit(1 if fail else 0)
