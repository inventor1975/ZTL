"""THE IMPLICIT JUDGE'S VERDICTS AS LEAN THEOREMS — the bridge, checked end to end.

tools/zimplicit_lean.py takes zimplicit's verdict on an implicit law ("q has a unique root in [lo, hi] over the box")
and turns it into `∀ p in the inner box, ∃! q ∈ [a, b], g(q, p) = 0` on VR's continuum, checked by the Lean kernel
(lean/ZRootPar.lean: par_root, or tree_root with a cover it searches). Here, on the laws of the zimplicit stand:
  * the FAN and the PUMP (blind tests) and four random laws (the stand's seed, one with atan) — THEOREMS;
  * a law with sin and one with cos (`q = a·cos(b·q) + p`, Dottie's number moved by parameters) — THEOREMS
    (ZXE.sin/cos since 2026-11-08: lean/ZSinIv.lean, VR's laws in lean/ZRootSin.lean);
  * a law with tan — NOT TRANSLATED (ZXE has no tan; said, not hidden);
  * a random law whose range touches the search end (a root is unique where it exists, but not every parameter has
    one) — NO VERDICT on existence;
  * NEGATIVE CONTROL: the fan's theorem with a bracket below every root — the kernel must refuse it.
The oil cooler (a 9-leaf cover found by the bridge, ~4 min) is measured, not run here: MEASURED 2026-11-08, theorem.
"""
import os, random, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, ROOT); sys.path.insert(0, os.path.join(ROOT, "tools"))
import zimplicit_lean as B  # noqa: E402
import zlaw2lean as Z  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


FAN = ("pmax=[44.16,51.84] credit, Qmax=[0.038,0.042] credit, K=[27200,36800] credit, Q=? credit",
       "pmax*(1 - Q/Qmax) - K*Q*Q", "Q", ["0", "0.06"])

print("1. the fan and the pump")
st = B.verdict_to_lean(*FAN, "ZBridgeFan")
check("fan: a theorem", st["status"] == "theorem", st)
pump = Z.LAWS["pump"]
st2 = B.verdict_to_lean(pump["qt"], pump["ex"], "Q", ["0.001", "0.06"], "ZBridgePump")
check("pump: a theorem", st2["status"] == "theorem", st2)

print("2. random laws of the zimplicit stand (seed 20261010)")
rnd = random.Random(20261010)
SHAPES = ["a*q*q*q + b*q - p", "a*q + c*exp(d*q) - p", "a*q - p/(1 + q*q) - b", "atan(a*q) + b*q - p", "q*q - p*q + b"]
laws = []
for i in range(6):
    text = SHAPES[i % 5]
    names = sorted(n for n in "abcdp" if n in text.replace("exp", "").replace("atan", ""))
    box = {}
    for n in names:
        c = rnd.choice([0.5, 1, 2, 3]); w = c * rnd.choice([0.02, 0.1, 0.3])
        box[n] = (round(c - w, 3), round(c + w, 3))
    laws.append((", ".join(f"{n}=[{lo},{hi}] credit" for n, (lo, hi) in box.items()) + ", q=? credit", text))
expect = {0: "theorem", 1: "theorem", 2: "no verdict", 3: "theorem", 5: "theorem"}
for i, want in expect.items():
    qt, text = laws[i]
    s = B.verdict_to_lean(qt, text, "q", ["-4", "4"], f"ZBridgeRand{i}")
    check(f"rand{i} ({text}): {want}", s["status"] == want, s)

s = B.verdict_to_lean("a=[0.98,1.02] credit, b=[1.8,2.2] credit, p=[1.96,2.04] credit, q=? credit",
                      "sin(a*q) + b*q - p", "q", ["-4", "4"], "ZBridgeSin")
check("sin(a*q) + b*q - p: a theorem", s["status"] == "theorem", s)
s = B.verdict_to_lean("a=[0.95,1.05] credit, b=[0.95,1.05] credit, p=[-0.05,0.05] credit, q=? credit",
                      "q - a*cos(b*q) - p", "q", ["-2", "2"], "ZBridgeCos")
check("q - a*cos(b*q) - p: a theorem", s["status"] == "theorem", s)
s = B.verdict_to_lean("a=[0.98,1.02] credit, b=[1.8,2.2] credit, p=[1.96,2.04] credit, q=? credit",
                      "tan(a*q/4) + b*q - p", "q", ["-4", "4"], "ZBridgeTan")
check("tan(a*q/4) + b*q - p: not translated", s["status"] == "not translated", s)

print("3. negative control")
fan_file = st.get("file")
if fan_file and os.path.exists(fan_file):
    txt = open(fan_file).read()
    lo = st["range"][0]
    bad = txt.replace(re.search(r"def qa : D := (.*)\n", txt).group(1), Z.dy(Z.floor_dy(lo / 4, 30)))
    bad = bad.replace(re.search(r"def qb : D := (.*)\n", bad).group(1), Z.dy(Z.floor_dy(lo / 2, 30)))
    bad = bad.replace("namespace ZBridgeFan", "namespace ZBridgeFanBad").replace("end ZBridgeFan", "end ZBridgeFanBad") \
        .replace("ZBridgeFan.law_root", "ZBridgeFanBad.law_root")
    out = B.run_lean(bad, "ZBridgeFanBad")
    check("the fan with a bracket below every root: the kernel refuses", "error" in out, out[:300])
else:
    check("negative control ran", False, "no fan file")

print(f"\n{ok} ok, {fail} fail")
print("ZIMPLICIT LEAN BRIDGE GREEN" if fail == 0 else "ZIMPLICIT LEAN BRIDGE RED")
sys.exit(1 if fail else 0)
