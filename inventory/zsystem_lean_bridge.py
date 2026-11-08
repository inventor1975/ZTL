"""THE SYSTEM JUDGE: a system of laws F(x, p) = 0 judged by the Lean kernel — the verdict is a theorem or nothing.

tools/zkraw2lean.py `system_to_lean`: Python PROPOSES (Newton for the centre, Y ≈ J⁻¹, Z ≈ J, the cube radius from the
solution's shift over the parameter box, a cover when the box is wide); the kernel DISPOSES (lean/ZKrawSys.lean
`sys_root`, lean/ZKrawCover.lean `kt_root`). Here:
  * the circle meets the exponential; a 3×3 system with exp and ln; the circle with a real radius parameter
    R ∈ [0.999, 1.001] — THEOREMS (a solution in the cube, unique there, for every parameter in the inner box);
  * x² + y² + 1 = 0 (no real solution) — NO VERDICT (Newton finds none; nothing is claimed);
  * a system with atan (y = atan x, x + y = 1) — a THEOREM; a system with sin — NOT TRANSLATED;
  * NEGATIVE CONTROL: the circle's theorem with the cube moved by 4r — the kernel must refuse it.
The 64-leaf cover of `chem3p` (kernel 66 s) is in lean/ZSysChem3p.lean, built by CI's lean job.
"""
import os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, ROOT); sys.path.insert(0, os.path.join(ROOT, "tools"))
import zkraw2lean as K  # noqa: E402
import zlaw2lean as Z  # noqa: E402

ok = fail = 0


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


CASES = [
    ("ZJudgeCircle", K.SYSTEMS["circle_exp"], "theorem"),
    ("ZJudgeChem3", K.SYSTEMS["chem3"], "theorem"),
    ("ZJudgeCircleR", dict(vars=["x", "y"], laws=["x*x + y*y - R*R", "x - exp(y)"], params={"R": ("0.999", "1.001")},
                           guess=[0.5, -0.5], title="the circle of a real radius R meets the exponential"), "theorem"),
    ("ZJudgeNone", dict(vars=["x", "y"], laws=["x*x + y*y + 1", "x - y"], guess=[0.5, 0.3],
                        title="no real solution"), "no verdict"),
    ("ZJudgeAtan", dict(vars=["x", "y"], laws=["atan(x) - y", "x + y - 1"], guess=[0.5, 0.5],
                        title="the line meets atan"), "theorem"),
    ("ZJudgeSin", dict(vars=["x", "y"], laws=["sin(x) - y", "x + y - 1"], guess=[0.5, 0.5],
                       title="sin is not in ZXE"), "not translated"),
]
print("1. the judge on systems")
first = None
for nm, spec, want in CASES:
    st = K.system_to_lean(spec, nm)
    check(f"{nm}: {want}", st["status"] == want, st)
    if nm == "ZJudgeCircle":
        first = st

print("2. negative control")
if first and first.get("file"):
    txt = open(first["file"]).read()
    m = re.search(r"def ys : List D := (\[.*\])\n", txt)
    r = re.search(r"InC 2 ys (\(⟨⟨\d+, \d+⟩, \d+⟩ : D\))", txt).group(1)
    rv = [F_ for F_ in re.findall(r"⟨⟨(\d+), (\d+)⟩, (\d+)⟩", r)][0]
    from fractions import Fraction as F
    rr = F(int(rv[0]) - int(rv[1]), 1 << int(rv[2]))
    ys = [F(int(p) - int(n), 1 << int(e)) for p, n, e in re.findall(r"⟨⟨(\d+), (\d+)⟩, (\d+)⟩", m.group(1))]
    moved = "[" + ", ".join(Z.dy(v + 4 * rr) for v in ys) + "]"
    bad = txt.replace(m.group(1), moved).replace("ZJudgeCircle", "ZJudgeCircleBad")
    path = os.path.join(LEAN, "gen", "ZJudgeCircleBad.lean")
    open(path, "w").write(bad)
    out = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1500)
    check("the circle with the cube moved by 4r: the kernel refuses", "error" in out.stdout + out.stderr,
          (out.stdout + out.stderr)[:300])
else:
    check("negative control ran", False, "no circle file")

print(f"\n{ok} ok, {fail} fail")
print("ZSYSTEM LEAN BRIDGE GREEN" if fail == 0 else "ZSYSTEM LEAN BRIDGE RED")
sys.exit(1 if fail else 0)
