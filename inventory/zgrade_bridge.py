"""THE JUDGE'S VERDICTS AS LEAN THEOREMS — the bridge, checked end to end on a sample of the paradox stands.

tools/zgrade2lean.py runs a stand with zverify.grade instrumented and writes every verdict (grade + value) as a
Lean theorem; lean/ZGrade.lean proves what a grade MEANS (hereditary / stable, both directions, zero axioms).
Here: the bridge on a few light stands, every emitted theorem checked by the Lean kernel, and a NEGATIVE CONTROL
(the same claim with a wrong grade) that the kernel must refuse.

The full run (all 53 stands, 36,025 distinct verdicts, ~5 min on 6 processes, one file up to ~10 GB) is
    python3 tools/zgrade2lean.py dilemmas/*.py --out lean/gen      # then: lake env lean lean/gen/ZGradeRun_*.lean
MEASURED 2026-11-08: 36,025 of 36,025 recomputed by the kernel, 0 disagreements (713 with 14–15 marks through a
witness completion, `ZGrade.notStable_witness`). Too heavy for CI; this stand is its sample.
"""
import glob, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, "lean")
SAMPLE = ["cogito.py", "moore.py", "hardy.py", "lottery.py", "bertrand.py", "agrippa_critics.py",
          "agrippa_nullary.py", "sleeping_beauty.py", "closure.py", "court.py"]


def lean_check(path):
    r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1500)
    return r.returncode == 0 and "error" not in (r.stdout + r.stderr), (r.stdout + r.stderr)[:400]


def main():
    out = tempfile.mkdtemp(prefix="zgrade_", dir=os.path.join(LEAN))
    try:
        stands = [os.path.join(ROOT, "dilemmas", s) for s in SAMPLE]
        r = subprocess.run([sys.executable, os.path.join(ROOT, "tools", "zgrade2lean.py"), *stands, "--out", out],
                           capture_output=True, text=True, timeout=900)
        if r.returncode != 0:
            print("RED: the bridge failed:", r.stderr[-400:]); return 1
        files = sorted(glob.glob(os.path.join(out, "ZGradeRun_*.lean")))
        n = 0
        for f in files:
            ok, msg = lean_check(f)
            k = open(f).read().count("\ntheorem ")
            print(f"  [{'OK ' if ok else 'FAIL'}] {os.path.basename(f)}: {k} verdicts")
            if not ok:
                print("RED:", msg); return 1
            n += k
        # NEGATIVE CONTROL: the first theorem with its grade replaced must be refused
        first = open(files[0]).read()
        m = re.search(r"theorem (g\d+) : grade (.*?) = \.(\w+) ∧", first, re.S)
        wrong = {"hereditary": "untilVerification", "sound": "hereditary", "untilVerification": "hereditary"}[m.group(3)]
        neg = first.split(f"theorem {m.group(1)} :")[0] + f"theorem neg : grade {m.group(2)} = .{wrong} := by decide +kernel\n"
        negf = os.path.join(out, "ZGradeNeg.lean")
        open(negf, "w").write(neg)
        ok, _ = lean_check(negf)
        if ok:
            print("RED: the kernel ACCEPTED a wrong grade"); return 1
        print(f"  [OK ] negative control: a wrong grade ({wrong} for {m.group(3)}) refused by the kernel")
        print(f"ZGRADE BRIDGE GREEN — {n} verdicts of {len(files)} stands recomputed by the Lean kernel; a wrong one refused")
        return 0
    finally:
        for f in glob.glob(os.path.join(out, "*")):
            os.remove(f)
        os.rmdir(out)


if __name__ == "__main__":
    sys.exit(main())
