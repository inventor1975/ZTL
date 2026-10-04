# -*- coding: utf-8 -*-
"""preflight — the cheap checks BEFORE the one full `run_all.py` (curator, 2026-10-04: "you run, see that the
count does not match, and run again — two runs where one would do, and each run is long").

What it runs, in seconds rather than minutes:
  1. every new or changed Lean module: `lake env lean <file>`; any "depends on axioms" line is a failure;
  2. every new or changed stand under dilemmas/, db/, pssl/, inventory/ ... that `run_all.py` lists: run it;
  3. inventory/paper_claims.py — the counts baked into the papers AND the CI floor in lean.yml (16 s;
     this is the check that made the second full run of 2026-10-04 necessary);
  4. inventory/axiom_audit.py — every theorem on the empty axiom list.
Green here -> ONE full run_all.py before the commit. Red here -> fix first; the full run would only repeat it.

It does NOT replace run_all.py: an untouched stand can still break through a shared module. It removes the
second full run caused by what a 30-second check already knows.

Run:  python3 preflight.py
"""
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.abspath(__file__))


def changed():
    out = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT, capture_output=True, text=True).stdout
    return [ln[3:].strip() for ln in out.splitlines() if ln.strip()]


def step(name, cmd, cwd=ROOT, bad=None):
    t = time.time()
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    out = r.stdout + r.stderr
    ok = r.returncode == 0 and not (bad and bad in out)
    print(f"  [{'OK ' if ok else 'FAIL'}] {name}  ({time.time() - t:.0f} s)")
    if not ok:
        print("\n".join("        " + ln for ln in out.strip().splitlines()[-8:]))
    return ok


def main():
    sys.path.insert(0, ROOT)
    import run_all
    listed = {s for s, _ in run_all.STANDS}
    files = changed()
    lean = [f for f in files if f.startswith("lean/") and f.endswith(".lean")]
    stands = [f for f in files if f in listed]
    print(f"preflight: {len(lean)} changed Lean module(s), {len(stands)} changed stand(s)")
    ok = True
    for f in lean:
        ok &= step(f, ["lake", "env", "lean", os.path.basename(f)], cwd=os.path.join(ROOT, "lean"),
                   bad="depends on axioms")
    for f in stands:
        ok &= step(f, [sys.executable, f])
    ok &= step("inventory/paper_claims.py (paper counts + CI floor)", [sys.executable, "inventory/paper_claims.py"])
    ok &= step("inventory/axiom_audit.py", [sys.executable, "inventory/axiom_audit.py"])
    print("PREFLIGHT GREEN — now ONE full run_all.py" if ok else "PREFLIGHT RED — fix before the full run")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
