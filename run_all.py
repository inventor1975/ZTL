# -*- coding: utf-8 -*-
"""
Unified ZTL regression runner: all stands + Lean.
Exit 0 = all green. Key markers are checked against the output.
"""

import subprocess
import sys

STANDS = [
    ("ztl.py",         ["axiom NOT(Z) = F"]),
    ("audit.py",       ["Total: alive 12, fallen 14"]),
    ("entailment.py",  ["Rules total: alive 12, fallen 2"]),
    ("tableau.py",     ["ALL decisions coincided"]),
    ("quantifiers.py", ["UI rule", "✗ ¬∃ ⊨ ∀¬"]),
    ("tableau_fo.py",  ["ALL decisions coincided"]),
    ("paradoxes.py",   ["No fixed point"]),
    ("fixedpoint.py",  ["NON-monotone", "quarantine: {λ}"]),
    ("expeditions.py", ["HYPOTHESIS CONFIRMED TOTALLY"]),
    ("crocodile.py",   ["THE DEAL DOES NOT EARN TRUTH"]),
    ("zsets.py",       ["merging not earned"]),
    ("reals.py",       ["apartness earned by t=1"]),
    ("zfuncs.py",      ["even id is not certified"]),
    ("zarith.py",      ["EARNED zero"]),
    ("zprob.py",       ["ZTL verdict: Z"]),
    ("zmodal.py",      ["threshold coincided"]),
    ("zrussell.py",    ["facts grounded: 8 of 9"]),
    ("zverify.py",     ["divergences: 0", "violations of stable-verdict monotonicity: 0"]),
    ("zcombine.py",    ["✓ on all cases"]),
    ("zalgebra.py",    ["ZTL IS ALGEBRAIZABLE", "✓ DDT two-way, total",
                        "512 of 512"]),
    ("zinterp.py",     ["✓ INTERPOLATION HOLDS, total on the pool"]),
    ("zsequent.py",    ["✓ CUT IS ADMISSIBLE (semantic cut elimination), total"]),
    ("zfo.py",         ["ALL verdicts cross-checked ✓", "guarded drinker"]),
    ("zpassport.py",   ["✓ STIPULATION THEOREM: total",
                        "parity cross-check: 62 of 62 ✓"]),
    ("bridge.py",      ["ALL ANSWERS COINCIDE"]),
    ("zquasi.py",      ["SUBDIRECTLY IRREDUCIBLE", "= 2 + 512, ALL externals",
                        "NOT a"]),
    ("tool/test_zfl.py", ["ZFL FOUNDATION GREEN"]),
]


def main():
    failures = []
    for script, markers in STANDS:
        r = subprocess.run([sys.executable, script],
                           capture_output=True, text=True, timeout=300)
        missing = [m for m in markers if m not in r.stdout]
        status = "OK " if r.returncode == 0 and not missing else "FAIL"
        print(f"  [{status}] {script}"
              + (f"  — missing markers: {missing}" if missing else "")
              + (f"  — exit code {r.returncode}" if r.returncode else ""))
        if status == "FAIL":
            failures.append(script)

    print("  [....] lean: lake build ...")
    r = subprocess.run(["lake", "build"], cwd="lean",
                       capture_output=True, text=True, timeout=900)
    lean_ok = r.returncode == 0 and \
        "does not depend on any axioms" in r.stdout + r.stderr
    print(f"  [{'OK ' if lean_ok else 'FAIL'}] lean (zero axioms: "
          f"{'confirmed' if lean_ok else 'NOT CONFIRMED'})")
    if not lean_ok:
        failures.append("lean")

    print()
    if failures:
        print(f"RED: {failures}")
        return 1
    print(f"ALL GREEN: {len(STANDS)} stands + Lean.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
