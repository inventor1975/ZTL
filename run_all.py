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
    ("zverify.py",     ["hereditary without sound: 0", "THE GRADES SEPARATE",
                        "revocations or grade losses: 0",
                        "invariant under EVERY single verification: True"]),
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
    ("zipc.py",        ["INCOMPARABLE sublogics of classical logic",
                        "Rule verdicts coincide: 14 of 14",
                        "match the canon ✓", "mismatches: 0"]),
    ("zopsets.py",     ["IDENTITY IS TOTALLY EARNABLE", "dedup EARNED",
                        "SOUND about the facts: 0",
                        "hereditary-warranted 0", "ORTHOGONALITY"]),
    ("zchoice.py",     ["mismatches 0", "violations 0 of",
                        "stage verdicts revoked by one revealed bit: 0",
                        "never T", "REDEEMED"]),
    ("zzhegalkin.py",  ["SURVIVES ENTIRELY", "514 = 514",
                        "x⊕x ≡ ⊥ on all three values ✓",
                        "Zhegalkin-as-ring FALLS"]),
    ("finn_reconcile.py", ["znor  == ¬x∩̇¬x  (Finn B3ex,¬ gen) : True",
                        "[znand] == [znor]   : True",
                        "|[znand]|           = 18",
                        "[x̄variant] == [znand]: False"]),
    ("pengine.py",     ["all 9015 one-sentence nets",
                        "0 violations",
                        "grounded without a unique model: 0",
                        "cautious Z (1 model, still Z): 1068",
                        "odd k → 0 solutions (Liar-type)",
                        "truncated Yablo is CONSISTENT"]),
    ("ztime.py",       ["ticks leaving an H-state: 0",
                        "caught waiting (value Z): 0",
                        "ending hereditary: 130",
                        "GENUINE entries into sound-only (predecessor not S): 0",
                        "FULL STRICT LADDER U → S → H: realized, rung by rung."]),
    ("tool/test_zfl.py", ["ZFL FOUNDATION GREEN"]),
    ("usage/car.py",   ["settled at tick 1; checks saved: 3",
                        "settled at tick 2; checks saved: 2",
                        "Once HEREDITARY, every remaining check buys nothing"]),
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
