# -*- coding: utf-8 -*-
"""
Unified ZTL regression runner: all stands + Lean.
Exit 0 = all green. Key markers are checked against the output.
"""

import os
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
    ("zeq.py",         ["ZEQ GREEN", "grounded: T total; marked: Z total",
                        "0 violations of 24 licensed substitutions"]),
    ("zdesc.py",       ["ZDESC GREEN", "a thing exists iff it is self-identical",
                        "ZTL is NOT supervaluational"]),
    ("zmodid.py",      ["ZMODID GREEN", "Kripke recovered",
                        "a name is rigid ⟺ it denotes"]),
    ("zeps.py",        ["ZEPS GREEN", "the choice term denotes exactly",
                        "the empty choice is the mark"]),
    ("zpassport.py",   ["✓ STIPULATION THEOREM: total",
                        "parity cross-check: 62 of 62 ✓"]),
    ("ztljudge.py",     ["ZTLJUDGE GREEN", "over an unchanged core",
                        "a mark reached the join"]),
    ("zsweep.py",      ["ZSWEEP GREEN", "natural implications, D = {T}   : 6",
                        "D = {T, Z}: 24", "modus ponens, no credit): 72",
                        "keeping the identity law p -> p : 0",
                        "designates T in every cell where truth is FORCED: 1",
                        "realized by some arrow: 28",
                        "no C-extending arrow has both ID and NOCREDIT",
                        "must therefore be NON-TRUTH-FUNCTIONAL"]),
    ("zledger.py",     ["ZLEDGER GREEN", "divergences: 0",
                        "NEW in ZTL: 0", "classical 16, ZTL 195",
                        "hold with ONE of two verified : 379",
                        "violations: [('Z', 'Z')]"]),
    ("zprove.py",      ["ZPROVE GREEN", "minimum verification bill: 3 atoms",
                        "markings that EARN the antecedent: 125"]),
    ("znum.py",        ["E37 GREEN", "0 revocations",
                        "one thing in the world: m - m over m=[0,9]  ->  (0, 0)",
                        "two acts of measuring : m - m over m=[0,9]  ->  (-9, 9)",
                        "share == 8/3 :  int -> F,  decimal2 -> F,  frac3 -> Z",
                        "not 'document share'"]),
    ("znumjudge.py",   ["ZNUMJUDGE GREEN", "contest type share:int"]),
    ("znumsolve.py",   ["ZNUMSOLVE GREEN", "x in [5, 5]",
                        "a in [6, 6], b in [4, 4]",
                        "solutions dropped by narrowing: 0",
                        "line3 = 1500   provenance: earned",
                        "line3 = 1500   provenance: credit"]),
    ("znumride.py",    ["ZNUMRIDE GREEN", "mismatches: 0 of 17"]),
    ("zparadox.py", ["E28 GREEN", "PARADOX (0 tables)",
                     "strong liar", "INTRINSIC"]),
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
    ("zexpire.py",     ["contentful formulas surviving unrestricted expiry: 0",
                        "the settled deal UNSETTLES",
                        "the verdict SURVIVES the expiry"]),
    ("zderive.py",     ["closure(∅, alive + both loans) = 0 formulas",
                        "yet ZTL-TAUTOLOGIES exist on this pool: 6",
                        "soundness cross-check on the core: 0 violations",
                        "the first measured"]),
    ("dilemmas/quantum_pair.py",
                       ["EVERY local address is empty",
                        "SINGLET REACHED (round 3)",
                        "the singlet line",
                        "violations 0"]),
    ("vrg/epoch_artifact.py",
                       ["(T, ALLOW_EXECUTION, hereditary)",
                        "evidence_expire => (Z, DENY, until-",
                        "revoke => fresh=F => (F, DENY, hereditary)",
                        "REJECTED: verify(fresh:=T) carries no source_reference"]),
    ("pssl/grounds.py", ["LEG 1 GREEN", "P1 HOLDS", "P2 HOLDS",
                         "calibration vs lean/QuantumWitness.lean: AGREE"]),
    ("pssl/arrow_control.py", ["Q1 HOLDS", "TACK 2a GREEN",
                               "none can succeed"]),
    ("pssl/family.py", ["THREE ZEROS THAT ARE NOT TIER C", "TACK 2b GREEN", "Q2 — Ł3 HAS the deduction theorem : FAILS",
                        "BOTH halves        : classical, intuitionistic",
                        "keeps DT, no MP    : LP"]),
    ("pssl/invariants.py", ["LEG 5 GREEN", "The trade is NOT a law of the space",
                            "across the extended eight : FAILS"]),
    ("pssl/census.py", ["CENSUS GREEN", "Our eight are RARE in their own space"]),
    ("pssl/ztl_signature.py", ["SIGNATURE GREEN", "uniform: True",
                               "NEVER appears"]),
    ("pssl/ztl_vs_k3.py", ["ZTL vs K3 GREEN", "They are INCOMPARABLE",
                           "hypothesis refuted, leg-3 artifact corrected"]),
    ("pssl/distance.py", ["LEG 3 GREEN", "R1 (kind predicts proximity) : FAILS",
                          "{CPC, IPC, LP, Ł3}", "DEPTH-1 POOL ARTIFACT"]),
    ("pssl/apartness.py", ["TACK 2c GREEN", "every pair carries a receipt",
                           "classical | LP  —  p, ¬p ⊨ q  (rule/arity 2)"]),
    ("pssl/kripke.py", ["KRIPKE CROSS-CHECK GREEN",
                        "definitive bugs (prover says ⊢, model refutes) : 0",
                        "14-rule battery : agree 14 / 14"]),
    ("inventory/paper_claims.py", ["PAPER CLAIMS GREEN"]),
    ("pssl/E27_instrument.py", ["E27 GREEN", "7 blindnesses reproduced",
                                "blindnesses that silently changed the answer: 7 of 7"]),
    ("dilemmas/solved/sorites/sorites.py", ["SORITES GREEN",
                             "'some grain is a cliff' (H & ~H-) = F",
                             "the same sum against a cited norm: EARNED"]),
    ("dilemmas/closure.py", ["CLOSURE GREEN",
                             "FAILS, counterexample",
                             "acts that settle it -> NONE",
                             "vat stipulated away: hands EARNED"]),
    ("dilemmas/surprise.py", ["SURPRISE GREEN",
                              "days left for a surprise: 0",
                              "days left for a surprise: 5",
                              "WARRANTY BELONGS TO A LEDGER"]),
    ("dilemmas/collatz.py", ["COLLATZ GREEN",
                             "changes of verdict or grade as the checked part grows: 0",
                             "the two F's are not the same F"]),
    ("dilemmas/tautology_boundary.py", ["BOUNDARY GREEN",
                                        "TAUTOLOGY HELD",
                                        "pipeline is LIVE"]),
    ("dilemmas/quantum_ladder.py",
                       ["0 of 512",
                        "0 of 64",
                        "Sasaki MP a∧(a→s b) ≤ b: True (216/216 triples)",
                        "iron at every rung"]),
    ("zclassify.py",   ["docket complete — every row pinned",
                        "Kripke transported, total",
                        "barber = Grelling = R∈R = liar",
                        "suspended ⊥ ⇒ DOWNSTREAM"]),
]


def _run_one(item):
    script, markers = item
    r = subprocess.run([sys.executable, script],
                       capture_output=True, text=True, timeout=900)
    # A stand may SKIP when an optional third-party backend is absent (the
    # quantum probes need qiskit-aer). A skip is NOT a pass: it is reported
    # separately, its markers are not claimed, and the summary says how many
    # stands actually ran. It is also not a failure — an unavailable device
    # is not a refuted theorem.
    if r.returncode == 0 and "SKIPPED" in r.stdout:
        return script, "skip", [], 0
    missing = [m for m in markers if m not in r.stdout]
    ok = r.returncode == 0 and not missing
    return script, ok, missing, r.returncode


def main():
    """Flags, because a full pass costs about two minutes and most edits
    touch one stand: `--only <substring>` runs the matching stands (and
    skips Lean unless a Lean file is what changed), `--no-lean` drops the
    `lake build`. No flag = everything, which is what a commit deserves."""
    argv = sys.argv[1:]
    pattern = None
    if "--only" in argv:
        pattern = argv[argv.index("--only") + 1]
    skip_lean = "--no-lean" in argv or pattern is not None
    if pattern:
        globals()["STANDS"] = [(s_, m) for s_, m in STANDS if pattern in s_]
        if not STANDS:
            print(f"no stand matches {pattern!r}")
            return 1
    failures = []
    # Stands are independent processes; run them on a pool. Kept
    # deterministic in REPORTING order (STANDS order), not completion
    # order, so the output reads the same as the sequential runner.
    from concurrent.futures import ThreadPoolExecutor, as_completed
    # Parallelism is bounded by the MACHINE, not by a constant. A fixed 30
    # is fine on a 32-core workstation and starves a 2-4 core CI runner: the
    # heaviest stand (pssl/ztl_signature.py, ~52 s alone) then exceeded the
    # old 300 s limit and the workflow died on a timeout, not on a result.
    # Green on the author's machine is exactly the assurance this project
    # refuses to grant itself, so the runner sets the width.
    workers = max(2, min(30, os.cpu_count() or 4, len(STANDS)))
    # Warm the Lean build ONCE before the pool. Several stands shell out to
    # `lake build` themselves (bridge.py compares 141 answers against the
    # kernel; inventory/paper_claims.py counts the #print axioms lines), and
    # on a COLD cache two of them racing over the same build directory come
    # back red. Locally the cache is always warm, so this was invisible here
    # and fatal in CI — found 2026-08-11 by running the suite in a fresh
    # clone, which is the only honest imitation of what CI sees.
    if not skip_lean:
        print("  warming the Lean build (cold cache would race the stands)…")
        subprocess.run(["lake", "build"], cwd="lean",
                       capture_output=True, text=True, timeout=1800)
    total = len(STANDS)
    results = {}
    # Live progress: the stands run in parallel and would otherwise print
    # nothing until all finish — which reads as "hung". Show a counter that
    # advances as each completes (reporting below stays in STANDS order).
    print(f"  running {total} stands, {workers} at a time — the slow part; progress below:",
          flush=True)
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(_run_one, item) for item in STANDS]
        for done, fut in enumerate(as_completed(futures), 1):
            script, ok, missing, rc = fut.result()
            results[script] = (ok, missing, rc)
            print(f"\r    {done}/{total} stands finished…", end="", flush=True)
    print()
    skipped = []
    for script, _markers in STANDS:
        ok, missing, rc = results[script]
        status = "SKIP" if ok == "skip" else ("OK " if ok else "FAIL")
        print(f"  [{status}] {script}"
              + ("  — optional backend absent; nothing claimed"
                 if ok == "skip" else "")
              + (f"  — missing markers: {missing}" if missing else "")
              + (f"  — exit code {rc}" if rc else ""))
        if ok == "skip":
            skipped.append(script)
        elif not ok:
            failures.append(script)

    if skip_lean:
        print("  [skip] lean (not asked for — nothing claimed for it here)")
    else:
        print(f"  [....] lean: lake build ...  ({workers} stands ran in parallel)")
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
    # Say what was actually exercised. "ALL GREEN: 59" while two stands never
    # ran would be exactly the kind of assurance this project refuses itself.
    ran = len(STANDS) - len(skipped)
    if skipped:
        print(f"ALL GREEN: {ran} of {len(STANDS)} stands + Lean "
              f"({len(skipped)} SKIPPED, backend absent: "
              f"{', '.join(skipped)} — nothing claimed for them).")
    else:
        print(f"ALL GREEN: {len(STANDS)} stands"
              + ("" if skip_lean else " + Lean")
              + ("" if not skip_lean else " (Lean not run)") + ".")
    return 0


if __name__ == "__main__":
    sys.exit(main())
