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
                        "a mark reached the join",
                        "label covered every load-bearing hole: 10806",
                        "label also named an innocent one: 1778"]),
    ("zsweep.py",      ["ZSWEEP GREEN", "natural implications, D = {T}   : 6",
                        "D = {T, Z}: 24", "modus ponens, no credit): 72",
                        "keeping the identity law p -> p : 0",
                        "designates T in every cell where truth is FORCED: 1",
                        "realized by some arrow: 28",
                        "no C-extending arrow has both ID and NOCREDIT",
                        "must therefore be NON-TRUTH-FUNCTIONAL"]),
    ("zcontain.py",    ["ZCONTAIN GREEN", "models of the sign-off pair: 0",
                        "3 of 3 numeric claims still judged",
                        "OPEN — verify ['summary_ok']"]),
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
                        "not 'document share'",
                        "NO readings at all     k int in [.2,.9]: E",
                        "NO readings, units     5 m == 3 RUB    : E"]),
    ("znumjudge.py",   ["ZNUMJUDGE GREEN", "contest type share:int",
                        "charged to a signature: {'reg-7': 2}",
                        "charged to no one, a pairing: [('area', 'fee')]",
                        "pending=['a <= b', 'ok']"]),
    ("znumsolve.py",   ["ZNUMSOLVE GREEN", "x in [5, 5]",
                        "a in [6, 6], b in [4, 4]",
                        "solutions dropped by narrowing: 0",
                        "line3 = 1500   provenance: earned",
                        "line3 = 1500   provenance: credit",
                        "age in [11, 13]",
                        "cure ['document total']"]),
    ("zbook.py",       ["ZBOOK GREEN",
                        "census: {'EARNED': 3, 'OPEN': 1, 'E': 1}",
                        "after inv-19 is withdrawn: changed=['c1']",
                        "c3: EARNED -> ON CREDIT",
                        "passport ['UNDERDETERMINED']",
                        "withdraw BOTH of k1's grounds -> k1 ON CREDIT, k2 EARNED",
                        "h6  EARNED  declared   [('x', 'inherited', 'h5')]",
                        "the graph on that pair   : [('h2', 'h3', ['h1'])]",
                        "when every clock runs out: [('p1', 'ON CREDIT'), ('p2', 'ON CREDIT')]",
                        "after they all run out: {'ON CREDIT': 4}",
                        "3 of 6 earned claims stand on",
                        "f2  EARNED  tested=declared   learning=settled expiry=perpetual",
                        "f3  EARNED  tested=documented learning=settled expiry=exposed",
                        "inv-17                 [0, 2]",
                        "plain-deed             [1, 1]   <- zero width: nothing taken on trust",
                        "ASSUMED, and unverifiable: the 4 external names below denote 4 distinct grounds",
                        "if inv-17 and invoice-17 are one paper: 2 + 2 -> 4",
                        "k0  EARNED  tested=documented expiry=perpetual",
                        "trustee-letter       carries     2650   (cost counts 2 claims)",
                        "partner-a-report     carries      300",
                        "RUB        5000", "m2            3",
                        "exposure(inv-17) is empty",
                        "mission.advance  both grounds are authority",
                        "survey.width    both grounds are evidence",
                        "k2  EARNED  tested=declared   expiry=perpetual"]),
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
    ("tool/zfl2doc.py", ["ZFL DOC GREEN",
                         "every code the validator raises is documented"]),
    ("tool/test_zfl2.py", ["ZFL2 GREEN",
                           "applies: {'numeric': True, 'passport': True, 'ledger': True, 'judge': True}",
                           "two lines on ONE document  : {'inv-17': [2, 2]}",
                           "cases the docket promises: 26, present: 26",
                           "39 examples, all validating and running",
                           "assembled sheet    : line=1500 earned:inv-17 RUB, budget=5000 earned:order-4 RUB",
                           "always required: ['name', 'status']   required in context: ['ground']"]),
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
    ("conformance/judge_table.py", ["JUDGE TABLE GREEN",
                                    "cases swept: 184,320",
                                    "Every one of them from INCOMPARABLE UNITS",
                                    "MATCHES the stored table"]),
    ("conformance/judge_table_three.py", ["JUDGE TABLE GREEN",
                                          "cases swept: 139,968",
                                          "MATCHES the stored table"]),
    ("conformance/book_table.py", ["BOOK TABLE GREEN",
                                   "books swept: 1,536",
                                   "MATCHES the stored table"]),
    ("conformance/passport_table.py", ["PASSPORT TABLE GREEN",
                                       "systems swept: 1,728",
                                       "0 violations"]),
    ("conformance/ztl_table.py", ["ZTL TABLE GREEN",
                                  "132 formulas x 9 markings = 1,188 verdicts",
                                  "VERDICT Z: 6 of 1,188"]),
    ("conformance/solver_table.py", ["SOLVER TABLE GREEN",
                                     "cases swept: 480",
                                     "case: 0 laundered values"]),
    ("db/probe_ledger.py", ["LEDGER PROBE GREEN",
                            "4: billed, line_a, line_b, margin",
                            "6500 EARNED  ->  6500 ON CREDIT"]),
    ("db/probe_assertions.py", ["ASSERTIONS PROBE GREEN",
                                "NEITHER 2   of 12",
                                "pairs that are INCOMPARABLE               55",
                                "grades that map to 'credit'               15"]),
    ("db/probe_lattice.py", ["LATTICE PROBE GREEN",
                             "coherent ways to draw the earned/credit line   168",
                             "is `billed` EARNED?   yes under 84 thresholds",
                             "margin     2  documentary"]),
    ("db/probe_override.py", ["OVERRIDE PROBE GREEN",
                              "13450 (and no idea what it added)",
                              "13450 ON CREDIT (2 of the parts)",
                              "thresholds where the two DISAGREE     118"]),
    ("db/probe_failures.py", ["FAILURES PROBE GREEN", "TOUCHES   2 of 8",
                              "OUT       4 of 8",
                              "Wirecard would have printed EARNED"]),
    ("db/probe_system_errors.py", ["SYSTEM ERRORS PROBE GREEN",
                                   "cannot compare 'lbf' with 'N'",
                                   "the formula as WRITTEN   -> EARNED",
                                   "-> ['dataset', 'finding', 'policy']",
                                   "CAUGHT 1 of 3   CAUGHT ONLY IF DECLARED 1"]),
    ("db/probe_sheet.py", ["SHEET PROBE GREEN",
                           "B6 <- B1, B2, B3, B4",
                           "(B2) turns out wrong  ->  margin, over_ceiling, "
                           "subtotal, vat, total",
                           "the count of links anybody typed is ZERO"]),
    ("db/probe_swarm.py", ["SWARM PROBE GREEN",
                           "one compromised agent, median fallout",
                           "Not a curve — a collapse"]),
    ("db/probe_topology.py", ["TOPOLOGY PROBE GREEN",
                              "random-local", "hierarchy", "scale-free",
                              "THE THRESHOLD IS AN ARTEFACT OF WHERE YOU AIM",
                              "<- deliberately targeted"]),
    ("db/probe_containment.py", ["CONTAINMENT PROBE GREEN",
                                 "THE COMMANDER    -> 100,000 of 100,000 fall",
                                 "the commander costs 100,000"]),
    ("db/probe_criterion.py", ["CRITERION PROBE GREEN",
                                 "The minimum does not determine C",
                                 # These two pin the CORRECTED claim. `1 - q* =
                                 # r* exactly` was pinned by a 1e-9 assert over
                                 # a 0.05 grid — it could not fail. The markers
                                 # now hold the gap the finer sweep shows, so
                                 # `exactly` cannot creep back.
                                 "ONE NUMBER OR TWO",
                                 "<- the gap the grid hid"]),
    ("db/probe_classes.py", ["CLASSES PROBE GREEN",
                             "two dimensions (evidence, authority)   r* = 0.65",
                             "four (plus shared model and sensor)    r* = 0.75",
                             "A_crit = 1.000, from authority root"]),
    ("db/probe_roots.py", ["ROOTS PROBE GREEN",
                           "1 authority root                   A_crit = 1.000",
                           "3 roots, SHARED upstream           A_crit = 1.000",
                           "THE SHARED UPSTREAM"]),
    ("db/probe_blindspot.py", ["BLINDSPOT PROBE GREEN",
                               "THE MAGNITUDE DID NOT REPRODUCE",
                               "THE DIRECTION HOLDS FOR THIS KIND OF EDGE",
                               "THE OTHER KIND OF MISSING EDGE"]),
    ("db/probe_currentness.py", ["CURRENTNESS PROBE GREEN",
                                 "A PREDICTION OF MINE, REFUTED BY ITS OWN TABLE",
                                 "blind steps == update lag, exactly",
                                 "max tolerable lag = action budget"]),
    ("db/probe_gate.py", ["A RUNTIME GATE",
                          "CONTAINS A FAILURE OF MY OWN",
                          "Purely descriptive, third pass",
                          "may continue to TREAT its current warrant as satisfying the"]),
    # The measured-against-the-package rows, so a future edit to the ledger's
    # claims cannot quietly drop what installing ProvSQL cost us.
    ("db/probe_provenance.py", ["PROVENANCE PROBE GREEN",
                                "inv-17 forged, what falls: line_a, line_b, "
                                "billed, margin",
                                "expected(sum(amount))` = 2000",
                                "cover more of this than expected"]),
    ("db/probe_sensitivity.py", ["SENSITIVITY PROBE GREEN",
                                 "BOTH REAL",
                                 "ANOTHER CONCLUSION WRITTEN BEFORE THE TABLE"]),
    # NO NUMERIC MARKERS. This stand reads the host's own package database,
    # so its figures differ per machine by design; pinning one machine's
    # A_crit made GitHub red for measuring correctly.
    ("db/probe_real.py", ["REAL PROBE GREEN",
                          "requirement groups offering an alternative",
                          "figures are this host's"]),
    ("db/probe_variance.py", ["VARIANCE PROBE GREEN",
                              "median 0.725", "varies 0.6..0.75",
                              "A_crit, 2 roots, either                median 0.117"]),
    ("inventory/note_claims.py", ["NOTE CLAIMS GREEN",
                                  "37 + 10 claims and 25 figures"]),
    # Added 2026-08-17 after a pre-deposit review found the same defect four
    # times: a claim withdrawn in one place and left standing in another. The
    # figure scan cannot see it — the numbers were right and the sentences
    # were false. On its first run it found a fifth site, in a third document
    # neither review had opened.
    ("inventory/withdrawn_claims.py", ["WITHDRAWN CLAIMS GREEN",
                                       "none live"]),
    ("inventory/paper_claims.py", ["PAPER CLAIMS GREEN"]),
    ("inventory/docket_claims.py", ["DOCKET TABLE GREEN",
                                    "rows printed in the paper: 21"]),
    ("inventory/corpus_book.py", ["CORPUS BOOK GREEN", "census: {'EARNED': 15}",
                                  "at 8 of 15 claims",
                                  "tomova                           [8, 8]",
                                  "the machine's own trust surface: 0 of 15",
                                  "grounds we cannot re-establish at all: ['tomova']",
                                  "the trust brackets, ground by ground: [(3, 3), (4, 4), (5, 5), (8, 8)]",
                                  "ASSUMED and unverifiable: the 6 external names below denote 6 distinct grounds",
                                  "if lake-build and tomova were one: 3 + 8 -> 10",
                                  "... 13 such pairs in all"]),
    ("pssl/E27_instrument.py", ["E27 GREEN", "7 blindnesses reproduced",
                                "blindnesses that silently changed the answer: 7 of 7"]),
    ("dilemmas/solved/sorites/sorites.py", ["SORITES GREEN",
                             "'some grain is a cliff' (H & ~H-) = F",
                             "the same sum against a cited norm: EARNED"]),
    # The philosophical case stands. They were written 2026-08-08 and were
    # never wired here — measured 2026-08-13: all five still green, but for
    # three months they held by luck while the judge kept changing. The
    # markers below pin the FINDING of each file, not merely its exit code.
    ("dilemmas/plato_third_man.py", [
        "ok  regress engine, all links unverified                                ON CREDIT T  until-verification weak=['g', 'n', 'r', 's']",
        "ok  middle Plato: every premise granted — regress still not delivered   OPEN      F  until-verification weak=['r']"]),
    ("dilemmas/agrippa.py", [
        "ok  F1 inference itself, everything unverified                 EARNED    T hereditary         weak=['j', 'k', 'ra', 'rb', 'rc']",
        "ok  F2 everything granted EXCEPT j                             OPEN      F until-verification weak=['j']"]),
    ("dilemmas/hume_guillotine.py", [
        "ok  F1 is -> ought, fact granted: nothing is delivered       OPEN      F until-verification weak=['o']",
        "ok  F2 bridge in place: bare modus ponens, earned            EARNED    T hereditary         weak=['d', 'o']"]),
    ("dilemmas/cogito.py", [
        "ok  F1 t -> i, thinking granted: no delivery                 OPEN      F until-verification weak=['i']",
        "ok  F2 bridge in place: bare modus ponens, earned            EARNED    T hereditary         weak=['i', 't']"]),
    ("dilemmas/theseus.py", [
        "ok  step 0: material T (ledger)       structural T (witness re-checked)",
        "ok  step 1: material F (culprit n0)   structural T (witness re-checked)"]),
    ("dilemmas/agrippa_nullary.py", ["AGRIPPA-NULLARY GREEN",
                        "UNDERDETERMINED  settings=2",
                        "INTRINSIC        settings=1",
                        "withdraw the act      : REFUSED",
                        "declared_structural: ['performed/my-favourite-axiom']"]),
    ("dilemmas/agrippa_book.py", ["AGRIPPA-BOOK GREEN",
                        "the last resting on nothing: {'ON CREDIT': 5}",
                        "blast radius of that one document: 5 of 5",
                        "retract doc5b   -> [5, 5] of 5",
                        "blast radius of each document: [(1, 1), (1, 1), (1, 1), (1, 1), (1, 1)]",
                        "take BOTH grounds under the bottom claim: ['v5'] moves",
                        "the strict reading of the web IS the tower",
                        "retract the original: nothing falls"]),
    ("dilemmas/epoch_line.py", ["EPOCH-LINE GREEN",
                        "the assertion, over all 9 markings: ['REFUTED']",
                        "with earned costs FROZEN — no expire allowed: 1 distinct answers, [100]",
                        "moore            single-marking",
                        "surprise exam    verify-only",
                        "berry            needs-expire"]),
    ("dilemmas/moore.py", ["MOORE GREEN",
                           "'it is raining but I do not believe it'  : 1 of 9",
                           "'raining, and I do not believe it', asserted: 0 of 9",
                           "omissive, over all 9 markings   : ['REFUTED']",
                           "the surviving marking(s): [{'p': 'T', 'bp': 'T', 'bt': 'F'}]"]),
    ("dilemmas/lottery.py", ["LOTTERY GREEN",
                             "5 losses believed: 'some ticket wins' -> REFUTED",
                             "credit & credit : OPEN"]),
    ("dilemmas/berry.py", ["BERRY GREEN",
                           "100 -> 107 -> 170 -> 177",
                           "E — no number left unnamed"]),
    ("dilemmas/omnipotence.py", ["OMNIPOTENCE GREEN",
                                 "'a stone heavier than an unlimited capacity': REFUTED",
                                 "liftable_by_him             : PARADOX",
                                 "'a capacity both unlimited and exceeded': E"]),
    ("dilemmas/ought_can.py", ["OUGHT_CAN GREEN",
                               "'filed by the 10th?': OPEN",
                               "a compliant date exists for each half alone: True and True",
                               "'save both, with means for one': REFUTED"]),
    ("dilemmas/lifeline.py", ["LIFELINE GREEN",
                              "All three are consistent",
                              "who is it, checkable = False",
                              "'one bearer persists'       : OPEN",
                              "CONTEST TYPE",
                              "'I am alive' (a claim about now)        : until-verification"]),
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
    ("zclassify.py",   ["genres present among the classified cases: ['loop']",
                        "docket complete — every row pinned",
                        "Kripke transported, total",
                        "barber = Grelling = R∈R = liar",
                        "suspended ⊥ ⇒ DOWNSTREAM"]),
]


def _run_one(item):
    script, markers = item
    # ZTL_SUITE tells a stand it is running inside the suite rather than by
    # hand. Only one stand reads it so far — conformance/judge_table.py,
    # which spreads its sweep over every core standalone and takes a single
    # process here, because the suite already saturates the machine and the
    # sweep is well off its critical path. A stand that forks 32 workers
    # inside a 30-way pool fights the run it belongs to.
    r = subprocess.run([sys.executable, script], env=dict(os.environ,
                       ZTL_SUITE="1"),
                       capture_output=True, text=True, timeout=900)
    # A stand may SKIP when an optional third-party backend is absent (the
    # quantum probes need qiskit-aer). A skip is NOT a pass: it is reported
    # separately, its markers are not claimed, and the summary says how many
    # stands actually ran. It is also not a failure — an unavailable device
    # is not a refuted theorem.
    # ONE EXIT, deliberately. This function used to return early on the skip
    # path, and when `why` was added to the normal path the two shapes
    # diverged — 4 values against 5. The suite then died with
    # `ValueError: not enough values to unpack` the moment a stand actually
    # skipped, which never happens on the author's machine (qiskit-aer is
    # installed here) and always happens on CI, where it is not. The change
    # that made CI failures legible was the change that broke CI. A single
    # exit makes that particular divergence unrepresentable.
    missing, why = [], ""
    if r.returncode == 0 and "SKIPPED" in r.stdout:
        # A skip is NOT a pass: it is reported separately, its markers are not
        # claimed, and the summary says how many stands actually ran. It is
        # also not a failure — an unavailable device is not a refuted theorem.
        ok = "skip"
    else:
        missing = [m for m in markers if m not in r.stdout]
        ok = r.returncode == 0 and not missing
        # WHY, not only WHAT. Three times a stand went red on CI while passing
        # here, and the report said which markers were absent and nothing
        # about the cause — so the author guessed, twice wrongly, at a machine
        # he cannot open. When a stand fails, its last stderr line goes with
        # the verdict: an exception type and message is usually the whole
        # diagnosis, and it costs nothing to carry.
        if not ok:
            tail = [ln for ln in (r.stderr or "").strip().splitlines()
                    if ln.strip()]
            if tail:
                why = tail[-1][:200]
            elif not r.stdout.strip():
                why = "no output at all"
    return script, ok, missing, r.returncode, why


def _selftest_runner():
    """The runner runs the stands; nothing ran the runner.

    `_run_one` has three outcomes — pass, fail, skip — and the SKIP branch is
    dead code on the author's machine, where every optional backend is
    installed. It was therefore the branch that broke: it kept returning a
    4-tuple after the other two grew a fifth field, and the suite died on CI
    with `ValueError: not enough values to unpack` in the middle of a run.
    Green here, red there, and the cause invisible from here.

    So the branch that cannot fire locally is fired deliberately, on two
    throwaway scripts, before the real run. It costs a fraction of a second
    and it is the only part of this file that tests this file.
    """
    import tempfile
    cases = [("print('SKIPPED — no backend')", "skip"),
             ("import sys; sys.exit('boom')", False),
             ("print('MARKER HERE')", True)]
    d = tempfile.mkdtemp()
    for i, (src, want) in enumerate(cases):
        p = os.path.join(d, f"case{i}.py")
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(src + "\n")
        got = _run_one((p, ["MARKER HERE"]))
        assert len(got) == 5, (
            f"_run_one returned {len(got)} values for the "
            f"{'skip' if want == 'skip' else want} case, not 5 — the bug that "
            f"crashed CI on 2026-08-17")
        _script, ok, _missing, _rc, _why = got
        assert ok == want, f"expected {want!r} for case{i}, got {ok!r}"
        os.unlink(p)
    os.rmdir(d)


def main():
    """Flags, because a full pass costs about two minutes and most edits
    touch one stand: `--only <substring>` runs the matching stands (and
    skips Lean unless a Lean file is what changed), `--no-lean` drops the
    `lake build`. No flag = everything, which is what a commit deserves."""
    _selftest_runner()
    argv = sys.argv[1:]
    pattern = None
    if "--only" in argv:
        pattern = argv[argv.index("--only") + 1]
    skip_lean = "--no-lean" in argv or pattern is not None
    if pattern:
        # `a|b` selects either, because the stands one wants to re-check after
        # a change are rarely a common substring.
        pats = pattern.split("|")
        globals()["STANDS"] = [(s_, m) for s_, m in STANDS
                               if any(p in s_ for p in pats)]
        if not STANDS:
            print(f"no stand matches {pattern!r}")
            return 1
    # A LISTED STAND MUST BE IN THE REPOSITORY. Learned 2026-08-13 from a
    # red CI run nobody could reproduce: `dilemmas/cogito.py` was wired into
    # this list after checking that it RAN, which it did — from the author's
    # working tree, where it had sat untracked for months. On a clean
    # checkout the file simply is not there, so the runner was green here and
    # red on GitHub, which is precisely the assurance this project refuses to
    # grant itself. Green on one machine is not a result; this check makes
    # the runner say so.
    import subprocess as _sp
    _tracked = set(_sp.run(["git", "ls-files"], capture_output=True,
                           text=True).stdout.split())
    if _tracked:                      # empty when run outside a git checkout
        _absent = [s for s, _m in STANDS if s not in _tracked]
        if _absent:
            print(f"RED: stands listed but not in the repository: {_absent}")
            print("     They may run here and cannot run anywhere else.")
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
            script, ok, missing, rc, why = fut.result()
            results[script] = (ok, missing, rc, why)
            print(f"\r    {done}/{total} stands finished…", end="", flush=True)
    print()
    skipped = []
    for script, _markers in STANDS:
        ok, missing, rc, why = results[script]
        status = "SKIP" if ok == "skip" else ("OK " if ok else "FAIL")
        print(f"  [{status}] {script}"
              + ("  — optional backend absent; nothing claimed"
                 if ok == "skip" else "")
              + (f"  — missing markers: {missing}" if missing else "")
              + (f"  — exit code {rc}" if rc else "")
              + (f"\n           why: {why}" if why else ""))
        if ok == "skip":
            skipped.append(script)
        elif not ok:
            # THE SUMMARY CARRIES THE DIAGNOSIS, not just the name. Three
            # times on 2026-08-16 a red CI was reported by pasting the tail
            # of the log, which held `RED: ['db/probe_ledger.py']` and
            # nothing else — the missing marker was hundreds of lines above,
            # in stand order. A summary that says WHICH stand failed and not
            # WHY sends the reader back up a log they have already scrolled
            # past, and on somebody else's machine there may be no log left
            # to scroll. The failure line must be self-sufficient.
            reason = why or (f"missing {missing}" if missing
                             else f"exit code {rc}" if rc else "unknown")
            failures.append(f"{script} ({reason})")

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
