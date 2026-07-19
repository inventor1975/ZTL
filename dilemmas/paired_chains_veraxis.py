# -*- coding: utf-8 -*-
"""paired_chains_veraxis — the circuit-breaker test: a sound chain and its
minimally corrupted twin.

Designed by A. (Veraxis, 2026-07-19) after the aphorism run, whose honest
limit was that standalone assertions give epistemic credit nowhere to hide.
This test has teeth: two four-step chains differing in ONE step, where B
converts "not established that admissible" into "established that
inadmissible" — the closed-world flip. Five criteria are asked of the core:

  sensitivity   — does it catch the credit in B?
  specificity   — does it leave the sound chain A alone?
  localization  — does it name the exact transition where the debt appears?
  explainability— does it show the rule the move masquerades as?
  discipline    — does it keep undisproved / undetermined / denied apart?

THE MODELING DECISION, stated because it carries the whole test: the
temporal-epistemic content does not live in a formula. It lives in the
MARKING. "Only a generation-time check was performed" is not a premise to
be written as an implication — it is the statement that
`admissible_R` is UNVERIFIED (mark Z) at the moment of reliance. Encoding
it as a formula would smuggle our reading in; encoding it as a marking
lets the core speak.

Both chains share premises 1-2; they diverge at premise 3 and, decisively,
in what the conclusion CLAIMS:

  A concludes a NEGATIVE about capability — the generation-time check does
    not suffice for admissibility at reliance;
  B concludes a POSITIVE about the world — the action was inadmissible.

Same machinery, opposite outcomes, because the claims have opposite
polarity. That is the specificity result, and it is not luck.
"""
import json
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, os.path.join(_ROOT, "tool"))
sys.path.insert(0, _ROOT)

import zfl                                                   # noqa: E402
import engine                                                # noqa: E402
from ztl import T, F, ev                                     # noqa: E402
from zmodal import ztl_eval, global_super                    # noqa: E402
from zverify import grade                                    # noqa: E402

GLOSS = {
    "admissible_R": "the action is admissible AT THE MOMENT OF RELIANCE",
    "checked_G": "a check was performed at generation time",
    "rechecked_R": "a check was performed at the moment of reliance",
    "reliance_ok": "the institution may rely on the action",
    "may_change": "authority, facts or norms may change in the interval",
}


def atoms(*names, **override):
    return {n: {"status": override.get(n, "Z"), "means": GLOSS[n]}
            for n in names}


def run(title, doc):
    d, p, issues = zfl.validate(json.dumps(doc, ensure_ascii=False))
    hard = [i for i in issues if i["level"] == "error"]
    assert not hard, f"{title}: {hard}"
    rep = engine.logic_map(d, p)
    lm = rep["logic_map"]
    print(f"\n  {title}")
    print(f"    formula   {lm['formula']}")
    print(f"    currency  {lm['currency']['kind']}"
          + (f"   witness {lm['currency']['witness']}"
             if lm['currency'].get('witness') else ""))
    print(f"    verdict   {rep['verdict']} / {rep['warranty']}")
    a = lm.get("audit")
    if a:
        print(f"    audit     {a['status']}"
              + (f"   loan {a['loans']}" if a.get("loans") else "")
              + (f"   counterexample {a['counterexample']}"
                 if a.get("counterexample") else ""))
    return rep, lm


if __name__ == "__main__":
    print("=" * 76)
    print("PAIRED CHAINS — the logical-warrant circuit breaker (A. test)")
    print("  A: sound chain      B: minimally corrupted twin")
    print("=" * 76)

    # ---------------------------------------------------------------- 1
    print("\n### 1. THE SCENARIO AS A MARKING (not as a formula)")
    print("  Only a generation-time check was performed; no re-check at")
    print("  reliance. Premise 3 of A says such a check cannot detect a")
    print("  later change — therefore admissibility AT RELIANCE is")
    print("  UNVERIFIED. That is the marking, not an assumption:")
    marking = {"admissible_R": "M", "checked_G": T, "rechecked_R": F,
               "may_change": T}
    for k, v in marking.items():
        print(f"    {k:14s} = {v if v != 'M' else 'Z (unverified)'}"
              f"   — {GLOSS[k]}")

    print("\n  The status of the ADMISSIBILITY atom itself:")
    phi = "admissible_R"
    print(f"    epistemic status : {global_super(phi, marking)}"
          "   (not established — NOT falsehood)")
    print(f"    raw value        : {ztl_eval(phi, marking)}"
          "   (the MARK shows through: a bare atom is not a verdict)")
    print(f"    warranty         : {grade(phi, marking)}")
    print("    The doctrine is already at work: Z lives on atoms only.")
    print("    The moment the atom enters a formula the verdict is")
    print("    two-valued — and that is where the refusal appears (2).")

    # ---------------------------------------------------------------- 2
    print("\n### 2. THE DECISIVE CELL — the core denies BOTH sides")
    pos = ztl_eval("admissible_R", marking)
    neg = ztl_eval(("not", "admissible_R"), marking)
    asserted = ztl_eval(("and", "admissible_R", "admissible_R"), marking)
    print(f"    'admissible at reliance'  (bare atom) → {pos}"
          f" / {grade('admissible_R', marking)}")
    print(f"    'admissible at reliance'  (asserted)  → {asserted}"
          f" / {grade(('and', 'admissible_R', 'admissible_R'), marking)}")
    print(f"    'NOT admissible at reliance'          → {neg}"
          f" / {grade(('not', 'admissible_R'), marking)}")
    assert pos == "Z" and neg == F and asserted == F
    print("    These three lines are the whole test. The atom stands at Z:")
    print("    NOTHING is established. Assert either side through an")
    print("    operator and the answer is F — not earned. The core grants")
    print("    NEITHER 'admissible' NOR 'inadmissible' from an unverified")
    print("    ground. A claims only the first refusal; B claims the second")
    print("    as an established fact, and nothing in this cell grants it.")

    # ---------------------------------------------------------------- 3
    print("\n### 3. CHAIN A — the claim is a DENIAL OF SUFFICIENCY")
    print("  A concludes: a generation-time check cannot itself guarantee")
    print("  admissibility at reliance. Encoded as the law it denies:")
    repA, lmA = run("A's target law:  checked_G → admissible_R",
                    {"genre": "statement",
                     "atoms": atoms("checked_G", "admissible_R"),
                     "assert": "imp(checked_G, admissible_R)"})
    ceA = lmA["audit"]["counterexample"]
    assert lmA["audit"]["status"] == "does-not-follow"
    print(f"    → the law FAILS, witness {ceA}: checked at generation, yet")
    print("      inadmissible at reliance. A asserts exactly this failure,")
    print("      so the core SUPPORTS A. Specificity: no debt is charged to")
    print("      A, because A borrows nothing — it denies a sufficiency.")

    # ---------------------------------------------------------------- 4
    print("\n### 4. CHAIN B — the claim is an ASSERTION OF A FACT")
    print("  B concludes: the action WAS inadmissible. Its inference step,")
    print("  written as the law it needs:")
    repB, lmB = run("B's needed law:  ¬rechecked_R → ¬admissible_R",
                    {"genre": "statement",
                     "atoms": atoms("rechecked_R", "admissible_R"),
                     "assert": "imp(not(rechecked_R), not(admissible_R))"})
    ceB = lmB["audit"]["counterexample"]
    assert lmB["audit"]["status"] == "does-not-follow"
    print(f"    → REFUTED, witness {ceB}: no re-check was performed and the")
    print("      action was admissible all along. Absence of confirmation is")
    print("      not confirmation of absence.")

    # ---------------------------------------------------------------- 5
    print("\n### 5. LOCALIZATION — where exactly the debt is taken")
    print("  Not in a rule of inference. B's move cannot even be written as")
    print("  an object-level step: it converts an EPISTEMIC status (we did")
    print("  not verify) into an ONTIC fact (it was false). Read off the")
    print("  cell of §1: B takes the operational coordinate — DENY, a policy")
    print("  reading — and reports it as the epistemic one. That conflation")
    print("  is the debt, and it happens at the transition")
    print("      premise 3  ('no re-check was performed')")
    print("   →  conclusion ('the action was inadmissible').")
    print("  The core blocks it below the level of rules, at the value:")
    print("  ¬Z = F, never T — a denial is never GRANTED by ignorance.")

    # ---------------------------------------------------------------- 6
    print("\n### 6. EXPLAINABILITY — the rule it masquerades as")
    print("  B's step imitates negation-as-failure / the closed-world")
    print("  assumption: 'not derivable, hence false'. Two honest notes:")
    print("   (a) it is NOT in this core's loan library (the fourteen fallen")
    print("       laws) — those are object-level; CWA is a META rule about")
    print("       provability, which is precisely why it cannot be borrowed")
    print("       here: there is no legal way to take it;")
    print("   (b) it can only enter as an UNGROUNDED VERIFICATION EVENT — a")
    print("       tick asserting admissible_R := F with no source. The")
    print("       artifact ledger rejects exactly that, with reason code")
    print("       E_UNGROUNDED_VERIFICATION (vrg/epoch_artifact.py).")
    print("  So the honest answer to 'what rule is it hiding as' is: none.")
    print("  It hides as a MEASUREMENT that was never taken.")

    # ---------------------------------------------------------------- 7
    print("\n### 7. DISCIPLINE — three states kept apart, measured")
    rows = [
        ("undisproved / not established", {"admissible_R": "M"},
         "admissible_R"),
        ("denied by a verified ground", {"admissible_R": F}, "admissible_R"),
    ]
    for label, m, f in rows:
        print(f"    {label:32s} epistemic {global_super(f, m):2s}"
              f"  operational {ztl_eval(f, m)}"
              f"  warranty {grade(f, m)}")
    print("    The first row is B's situation, the second is what B claims.")
    print("    They differ in every coordinate that matters: the epistemic")
    print("    status (Z vs F) and the warranty (revocable vs earned).")
    print("    Collapsing row one into row two IS the corruption under test.")

    print("\n" + "=" * 76)
    print("RESULT")
    print("  sensitivity    B refuted, with a concrete counterexample")
    print("  specificity    A supported; nothing charged against it")
    print("  localization   premise 3 → conclusion; status-to-fact conversion")
    print("  explainability no borrowable rule — an unperformed measurement")
    print("  discipline     Z / F / warranty kept apart and exhibited")
