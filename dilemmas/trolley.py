# -*- coding: utf-8 -*-
"""trolley — the trolley problem under warrant grades: two earned-feeling bridges, a refuted pair.

Foot (1967), Thomson (1976, 1985). A runaway trolley will kill five; pulling a lever diverts it onto a track where it
kills one (SWITCH). Variant (FOOTBRIDGE): the five are saved only by pushing a large man off a bridge into the
trolley's path. Most people say "pull" in SWITCH and "don't push" in FOOTBRIDGE, with the same five-against-one count.
This stand does not argue for an answer. It runs the skeleton and reads the warranty.

  ATOMS (stated in words first; the skeleton is ours, and a bad skeleton refutes only a straw man).
    f  = "if nothing is done, the five die"            (a FACT of the case: a forecast)
    k  = "if the lever is pulled, the one dies"        (a FACT of the case: a forecast)
    m  = "the one's death is the MEANS of the rescue"  (a FACT about the causal structure: F in SWITCH, T in FOOTBRIDGE)
    u  = the COUNTING bridge: "where an act ends in fewer deaths, it ought to be done"           (a norm)
    dk = the DOING bridge:    "where an act kills someone, it ought not be done"                (a norm)
    o  = "the lever ought to be pulled" (in FOOTBRIDGE: "the man ought to be pushed")           (the conclusion)

  WHAT THE MEASUREMENTS SAY (each pinned below):

  F1  THE ARITHMETIC IS EARNED ONLY INSIDE THE STORY. "1 < 5" with the counts granted by the
      story is EARNED. With the same counts held as forecasts it is ON CREDIT (toward T): the
      verdict rides on two documents nobody has checked. With the forecast honestly widened
      ("the five may escape": 0..5 deaths) it is OPEN, and the judge's next check is to MEASURE
      the five. The thought experiment's certainty is a stipulation, and it carries the arithmetic.

  F2  NO DELIVERY FROM THE FACTS. f -> o with f granted stays OPEN, weak link o (Hume; see
      hume_guillotine.py). Five against one, by itself, says nothing about the lever.

  F3  THE TWO BRIDGES ARE A REFUTED PAIR. Each bridge alone is a usable principle. Together,
      on the SWITCH facts, they demand o and not-o: REFUTED IF STABLE (stable = "the lever"
      means the same act in both). The trolley problem in ZTL is not "which answer is right";
      it is a proof that the two bridges cannot both be held with these facts. The address is
      the PAIR (u, dk), and the agent who fails one of them has not failed: the defect is in
      the bridge set, as in ought_can.py section 3.

  F4  THE COUNT CANNOT SPLIT SWITCH FROM FOOTBRIDGE. On the counting bridge alone, "pull in
      SWITCH and do not push in FOOTBRIDGE" is REFUTED IF STABLE: same count, same verdict. So
      the common split of intuitions needs an atom the count does not contain. The judge names it:
      once the bridge is written so that it does not cover a death used as a means (u & f & ~m),
      the FOOTBRIDGE conclusion is no longer delivered (weak link o_fb). The split lives in m and
      in the norm that reads m (double effect, Kant's means-formula). It is not in the arithmetic.

  F5  THE CEILING IS FROZEN. The facts are witnessable (f, k: Z_REDEEMABLE_STABLE); the bridges
      and the ought are not (u, dk, o: Z_PERMANENT). The two-bridge package: earned futures 0 of
      4, refuted 4 of 4. The counting bridge alone: earned 0 of 2. No verdict on the lever is ever
      EARNED; what IS earned is the impossibility of holding both bridges (F3) and the
      insufficiency of the count (F4).

HONEST SCOPE. The atoms are ours, and every result is relative to them. F3 is the familiar
"conflict of principles" put through the judge; what the judge adds is that it is a proof with
an address (the bridge pair), not a mood. F4 matches the literature's diagnosis (doctrine of
double effect; Thomson's "using") and contributes only the measurement that the count alone
cannot carry the split. "Norms are unwitnessable" is a stipulation of the operational register
(as in hume_guillotine.py), recorded, not proved.

AI participation: written by Claude (Anthropic) at the curator's request (Vitaly Reznik, 2026-11-10).

Run:  python3 dilemmas/trolley.py        (asserts every measurement)
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztljudge import judge                                  # noqa: E402
from zredeem import stamp, ceiling                          # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities   # noqa: E402

TWO_BRIDGES = "((u & f) -> o) & ((dk & k) -> ~o) & u & dk & f & k"


def expect(label, formula, marking, disp, verdict, grade, weak):
    r = judge(formula, marking)
    got = (r["disposition"], r["verdict"], r["grade"], sorted(r["unverified"]))
    want = (disp, verdict, grade, sorted(weak))
    ok = got == want
    print(f"{'ok ' if ok else 'FAIL'} {label:<58} {got[0]:<17} {got[1]} {got[2]:<18} weak={got[3] or '—'}")
    assert ok, f"{label}: expected {want}, got {got}"


def expect_num(label, sheet, claim, disp, polarity=None):
    q, m = parse_quantities(sheet)
    r = judge_sheet_claim(claim, q, m)
    ok = r["disposition"] == disp and (polarity is None or r.get("polarity") == polarity)
    print(f"{'ok ' if ok else 'FAIL'} {label:<58} {r['disposition']:<10} "
          f"{r.get('polarity') or ''}  next: {r.get('next_check') or '—'}")
    assert ok, f"{label}: got {r['disposition']} / {r.get('polarity')}"


def run():
    print("TROLLEY. TWO BRIDGES, ONE LEVER: THE PAIR, REFUTED")
    print("=" * 72)

    print("\n### F1. The arithmetic: earned in the story, on credit in the world")
    expect_num("deaths if pulled < deaths if not, counts GIVEN by the story",
               "dn=5 earned:story, dp=1 earned:story", "dp < dn", "EARNED")
    expect_num("the same counts held as FORECASTS",
               "dn=5 credit, dp=1 credit", "dp < dn", "ON CREDIT", "toward T")
    expect_num("the forecast widened: the five may escape (0..5)",
               "dn=[0,5] credit int, dp=1 credit int", "dp < dn", "OPEN")

    print("\n### F2. Five against one delivers no ought")
    expect("f -> o, the fact granted", "f -> o", {"f": "T"},
           "OPEN", "F", "until-verification", ["o"])

    print("\n### F3. The counting bridge and the doing bridge: a refuted pair")
    expect("both bridges + SWITCH facts, nothing granted", TWO_BRIDGES, None,
           "REFUTED IF STABLE", "F", "hereditary", ["dk", "f", "k", "o", "u"])
    expect("   facts granted", TWO_BRIDGES, {"f": "T", "k": "T"},
           "REFUTED IF STABLE", "F", "hereditary", ["dk", "o", "u"])
    expect("   facts and both bridges granted: only 'same lever' remains", TWO_BRIDGES,
           {"u": "T", "dk": "T", "f": "T", "k": "T"},
           "REFUTED IF STABLE", "F", "hereditary", ["o"])
    expect("the impossibility itself, as a claim",
           "~((u & f & dk & k) & (((u & f) -> o) & ((dk & k) -> ~o)))", None,
           "EARNED IF STABLE", "T", "hereditary", ["dk", "f", "k", "o", "u"])

    print("\n### F4. The count cannot split SWITCH from FOOTBRIDGE")
    expect("counting bridge: pull in SWITCH, don't push in FOOTBRIDGE",
           "((u & f) -> o_sw) & ((u & f) -> o_fb) & u & f & o_sw & ~o_fb", {"u": "T", "f": "T"},
           "REFUTED IF STABLE", "F", "hereditary", ["o_fb", "o_sw"])
    expect("bridge excluding a death used as a MEANS, m granted",
           "((u & f & ~m) -> o_fb) & u & f & m", {"u": "T", "f": "T", "m": "T"},
           "EARNED", "T", "hereditary", ["o_fb"])
    print("ok  the split is carried by m and the norm that reads it — not by the count")

    print("\n### F5. Redeemability: the ceiling")
    marking = {a: "Z" for a in ("u", "dk", "f", "k", "o")}
    OBSERVABLE = {"f", "k"}          # forecasts can be checked; bridges and oughts cannot
    for a in ("f", "k", "u", "dk", "o"):
        print(f"ok  stamp({a}) = {stamp(a, marking, OBSERVABLE)}")
    assert stamp("f", marking, OBSERVABLE) == "Z_REDEEMABLE_STABLE"
    assert stamp("k", marking, OBSERVABLE) == "Z_REDEEMABLE_STABLE"
    for a in ("u", "dk", "o"):
        assert stamp(a, marking, OBSERVABLE) == "Z_PERMANENT"
    c = ceiling(TWO_BRIDGES, marking, OBSERVABLE)
    print(f"ok  two-bridge package: frozen={sorted(c['frozen'])}, earned={c['earned_futures']}/{c['futures']}, "
          f"refuted={c['refuted_futures']}/{c['futures']}")
    assert c["ceiling_frozen"] and c["earned_futures"] == 0 and c["refuted_futures"] == c["futures"]
    c1 = ceiling("((u & f) -> o) & u & f & o", {a: "Z" for a in ("u", "f", "o")}, {"f"})
    print(f"ok  counting bridge alone: earned={c1['earned_futures']}/{c1['futures']}, "
          f"refuted={c1['refuted_futures']}/{c1['futures']}")
    assert c1["ceiling_frozen"] and c1["earned_futures"] == 0

    print("\nTROLLEY: all measurements hold.")
    print("The count is earned only inside the story; five against one delivers")
    print("no ought; the counting and the doing bridges cannot both be held on")
    print("these facts, and that is a proof with an address, not a verdict on the")
    print("agent; the count cannot tell the lever from the push, so the common")
    print("split lives in 'means', not in arithmetic; and no answer on the lever")
    print("is ever earned. What is earned is the shape of the disagreement.")
    return 0


if __name__ == "__main__":
    sys.exit(run())
