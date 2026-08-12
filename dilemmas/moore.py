# -*- coding: utf-8 -*-
"""
Moore's paradox: a sentence that is consistent and cannot be said.

    "It is raining, but I do not believe that it is raining."

Nothing is contradictory here. The world contains people it is true of —
it rains, and they do not believe it. A third party can say it about you
without a stumble, and you can say it about your past self. Yet you cannot
assert it now, in your own mouth, and no one has ever been able to say what
rule is broken. Moore (1942) posed it; Wittgenstein thought it mattered
more than anything else in Moore.

The machine takes it because the puzzle lives exactly on this corpus's
seam: the difference between what is TRUE and what is EARNED. Two
instruments, and they disagree by construction.

MEASURED HERE:

  1. as a state of affairs the sentence is fine: of the nine markings over
     its two atoms, one designates it — the same score as any ordinary
     contingent conjunction, and unlike a real contradiction, which scores
     zero. The logic has no complaint;
  2. add ONE bridge — that asserting p requires a witness for p, which is
     what believing p reports — and the count drops to zero of nine. Not
     unproven: REFUTED, in every marking. The assertion kills itself;
  3. and the bridge is not invented for the case. It is this corpus's
     standing rule, "no truth on credit", the same one that costs us the
     identity law. Moore's sentence is the first-person instance of it;
  4. there is no gentler form. Both the omissive and the commissive die
     REFUTED in EVERY marking, and "my belief is not settled yet" does not
     rescue anything — our own axiom NOT(Z) = F makes "I do not believe it"
     false when the belief is merely unsettled, since non-belief cannot be
     claimed on credit either. This refutes a prediction made before the
     run and is harsher than the literature: not odd, not unassertable —
     false, whatever you do;
  5. the escape is measured, and it is UNIQUE. Put the belief in another
     epoch ("it rained and I did not believe it") and the sentence is
     assertable again — in exactly ONE marking of twenty-seven, the one
     where you believe it NOW and did not believe it THEN. The bridge does
     not stop binding; it binds the present belief and leaves the past one
     alone. That is why only the first-person present is defective — the
     epoch boundary of §§21-23, met from a third direction after the liar
     and after Berry.

WHAT THIS IS NOT: news. That Moore's puzzle concerns assertion rather than
truth is the standard reading, from Wittgenstein through Shoemaker and
Heal. The corpus adds no thesis about belief. What it adds is that the
assertion rule did not have to be imported — it was already the machine's,
and the case falls out of the ledger instead of being installed in it.

Run:  python3 dilemmas/moore.py
"""
import os
import sys
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                ".."))

from ztl import T, F, Z                                         # noqa: E402
from ztljudge import judge                                      # noqa: E402

VALUES = (T, F, Z)

# p   — it is raining
# bp  — I believe it is raining
# bn  — I believe it is NOT raining
# bt  — I believed it, back then (a different epoch, same person)
OMISSIVE = "p & ~bp"                 # the classic form
COMMISSIVE = "p & bn"                # "it is raining but I believe it is not"
PAST = "p & ~bt"                     # "it rained and I did not believe it"

# The bridge. To assert p you must hold a witness for p; holding one is
# what "I believe p" reports. Written as an implication, it is the
# corpus's own rule of no-credit, in the first person and the present.
ASSERT = "(p -> bp)"
ASSERT_N = "(bn -> ~p)"              # the same rule applied to the other belief


def designated(formula, atoms):
    """How many of the markings over these atoms designate the formula —
    the ordinary satisfiability count, with no talk of warranty."""
    n = 0
    for combo in product(VALUES, repeat=len(atoms)):
        m = dict(zip(atoms, combo))
        if judge(formula, m)["verdict"] == T:
            n += 1
    return n


def sec1_the_sentence_is_innocent():
    print("-" * 72)
    print("1. AS A DESCRIPTION OF THE WORLD, NOTHING IS WRONG WITH IT")
    moore = designated(OMISSIVE, ["p", "bp"])
    plain = designated("p & ~q", ["p", "q"])
    contra = designated("p & ~p", ["p"])
    print(f"   'it is raining but I do not believe it'  : {moore} of 9")
    print(f"   an ordinary conjunction, p & ~q          : {plain} of 9")
    print(f"   an actual contradiction, p & ~p          : {contra} of 3")
    assert moore == plain == 1 and contra == 0
    print("   Moore's sentence scores exactly what a plain contingent")
    print("   conjunction scores, and a contradiction scores zero. So the")
    print("   defect is NOT logical form: there are people it is true of,")
    print("   and a third party can say it about them without a stumble.")


def sec2_one_bridge_and_it_dies():
    print("-" * 72)
    print("2. NOW SAY IT YOURSELF — ADD THE ASSERTION RULE")
    print(f"   the bridge: {ASSERT}  — to assert p you must hold a witness")
    print("   for p, and holding one is what 'I believe p' reports.")
    with_bridge = designated(f"{ASSERT} & {OMISSIVE}", ["p", "bp"])
    print(f"   'raining, and I do not believe it', asserted: "
          f"{with_bridge} of 9")
    r = judge(f"{ASSERT} & {OMISSIVE}", {"p": T, "bp": F})
    print(f"   the one marking that used to work (p=T, bp=F): "
          f"{r['disposition']}")
    assert with_bridge == 0 and r["disposition"] == "REFUTED"
    print("   Zero. And REFUTED, not merely unproven: there is no marking")
    print("   left, no witness that could be produced, no cure. The sentence")
    print("   survives every test the world can give it and dies the moment")
    print("   its speaker is the one making the claim.")


def sec3_the_bridge_was_already_ours():
    print("-" * 72)
    print("3. AND THE BRIDGE IS NOT AN EXTRA ASSUMPTION")
    print("   It is the corpus's standing rule, in the first person: a")
    print("   designated claim needs a witness, no truth on credit. The")
    print("   same rule that costs us the identity law — measured in")
    print("   zsweep, where NO arrow keeps p -> p and refuses credit.")
    both = f"{ASSERT} & {ASSERT_N} & {COMMISSIVE}"
    naked = designated(COMMISSIVE, ["p", "bn"])
    dressed = designated(both, ["p", "bn"])
    print(f"   commissive form, 'raining but I believe it is not':")
    print(f"     as a description  : {naked} of 9")
    print(f"     in your own mouth : {dressed} of 9")
    assert naked == 1 and dressed == 0
    # A PREDICTION THAT FAILED, kept because the refusal is the finding.
    # Expected: the omissive form would be the gentler one — a belief not
    # yet settled is something you can go and settle, so p=T with bp=Z
    # should come out OPEN with `bp` as the named check, against outright
    # refusal for the commissive. Measured over every marking of each:
    om_d = {judge(f"{ASSERT} & {OMISSIVE}", dict(zip(["p", "bp"], c)))
            ["disposition"]
            for c in product(VALUES, repeat=2)}
    com_d = {judge(both, dict(zip(["p", "bn"], c)))["disposition"]
             for c in product(VALUES, repeat=2)}
    soft = judge(f"{ASSERT} & {OMISSIVE}", {"p": T, "bp": Z})
    print(f"   omissive, over all 9 markings   : {sorted(om_d)}")
    print(f"   commissive, over all 9 markings : {sorted(com_d)}")
    print(f"   the hoped-for soft case (p=T, bp=Z): {soft['disposition']}"
          f", named check {sorted(soft['unverified'])}")
    assert om_d == com_d == {"REFUTED"}
    print("   The prediction failed, and the refusal is worth more than the")
    print("   prediction was. There is no gentler form: both die REFUTED in")
    print("   every marking, and 'my belief is not settled yet' does not")
    print("   help. The reason is our own axiom, NOT(Z) = F — an unsettled")
    print("   belief makes 'I do not believe it' FALSE, because non-belief")
    print("   cannot be claimed on credit either. The judge still names the")
    print("   check `bp`, which is honest and useless here: verifying it")
    print("   cannot rescue a formula that is already refuted.")
    print("   So the corpus is harsher on Moore than the literature is. It")
    print("   does not say the sentence is odd, or unassertable, or")
    print("   pragmatically self-defeating. It says: false, whatever you do.")


def sec4_the_escape_is_an_epoch():
    print("-" * 72)
    print("4. WHY THE PAST TENSE IS FINE — MEASURED")
    print("   'It was raining and I did not believe it' is unremarkable.")
    print("   The bridge binds the belief of the SPEAKER AT THE MOMENT OF")
    print("   SPEAKING; the belief reported here belongs to another epoch,")
    print("   so the rule does not reach it.")
    atoms = ["p", "bp", "bt"]
    past = designated(f"{ASSERT} & {PAST}", atoms)
    survivors = [dict(zip(atoms, c)) for c in product(VALUES, repeat=3)
                 if judge(f"{ASSERT} & {PAST}", dict(zip(atoms, c)))
                 ["verdict"] == T]
    print(f"   'it rained and I did not believe it', asserted now: "
          f"{past} of {3 ** 3}")
    print(f"   and the surviving marking(s): {survivors}")
    assert past == 1 and survivors == [{"p": T, "bp": T, "bt": F}]
    print("   Back from zero — but by exactly ONE route, and the machine")
    print("   picked it out without being told: you may say it only if you")
    print("   believe it NOW and did not believe it THEN. Which is the")
    print("   English sentence, exactly as people use it. (A second guess")
    print("   said three markings, on the thought that the present belief")
    print("   would be left free. It is not: the bridge still binds it.)")
    print("   So the defect was never in the words and never in the logic:")
    print("   it is the coincidence of the epoch of the ASSERTION with the")
    print("   epoch of the BELIEF.")
    print("   That is the epoch boundary of §§21-23, reached now from a")
    print("   third direction: the liar found it in self-reference, Berry")
    print("   in definition, Moore in the first person.")


def sec5_what_is_not_claimed():
    print("-" * 72)
    print("5. WHAT IS NOT CLAIMED")
    print("   No news about belief. That Moore's puzzle is about assertion")
    print("   and not about truth is the standard reading — Wittgenstein")
    print("   first, then Shoemaker and Heal — and nothing above improves")
    print("   on it.")
    print("   One place the corpus does say MORE, and it should be read as")
    print("   a fact about our register rather than about Moore: the")
    print("   literature calls the sentence absurd, unassertable, or")
    print("   pragmatically self-defeating while granting it could be true.")
    print("   Here, with the no-credit bridge in force, it is FALSE in every")
    print("   marking. That is stronger, and it is bought — the price was")
    print("   paid at NOT(Z) = F, long before Moore came up. A register that")
    print("   allowed truth on credit would give the softer verdict.")
    print("   The one thing the corpus can say is procedural: the assertion")
    print("   rule was not imported for this case. It is the same no-credit")
    print("   rule the whole system is built on, and the case falls out of")
    print("   the ledger rather than being installed in it. A machine that")
    print("   separates TRUE from EARNED gets Moore for free — which is a")
    print("   fact about the machine, not a discovery about the mind.")


if __name__ == "__main__":
    print("=" * 72)
    print("MOORE — consistent, and unsayable")
    print("=" * 72)
    sec1_the_sentence_is_innocent()
    sec2_one_bridge_and_it_dies()
    sec3_the_bridge_was_already_ours()
    sec4_the_escape_is_an_epoch()
    sec5_what_is_not_claimed()
    print("=" * 72)
    print("MOORE GREEN — the sentence scores exactly what a plain contingent")
    print("conjunction scores, so its form is innocent; add the one rule")
    print("that asserting p needs a witness for p and it is REFUTED in every")
    print("marking, with no cure. Omissive and commissive die alike, and an")
    print("unsettled belief does not soften either, because NOT(Z) = F. The")
    print("past tense is measured back to satisfiable by exactly ONE marking —")
    print("believe it now, did not believe it then — which locates the")
    print("defect exactly: not in the words, in the epoch shared by the")
    print("assertion and the belief.")
