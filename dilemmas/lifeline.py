# -*- coding: utf-8 -*-
"""
Is the earthly god alive? The curator's dilemma, priced.

    None of us died when, after conception, the cell divided in two.
    Life on Earth began some four billion years ago as a cell, and the
    dividing has not stopped since. So is that first living thing alive
    today?

The curator's own report: he can find no contradiction in it. He is
right — and this stand says why, which is more useful than a verdict.
There is no contradiction because the argument is VALID under one
reading of identity, and its conclusion is simply the price of that
reading. What is hidden is not an error but a FORK.

MEASURED HERE:

  1. two words doing double duty. "Division" names one relation when a
     zygote cleaves — the two cells are PARTS of one organism, this is
     growth — and a different one when a bacterium divides, where the two
     cells are two organisms, and that is reproduction. The human case
     that actually matches the chain is not cleavage but identical
     TWINNING. And "did not die" is earned in the process sense (the
     living never stopped) while the conclusion needs the bearer sense
     (something one persists).
  2. the fork: THREE rules for fission, each consistent, each with its
     own bill.
       BOTH daughters inherit identity -> the god lives, and you and I
         are one individual;
       ONE daughter inherits it -> the god lives as some single lineage,
         and NOTHING can ever say which: an unpayable claim, the empty
         cure set again;
       NEITHER -> only the process continues, and your zygote was not
         you either.
     No contradiction anywhere. Three bills.
  3. and the ZTL cut, the same one this corpus has now measured three
     times: a premise earned in one sense is carried into a conclusion
     that needs another. The sorites did it with "the step fails" and
     "here is the cliff"; the surprise exam did it with a warranty
     belonging to somebody else's ledger; this does it with "did not
     die" and "is the same thing".

Run:  python3 dilemmas/lifeline.py
"""
import os
import sys
from itertools import product

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z                                       # noqa: E402
from ztljudge import judge                                    # noqa: E402
from zverify import grade                                     # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402


def sec1_the_dates_in_passing():
    print("-" * 72)
    print("1. THE NUMBERS, JUDGED IN PASSING")
    # the floor does its ordinary job on the figures the dilemma quotes
    q, m = parse_quantities(
        "earth=4.54 earned:radiometric-CAI Gyr, "
        "life_start=[3.5,4.1] earned:fossil-and-isotope Gyr, "
        "claimed=4.5 credit Gyr")
    r = judge_sheet_claim("claimed == life_start", q, m)
    print(f"   'life began 4.5 billion years ago': {r['disposition']}"
          f" {r['polarity']}   cure {r['next_check']}")
    print(f"     the earned window is [3.5, 4.1] Gyr — 4.54 is the age of")
    print(f"     the PLANET, not of life on it")
    # and note WHICH verdict the floor gives: the figure is refuted, but
    # the refutation rides the figure's own unwitnessed bound, so it is
    # capped — falsity is not taken on credit either (the rule added to
    # this corpus the day before this stand was written)
    assert r["disposition"] == "ON CREDIT" and r["polarity"] == "toward F"
    assert r["next_check"] == ["document claimed"]
    # cite the figure to a source and the cap lifts
    q1, m1 = parse_quantities(
        "life_start=[3.5,4.1] earned:fossil-and-isotope Gyr, "
        "claimed=4.5 earned:the-dilemma-as-stated Gyr")
    assert judge_sheet_claim("claimed == life_start",
                             q1, m1)["disposition"] == "REFUTED"
    r2 = judge_sheet_claim("life_start < earth", q, m)
    print(f"   'life is younger than the Earth': {r2['disposition']}")
    assert r2["disposition"] == "EARNED"
    print("   the slip changes nothing in the argument — but a judge that")
    print("   lets a number pass because the argument is interesting is not")
    print("   a judge. Noted and set aside.")


def sec2_one_word_two_relations():
    print("-" * 72)
    print("2. ONE WORD, TWO RELATIONS")
    print("   cleavage of a zygote : the two cells are PARTS of one organism")
    print("                          -> growth, one individual throughout")
    print("   division of a microbe: the two cells are TWO organisms")
    print("                          -> reproduction, one becomes two")
    print("   The chain from the first cell to today is made of the SECOND")
    print("   kind. The premise 'I did not die when my cell divided' is")
    print("   about the FIRST. The human case that really matches the chain")
    print("   is identical twinning — and that is exactly the case where")
    print("   nobody can say which twin is the original.")
    # and the second equivocation: alive-as-process vs alive-as-bearer
    process = judge("living_never_stopped",
                    {"living_never_stopped": "T"})
    bearer = judge("one_bearer_persists", {"one_bearer_persists": "Z"})
    print(f"   'the living never stopped'  : {process['disposition']}")
    print(f"   'one bearer persists'       : {bearer['disposition']}")
    assert process["disposition"] == "EARNED"
    assert bearer["disposition"] == "OPEN"
    print("   two atoms, not one. The argument earns the first and spends")
    print("   the second.")


def sec3_the_fork_by_model_count():
    print("-" * 72)
    print("3. THE FORK: THREE RULES FOR FISSION, NOT TWO")
    # The first draft of this stand offered two rules — identity survives
    # fission or it does not — and that is too coarse. There is a third,
    # and it is the one that saves the most: identity survives but passes
    # to AT MOST ONE successor (the closest-continuer view).
    #
    #   BOTH     both daughters inherit the identity. Transitivity then
    #            makes every living thing one individual.
    #   ONE      exactly one daughter inherits it. Some single lineage
    #            today IS the first cell — and nothing can say which.
    #   NEITHER  the individual ends at every fission; only the process
    #            continues.
    rules = {
        "BOTH   ": dict(god=True, persons_distinct=False, witnessable=True),
        "ONE    ": dict(god=True, persons_distinct=True, witnessable=False),
        "NEITHER": dict(god=False, persons_distinct=True, witnessable=True),
    }
    for name, r in rules.items():
        print(f"   {name}: earthly god alive = {str(r['god']):5}   "
              f"persons distinct = {str(r['persons_distinct']):5}   "
              f"who is it, checkable = {r['witnessable']}")
    # each rule is CONSISTENT — the dilemma contains no contradiction —
    # and each charges a different price
    assert all(isinstance(r["god"], bool) for r in rules.values())
    assert rules["BOTH   "]["persons_distinct"] is False
    assert rules["ONE    "]["witnessable"] is False
    assert rules["NEITHER"]["god"] is False
    print("   All three are consistent. The curator is right: there is no")
    print("   contradiction in the dilemma. There are three bills.")
    print()
    print("   And the judge has something to say about the middle one,")
    print("   which is the tempting escape — keep the god AND keep persons")
    print("   distinct by letting identity follow one branch:")
    r = judge("the_god_is_this_lineage",
              {"the_god_is_this_lineage": "Z"})
    print(f"     'THIS lineage is the original individual': "
          f"{r['disposition']} — verify {r['unverified']}")
    assert r["disposition"] == "OPEN"
    print("     and no act can verify it: the two daughters of every")
    print("     division are indistinguishable in every respect that could")
    print("     bear on which one 'continues' the parent. So the middle")
    print("     rule buys a god nobody can ever point at — the same shape")
    print("     as the brain in a vat, where the cure set is empty rather")
    print("     than unfinished. It is not refuted; it is unpayable.")


def sec4_the_cut():
    print("-" * 72)
    print("4. THE CUT, AND WHY IT LOOKS LIKE A PARADOX")
    r = judge("living_never_stopped & one_bearer_persists",
              {"living_never_stopped": "T", "one_bearer_persists": "Z"})
    print(f"   'the living never stopped AND one bearer persists': "
          f"{r['disposition']} — verify {r['unverified']}")
    assert r["disposition"] == "OPEN"
    assert r["unverified"] == ["one_bearer_persists"]
    print("   The feeling of paradox comes from a witnessed fact being")
    print("   spent on an unwitnessed identity. The chain of divisions is")
    print("   a fact with witnesses in the rock. 'One thing persists")
    print("   through it' is not a fact at all — it is a way of counting,")
    print("   and where the world does not count for us, we count for")
    print("   ourselves. Same shape as the heap's boundary and the")
    print("   surprise exam's stamp: this corpus keeps arriving at the")
    print("   same cell from different directions.")
    print("   What the judge refuses to do is choose the package. Where")
    print("   there is no ground there is no target — and this is where")
    print("   our freedom lives, which is the third time that capstone has")
    print("   turned up in a week.")


def sec5_two_storeys():
    print("-" * 72)
    print("5. THE CURATOR'S REFINEMENT: two storeys, and what it costs")
    print("   'In me there are billions of living cells; each could in")
    print("   principle start another me. But when I say I, I mean the")
    print("   consciousness. And the god is not a person — the cells are")
    print("   his platform.'")
    print()
    print("   That splits the case in two, and the split is not a dodge:")
    print("     PLATFORM  the cell lineage. Divides, never stopped, carries")
    print("               no self.")
    print("     PERSON    the consciousness. Does not divide, is not")
    print("               transmitted by cell division, ends.")
    # the objection from section 3 dissolves: transitivity ran through the
    # cell line, and personal identity was never riding on it
    print("   The bill from section 3 — 'then you and I are one individual'")
    print("   — is PAID by this move rather than dodged: identity through")
    print("   fission belongs to the platform, where it costs nothing,")
    print("   because nobody claimed the platform was a person. The")
    print("   transitivity collapse was an argument against a claim the")
    print("   curator was not making.")
    # what survives, and what it now needs
    chain = judge("lineage_unbroken", {"lineage_unbroken": "T"})
    print(f"   'the lineage has never been interrupted': "
          f"{chain['disposition']}  (witness: common descent — the judge")
    print("     records who vouches, it never checks the biology itself)")
    assert chain["disposition"] == "EARNED"
    alive = judge("lineage_is_a_living_bearer",
                  {"lineage_is_a_living_bearer": "Z"})
    print(f"   'the lineage is a LIVING BEARER, a thing that is alive': "
          f"{alive['disposition']}")
    assert alive["disposition"] == "OPEN"
    print("   and here is the finding: that second claim has no measurement")
    print("   and no document that could settle it. 'Alive' is a predicate")
    print("   of BEARERS — things with a boundary and a metabolism — and a")
    print("   lineage is a relation of descent, not a bearer. Extending the")
    print("   predicate to lineages is a decision about the ENCODING.")
    print("   So the cure is the fourth one, the one this corpus minted")
    print("   yesterday for a pizza: not `measure`, not `document`, but")
    print("   CONTEST TYPE — argue about what sort of thing may be called")
    print("   alive. No experiment is owed, and none would help.")


def sec6_the_two_deaths():
    print("-" * 72)
    print("6. AND THE ASYMMETRY OF DEATH")
    # the person's claim expires; the lineage's cannot
    person_now = grade("i_am_alive", {"i_am_alive": "M"})
    lineage_past = grade("lineage_was_continuous",
                         {"lineage_was_continuous": T})
    print(f"   'I am alive' (a claim about now)        : {person_now}")
    print(f"   'the lineage ran unbroken' (about the past): {lineage_past}")
    assert person_now == "until-verification"
    assert lineage_past == "hereditary"
    print("   The person's claim lives in the present and expires: it must")
    print("   be re-earned every moment, and one day it will not be. The")
    print("   lineage's claim is about the past and, once witnessed, cannot")
    print("   be revoked by anything that happens next.")
    print("   So the god cannot die the way you can. If the last cell goes")
    print("   out, the lineage ENDS — but the claim that it ran unbroken")
    print("   for four billion years stays earned forever. That is not")
    print("   immortality; it is a different grammar of ending, and it is")
    print("   the sharpest thing the machine can say about the question.")


if __name__ == "__main__":
    print("=" * 72)
    print("THE EARTHLY GOD — the curator's dilemma, priced")
    print("=" * 72)
    sec1_the_dates_in_passing()
    sec2_one_word_two_relations()
    sec3_the_fork_by_model_count()
    sec4_the_cut()
    sec5_two_storeys()
    sec6_the_two_deaths()
    print("=" * 72)
    print("LIFELINE GREEN — no contradiction, and the curator was right to")
    print("keep failing to find one. Three rules for fission, three bills;")
    print("and his own refinement — the god is the PLATFORM, the I is the")
    print("consciousness — pays the heaviest of them, since identity")
    print("through fission then belongs to the cell line, where nobody")
    print("claimed a person lived. What survives the split is one claim")
    print("with an EARNED chain (the lineage never broke) and one with no")
    print("possible witness (the lineage is a thing that is ALIVE) — and")
    print("the cure for the second is neither measurement nor document but")
    print("CONTEST TYPE: a decision about what sort of thing may be called")
    print("alive. Plus the asymmetry that answers the title question best:")
    print("the person's 'I am alive' is until-verification and expires; the")
    print("lineage's 'it ran unbroken' is hereditary and cannot be revoked")
    print("by anything that happens next. The god does not die the way you")
    print("do — not because he is immortal, but because his ending has a")
    print("different grammar.")
