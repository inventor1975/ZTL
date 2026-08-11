# -*- coding: utf-8 -*-
"""
Epistemic closure and the brain in a vat: two axes, one confusion.

The live dispute (Dretske 1970 and Nozick 1981 against closure; DeRose,
Hawthorne, Williamson for it; Wright and Davies separating closure from
the TRANSMISSION of warrant) turns on one argument:

    I know I have hands.                                        h
    Having hands entails I am not a handless brain in a vat.    h |= ~b
    So — by closure — I know I am not a brain in a vat.         ~b
    But surely I do not know that.

Deny closure (Dretske) and you must swallow DeRose's abominable
conjunction: "I know I have hands, but I do not know I am not a handless
vat-brain." Keep closure and you must explain why looking at your hands
settles the first and does nothing for the second.

PRIOR ART, stated before the measurement rather than after it: that
closure can hold while WARRANT fails to transmit is Wright's and Davies's,
not ours, and the literature has no agreed criterion for when transmission
fails.

WHAT THE MACHINE ACTUALLY SAID, against the prediction written before the
run (which was "the abominable conjunction will be unwritable here"):

  * the sceptic's own entailment FAILS in this logic. MEASURED:
    {h, ~(h & b)} does NOT entail ~b — counterexample h = T, b = Z. The
    closure step never fires, not because closure is a bad principle but
    because the specific classical entailment it uses is one of the 372
    classical validities we lack;
  * so the abominable conjunction is not unwritable — it is the DEFAULT.
    In the ordinary ledger (hands verified, vat never examined) "I have
    hands" is EARNED and "I am not in a vat" is not;
  * and the reason is free truth once more: the incompatibility premise
    ~(h & b) is satisfied VACUOUSLY at an unexamined b, so it has no grip
    to transmit anything. The premise everyone grants for free is the one
    doing no work.

Read the F on "I am not in a vat" carefully: it is denial for want of
ground, not the assertion that you are in one. The vat claim itself stays
OPEN in the same ledger — b = Z while ~b = F, because negation burns the
mark. Denial without a witness, the same shape this corpus measured for
Collatz and for the heap.

Run:  python3 dilemmas/closure.py
"""
import os
import sys
from itertools import product

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z, ev                                   # noqa: E402
from ztljudge import judge                                    # noqa: E402
from zverify import grade                                     # noqa: E402

# h — I have hands; b — I am a handless brain in a vat; e — my experience
# is hands-like. The case fixes h = ~b (having hands rules the vat out),
# and the evidence is IDENTICAL in both worlds: e is T either way.
HANDS, VAT = "h", "b"


def sec1_the_step_that_never_fires():
    print("-" * 72)
    print("1. THE SCEPTIC'S ENTAILMENT, CHECKED RATHER THAN GRANTED")
    from entailment import entails
    inc = ("not", ("and", "h", "b"))       # hands and vat are incompatible
    cex = entails(["h", inc], ("not", "b"))
    print(f"   classically {{h, ~(h & b)}} |= ~b;  here: "
          f"{'holds' if cex is None else 'FAILS, counterexample ' + str(cex)}")
    assert cex is not None and cex["h"] == T and cex["b"] == Z
    m = {"h": T, "b": Z}
    print(f"   at that cell: ~(h & b) = {ev(inc, m)}   h = {m['h']}   "
          f"~b = {ev(('not', 'b'), m)}   b = {m['b']}")
    assert ev(inc, m) == T and ev(("not", "b"), m) == F
    print("   the incompatibility premise is T — VACUOUSLY, because an")
    print("   unexamined vat makes the conjunction false all by itself. A")
    print("   premise satisfied for free transmits nothing, so the closure")
    print("   step has nothing to carry. Closure as a principle is not")
    print("   touched: what fails is this entailment, at this cell.")
    # and the warranty ladder, for the record
    assert grade("h", {"h": T}) == "hereditary"
    assert grade("h", {"h": "M"}) == "until-verification"


def sec2_no_act_distinguishes_the_worlds():
    print("-" * 72)
    print("2. THE ACTS, MODELLED RATHER THAN ASSERTED")
    # Two worlds and a repertoire of acts. An act yields an observation;
    # it SETTLES a claim only if the observation differs across the worlds
    # in which the claim differs. The vat world is built to produce the
    # same observations — that is the whole content of the thought
    # experiment — so this is a two-line model, not a stipulation.
    worlds = {"hands": {"h": T, "b": F}, "vat": {"h": F, "b": T}}
    acts = {"look": lambda w: "hands-like image",
            "touch": lambda w: "hands-like feel",
            "ask a friend": lambda w: "a friend agreeing",
            "look again, harder": lambda w: "hands-like image"}
    def settles(act, claim):
        seen = {acts[act](w) for w in worlds}
        if len(seen) > 1:                     # the act tells worlds apart
            return True
        vals = {ev(claim, worlds[w]) for w in worlds}
        return len(vals) == 1                 # or the claim is constant
    for name, claim in (("I have hands   ", "h"),
                        ("I am not in a vat", ("not", "b"))):
        good = [a for a in acts if settles(a, claim)]
        print(f"   {name}: acts that settle it -> {good or 'NONE'}")
        assert good == []
    print("   NEITHER claim is settleable — and that is the finding. The")
    print("   asymmetry Dretske feels is not evidential: looking does not")
    print("   settle the hands either, since the vat world looks the same.")
    print("   Whatever makes 'I have hands' respectable, it is not an act")
    print("   in this repertoire.")


def sec3_the_abominable_conjunction():
    print("-" * 72)
    print("3. IS THE ABOMINABLE CONJUNCTION EVEN AVAILABLE?")
    # Enumerate every ledger over the two claims and ask for the one
    # Dretske needs: h EARNED while ~b is not.
    found = []
    for hv, bv in product((T, F, Z), repeat=2):
        marking = {"h": hv, "b": bv}
        # the case's own constraint: hands and vat are incompatible, and
        # the subject asserts hands. A ledger is admissible only if it
        # respects that constraint as an earned fact.
        if ev(("not", ("and", "h", "b")), marking) != T:
            continue
        h_claim = judge("h", marking)
        nb_claim = judge("~b", marking)
        if h_claim["disposition"] == "EARNED" and \
                nb_claim["disposition"] != "EARNED":
            found.append((hv, bv, h_claim["disposition"],
                          nb_claim["disposition"]))
        print(f"   h={hv} b={bv}:  'I have hands' {h_claim['disposition']:9}"
              f"   'not in a vat' {nb_claim['disposition']}")
    print(f"   ledgers where hands are EARNED and not-vat is not: "
          f"{len(found)}  -> {found}")
    # the prediction written before the run said this would be empty. It
    # is not, and the one cell it contains is the ordinary human ledger:
    # hands looked at, vat never examined.
    assert found == [(T, Z, "EARNED", "OPEN")]
    print("   exactly one, and it is the ledger everybody actually keeps:")
    print("   hands verified, vat never examined. So DeRose's abominable")
    print("   conjunction is not abominable here and not unwritable — it is")
    print("   the DEFAULT. Note also the shape of the denial: at b = Z the")
    print("   claim 'not in a vat' is OPEN while its negation would be F —")
    print("   the machine refuses the exculpation without asserting the vat.")


def sec4_the_control():
    print("-" * 72)
    print("4. THE CONTROL: an ordinary deduction, where the cure DOES pass")
    # 'the cup is red' entails 'the cup is coloured', and the act that
    # settles the premise settles the conclusion too
    red = judge("red", {"red": "Z"})
    coloured = judge("red | blue", {"red": "Z", "blue": "F"})
    print(f"   'the cup is red'      : {red['disposition']} — "
          f"cure {red['unverified']}")
    print(f"   'the cup is coloured' : {coloured['disposition']} — "
          f"cure {coloured['unverified']}")
    assert red["unverified"] == ["red"] and coloured["unverified"] == ["red"]
    print("   same cure, one act, and it settles both. So the contrast is")
    print("   not vacuous: in an ordinary deduction the conclusion's cure")
    print("   lies inside the repertoire, and in the sceptical case NEITHER")
    print("   claim has a cure there at all — which is why no amount of")
    print("   looking ever felt like progress.")


def sec5_the_move_is_a_stipulation():
    print("-" * 72)
    print("5. WHAT ACTUALLY MOVES THE LEDGER: an act of stipulation")
    a = (judge("h", {"h": T, "b": Z})["disposition"],
         judge("~b", {"h": T, "b": Z})["disposition"])
    c = (judge("h", {"h": T, "b": F})["disposition"],
         judge("~b", {"h": T, "b": F})["disposition"])
    print(f"   vat never examined : hands {a[0]}, not-in-a-vat {a[1]}")
    print(f"   vat stipulated away: hands {c[0]}, not-in-a-vat {c[1]}")
    assert a == ("EARNED", "OPEN") and c == ("EARNED", "EARNED")
    print("   and section 2 measured that NO act carries you from the first")
    print("   ledger to the second. The step is not a measurement; it is a")
    print("   STIPULATION — the same move the heap needed, and the same")
    print("   freedom: where there is no ground there is no target.")
    print("   THE READING. The quarrel is not about closure. Grant the")
    print("   anti-sceptical stipulation and both claims are earned")
    print("   together, closure intact. Refuse it and both are open")
    print("   together — you do not know the hands either, which is what")
    print("   the sceptic said in the first place. The abominable")
    print("   conjunction lives in exactly one ledger: the one that")
    print("   stipulates the hands and forgets to write down that it did.")
    print("   That is not knowledge failing to transmit; it is an entry")
    print("   missing from the books.")
    print("   HONEST PLACEMENT. That closure and transmission come apart is")
    print("   Wright's and Davies's, and this stand does not improve on")
    print("   them. What is ours is mechanical rather than argued: the")
    print("   sceptic's own entailment is measured and it FAILS here (§1),")
    print("   the evidential asymmetry is measured and it does NOT exist")
    print("   (§2), and what remains is a stipulation the ledger can show")
    print("   as a line item with its own cure — 'document the assumption'.")


if __name__ == "__main__":
    print("=" * 72)
    print("EPISTEMIC CLOSURE — the vat, priced on two axes")
    print("=" * 72)
    sec1_the_step_that_never_fires()
    sec2_no_act_distinguishes_the_worlds()
    sec3_the_abominable_conjunction()
    sec4_the_control()
    sec5_the_move_is_a_stipulation()
    print("=" * 72)
    print("CLOSURE GREEN — and against the prediction written before the")
    print("run. The sceptic's entailment FAILS here at h = T, b = Z, so the")
    print("closure step never fires; the premise everyone grants for free")
    print("— hands and vat are incompatible — is true vacuously and")
    print("transmits nothing. The abominable conjunction is therefore not")
    print("unwritable but DEFAULT, in exactly one ledger of nine. No act")
    print("in the repertoire settles either claim, so the felt asymmetry")
    print("is not evidential: what separates the hands from the vat is a")
    print("stipulation nobody wrote down. Enter it and closure is intact;")
    print("refuse it and both claims are open together.")
