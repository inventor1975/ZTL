# -*- coding: utf-8 -*-
"""
Agrippa's third horn splits, and the instrument already knew the difference.

The trilemma's dogma horn is stated as one thing: the chain stops at an
unjustified foundation. The curator's objection, which this file measures,
is that it glues together two situations that are not alike —

    a CHOSEN stop      you assert a proposition without proof, and a rival
                       assertion is available. The fifth postulate, AC,
                       propositional extensionality. You could have gone
                       otherwise, and someone did;

    a FORCED stop      the chain ends because the next question has no
                       form. Not a proposition, so nothing to deny; the
                       "alternative" is not a rival position but silence.
                       VR's ∅ is the instance: a NULLARY operation, a
                       0-ary term-former with nothing to supply it.

Agrippa's argument is about the justification of STATEMENTS. Against the
first it bites. Against the second it does not fail — it does not reach.

MEASURED HERE, and the first measurement is the surprise:

  1. the criterion the objection needs — HOW MANY admissible settings does
     the stopping point have — is not new machinery. It is the passport's
     model count, which this corpus has been printing since E18 under other
     names. A self-supporting foundation is UNDERDETERMINED with 2 models:
     the choice was real, and that is dogma. A self-forcing one is
     INTRINSIC with exactly 1: nothing was chosen. The split Agrippa's
     third horn needs was already implemented, and we never read it that
     way;
  2. in the book the two stops are still indistinguishable, because a
     ground was a ground. So the instrument was extended, minimally: a
     witness may now declare itself PERFORMED — a ground with no inputs —
     and asking to withdraw it raises NotAMove. Not "protected", not
     "survived the retraction": the move is refused, because there is
     nothing to fail to supply;
  3. and the honest part, which is the whole value: the book CANNOT verify
     nullarity. Anyone may label an axiom `performed/` and buy immunity.
     What the book can do is make every such claim ITEMISED and
     ATTRIBUTABLE — `declared_structural` lists them all. That is the real
     gain over the dogma horn, which is silent by nature: we do not detect
     honest foundations, we make the claim of one impossible to hide.

WHERE IT CAN BE CHECKED, and this is stated rather than measured here: in
VR the declaration is not taken on trust. `VR.lean` is `[]` — the
elaborator confirms the construction leans on nothing, `∅` being `base`,
the 0-ary constructor of an inductive type, and induction being the
recursor rather than a postulate. That is a declaration with a machine
behind it, and it is the difference between this file's `performed/` and
VR's zero.

WHAT IS NOT CLAIMED: the philosophical move is old — Wittgenstein's
bedrock, the pragmatists, and closest of all Brouwer, for whom the
primordial intuition is explicitly not an axiom. No priority is claimed for
the idea. What did not exist before is the EXHIBIT: a foundation whose
axiom cost is zero and machine-confirmed.

Run:  python3 dilemmas/agrippa_nullary.py
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                ".."))

from zpassport import (passports, component_models, deps)          # noqa: E402
from zbook import (judge_book, fallout, declared_structural,       # noqa: E402
                   NotAMove, census)

# Stopping points, as systems. Each is a chain that has come to rest.
CHOSEN = {"foundation": "foundation"}            # it supports itself: τ
FORCED = {"foundation": ("xnor", "foundation", "foundation")}
VICIOUS = {"foundation": ("not", "foundation")}  # the liar, for contrast


def settings(system):
    """How many admissible settings the stopping point has — the passport's
    own model count, which is the criterion the objection needs."""
    lfp, reports = passports(system)[0], passports(system)[1]
    out = []
    for comp, kind, _why in reports:
        env_names = set()
        for s in comp:
            env_names |= deps(system[s]) - set(comp)
        env = {n: lfp[n] for n in env_names}
        out.append((kind, list(component_models(comp, system, env))))
    return out


def sec1_the_criterion_was_already_here():
    print("-" * 72)
    print("1. COUNTING THE SETTINGS OF A STOPPING POINT")
    for label, system in (("chosen  (f := f)", CHOSEN),
                          ("forced  (f := f xnor f)", FORCED),
                          ("vicious (f := not f)", VICIOUS)):
        (kind, models), = settings(system)
        print(f"   {label:26} {kind:16} settings={len(models)} {models}")
    (k_ch, m_ch), = settings(CHOSEN)
    (k_fo, m_fo), = settings(FORCED)
    (k_vi, m_vi), = settings(VICIOUS)
    assert (k_ch, len(m_ch)) == ("UNDERDETERMINED", 2)
    assert (k_fo, len(m_fo)) == ("INTRINSIC", 1)
    assert (k_vi, len(m_vi)) == ("PARADOX", 0)
    print("   Two settings: the choice was real, and Agrippa is right —")
    print("   this is dogma, and someone else's axiomatisation is waiting.")
    print("   ONE setting: there was nothing to choose. The chain stops")
    print("   without anybody deciding to stop it.")
    print("   The surprise is that this needed no new machinery. The")
    print("   criterion is the passport's model count, printed by this")
    print("   corpus since E18 under the names UNDERDETERMINED and")
    print("   INTRINSIC. The split Agrippa's third horn needs was already")
    print("   implemented; we had simply never read it as a reply to him.")


def sec2_the_book_could_not_tell_them_apart():
    print("-" * 72)
    print("2. IN THE BOOK, BOTH STOPS LOOKED THE SAME — AND DO NOT NOW")
    doc = [("t1", "x == 1", "x=1 earned:claim/t2"),
           ("t2", "x == 1", "x=1 earned:axiom-A")]
    act = [("n1", "x == 1", "x=1 earned:claim/n2"),
           ("n2", "x == 1", "x=1 earned:performed/nullary")]
    print(f"   a tower on a document : {census(judge_book(doc))}")
    print(f"   a tower on an act     : {census(judge_book(act))}")
    assert census(judge_book(doc)) == census(judge_book(act)) == {"EARNED": 2}
    print(f"   withdraw the document : "
          f"{[h[0] for h in fallout(doc, 'axiom-A')]}")
    refused = None
    try:
        fallout(act, "performed/nullary")
    except NotAMove as exc:
        refused = str(exc)
    print(f"   withdraw the act      : REFUSED — {refused}")
    assert len(fallout(doc, "axiom-A")) == 2 and refused
    print("   Both towers earn identically, which is right: a ground is a")
    print("   ground. They part on the only question that separates them —")
    print("   what happens when you try to take the ground away. The")
    print("   document has a blast radius. The act has no retraction: not")
    print("   a radius of zero, which would mean the move succeeded and")
    print("   cost nothing, but NO MOVE, because there is nothing to fail")
    print("   to supply.")


def sec3_the_machine_cannot_verify_it():
    print("-" * 72)
    print("3. AND THE BOOK CANNOT CHECK THAT ANY OF THIS IS TRUE")
    liar = [("d1", "x == 1", "x=1 earned:performed/my-favourite-axiom")]
    print(f"   an ordinary axiom, relabelled as an act: "
          f"{census(judge_book(liar))}")
    try:
        fallout(liar, "performed/my-favourite-axiom")
        raise AssertionError("should have refused")
    except NotAMove:
        print("   ... and its retraction is refused, exactly as VR's zero is.")
    print(f"   declared_structural: {declared_structural(liar)}")
    assert declared_structural(liar) == ["performed/my-favourite-axiom"]
    v = judge_book(liar)["d1"]
    print(f"   and the verdict itself: {v['disposition']} / "
          f"warranty {v['warranty']} / {v['declared']}")
    assert v["warranty"] == "declared"
    print("   Nullarity is DECLARED, never verified. Anyone can buy immunity")
    print("   with a prefix, and this file's machinery cannot stop them.")
    print("   What it does instead is the whole of the gain: every claim of")
    print("   a structural stop is itemised and attributable. Agrippa's")
    print("   dogma horn is dangerous because it is SILENT — the stopping")
    print("   point does not announce itself. Here it must, by name, or it")
    print("   does not get the immunity. We do not detect honest")
    print("   foundations; we make a dishonest one impossible to hide.")
    print("   And the immunity is no longer free of charge in the record:")
    print("   the verdict carries the warranty, so a claim standing on a")
    print("   declared act reads EARNED / declared rather than plain")
    print("   EARNED, and the qualification is inherited by everything")
    print("   above it. A book of pure declarations no longer looks like a")
    print("   book of documents.")


def sec4_where_the_declaration_has_a_machine():
    print("-" * 72)
    print("4. WHERE THE DECLARATION IS NOT TAKEN ON TRUST")
    print("   Stated, not measured here — it belongs to the VR repository:")
    print("   `VR.lean` carries axiom cost `[]`. The elaborator confirms the")
    print("   construction leans on nothing — no propext, no Quot.sound, no")
    print("   Classical.choice. ∅ is `base`, the 0-ary constructor of an")
    print("   inductive type, and induction is the RECURSOR, not a")
    print("   postulate: what first-order exposition must assume, type")
    print("   formation absorbs.")
    print("   So VR's ground is a `performed/` declaration with a machine")
    print("   behind it, which is the whole distance between section 3 and")
    print("   a real answer to the horn. The philosophical move is old —")
    print("   Wittgenstein's bedrock, the pragmatists, and nearest of all")
    print("   Brouwer, whose primordial intuition is explicitly not an")
    print("   axiom. What did not exist before is the exhibit.")


def sec5_what_is_still_open():
    print("-" * 72)
    print("5. WHAT IS STILL OPEN")
    print("   The floor is clean and the STOREYS are priced. Reaching the")
    print("   classical real line costs Tier-3 and VR prints the invoice;")
    print("   the Brouwer continuum stays below the choice floor. So the")
    print("   dogma-free zone has a boundary, drawn by the same project.")
    print("   And one place the skeptic still stands, which no measurement")
    print("   here touches: accepting less in exchange for a clean floor is")
    print("   a choice about GOALS. Not about justification, not about")
    print("   facts — which means it is no longer Agrippa's horn, but it is")
    print("   not nothing either.")
    print("   Still missing from the book, recorded and not patched:")
    print("   ALTERNATIVE witnesses — 'two independent invoices, either")
    print("   suffices'. Support here remains conjunctive, which is why")
    print("   `agrippa_book.py` had to score a web below a tower.")


if __name__ == "__main__":
    print("=" * 72)
    print("AGRIPPA'S THIRD HORN, SPLIT — chosen stops and forced ones")
    print("=" * 72)
    sec1_the_criterion_was_already_here()
    sec2_the_book_could_not_tell_them_apart()
    sec3_the_machine_cannot_verify_it()
    sec4_where_the_declaration_has_a_machine()
    sec5_what_is_still_open()
    print("=" * 72)
    print("AGRIPPA-NULLARY GREEN — the dogma horn splits by a count that was")
    print("already implemented: a self-supporting foundation is")
    print("UNDERDETERMINED with 2 settings (the choice was real — dogma), a")
    print("self-forcing one INTRINSIC with 1 (nothing was chosen). The book")
    print("now separates them too: withdrawing a document has a blast")
    print("radius, withdrawing a ground with no inputs raises NotAMove — the")
    print("move is refused, not survived. Nullarity is declared and cannot")
    print("be verified here, so the gain is not detection but disclosure:")
    print("every claim of a structural stop is itemised, where Agrippa's")
    print("horn is silent by nature.")
