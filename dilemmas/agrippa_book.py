# -*- coding: utf-8 -*-
"""
Agrippa in the book of claims: the three horns, priced by blast radius.

`dilemmas/agrippa.py` puts the Münchhausen trilemma through the judge and
the passport: the skeptic's logic is conceded (F1), the lethality is
located in the binary-warrant premise (F2), the circle is shown to be
vicious by PARITY and not by circularity (F5), and dogma is shown to be a
named, priced stipulation point (F6).

This file asks the question that only `zbook` can ask. The book is itself a
justification graph — a claim's ground may be a document or another claim —
so the trilemma is not a subject it discusses but a shape it can be BUILT
in. Build each horn and measure it in the book's own currency: how much of
the structure falls when one ground is withdrawn.

MEASURED HERE:

  1. REGRESS, five claims each resting on the next and the last resting on
     nothing: five ON CREDIT, zero EARNED. The horn is exactly as
     advertised — an unfinished chain warrants nothing, at any storey;
  2. DOGMA, the same chain with one document under the bottom: five of
     five EARNED. One sheet of paper converts the whole tower. And the
     blast radius of that sheet is 5 of 5 — everything, including the four
     claims that never name it;
  3. so the two horns are the SAME STRUCTURE at two settings, and the
     trilemma's choice between them is a choice between warranting nothing
     and warranting everything on one card. That is not a discovery, but
     having it as two numbers rather than two adjectives is the point of a
     ledger;
  4. and the third configuration — mutual support, each claim on its own
     document PLUS a neighbour's claim — was expected to be the robust
     one. MEASURED: it is not. Blast radii run 1, 2, 3, 4, 5, 5. The claim
     with TWO independent documents is the most fragile in the book, not
     the safest, because each document is another way to break it. Adding
     grounds buys no strength here;
  5. the only structure that limits damage is five claims that do NOT
     support each other: blast radius 1 apiece. Robustness comes from
     INDEPENDENCE, never from mutual support — which is the same finding
     `inventory/corpus_book.py` made about this project's own results,
     arrived at from the opposite end.

THE GAP THIS FOUND. Point 4 is not a fact about justification; it is a
limitation of the machine, and the trilemma is what exposed it. This
register knows only CONJUNCTIVE support — every ground is necessary, so a
second ground is a second liability. It cannot express ALTERNATIVE support
("two independent invoices for the same sum; either one suffices"), which
is what coherentist and Bayesian pictures actually rely on, and which is an
ordinary thing in an audit. Until a quantity may carry alternative
witnesses, the book will always score a web below a tower, and that score
should be read as the instrument's, not the world's.

Run:  python3 dilemmas/agrippa_book.py
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                ".."))

from zbook import judge_book, fallout, census, classify_cycles  # noqa: E402

N = 5


def regress(n=N):
    """Each claim rests on the next; the last rests on nothing."""
    book = [(f"r{i}", "x == 1", f"x=1 earned:claim/r{i + 1}")
            for i in range(1, n)]
    return book + [(f"r{n}", "x == 1", "x=1 credit")]


def dogma(n=N):
    """The same chain, with one document under the bottom."""
    book = [(f"d{i}", "x == 1", f"x=1 earned:claim/d{i + 1}")
            for i in range(1, n)]
    return book + [(f"d{n}", "x == 1", "x=1 earned:axiom")]


def web(n=N):
    """Each claim on its own document AND on a neighbour's claim."""
    book = [(f"w{i}", "sum(a,b) == 2",
             f"a=1 earned:doc{i}, b=1 earned:claim/w{i + 1}")
            for i in range(1, n)]
    return book + [(f"w{n}", "sum(a,b) == 2",
                    f"a=1 earned:doc{n}, b=1 earned:doc{n}b")]


def independent(n=N):
    """Five claims that do not support each other at all."""
    return [(f"s{i}", "x == 1", f"x=1 earned:doc{i}") for i in range(1, n + 1)]


def circle(n=3):
    """A ring of mutual support, no document anywhere."""
    return [(f"c{i}", "x == 1",
             f"x=1 earned:claim/c{i % n + 1}") for i in range(1, n + 1)]


def radii(book, grounds):
    return {g: len(fallout(book, g)) for g in grounds}


def sec1_regress_warrants_nothing():
    print("-" * 72)
    print("1. THE REGRESS HORN, BUILT")
    book = regress()
    res = judge_book(book)
    print(f"   a chain of {N}, the last resting on nothing: {census(res)}")
    for cid, _f, _d in book:
        print(f"     {cid}  {res[cid]['disposition']:9} "
              f"leaning on {res[cid]['cites'] or ['—']}")
    assert census(res) == {"ON CREDIT": N}
    print("   Zero earned, at every storey. Not a philosophical verdict —")
    print("   the same rule that runs the invoices: a ground taken on")
    print("   somebody's word is not a ground. Agrippa's first horn is")
    print("   conceded in full, and it is the cheapest of the three to")
    print("   reproduce.")


def sec2_one_sheet_of_paper():
    print("-" * 72)
    print("2. THE DOGMA HORN: THE SAME CHAIN, PLUS ONE DOCUMENT")
    book = dogma()
    res = judge_book(book)
    hits = fallout(book, "axiom")
    print(f"   the identical chain with a document under the bottom: "
          f"{census(res)}")
    print(f"   blast radius of that one document: {len(hits)} of {N} — "
          f"{[h[0] for h in hits]}")
    assert census(res) == {"EARNED": N} and len(hits) == N
    print("   One sheet of paper converts the whole tower, and withdrawing")
    print("   it un-converts every storey — including the four claims that")
    print("   never name it. So the two horns are ONE structure at two")
    print("   settings, and the trilemma's choice between them is the choice")
    print("   between warranting nothing and warranting everything on one")
    print("   card. Both true, both known; the gain is that they are now two")
    print("   numbers instead of two adjectives.")


def sec3_the_circle_again():
    print("-" * 72)
    print("3. THE CIRCLE HORN, FOR COMPLETENESS")
    book = circle()
    res = judge_book(book)
    kinds = [k for _members, k in classify_cycles(book)]
    print(f"   a ring of three, no document anywhere: {census(res)}")
    print(f"   the passport on the ring: {kinds}")
    assert census(res) == {"CIRCULAR": 3} and kinds == [["UNDERDETERMINED"]]
    print("   Ungrounded rather than refuted, curable only by stipulating a")
    print("   member — and `agrippa.py` F5 measured the rest: viciousness")
    print("   is the PARITY of the negations, not the circularity. Nothing")
    print("   new here; it is included so the three horns are in one place.")


def sec4_mutual_support_buys_nothing():
    print("-" * 72)
    print("4. THE CONFIGURATION THAT WAS EXPECTED TO BE ROBUST")
    book = web()
    grounds = [f"doc{i}" for i in range(1, N + 1)] + [f"doc{N}b"]
    r = radii(book, grounds)
    print("   each claim on its own document AND on a neighbour's claim:")
    for g in grounds:
        print(f"     retract {g:7} -> {r[g]} of {N} fall")
    assert sorted(r.values()) == [1, 2, 3, 4, 5, 5]
    print(f"   The prediction was that spreading the support would spread")
    print(f"   the risk. It does not. The worst radius is still {max(r.values())}"
          f" of {N},")
    print("   and the claim with TWO independent documents is the most")
    print("   fragile object in the book, not the safest: every ground it")
    print("   holds is another way to break it.")
    print("   The reason is the register, not the world. Support here is")
    print("   CONJUNCTIVE — every ground necessary — so a second ground is")
    print("   a second liability. Alternative support, 'either invoice will")
    print("   do', cannot be written down at all.")


def sec5_only_independence_helps():
    print("-" * 72)
    print("5. WHAT ACTUALLY LIMITS THE DAMAGE")
    book = independent()
    grounds = [f"doc{i}" for i in range(1, N + 1)]
    r = radii(book, grounds)
    print(f"   five claims that do not support each other: "
          f"{census(judge_book(book))}")
    print(f"   blast radius of each document: {sorted(r.values())}")
    assert sorted(r.values()) == [1] * N
    print("   One apiece, and that is the whole of it. In this register")
    print("   robustness comes from INDEPENDENCE and never from mutual")
    print("   support — the same result `inventory/corpus_book.py` reached")
    print("   about this project's own findings, from the opposite end:")
    print("   the corpus survives a bad instrument because its stacks do")
    print("   not cite each other, not because they reinforce each other.")
    print("   Note what this is NOT: an escape from Agrippa. Five towers")
    print("   are five dogmas. The trilemma is untouched; what the ledger")
    print("   adds is that the dogmatic horn is not one thing but a range,")
    print("   from one axiom under everything to one axiom apiece.")


def sec6_the_gap_this_found():
    print("-" * 72)
    print("6. THE HOLE THIS OPENED IN OUR OWN TOOL")
    print("   Section 4 is not a fact about justification. It is a limit of")
    print("   the machine, and the trilemma is what exposed it: the book")
    print("   knows only conjunctive support, so it must score a web below")
    print("   a tower, and that score belongs to the instrument.")
    print("   What is missing is ALTERNATIVE witnesses — two independent")
    print("   invoices for the same sum, either sufficient. That is not an")
    print("   exotic epistemology; it is an ordinary audit, and it is the")
    print("   thing coherentist and Bayesian pictures actually run on.")
    print("   Recorded as a gap, not patched here: it changes what EARNED")
    print("   means, and a change of that size is settled in words first.")


if __name__ == "__main__":
    print("=" * 72)
    print("AGRIPPA IN THE BOOK — the three horns, priced by blast radius")
    print("=" * 72)
    sec1_regress_warrants_nothing()
    sec2_one_sheet_of_paper()
    sec3_the_circle_again()
    sec4_mutual_support_buys_nothing()
    sec5_only_independence_helps()
    sec6_the_gap_this_found()
    print("=" * 72)
    print("AGRIPPA-BOOK GREEN — regress warrants nothing at any storey (5 ON")
    print("CREDIT, 0 earned); one document under the bottom earns all five")
    print("and carries a blast radius of 5 of 5; the ring is UNDERDETERMINED.")
    print("The configuration expected to be robust — mutual support — is not:")
    print("radii 1,2,3,4,5,5, and the claim with two documents is the most")
    print("fragile, because support here is conjunctive and every ground is")
    print("another liability. Only independence limits damage, one apiece,")
    print("which is five dogmas rather than an escape. The gap the trilemma")
    print("found in our tool — no alternative witnesses — is recorded, not")
    print("patched.")
