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
     support each other: blast radius 1 apiece — SUPERSEDED by point 6,
     and left standing because the correction is the point;
  6. because point 4 was never a fact about justification. It was a limit
     of the machine, and the trilemma is what exposed it: the book knew
     only CONJUNCTIVE support, every ground necessary, so a second ground
     was a second liability and a web had to score below a tower. `zbook`
     can now say EITHER — `earned:inv-17|inv-18`, two independent invoices
     for one sum, one sufficing. THE SAME WEB, REBUILT: every single
     retraction costs nothing at all, and taking BOTH grounds under the
     bottom claim moves that claim and nothing above it. The cascade dies
     one storey up. So robustness does not come only from independence; it
     comes from ALTERNATIVES, which is what the coherentist and Bayesian
     pictures were saying all along — we had no way to write it down;
  7. and independence itself is DECLARED, never verified: two copies of
     one invoice are one witness under two names, and the book buys the
     robustness anyway. Same answer as for the nullary ground — not
     detection but DISCLOSURE, `declared_alternatives` itemising every
     claim of independence by name.

WHAT THE TRILEMMA ACTUALLY YIELDED, then, is not a verdict on the trilemma.
It is a missing word in our own instrument, found by building the horns
instead of discussing them.

Run:  python3 dilemmas/agrippa_book.py
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                ".."))

from zbook import (judge_book, fallout, census, classify_cycles,   # noqa: E402
                   retract, declared_alternatives, cost)

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


def alt_web(n=N):
    """The same web, once the register can say EITHER — each claim on its own
    document OR a neighbour's claim, one ground sufficing."""
    book = [(f"v{i}", "x == 1", f"x=1 earned:doc{i}|claim/v{i + 1}")
            for i in range(1, n)]
    return book + [(f"v{n}", "x == 1", f"x=1 earned:doc{n}|doc{n}b")]


def circle(n=3):
    """A ring of mutual support, no document anywhere."""
    return [(f"c{i}", "x == 1",
             f"x=1 earned:claim/c{i % n + 1}") for i in range(1, n + 1)]


def radii(book, grounds):
    """Brackets, not numbers — see `zbook.cost`. The pair is the answer; a
    width above zero is the price of a declaration in this book."""
    return {g: cost(book, g) for g in grounds}


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
        print(f"     retract {g:7} -> [{r[g]['low']}, {r[g]['high']}] of {N}")
    assert sorted(c["low"] for c in r.values()) == [1, 2, 3, 4, 5, 5]
    assert {c["width"] for c in r.values()} == {0}
    worst = max(c["low"] for c in r.values())
    print(f"   The prediction was that spreading the support would spread")
    print(f"   the risk. It does not. The worst radius is still {worst}"
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
    print(f"   blast radius of each document: "
          f"{sorted((c['low'], c['high']) for c in r.values())}")
    assert sorted(c["low"] for c in r.values()) == [1] * N
    assert {c["width"] for c in r.values()} == {0}
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
    print("   READ SECTION 6 BEFORE QUOTING THIS ONE: 'only independence")
    print("   helps' held of a register that could not say EITHER. It can")
    print("   now, and the sentence does not survive the change.")


def sec6_the_gap_closed_and_the_web_rebuilt():
    print("-" * 72)
    print("6. THE HOLE THIS OPENED IN OUR TOOL — AND WHAT CLOSING IT DID")
    print("   Section 4 was never a fact about justification. It was a limit")
    print("   of the machine: the book knew only CONJUNCTIVE support, every")
    print("   ground necessary, so it had to score a web below a tower.")
    print("   `zbook` can now say EITHER — `earned:inv-17|inv-18`, two")
    print("   independent invoices for one sum, one of them sufficing. The")
    print("   same web, rebuilt:")
    book = alt_web()
    grounds = [f"doc{i}" for i in range(1, N + 1)] + [f"doc{N}b"]
    r = radii(book, grounds)
    for g in grounds:
        print(f"     retract {g:7} -> [{r[g]['low']}, {r[g]['high']}]")
    assert census(judge_book(book)) == {"EARNED": N}
    assert {c["low"] for c in r.values()} == {0}
    assert sorted(c["high"] for c in r.values()) == [1, 2, 3, 4, 5, 5]
    print("   and every bracket is WIDE. Read the high ends alone —")
    print("   1, 2, 3, 4, 5, 5 — and they are EXACTLY section 4's numbers:")
    print("   the strict reading of the web IS the tower. Which is the")
    print("   cleanest statement of what a declaration buys and what it")
    print("   costs, in one line of arithmetic: believe the independence and")
    print("   nothing falls; disbelieve it and you are back in the tower you")
    print("   started from. Both ends are printed, always, because the")
    print("   machine cannot tell you which of them you are living in.")
    # and the deeper question: does the CASCADE stop, or is it merely delayed?
    stripped = retract(retract(book, f"doc{N}"), f"doc{N}b")
    before, after = judge_book(book), judge_book(stripped)
    moved = [c for c in before
             if before[c]["disposition"] != after[c]["disposition"]]
    print(f"   take BOTH grounds under the bottom claim: {moved} moves, "
          f"and nothing above it")
    assert moved == [f"v{N}"]
    print("   Every single retraction now costs NOTHING, and even destroying")
    print("   the bottom claim outright stops there: the storey above still")
    print("   holds its own document, so the cascade dies one step up.")
    print("   Against the conjunctive web measured in section 4 — radii 1 to")
    print("   5, one document taking the lot — that is the whole difference")
    print("   between a web and a tower, and it was invisible for as long as")
    print("   the register could only say AND.")
    print("   So section 5's sentence is retracted: robustness does NOT come")
    print("   only from independence. It comes from ALTERNATIVES, which is")
    print("   what coherentist and Bayesian pictures were saying all along —")
    print("   we simply had no way to write it down. Agrippa's trilemma")
    print("   found the missing vocabulary in our own instrument, which is a")
    print("   better return than a verdict on the trilemma would have been.")


def sec7_what_the_machine_still_cannot_check():
    print("-" * 72)
    print("7. AND WHAT THE MACHINE STILL CANNOT CHECK")
    fake = [("f1", "x == 1", "x=1 earned:inv-17|inv-17-photocopy")]
    print(f"   two grounds, one of them a copy of the other: "
          f"{census(judge_book(fake))}")
    print(f"   retract the original: "
          f"{[h[0] for h in fallout(fake, 'inv-17')] or 'nothing falls'}")
    print(f"   declared_alternatives: {declared_alternatives(fake)}")
    assert not fallout(fake, "inv-17")
    assert declared_alternatives(fake) == [("f1", "x",
                                            ["inv-17", "inv-17-photocopy"])]
    v = judge_book(fake)["f1"]
    print(f"   the verdict: {v['disposition']} / warranty {v['warranty']}"
          f" / {v['declared']}")
    assert v["warranty"] == "declared"
    print("   INDEPENDENCE IS DECLARED AND, BETWEEN DOCUMENTS, NEVER")
    print("   VERIFIABLE. Two copies of one invoice are one witness under")
    print("   two names, and this book buys the robustness anyway. Exactly the situation the nullary")
    print("   ground is in (`agrippa_nullary.py` §3), and the answer is the")
    print("   same: not detection, DISCLOSURE. Every claim of independence")
    print("   is itemised by name, so a bogus one is visible instead of")
    print("   silent — and the verdict says so too, reading EARNED with a")
    print("   DECLARED warranty rather than plain EARNED. Between CLAIMS")
    print("   the graph does better than disclosure: a shared ancestor")
    print("   refutes the independence outright and is named (`zbook`")
    print("   sections 7-8). Documents are where the promise stops.")


if __name__ == "__main__":
    print("=" * 72)
    print("AGRIPPA IN THE BOOK — the three horns, priced by blast radius")
    print("=" * 72)
    sec1_regress_warrants_nothing()
    sec2_one_sheet_of_paper()
    sec3_the_circle_again()
    sec4_mutual_support_buys_nothing()
    sec5_only_independence_helps()
    sec6_the_gap_closed_and_the_web_rebuilt()
    sec7_what_the_machine_still_cannot_check()
    print("=" * 72)
    print("AGRIPPA-BOOK GREEN — regress warrants nothing at any storey (5 ON")
    print("CREDIT, 0 earned); one document under the bottom earns all five")
    print("and carries a blast radius of 5 of 5; the ring is UNDERDETERMINED.")
    print("Under conjunctive support a web scored WORSE than a tower — radii")
    print("1,2,3,4,5,5 — which was the instrument speaking, not the world.")
    print("With alternatives in the register the same web takes zero damage")
    print("from any single retraction, and losing both grounds under the")
    print("bottom claim moves that claim alone: the cascade dies one storey")
    print("up. Robustness comes from ALTERNATIVES, not only independence.")
    print("Independence itself stays declared and unverifiable — a photocopy")
    print("buys the same immunity — so the promise is disclosure, not")
    print("detection: every claim of independence itemised by name.")
