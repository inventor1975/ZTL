# -*- coding: utf-8 -*-
"""
The surprise examination, judged: a stamp nobody issued.

The teacher, on Friday: next week there is exactly one exam, and on the
morning of that day you will not know it is today. The class reasons
backwards — not Friday (we would know by Thursday evening), therefore not
Thursday (Friday is out), and so down to Monday: no exam is possible. On
Wednesday the papers are handed out and everyone is surprised.

The classical literature blames the logic, the announcement, or the word
"know". This stand asks the question the corpus is built for: WHO PAID
for each step. The answer is one stamp — the class treats the teacher's
announcement as knowledge they hold, and nobody issued that.

MEASURED HERE:

  1. the same calendar, twice: with the announcement EARNED, 0 days
     survive the elimination — the class is right and the promise is
     self-defeating; with the announcement ON CREDIT, all 5 survive and
     the exam can land on any of them, surprising;
  2. under perfect knowledge the case contains a liar: A = (E & ~A) gets
     the passport PARADOX — 0 models, period 2, refusal PERMANENT — while
     the same equation with no exam is simply grounded. The surprise exam
     is the liar wearing a calendar, and only the stamp puts him there;
  3. the same sentence, two ledgers: 'the exam is today and you do not
     know it' is EARNED in the teacher's book and OPEN in the class's,
     both correct at once. A warranty belongs to a LEDGER, not to a
     sentence — and the class spent a receipt issued to somebody else.

Run:  python3 dilemmas/surprise.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z, AND, NOT                            # noqa: E402
from ztljudge import judge                                   # noqa: E402
from zpassport import passports                              # noqa: E402
from zverify import grade                                    # noqa: E402

DAYS = ["Mon", "Tue", "Wed", "Thu", "Fri"]


def eliminate(announcement):
    """The class's backward induction, run in the logic rather than in
    prose. A day is eliminated when the announcement holds AND every
    later day is already out — then the morning of that day would tell
    them. `announcement` is the value the class assigns to the teacher's
    words: T if they hold it as knowledge, Z if they hold it on credit."""
    eliminated = {}
    later_all_out = T                       # vacuously, after the last day
    for day in reversed(DAYS):
        eliminated[day] = AND(announcement, later_all_out)
        later_all_out = AND(later_all_out, eliminated[day])
    return eliminated


def sec1_the_calendar_twice():
    print("-" * 72)
    print("1. THE SAME CALENDAR, TWICE")
    for label, value in (("the class KNOWS the announcement ", T),
                         ("the class holds it ON CREDIT     ", Z)):
        out = eliminate(value)
        survivors = [d for d in DAYS if out[d] != T]
        print(f"   {label}: eliminated "
              f"{[d for d in DAYS if out[d] == T] or '—'}, "
              f"days left for a surprise: {len(survivors)}")
    known = eliminate(T)
    credit = eliminate(Z)
    assert [d for d in DAYS if known[d] == T] == DAYS          # all gone
    assert [d for d in DAYS if credit[d] == T] == []           # none gone
    print("   0 against 5, and the logic did not change between the runs —")
    print("   only the stamp on the teacher's words did. With the stamp the")
    print("   class is RIGHT: the promise cannot be kept. Without it the")
    print("   elimination never starts, because 'we would know' rests on")
    print("   the very announcement they have not verified (greedy: Z & T")
    print(f"   = {AND(Z, T)} — a conclusion is not minted from a mark).")


def sec2_the_liar_in_the_calendar():
    print("-" * 72)
    print("2. UNDER PERFECT KNOWLEDGE, A LIAR IS SITTING INSIDE")
    # the announcement about a given day, for knowers who know whatever is
    # true the moment it is true: A holds iff the exam is today AND A is
    # not known — that is, iff the exam is today and A itself fails
    for label, exam in (("the exam IS today  ", T), ("no exam today      ", F)):
        system = {"A": ("and", "E", ("not", "A")), "E": exam}
        reports = {tuple(sorted(c)): (k, w) for c, k, w in passports(system)[1]}
        kind, why = reports.get(("A",), ("GROUNDED", "settled outright"))
        print(f"   {label}: A = (E & ~A)  ->  {kind:9} — {why}")
    sys_yes = {"A": ("and", "E", ("not", "A")), "E": T}
    kinds = {tuple(sorted(c)): k for c, k, w in passports(sys_yes)[1]}
    assert kinds[("A",)] == "PARADOX"
    sys_no = {"A": ("and", "E", ("not", "A")), "E": F}
    assert ("A",) not in {tuple(sorted(c)) for c, k, w in passports(sys_no)[1]}
    print("   so the famous puzzle is the liar wearing a calendar — but")
    print("   only for knowers whose knowledge is instantaneous and")
    print("   perfect. Take that idealisation away and the equation is")
    print("   about a day, not about itself, and it is simply grounded.")


def sec3_whose_warranty_is_it():
    print("-" * 72)
    print("3. THE SAME SENTENCE, TWO LEDGERS")
    # the announcement about the actual day: 'the exam is today AND the
    # class does not know it'. Judge it twice — once from the teacher's
    # ledger, once from the class's, changing nothing but who is holding
    # the book.
    phi = "exam_today & ~class_knows"
    teacher = judge(phi, {"exam_today": "T", "class_knows": "F"})
    pupils = judge(phi, {"exam_today": "Z", "class_knows": "Z"})
    print(f"   teacher's ledger (sets the day, sees the class): "
          f"{teacher['disposition']}")
    print(f"   class's ledger   (neither fact verified)       : "
          f"{pupils['disposition']} — verify {pupils['unverified']}")
    assert teacher["disposition"] == "EARNED"
    assert pupils["disposition"] == "OPEN"
    # and the grades behind them: hereditary there, until-verification here
    assert grade("A", {"A": T}) == "hereditary"
    assert grade("A", {"A": "M"}) == "until-verification"
    print("   one sentence, both readings correct at once, and no")
    print("   contradiction: a WARRANTY BELONGS TO A LEDGER, not to a")
    print("   sentence. The teacher's announcement is earned — by the")
    print("   teacher. The class picked up his receipt and spent it as")
    print("   their own, on Monday, for a fact that only their Wednesday")
    print("   could verify. Everything after that is honest reasoning on")
    print("   a forged stamp, which is why the argument feels airtight")
    print("   and ends in the wrong place.")


def sec4_the_everyday_case():
    print("-" * 72)
    print("4. THE EVERYDAY CASE: 'the inspection comes unannounced'")
    # the audited party's plan rests on a claim it cannot earn in advance
    plan = judge("no_inspection_today & cleanup_can_wait",
                 {"no_inspection_today": "Z", "cleanup_can_wait": "T"})
    print(f"   'no inspection today, so the cleanup can wait': "
          f"{plan['disposition']} — verify {plan['unverified']}")
    assert plan["disposition"] == "OPEN"
    assert plan["unverified"] == ["no_inspection_today"]
    # and the streak of quiet mornings buys nothing, exactly as with the heap
    streak = judge("no_inspection_today",
                   {"no_inspection_today": "Z", "quiet_for_200_days": "T"})
    assert streak["disposition"] == "OPEN"
    print("   two hundred quiet mornings do not raise it either: the")
    print("   clause is written precisely so that the audited party can")
    print("   never earn 'not today' in advance. That is not a paradox,")
    print("   it is the point of the clause — and the same shape as the")
    print("   teacher's promise, which is why the class could not")
    print("   reason its way out of the exam.")


if __name__ == "__main__":
    print("=" * 72)
    print("THE SURPRISE EXAMINATION — priced")
    print("=" * 72)
    sec1_the_calendar_twice()
    sec2_the_liar_in_the_calendar()
    sec3_whose_warranty_is_it()
    sec4_the_everyday_case()
    print("=" * 72)
    print("SURPRISE GREEN — the class's logic is sound and its stamp is")
    print("forged. Holding the announcement as knowledge, 0 days survive")
    print("and the promise refutes itself; holding it on credit, all 5 do")
    print("and Wednesday is a genuine surprise. Under perfect knowers the")
    print("case hides a liar (A = E & ~A, passport PARADOX, refusal")
    print("permanent); with ordinary knowers there is no liar at all. And")
    print("the warranty the argument leans on is hereditary only after the")
    print("exam — the class spends on Monday a receipt dated Wednesday.")
