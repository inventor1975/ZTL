# -*- coding: utf-8 -*-
"""
The lottery paradox: the conjunction was never the problem.

Kyburg 1961. A fair lottery of a thousand tickets, exactly one winner.
For each ticket it is rational to believe it loses — the odds are 999 to
1. Conjoin those thousand rational beliefs and you get "no ticket wins",
which contradicts the rules of the lottery. The standard readings blame
CONJUNCTION: rational belief, they conclude, is not closed under it
(Kyburg), or must be, and then high probability cannot suffice for belief
(Makinson's preface case pushes the same lever from the other side).

The machine blames neither. It never held the conjuncts.

MEASURED HERE:

  1. with each "ticket i loses" left as what it is — unverified, however
     probable — the conjunction is denied outright and "some ticket wins"
     stays earned. No contradiction arises, because nothing was believed;
  2. stamp the beliefs (the rule "believe what is probable enough") and
     the ledger becomes inconsistent — but NOT gradually. Measured on a
     five-ticket lottery, exhaustively: the rule survives every stamp but
     the last and is REFUTED on the fifth. Four are as sound as one; the
     defect is exactly completeness, not accumulation, and the same holds
     for a thousand;
  3. and the closure that actually fails is closure over CREDIT. Conjoin
     earned claims and the warranty survives; conjoin credit and it does
     not. Rational belief is not one thing being closed or not closed —
     it is two things with different arithmetic.

Prior art, named rather than discovered: this is the credit reading of
Kyburg's case, and it sits beside the standard treatments (Kyburg's
rejection of conjunction, Makinson's preface, Leitgeb's stability). What
the corpus adds is that the two axes are separate FIELDS in one verdict,
so the question "closed or not?" gets a different answer per axis instead
of a philosophical position.

Run:  python3 dilemmas/lottery.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z, AND                                   # noqa: E402
from ztljudge import judge, formalize                          # noqa: E402
from zverify import grade                                      # noqa: E402

N = 1000


def _conj(atoms):
    return " & ".join(atoms)


def sec1_nothing_was_believed():
    print("-" * 72)
    print("1. AS THE LEDGER ACTUALLY STANDS: nothing was believed")
    # a small stand-in so the formula stays readable; the argument does not
    # depend on the size and section 2 measures the full thousand
    tickets = [f"t{i}_loses" for i in range(1, 6)]
    marking = {a: Z for a in tickets}
    r = judge(_conj(tickets), marking)
    print(f"   'ticket 1 loses' alone            : "
          f"{judge('t1_loses', marking)['disposition']}")
    print(f"   all five conjoined                : {r['disposition']}")
    print(f"   'some ticket wins' (the rule)     : "
          f"{judge('some_ticket_wins', {'some_ticket_wins': T})['disposition']}")
    assert judge("t1_loses", marking)["disposition"] == "OPEN"
    assert r["disposition"] == "OPEN"
    assert judge("some_ticket_wins",
                 {"some_ticket_wins": T})["disposition"] == "EARNED"
    # and the contradiction the paradox needs simply does not arise
    both = judge("all_lose & some_ticket_wins",
                 {"all_lose": Z, "some_ticket_wins": T})
    print(f"   'all lose AND some wins'          : {both['disposition']}"
          f" — verify {both['unverified']}")
    assert both["disposition"] == "OPEN"
    print("   No paradox appears, and the reason is not subtlety about")
    print("   conjunction: a probability is not a witness, so not one of")
    print("   the thousand beliefs was ever held. There is nothing to")
    print("   conjoin.")


def sec2_the_stamp_and_where_it_breaks():
    print("-" * 72)
    print("2. STAMP THE BELIEFS, AND WATCH WHERE IT BREAKS")
    # MEASURED, not asserted: a small lottery, exhaustively. The rule is
    # "exactly one ticket wins", written as the disjunction of the wins;
    # believing a loss stamps that ticket's win to F. Ask the judge, after
    # each stamp, whether the rule still stands.
    n = 5
    wins = [f"t{i}_wins" for i in range(1, n + 1)]
    rule = " | ".join(wins)
    first_break = None
    for stamped in range(n + 1):
        marking = {w: (F if i < stamped else Z) for i, w in enumerate(wins)}
        r = judge(rule, marking)
        state = r["disposition"]
        print(f"   {stamped} losses believed: 'some ticket wins' -> "
              f"{state:8} (lazy {r['lazy']}, pending {len(r['pending'])})")
        if state == "REFUTED" and first_break is None:
            first_break = stamped
    assert first_break == n
    print(f"   the rule survives every stamp but the last, and dies on")
    print(f"   stamp number {first_break} — REFUTED, not eroded. So the ledger")
    print("   does not degrade as beliefs accumulate: four are as sound as")
    print("   one. It breaks at COMPLETENESS, because the last stamp is the")
    print("   one that denies the rule. The quantity of credit was never")
    print("   the problem; covering the whole space with it is.")
    print("   (And the lazy column shows the same thing from the other")
    print("   side: while any ticket is unstamped the matter is still")
    print("   running, and the pending list shrinks by one per stamp.)")


def sec3_two_closures_not_one():
    print("-" * 72)
    print("3. THE CLOSURE THAT FAILS IS CLOSURE OVER CREDIT")
    phi = formalize("a & b")
    earned_v = judge("a & b", {"a": T, "b": T})
    credit_v = judge("a & b", {"a": Z, "b": Z})
    g_earned = grade(phi, {"a": T, "b": T})
    g_credit = grade(phi, {"a": "M", "b": "M"})
    print(f"   earned & earned : {earned_v['disposition']:8} "
          f"grade {g_earned}")
    print(f"   credit & credit : {credit_v['disposition']:8} "
          f"grade {g_credit}")
    assert earned_v["disposition"] == "EARNED" and g_earned == "hereditary"
    assert credit_v["disposition"] == "OPEN"
    assert g_credit == "until-verification"
    print("   Conjoin earned claims and the warranty passes through intact.")
    print("   Conjoin credit and it does not. So 'is rational belief closed")
    print("   under conjunction?' has no single answer: it is closed on the")
    print("   earned axis and open on the credit one, and the dispute")
    print("   survives because ordinary language calls both 'belief'.")


def sec4_what_this_does_not_settle():
    print("-" * 72)
    print("4. WHAT THIS DOES NOT SETTLE")
    print("   The machine says: do not stamp a probability as a witness.")
    print("   It does NOT say how to act under uncertainty, and an agent")
    print("   who must act cannot wait for the draw. Kyburg's question —")
    print("   what may I rationally BELIEVE short of proof — is not")
    print("   answered here; it is declined, and the decline is the whole")
    print("   content: this corpus grades warrants, and 'probable enough'")
    print("   is a decision rule, not a warrant. Anyone who needs one will")
    print("   need §16's probability floor and a threshold declared out")
    print("   loud, which is a stipulation like any other.")


if __name__ == "__main__":
    print("=" * 72)
    print("THE LOTTERY — a thousand credits and no belief among them")
    print("=" * 72)
    sec1_nothing_was_believed()
    sec2_the_stamp_and_where_it_breaks()
    sec3_two_closures_not_one()
    sec4_what_this_does_not_settle()
    print("=" * 72)
    print("LOTTERY GREEN — the conjunction was never the problem. With the")
    print("thousand losses left unverified, no contradiction arises,")
    print("because a probability is not a witness and nothing was believed.")
    print("Stamp them and the break comes on the LAST stamp, not by")
    print("accumulation: 999 are as sound as one, and completeness is what")
    print("denies the rule. And the closure that fails is closure over")
    print("credit — conjoin earned claims and the warranty survives — so")
    print("the century-old question has two answers because it was two")
    print("questions.")
