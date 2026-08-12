# -*- coding: utf-8 -*-
"""
"Ought implies can", judged: three kinds of impossible duty.

Kant's principle — a duty presupposes the power to discharge it — is
still contested (defenders of genuine moral dilemmas hold that one can be
bound to incompatible things). This stand does not argue the principle.
It asks the machine's question: WHAT KIND of object is an unfulfillable
norm, and WHO is answerable for it.

Measured here, and the trichotomy is the finding:

  E         the clause is not a demand at all. Its own specification has
            no admissible reading — a quantity no value satisfies, a
            requirement stated in units that cannot meet. Nothing was
            asked, so nothing can be obeyed or disobeyed. The author of
            the clause is named.
  REFUTED   each clause is fine alone; TOGETHER they have no solution.
            This is a proved impossibility with a witness — the pair —
            and it is stronger than a complaint: compliance is not
            missing, it is unavailable.
  OPEN      the ordinary case: compliance is not yet established and the
            act is still owed. This is where duty actually lives.

The ethical consequence is the same in the first two and it is not
neutral: the agent who fails an E or a REFUTED duty has not failed. The
defect is in the declaration, and the ledger prints its signature. What
distinguishes them is only whether the impossibility is inside one clause
or between two — which decides whether one author is charged or a pair.

And the case with no author at all: where reality, not a rule-maker,
offers incompatible goods, the same REFUTED verdict appears with nobody
to charge. The machine says the demand cannot be met and declines to
invent a culprit — which is the correct silence.

Run:  python3 dilemmas/ought_can.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import (judge_sheet_claim, parse_quantities,      # noqa: E402
                       e_census)
from znumsolve import solve_claim                                # noqa: E402


def sec1_the_ordinary_duty():
    print("-" * 72)
    print("1. THE ORDINARY DUTY: compliance owed, not yet shown")
    q, m = parse_quantities("filed_on=? credit int, deadline=10 earned:reg-3")
    r = judge_sheet_claim("filed_on <= deadline", q, m)
    print(f"   'filed by the 10th?': {r['disposition']}   "
          f"cure {r['next_check']}")
    assert r["disposition"] == "OPEN"
    print("   the act is still owed and the ledger says what would settle")
    print("   it. This is duty in working order — and the baseline the")
    print("   other two are measured against.")
    print("   (Method note, caught by the machine while this was written:")
    print("   do NOT put a norm through the SOLVER. Narrowing pins the")
    print("   unknown to the compliant range and the norm comes out")
    print("   satisfied by construction — a tautology, not a judgment. The")
    print("   date of filing is a FACT to be verified, not an unknown to")
    print("   be solved for; compliance must be measured, never derived.)")


def sec2_the_clause_that_asks_nothing():
    print("-" * 72)
    print("2. E — THE CLAUSE THAT ASKS NOTHING")
    cases = [
        ("headcount must be a whole number between 0.2 and 0.9",
         "headcount >= 1",
         "headcount=[0.2,0.9] credit int"),
        ("the fee must equal the floor area",
         "fee == area",
         "fee=5 earned:reg-7 RUB, area=3 earned:plan m2"),
        ("compensate the damage with the flight hours",
         "damage == hours",
         "damage=200000 earned:akt RUB, hours=12 earned:log h"),
    ]
    for title, formula, data in cases:
        q, m = parse_quantities(data)
        r = judge_sheet_claim(formula, q, m)
        print(f"   {title[:44]:46} {r['disposition']}  — {r['why']}")
        assert r["disposition"] == "E"
    print("   None of these was disobeyed, because none of them ASKED. A")
    print("   clause whose own specification has no reading is not a demand")
    print("   that failed; it is a description that never worked. Nobody")
    print("   can comply, and nobody has offended.")


def sec3_the_pair_that_cannot_be_obeyed():
    print("-" * 72)
    print("3. REFUTED — EACH CLAUSE FINE, THE PAIR IMPOSSIBLE")
    q, m = parse_quantities("filed_on=? int, early=10 earned:reg-3, "
                            "late=15 earned:reg-9")
    r = solve_claim("filed_on <= early & filed_on >= late", q, m)
    print(f"   'file by the 10th' AND 'not before the 15th': "
          f"{r['disposition']}")
    assert r["disposition"] == "REFUTED"
    # and each half alone is perfectly fulfillable
    q1, m1 = parse_quantities("filed_on=? int, early=10 earned:reg-3")
    q2, m2 = parse_quantities("filed_on=? int, late=15 earned:reg-9")
    # the question here is EXISTENCE — is there any compliant date? — so
    # the solver is the right tool, and the honest read-out is whether the
    # box came back empty, not the disposition of a compliance claim
    a = solve_claim("filed_on <= early", q1, m1)["disposition"] != "REFUTED"
    b = solve_claim("filed_on >= late", q2, m2)["disposition"] != "REFUTED"
    print(f"   a compliant date exists for each half alone: {a} and {b}")
    assert a and b
    print("   so the impossibility lives BETWEEN the clauses, not inside")
    print("   either — and the address is the pair, reg-3 with reg-9. This")
    print("   is not a complaint about bureaucracy; it is a proof, and the")
    print("   proof is what an appeal needs.")


def sec4_the_dilemma_with_no_author():
    print("-" * 72)
    print("4. THE SAME SHAPE WITH NOBODY TO CHARGE")
    # two goods, one resource: the classic tragic choice, with no
    # rule-maker anywhere — reality itself offers the incompatible pair
    q, m = parse_quantities("given_to_a=? int, given_to_b=? int, "
                            "have=1 earned:fact, need_a=1 earned:fact, "
                            "need_b=1 earned:fact")
    r = solve_claim("given_to_a >= need_a & given_to_b >= need_b "
                    "& sum(given_to_a,given_to_b) <= have", q, m)
    print(f"   'save both, with means for one': {r['disposition']}")
    assert r["disposition"] == "REFUTED"
    print("   the same verdict as the contradictory regulation, and the")
    print("   same exoneration of the agent — but here the ledger has no")
    print("   signature to print, because no one declared anything. The")
    print("   machine says the demand cannot be met and does NOT invent a")
    print("   culprit. That silence is the correct output, and it is the")
    print("   difference between a cruel rule and a cruel world.")


def sec5_the_census_on_a_regulation():
    print("-" * 72)
    print("5. THE CENSUS ON A SMALL REGULATION")
    reg = [
        ("art_1", "headcount <= cap",
         "headcount=[0.2,0.9] earned:reg-7 int, cap=75 earned:law"),
        ("art_2", "fee == area", "fee=5 earned:reg-7 RUB, area=3 earned:plan m2"),
        ("art_3", "filed_on <= deadline",
         "filed_on=5 earned:clerk int, deadline=10 earned:law int"),
        ("art_4", "quota >= floor",
         "quota=[0.1,0.4] earned:reg-7 int, floor=1 earned:law"),
    ]
    census = e_census(reg)
    print(f"   articles: {census['claims']}, unjudgeable: "
          f"{census['unjudgeable']}")
    print(f"   charged to a signature: {census['by_signature']}")
    print(f"   charged to nobody (a pairing): {census['pairings']}")
    assert census["unjudgeable"] == 3
    assert census["by_signature"] == {"reg-7": 2}
    print("   two of the four articles are not demands at all, and both")
    print("   carry one signature. That is not an accusation of intent —")
    print("   the ledger cannot see intent — it is an address, and a")
    print("   distribution. One is a slip; two of four is a hand.")


if __name__ == "__main__":
    print("=" * 72)
    print("OUGHT IMPLIES CAN — impossible duties, sorted by kind")
    print("=" * 72)
    sec1_the_ordinary_duty()
    sec2_the_clause_that_asks_nothing()
    sec3_the_pair_that_cannot_be_obeyed()
    sec4_the_dilemma_with_no_author()
    sec5_the_census_on_a_regulation()
    print("=" * 72)
    print("OUGHT_CAN GREEN — an unfulfillable duty is not one thing but")
    print("three. E: the clause asks nothing, its own specification having")
    print("no reading, and its author is named. REFUTED: each clause is")
    print("sound and the pair has no solution — a proved impossibility with")
    print("an address. OPEN: the ordinary case, where the act is still")
    print("owed. In the first two the agent who 'failed' did not, and the")
    print("defect is in the declaration; and where reality rather than a")
    print("rule-maker offers the incompatible pair, the same refutation")
    print("comes back with nobody to charge — the machine declining to")
    print("invent a culprit, which is the correct silence.")
