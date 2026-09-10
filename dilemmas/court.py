# -*- coding: utf-8 -*-
"""
The paradox of the court (Protagoras v. Euathlus), judged: a contract
whose condition is settled by the very judgment it is pleaded in.

Protagoras teaches rhetoric to Euathlus. Half the fee is paid at once;
the second half falls due WHEN EUATHLUS WINS HIS FIRST CASE. Euathlus
takes no cases. Protagoras sues him — and that suit is the first case.

  Protagoras: if I win, he pays by the judgment; if I lose, he has won
              his first case, so he pays by the contract. Either way.
  Euathlus:   if I win, I do not pay by the judgment; if I lose, I have
              not won my first case, so I owe nothing by the contract.
              Either way.

Two impeccable arguments, opposite conclusions. Aulus Gellius (Noctes
Atticae V.10) reports that the judges adjourned the case to a distant
day — the tradition has argued about which side is right ever since.

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:

  V  the court rules FOR PROTAGORAS in this suit
  W  "Euathlus has won his first case", the contract's condition
  and the one link the arguments never write down:  W = ¬V
  because this suit IS the first case, so Euathlus wins it exactly when
  the court rules against Protagoras.

  Euathlus owes BY THE JUDGMENT  iff V.
  Euathlus owes BY THE CONTRACT  iff W.

MEASURED HERE:

  1. the two sources are exact negations of each other, in 2 branches of
     2: whichever way the court rules, judgment and contract point
     opposite ways. The famous dilemma is not "pays or not" — it is that
     the case has two ledgers and they disagree by construction;
  2. hold the condition as decided and each side proves its own
     conclusion — 2 of 2 branches, both sides. Hold it as what it is at
     the moment of the ruling, unverified, and neither side earns
     anything: 0 of 2, both sides. The contradiction is not made by the
     logic. It is made by spending a fact the judgment has not yet
     issued;
  3. require the court to decide BY the contract at that moment and the
     case is a liar: V = W, W = ¬V gets the passport PARADOX, no
     classical models, oscillation period 4, refusal PERMANENT. Read the
     contract on the state of the world AT FILING and there is no
     paradox at all — the system is grounded, Protagoras loses, and the
     SECOND suit, brought on a condition that is now verified, he wins;
  4. the everyday shape, and Holmes saw it in 1881: "all conditions are
     precedent to the moment at which the promisor is compelled to pay"
     (The Common Law, Lecture IX). A clause whose fact is fixed BY the
     outcome of the dispute about that clause cannot be tried in that
     dispute. Not void — unverified. The sound order is not a verdict
     but a GROUNDING ORDER: settle the fact first, then judge.

Run:  python3 dilemmas/court.py
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z, NOT                                 # noqa: E402
from ztljudge import judge                                   # noqa: E402
from zpassport import passports                              # noqa: E402
from zverify import grade                                    # noqa: E402

BRANCHES = (("the court rules FOR Protagoras", T),
            ("the court rules FOR Euathlus  ", F))


def sec1_two_ledgers():
    print("-" * 72)
    print("1. TWO LEDGERS, AND THEY DISAGREE BY CONSTRUCTION")
    disagree = 0
    for label, v in BRANCHES:
        w = NOT(v)                       # this suit IS the first case
        by_judgment, by_contract = v, w
        if by_judgment != by_contract:
            disagree += 1
        print(f"   {label}: owes by judgment {by_judgment} · "
              f"owes by contract {by_contract}")
    assert disagree == len(BRANCHES)
    print(f"   {disagree} of {len(BRANCHES)} branches disagree — every one.")
    print("   The contract's condition is the NEGATION of the judgment in")
    print("   this suit, so no ruling can satisfy both books. That is the")
    print("   dilemma, and it is arithmetic, not rhetoric.")


def sec2_the_price_of_deciding_it_early():
    print("-" * 72)
    print("2. THE SAME ARGUMENTS, WITH THE CONDITION DECIDED AND UNDECIDED")
    # each side's own inference, run in its own branch. Protagoras leans on
    # the branch where he loses (then W is true); Euathlus on the branch
    # where he loses (then W is false).
    settled = credit = 0
    for who, formula, marks_decided in (
            ("Protagoras: 'he owes me'   ", "won_first_case",
             {"won_first_case": "T"}),
            ("Euathlus:   'I owe nothing'", "~won_first_case",
             {"won_first_case": "F"})):
        d = judge(formula, marks_decided)
        c = judge(formula, {"won_first_case": "Z"})
        settled += d["disposition"] == "EARNED"
        credit += c["disposition"] == "EARNED"
        print(f"   {who}: condition DECIDED -> {d['disposition']:7} · "
              f"UNVERIFIED -> {c['disposition']} "
              f"(verify {c['unverified']})")
    assert settled == 2 and credit == 0
    print(f"   {settled} of 2 earned while the condition is spent as decided,")
    print(f"   {credit} of 2 once it is read as it stands at the ruling. Both")
    print("   sides are refuted by THE SAME missing fact — and neither is")
    print("   refuted by the other. In classical logic both conclusions are")
    print("   asserted and the case explodes; here neither is asserted, and")
    print("   what the ledger returns is not a winner but a thing to verify.")
    assert grade("A", {"A": "M"}) == "until-verification"


def sec3_the_liar_in_the_contract():
    print("-" * 72)
    print("3. DECIDE BY THE CONTRACT AT THAT MOMENT — AND IT IS A LIAR")
    loop = {"V": "W", "W": ("not", "V")}          # judgment by contract,
    reports = {tuple(sorted(c)): (k, w) for c, k, w in passports(loop)[1]}
    kind, why = reports[("V", "W")]
    print(f"   V = W, W = ¬V  ->  {kind} — {why}")
    assert kind == "PARADOX"
    at_filing = passports({"V": F})               # contract read as it stands
    assert at_filing[1] == []
    print(f"   read at FILING (nothing won yet, W = F)  ->  grounded, "
          f"V = {at_filing[0]['V']}: Protagoras loses")
    second = judge("won_first_case", {"won_first_case": "T"})
    assert second["disposition"] == "EARNED"
    print(f"   and the SECOND suit, on a condition now verified  ->  "
          f"{second['disposition']}: he wins")
    print("   The paradox is not in the story. It appears exactly when the")
    print("   court is required to decide by a clause whose fact its own")
    print("   decision creates — and it disappears when the fact is grounded")
    print("   first. Gellius says the judges adjourned to a distant day.")
    print("   That was not evasion. It was the only sound order available.")


def sec4_the_everyday_clause():
    print("-" * 72)
    print("4. THE EVERYDAY CLAUSE")
    # a fee owed 'if we win', tried in the suit that decides whether we won
    now = judge("we_won_this_case", {"we_won_this_case": "Z"})
    later = judge("we_won_this_case", {"we_won_this_case": "T"})
    print(f"   'the fee falls due if we win', tried IN that suit: "
          f"{now['disposition']} — verify {now['unverified']}")
    print(f"   the same clause after judgment:                    "
          f"{later['disposition']}")
    assert now["disposition"] == "OPEN" and later["disposition"] == "EARNED"
    # the drafter's test: is there any other way to verify the condition?
    other = judge("we_won_this_case | independent_record",
                  {"we_won_this_case": "Z", "independent_record": "T"})
    assert other["disposition"] == "EARNED"
    print(f"   with an INDEPENDENT way to verify the same condition: "
          f"{other['disposition']}")
    print("   so the drafter's test is one question: can this condition be")
    print("   verified by anything other than the outcome of this dispute?")
    print("   If not, the clause cannot be tried here — and a court that")
    print("   rules anyway is not resolving a paradox, it is issuing a")
    print("   verdict on a fact it has not got.")


def sec5_three_questions_one_case():
    print("-" * 72)
    print("5. THREE QUESTIONS, ONE CASE — AND ONLY ONE OF THEM HAS NO ANSWER")
    # the reader wants a yes or a no. The case HAS them; they belong to
    # questions people forget to keep apart.
    now = judge("owes_now", {"owes_now": "F"})                 # read at filing
    ever = judge("owes_after_first_win", {"owes_after_first_win": "T"})
    loop = {"V": "W", "W": ("not", "V")}
    kinds = {tuple(sorted(c)): k for c, k, w in passports(loop)[1]}
    print(f"   'does he owe NOW?'                     -> "
          f"{now['disposition']:7} · verdict {now['verdict']} — NO")
    print(f"   'will he owe once he wins a case?'     -> "
          f"{ever['disposition']:7} · verdict {ever['verdict']} — YES")
    print(f"   'settle it BY THAT CLAUSE, now?'       -> "
          f"{kinds[('V', 'W')]} — no assignment agrees with the clause's")
    print("                                              own definition, and")
    print("                                              no discovery repairs it")
    # "he owes now" is REFUTED — which is the definite NO, not a missing answer
    assert now["disposition"] == "REFUTED" and now["verdict"] == "F"
    assert ever["disposition"] == "EARNED" and ever["verdict"] == "T"
    assert kinds[("V", "W")] == "PARADOX"
    print("   Two crisp answers and one provable refusal. The paradox is not")
    print("   a property of the case — it is a property of the THIRD QUESTION.")
    print("   And the three refusals are not one thing: OPEN says GO AND FIND")
    print("   THE FACT; PARADOX says THERE IS NO FACT TO FIND, THE CLAUSE IS")
    print("   THE DEFECT. Opposite instructions to the same person. A system")
    print("   that can only answer yes or no will answer the third question")
    print("   too, and its answer is a stamp on nothing.")


def sec6_two_courts_do_not_help(steps=4):
    """The curator's question, 2026-09-10: the oscillation period is EVEN —
    might the answer be two courts in a row? Measured, and the answer is no,
    for a reason worth more than a yes."""
    print("-" * 72)
    print("6. THE PERIOD IS 4, AND TWO SUITS ARE 4 STEPS — DOES ITERATING HELP?")
    # one suit is two steps: the court reads the contract (W -> V), and the
    # outcome fixes the contract's condition (V -> W).
    state = (T, T)
    trace = [state]
    for _ in range(steps):
        v, w = state
        state = (w, NOT(v))
        trace.append(state)
    print("   suit 1: " + " -> ".join(f"(V={v},W={w})" for v, w in trace[:3]))
    print("   suit 2: " + " -> ".join(f"(V={v},W={w})" for v, w in trace[2:5]))
    assert trace[0] == trace[steps]                 # exactly one full period
    print(f"   after {steps} steps — two whole suits — the state is the one we")
    print(f"   started from: {trace[0]}. Period 4 does not mean 'settled on the")
    print("   fourth step'. It means the fourth step is the first one again.")
    # and now the same two suits with the world changed in between: after the
    # first judgment, 'he won a case' stops being a function of the next
    # verdict and becomes a RECORD.
    first = judge("owes_now", {"owes_now": "F"})
    second = judge("won_first_case", {"won_first_case": "T"})
    assert first["disposition"] == "REFUTED"
    assert second["disposition"] == "EARNED" and second["grade"] == "hereditary"
    print(f"   the SAME two suits, with the fact grounded in between:")
    print(f"     suit 1 'does he owe now'  -> {first['disposition']} (NO)")
    print(f"     suit 2 'has he won a case'-> {second['disposition']}, "
          f"{second['grade']} (YES)")
    print("   Two courts help — and not because there were two of them. In")
    print("   between, the first judgment CHANGED THE WORLD: 'he has won a")
    print("   case' stopped being a function of the next verdict and became a")
    print("   matter of record. The second court reads a fact, not a loop.")
    print("   REPEATING A PROCEDURE IS NOT GROUNDING A FACT — and that is")
    print("   exactly the mistake the even period tempts you into: appeal")
    print("   again, review again, re-run the committee, and arrive at the")
    print("   state you began with, having spent two rounds.")


def sec7_the_signature_of_a_paradox(max_len=6):
    """The curator's second remark, 2026-09-10: the even period is not a
    quirk of THIS case, it is a property of the paradox. Measured over every
    simple loop up to `max_len` nodes and every placement of negations."""
    print("-" * 72)
    print("7. WHY THE PERIOD IS EVEN — THE SIGNATURE OF A PARADOX")
    seen = {}
    for n in range(1, max_len + 1):
        for mask in range(1 << n):                  # which edges carry a NOT
            system = {}
            for i in range(n):
                nxt = f"x{(i + 1) % n}"
                system[f"x{i}"] = ("not", nxt) if (mask >> i) & 1 else nxt
            odd = bin(mask).count("1") % 2 == 1
            rows = passports(system)[1]
            kind = rows[0][1] if rows else "GROUNDED"
            period = None
            if rows and "period" in rows[0][2]:
                period = int(rows[0][2].split("period")[1].split(";")[0])
            seen.setdefault((odd, kind), []).append((n, period))
    for (odd, kind), got in sorted(seen.items()):
        periods = sorted({p for _, p in got if p is not None})
        print(f"   negations {'ODD ' if odd else 'EVEN'} -> {kind:16} "
              f"in {len(got):3} loops · periods {periods}")
    # the law, stated and checked: an ODD number of negations round the loop
    # is exactly a paradox, and its period is never odd.
    kinds_odd = {k for (o, k) in seen if o}
    kinds_even = {k for (o, k) in seen if not o}
    assert kinds_odd == {"PARADOX"}
    assert "PARADOX" not in kinds_even
    for (odd, kind), got in seen.items():
        if kind == "PARADOX":
            assert all(p is not None and p % 2 == 0 for _, p in got)
    print("   Every loop that flips an ODD number of times is a PARADOX, and")
    print("   not one of them has an odd period. Every loop that flips an EVEN")
    print("   number of times is not a paradox at all. The reason is one line:")
    print("   go once round an odd loop and every value comes back inverted, so")
    print("   no assignment survives a full turn — and the walk can only close")
    print("   after going round TWICE. The even period is not a hint about how")
    print("   many courts to hold. It is the FINGERPRINT of the refusal.")


if __name__ == "__main__":
    print("=" * 72)
    print("THE PARADOX OF THE COURT — priced")
    print("=" * 72)
    sec1_two_ledgers()
    sec2_the_price_of_deciding_it_early()
    sec3_the_liar_in_the_contract()
    sec4_the_everyday_clause()
    sec5_three_questions_one_case()
    sec6_two_courts_do_not_help()
    sec7_the_signature_of_a_paradox()
    print("=" * 72)
    print("COURT GREEN — the contract's condition is the negation of the")
    print("judgment in this very suit, so the two books disagree in 2 of 2")
    print("branches. Each side earns its conclusion only by spending a fact")
    print("the ruling has not yet issued: 2 of 2 with the condition held")
    print("decided, 0 of 2 with it held as it stands. Require the court to")
    print("decide by that clause and the case is a liar (V = W, W = ¬V,")
    print("passport PARADOX, period 4, refusal PERMANENT); ground the fact")
    print("first and there is no paradox — only a suit brought too early.")
