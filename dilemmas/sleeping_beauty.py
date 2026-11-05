# -*- coding: utf-8 -*-
"""
The Sleeping Beauty problem, judged: two ledgers, and "the probability of heads" names neither.

Sunday: Beauty is put to sleep and a fair coin is tossed. Heads: she is woken on Monday only. Tails: she is woken
on Monday and on Tuesday, and the Monday waking is erased from her memory. On each waking she is asked: what is
your credence that the coin landed heads? Halfers say 1/2 (she learns nothing she did not know on Sunday);
thirders say 1/3 (she is in one of three wakings, one of them a heads waking). Elga (2000), Lewis (2001).

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:

  TWO LEDGERS, as in the court of Protagoras (dilemmas/court.py): the same runs, counted by two units.
    per EXPERIMENT   one entry per coin toss         -> the share of heads entries is 1/2
    per AWAKENING    one entry per waking            -> the share of heads entries is 1/3 (H: 1 waking, T: 2)
  Both are correct counts. "The probability of heads" fixes a value only once the unit is named — the unit is a
  CONVENTION (znumjudge token `convention`, 2026-11-05), not a fact Beauty could look up.
  BETS make the unit physical: a bet on heads at price p, paid at EVERY waking, breaks even at p = 1/3; settled
  ONCE per experiment, at p = 1/2. Under a named payment protocol the right price is a measurable frequency.

MEASURED HERE (each section asserts what it prints):

  1. the two ledgers exactly (fractions) and by seeded simulation (each within 0.01);
  2. the two betting protocols: expected profit per experiment of a heads bet at price p is exactly 0 at p = 1/3
     (paid per waking) and at p = 1/2 (settled once), positive below and negative above — each protocol has one
     break-even price, and halfers and thirders AGREE on it once the protocol is named;
  3. the numeric judge on "P == 1/2", "P == 1/3", "P <= 1/2", "P >= 1/3":
       the unit unnamed, P a convention between the two ledgers: OPEN / OPEN / EARNED / EARNED, cure "stipulate P";
       per experiment stipulated: EARNED / REFUTED / EARNED / EARNED;
       per awakening stipulated:  REFUTED / EARNED / EARNED / EARNED;
       P as the break-even price of a NAMED protocol, not yet computed: OPEN, cure "measure P";

NOT CLAIMED: what Beauty's credence "really" is. Whether credence is per waking by its nature (a centred belief)
or per world is the live philosophical dispute; the judge records that the answer rides on that choice, prices
what holds either way (1/3 <= P <= 1/2), and names the choice as the thing to settle. That the dispute dissolves
once the counting unit or the payment protocol is fixed is known (e.g. Groisman 2008, "The End of Sleeping
Beauty's Nightmare"); what is added here is the same form the judge gives every such case.

Run:  python3 dilemmas/sleeping_beauty.py
"""
import os
import random
import sys
from fractions import Fraction

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402

N = 200_000
WAKINGS = {"H": 1, "T": 2}


def ledgers_exact():
    # each outcome has probability 1/2; per experiment: one entry each; per waking: 1 heads entry, 2 tails entries
    per_experiment = Fraction(1, 2)
    per_awakening = Fraction(WAKINGS["H"], WAKINGS["H"] + WAKINGS["T"])
    return per_experiment, per_awakening


def sec1_two_ledgers():
    print("-" * 72)
    print("1. TWO LEDGERS OVER THE SAME RUNS")
    pe, pa = ledgers_exact()
    assert (pe, pa) == (Fraction(1, 2), Fraction(1, 3))
    rng = random.Random(2000)
    exp_heads = wake_heads = wakes = 0
    for _ in range(N):
        c = "H" if rng.random() < 0.5 else "T"
        exp_heads += c == "H"
        wake_heads += WAKINGS[c] if c == "H" else 0
        wakes += WAKINGS[c]
    se, sa = exp_heads / N, wake_heads / wakes
    assert abs(se - 0.5) < 0.01 and abs(sa - 1 / 3) < 0.01
    print(f"   per experiment: exact {pe}  simulated {se:.4f}")
    print(f"   per awakening:  exact {pa}  simulated {sa:.4f}")


def profit(p, protocol):
    """expected profit per experiment of a bet on heads that costs p and pays 1 if heads"""
    if protocol == "per waking":       # the bet is made and settled at every waking
        return Fraction(1, 2) * WAKINGS["H"] * (1 - p) + Fraction(1, 2) * WAKINGS["T"] * (-p)
    return Fraction(1, 2) * (1 - p) + Fraction(1, 2) * (-p)    # settled once per experiment


def sec2_bets():
    print("-" * 72)
    print("2. BETS MAKE THE UNIT PHYSICAL")
    for protocol, even in (("per waking", Fraction(1, 3)), ("once per experiment", Fraction(1, 2))):
        assert profit(even, protocol) == 0
        assert profit(even - Fraction(1, 100), protocol) > 0 > profit(even + Fraction(1, 100), protocol)
        print(f"   paid {protocol:20s}: break-even price {even}; cheaper wins, dearer loses")
    print("   Name the protocol and halfers and thirders quote the same price.")


GROUNDS = [
    ("the unit unnamed (P a convention)", "P=[1/3,1/2] earned:two-ledgers convention",
     ["OPEN", "OPEN", "EARNED", "EARNED"], ["stipulate P"]),
    ("per experiment stipulated", "P=1/2 earned:per-experiment convention",
     ["EARNED", "REFUTED", "EARNED", "EARNED"], []),
    ("per awakening stipulated", "P=1/3 earned:per-awakening convention",
     ["REFUTED", "EARNED", "EARNED", "EARNED"], []),
    ("break-even of a named protocol, not computed", "P=[1/3,1/2] earned:two-ledgers",
     ["OPEN", "OPEN", "EARNED", "EARNED"], ["measure P"]),
]
CLAIMS = ["P == 1/2", "P == 1/3", "P <= 1/2", "P >= 1/3"]


def sec3_the_judge():
    print("-" * 72)
    print("3. THE JUDGE: WHAT RIDES ON THE UNIT, AND WHAT HOLDS EITHER WAY")
    print(f"   {'ground':45s} " + "  ".join(f"{c:8s}" for c in CLAIMS) + "  cure for 'P == 1/2'")
    for label, sheet, want, cure in GROUNDS:
        qs, marks = parse_quantities(sheet)
        rs = [judge_sheet_claim(c, qs, marks) for c in CLAIMS]
        got = [r["disposition"] for r in rs]
        assert got == want, (label, got)
        assert rs[0]["next_check"] == cure, (label, rs[0]["next_check"])
        print(f"   {label:45s} " + "  ".join(f"{g:8s}" for g in got) + f"  {cure}")


if __name__ == "__main__":
    for sec in (sec1_two_ledgers, sec2_bets, sec3_the_judge):
        sec()
    print("-" * 72)
    print("SLEEPING BEAUTY: all measurements hold.")
