# -*- coding: utf-8 -*-
"""
Monty Hall, judged: "should you switch?" is a question about the HOST's protocol, and the story usually leaves it out.

Three doors, a car behind one. You pick a door; the host opens another, showing a goat, and offers a switch.
vos Savant (1990): switch, 2/3. Thousands of readers: 1/2. Both answer real questions — about different hosts.

THE FORMALISATION, IN WORDS FIRST:
  the host's protocol is part of the problem. Four protocols, each computed exactly by enumerating every
  (car, pick, host's choice) with its probability, conditioned on what you saw (a goat behind an opened door and
  an offer to switch):
    STANDARD   the host knows, always opens an unpicked goat door (at random if two), always offers -> switch wins 2/3
    IGNORANT   the host opens an unpicked door at random; it happened to show a goat           -> 1/2
    HELL       the host offers a switch only when your pick is the car                         -> 0
    ANGEL      the host offers a switch only when your pick is a goat                          -> 1
  With the protocol unnamed, "switching wins with probability 2/3" is OPEN; the cure is to stipulate the protocol
  (a puzzle) or to measure it (a real host's past behaviour). With one named it is earned or refuted.

MEASURED HERE: the four probabilities exactly (Fractions over the full enumeration) and by seeded simulation
(within 0.01); the numeric judge under the protocol unnamed (a convention, P in [0, 1]) — OPEN, "stipulate P";
standard stipulated — EARNED; ignorant stipulated — REFUTED; a real host whose protocol is to be observed — "measure P".
Run:  python3 dilemmas/monty_hall.py
"""
import os
import random
import sys
from fractions import Fraction as Fr

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402

DOORS = (0, 1, 2)


def outcomes(protocol):
    """(probability, switch_wins) for every run in which you see a goat opened AND are offered the switch"""
    for car in DOORS:
        for pick in DOORS:
            base = Fr(1, 9)
            others = [d for d in DOORS if d != pick]
            if protocol == "ignorant":
                opens = [(d, Fr(1, 2)) for d in others]
            else:
                goats = [d for d in others if d != car]
                opens = [(d, Fr(1, len(goats))) for d in goats]
            for door, p in opens:
                if door == car:
                    continue                                   # a car was shown: not the situation you are in
                offered = {"standard": True, "ignorant": True,
                           "hell": pick == car, "angel": pick != car}[protocol]
                if offered:
                    yield base * p, pick != car


def win_if_switch(protocol):
    runs = list(outcomes(protocol))
    total = sum(p for p, _ in runs)
    return sum(p for p, w in runs if w) / total


def simulate(protocol, rng, n=200_000):
    seen = wins = 0
    for _ in range(n):
        car, pick = rng.randrange(3), rng.randrange(3)
        others = [d for d in DOORS if d != pick]
        door = rng.choice(others) if protocol == "ignorant" else rng.choice([d for d in others if d != car])
        if door == car:
            continue
        if {"standard": True, "ignorant": True, "hell": pick == car, "angel": pick != car}[protocol]:
            seen += 1
            wins += pick != car
    return wins / seen


if __name__ == "__main__":
    print("-" * 72)
    print("1. FOUR HOSTS, FOUR ANSWERS")
    want = {"standard": Fr(2, 3), "ignorant": Fr(1, 2), "hell": Fr(0), "angel": Fr(1)}
    rng = random.Random(1990)
    for proto, w in want.items():
        got = win_if_switch(proto)
        sim = simulate(proto, rng)
        assert got == w and abs(sim - float(w)) < 0.01, (proto, got, sim)
        print(f"   {proto:9s}: switching wins {str(got):4s} (simulated {sim:.4f})")
    print("-" * 72)
    print("2. THE JUDGE ON 'SWITCHING WINS WITH PROBABILITY 2/3'")
    rows = [("the protocol unnamed", "P=[0,1] earned:four-hosts convention", "OPEN", ["stipulate P"]),
            ("the standard host stipulated", "P=2/3 earned:standard convention", "EARNED", []),
            ("the ignorant host stipulated", "P=1/2 earned:ignorant convention", "REFUTED", []),
            ("a real host, protocol to be observed", "P=[0,1] earned:four-hosts", "OPEN", ["measure P"])]
    for label, sheet, disp, cure in rows:
        r = judge_sheet_claim("P == 2/3", *parse_quantities(sheet))
        assert r["disposition"] == disp and r["next_check"] == cure, (label, r)
        print(f"   {label:38s}: {r['disposition']:8s} {cure}")
    print("-" * 72)
    print("MONTY HALL: all measurements hold.")
