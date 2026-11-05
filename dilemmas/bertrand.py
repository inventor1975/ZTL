# -*- coding: utf-8 -*-
"""
Bertrand's chord, judged: "a random chord" names no measure.

Joseph Bertrand (Calcul des probabilités, 1889): draw a chord of a circle at random; what is the probability that it
is longer than the side of the inscribed equilateral triangle? Three natural ways to draw it give three answers —
1/3, 1/2, 1/4 — and each argument is correct. The paradox is that one question has three right answers.

THE FORMALISATION, IN WORDS FIRST — a bad skeleton refutes a straw man:

  P       "the probability that the chord is longer than the triangle's side" — a quantity.
  A METHOD is a stipulation: it fixes the measure on chords, and only then does P have a value.
  The three classical methods (r = 1, the side is sqrt(3), a chord is longer iff its distance from the centre < 1/2):
    endpoints  both ends uniform on the circle          -> P = 1/3 (the far end lands on the opposite third)
    radius     a radius at random, a point uniform on it -> P = 1/2 (distance uniform on [0, 1])
    midpoint   the chord's midpoint uniform in the disk  -> P = 1/4 (the inner disk of radius 1/2, area 1/4)
  A FAMILY of radius-style methods, distance = u^k with u uniform: P = (1/2)^(1/k), which takes EVERY value in
  (0, 1) as k runs over (0, inf) — so "a natural method" fixes nothing by itself; the repertoire must be named.

MEASURED HERE (each section asserts what it prints):

  1. the three values exactly (closed forms, as fractions) and by seeded simulation (an independent check: each
     within 0.01 of its exact value);
  2. the family reaches any target in (0, 1): for 0.05, 0.25, 1/3, 0.5, 0.9 a k is computed and the simulated P
     agrees within 0.01;
  3. the numeric judge on "P == 1/2", "P >= 1/4", "P > 1/2" under four grounds:
       no method named, the classical three (P in [1/4, 1/2], hull earned by computation): OPEN / EARNED / REFUTED;
       any method of the family (P in [0, 1]):                                            OPEN / OPEN / OPEN;
       the endpoints method stipulated (P = 1/3):                                        REFUTED / EARNED / REFUTED;
       Jaynes's invariance principle stipulated (rotation, scale, translation; P = 1/2): EARNED / EARNED / REFUTED;
     and the same hull taken on the story alone, not computed (credit): every forced verdict capped at ON CREDIT.
     The whole of Bertrand's dispute is which ground is laid; the judge's answer moves with it and names it;
  4. the cure the judge names for the open claim is "measure P". For Bertrand that reads: name a procedure. A
     convention narrows P by stipulation; a PHYSICAL procedure can be measured instead — Jaynes reported straws
     tossed onto a circle agreeing with 1/2 (E. T. Jaynes, "The well-posed problem", Found. Phys. 3, 1973). A
     stipulation and a measurement are two different grounds; the word "measure" covers only the second.

NOT CLAIMED: that 1/2 is "the" answer (it is the answer on Jaynes's stated premise); anything about which
premise is right. The judge prices the answers by their grounds; choosing the ground is not its job.

Run:  python3 dilemmas/bertrand.py
"""
import math
import os
import random
import sys
from fractions import Fraction

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402

N = 200_000
HALF = 0.5                     # the chord beats the side (sqrt 3, radius 1) iff its distance from the centre < 1/2


def exact():
    # endpoints: fix one end; the chord is long iff the other end lies on the opposite third of the circle
    endpoints = Fraction(2, 3) - Fraction(1, 3)
    # radius: the distance is uniform on [0, 1]; long iff it is below 1/2
    radius = Fraction(1, 2)
    # midpoint: uniform in the disk; long iff inside the disk of radius 1/2 — area ratio (1/2)^2
    midpoint = Fraction(1, 2) ** 2
    return {"endpoints": endpoints, "radius": radius, "midpoint": midpoint}


def simulate(method, rng, n=N, k=None):
    long_ = 0
    for _ in range(n):
        if method == "endpoints":
            a, b = rng.random() * 2 * math.pi, rng.random() * 2 * math.pi
            d = abs(math.cos((a - b) / 2))                   # distance of the chord from the centre
        elif method == "radius":
            d = rng.random()
        elif method == "midpoint":
            while True:                                      # a point uniform in the unit disk (rejection)
                x, y = 2 * rng.random() - 1, 2 * rng.random() - 1
                if x * x + y * y <= 1:
                    break
            d = math.hypot(x, y)
        else:                                                # the family: distance = u^k
            d = rng.random() ** k
        long_ += d < HALF
    return long_ / n


def sec1_three_answers():
    print("-" * 72)
    print("1. ONE QUESTION, THREE RIGHT ANSWERS")
    rng = random.Random(1889)
    ex = exact()
    assert ex == {"endpoints": Fraction(1, 3), "radius": Fraction(1, 2), "midpoint": Fraction(1, 4)}
    for m, v in ex.items():
        sim = simulate(m, rng)
        assert abs(sim - float(v)) < 0.01, (m, sim, v)
        print(f"   {m:9s}: exact {str(v):4s}  simulated {sim:.4f}")
    print("   Each argument is correct. The question names no measure, and each method supplies one.")


def sec2_any_value():
    print("-" * 72)
    print("2. A FAMILY OF 'NATURAL' METHODS REACHES ANY VALUE")
    rng = random.Random(1973)
    for target in (0.05, 0.25, 1 / 3, 0.5, 0.9):
        k = math.log(0.5) / math.log(target)                 # (1/2)^(1/k) = target
        sim = simulate("family", rng, k=k)
        assert abs(sim - target) < 0.01, (target, sim)
        print(f"   distance = u^{k:.3f}: P = {target:.4f} (simulated {sim:.4f})")
    print("   So 'a natural way to draw a chord' pins nothing down: the repertoire has to be named.")


GROUNDS = [
    ("no method named; the classical three, hull computed", "P=[1/4,1/2] earned:three-methods",
     ["OPEN", "EARNED", "REFUTED"]),
    ("any method of the family u^k", "P=[0,1] earned:family", ["OPEN", "OPEN", "OPEN"]),
    ("the endpoints method stipulated", "P=1/3 earned:endpoints", ["REFUTED", "EARNED", "REFUTED"]),
    ("Jaynes's invariance stipulated", "P=1/2 earned:invariance", ["EARNED", "EARNED", "REFUTED"]),
    ("the classical hull on the story alone", "P=[1/4,1/2] credit", ["OPEN", "ON CREDIT", "ON CREDIT"]),
]
CLAIMS = ["P == 1/2", "P >= 1/4", "P > 1/2"]


def sec3_the_ground_decides():
    print("-" * 72)
    print("3. THE JUDGE'S ANSWER MOVES WITH THE GROUND — AND NAMES IT")
    print(f"   {'ground':52s} " + "  ".join(f"{c:9s}" for c in CLAIMS))
    for label, sheet, want in GROUNDS:
        qs, marks = parse_quantities(sheet)
        got = [judge_sheet_claim(c, qs, marks)["disposition"] for c in CLAIMS]
        assert got == want, (label, got, want)
        print(f"   {label:52s} " + "  ".join(f"{g:9s}" for g in got))


def sec4_measure_or_stipulate():
    print("-" * 72)
    print("4. 'MEASURE P' — OR STIPULATE A METHOD")
    qs, marks = parse_quantities("P=[1/4,1/2] earned:three-methods")
    r = judge_sheet_claim("P == 1/2", qs, marks)
    assert r["disposition"] == "OPEN" and r["next_check"] == ["measure P"]
    print(f"   'P == 1/2' with no method: {r['disposition']}, cure named: {r['next_check']}")
    print("   A convention narrows P by stipulation; a physical procedure can be measured instead (Jaynes,")
    print("   1973: straws tossed onto a circle agreed with 1/2). Two different grounds; 'measure' names one.")


if __name__ == "__main__":
    for sec in (sec1_three_answers, sec2_any_value, sec3_the_ground_decides, sec4_measure_or_stipulate):
        sec()
    print("-" * 72)
    print("BERTRAND: all measurements hold.")
