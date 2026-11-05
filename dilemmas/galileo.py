# -*- coding: utf-8 -*-
"""
Galileo's squares and Hilbert's hotel, judged: "fewer" names three different relations.

  GALILEO  (Two New Sciences, 1638): every square is a natural number and most naturals are not squares — so there
           are fewer squares; but n <-> n^2 pairs them off one to one — so there are as many. Galileo concluded
           that "equal", "greater" and "less" do not apply to infinite collections.
  HILBERT  a full hotel with a room for every natural number takes one more guest (move n to n + 1), and infinitely
           many more (move n to 2n).

THE FORMALISATION, IN WORDS FIRST:
  three relations all called "fewer" for finite sets, and they agree there:
    INCLUSION    A is a proper part of B;
    DENSITY      A's share of {1..N} tends to a smaller limit than B's;
    CARDINALITY  no one-to-one map of B into A exists (Cantor's "fewer").
  For infinite sets they come apart. "Fewer", with the relation unnamed, is a CONVENTION; each relation, named,
  gives an earned verdict. Galileo's refusal to compare was the judge's refusal with the cure unnamed; Cantor's
  choice of cardinality was a stipulation, and a fruitful one.

MEASURED HERE:
  1. for all pairs of subsets of {1..6}, the three relations agree on "A has fewer elements than B" except where
     inclusion is silent (incomparable sets): whenever A is a proper part of B, A has fewer elements — checked
     exhaustively (4096 pairs);
  2. squares against naturals: proper part (EARNED: 2 is not a square); density of squares in {1..N} for
     N = 10^2..10^8 is exactly 1/sqrt(N) -> 0 (fewer); the map n -> n^2 is one-to-one and onto the squares on
     every initial segment (checked to 10^6) — the same number, as cardinality counts;
  3. Hilbert: n -> n + 1 and n -> 2n are one-to-one into the rooms (checked to 10^6) and leave rooms free (room 1;
     every odd room) — a full hotel has room, as cardinality counts, and is full, as occupancy counts;
  4. the numeric judge on "the squares are fewer": the relation unnamed (a convention between 0 and 1 meaning
     same/fewer): OPEN, cure "stipulate"; inclusion or density stipulated: EARNED; cardinality stipulated: REFUTED.
Run:  python3 dilemmas/galileo.py
"""
import math
import os
import sys
from itertools import combinations

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402


def subsets(n):
    xs = list(range(1, n + 1))
    return [frozenset(c) for r in range(n + 1) for c in combinations(xs, r)]


def sec1_finite_agree():
    print("-" * 72)
    print("1. FOR FINITE SETS THE THREE 'FEWER'S AGREE")
    S = subsets(6)
    checked = 0
    for A in S:
        for B in S:
            checked += 1
            if A < B:                                   # inclusion says fewer
                assert len(A) < len(B)                  # cardinality agrees
    assert checked == 4096
    print(f"   {checked} pairs of subsets of {{1..6}}: every proper part has fewer elements")


def sec2_squares():
    print("-" * 72)
    print("2. THE SQUARES: A PROPER PART, DENSITY 0 — AND AS MANY")
    assert math.isqrt(2) ** 2 != 2                     # 2 is a natural that is not a square
    for e in range(2, 9, 2):
        N = 10 ** e
        dens = math.isqrt(N) / N
        assert dens == 1 / math.isqrt(N)
        print(f"   share of squares in {{1..10^{e}}}: {dens:.0e}")
    N = 10 ** 6
    images = [n * n for n in range(1, N + 1)]
    assert len(set(images)) == N                       # one-to-one
    # onto: the squares up to N^2 are exactly isqrt(N^2) = N in number, and all N images lie among them
    assert math.isqrt(N * N) == N and max(images) == N * N and all(math.isqrt(v) ** 2 == v for v in images)
    print("   n -> n^2 is one-to-one on 1..10^6, onto the squares up to 10^12: the same count, pair by pair")


def sec3_hilbert():
    print("-" * 72)
    print("3. HILBERT'S HOTEL")
    N = 10 ** 6
    shift = [n + 1 for n in range(1, N + 1)]
    double = [2 * n for n in range(1, N + 1)]
    assert len(set(shift)) == N and 1 not in shift
    assert len(set(double)) == N and all(r % 2 == 0 for r in double)
    print("   n -> n + 1: every guest keeps a room, room 1 is free; n -> 2n: every odd room is free")
    print("   full by occupancy, with room by cardinality — two relations, not one hotel in two states")


def sec4_the_judge():
    print("-" * 72)
    print("4. THE JUDGE ON 'THE SQUARES ARE FEWER' (F = 1 fewer, F = 0 as many)")
    rows = [("the relation unnamed", "F=[0,1] int earned:three-relations convention", "OPEN", ["stipulate F"]),
            ("inclusion stipulated", "F=1 earned:inclusion convention", "EARNED", []),
            ("density stipulated", "F=1 earned:density convention", "EARNED", []),
            ("cardinality stipulated", "F=0 earned:cardinality convention", "REFUTED", [])]
    for label, sheet, want, cure in rows:
        r = judge_sheet_claim("F == 1", *parse_quantities(sheet))
        assert r["disposition"] == want and r["next_check"] == cure, (label, r)
        print(f"   {label:24s}: {r['disposition']:8s} {cure}")


if __name__ == "__main__":
    for sec in (sec1_finite_agree, sec2_squares, sec3_hilbert, sec4_the_judge):
        sec()
    print("-" * 72)
    print("GALILEO AND HILBERT: all measurements hold.")
