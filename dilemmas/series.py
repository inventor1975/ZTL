# -*- coding: utf-8 -*-
"""
Grandi's series and Riemann's rearrangement, judged: "the sum" of an infinite series names a method.

The family of 1 + 2 + 3 + ... = -1/12 (ztljudge.com/articles/mathematics/minus-one-twelfth/: "one S, or two?").

  GRANDI   1 - 1 + 1 - 1 + ...: the partial sums are 1, 0, 1, 0, ... and have no limit. Grandi (1703) said 1/2;
           Cesàro's mean of the partial sums and Abel's sum (the power series at x -> 1) both give 1/2.
  RIEMANN  1 - 1/2 + 1/3 - 1/4 + ... converges, to ln 2 — in that order. Take p positive terms for every q
           negative ones and the sum becomes ln 2 + (1/2) ln(p / q): Riemann's theorem says a conditionally
           convergent series can be rearranged to any value. An absolutely convergent one cannot.

THE FORMALISATION, IN WORDS FIRST:
  "the sum" as the LIMIT of the partial sums in the given order is a definition; where that limit does not exist
  (Grandi), the description has no subject — E. "the sum" as Cesàro's, Abel's, or any other method's is a
  CONVENTION — stipulated, then earned. "the sum of the TERMS", with no order named, is a convention too wherever
  the series is only conditionally convergent: the order is part of the question.

MEASURED HERE:
  1. Grandi: partial sums alternate 1, 0 (no limit: the limit-sum is E); the Cesàro mean of the first 2*10^5
     partial sums is 1/2 exactly; Abel's sum at x = 1 - 1e-9 is 1/2 within 1e-9;
  2. why 1/2 is forced once two properties are required: any method that is LINEAR and STABLE (dropping the first
     term subtracts it) assigns S = 1 - S, so S = 1/2 — checked as a linear equation, exactly;
  3. Riemann: the alternating harmonic series in four orders (p : q = 1:1, 2:1, 1:2, 4:1), summed to 3*10^5
     terms, matches ln 2 + (1/2) ln(p/q) within 1e-4; the absolutely convergent sum (-1)^(n+1)/n^2 gives the same
     value pi^2/12 in all four orders;
  4. the numeric judge: Grandi's S with the method unnamed (S a convention, any value in [0, 1]): "S == 1/2" OPEN,
     cure "stipulate S"; Cesàro stipulated: EARNED. The rearranged sum with the order unnamed: "S == ln 2" OPEN,
     cure "stipulate S"; the given order stipulated: EARNED.
Run:  python3 dilemmas/series.py
"""
import math
import os
import sys
from fractions import Fraction

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402


def sec1_grandi():
    print("-" * 72)
    print("1. GRANDI: 1 - 1 + 1 - ...")
    partial, s = [], 0
    for n in range(200_000):
        s += (-1) ** n
        partial.append(s)
    assert set(partial[:10]) == {0, 1} and partial[-2:] == [1, 0]
    limit_mark = "E" if len(set(partial[-1000:])) > 1 else "T"        # computed: the tail does not settle
    r = judge("limit_sum_is_half", {"limit_sum_is_half": limit_mark})
    assert r["disposition"] == "E"
    cesaro = Fraction(sum(partial), len(partial))
    assert cesaro == Fraction(1, 2)
    x = 1 - 1e-9
    abel = 1 / (1 + x)                                                 # sum (-1)^n x^n, closed form
    assert abs(abel - 0.5) < 1e-9
    print(f"   partial sums alternate 1, 0: 'the limit is 1/2' -> {r['disposition']} (no limit to speak of)")
    print(f"   Cesàro mean of 2*10^5 partial sums: {cesaro}; Abel at x = 1 - 1e-9: {abel:.10f}")


def sec2_linear_and_stable():
    print("-" * 72)
    print("2. WHY 1/2: LINEARITY AND STABILITY FORCE IT")
    # stability: S(a0, a1, ...) = a0 + S(a1, a2, ...); linearity: S(-a) = -S(a); and (a1, a2, ...) = -(a0, a1, ...)
    # so S = 1 + S(-1, 1, -1, ...) = 1 - S  ->  2S = 1
    S = Fraction(1, 2)
    assert S == 1 - S
    print("   S = 1 - S under any linear, stable method: S = 1/2 — the properties are stipulated, the value follows")


def rearranged(p, q, terms):
    s, pos, neg, n = 0.0, 1, 2, 0
    while n < terms:
        for _ in range(p):
            s += 1 / pos; pos += 2; n += 1
        for _ in range(q):
            s -= 1 / neg; neg += 2; n += 1
    return s


def rearranged_abs(p, q, terms):
    s, pos, neg, n = 0.0, 1, 2, 0
    while n < terms:
        for _ in range(p):
            s += 1 / pos ** 2; pos += 2; n += 1
        for _ in range(q):
            s -= 1 / neg ** 2; neg += 2; n += 1
    return s


def sec3_riemann():
    print("-" * 72)
    print("3. RIEMANN: THE SAME TERMS, ANOTHER ORDER, ANOTHER SUM")
    for p, q in ((1, 1), (2, 1), (1, 2), (4, 1)):
        got, want = rearranged(p, q, 300_000), math.log(2) + 0.5 * math.log(p / q)
        assert abs(got - want) < 1e-4, (p, q, got, want)
        absval = rearranged_abs(p, q, 300_000)
        assert abs(absval - math.pi ** 2 / 12) < 1e-4, (p, q, absval)
        print(f"   {p} positive : {q} negative -> {got:.5f} (ln 2 + ln({p}/{q})/2 = {want:.5f});"
              f"  absolutely convergent: {absval:.5f}")
    print("   conditionally convergent: the order is part of the question; absolutely convergent: it is not")


def sec4_the_judge():
    print("-" * 72)
    print("4. THE JUDGE: THE METHOD, OR THE ORDER, IS A CONVENTION")
    rows = [("Grandi, the method unnamed", "S == 1/2", "S=[0,1] earned:any-method convention", "OPEN", ["stipulate S"]),
            ("Grandi, Cesàro stipulated", "S == 1/2", "S=1/2 earned:cesaro convention", "EARNED", []),
            ("alternating harmonic, the order unnamed", "S >= 69/100",
             "S=[0,2] earned:any-order convention", "OPEN", ["stipulate S"]),
            ("alternating harmonic, the given order", "S >= 69/100",
             "S=[6931/10000,6932/10000] earned:given-order convention", "EARNED", [])]
    for label, claim, sheet, want, cure in rows:
        r = judge_sheet_claim(claim, *parse_quantities(sheet))
        assert r["disposition"] == want and r["next_check"] == cure, (label, r)
        print(f"   {label:42s} '{claim}': {r['disposition']:7s} {cure}")


if __name__ == "__main__":
    for sec in (sec1_grandi, sec2_linear_and_stable, sec3_riemann, sec4_the_judge):
        sec()
    print("-" * 72)
    print("SERIES: all measurements hold.")
