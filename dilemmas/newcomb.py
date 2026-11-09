# -*- coding: utf-8 -*-
"""
Newcomb's problem (Nozick 1969).

A predictor, right with probability p, put $1,000,000 in the opaque box B if and only if it predicted you would
take B alone; the open box A holds $1,000. One-box or two-box? Dominance: whatever is in B, both boxes give $1,000
more. Expectation with the act as evidence: one-boxing gives p·1,000,000, two-boxing (1−p)·1,000,000 + 1,000.

Picked by a scout (2026-11-09), not in the corpus before.

MEASURED HERE:
  1. both arithmetics are exact (fractions) and both are RIGHT: with the act as evidence of the prediction,
     one-boxing is better exactly when p > 1001/2000 = 0.5005; with the contents fixed before the act (probability
     q, independent of the act), two-boxing is better by exactly 1,000 for every q;
  2. the claim "one-boxing is better" is therefore EARNED under the evidential dependence, REFUTED under the causal
     one, and with the dependence not declared — a dirty atom `ev` — OPEN, the judge naming `ev` as the check;
  3. so the paradox is the genre of 1 + 2 + 3 + … = −1/12 and Bertrand's chord: a hidden convention. Not a
     contradiction: two correct computations of two different questions. The decision needs the dependence
     DECLARED (is the prediction caused by, or merely correlated with, the act?), and the judge will not answer
     without it.

WHAT THIS IS NOT: a resolution. Which dependence is right is the whole literature (evidential vs causal decision
theory); the machine does not pick one. It refuses to answer without one, and names the missing declaration.

The two arithmetic claims are also Lean theorems over their parameter boxes (tools/zbound2lean.py, the run of
2026-11-09): evidential, p in [1001/2000, 1]: EV(one) − EV(two) >= 0; causal, q in [0, 1]: EV(two) − EV(one) >= 1000.

Run:  python3 dilemmas/newcomb.py
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztl import T, F, Z                                         # noqa: E402
from ztljudge import judge                                      # noqa: E402

M, K = 1_000_000, 1_000


def ev_one(p):
    return p * M


def ev_two(p):
    return (1 - p) * M + K


def causal_two_minus_one(q):
    return (q * (M + K) + (1 - q) * K) - q * M


def sec1_both_arithmetics():
    print("-" * 72)
    print("1. BOTH ARITHMETICS, EXACT")
    star = Fr(M + K, 2 * M)
    print(f"   evidential: EV(one) − EV(two) = 2M·p − (M + K), zero at p* = {star} = {float(star)}")
    assert ev_one(star) == ev_two(star) and ev_one(Fr(99, 100)) - ev_two(Fr(99, 100)) == 979_000
    for q in (Fr(0), Fr(1, 3), Fr(1)):
        assert causal_two_minus_one(q) == K
    print(f"   causal: EV(two) − EV(one) = {K} for every q (checked at q = 0, 1/3, 1; exact algebra: identically K)")
    print("   Both are right. They answer two different questions.")


def sec2_the_claim_needs_the_dependence():
    print("-" * 72)
    print("2. 'ONE-BOXING IS BETTER' — WITH AND WITHOUT THE DEPENDENCE DECLARED")
    claim = "(ev & numev) | (~ev & numca)"     # ev: the act is evidence of the prediction (evidential dependence)
    base = {"numev": T, "numca": F}            # numev: the evidential arithmetic says one-box (p = 0.99 > p*);
    out = {}                                   # numca: the causal arithmetic says one-box — it does not
    for ev in (T, F, Z):
        r = judge(claim, dict(base, ev=ev))
        out[ev] = (r["disposition"], sorted(r.get("unverified", [])))
        print(f"   ev = {ev}: {out[ev][0]}" + (f", the check named: {out[ev][1]}" if out[ev][1] else ""))
    assert out[T][0] == "EARNED" and out[F][0] == "REFUTED" and out[Z] == ("OPEN", ["ev"])
    print("   Declared, the claim is decided either way; undeclared, OPEN — and the judge names `ev`:")
    print("   the missing declaration is the dependence, not a number.")


if __name__ == "__main__":
    sec1_both_arithmetics()
    sec2_the_claim_needs_the_dependence()
    print("-" * 72)
    print("NEWCOMB: two exact arithmetics, both right; the claim is OPEN until the dependence is declared.")
    print("NEWCOMB GREEN")
