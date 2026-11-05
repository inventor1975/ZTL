# -*- coding: utf-8 -*-
"""
The two envelopes and St. Petersburg, judged: an expectation that has no value is a description with no subject.

  TWO ENVELOPES  One envelope holds twice the other. You open one and see a. "The other holds 2a or a/2, each with
                 probability 1/2, so it is worth 5a/4: switch." The same argument, before opening, says switch back.
  ST. PETERSBURG Toss a fair coin until heads; if that takes k tosses you win 2^k. The expected win is
                 1 + 1 + 1 + ... = infinity. What is a fair price to play? (Bernoulli, 1738.)

THE FORMALISATION, IN WORDS FIRST:
  "each with probability 1/2, whatever a is" needs a prior that is uniform over all amounts — there is no such
  probability distribution: the description names nothing (E). With a PROPER prior, three cases, all computed
  exactly here: (a) a finite mean — always switching gains exactly 0, and the conditional gain is positive for some
  observed a and negative for others; (b) Broome's prior (J. Broome, "The Two-Envelope Paradox", Analysis 55, 1995, p. 7: the smaller amount 2^k with
  probability (1/3)(2/3)^k) —
  switching gains at EVERY observed a, yet the two envelopes are symmetric, because the mean is infinite and "the
  expected gain" is infinity minus infinity: no value, E. St. Petersburg is case (b) without the envelopes: "the
  fair price" is an expectation with no value — E; name the bank (the casino's limit) and the price is a number.

MEASURED HERE:
  1. no prior gives 1/2 at every observed amount: for the proper priors of 2 and 3, the probability that the other
     envelope is the larger differs from 1/2 at some observed a (exact fractions);
  2. finite mean (smaller amount 2^k with probability (2/3)(1/3)^k): the expected gain of always switching is 0
     (summed exactly to k = 60, the tail below 1e-25), while the conditional gain is +1 at a = 1 and negative at
     every a >= 2;
  3. Broome's prior: the conditional expected gain is exactly a/10 > 0 at every a = 2^n, n >= 1 (and +1 at a = 1),
     and the mean of the smaller amount diverges (partial sums of (1/3)(4/3)^k exceed 10^6) — "the expected gain
     of always switching" has no value: E;
  4. St. Petersburg: with a bank of 2^m the fair price is exactly m + 1 (checked for m = 0..40); without a bank,
     "the fair price" is E; the numeric judge, with the bank named a quantity on credit, prices the claim
     "the price <= 41" ON CREDIT and names the bank to document.
Run:  python3 dilemmas/expectations.py
"""
import os
import sys
from fractions import Fraction as Fr

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                    # noqa: E402
from znumjudge import judge_sheet_claim, parse_quantities      # noqa: E402

K = 60


def finite_prior(k):            # smaller amount 2^k with probability (2/3)(1/3)^k: mean finite
    return Fr(2, 3) * Fr(1, 3) ** k


def broome_prior(k):            # smaller amount 2^k with probability (1/3)(2/3)^k: mean infinite
    return Fr(1, 3) * Fr(2, 3) ** k


def p_other_larger(prior, n):
    """P(the other envelope is the larger | observed a = 2^n)"""
    if n == 0:
        return Fr(1)            # 1 can only be the smaller amount
    mine_small = prior(n)       # x = 2^n, I hold the smaller (each envelope opened with probability 1/2)
    mine_large = prior(n - 1)   # x = 2^(n-1), I hold the larger
    return mine_small / (mine_small + mine_large)


def cond_gain(prior, n):
    a = Fr(2) ** n
    p = p_other_larger(prior, n)
    return p * (2 * a) + (1 - p) * (a / 2) - a


def sec1_no_flat_prior():
    print("-" * 72)
    print("1. '1/2 WHATEVER a IS' — NO PRIOR DOES IT")
    for name, prior in (("finite mean", finite_prior), ("Broome", broome_prior)):
        ps = {n: p_other_larger(prior, n) for n in range(0, 6)}
        assert any(v != Fr(1, 2) for v in ps.values())
        print(f"   {name:12s}: P(other is larger | a = 2^n), n = 0..5: " + ", ".join(str(v) for v in ps.values()))
    # computed: a weight c on each of infinitely many amounts sums to 0 (c = 0) or passes 1 after ceil(1/c) terms
    # (c > 0) — never to 1; so no distribution answers to the description, and its mark is "no subject"
    def total_mass(c):
        """the total weight of c on each of infinitely many amounts: 0 if c = 0; otherwise the partial sum passes 1
        after n = floor(1/c) + 1 terms and keeps growing — no finite total"""
        if c == 0:
            return Fr(0)
        n = int(1 / c) + 1
        assert n * c > 1
        return None                                 # unbounded

    def can_sum_to_one(c):
        return total_mass(c) == 1
    candidates = [Fr(0), Fr(1, 10), Fr(1, 1000), Fr(1, 10 ** 9)]
    mark = "E" if not any(can_sum_to_one(c) for c in candidates) else "T"
    r = judge("uniform_over_all_amounts", {"uniform_over_all_amounts": mark})
    assert r["disposition"] == "E"
    print(f"   'a prior uniform over all amounts': {r['disposition']} — no probability distribution is that")


def sec2_finite_mean():
    print("-" * 72)
    print("2. A FINITE MEAN: ALWAYS SWITCHING GAINS NOTHING")
    total = Fr(0)
    for k in range(K):
        x = Fr(2) ** k
        total += finite_prior(k) * (Fr(1, 2) * (2 * x - x) + Fr(1, 2) * (x - 2 * x))    # hold small / hold large
    assert total == 0
    gains = [cond_gain(finite_prior, n) for n in range(0, 6)]
    assert gains[0] == 1 and all(g < 0 for g in gains[1:])
    print(f"   expected gain of always switching: {total}; conditional gain at a = 1, 2, 4, ...: "
          + ", ".join(str(g) for g in gains))


def sec3_broome():
    print("-" * 72)
    print("3. BROOME'S PRIOR: GAIN AT EVERY a, YET SYMMETRIC — THE MEAN IS INFINITE")
    gains = [cond_gain(broome_prior, n) for n in range(0, 12)]
    assert gains[0] == 1 and all(gains[n] == Fr(2) ** n / 10 for n in range(1, 12))
    partial, k = Fr(0), 0
    while partial <= 10 ** 6:
        partial += broome_prior(k) * Fr(2) ** k
        k += 1
    # computed: the terms of the mean grow by the ratio (2/3)*2 = 4/3 > 1 — the series diverges, the expectation
    # of either envelope has no finite value, and the gain of switching is infinity minus infinity
    ratio = (broome_prior(1) * 2) / broome_prior(0)
    mark = "E" if ratio >= 1 else "T"
    r = judge("expected_gain_of_switching_is_positive", {"expected_gain_of_switching_is_positive": mark})
    assert r["disposition"] == "E"
    print(f"   conditional gain at a = 2^n: exactly a/10 for n = 1..11 (and +1 at a = 1)")
    print(f"   the mean of the smaller amount passes 10^6 after {k} terms: it diverges")
    print(f"   'always switching gains in expectation': {r['disposition']} — infinity minus infinity has no value")


def sec4_st_petersburg():
    print("-" * 72)
    print("4. ST. PETERSBURG: NAME THE BANK")
    for m in range(0, 41):
        bank = Fr(2) ** m
        price = sum(Fr(1, 2 ** k) * min(Fr(2) ** k, bank) for k in range(1, 200))
        assert abs(price - (m + 1)) < Fr(1, 10 ** 40), (m, float(price))
    # computed: without a bank every toss count contributes exactly 1 to the mean — the sum has no finite value
    contrib = {k: Fr(1, 2 ** k) * Fr(2) ** k for k in range(1, 50)}
    mark = "E" if all(v == 1 for v in contrib.values()) else "T"
    r = judge("fair_price_without_a_bank", {"fair_price_without_a_bank": mark})
    assert r["disposition"] == "E"
    s = judge_sheet_claim("price <= 41", *parse_quantities("price=[1,41] credit"))
    assert s["disposition"] == "ON CREDIT" and "document price" in s["next_check"]
    print("   bank 2^m -> fair price exactly m + 1 (m = 0..40): a bank of about a trillion makes it 41")
    print(f"   without a bank: {r['disposition']}; with the bank only told, 'price <= 41': {s['disposition']} {s['next_check']}")


if __name__ == "__main__":
    for sec in (sec1_no_flat_prior, sec2_finite_mean, sec3_broome, sec4_st_petersburg):
        sec()
    print("-" * 72)
    print("EXPECTATIONS: all measurements hold.")
