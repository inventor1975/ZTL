# -*- coding: utf-8 -*-
"""
zseries.point ↔ lean/ZAltSeries.lean — the Bessel/Kelvin bracket is the theorem's bracket (2026-11-27).

`lean/ZAltSeries.lean` proves (no axioms): if from index k on the terms alternate and do not grow (`AltStep`), every
later partial sum — hence the limit — lies between S_k and S_{k+1} (`alt_bracket`, `limit_in_bracket`); and the
terms do not grow from k on when the size ratio ρ_j is ≤ 1 at k and non-increasing after (`ratio_decreasing`).
This stand checks, for J0, J1, ber, bei and their first two derivatives at seeded rational points:
  1. the bracket `zseries.point` returns contains [min(S_k, S_{k+1}), max(...)] for the k where it stopped, rounded
     outward (the code's own rule, recomputed here);
  2. the theorem's premises at that k, exactly in fractions: ρ_k ≤ 1 and ρ non-increasing for the next 300 terms,
     signs alternating (each family's ρ_j is x^s divided by a product increasing in j — the 300 terms are a check
     of the code, not the proof);
  3. the theorem's conclusion on the instance: the partial sums S_{k+1+j}, j < 300, all lie in the bracket;
  4. both sides: points where the series needs many terms (|x| up to 12) and few (|x| < 1).
MUTATION: the bracket collapsed onto S_{k+1} -> a later partial sum falls outside. (One term EARLIER is not a
mutation: the brackets nest, it is wider and still true.)

Run:  python3 inventory/zseries_bridge.py   -> ZSERIES BRIDGE GREEN
"""
import os
import random
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import zseries as Z                    # noqa: E402


def stop_index(name, x):
    """replay point()'s loop: the k at which it stopped, and the terms"""
    base, n = Z.split(name)
    terms, prev_abs, prev_ratio, partial = [], None, None, Fraction(0)
    for k, sg, coef, e in Z._terms(base, n):
        t = sg * coef * x ** e
        terms.append(t)
        partial += t
        a = abs(t)
        if prev_abs is not None and prev_abs > 0:
            ratio = a / prev_abs
            if ratio < 1 and (prev_ratio is None or ratio <= prev_ratio) and \
                    a < Fraction(1, 1 << (Z.ZF.BITS + 16)) * (1 + abs(partial)):
                return len(terms) - 1, terms
            prev_ratio = ratio
        prev_abs = a


def more_terms(name, x, upto):
    base, n = Z.split(name)
    out = []
    for k, sg, coef, e in Z._terms(base, n):
        out.append(sg * coef * x ** e)
        if len(out) >= upto:
            return out


def main():
    rnd = random.Random(20261127)
    names = [f"{b}{d}" for b in ("besselj0", "besselj1", "ber", "bei") for d in ("", "_d1", "_d2")]
    ok = fail = many = few = 0
    mut_caught = 0
    for name in names:
        for _ in range(12):
            x = Fraction(rnd.randint(-1200, 1200), 100)
            if x == 0:
                continue
            lo, hi = Z.point(name, x)
            k, terms = stop_index(name, x)
            T = more_terms(name, x, k + 302)
            S = [Fraction(0)]
            for t in T:
                S.append(S[-1] + t)
            a, b = S[k], S[k + 1]
            br = (min(a, b), max(a, b))
            good = lo <= br[0] and br[1] <= hi
            sizes = [abs(t) for t in T]
            rho = [sizes[j + 1] / sizes[j] for j in range(k, k + 300) if sizes[j] > 0]
            good &= rho[0] <= 1 and all(rho[i + 1] <= rho[i] for i in range(len(rho) - 1))
            good &= all((T[j] >= 0) != (T[j + 1] >= 0) or T[j + 1] == 0 for j in range(k, k + 300))
            good &= all(br[0] <= S[k + 1 + j] <= br[1] for j in range(300))
            ok += good; fail += not good
            many += k > 20; few += k <= 6
            # mutation: the bracket collapsed onto S_{k+1} (a claim of more than the theorem gives)
            m_lo = m_hi = S[k + 1]
            mut_caught += any(not (m_lo <= S[k + 1 + j] <= m_hi) for j in range(300))
    print(f"points {ok + fail} over {len(names)} functions: bracket ⊇ [S_k, S_k+1], premises at k, 300 later partial "
          f"sums inside: {ok}, differ {fail}; many-term cases {many}, few-term {few}")
    print(f"mutation (bracket collapsed onto S_k+1): caught in {mut_caught}/{ok + fail}")
    if fail == 0 and many > 0 and few > 0 and mut_caught > 0:
        print("ZSERIES BRIDGE GREEN")
    else:
        print("ZSERIES BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
