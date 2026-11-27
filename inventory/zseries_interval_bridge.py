# -*- coding: utf-8 -*-
"""
zseries over an interval ↔ lean/ZPowTaylor.lean (2026-11-27).

`zseries._taylor2` reads f on [m − r, m + r] as f(m) ± |f'(m)|·r + D2·r²/2, D2 = Σ |c_k| e_k (e_k − 1) R^(e_k − 2).
PROVED (lean/ZPowTaylor.lean, zero axioms): for every partial sum P_N = Σ c_k x^{e_k} with |c_k| ≤ a_k and |x|, |m| ≤ R,
|P_N(x) − P_N(m) − P'_N(m)(x − m)| ≤ (Σ a_k Bd_{e_k}(R))·(x − m)²,  Bd_e = e(e−1)/2·R^(e−2) (`taylor_sum`); and the
positive tail after halving terms stays below the last term (`tail_halving`, the code's "+ t").
The MONOTONE branch (a derivative of one sign ⇒ the ends bound f) is lean/ZMonoTaylor.lean `mono_up`, `mono_up_right`:
from the Taylor bound and a floor m > 0 of the derivative alone, no mean value theorem. Still a named premise:
|J_n(x)| ≤ 1 (the clamp of J0, J1).
This stand checks, for J0, J1, ber, bei and the first derivatives on seeded intervals in [−6, 6]:
  1. the code's D2 ≥ 2·Σ_{k<N} |c_k| Bd_{e_k}(R) for N = 200 terms (exact) — D2 is the theorem's coefficient, tail added;
  2. the halving premise holds for 150 terms after the code's cut (ratio ≤ 1/2 and non-increasing);
  3. the Taylor reading the code returns equals the theorem's formula recomputed from the point brackets and D2;
  4. soundness on the instance: the partial sum P_200 at 25 points of the interval lies inside `interval(name, a)`.
MUTATION: D2 halved -> some sampled value falls outside the Taylor reading on some interval.

Run:  python3 inventory/zseries_interval_bridge.py   -> ZSERIES INTERVAL BRIDGE GREEN
"""
import os
import random
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import zseries as Z                    # noqa: E402


def terms(name, upto):
    base, n = Z.split(name)
    out = []
    for k, sg, coef, e in Z._terms(base, n):
        out.append((sg * coef, e))
        if len(out) >= upto:
            return out


def P(ts, x):
    return sum(c * x ** e for c, e in ts)


def Bd(e, R):
    return Fr(e * (e - 1), 2) * R ** (e - 2) if e >= 2 else Fr(0)


def main():
    rnd = random.Random(20261127)
    names = ["besselj0", "besselj1", "ber", "bei", "besselj0_d1", "ber_d1"]
    ok = fail = 0
    mut_caught = 0
    mono = 0
    for name in names:
        ts = terms(name, 200)
        for _ in range(8):
            a0 = Fr(rnd.randint(-600, 500), 100)
            a1 = a0 + Fr(rnd.randint(1, 100), 100)
            base, n = Z.split(name)
            m = Z._mid(a0, a1)
            r = max(m - a0, a1 - m)
            R = max(abs(a0), abs(a1))
            D2 = Z._abs_series_bound(base, n + 1, R)
            Q = sum(abs(c) * Bd(e, R) for c, e in ts)
            good = D2 >= 2 * Q
            # halving after the cut, for the positive series of the second derivative
            sec = terms(f"{base}_d{n + 2}", 400)
            sz = [abs(c) * R ** e for c, e in sec]
            cut = next(j for j in range(1, 399) if sz[j - 1] > 0 and sz[j] / sz[j - 1] <= Fr(1, 2)
                       and sz[j] < Fr(1, 1 << (Z.ZF.BITS + 16)) * (1 + sum(sz[:j + 1])))
            good &= all(sz[j + 1] * 2 <= sz[j] for j in range(cut, cut + 150))
            lo, hi = Z.point(name, m)
            dlo, dhi = Z.point(Z.derivative_name(name), m)
            slope = max(abs(dlo), abs(dhi))
            want = (Z.ZF._down(lo - slope * r - D2 * r * r / 2), Z.ZF._up(hi + slope * r + D2 * r * r / 2))
            good &= Z._taylor2(name, a0, a1) == want
            out = Z.interval(name, (a0, a1))
            xs = [a0 + (a1 - a0) * Fr(j, 24) for j in range(25)]
            vals = [P(ts, x) for x in xs]
            good &= all(out[0] <= v <= out[1] for v in vals)
            d = Z._taylor2(Z.derivative_name(name), a0, a1)
            if d[0] > 0 or d[1] < 0:
                mono += 1                     # the branch fired: mono_up's floor m = d's end, Q = D2/2 (both ≥ 0)
            ok += good; fail += not good
            mlo = Z.ZF._down(lo - slope * r - D2 / 2 * r * r / 2)
            mhi = Z.ZF._up(hi + slope * r + D2 / 2 * r * r / 2)
            mut_caught += any(not (mlo <= v <= mhi) for v in vals)
    print(f"intervals {ok + fail} over {len(names)} functions: D2 ≥ 2Σ|c|Bd, halving tail, Taylor formula, 25 sampled "
          f"values inside: {ok}, differ {fail}")
    print(f"monotone branch used on {mono} intervals (mono_up's premises: the derivative's reading of one sign)")
    print(f"mutation (D2 halved): caught on {mut_caught} intervals")
    if fail == 0 and mut_caught > 0 and mono > 0:
        print("ZSERIES INTERVAL BRIDGE GREEN — caught")
    else:
        print("ZSERIES INTERVAL BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
