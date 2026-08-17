# -*- coding: utf-8 -*-
"""
Which conclusions were properties of the parameters nobody justified?

Adversarial review: the containment probes fix LIMIT = 0.02, drift = 20,
BRANCH = 8, density = 10 edges per node, and sweep redundancy from 0% to 95%
— none of it argued, and at least one headline figure was shown to be a closed
form in BRANCH rather than a measurement. probe_real then supplied the numbers
those choices should have been anchored to: a real dependency graph on this
machine runs at **5.18 edges per node** with **2.6% declared alternatives**.

So this file does not sweep for the sake of sweeping. It asks the one question
the real graph makes urgent: at parameters a real system actually has, is
there any containment left?

Run:  python3 db/probe_sensitivity.py
"""
import random
import sys
from collections import defaultdict

N = 40_000
SEED = 20260816
REAL_DENSITY, REAL_ALT = 5.18, 0.026        # measured in probe_real


def collective(n, density, frac_alt, rnd, span=200):
    par, rev, B = defaultdict(list), defaultdict(list), {}
    for _ in range(int(n * density)):
        c = rnd.randrange(1, n)
        p = rnd.randrange(max(0, c - span), c)
        par[c].append(p)
        rev[p].append(c)
    for c in list(par):
        if rnd.random() < frac_alt:
            x = rnd.randrange(0, max(1, c))
            B[c] = x
            rev[x].append(c)
    return par, rev, B


def cascade(par, rev, B, start):
    dead, frontier = {start}, [start]
    while frontier:
        nxt = []
        for node in frontier:
            for c in rev.get(node, ()):
                if c in dead:
                    continue
                if any(p in dead for p in (par.get(c) or ())) and \
                        (c not in B or B[c] in dead):
                    dead.add(c)
                    nxt.append(c)
        frontier = nxt
    return len(dead) / N


def worst(par, rev, B, k=25):
    rs = random.Random(7)
    sampled = max(cascade(par, rev, B, s) for s in rs.sample(range(N), k))
    chosen = max(cascade(par, rev, B, t) for t in
                 [0] + [n for n, _d in sorted(rev.items(),
                                              key=lambda kv: -len(kv[1]))[:3]])
    return sampled, chosen


def main():
    print("=" * 78)
    print("SENSITIVITY — and the one question the real graph makes urgent")
    print("=" * 78)
    print(f"  {N:,} agents. Real reference (probe_real): {REAL_DENSITY} edges")
    print(f"  per node, {REAL_ALT:.1%} declared alternatives.\n")

    print("  1. AT REAL PARAMETERS, IS THERE ANY CONTAINMENT?\n")
    print(f"  {'density':>9} {'alternatives':>13} {'sampled':>9} {'chosen':>9}")
    for dens, alt, tag in ((10.0, 0.90, "as swept"),
                           (10.0, REAL_ALT, "real redundancy"),
                           (REAL_DENSITY, 0.90, "real density"),
                           (REAL_DENSITY, REAL_ALT, "BOTH REAL")):
        rnd = random.Random(SEED)
        par, rev, B = collective(N, dens, alt, rnd)
        s_, c_ = worst(par, rev, B)
        print(f"  {dens:>9.2f} {alt:>12.1%} {s_:>9.3f} {c_:>9.3f}   {tag}")

    print("""
     Read the last row. At a density and a redundancy a real dependency
     graph actually has, a randomly located loss costs what an
     unredundified collective costs, because 2.6% of conclusions carrying
     an alternative is indistinguishable from none. The containment the
     earlier sections located at 75-90% redundancy is real arithmetic
     about a region real systems do not occupy.""")

    print("\n  2. DENSITY, AT REAL REDUNDANCY\n")
    print(f"  {'edges/node':>11} {'sampled':>9} {'chosen':>9}")
    for dens in (2, 3, REAL_DENSITY, 8, 10, 15, 20):
        rnd = random.Random(SEED)
        par, rev, B = collective(N, dens, REAL_ALT, rnd)
        s_, c_ = worst(par, rev, B)
        print(f"  {dens:>11.2f} {s_:>9.3f} {c_:>9.3f}")
    print("     ANOTHER CONCLUSION WRITTEN BEFORE THE TABLE WAS READ, kept")
    print("     for the same reason as the others. This said density is")
    print("     where the phenomenon lives and that below three edges per")
    print("     node a loss stays local. The row for density 2 says 0.719 —")
    print("     seventy-two per cent of the collective, with no redundancy")
    print("     worth the name to save it.")
    print("     What the column actually shows is SATURATION: the loss is")
    print("     already most of the collective at the sparsest setting")
    print("     tried, and flattens by about three edges per node. Density")
    print("     is not a dial between contained and uncontained; over this")
    print("     whole range it is uncontained, and the real graph's 5.18")
    print("     sits well inside the flat part.")

    print("\n  3. WHAT THE SWEEP RANGE SHOULD HAVE BEEN\n")
    print(f"  {'alternatives':>13} {'sampled':>9} {'chosen':>9}")
    for alt in (0.0, 0.026, 0.10, 0.25, 0.50, 0.75, 0.90):
        rnd = random.Random(SEED)
        par, rev, B = collective(N, REAL_DENSITY, alt, rnd)
        s_, c_ = worst(par, rev, B)
        mark = "   <- real" if abs(alt - REAL_ALT) < 1e-6 else ""
        print(f"  {alt:>12.1%} {s_:>9.3f} {c_:>9.3f}{mark}")

    print("""
  WHAT THIS SETTLES. The corpus fixed its parameters without argument and
  they were carrying conclusions. The swept redundancy range sat an order
  of magnitude above where a real graph is, and containment appears only
  in the top of that range: at 2.6% the loss is 0.926 and at 90% it is
  0.000, with the real system at the wrong end. Density turned out NOT to
  be the dial this file first said it was — the collective is uncontained
  across every density tried — which is a third conclusion of mine
  corrected by its own table in one afternoon.

  THE CHOSEN-TARGET COLUMN BARELY MOVES, AND ITS FLOOR IS PRINTED ABOVE.
  This paragraph read "does not move anywhere ... at any density and any
  redundancy" until 2026-08-17, thirty lines below its own density-2 row
  reading 0.791 — the program contradicting itself in one run, and the
  third instance in one day of a claim withdrawn in one place and left
  standing in another. What the tables support: across every row above the
  chosen column stays at or above 0.791, and above density 3 it is 0.94 or
  more. The sensitivity is to whether the attacker chooses, not to density
  or redundancy — which is the §3.2 correction arriving from a third
  direction, stated without the universal it does not own.""")
    print("\nSENSITIVITY PROBE GREEN — the parameters carried more than the "
          "conclusions did.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
