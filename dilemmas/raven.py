# -*- coding: utf-8 -*-
"""
Hempel's raven paradox (Hempel 1945).

"All ravens are black" is equivalent to "all non-black things are non-ravens". An instance confirms its law
(Nicod); what confirms a law confirms its equivalents (the equivalence condition). So a white shoe confirms that all
ravens are black.

Picked by a scout (2026-11-09), not in the corpus before.

MEASURED HERE (atoms per observed object: r — it is a raven, b — it is black):
  1. on VERIFIED observations the instance and its contrapositive have the same verdict in every marking — the
     equivalence condition holds there, and the white shoe (r = F, b = F) earns the instance exactly as a black
     raven does. ZTL has no logical objection to Hempel's step;
  2. they part only where the colour is NOT verified: a raven of unchecked colour leaves "raven -> black" OPEN but
     makes "non-black -> non-raven" ON CREDIT (T now, a verification can kill it) — contraposition is the rule ZTL
     gives up on dirty atoms (ztl.py, fixed fork 1), and it gives it up exactly here;
  3. so the paradox is not logical but QUANTITATIVE, and the quantity depends on how the object was found (the
     protocol — a hidden convention again). In a finite universe, H: no non-black raven, against H': one raven
     non-black, the Bayes factor of one observation is exact: a random RAVEN found black — nR/(nR − 1); a random
     NON-BLACK thing found a non-raven — nB/(nB − 1), barely above 1; a random NON-RAVEN found non-black — exactly 1.

WHAT THIS IS NOT: news. The Bayesian reading (Hosiasson-Lindenbaum; Good; Fitelson & Hawthorne 2010) and the
protocol dependence are the literature's. The machine adds only where its logic draws the line: equivalence is
safe on verified data and fails, by design, on unverified colour.

The factors over their boxes are Lean theorems (tools/zbound2lean.py, 2026-11-09): nR in [5, 10]: the raven's
factor >= 10/9; nB in [50, 90]: the shoe's factor in [1.011, 1.021].

Run:  python3 dilemmas/raven.py
"""
import os
import sys
from fractions import Fraction as Fr
from itertools import product

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from ztl import T, F, Z                                         # noqa: E402
from ztljudge import judge                                      # noqa: E402

VALUES = (T, F, Z)
LAW = "(r -> b)"               # this object: if a raven, then black
CONTRA = "(~b -> ~r)"          # this object: if not black, then not a raven


def sec1_and_2_equivalence():
    print("-" * 72)
    print("1-2. THE INSTANCE AND ITS CONTRAPOSITIVE, MARKING BY MARKING")
    same, differ = [], []
    for c in product(VALUES, repeat=2):
        m = {"r": c[0], "b": c[1]}
        a, b = judge(LAW, m)["disposition"], judge(CONTRA, m)["disposition"]
        print(f"   r={c[0]} b={c[1]}:  raven->black {a:10s}  non-black->non-raven {b}")
        (same if a == b else differ).append((c, a, b))
    clean = [x for x in same + differ if Z not in x[0]]
    assert all(a == b for _, a, b in clean)
    assert sorted(x[0] for x in differ) == [(T, Z), (Z, Z)]
    assert all(a == "OPEN" and b == "ON CREDIT" for _, a, b in differ)
    shoe = judge(LAW, {"r": F, "b": F})["disposition"]
    raven = judge(LAW, {"r": T, "b": T})["disposition"]
    assert shoe == raven == "EARNED"
    print("   Verified data: the same verdict in all four clean markings — equivalence holds, the white")
    print("   shoe earns the instance exactly as a black raven does. Only an unverified colour splits them:")
    print("   the law OPEN, its contrapositive ON CREDIT.")


def factors(nR, nB):
    return {"raven found black": Fr(nR, nR - 1), "non-black found non-raven": Fr(nB, nB - 1),
            "non-raven found non-black": Fr(1)}


def sec3_the_quantity_and_its_protocol():
    print("-" * 72)
    print("3. THE BAYES FACTOR OF ONE OBSERVATION, H (no non-black raven) against H' (one), exact")
    for nR, nB in ((5, 50), (10, 90)):
        f = factors(nR, nB)
        print(f"   nR = {nR}, nB = {nB}: " + "; ".join(f"{k} {v} = {float(v):.4f}" for k, v in f.items()))
    lo, hi = factors(10, 90), factors(5, 50)
    assert lo["raven found black"] >= Fr(10, 9) and Fr(1011, 1000) <= lo["non-black found non-raven"]
    assert hi["non-black found non-raven"] <= Fr(1021, 1000)
    print("   The shoe confirms — by 1 % to 2 %; a black raven by 11 % to 25 %; a non-raven drawn as such, not")
    print("   at all. Which number answers 'does it confirm?' depends on how the object was drawn.")


if __name__ == "__main__":
    sec1_and_2_equivalence()
    sec3_the_quantity_and_its_protocol()
    print("-" * 72)
    print("RAVEN: equivalence holds on verified data; it splits only on unverified colour; the confirmation")
    print("is a number, and the number depends on the protocol.")
    print("RAVEN GREEN")
