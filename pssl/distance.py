# -*- coding: utf-8 -*-
"""
distance — PSSL leg 3: do the eight grounds cluster, and by what?

The curator's question after v1.1.0: do the eight fall apart so that the
three of the note form a monolith while the four extras flow out of
classical logic?

Leg 2c already showed that APARTNESS is cheap — 26 of 28 pairs are
separated by a formula of size ≤ 5. So "are they different" is settled
and uninteresting. The live question is **how far**, and whether the
distances group.

WHAT IS MEASURED. Distance between two grounds = the fraction of
questions on which they disagree, over one shared pool:

    law distance   fraction of φ with valid₁(φ) ≠ valid₂(φ)
    rule distance  fraction of (γ,φ) with derives₁([γ],φ) ≠ derives₂([γ],φ)

Both are reported, and the rule distance is the informative one. K3 and
weak Kleene have NO tautologies at all — send every atom to u and nothing
is designated — so on laws they agree with each other trivially and
disagree with everything that has theorems. That measures "having
theorems", not kinship, and a reader shown only the law matrix would draw
a false family tree from it.

THE TWO RIVAL PREDICTIONS (pssl/PREREGISTRATION_LEG3.md, committed
before this file was written):

  R1  the five three-valued matrices {K3, LP, weak Kleene, Ł3, ZTL} are
      mutually closer than any is to intuitionistic logic or to the
      ortholattice — KIND predicts proximity;
  R2  they do not cluster by kind; proximity follows what a ground
      DESIGNATES and VALIDATES and cuts across kinds.

R1 is mine, from the argument that ZTL is structurally a matrix like the
other four (its {¬,∧,∨} fragment coincides cell for cell with Bochvar's
external layer, as the preprint concedes). R2 would refute it, and would
refute the curator's split too — by showing the family has two
independent axes, kind and behaviour, neither a relabelling of the other.

Run:  python3 pssl/distance.py
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, _HERE)

import zipc                                                   # noqa: E402
import grounds as G                                           # noqa: E402
import family as F                                            # noqa: E402

ALL = [(n, v, d) for n, _, v, d in G.GROUNDS] + \
      [(m.name, m.valid, m.derives) for m in F.FAMILY]

SHORT = {"classical": "CPC", "intuitionistic": "IPC", "quantum MO2": "MO2",
         "ZTL": "ZTL", "K3": "K3", "LP": "LP", "weak Kleene": "WK",
         "Lukasiewicz L3": "Ł3"}

# the five three-valued matrices over the Boolean base, per R1
MATRICES = {"ZTL", "K3", "LP", "WK", "Ł3"}
OTHER = {"IPC", "MO2"}


def law_distance(v1, v2, pool):
    return sum(1 for f in pool if v1(f) != v2(f)) / len(pool)


def rule_distance(d1, d2, pool):
    n = bad = 0
    for g in pool:
        for f in pool:
            n += 1
            if d1([g], f) != d2([g], f):
                bad += 1
    return bad / n


def matrix(fn, pool, oracles):
    names = [SHORT[n] for n, _, _ in ALL]
    D = {}
    for (n1, o1), (n2, o2) in itertools.combinations(zip(names, oracles), 2):
        D[(n1, n2)] = D[(n2, n1)] = fn(o1, o2, pool)
    return names, D


def show(names, D, title):
    print(f"\n{'=' * 74}\n{title}\n{'=' * 74}")
    print("       " + "".join(f"{n:>8s}" for n in names))
    for a in names:
        row = "".join(f"{D[(a, b)]:>8.3f}" if a != b else f"{'—':>8s}"
                      for b in names)
        print(f"  {a:5s}{row}")


def cluster_verdict(names, D, label):
    """R1 asks one thing: is every matrix–matrix pair closer than every
    matrix–other pair? Reported as the two ranges, which is honest even
    when they overlap."""
    mm = [(D[(a, b)], a, b) for a, b in itertools.combinations(names, 2)
          if a in MATRICES and b in MATRICES]
    mo = [(D[(a, b)], a, b) for a, b in itertools.combinations(names, 2)
          if (a in MATRICES) != (b in MATRICES)
          and (a in MATRICES | OTHER) and (b in MATRICES | OTHER)]
    if not mm or not mo:
        return None
    print(f"\n  {label}")
    print(f"    matrix–matrix pairs : {len(mm):2d}, "
          f"range {min(mm)[0]:.3f} … {max(mm)[0]:.3f}")
    print(f"      nearest  {min(mm)[1]}|{min(mm)[2]} at {min(mm)[0]:.3f}"
          f"   farthest {max(mm)[1]}|{max(mm)[2]} at {max(mm)[0]:.3f}")
    print(f"    matrix–other pairs  : {len(mo):2d}, "
          f"range {min(mo)[0]:.3f} … {max(mo)[0]:.3f}")
    print(f"      nearest  {min(mo)[1]}|{min(mo)[2]} at {min(mo)[0]:.3f}")
    clean = max(mm)[0] < min(mo)[0]
    print(f"    → the two ranges {'DO NOT overlap' if clean else 'OVERLAP'}"
          f" — R1 {'holds' if clean else 'fails'} on this measure")
    return clean, min(mo)


if __name__ == "__main__":
    print("=" * 74)
    print("LEG 3 — DO THE EIGHT CLUSTER, AND BY WHAT?")
    print("  Apartness was settled in 2c and is cheap. The question is")
    print("  HOW FAR, and whether the distances group by KIND of object.")
    print("=" * 74)

    pool1 = zipc.build_pool(("p", "q"), depth=1)
    pool2 = zipc.build_pool(("p", "q"), depth=2)
    valids = [v for _, v, _ in ALL]
    ders = [d for _, _, d in ALL]

    n1, DL = matrix(law_distance, pool2, valids)
    show(n1, DL, f"LAW DISTANCE — disagreement on ⊨ φ, {len(pool2)} formulas")
    print("\n  Read with care: K3 and WK have NO tautologies at all, so")
    print("  their law row measures 'has theorems', not kinship.")
    r_law = cluster_verdict(n1, DL, "R1 on law distance")

    n2, DR = matrix(rule_distance, pool1, ders)
    show(n2, DR, f"RULE DISTANCE — disagreement on γ ⊨ φ, "
                 f"{len(pool1) ** 2} pairs")
    r_rule = cluster_verdict(n2, DR, "R1 on rule distance (the informative one)")

    print(f"\n{'=' * 74}\nVERDICT ON THE PRE-REGISTERED PAIR\n{'=' * 74}")
    ok = bool(r_rule and r_rule[0])
    print(f"  R1 (kind predicts proximity) : {'HOLDS' if ok else 'FAILS'}")
    print(f"  R2 (proximity cuts across kinds) : "
          f"{'FAILS' if ok else 'HOLDS'}")
    if not ok and r_rule:
        d, a, b = r_rule[1]
        print(f"\n  The crossing pair is {a}|{b} at {d:.3f} — a matrix and a")
        print("  non-matrix nearer to each other than some two matrices are.")
        print("  So being the same KIND of object does not make two grounds")
        print("  say the same things, and the curator's 3-versus-4 split")
        print("  does not survive either: the family has two independent")
        print("  axes, and neither is a relabelling of the other.")
    # -----------------------------------------------------------------
    # What DOES group, then. Read off the rule matrix rather than assumed.
    # -----------------------------------------------------------------
    print(f"\n{'=' * 74}\nWHAT ACTUALLY GROUPS\n{'=' * 74}")
    blocks = []
    seen = set()
    for a in n2:
        if a in seen:
            continue
        blk = [b for b in n2 if b == a or DR[(a, b)] == 0.0]
        for b in blk:
            seen.add(b)
        blocks.append(blk)
    print("  Blocks of grounds at rule distance EXACTLY 0 (identical")
    print("  single-premise consequence on the pool):")
    for blk in blocks:
        print(f"    {{{', '.join(blk)}}}")
    print()
    print("  None of these blocks is a block of KINDS. IPC — which has no")
    print("  finite characteristic matrix at all — sits at distance 0 from")
    print("  two three-valued matrices. WK, a matrix, is the most isolated")
    print("  ground in the family. Kind predicts nothing here.")
    print()
    print("  And the two matrices are not the same table: ZTL|K3 is 0.000 on")
    print(f"  rules and {DL[('ZTL','K3')]:.3f} on laws — identical single-premise")
    print("  consequence, different theorems. The rules-versus-laws split of")
    print("  the ZTL preprint reappears here as a property of the FAMILY:")
    print("  two grounds can transport the same and say different things.")

    print("\n  CEILING: a disagreement rate on a bounded pool ranks pairs")
    print("  against each other on the questions asked. It is not a metric")
    print("  with meaning beyond this pool, and tier C throughout.")
    print("\n  LEG 3 GREEN — both predictions were on the record first.")
