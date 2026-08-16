# -*- coding: utf-8 -*-
"""
Warrant containment: redundancy that is declared but shared.

Two corrections from Arkadiy Miteiko, both accepted, both material.

FIRST, a method error this file exists to repair: "worst of 25 random
failures" is not a worst case. On a hierarchy or a hub graph the adversary
chooses, and it chooses the commander or the biggest hub — exactly where a
random draw almost never lands. Targets are picked deliberately here.

SECOND, a terminology error of mine. I wrote that attestation would confirm
two grounds come from different sources. It would not. Attestation
establishes IDENTITY and ORIGIN; it says nothing about whether two
authenticated agents rest on one model, one sensor, one intelligence feed or
one authority root. Independence is a property of provenance, not of
identity, and the difference is the whole subject below.

THE DESTRUCTIVE TEST. Hold redundancy at 90% — the level at which the
previous probes reported a collective as contained — and raise the fraction
of those "independent" pairs that secretly share an origin. A pair that
shares its origin is not redundant at all: one withdrawal takes both.

Run:  python3 db/probe_containment.py
"""
import random
import sys
from collections import defaultdict

N, E = 100_000, 1_000_000
SEED = 20260816


def hierarchy(rnd, branching=8):
    par, rev = defaultdict(list), defaultdict(list)
    for c in range(1, N):
        p = (c - 1) // branching
        par[c].append(p)
        rev[p].append(c)
    for _ in range(E - (N - 1)):
        c = rnd.randrange(branching + 1, N)
        lo = max(0, ((c - 1) // branching) * branching - branching)
        p = rnd.randrange(lo, c)
        par[c].append(p)
        rev[p].append(c)
    return par, rev


def dress(par, rev, frac_two, frac_shared, rnd):
    """`two` are conclusions declared to rest on two independent grounds.
    `sham` are those among them whose two grounds secretly share an origin —
    declared redundant, behaving as single."""
    two, sham = set(), set()
    for c in list(par):
        if rnd.random() < frac_two:
            x = rnd.randrange(0, max(1, c))
            par[c].append(x)
            rev[x].append(c)
            two.add(c)
            if rnd.random() < frac_shared:
                sham.add(c)
    return two, sham


def cascade(par, rev, two, sham, start):
    dead, frontier = set(start), list(start)
    while frontier:
        nxt = []
        for node in frontier:
            for c in rev.get(node, ()):
                if c in dead:
                    continue
                ps = par.get(c) or []
                genuine = c in two and c not in sham
                if (all(p in dead for p in ps) if genuine
                        else any(p in dead for p in ps)):
                    dead.add(c)
                    nxt.append(c)
        frontier = nxt
    return len(dead)


def targets(rev, k=3):
    """What an adversary would actually pick: the nodes the most conclusions
    hang off. Random sampling finds these roughly never."""
    return [n for n, _d in sorted(rev.items(), key=lambda kv: -len(kv[1]))[:k]]


def main():
    print("=" * 78)
    print("WARRANT CONTAINMENT — declared redundancy against shared origin")
    print("=" * 78)
    rnd = random.Random(SEED)
    par0, rev0 = hierarchy(rnd)
    tgt = targets(rev0)
    print(f"  hierarchy, {N:,} agents, {E:,} links")
    print(f"  adversary targets the three most-depended-on agents: {tgt}")
    print(f"  (they carry {', '.join(str(len(rev0[t])) for t in tgt)} "
          f"direct dependents)")

    print("\n  1. CHOSEN TARGET vs RANDOM TARGET, at 90% declared redundancy")
    for label, picks in (("random agent", [7]), ("top hub", [tgt[0]]),
                         ("top three hubs", tgt), ("THE COMMANDER", [0])):
        rnd = random.Random(SEED)
        par, rev = hierarchy(rnd)
        two, sham = dress(par, rev, 0.90, 0.0, rnd)
        print(f"       {label:16} -> {cascade(par, rev, two, sham, picks):>7,}"
              f" of {N:,} fall")
    print("     Choosing the target matters and random sampling hid it —")
    print("     and the commander is not a hub, so degree does not find it")
    print("     either. Losing the root takes the WHOLE collective at 90%")
    print("     redundancy, because the 10% of conclusions that carry a")
    print("     single ground are enough to carry the cascade through every")
    print("     level. Redundancy does not contain a root compromise at all:")
    print("     containment is bounded by the WORST-covered path, not by the")
    print("     average one. This is a negative result about our own claim,")
    print("     found by taking the objection seriously rather than by")
    print("     sampling harder.")
    rnd = random.Random(SEED)
    par, rev = hierarchy(rnd)
    two, sham = dress(par, rev, 1.00, 0.0, rnd)
    print(f"       and at 100% redundancy the commander costs "
          f"{cascade(par, rev, two, sham, [0]):,}")

    print("\n  2. THE DESTRUCTIVE TEST — 90% redundancy, rising shared origin")
    print("       (the collective REPORTS the same 90% throughout)")
    print(f"\n       {'secretly shared':>16} {'random':>10} {'top hub':>10}"
          f" {'top three':>11}")
    row = {}
    for shared in (0.0, 0.10, 0.25, 0.50, 0.75, 1.00):
        cells = []
        for picks in ([7], [tgt[0]], tgt):
            rnd = random.Random(SEED)
            par, rev = hierarchy(rnd)
            two, sham = dress(par, rev, 0.90, shared, rnd)
            cells.append(cascade(par, rev, two, sham, picks))
        row[shared] = cells
        print(f"       {int(shared * 100):>15}% {cells[0]:>10,}"
              f" {cells[1]:>10,} {cells[2]:>11,}")

    print("""
  WHAT THIS SAYS. The collective's own report does not move: 90% of its
  conclusions carry two grounds at every row of that table. What moves is
  whether those grounds are two things. Nothing in the ledger, and nothing
  in an attestation layer, distinguishes the top row from the bottom one —
  attestation authenticates each ground and both are genuine documents from
  genuine agents. They simply happen to rest on the same thing.

  So the honest architectural split is three-part, not two, and the middle
  part is the one nobody owns:

    attestation  establishes identity and origin of a ground
    PROVENANCE   establishes whether two grounds are actually distinct
    ZTL          computes what stops standing once grounds go
    topology     bounds how far that loss can travel

  Local inference control is therefore not a property of an inference
  algorithm. It is a containment property of the whole architecture, and
  it has a measurable boundary set by all four together. That sentence is
  Arkadiy's; this file is the measurement under it.""")
    assert row[1.0][2] > row[0.0][2] * 5
    print("\nCONTAINMENT PROBE GREEN — the report holds still while the "
          "collective fails.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
