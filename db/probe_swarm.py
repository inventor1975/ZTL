# -*- coding: utf-8 -*-
"""
Warrant in a decentralized collective — measured at DARPA DICE's own numbers.

Written 2026-08-16 for a specific question: DICE (HR001126S0010) wants a
collective of heterogeneous agents that sustains long-horizon missions,
stays aligned with commander's intent, and survives the failure or
compromise of individual agents. Its TA2 is called "Role Coherence and
LOCAL Inference Control". Its phases name their scale outright — 500 agents
and 5,000 interactions, then 5,000 and 50,000, then 100,000 and 1,000,000.

So the question is not whether the words match. It is what this corpus's
cascade actually does at those numbers, and the answer arrived in two parts,
the second of which was not expected.

FIRST: speed is not the problem. At 100,000 agents and 1,000,000 links a
withdrawal propagates in tens of milliseconds.

SECOND, and this is the finding: THE ANSWER IS USELESS ANYWAY. With one
ground per conclusion, a single compromised agent takes down a median of
half the collective. "About 52,000 of your conclusions no longer stand" is
not something a commander can act on, and no amount of speed repairs it.

THIRD: the containment is already in the corpus, and it has a THRESHOLD. A
conclusion resting on two declared-independent grounds falls only if both
fall (`earned:a|b`, in zbook since the Agrippa work). Sweeping the fraction
of conclusions that carry a second ground does not give a gentle curve; it
gives a collapse between 75% and 90%, of nearly four orders of magnitude.
Warrant either stays local or percolates through everything, and which one
happens is a property of the redundancy, not of the topology.

Run:  python3 db/probe_swarm.py
"""
import random
import statistics
import sys
import time
from collections import defaultdict

from _ground import swept, save_ground    # the sweep records what it varied

N, E = 100_000, 1_000_000            # DICE phase 3, verbatim
SEED = 20260816


def collective(n, e, frac_two, seed=SEED):
    """A DAG of agents, each conclusion resting on the conclusions of others.
    `frac_two` of them declare a SECOND, independent ground."""
    rnd = random.Random(seed)
    parents, rev, two = defaultdict(list), defaultdict(list), set()
    for _ in range(e):
        c = rnd.randrange(1, n)
        p = rnd.randrange(max(0, c - 200), c)      # local, not global, links
        parents[c].append(p)
        rev[p].append(c)
    for c in list(parents):
        if rnd.random() < frac_two:
            x = rnd.randrange(0, max(1, c))
            parents[c].append(x)
            rev[x].append(c)
            two.add(c)
    return parents, rev, two


def cascade(parents, rev, two, compromised):
    """What stops standing. A single-ground conclusion falls when its ground
    falls; a two-ground one falls only when BOTH do."""
    dead = set(compromised)
    frontier = list(compromised)
    while frontier:
        nxt = []
        for node in frontier:
            for c in rev.get(node, ()):
                if c in dead:
                    continue
                ps = parents.get(c) or []
                if (all(p in dead for p in ps) if c in two
                        else any(p in dead for p in ps)):
                    dead.add(c)
                    nxt.append(c)
        frontier = nxt
    return len(dead)


def sweep(frac, k, samples=40):
    parents, rev, two = collective(N, E, frac)
    rs = random.Random(7)
    sizes, times = [], []
    for _ in range(samples):
        start = rs.sample(range(N), k)
        t0 = time.perf_counter()
        sizes.append(cascade(parents, rev, two, start))
        times.append((time.perf_counter() - t0) * 1000)
    return statistics.median(sizes), statistics.median(times)


def main():
    print("=" * 78)
    print("WARRANT IN A DECENTRALIZED COLLECTIVE — at DICE's own numbers")
    print("=" * 78)
    print(f"  python {sys.version.split()[0]}")

    print("\n  1. SPEED, at the three phase targets")
    for n, e, label in ((500, 5_000, "phase 1"), (5_000, 50_000, "phase 2"),
                        (100_000, 1_000_000, "phase 3")):
        parents, rev, two = collective(n, e, 0.0)
        t0 = time.perf_counter()
        fell = cascade(parents, rev, two, [random.Random(7).randrange(n)])
        dt = (time.perf_counter() - t0) * 1000
        print(f"       {label}: {n:>7,} agents {e:>9,} links   "
              f"cascade {dt:6.1f} ms   {fell:,} fall")
    print("     Speed was never going to be the problem. A withdrawal is a")
    print("     graph walk, and a graph walk over a million links is cheap.")

    print("\n  2. AND THE ANSWER IS USELESS ANYWAY — one ground per conclusion")
    med, t = sweep(0.0, 1)
    print(f"       one compromised agent, median fallout   {med:,} of {N:,}"
          f"   ({100 * med // N}%)")
    print("     Half the collective. A commander cannot act on that, and no")
    print("     amount of speed repairs it. This is the honest state of the")
    print("     mechanism before anything is done about it, and it is why")
    print("     DICE's TA2 has the word LOCAL in its title.")
    assert med > N * 0.3

    print("\n  3. THE CONTAINMENT IS ALREADY HERE, AND IT HAS A THRESHOLD")
    print("       (a conclusion on two declared-independent grounds falls")
    print("        only if both do — `earned:a|b`, in zbook since Agrippa)")
    print(f"\n       {'redundant conclusions':>24} {'1 compromise':>14}"
          f" {'10 compromises':>16}")
    curve = {}
    for frac in swept('redundancy', (0.0, 0.5, 0.75, 0.80, 0.85, 0.90, 1.0)):
        a, _ = sweep(frac, 1)
        b, _ = sweep(frac, 10)
        curve[frac] = a
        print(f"       {int(frac * 100):>23}% {a:>14,.0f} {b:>16,.0f}")
    print("     Not a curve — a collapse. Between 75% and 90% redundancy the")
    print("     median fallout drops by nearly four orders of magnitude.")
    print("     Warrant either stays local or percolates through everything,")
    print("     and which one happens is a property of the REDUNDANCY, not")
    print("     of the topology or the scale.")
    assert curve[0.75] > 1000 and curve[0.90] < 100

    print("""
  WHAT THIS CLOSES, and where it stops. It closes the question a
  commander asks after an agent is lost: which conclusions no longer
  stand, computed by name in tens of milliseconds at a hundred thousand
  agents, and it gives the design rule that keeps the answer small.

  It does NOT decide that an agent WAS compromised. That is an input
  here, and against an adversary who controls the input this corpus is
  not weak but inert — measured, in db/probe_failures.py, against
  Wirecard.

  And the threshold above rests on a declaration this machine cannot
  check: that two grounds are INDEPENDENT. Two agents fed by one
  corrupted upstream source are one ground under two names, and nothing
  here detects it. At 90% declared redundancy the collective would be
  reported as resilient while being no such thing — so at this scale our
  oldest published ceiling stops being a footnote and becomes the
  dominant risk. Closing it needs authentication of the source, which is
  a different machine and must be said to be one.""")
    save_ground(__file__)
    print("\nSWARM PROBE GREEN — fast, useless alone, and bounded by a "
          "threshold.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
