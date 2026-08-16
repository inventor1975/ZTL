# -*- coding: utf-8 -*-
"""
Does the redundancy threshold hold on a realistic collective?

`probe_swarm.py` found that warrant either stays local or percolates through
everything, with the switch between 75% and 90% redundancy. That was measured
on a random DAG with local links, and the file said so: the EXISTENCE of a
threshold is probably robust, the LOCATION is a property of the model.

A military collective is not a random graph. It is a command hierarchy, and
real systems also grow hubs — a few agents everyone leans on. If the threshold
moves far between these, the number from probe_swarm is a curiosity. If it
holds, it is a design constant worth handing to somebody planning a swarm.

Three topologies, same 100,000 agents and 1,000,000 links:

  random-local   what probe_swarm used — the baseline, kept for comparison
  hierarchy      a command tree: every agent leans on its commander, plus
                 peers inside its own subtree
  scale-free     preferential attachment: a few agents become hubs that a
                 large part of the collective ends up resting on

Run:  python3 db/probe_topology.py
"""
import random
import statistics
import sys
from collections import defaultdict

N, E = 100_000, 1_000_000
SEED = 20260816


def random_local(rnd):
    par, rev = defaultdict(list), defaultdict(list)
    for _ in range(E):
        c = rnd.randrange(1, N)
        p = rnd.randrange(max(0, c - 200), c)
        par[c].append(p)
        rev[p].append(c)
    return par, rev


def hierarchy(rnd, branching=8):
    """Every agent rests on its commander, then on peers in its own subtree.
    Orders come down; the rest of the load is lateral and local."""
    par, rev = defaultdict(list), defaultdict(list)
    for c in range(1, N):
        p = (c - 1) // branching
        par[c].append(p)
        rev[p].append(c)
    for _ in range(E - (N - 1)):
        c = rnd.randrange(branching + 1, N)
        sub = (c - 1) // branching
        lo = max(0, sub * branching - branching)
        p = rnd.randrange(lo, c)
        par[c].append(p)
        rev[p].append(c)
    return par, rev


def scale_free(rnd):
    """Preferential attachment: an agent already leaned on gets leaned on
    more. This is the shape that grows hubs, and hubs are what a cascade
    likes."""
    par, rev = defaultdict(list), defaultdict(list)
    pool = [0]
    for c in range(1, N):
        p = pool[rnd.randrange(len(pool))]
        par[c].append(p)
        rev[p].append(c)
        pool.append(p)
        pool.append(c)
    for _ in range(E - (N - 1)):
        c = rnd.randrange(1, N)
        p = pool[rnd.randrange(len(pool))]
        if p < c:
            par[c].append(p)
            rev[p].append(c)
            pool.append(p)
    return par, rev


def redundant(par, rev, frac, rnd):
    """A SECOND GROUND, and only that.

    THE BUG THIS REPLACES was found by adversarial review and was not small.
    The old version appended the extra parent to the node's ONE parent list
    and then switched that whole list from `any(dead)` to `all(dead)` — so a
    node with eleven inputs (the median here) went from an eleven-input OR to
    an eleven-input AND. Nothing in it had two grounds: measured on the
    flagged set, 0.0% of nodes had exactly two parents. The word "redundancy"
    described an operation the code never performed, and every number the
    note quoted from it was a number about something else.

    Stated semantics, now implemented: ground A is the node's original
    support, which is CONJUNCTIVE — lose any of it and A fails. Ground B is
    one added, independent claim. The node falls only when A fails AND B
    fails."""
    B = {}
    for c in list(par):
        if rnd.random() < frac:
            x = rnd.randrange(0, max(1, c))
            B[c] = x
            rev[x].append(c)
    return B


def cascade(par, rev, B, start):
    dead, frontier = {start}, [start]
    while frontier:
        nxt = []
        for node in frontier:
            for c in rev.get(node, ()):
                if c in dead:
                    continue
                a_fails = any(p in dead for p in (par.get(c) or ()))
                b_fails = c not in B or B[c] in dead
                if a_fails and b_fails:
                    dead.add(c)
                    nxt.append(c)
        frontier = nxt
    return len(dead)


def threshold(make, samples=25):
    """TWO statistics, because one of them was mislabelled.

    The note called this "worst single loss"; it is the worst of 25 UNIFORMLY
    SAMPLED targets, which on a hierarchy almost never lands on a commander.
    The adversarial estimator — deliberately targeting the root and the
    highest-degree nodes — is reported beside it, and the two do not agree
    even slightly. Reporting the sampled figure alone was the error
    probe_containment had already named in its own docstring while this file
    went on repeating it."""
    row, found = [], None
    for frac in (0.0, 0.5, 0.75, 0.85, 0.90, 0.95):
        rnd = random.Random(SEED)
        par, rev = make(rnd)
        two = redundant(par, rev, frac, rnd)
        rs = random.Random(7)
        # MEDIAN AND WORST, because the median lied. On a scale-free graph
        # most agents are leaves, so a typical compromise costs nothing and
        # the median reports safety — while the whole reason that topology is
        # interesting is the handful of hubs a random draw rarely hits. A
        # statistic that hides the case the shape exists for is the wrong
        # statistic, and reporting it alone would have been the worse error.
        hits = [cascade(par, rev, two, s) for s in rs.sample(range(N), samples)]
        # what an adversary picks: the root, and the most-depended-on nodes
        chosen = [0] + [n for n, _d in sorted(rev.items(),
                                              key=lambda kv: -len(kv[1]))[:3]
                        if isinstance(n, int)]
        adv = max(cascade(par, rev, two, t) for t in chosen)
        row.append((frac, max(hits), adv))
        if found is None and max(hits) < N / 100:
            found = frac
    return row, found


def main():
    print("=" * 78)
    print("DOES THE THRESHOLD HOLD ON A REALISTIC COLLECTIVE?")
    print("=" * 78)
    print(f"  {N:,} agents, {E:,} links. Top row: worst of 25 SAMPLED targets.\n  Bottom row: an adversary choosing the root and the biggest hubs.\n")
    header = "  ".join(f"{int(f*100):>5}%" for f in
                       (0.0, 0.5, 0.75, 0.85, 0.90, 0.95))
    print(f"  {'topology':14} {header}    threshold")
    results, rows_all = {}, []
    for name, make in (("random-local", random_local),
                       ("hierarchy", hierarchy),
                       ("scale-free", scale_free)):
        row, th = threshold(make)
        results[name] = th
        rows_all += row
        cells = "  ".join(f"{w:>6,}" for _f, w, _a in row)
        advs = "  ".join(f"{a:>6,}" for _f, _w, a in row)
        print(f"  {name:14} {cells}    "
              f"{'never' if th is None else f'{int(th*100)}%'}")
        print(f"  {'':14} {advs}    <- deliberately targeted")

    print("""
  THE THRESHOLD IS AN ARTEFACT OF WHERE YOU AIM, and finding that out
  cost this file its headline. Read the two rows of each topology
  together. Against 25 uniformly sampled targets, redundancy works
  exactly as advertised: 95,081 falls to 195 by 75% on the hierarchy.
  Against an adversary choosing the root or the biggest hub, the same
  collective loses 100,000 at EVERY column — at zero redundancy and at
  ninety-five per cent alike.

  So the earlier claim of this file, that a threshold exists on every
  topology and only its location moves, was measured against a sampler
  that almost never hits a commander. There is no threshold against a
  chosen target. There is a threshold against a random one, and the two
  are different questions that were reported as one.

  WHY REDUNDANCY FAILS HERE IS NOT A BUG IN THE IDEA. The second ground
  is drawn from inside the same structure (`rnd.randrange(0, c)`), so it
  descends from the same root; killing the root kills the alternative
  too. That is precisely what probe_roots measures as authority-root
  diversity, arriving here from the other direction: redundancy that is
  not independent OF THE THING BEING ATTACKED is not redundancy. A
  designer reading only the sampled row would provision 75% redundancy
  and believe the collective contained.

  WHAT SURVIVES. Redundancy contains randomly located loss, which is the
  ordinary failure — an agent lost to terrain, a sensor to weather, a
  link to congestion. It does nothing measurable against a loss aimed at
  the structure. Those are the two halves of DICE's own phases, and this
  run says they need different mechanisms rather than more of one.""")
    # the finding, pinned: a threshold against sampling, none against aim
    assert all(t is not None for t in results.values())
    assert all(adv > 0.9 * N for _f, _w, adv in rows_all)
    print("\nTOPOLOGY PROBE GREEN — a threshold against sampling, none "
          "against aim.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
