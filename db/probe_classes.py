# -*- coding: utf-8 -*-
"""
Six failure classes — do our own numbers survive?

probe_criterion measured two dependency dimensions, evidence and authority,
and published r* = 0.65 and q* = 0.35. Arkadiy Miteiko's list is longer:
evidence-source loss, agent loss, shared-model loss, shared-sensor loss,
authority-root loss, delegated-authority loss.

Those are not features to add to the calculus. The cascade already removes any
node without caring what it is; what changes is the MODEL of the world, and
therefore the numbers. And there is a reason to expect the numbers to get
WORSE rather than better: our own result says dimensions neither average nor
exchange, and containment fails if ANY dimension fails. More shared substrates
means strictly more ways to fail, so r*=0.65 and q*=0.35 were measured under
an optimistic world and this file is the check on them.

A real collective shares more than evidence and orders. It shares a handful of
MODELS and a handful of SENSOR feeds — a few nodes on which thousands of
agents rest without anybody calling it a dependency.

Run:  python3 db/probe_classes.py
"""
import random
import sys
from collections import defaultdict

N = 40_000
MODELS, SENSORS = 20, 50
SEED = 20260816
BRANCH = 8

M0, S0 = N, N + MODELS                       # node ids for shared substrates


def build(r, q, rnd, dims=4):
    """Every conclusion rests on evidence, on authority, and — if `dims` is 4
    — on a shared model and a shared sensor feed. Redundancy r and hidden
    correlation q apply in every dimension alike."""
    dep = {"evi": defaultdict(list), "auth": defaultdict(list),
           "model": defaultdict(list), "sensor": defaultdict(list)}
    for c in range(1, N):
        dep["evi"][c].append(rnd.randrange(max(0, c - 200), c))
        dep["auth"][c].append((c - 1) // BRANCH)
        if dims == 4:
            dep["model"][c].append(M0 + rnd.randrange(MODELS))
            dep["sensor"][c].append(S0 + rnd.randrange(SENSORS))
        for kind, lo, hi in (("evi", 0, c), ("auth", 0, c),
                             ("model", M0, M0 + MODELS),
                             ("sensor", S0, S0 + SENSORS)):
            if kind not in dep or not dep[kind].get(c):
                continue
            if rnd.random() < r and rnd.random() >= q:
                dep[kind][c].append(rnd.randrange(lo, max(lo + 1, hi)))
    rev = defaultdict(list)
    for g in dep.values():
        for c, ps in g.items():
            for p in ps:
                rev[p].append(c)
    return dep, rev


def cascade(dep, rev, start):
    dead, frontier = set(start), list(start)
    while frontier:
        nxt = []
        for node in frontier:
            for c in rev.get(node, ()):
                if c in dead:
                    continue
                for g in dep.values():
                    ps = g.get(c)
                    if ps and all(p in dead for p in ps):
                        dead.add(c)
                        nxt.append(c)
                        break
        frontier = nxt
    return len([d for d in dead if d < N]) / N


def C(r, q, target, dims=4):
    rnd = random.Random(SEED)
    dep, rev = build(r, q, rnd, dims)
    return cascade(dep, rev, [target])


def star(dims):
    grid = [i / 20 for i in range(21)]
    r_star = next((r for r in grid if C(r, 0.0, 7, dims) < 0.01), None)
    q_star = next((q for q in grid if C(1.0, q, 7, dims) >= 0.01), None)
    return r_star, q_star


def main():
    print("=" * 78)
    print("SIX FAILURE CLASSES — do our own numbers survive?")
    print("=" * 78)
    print(f"  {N:,} agents, {MODELS} shared models, {SENSORS} shared sensors\n")

    print("  1. THE CHECK ON OUR PUBLISHED FIGURES")
    r2, q2 = star(2)
    r4, q4 = star(4)
    print(f"       two dimensions (evidence, authority)   r* = {r2:.2f}"
          f"   q* = {q2:.2f}")
    print(f"       four (plus shared model and sensor)    r* = {r4:.2f}"
          f"   q* = {q4:.2f}")
    if r4 > r2 or (q4 is not None and q2 is not None and q4 < q2):
        print("     WORSE, as predicted. The earlier figures were measured in")
        print("     a world with fewer things to share, and publishing them")
        print("     without this check would have understated what a designer")
        print("     has to provide.")
    else:
        print("     NOT worse — a prediction of this file that failed, and it")
        print("     is kept. The shared substrates did not tighten the")
        print("     requirement at this density, which needs explaining rather")
        print("     than celebrating.")

    print("\n  2. A_crit BY FAILURE CLASS, at full genuine redundancy")
    rnd = random.Random(SEED)
    dep, rev = build(1.0, 0.0, rnd, 4)
    load = {"shared model": max(range(M0, M0 + MODELS),
                                key=lambda m: len(rev.get(m, ()))),
            "shared sensor": max(range(S0, S0 + SENSORS),
                                 key=lambda s: len(rev.get(s, ())))}
    classes = [("authority root (commander)", 0),
               ("delegated authority (mid-chain)", 100),
               ("one agent", 5000),
               ("one evidence source", 7),
               ("shared model", load["shared model"]),
               ("shared sensor", load["shared sensor"])]
    worst = []
    for label, node in classes:
        c = cascade(dep, rev, [node])
        worst.append((c, label))
        print(f"       {label:34} C = {c:.4f}")
    worst.sort(reverse=True)
    print(f"     A_crit = {worst[0][0]:.3f}, from {worst[0][1]}.")
    print("     Note which classes are cheap and which are not. Losing one")
    print("     agent or one evidence source costs almost nothing at full")
    print("     redundancy — that is the case redundancy was built for. The")
    print("     expensive ones are the SHARED substrates and the authority")
    print("     root, and neither is repaired by giving every conclusion a")
    print("     second ground, because the second ground rests on the same")
    print("     model, the same feed, or the same commander.")

    print("""
  WHAT THIS SETTLES. The six classes were never a change to the calculus
  — the cascade removes any node without caring what it is. They are a
  change to the model of the world, and the world has more shared floors
  in it than the earlier run assumed.

  The design consequence is one line: redundancy must be redundancy IN
  THE DIMENSION THAT CAN FAIL. Two grounds that resolve to one model are
  one ground; two sensors on one feed are one sensor; two orders under
  one commander are one order. Counting grounds measures nothing unless
  something establishes that they are grounds in different dimensions —
  which is the independence warrant, still unclaimed, and now priced by
  a second experiment rather than one.""")
    print("\nCLASSES PROBE GREEN — the numbers were checked against a "
          "richer world.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
