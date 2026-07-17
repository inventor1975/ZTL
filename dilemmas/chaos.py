# -*- coding: utf-8 -*-
"""chaos — will the thinking system survive in binary chaos?

The self-test: OUR architecture (the coin pipeline + memory + the world
remembering its stipulations) dropped into a random binary world, under
the action zugzwang (a bivalent answer is mandatory per query).

World: 30 atoms with hidden random bits; 6 are FREE cells — the world
never reveals them, but REMEMBERS the agent's stipulations (a laid
ground becomes truth). Queries: a stream of random formulas; every
query must be answered T/F.

Agents: the believer (bivalence: guesses all atoms upfront, never
verifies), the amnesiac (the coin pipeline, no memory), the rememberer
(pipeline + memory, budget 1 verification per query), the orderer
(same, but verifies the most-queried atoms first).
"""
import os
import random
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztl import T, F, Z, ev

random.seed(7)
ATOMS = [f"a{i}" for i in range(30)]
FREE = set(random.sample(ATOMS, 6))
BASE = {a: random.choice([T, F]) for a in ATOMS}
OPS = ["and", "or", "imp", "xor", "xnor"]


def rand_formula():
    a, b, c = random.sample(ATOMS, 3)
    f = (random.choice(OPS), a, b)
    return (random.choice(OPS), f, c) if random.random() < .5 else f


QUERIES = [rand_formula() for _ in range(2000)]


def atoms_of(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi in BASE:
            acc.add(phi)
    else:
        for x in phi[1:]:
            atoms_of(x, acc)
    return acc


FREQ = {}
for q in QUERIES:
    for a in atoms_of(q):
        FREQ[a] = FREQ.get(a, 0) + 1


from itertools import product


def forced(q, known):
    """The stage court of the query: the verdict forced by the known
    bits, or None. (The greedy register never asks — it answers F on the
    unverified; the honest verification trigger is UNFORCEDNESS.)"""
    unk = sorted(a for a in atoms_of(q) if a not in known)
    vals = set()
    for combo in product((T, F), repeat=len(unk)):
        env = {a: known[a] for a in atoms_of(q) if a in known}
        env.update(zip(unk, combo))
        vals.add(ev(q, env))
        if len(vals) > 1:
            return None
    return vals.pop()


def run(policy):
    """policy: 'believer' | 'amnesiac' | 'rememberer' | 'orderer'."""
    world = dict(BASE)                      # this agent's copy of the world
    beliefs = {a: random.choice([T, F]) for a in ATOMS}
    known = {}
    errors, verifs = [], 0
    for q in QUERIES:
        if policy == "believer":
            v = ev(q, beliefs)
        else:
            if policy == "amnesiac":
                known = {}
            v = forced(q, known)
            budget = 1
            while v is None:
                cand = [a for a in atoms_of(q) if a not in known]
                if not cand:
                    break
                if policy == "orderer":
                    cand.sort(key=lambda a: -FREQ.get(a, 0))
                a = cand[0]
                if a in FREE:
                    known[a] = F            # stipulate the F-coin —
                    world[a] = F            # and the WORLD REMEMBERS it
                elif budget > 0:
                    known[a] = world[a]     # verify (pay)
                    verifs += 1
                    budget -= 1
                else:
                    break
                v = forced(q, known)
            if v is None:
                v = F                       # zugzwang: the coin answers F
        errors.append(v != ev(q, world))
    e0 = sum(errors[:200]) / 2
    e9 = sum(errors[-200:]) / 2
    return e0, e9, sum(errors), verifs


def skewed_world():
    """EXP 2 — ordering pays only where chaos has STRUCTURE. A Zipf-skewed
    world (hot and cold atoms), scarce budget (one verification per 10
    queries): the INVESTOR (verifies the world's hot core proactively)
    against the hole-patcher (verifies the current query's atoms)."""
    rnd = random.Random(7)
    n = 300
    atoms = [f"b{i}" for i in range(n)]
    base = {a: rnd.choice([T, F]) for a in atoms}
    w = [1 / (i + 1) for i in range(n)]

    def rf():
        picks = []
        while len(picks) < 3:
            x = rnd.choices(atoms, weights=w, k=1)[0]
            if x not in picks:
                picks.append(x)
        a, b, c = picks
        f = (rnd.choice(OPS), a, b)
        return (rnd.choice(OPS), f, c) if rnd.random() < .5 else f

    queries = [rf() for _ in range(1500)]
    freq = {}
    for q in queries:
        for a in atoms_of_gen(q, base):
            freq[a] = freq.get(a, 0) + 1

    def forced_g(q, known):
        unk = sorted(a for a in atoms_of_gen(q, base) if a not in known)
        vals = set()
        for combo in product((T, F), repeat=len(unk)):
            env = {a: known[a] for a in atoms_of_gen(q, base) if a in known}
            env.update(zip(unk, combo))
            vals.add(ev(q, env))
            if len(vals) > 1:
                return None
        return vals.pop()

    def run2(strategy):
        known, errs = {}, 0
        pool = sorted(atoms, key=lambda a: -freq.get(a, 0))
        for i, q in enumerate(queries):
            if i % 10 == 0:
                if strategy == "patcher":
                    cand = [a for a in atoms_of_gen(q, base) if a not in known]
                    pick = cand[0] if cand else next(
                        (a for a in pool if a not in known), None)
                else:
                    pick = next((a for a in pool if a not in known), None)
                if pick:
                    known[pick] = base[pick]
            v = forced_g(q, known)
            if v is None:
                v = F
            errs += (v != ev(q, base))
        return errs

    e_patch, e_inv = run2("patcher"), run2("investor")
    print(f"  hole-patcher (current query)  : {e_patch} errors of 1500")
    print(f"  INVESTOR (the world's hot core): {e_inv} errors of 1500 — "
          "same 150 verifications")
    assert e_inv < e_patch
    return e_patch, e_inv


def atoms_of_gen(phi, base, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi in base:
            acc.add(phi)
    else:
        for x in phi[1:]:
            atoms_of_gen(x, base, acc)
    return acc




def drifting_world():
    """EXP 3 — the destruction effect (the curator's dropout): the world
    DRIFTS — bits silently flip. Stale knowledge does not just age, it
    changes grade in the dark: it looks hereditary and has become
    credit. The archivist (eternal memory) against forgetters (memory
    with a TTL — dropout as hygiene)."""
    rnd = random.Random(7)
    atoms = [f"c{i}" for i in range(30)]
    base = {a: rnd.choice([T, F]) for a in atoms}

    def rf():
        a, b, c = rnd.sample(atoms, 3)
        f = (rnd.choice(OPS), a, b)
        return (rnd.choice(OPS), f, c) if rnd.random() < .5 else f

    queries = [rf() for _ in range(3000)]
    flips = [[a for a in atoms if rnd.random() < 0.0015]
             for _ in range(3000)]

    def forced_d(q, known):
        unk = sorted(a for a in atoms_of_gen(q, base) if a not in known)
        vals = set()
        for combo in product((T, F), repeat=len(unk)):
            env = {a: known[a] for a in atoms_of_gen(q, base) if a in known}
            env.update(zip(unk, combo))
            vals.add(ev(q, env))
            if len(vals) > 1:
                return None
        return vals.pop()

    def run3(ttl):
        w = dict(base)
        mem = {}
        errs, ver = [], 0
        for i, q in enumerate(queries):
            for a in flips[i]:
                w[a] = T if w[a] == F else F
            known = {a: v for a, (v, t) in mem.items() if i - t < ttl}
            v = forced_d(q, known)
            budget = 1
            while v is None and budget > 0:
                cand = [a for a in atoms_of_gen(q, base) if a not in known]
                if not cand:
                    break
                a = cand[0]
                mem[a] = (w[a], i)
                known[a] = w[a]
                ver += 1
                budget -= 1
                v = forced_d(q, known)
            if v is None:
                v = F
            errs.append(v != ev(q, w))
        return sum(errs[:500]) / 5, sum(errs[-500:]) / 5, sum(errs), ver

    rows = {}
    for name, ttl in (("archivist (eternal memory)", 10**9),
                      ("forgetter  (TTL 250)      ", 250),
                      ("forgetter  (TTL 40)       ", 40)):
        e0, e9, tot, ver = run3(ttl)
        rows[ttl] = (e0, e9, tot, ver)
        print(f"  {name}: err {e0:.1f}% -> {e9:.1f}%, total {tot}, "
              f"verifs {ver}")
    assert rows[10**9][1] > 30            # eternal memory rots blind
    assert rows[250][2] < rows[10**9][2]  # forgetting is hygiene
    assert rows[40][2] < rows[250][2] and rows[40][3] > 3 * rows[250][3]
    print("""
  in a drifting world eternal memory KILLS (the archivist climbs to 40%
  — only the believer is worse): stale knowledge wears the wrong grade.
  Forgetting is hygiene — dropout re-grades the stale back to honest Z;
  and the TTL is a price dial: faster forgetting buys accuracy at a
  verification cost. The ritual closes its own loop here: even the
  verified must be re-verified — the ritual is eternal because the
  world drifts.""")

if __name__ == "__main__":
    print("BINARY CHAOS — the self-test of the architecture\n")
    print("EXP 1 — uniform chaos: is survival possible?\n")
    print(f"  {'agent':12} {'err first 200':>14} {'err last 200':>13} "
          f"{'errors total':>13} {'verifs':>7}")
    rows = {}
    for p in ("believer", "amnesiac", "rememberer", "orderer"):
        e0, e9, tot, ver = run(p)
        rows[p] = (e0, e9, tot, ver)
        print(f"  {p:12} {e0:13.1f}% {e9:12.1f}% {tot:13} {ver:7}")
    assert rows["believer"][1] > 20          # bivalence never learns
    assert rows["amnesiac"][1] > 20          # no memory — no survival
    assert rows["rememberer"][1] < 5         # memory turns chaos into a floor
    print("\n  memory is survival: the rememberer decays to the floor (24")
    print("  verifications, then everything is forced; stipulated free cells")
    print("  are owned forever — the world remembers). HONEST NEGATIVE: the")
    print("  orderer gains nothing here (5 vs 3 errors — noise): in UNIFORM")
    print("  chaos there is nothing to order.\n")
    print("EXP 2 — skewed chaos, scarce budget: does ordering pay?\n")
    skewed_world()
    print("\nEXP 3 — the drifting world: destruction of the built\n")
    drifting_world()
    print("""
  VERDICT: survival is bought by MEMORY, not by wit (the pipeline without
  memory scores like a guesser). What will it do? Grow territory: the
  verified plus the stipulated (the world remembers — the sediment of
  decisions is literal property; the self made of laid grounds). Will a
  GOAL of ordering emerge? The logic has no goals (value is off its
  axis) — and the gradient itself is conditional: absent in uniform
  chaos, real in structured chaos (the investor beats the hole-patcher
  at equal budget). So the drive to order is not born of chaos — it is
  the reflection of the structure already in the world; any selection
  over survival will find it there, and only there.""")
