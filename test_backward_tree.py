# -*- coding: utf-8 -*-
"""
Stand for zbackward_tree.py: the backward pass read off the connectives' tables.

The reference is `zbackward.backward` itself, run WITHOUT its size cut (max_k and
cap raised), where it can finish; past that the answers are checked against the
judge directly, filling by filling.

Checks:
  1. 1500 seeded random formulas, each unverified ground once (read-once), up to
     7 grounds, every target (EARNED, REFUTED, ON CREDIT, OPEN, settled; T, F by
     value): the families equal `zbackward.backward`'s exactly — 0 mismatches;
  2. BEYOND the old cut (MAX_K = 4): a conjunction of n = 5..12 unverified grounds,
     target "settled": the tree gives one set, all n grounds; the judge confirms it
     — every filling of all n settles the claim, and leaving any ONE ground open
     admits a filling that does not (so the set is minimal); n = 200 answers too;
  3. a formula that repeats an unverified ground: not handled (None) — the caller
     keeps the enumeration; and `zbackward.backward` still answers it as before;
  4. MUTATION: one entry of the AND table flipped — check 1 must FAIL.

Run:  python3 test_backward_tree.py   -> BACKWARD TREE GREEN
"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import zbackward as ZB                 # noqa: E402
import zbackward_tree as ZT            # noqa: E402
from ztl import T, F, Z                # noqa: E402

ok = fail = 0
KEYS = ("already", "possible", "guaranteed", "possible_none", "guaranteed_none")
OPS = ["and", "or", "imp", "xor", "xnor"]


def check(name, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {name}")
    else:
        fail += 1; print(f"  FAIL {name} — {why}")


def gen(rnd, atoms):
    if len(atoms) == 1:
        return ("not", atoms[0]) if rnd.random() < 0.2 else atoms[0]
    k = rnd.randint(1, len(atoms) - 1)
    node = (rnd.choice(OPS), gen(rnd, atoms[:k]), gen(rnd, atoms[k:]))
    return ("not", node) if rnd.random() < 0.15 else node


def norm(r):
    # ORDER COUNTS (2026-10-09: the studio shows the list; a first version matched as sets
    # and the studio's test caught the order) — compared as given, not sorted
    return {k: r[k] for k in KEYS}


def equivalence(n_formulas=1500, seed=3):
    rnd = random.Random(seed)
    mism, cases = [], 0
    for _ in range(n_formulas):
        n = rnd.randint(1, 7)
        atoms = [f"a{j}" for j in range(n)]
        rnd.shuffle(atoms)
        phi = gen(rnd, atoms)
        mk = {a: rnd.choice((T, F, Z, Z)) for a in atoms}
        for by_d, targets in ((True, ["EARNED", "REFUTED", "ON CREDIT", "OPEN", ZB.TERMINAL]), (False, [T, F])):
            for tg in targets:
                ref = ZB.backward(phi, mk, tg, by_disposition=by_d, cap_grounds=99, max_k=99, use_tree=False)
                new = ZT.backward_tree(phi, mk, tg, by_disposition=by_d)
                cases += 1
                if new is None or norm(ref) != norm(new):
                    mism.append((phi, mk, tg, by_d))
    return mism, cases


print("1. equal to zbackward.backward (uncut) on read-once formulas")
mism, cases = equivalence()
check(f"{cases} comparisons over 1500 random formulas: 0 mismatches", not mism, str(mism[:2]))

print("2. beyond the old cut: a conjunction of n unverified grounds, target settled")
settled = ZB.TERMINAL


def disp(phi, m):
    return ZB._disposition(phi, m)


all_good = True
for n in range(5, 13):
    atoms = [f"g{i}" for i in range(n)]
    phi = atoms[0]
    for a in atoms[1:]:
        phi = ("and", phi, a)
    mk = {a: Z for a in atoms}
    r = ZT.backward_tree(phi, mk, settled)
    one_set = r["guaranteed"] == [tuple(sorted(atoms))]
    old = ZB.backward(phi, mk, settled, cap_grounds=99, use_tree=False)
    old_blind = old.get("не_искал_дальше") is not None and not old["guaranteed"]
    if n <= 10:     # the judge, filling by filling (2^n fillings)
        every = all(disp(phi, dict(zip(atoms, vals))) in settled
                    for vals in itertools.product((T, F), repeat=n))
        minimal = all(any(disp(phi, dict(zip(atoms, vals), **{a: Z})) not in settled
                          for vals in itertools.product((T, F), repeat=n))
                      for a in atoms)
    else:
        every = minimal = True
    all_good &= one_set and old_blind and every and minimal
check("n = 5..12: the old pass is blind past size 4; the tree gives all n grounds, the judge confirms "
      "guarantee and minimality (n <= 10 filling by filling)", all_good)
atoms = [f"g{i}" for i in range(200)]
phi = atoms[0]
for a in atoms[1:]:
    phi = ("and", phi, a)
r = ZT.backward_tree(phi, {a: Z for a in atoms}, settled)
check("n = 200: one guaranteed set of all 200 grounds", [len(s) for s in r["guaranteed"]] == [200], str(r)[:200])

print("3. a repeated unverified ground: outside the tranche")
phi = ("or", ("and", "p", "q"), ("and", "p", "r"))
mk = {"p": Z, "q": Z, "r": Z}
check("backward_tree returns None (the caller keeps the enumeration)", ZT.backward_tree(phi, mk, settled) is None)
r = ZB.backward(phi, mk, settled)
check("zbackward.backward still answers it (by enumeration)", isinstance(r.get("guaranteed"), list), str(r)[:200])

print("4. mutation: one AND entry flipped must break check 1")
saved = dict(ZT.TABLE2["and"])
ZT.TABLE2["and"][(T, T)] = F
mism_m, _ = equivalence(n_formulas=150, seed=9)
ZT.TABLE2["and"].clear(); ZT.TABLE2["and"].update(saved)
check("mutation caught", len(mism_m) > 0, "mutation survived")

print(f"backward tree: {ok} ok, {fail} failed")
print("BACKWARD TREE GREEN" if fail == 0 else "BACKWARD TREE RED")
