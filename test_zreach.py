# -*- coding: utf-8 -*-
"""zreach against enumeration: the set of values over every completion / every refinement, on random formulas with
repeated atoms, every connective, mixed markings. And the witnesses: each re-evaluated (zreach does it itself)."""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ztl import T, F, Z, ev           # noqa: E402
import zreach as R                    # noqa: E402

OPS = ("and", "or", "imp", "xor", "xnor")


def rand_phi(rng, atoms, depth):
    if depth == 0 or rng.random() < 0.25:
        return rng.choice(atoms) if rng.random() < 0.92 else rng.choice((T, F, Z))
    if rng.random() < 0.2:
        return ("not", rand_phi(rng, atoms, depth - 1))
    return (rng.choice(OPS), rand_phi(rng, atoms, depth - 1), rand_phi(rng, atoms, depth - 1))


def atoms_of(phi, acc):
    if isinstance(phi, str):
        if phi not in (T, F, Z):
            acc.add(phi)
    else:
        for c in phi[1:]:
            atoms_of(c, acc)
    return acc


def brute(phi, marking, vals):
    dirty = sorted(a for a, v in marking.items() if v == Z)
    out = set()
    for combo in itertools.product(vals, repeat=len(dirty)):
        out.add(ev(phi, dict(marking, **dict(zip(dirty, combo)))))
    return frozenset(out)


def _consts(phi):
    if isinstance(phi, str):
        return [phi] if phi in (T, F, Z) else []
    return [c for x in phi[1:] for c in _consts(x)]


def main():
    rng = random.Random(20261109)
    n = bad = refused = 0
    for _ in range(6000):
        names = [f"p{i}" for i in range(rng.randint(1, 6))]
        phi = rand_phi(rng, names, rng.randint(1, 5))
        marking = {a: rng.choice((Z, Z, T, F)) for a in atoms_of(phi, set())}
        for mode, vals in (("completion", (T, F)), ("refinement", (T, F, Z))):
            r = R.reach(phi, marking, mode)
            if "refused" in r:
                refused += 1
                continue
            n += 1
            if r["values"] != brute(phi, marking, vals):
                bad += 1
                if bad <= 5:
                    print("MISMATCH", mode, phi, marking, set(r["values"]), set(brute(phi, marking, vals)))
    print(f"{n} (formula, marking, mode) cases against enumeration, {bad} mismatches, {refused} refused")
    # the cap refuses aloud
    big = ("and",) + (("xor", "a", "b"),)
    phi = "a0"
    for i in range(1, 15):
        phi = ("xor", phi, ("and", "a0", f"a{i}"))
    phi = ("and", phi, ("or",) + tuple([phi[1]]) + ("a14",)) if False else phi
    r = R.reach(phi, {f"a{i}": Z for i in range(15)}, cap=0)
    assert "refused" in r, r
    # a read-once AND/OR of 1000 atoms: one pass
    import time
    rng = random.Random(7)
    lits = [f"x{i}" if rng.random() < .5 else ("not", f"x{i}") for i in range(1000)]
    while len(lits) > 1:
        lits = [(rng.choice(("and", "or")), lits[i], lits[i + 1]) if i + 1 < len(lits) else lits[i]
                for i in range(0, len(lits), 2)]
    t = time.perf_counter()
    ans = R.sat(lits[0], {f"x{i}": Z for i in range(1000)})
    took = time.perf_counter() - t
    assert ans[0] in ("YES", "NO")
    print(f"1000 read-once atoms: {ans[0]} in {took * 1000:.1f} ms")
    # zverify's two bits through zreach, against their DEFINITIONS (every completion / every refinement)
    import zverify as V
    from zmodal import worlds, ztl_eval
    rng = random.Random(11)
    nb = bad_b = refused_b = 0
    for _ in range(3000):
        names = [f"p{i}" for i in range(rng.randint(1, 5))]
        phi = rand_phi(rng, names, rng.randint(1, 4))
        if any(c in (T, F, Z) for c in [phi] if isinstance(phi, str)):
            continue
        marking = {a: rng.choice(("M", "M", T, F)) for a in atoms_of(phi, set())}
        if any(x == Z for x in _consts(phi)):
            continue                      # a literal Z constant: zverify's old path, not zreach's
        v = ztl_eval(phi, marking)
        st = all(ev(phi, w) == v for w in worlds(marking))
        her = all(ztl_eval(phi, m2) == v for m2 in V.refinements(marking))
        nb += 1
        # budget=1: every claim with a mark goes the zreach way (in place of the refusal); None = zreach refused
        sb, hb = V.stable_bit(phi, marking, budget=1), V.hereditary_bit(phi, marking, budget=1)
        if sb is None or hb is None:
            refused_b += 1
        if (sb is not None and sb != st) or (hb is not None and hb != her) or \
                V.stable_bit(phi, marking) != st or V.hereditary_bit(phi, marking) != her:
            bad_b += 1
            if bad_b <= 5:
                print("GRADE MISMATCH", phi, marking)
    print(f"zverify stable/hereditary through zreach: {nb} cases against the definitions, {bad_b} mismatches ({refused_b} refused)")
    bad += bad_b
    if bad:
        print("ZREACH RED")
        sys.exit(1)
    print("ZREACH GREEN")


if __name__ == "__main__":
    main()
