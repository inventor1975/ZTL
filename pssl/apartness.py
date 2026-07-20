# -*- coding: utf-8 -*-
"""
apartness — PSSL leg 2, tack 2c: the receipt of laying a ground.

The cycle's R3: *apartness is earned, identity is not.* Applied to
grounds, it settles what the right object is:

  * "these two grounds are the SAME" quantifies over all formulas. Not
    performable, not witnessable, never earned. There is no act that
    establishes it.
  * "these two grounds are APART" is one formula and one disagreement.
    Finite, checkable, and cheap — an act with a receipt.

So this file does not compute an identity relation on grounds. It
computes, for every pair, the **cheapest witness that they are apart** —
the smallest formula on which their verdicts differ. Minimality is
decided by size, which is objective and needs no interpretation.

The number that comes out is a distance of a sort: how much language you
must build before two grounds can be told apart. It is the operational
content of "a ground is an act": the receipt says what the act bought.

Grounds: the four of leg 1 (`grounds.py`) plus the four of leg 2b
(`family.py`) — classical, intuitionistic, quantum MO2, ZTL, K3, LP,
weak Kleene, Łukasiewicz Ł3.

Run:  python3 pssl/apartness.py
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, _HERE)

import grounds as G                                           # noqa: E402
import family as F                                            # noqa: E402

ALL = [(n, v, d) for n, _, v, d in G.GROUNDS] + \
      [(m.name, m.valid, m.derives) for m in F.FAMILY]

ATOMS = ("p", "q")
OPS = ("and", "or", "imp")


def size(phi):
    return 1 if isinstance(phi, str) else 1 + sum(size(s) for s in phi[1:])


def by_size(maxsize):
    """Every formula over p,q up to `maxsize`, generated in size order so
    that the first separator found is the minimal one."""
    layers = {1: list(ATOMS)}
    yield from layers[1]
    for n in range(2, maxsize + 1):
        cur = []
        for sub in layers[n - 1]:
            cur.append(("not", sub))
        for k in range(1, n - 1):
            for a in layers.get(k, []):
                for b in layers.get(n - 1 - k, []):
                    for op in OPS:
                        cur.append((op, a, b))
        layers[n] = cur
        yield from cur


def show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return f"¬{show(phi[1])}"
    sym = {"and": "∧", "or": "∨", "imp": "→"}[phi[0]]
    return f"({show(phi[1])}{sym}{show(phi[2])})"


def minimal_law_witness(v1, v2, maxsize=5):
    """The smallest φ with valid₁(φ) ≠ valid₂(φ). None if the two agree on
    every formula of that size — which is NOT a proof that they agree."""
    for phi in by_size(maxsize):
        if v1(phi) != v2(phi):
            return phi
    return None


def minimal_rule_witness(d1, d2, maxsize=3, arity=1):
    """Some pairs agree on every law and differ only on a rule.

    APARTNESS HAS AN ARITY, exactly as the deduction theorem did in tack
    2b, and the sweep learned it the same way — by an assertion failing.
    Classical logic and LP share EVERY law (LP's tautologies are the
    classical ones; it is paraconsistent in its consequence relation, not
    in its theorems) and every one-premise rule. They are apart only at
    two premises, where explosion p, ¬p ⊨ q separates them. A
    one-premise search reports "no separator" and would have been read as
    "no difference"."""
    pool = sorted(by_size(maxsize), key=size)
    for combo in itertools.product(pool, repeat=arity):
        for f in pool:
            if d1(list(combo), f) != d2(list(combo), f):
                return (list(combo), f)
    return None


if __name__ == "__main__":
    print("=" * 78)
    print("LEG 2, TACK 2c — APARTNESS OF GROUNDS")
    print("  R3 of the cycle: apartness is earned, identity is not.")
    print("  Two grounds being the SAME quantifies over all formulas and")
    print("  is never witnessed. Two grounds being APART is one formula.")
    print("=" * 78)

    names = [n for n, _, _ in ALL]
    print(f"\n  {len(names)} grounds, {len(names) * (len(names) - 1) // 2} pairs."
          "  Minimal separating formula, by size.\n")
    print(f"  {'pair':40s}{'size':>6s}   witness")

    rows = []
    unresolved = []
    for (n1, v1, d1), (n2, v2, d2) in itertools.combinations(ALL, 2):
        w = minimal_law_witness(v1, v2)
        if w is not None:
            rows.append((n1, n2, size(w), show(w), "law"))
            print(f"  {n1 + ' | ' + n2:40s}{size(w):>6d}   ⊨ {show(w)}")
        else:
            r, ar = None, None
            for a in (1, 2):
                r = minimal_rule_witness(d1, d2, arity=a)
                if r is not None:
                    ar = a
                    break
            if r is None:
                unresolved.append((n1, n2))
                print(f"  {n1 + ' | ' + n2:40s}{'—':>6s}   "
                      "no separator found (NOT a proof of sameness)")
            else:
                tot = sum(size(g) for g in r[0]) + size(r[1])
                txt = ", ".join(show(g) for g in r[0]) + f" ⊨ {show(r[1])}"
                rows.append((n1, n2, tot, txt, f"rule/arity {ar}"))
                print(f"  {n1 + ' | ' + n2:40s}{tot:>6d}   "
                      f"{txt}  (rule, arity {ar})")

    print(f"\n{'=' * 78}\nWHAT THE RECEIPTS SAY\n{'=' * 78}")
    laws = [r for r in rows if r[4] == "law"]
    rules = [r for r in rows if r[4].startswith("rule")]
    print(f"  separated by a LAW              : {len(laws)}")
    print(f"  separated only by a RULE        : {len(rules)}")
    for r in rules:
        print(f"      {r[0]} | {r[1]}  —  {r[3]}  ({r[4]})")
    print(f"  no separator found in this range: {len(unresolved)}")

    if rows:
        cheapest = min(rows, key=lambda r: r[2])
        dearest = max(rows, key=lambda r: r[2])
        print(f"\n  cheapest apartness : {cheapest[0]} | {cheapest[1]} "
              f"at size {cheapest[2]} — {cheapest[3]}")
        print(f"  dearest apartness  : {dearest[0]} | {dearest[1]} "
              f"at size {dearest[2]} — {dearest[3]}")

    print("\n  A pair separated only by a rule is the interesting kind: the")
    print("  two grounds agree on every law we can write at this size and")
    print("  still transport differently. Laws are what a ground SAYS;")
    print("  rules are what it DOES. The receipt can be issued by either,")
    print("  and which one issues it is itself information.")

    print(f"\n{'=' * 78}\nCLAIM CEILING\n{'=' * 78}")
    print("  Every 'no separator found' is exactly that — not a proof that")
    print("  two grounds coincide. Sameness of grounds is not witnessable;")
    print("  that is the point of the tack, not a limitation of the sweep.")
    print("  This work retracted a prediction earlier today for forgetting")
    print("  it (Ł3 read gap 0 on a shallow pool and does not have the")
    print("  deduction theorem). A zero is the absence of a counterexample")
    print("  we could reach.")

    assert not unresolved, \
        f"pairs with no separator: {unresolved} — widen the range or say so"
    print("\n  TACK 2c GREEN — every pair carries a receipt.")
