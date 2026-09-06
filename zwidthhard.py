# -*- coding: utf-8 -*-
"""
Expedition E58: THE WIDTH OF AN INQUIRY IS NP-HARD TO KNOW.

§19's width: the smallest number of unverified grounds whose JOINT filling
moves the greedy verdict; None if nothing moves it (= the hereditary grade).
The judge reports width 1 (`joint`) and does not compute the exact width.
`lean/ZWidthHard.lean` proves, on the empty axiom list, that on E57's witness
`(∧ᵢ xᵢ∨¬xᵢ) → ψ` at the all-marked start

    nothing short of the whole guard moves the verdict     (no_move_below)
    the whole guard moves it  ⟺  ψ has a falsifying point (width_iff_refutable)

so the width is n+1 exactly when ¬ψ is satisfiable and undefined otherwise:
"width ≤ k" is NP-complete, and the judge's cut — width 1 cheap, exact width
not — is forced. Measured here with the instrument's own `width` (copied
verbatim from inventory/width/bench.py, which has no import guard).
"""
import itertools
import random
from ztl import T, F, Z, ev
from zheredtaut import witness, taut, formulas


def width(phi, m, atoms):
    """Smallest number of unverified grounds whose JOINT filling moves the
    verdict. Returns None if no subset moves it at all.
    (inventory/width/bench.py, verbatim.)"""
    marks = [a for a in atoms if m[a] == Z]
    base = ev(phi, m)
    for k in range(1, len(marks) + 1):
        for S in itertools.combinations(marks, k):
            for vals in itertools.product((T, F), repeat=k):
                m2 = dict(m)
                m2.update(dict(zip(S, vals)))
                if ev(phi, m2) != base:
                    return k
    return None


def check_pool(pool, xs, label):
    allZ = {x: Z for x in xs}
    dist = {}
    div = 0
    for psi in pool:
        w = width(witness(psi, xs), allZ, xs)
        t = taut(psi, xs)
        dist[w] = dist.get(w, 0) + 1
        if w != (None if t else len(xs)):
            div += 1
            print(f"  ✗ DIVERGENCE {psi}: tautology {t}, width {w}")
    shown = {str(k): v for k, v in sorted(dist.items(), key=lambda kv: (kv[0] is None, kv[0] or 0))}
    print(f"  {label}: {len(pool)} formulas; width distribution {shown}; divergences {div}")
    return div == 0


def main():
    print("=" * 72)
    print("E58. WIDTH IS ALL OR NOTHING ON THE WITNESS: n+1 IFF ¬ψ IS SATISFIABLE")
    print("=" * 72)
    xs2 = ["p", "q"]
    ok1 = check_pool(formulas(2, xs2), xs2, "all formulas of depth ≤ 2 over p, q (guard of 2)")
    rnd = random.Random(58)
    xs3 = ["p", "q", "r"]

    def rf(d):
        if d == 0 or rnd.random() < 0.2:
            return rnd.choice(xs3)
        op = rnd.choice(["not", "and", "or", "imp", "xor", "xnor"])
        return ("not", rf(d - 1)) if op == "not" else (op, rf(d - 1), rf(d - 1))
    ok2 = check_pool([rf(3) for _ in range(600)], xs3, "600 random formulas of depth ≤ 3 over p, q, r (guard of 3, seed 58)")
    print("\n  Reading: no set smaller than the whole guard ever moves the verdict, and the")
    print("  whole guard moves it exactly when ψ can fail. Width ≤ k decides SAT.")
    ok = ok1 and ok2
    print("\n" + ("E58 GREEN: width is n+1 or None on every witness, split exactly by tautology-hood"
                  if ok else "E58 RED"))
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
