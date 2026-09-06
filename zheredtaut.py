# -*- coding: utf-8 -*-
"""
Expedition E57: THERE IS NO STRUCTURAL CRITERION FOR THE HEREDITARY GRADE —
checking it is checking a tautology.

§27 asked, after E33 (fence depth exactly m−1), for "a structural,
non-enumerative criterion" of the hereditary warranty. The answer is a
reduction, proved in `lean/ZHeredTaut.lean` on the empty axiom list and
MEASURED here against the brute-force grade of `zverify.py`:

  guard   G(x⃗) = ∧ᵢ (xᵢ ∨ ¬xᵢ)   — excluded middle as the meter of "verified":
                                     F while any xᵢ is a mark, T once all are;
  witness Φ_ψ = G → ψ              — T at the all-marked start (F → _ = T);
  THEOREM  Hereditary Φ_ψ allZ  ⟺  ψ is a classical tautology.

So a procedure deciding the hereditary grade in polynomial time would decide
TAUT; no structural non-enumerative criterion exists unless P = coNP. What
exists are SUFFICIENT conditions (`NoGift.no_gift`), and E33's fence family is
the case ψ = (a → a): the gap between "sufficient" and "exact" is coNP.

The stand fails in both directions: a divergence between `hereditary_bit`
and tautology-hood on any ψ is red, and so is a witness that is not T at the
start.
"""
import random
from itertools import product
from ztl import T, F, ev
from zverify import hereditary_bit
from zmodal import ztl_eval


def guard(xs):
    g = None
    for x in xs:
        lem = ("or", x, ("not", x))
        g = lem if g is None else ("and", g, lem)
    return g


def witness(psi, xs):
    return ("imp", guard(xs), psi)


def taut(psi, xs):
    return all(ev(psi, dict(zip(xs, vals))) == T for vals in product((T, F), repeat=len(xs)))


def formulas(depth, xs):
    if depth == 0:
        return list(xs)
    sub = formulas(depth - 1, xs)
    out = list(sub)
    out += [("not", a) for a in sub]
    for op in ("and", "or", "imp", "xor", "xnor"):
        out += [(op, a, b) for a in sub for b in sub]
    return out


def check_pool(pool, xs, label):
    allM = {x: "M" for x in xs}
    n = tauts = div = bad_start = 0
    for psi in pool:
        n += 1
        t = taut(psi, xs)
        tauts += t
        w = witness(psi, xs)
        if ztl_eval(w, allM) != T:
            bad_start += 1
        if hereditary_bit(w, allM) != t:
            div += 1
            print(f"  ✗ DIVERGENCE {psi}: tautology {t}, hereditary {not t}")
    print(f"  {label}: {n} formulas, {tauts} tautologies, {n - tauts} non-tautologies;"
          f" witnesses not T at start: {bad_start}; divergences: {div}")
    return div == 0 and bad_start == 0


def main():
    print("=" * 72)
    print("E57. THE HEREDITARY GRADE IS A TAUTOLOGY CHECK: THE REDUCTION, MEASURED")
    print("=" * 72)
    xs2 = ["p", "q"]
    ok1 = check_pool(formulas(2, xs2), xs2, "all formulas of depth ≤ 2 over p, q")
    rnd = random.Random(57)
    xs3 = ["p", "q", "r"]

    def rf(d):
        if d == 0 or rnd.random() < 0.2:
            return rnd.choice(xs3)
        op = rnd.choice(["not", "and", "or", "imp", "xor", "xnor"])
        return ("not", rf(d - 1)) if op == "not" else (op, rf(d - 1), rf(d - 1))
    ok2 = check_pool([rf(3) for _ in range(2000)], xs3, "2000 random formulas of depth ≤ 3 over p, q, r (seed 57)")
    print("\n  Reading: the T verdict of `(p∨¬p)∧(q∨¬q) → ψ` at the all-marked start is")
    print("  hereditary exactly when ψ is a tautology. A structural criterion for")
    print("  heredity would be a structural criterion for TAUT.")
    ok = ok1 and ok2
    print("\n" + ("E57 GREEN: hereditary ⟺ tautology on every formula of both pools"
                  if ok else "E57 RED"))
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
