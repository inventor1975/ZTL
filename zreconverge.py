# -*- coding: utf-8 -*-
"""
Expedition E61: RECONVERGENCE IS THE MEET — no shared unresolved ancestor changes
eligibility (T2 of the 2026-09-06 roadmap, answered in the negative).

`RelianceBridge`: bundle [] = ⊤, bundle [φ] = φ, bundle (φ::ψ::r) = φ ∧ bundle (ψ::r);
verdict m Γ = evalF m (bundle Γ); eligible ⟺ verdict = T. Recombining two
branches is appending their bundles. `lean/ZReconverge.lean` proves on the empty
axiom list that verdict (Γ₁ ++ Γ₂) = zand (verdict Γ₁) (verdict Γ₂) and hence
eligible (Γ₁ ++ Γ₂) ⟺ eligible Γ₁ ∧ eligible Γ₂ — for every marking and every
pair of bundles, whatever they share. Measured here with the greedy evaluator.
"""
import itertools
import random
from ztl import T, F, Z, ev

OPS = ("and", "or", "imp", "xor", "xnor")


def bundle(G):
    if not G:
        return None
    if len(G) == 1:
        return G[0]
    return ("and", G[0], bundle(G[1:]))


def verdict(m, G):
    b = bundle(G)
    return T if b is None else ev(b, m)


def zand(x, y):
    return ev(("and", "a", "b"), {"a": x, "b": y})


def pool():
    atoms = ["p", "q"]
    d1 = [("not", a) for a in atoms] + [(op, a, b) for op in OPS for a in atoms for b in atoms]
    return atoms + d1


def check(pairs, markings, label):
    """Verdict = meet is claimed for NON-EMPTY bundles only: bundle [] = ⊤ and
    bundle [φ] = φ bare, so a singleton keeps an atom's Z while zand Z T = F.
    That edge was predicted away and found here first; eligibility never sees it."""
    n = meet_div = edge_div = elig_div = elig_pairs = 0
    for G1, G2 in pairs:
        for m in markings:
            n += 1
            v1, v2, v12 = verdict(m, G1), verdict(m, G2), verdict(m, list(G1) + list(G2))
            if v12 != zand(v1, v2):
                if G1 and G2:
                    meet_div += 1
                else:
                    edge_div += 1
            e1, e2, e12 = v1 == T, v2 == T, v12 == T
            if e12 != (e1 and e2):
                elig_div += 1
            elig_pairs += (e1 and e2)
    print(f"  {label}: {n} (pair, marking) cells; verdict ≠ meet with both non-empty: {meet_div};"
          f" on the empty-bundle edge: {edge_div}; eligibility ≠ conjunction: {elig_div};"
          f" both-eligible cells: {elig_pairs}")
    return meet_div == 0 and elig_div == 0


def main():
    print("=" * 72)
    print("E61. THE VERDICT OF A FAN-IN IS THE MEET; ELIGIBILITY IS THE CONJUNCTION")
    print("=" * 72)
    P = pool()
    markings = [dict(zip(("p", "q"), c)) for c in itertools.product((T, F, Z), repeat=2)]
    b2 = [()] + [(f,) for f in P] + [(f, g) for f in P for g in P]
    b1 = [()] + [(f,) for f in P]
    ok1 = check([(G1, G2) for G1 in b2 for G2 in b1], markings,
                "bundles |Γ₁| ≤ 2 × |Γ₂| ≤ 1 over depth ≤ 1 formulas on p, q")
    rnd = random.Random(61)
    longer = [(tuple(rnd.choice(P) for _ in range(rnd.randint(0, 4))),
               tuple(rnd.choice(P) for _ in range(rnd.randint(0, 4)))) for _ in range(3000)]
    ok2 = check(longer, markings, "3000 random pairs with |Γ| ≤ 4 (seed 61)")
    allZ = {"p": Z, "q": Z}
    once, twice = verdict(allZ, ["p"]), verdict(allZ, ["p", "p"])
    og1, og2 = verdict(allZ, [("not", ("not", "p"))]), verdict(allZ, [("not", ("not", "p")), ("not", ("not", "p"))])
    print(f"  shared unresolved ancestor: [p] → {once}, [p, p] → {twice} — the VERDICT moves, neither eligible")
    print(f"  over-grant: [¬¬p] → {og1}, [¬¬p, ¬¬p] → {og2} — eligible, and recombination neutral")
    ok3 = once == Z and twice == F and og1 == T and og2 == T
    print("\n  Reading: two eligible branches recombine eligibly whatever ancestor they")
    print("  share; sharing shows in the verdict below eligibility, never in eligibility.")
    ok = ok1 and ok2 and ok3
    print("\n" + ("E61 GREEN: verdict = meet on non-empty pairs, eligibility = conjunction on every pair; T2 has no witness"
                  if ok else "E61 RED"))
    return 0 if ok else 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
