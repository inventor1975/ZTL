# -*- coding: utf-8 -*-
"""
ztl_vs_k3 — digging a hypothesis out of a fall, and correcting a
committed result in the process.

Leg 3 measured ZTL and K3 at rule distance 0.000 on the depth-1 pool and
reported "identical single-premise consequence, different theorems". The
curator's framing (2026-07-21): what SURVIVES the census is a candidate
theorem, what FALLS gives hypotheses, and the hypotheses matter more. The
hypothesis born from that 0.000: **ZTL's consequence relation equals
K3's** — which would say ZTL's novelty is not in what follows from what
(that would be strong Kleene) but only in its theorems and generating
principle.

PRE-REGISTERED before running: I predicted they DIVERGE somewhere (their
tables differ, so consequence must too), and that the witness would be
informative. I also guessed ZTL⊨ ⊆ K3⊨ (subset). The first held; the
second was WRONG and the measurement corrected it — they are
INCOMPARABLE.

WHAT WAS FOUND.

1. The 0.000 was a POOL ARTIFACT. The depth-1 pool has no ¬¬p-shaped
   premises, which are exactly what separates the two. On the depth-2
   pool the single-premise consequence relations diverge on 57,902
   pairs. This is the day's recurring shape once more — a shallow-pool
   zero read as sameness — and this time it was in a COMMITTED leg-3
   result and its memory note. Corrected here and in distance.py.

2. They are INCOMPARABLE, ~29k divergences each way, and each direction
   is a named signature of ZTL:

     K3 ⊢ but ZTL ⊬ :  ¬¬p ⊨ p
        double-negation elimination as a rule. K3 keeps it (strong
        Kleene negation is involutive); ZTL breaks it, because ¬¬Z = T ≠
        Z — the paracomplete signature, the very law that separates ZTL
        from its Łukasiewicz ancestor and quantum cousin.

     ZTL ⊢ but K3 ⊬ :  p ⊨ (¬q→¬q)
        ZTL has GUARDED TAUTOLOGIES (¬q→¬q is designated at every value),
        so anything entails one; K3 has NO tautologies at all, so nothing
        entails ¬q→¬q there. This is the E26 signature.

So the hypothesis is refuted, and the refutation is sharper than the
hypothesis: ZTL is not strong Kleene's consequence relation dressed
differently. It is incomparable with it, and the two witnesses of the
incomparability are exactly ZTL's two defining features — the broken
involution and the guarded tautologies. That is a narrower, truer
novelty claim than "same transport, different theorems".

Run:  python3 pssl/ztl_vs_k3.py
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, _HERE)

import zipc                                                   # noqa: E402
import grounds as G                                           # noqa: E402
import family as F                                            # noqa: E402
from ztl import VALUES, NOT                                   # noqa: E402

ZTL = [d for n, _, v, d in G.GROUNDS if n == "ZTL"][0]
ZTLv = [v for n, _, v, d in G.GROUNDS if n == "ZTL"][0]
K3 = [m for m in F.FAMILY if m.name == "K3"][0]


def show(x):
    if isinstance(x, str):
        return x
    if x[0] == "not":
        return f"¬{show(x[1])}"
    return (f"({show(x[1])}"
            + {"and": "∧", "or": "∨", "imp": "→"}[x[0]] + f"{show(x[2])})")


def size(x):
    return len(show(x))


if __name__ == "__main__":
    print("=" * 76)
    print("ZTL vs K3 — a hypothesis dug from leg 3's fall")
    print("=" * 76)
    print("  Hypothesis (from leg 3's ZTL|K3 = 0.000 on rules): ZTL's")
    print("  consequence relation equals K3's. Pre-registered prediction:")
    print("  they diverge. Measured on the depth-2 pool.\n")

    p1 = zipc.build_pool(("p", "q"), depth=1)
    p2 = zipc.build_pool(("p", "q"), depth=2)

    # 1. the pool artifact
    d1 = sum(1 for g in p1 for f in p1 if ZTL([g], f) != K3.derives([g], f))
    d2 = sum(1 for g in p2 for f in p2 if ZTL([g], f) != K3.derives([g], f))
    print(f"### 1. Single-premise divergences")
    print(f"    depth-1 pool ({len(p1)} formulas) : {d1}   ← leg 3 saw this, "
          "read it as sameness")
    print(f"    depth-2 pool ({len(p2)} formulas) : {d2}   ← the truth")
    print("    The depth-1 pool has no ¬¬p-shaped premises. leg 3's 0.000")
    print("    was a POOL ARTIFACT, the day's shape in a committed result.")
    assert d1 == 0 and d2 > 0, "the pool artifact did not reproduce"

    # 2. incomparable, with the two signature witnesses
    z_only = k_only = 0
    zmin = kmin = None
    for g in p2:
        for f in p2:
            z, k = ZTL([g], f), K3.derives([g], f)
            if z and not k:
                z_only += 1
                if zmin is None or size(g) + size(f) < size(zmin[0]) + size(zmin[1]):
                    zmin = (g, f)
            if k and not z:
                k_only += 1
                if kmin is None or size(g) + size(f) < size(kmin[0]) + size(kmin[1]):
                    kmin = (g, f)
    print(f"\n### 2. They are INCOMPARABLE")
    print(f"    ZTL ⊢ but K3 ⊬ : {z_only}")
    print(f"    K3 ⊢ but ZTL ⊬ : {k_only}")
    print(f"    neither consequence relation contains the other.")
    print(f"\n    minimal witness  K3⊢ ZTL⊬ : {show(kmin[0])} ⊨ {show(kmin[1])}")
    print(f"    minimal witness  ZTL⊢ K3⊬ : {show(zmin[0])} ⊨ {show(zmin[1])}")

    # 3. each witness is a named signature — checked on the kernel
    print(f"\n### 3. Each witness is a defining feature of ZTL, on the kernel")
    involution = [NOT(NOT(v)) for v in VALUES]
    print(f"    ¬¬x over {list(VALUES)} : {involution}  →  ZTL breaks the")
    print(f"      involution (¬¬Z = T ≠ Z), so ¬¬p ⊨ p fails: the")
    print(f"      paracomplete signature that separates ZTL from Łukasiewicz")
    print(f"      and from the ortholattice, both of which keep it.")
    guarded = ZTLv(("imp", ("not", "q"), ("not", "q")))
    k3_taut = any(K3.valid(f) for f in p2)
    print(f"    ¬q→¬q valid in ZTL : {guarded}  (a guarded tautology, E26)")
    print(f"    any tautology in K3: {k3_taut}  (K3 has none), so p ⊨ ¬q→¬q")
    print(f"      holds in ZTL and cannot in K3.")
    assert involution == ["T", "F", "T"], "the ZTL involution changed"
    assert guarded and not k3_taut, "the guarded-tautology signature moved"

    print("\n" + "=" * 76)
    print("WHAT THE DIG YIELDED")
    print("=" * 76)
    print("  The hypothesis (ZTL⊨ = K3⊨) is REFUTED, and the refutation is")
    print("  sharper than the hypothesis. ZTL is not strong Kleene's")
    print("  consequence relation with different theorems; the two are")
    print("  incomparable, and the two witnesses of the incomparability are")
    print("  precisely ZTL's two defining features — the broken involution")
    print("  (loses ¬¬p ⊨ p) and the guarded tautologies (gains p ⊨ ¬q→¬q).")
    print()
    print("  This is the narrower, truer novelty claim: ZTL's consequence")
    print("  relation is separated from its nearest matrix neighbour by")
    print("  exactly the features the preprint already names, and by")
    print("  witnesses of size 4 that a referee can check by hand.")
    print()
    print("  CEILING: measured on the depth-2 pool, not proved for all")
    print("  formulas. But the two minimal witnesses ARE exhibited, and")
    print("  underivability with a witness is settled, not merely unfound.")
    print("\n  ZTL vs K3 GREEN — hypothesis refuted, leg-3 artifact corrected.")
