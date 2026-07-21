# -*- coding: utf-8 -*-
"""
ztl_signature — what makes ZTL ZTL among the three-valued matrices: it
cannot express them, and one rule of size 3 separates it from all of them.

Two structural facts, both measured and both backed by a theorem the
corpus already proves.

PART A — EXPRESSIBILITY. Can the neighbour logics be expressed FROM ZTL,
i.e. are their connectives definable as ZTL formulas? No, and the reason
is greediness (evalF_classical, lean/ZTL.lean, empty axiom list): every
COMPOUND ZTL formula is classical — it returns T or F on any input, never
the mark. The mark evaporates at the first operator. But K3, LP, weak
Kleene and Łukasiewicz all have connectives that RETURN the third value
on some input. A function that outputs the third value cannot be built
from operators that never do. So none of the three-valued neighbours is
expressible from ZTL — not for want of trying, but by a theorem.

The boundary is exact: ZTL is expressively complete for functions with
CLASSICAL output (V → {T,F}) — the whole external layer, the detectors,
isZ — and expresses NOTHING that carries the mark onward. It speaks only
in verdicts, which is why it cannot pronounce a logic that keeps
not-knowing inside a compound.

(MO2 is inexpressible for a different reason — six carrier elements, not
three, a different language. IPC has no finite characteristic matrix at
all, Gödel 1932, so there is nothing to express.)

PART B — THE ONE RULE. ZTL's consequence relation is incomparable with
every three-valued neighbour (ztl_vs_k3.py has the K3 pair in full). The
"neighbour ⊢ but ZTL ⊬" witness is the SAME for all four:

    ¬¬p ⊨ p

Every neighbour keeps double-negation elimination as a rule; ZTL alone
breaks it, because ¬¬Z = T ≠ Z — the broken involution. So one rule of
size 3 witnesses ZTL's separation-from-below against the entire family.
The other direction ("ZTL ⊢ but neighbour ⊬") varies by neighbour and
names that neighbour's own defect — LP's rejected explosion, weak
Kleene's infectious ∨, Ł3's arrow.

PRE-REGISTERED, and honestly recorded: I predicted the ZTL-side witness
would be a guarded tautology uniformly. Wrong — it varies. The uniform
witness is on the OTHER side, ¬¬p ⊨ p, and that is the sharper finding:
the broken involution is the single consequence-level feature separating
ZTL from all four neighbours.

Run:  python3 pssl/ztl_signature.py
"""
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, _HERE)

import zipc                                                   # noqa: E402
import grounds as G                                           # noqa: E402
import family as Fm                                           # noqa: E402
from ztl import VALUES, NOT, AND, OR, IMP, XOR, XNOR           # noqa: E402

ZTL = [d for n, _, v, d in G.GROUNDS if n == "ZTL"][0]
ZTLv = [v for n, _, v, d in G.GROUNDS if n == "ZTL"][0]


def show(x):
    if isinstance(x, str):
        return x
    if x[0] == "not":
        return f"¬{show(x[1])}"
    return (f"({show(x[1])}"
            + {"and": "∧", "or": "∨", "imp": "→"}[x[0]] + f"{show(x[2])})")


def size(x):
    return len(show(x))


DNE = (("not", ("not", "p")), "p")     # ¬¬p ⊨ p


if __name__ == "__main__":
    print("=" * 76)
    print("ZTL's SIGNATURE among the three-valued matrices")
    print("=" * 76)

    # ---------------------------------------------------------- PART A
    print("\n### A. Expressibility — can the neighbours be built FROM ZTL?")
    zoutputs = set()
    for a in VALUES:
        zoutputs.add(NOT(a))
        for b in VALUES:
            for op in (AND, OR, IMP, XOR, XNOR):
                zoutputs.add(op(a, b))
    print(f"    outputs of EVERY ZTL operator: {sorted(zoutputs)}"
          f"  — the mark {'appears' if 'Z' in zoutputs else 'NEVER appears'}")
    print("    (greediness / evalF_classical: every compound is classical)\n")
    for m in Fm.FAMILY:
        thirds = []
        if any(m.neg(a) == "u" for a in ("1", "u", "0")):
            thirds.append("¬")
        for op, nm in ((m.conj, "∧"), (m.disj, "∨"), (m.imp, "→")):
            if any(op(a, b) == "u" for a in ("1", "u", "0")
                   for b in ("1", "u", "0")):
                thirds.append(nm)
        print(f"    {m.name:16s} returns the third value on {thirds}"
              f"  → NOT expressible from ZTL")
    assert "Z" not in zoutputs, "a ZTL operator returned the mark"
    print("\n    Boundary: ZTL expresses every function with CLASSICAL output")
    print("    (V→{T,F}) and nothing that carries the mark. It speaks only")
    print("    in verdicts, so it cannot pronounce a mark-carrying logic.")

    # ---------------------------------------------------------- PART B
    print("\n### B. One rule separates ZTL from all four, from below")
    pool = zipc.build_pool(("p", "q"), depth=2)
    print(f"    {'neighbour':16s}{'relation':14s}  ¬¬p⊨p in ZTL / in it")
    z_dne = ZTL([DNE[0]], DNE[1])
    all_incomp = True
    uniform = True
    for m in Fm.FAMILY:
        z_only = k_only = 0
        zmin = kmin = None
        for g in pool:
            for f in pool:
                z, k = ZTL([g], f), m.derives([g], f)
                if z and not k:
                    z_only += 1
                    if zmin is None or size(g) + size(f) < size(zmin[0]) + size(zmin[1]):
                        zmin = (g, f)
                if k and not z:
                    k_only += 1
                    if kmin is None or size(g) + size(f) < size(kmin[0]) + size(kmin[1]):
                        kmin = (g, f)
        rel = ("incomparable" if z_only and k_only
               else "ZTL ⊋" if not k_only else "⊋ ZTL" if not z_only else "=")
        m_dne = m.derives([DNE[0]], DNE[1])
        all_incomp = all_incomp and (z_only and k_only)
        # is the neighbour's minimal "it can, ZTL can't" witness exactly ¬¬p⊨p?
        is_dne = kmin == DNE
        uniform = uniform and is_dne
        print(f"    {m.name:16s}{rel:14s}  {z_dne} / {m_dne}"
              f"   min witness (it\\ZTL): {show(kmin[0])}⊨{show(kmin[1])}")
    print(f"\n    ¬¬p ⊨ p : broken in ZTL ({z_dne}), kept by every neighbour.")
    print("    It is the minimal 'neighbour can, ZTL cannot' witness for all")
    print(f"    four — the SAME rule, size 3. uniform: {uniform}")
    assert all_incomp, "ZTL is not incomparable with some neighbour"
    assert not z_dne, "ZTL started proving ¬¬p ⊨ p — the involution returned"
    assert uniform, "the uniform ¬¬p⊨p witness broke for some neighbour"
    # the general lemma covers a neighbour iff its ¬ is involutive — check
    inv_all = all(all(m.neg(m.neg(x)) == x for x in ("1", "u", "0"))
                  for m in Fm.FAMILY)
    print(f"\n    every neighbour's ¬ is involutive: {inv_all}"
          "  → involution_gives_dne (Lean) covers all four")
    assert inv_all, "a neighbour has non-involutive ¬ — the lemma misses it"

    print("\n" + "=" * 76)
    print("THE SIGNATURE, IN ONE LINE")
    print("=" * 76)
    print("  Among three-valued matrices ZTL is the unique member that")
    print("  breaks ¬¬p ⊨ p, and that single rule witnesses its separation")
    print("  from every neighbour below; above, each neighbour is separated")
    print("  by its own defect. And ZTL cannot express any of them, because")
    print("  greediness forbids a compound from ever carrying the mark.")
    print("  Both facts are the same feature seen twice: ZTL speaks only in")
    print("  verdicts, so it neither keeps the involution nor utters a logic")
    print("  that does.")
    print("\n  NOW PROVED IN LEAN (lean/Signature.lean, empty axiom list):")
    print("  the WHY is a theorem, not a measurement. involution_gives_dne —")
    print("  any involutive negation forces ¬¬p ⊨ p, so every neighbour")
    print("  keeps it by ONE general lemma; ztl_not_involutive + ztl_breaks_dne")
    print("  — ZTL's ¬¬Z = T breaks the involution and the rule with it.")
    print("  The four neighbours' involutivity is confirmed here in Python;")
    print("  the structural reason is the Lean theorem.")
    print("\n  CEILING: consequence measured on the depth-2 pool (witnesses")
    print("  exhibited, so underivability is settled); the CAUSE (involution")
    print("  ⟹ DNE, and ZTL breaking it) is now Lean, exact and not pool-bounded.")
    print("\n  SIGNATURE GREEN")
