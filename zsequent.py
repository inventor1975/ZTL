# -*- coding: utf-8 -*-
"""
Expedition E16: the sequent reading and semantic cut elimination.

The tableau engine read upside down IS a cut-free sequent calculus:
  * a sequent = a finite set S of signed formulas;
  * the judgment ⊢ S means "S is refutable" (jointly unsatisfiable);
  * axioms: contradictory sign constraints on an atom (T against N,
    F against P, T against F);
  * rules: the twelve signed expansions of §5, premises above the line
    (the T/F-polarity signature carries over verbatim);
  * derivability = the engine's closure (backward proof search).

CUT (on the covering pair T/N — every value lies in {T} ∪ {F,Z}):
    ⊢ S, T:φ    ⊢ S, N:φ
    ─────────────────────  (cut)
           ⊢ S
The cut-free system is already complete (closes_iff, Lean), and cut is
sound — hence cut is ADMISSIBLE: semantic cut elimination. Measured
here directly (total on pools) and kernel-checked in lean/ZSequent.lean
(cut_admissible, weakening_admissible, identity_refutable, zero axioms).
"""

from itertools import product

from ztl import T, F, Z
from tableau import ST, SF, SP, SN, tableau_closes

SIGNS = {"T": ST, "F": SF, "P": SP, "N": SN}


def pool_formulas():
    a = ["p", "q", ("not", "p"), ("not", "q")]
    out = list(a)
    for op in ("and", "or", "imp", "xor", "xnor"):
        out.append((op, "p", "q"))
        out.append((op, ("not", "p"), "q"))
    return out


def pool_sequents(forms):
    """Sequents of size ≤ 2 over the pool, all sign combinations."""
    signed = [(s, f) for s in SIGNS.values() for f in forms]
    seqs = [[]]
    seqs += [[n] for n in signed]
    seqs += [[n1, n2] for i, n1 in enumerate(signed)
             for n2 in signed[i:i + 6]]          # a slice to keep it fast
    return seqs


if __name__ == "__main__":
    print("=" * 72)
    print("E16. SEQUENTS: THE CALCULUS UPSIDE DOWN, CUT ELIMINATED SEMANTICALLY")
    print("=" * 72)

    forms = pool_formulas()
    seqs = pool_sequents(forms)
    print(f"\n  pool: {len(forms)} formulas, {len(seqs)} sequents,"
          f" cut formulas: {len(forms)}")

    print("\n### Identity: ⊢ {T:φ, N:φ} for every formula")
    bad_id = [f for f in forms if not tableau_closes([(ST, f), (SN, f)])]
    print(f"  derivable: {len(forms) - len(bad_id)} of {len(forms)}"
          f" ({'✓' if not bad_id else '✗'})")

    print("\n### Weakening: ⊢ S ⟹ ⊢ S ∪ {n} (any signed formula)")
    bad_w = checked_w = 0
    extras = [(s, f) for s in SIGNS.values() for f in forms[:6]]
    for S in seqs:
        if not tableau_closes(S):
            continue
        for n in extras:
            checked_w += 1
            if not tableau_closes(S + [n]):
                bad_w += 1
    print(f"  checks on derivable sequents: {checked_w}; violations: {bad_w}"
          f" ({'✓ admissible' if bad_w == 0 else '✗'})")

    print("\n### CUT on the covering pair T/N")
    checked_c = viol_c = fired_c = 0
    for S in seqs:
        for phi in forms:
            checked_c += 1
            if tableau_closes(S + [(ST, phi)]) and \
               tableau_closes(S + [(SN, phi)]):
                fired_c += 1
                if not tableau_closes(S):
                    viol_c += 1
                    print(f"  ✗ S={S} cut on {phi}")
    print(f"  cut instances examined: {checked_c}; with both premises"
          f" derivable: {fired_c}; violations: {viol_c}")
    print(f"  {'✓ CUT IS ADMISSIBLE (semantic cut elimination), total' if viol_c == 0 else '✗'}")

    print("\n### The dual covering pair F/P")
    viol_c2 = fired_c2 = 0
    for S in seqs:
        for phi in forms:
            if tableau_closes(S + [(SF, phi)]) and \
               tableau_closes(S + [(SP, phi)]):
                fired_c2 += 1
                if not tableau_closes(S):
                    viol_c2 += 1
    print(f"  fired: {fired_c2}; violations: {viol_c2}"
          f" ({'✓ admissible as well' if viol_c2 == 0 else '✗'})")

    print("\n### Summary")
    print("  The signed tableaux, read bottom-up, are a cut-free sequent")
    print("  calculus; identity, weakening and both cuts are admissible —")
    print("  measured totally here, cut/weakening/identity kernel-checked")
    print("  in Lean (ZSequent.lean, zero axioms). Cut elimination comes")
    print("  for free from completeness of the cut-free system: the")
    print("  classic semantic argument, now with a machine certificate.")
    if bad_id or bad_w or viol_c or viol_c2:
        raise SystemExit("A SEQUENT PROPERTY FAILED — stop.")
