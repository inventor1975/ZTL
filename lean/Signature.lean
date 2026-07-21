/-
  Signature.lean — ZTL's separation from the three-valued family is the
  broken involution, proved structurally rather than case by case.

  Measured (pssl/ztl_signature.py): among the three-valued matrices ZTL
  is separated from all four neighbours (K3, LP, weak Kleene,
  Łukasiewicz) by a single rule of size 3 — double-negation elimination
  as a consequence, ¬¬p ⊨ p. Every neighbour keeps it; ZTL alone breaks
  it. This file promotes the WHY to a theorem.

  The reason each neighbour keeps it is not four coincidences: all four
  have an INVOLUTIVE negation (¬¬x = x), and involution forces DNE. ZTL's
  greedy negation is NOT involutive (¬¬Z = T ≠ Z), and that single cell
  is the whole of the failure.

  So the structural statement, on the empty axiom list:

    involution  ⟹  ¬¬p ⊨ p            (general — covers every neighbour)
    ZTL breaks involution              (one cell: ¬¬Z = T)
    ⟹ ZTL breaks ¬¬p ⊨ p               (the signature)

  The general lemma is proved once for an ARBITRARY negation and
  designated predicate, so applying it to any involutive matrix is
  immediate; the four neighbours' involutivity is confirmed in Python
  (they are not encoded here). ZTL is the exhibited witness of the
  converse.

  VR discipline: imports only ZTL (no mathlib); `#print axioms` per
  object, empty list throughout.
-/
import ZTL

namespace Signature

open V

/-- **Involution forces double-negation elimination.** For any type `α`,
any negation `neg : α → α`, and any designated predicate `D`, if `neg` is
involutive then `¬¬p ⊨ p`: whenever `neg (neg x)` is designated, so is
`x`. The proof is that involutivity rewrites the hypothesis into the
goal — DNE-elim is not a lucky feature of the neighbours but a
consequence of keeping the involution. -/
theorem involution_gives_dne {α : Type} (neg : α → α) (D : α → Prop)
    (inv : ∀ x, neg (neg x) = x) :
    ∀ x, D (neg (neg x)) → D x := by
  intro x h
  rw [inv] at h
  exact h

/-- **ZTL's negation is not involutive** — the one cell that does it. -/
theorem ztl_not_involutive : ¬ ∀ x : V, znot (znot x) = x := by decide

/-- The witnessing cell, named: `¬¬Z = T`, while `Z ≠ T`. Double negation
turns the mark into a verdict, so the mark cannot survive it. -/
theorem ztl_dne_witness : znot (znot Z) = T ∧ Z ≠ T := by decide

/-- **ZTL breaks double-negation elimination as a consequence.** There is
a value — the mark — at which `¬¬p` is designated (`= T`) while `p` is
not. This is the signature rule `¬¬p ⊨ p`, failing, and it is exactly
`rule_dn_elim_fails` of `ZTL.lean` re-stated as an existential witness. -/
theorem ztl_breaks_dne : ∃ x : V, znot (znot x) = T ∧ x ≠ T :=
  ⟨Z, by decide⟩

/-- **The signature, assembled.** DNE-elim is forced by involution
(general), and ZTL breaks it because — and exactly because — its negation
is not involutive. The same feature, the greedy `¬¬Z = T`, is what makes
ZTL a logic of verdicts and what separates it from every involutive
neighbour on this one rule. -/
theorem signature :
    (∀ (α : Type) (neg : α → α) (D : α → Prop),
        (∀ x, neg (neg x) = x) → ∀ x, D (neg (neg x)) → D x)
    ∧ (¬ ∀ x : V, znot (znot x) = x)
    ∧ (∃ x : V, znot (znot x) = T ∧ x ≠ T) :=
  ⟨fun _ neg D inv => involution_gives_dne neg D inv,
   ztl_not_involutive, ztl_breaks_dne⟩

#print axioms involution_gives_dne
#print axioms ztl_not_involutive
#print axioms ztl_dne_witness
#print axioms ztl_breaks_dne
#print axioms signature

end Signature
