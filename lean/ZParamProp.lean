/-
  ZParamProp.lean — E46: THE PROPOSITIONAL STEPS, IN THE QUANTIFIED LANGUAGE.

  §27 named exactly this as what the port still lacked: the propositional
  rules carried over to formulas that may contain quantifiers. With them,
  EVERY rule of the calculus preserves satisfiability — the quantifier steps
  in `ZParamTableau`, these here — and closure denies it
  (`ZParamClosure`). The soundness argument is then complete for the whole
  language rather than for its quantifier fragment.

  THE RULES ARE NOT INVENTED HERE. Each is read off a cover lemma of §5 —
  `cover_not_T`, `cover_and_T`, `cover_or_F`, `cover_imp_T`, `cover_imp_F` —
  which state the exact preimage of a sign under a connective. That is why
  the weak signs appear where they do: `F:¬φ` yields P and not F, because
  `¬v = F` holds for v = T AND for v = Z, and a rule that wrote F there
  would be claiming more than the table allows.

  BRANCHING AND NON-BRANCHING ARE DIFFERENT THEOREMS, and the difference is
  the whole point of a tableau. A non-branching step says: the extended
  branch is satisfied. A branching step says: AT LEAST ONE of the successor
  branches is satisfied — which is what makes closure of ALL branches a
  proof.
-/
import ZParamTableau

namespace ZParamProp

open V
open ZParamSyntax
open ZParamTableau

variable {α : Type}

/-! ### Reading a node's value off the branch -/

theorem node_value (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (hb : satBranch I ρ d b) (s : Sign) (φ : QFm)
    (hmem : (s, φ) ∈ b) : ∃ v, Holds I ρ d [] φ v ∧ s v = true := hb _ hmem

/-! ### Non-branching steps -/

/-- **T:¬φ ⟹ F:φ.** By `cover_not_T`: a denial is T exactly on F. -/
theorem step_not_T (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignT, QFm.neg φ) ∈ b) :
    satBranch I ρ d ((SignF, φ) :: b) := by
  intro nd hnd
  cases hnd with
  | head =>
      have ⟨v, hv, hs⟩ := hb _ hmem
      have hvT : v = T := (vT v).mp hs
      have ⟨u, hu, he⟩ := hv
      have : znot u = T := by rw [he]; exact hvT
      exact ⟨u, hu, (vF u).mpr ((cover_not_T u).mp this)⟩
  | tail _ ht => exact hb nd ht

/-- **F:¬φ ⟹ P:φ**, the WEAK sign — because `¬v = F` holds at T and at Z
alike, and claiming F there would exceed the table. -/
theorem step_not_F (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignF, QFm.neg φ) ∈ b) :
    satBranch I ρ d ((SignP, φ) :: b) := by
  intro nd hnd
  cases hnd with
  | head =>
      have ⟨v, hv, hs⟩ := hb _ hmem
      have hvF : v = F := (vF v).mp hs
      have ⟨u, hu, he⟩ := hv
      have : znot u = F := by rw [he]; exact hvF
      exact ⟨u, hu, (vP u).mpr ((cover_not_F u).mp this)⟩
  | tail _ ht => exact hb nd ht

/-- **T:(φ∧ψ) ⟹ T:φ and T:ψ.** -/
theorem step_and_T (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ ψ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignT, QFm.conj φ ψ) ∈ b) :
    satBranch I ρ d ((SignT, φ) :: (SignT, ψ) :: b) := by
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvT : v = T := (vT v).mp hs
  have ⟨a, c, ha, hc, he⟩ := hv
  have hac : zand a c = T := by rw [he]; exact hvT
  have hsplit := (cover_and_T a c).mp hac
  intro nd hnd
  cases hnd with
  | head => exact ⟨a, ha, (vT a).mpr hsplit.1⟩
  | tail _ ht =>
      cases ht with
      | head => exact ⟨c, hc, (vT c).mpr hsplit.2⟩
      | tail _ ht2 => exact hb nd ht2

/-- **F:(φ∨ψ) ⟹ N:φ and N:ψ**, both weak. -/
theorem step_or_F (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ ψ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignF, QFm.disj φ ψ) ∈ b) :
    satBranch I ρ d ((SignN, φ) :: (SignN, ψ) :: b) := by
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvF : v = F := (vF v).mp hs
  have ⟨a, c, ha, hc, he⟩ := hv
  have hac : zor a c = F := by rw [he]; exact hvF
  have hsplit := (cover_or_F a c).mp hac
  intro nd hnd
  cases hnd with
  | head => exact ⟨a, ha, (vN a).mpr hsplit.1⟩
  | tail _ ht =>
      cases ht with
      | head => exact ⟨c, hc, (vN c).mpr hsplit.2⟩
      | tail _ ht2 => exact hb nd ht2

/-- **F:(φ→ψ) ⟹ P:φ and N:ψ.** -/
theorem step_imp_F (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ ψ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignF, QFm.imp φ ψ) ∈ b) :
    satBranch I ρ d ((SignP, φ) :: (SignN, ψ) :: b) := by
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvF : v = F := (vF v).mp hs
  have ⟨a, c, ha, hc, he⟩ := hv
  have hac : zimp a c = F := by rw [he]; exact hvF
  have hsplit := (cover_imp_F a c).mp hac
  intro nd hnd
  cases hnd with
  | head => exact ⟨a, ha, (vP a).mpr hsplit.1⟩
  | tail _ ht =>
      cases ht with
      | head => exact ⟨c, hc, (vN c).mpr hsplit.2⟩
      | tail _ ht2 => exact hb nd ht2

/-! ### Branching steps — AT LEAST ONE successor survives -/

/-- **T:(φ∨ψ) ⟹ T:φ | T:ψ.** -/
theorem step_or_T (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ ψ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignT, QFm.disj φ ψ) ∈ b) :
    satBranch I ρ d ((SignT, φ) :: b) ∨ satBranch I ρ d ((SignT, ψ) :: b) := by
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvT : v = T := (vT v).mp hs
  have ⟨a, c, ha, hc, he⟩ := hv
  have hac : zor a c = T := by rw [he]; exact hvT
  cases (cover_or_T a c).mp hac with
  | inl h =>
      refine Or.inl ?_
      intro nd hnd
      cases hnd with
      | head => exact ⟨a, ha, (vT a).mpr h⟩
      | tail _ ht => exact hb nd ht
  | inr h =>
      refine Or.inr ?_
      intro nd hnd
      cases hnd with
      | head => exact ⟨c, hc, (vT c).mpr h⟩
      | tail _ ht => exact hb nd ht

/-- **T:(φ→ψ) ⟹ F:φ | T:ψ**, the classical shape of the arrow, read off
`cover_imp_T`. -/
theorem step_imp_T (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ ψ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignT, QFm.imp φ ψ) ∈ b) :
    satBranch I ρ d ((SignF, φ) :: b) ∨ satBranch I ρ d ((SignT, ψ) :: b) := by
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvT : v = T := (vT v).mp hs
  have ⟨a, c, ha, hc, he⟩ := hv
  have hac : zimp a c = T := by rw [he]; exact hvT
  cases (cover_imp_T a c).mp hac with
  | inl h =>
      refine Or.inl ?_
      intro nd hnd
      cases hnd with
      | head => exact ⟨a, ha, (vF a).mpr h⟩
      | tail _ ht => exact hb nd ht
  | inr h =>
      refine Or.inr ?_
      intro nd hnd
      cases hnd with
      | head => exact ⟨c, hc, (vT c).mpr h⟩
      | tail _ ht => exact hb nd ht

/-- **F:(φ∧ψ) ⟹ N:φ | N:ψ**, both weak. -/
theorem step_and_F (I : Nat → List α → V) (ρ : Nat → α) (d : α)
    (b : Branch) (φ ψ : QFm) (hb : satBranch I ρ d b)
    (hmem : (SignF, QFm.conj φ ψ) ∈ b) :
    satBranch I ρ d ((SignN, φ) :: b) ∨ satBranch I ρ d ((SignN, ψ) :: b) := by
  have ⟨v, hv, hs⟩ := hb _ hmem
  have hvF : v = F := (vF v).mp hs
  have ⟨a, c, ha, hc, he⟩ := hv
  have hac : zand a c = F := by rw [he]; exact hvF
  cases (cover_and_F a c).mp hac with
  | inl h =>
      refine Or.inl ?_
      intro nd hnd
      cases hnd with
      | head => exact ⟨a, ha, (vN a).mpr h⟩
      | tail _ ht => exact hb nd ht
  | inr h =>
      refine Or.inr ?_
      intro nd hnd
      cases hnd with
      | head => exact ⟨c, hc, (vN c).mpr h⟩
      | tail _ ht => exact hb nd ht

end ZParamProp

#print axioms ZParamProp.step_not_T
#print axioms ZParamProp.step_not_F
#print axioms ZParamProp.step_and_T
#print axioms ZParamProp.step_or_F
#print axioms ZParamProp.step_imp_F
#print axioms ZParamProp.step_or_T
#print axioms ZParamProp.step_imp_T
#print axioms ZParamProp.step_and_F
