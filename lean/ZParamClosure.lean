/-
  ZParamClosure.lean — E45: A CLOSED BRANCH HAS NO MODEL.

  The step that turns preserved satisfiability into a proof. A tableau is
  sound because every rule preserves satisfiability and a CLOSED branch has
  none; contraposition does the rest. The steps were proved in
  `ZParamTableau`; here is the other half.

  AND IT NEEDS A LEMMA THAT IS NOT OBVIOUS WHEN SATISFACTION IS A RELATION.
  A closed branch carries two nodes about the SAME formula whose signs cannot
  both be met. To get a contradiction one must know the formula has ONE
  value — and with `Holds` written as a relation rather than a function, that
  is a theorem, not a definition.

  DETERMINISM IS PROVED CONSTRUCTIVELY, and the quantifier case is where it
  could have gone wrong. For `∀`, the specification says the value is T
  exactly when every instance is T, and is T or F. Two values v and w both
  satisfying that could differ only if one is T and the other F — and then
  the T one forces the universal, which forces the other to T as well. No
  case analysis on the undecidable universal is required; the two
  specifications are played against each other instead.

  WHAT THIS COMPLETES AND WHAT IT DOES NOT. With this, the soundness argument
  for the quantified calculus is complete in its parts: steps preserve
  satisfiability, closure denies it. What is still absent is the SEARCH — the
  fuel-bounded procedure that applies the steps and reports closure — and
  therefore the end-to-end theorem about a whole tableau run. That is
  engineering on top of these theorems rather than another argument, but it
  is not written, and this file does not pretend otherwise.
-/
import ZParamTableau

namespace ZParamClosure

open V
open ZParamSyntax
open ZParamTableau

variable {α : Type}

/-! ### One formula, one value -/

theorem holds_det (I : Nat → List α → V) (ρ : Nat → α) (d : α) :
    ∀ (φ : QFm) (η : List α) (v w : V),
      Holds I ρ d η φ v → Holds I ρ d η φ w → v = w
  | QFm.atom P ts, η, v, w, hv, hw => by
      show v = w
      have h1 : I P (trmVals ρ η d ts) = v := hv
      have h2 : I P (trmVals ρ η d ts) = w := hw
      rw [← h1, ← h2]
  | QFm.neg φ, η, v, w, hv, hw => by
      have ⟨u1, h1, e1⟩ := hv
      have ⟨u2, h2, e2⟩ := hw
      rw [← e1, ← e2, holds_det I ρ d φ η u1 u2 h1 h2]
  | QFm.conj φ ψ, η, v, w, hv, hw => by
      have ⟨a1, b1, ha1, hb1, e1⟩ := hv
      have ⟨a2, b2, ha2, hb2, e2⟩ := hw
      rw [← e1, ← e2, holds_det I ρ d φ η a1 a2 ha1 ha2,
          holds_det I ρ d ψ η b1 b2 hb1 hb2]
  | QFm.disj φ ψ, η, v, w, hv, hw => by
      have ⟨a1, b1, ha1, hb1, e1⟩ := hv
      have ⟨a2, b2, ha2, hb2, e2⟩ := hw
      rw [← e1, ← e2, holds_det I ρ d φ η a1 a2 ha1 ha2,
          holds_det I ρ d ψ η b1 b2 hb1 hb2]
  | QFm.imp φ ψ, η, v, w, hv, hw => by
      have ⟨a1, b1, ha1, hb1, e1⟩ := hv
      have ⟨a2, b2, ha2, hb2, e2⟩ := hw
      rw [← e1, ← e2, holds_det I ρ d φ η a1 a2 ha1 ha2,
          holds_det I ρ d ψ η b1 b2 hb1 hb2]
  | QFm.all φ, η, v, w, hv, hw => by
      have ⟨i1, c1⟩ := hv
      have ⟨i2, c2⟩ := hw
      cases c1 with
      | inl h1 =>
          cases c2 with
          | inl h2 => rw [h1, h2]
          | inr h2 => exact absurd (i2.mpr (i1.mp h1)) (by rw [h2]; intro h; cases h)
      | inr h1 =>
          cases c2 with
          | inl h2 => exact absurd (i1.mpr (i2.mp h2)) (by rw [h1]; intro h; cases h)
          | inr h2 => rw [h1, h2]
  | QFm.ex φ, η, v, w, hv, hw => by
      have ⟨i1, c1⟩ := hv
      have ⟨i2, c2⟩ := hw
      cases c1 with
      | inl h1 =>
          cases c2 with
          | inl h2 => rw [h1, h2]
          | inr h2 => exact absurd (i2.mpr (i1.mp h1)) (by rw [h2]; intro h; cases h)
      | inr h1 =>
          cases c2 with
          | inl h2 => exact absurd (i1.mpr (i2.mp h2)) (by rw [h1]; intro h; cases h)
          | inr h2 => rw [h1, h2]

/-! ### Closure -/

/-- Two signs clash when no value meets both. -/
def clash (s t : Sign) : Prop := ∀ v : V, ¬(s v = true ∧ t v = true)

/-- A branch is closed when it carries two clashing signs on one formula. -/
def Closed (b : Branch) : Prop :=
  ∃ (s t : Sign) (φ : QFm), (s, φ) ∈ b ∧ (t, φ) ∈ b ∧ clash s t

/-- **A CLOSED BRANCH HAS NO MODEL.** With the steps of `ZParamTableau` this
is the whole soundness argument: satisfiability is carried forward by every
rule and denied at closure. -/
theorem closed_unsat (I : Nat → List α → V) (ρ : Nat → α) (d : α) (b : Branch)
    (hc : Closed b) : ¬ satBranch I ρ d b := by
  intro hb
  have ⟨s, t, φ, hs, ht, hcl⟩ := hc
  have ⟨v, hv, hsv⟩ := hb (s, φ) hs
  have ⟨w, hw, htw⟩ := hb (t, φ) ht
  have : v = w := holds_det I ρ d φ [] v w hv hw
  rw [this] at hsv
  exact hcl w ⟨hsv, htw⟩

/-- The signs of §5 clash as they should: T against F, T against N. -/
theorem clash_T_F : clash SignT SignF := by
  intro v ⟨h1, h2⟩
  rw [(vT v).mp h1] at h2
  exact Bool.noConfusion h2

theorem clash_T_N : clash SignT SignN := by
  intro v ⟨h1, h2⟩
  have hT : v = T := (vT v).mp h1
  have : ¬(v = T) := (vN_neq v).mp ((vN v).mp h2)
  exact this hT

end ZParamClosure

#print axioms ZParamClosure.holds_det
#print axioms ZParamClosure.closed_unsat
#print axioms ZParamClosure.clash_T_F
#print axioms ZParamClosure.clash_T_N
