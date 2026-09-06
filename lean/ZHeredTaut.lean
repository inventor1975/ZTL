/-
  ZHeredTaut.lean — E57: THERE IS NO STRUCTURAL CRITERION FOR THE HEREDITARY
  GRADE — CHECKING IT IS CHECKING A TAUTOLOGY.

  §27 leaves one question open after E33: the fence depth is exactly m−1, so
  no constant-depth check certifies the hereditary grade — "what remains
  open is a structural, non-enumerative criterion". This file answers it
  with a reduction, on the empty axiom list.

  THE GUARD. Excluded middle, `x ∨ ¬x`, is not a law in ZTL: at a mark it
  reads `Z ∨ ¬Z = Z ∨ F = F`, and on any verified value it reads T. So the
  conjunction `G_N = ∧_{i<N} (xᵢ ∨ ¬xᵢ)` is a METER: F while any of the first
  N atoms is unverified, T once all are. The fallen law becomes the
  instrument that says "everything has been checked".

  THE WITNESS. For a classical formula ψ over atoms below N, put
  `Φ_ψ = G_N → ψ`. At the all-marked start, `G_N = F` and `F → _ = T`: the
  verdict is T. Under any refinement that leaves one guarded atom marked the
  guard stays F and the verdict stays T. Under a refinement that verifies
  them all, `Φ_ψ` reads `T → ψ = ψ` at that classical point. So the T
  verdict is HEREDITARY exactly when ψ is true at every classical point —
  exactly when ψ is a tautology (`hereditary_iff_taut`).

  WHAT FOLLOWS, in prose since complexity classes are not formalised here:
  the witness has the size of ψ plus N, so any procedure deciding the
  hereditary grade in time polynomial in the formula decides TAUT; a
  structural, non-enumerative criterion would put coNP in P. The grade is
  coNP-HARD — that is the claim, and the reduction `hereditary_iff_taut`
  is its whole content. Membership in coNP — a refinement that revokes the
  verdict would be a certificate, checked in one greedy pass — is an
  argument in prose that nothing here formalises; it is not claimed, so
  "coNP-complete" is not said (the first version of this header said it;
  one grade above the evidence). What exists are SUFFICIENT structural
  conditions — `NoGift.no_gift`, no mark under a negation — and the
  reduction says no exact one can be cheap.

  This is E33's fence family read the other way: the guard family
  `(b₁ ∧ … ∧ b_{m−1}) → (a → a)` showed the depth; the same shape with `ψ` in
  the gap shows the hardness.

  FORM. Over `ZTime` (own `V`, no tactic instances): three-valued facts by
  explicit `cases`; a bounded search `hasMark` decides "some guarded atom is
  still marked" so that no `Classical.em` is needed; `dependsOn`,
  `evalF_congr_dep` and `close` reused from `ZFenceDepth`.
-/
import ZFenceDepth

namespace ZHeredTaut

open ZTime
open ZTime.V
open ZFenceDepth

/-! ### Three-valued facts -/

theorem lem_Z : zor V.Z (znot V.Z) = V.F := rfl
theorem lem_grounded : ∀ x : V, x ≠ V.Z → zor x (znot x) = V.T := by
  intro x hx
  cases x with
  | T => rfl
  | F => rfl
  | Z => exact absurd rfl hx
theorem and_F_left : ∀ x : V, zand V.F x = V.F := by intro x; cases x <;> rfl
theorem imp_T_left : ∀ x : V, x ≠ V.Z → zimp V.T x = x := by
  intro x hx
  cases x with
  | T => rfl
  | F => rfl
  | Z => exact absurd rfl hx

/-- A compound never reads Z: the lifts answer T or F. -/
theorem lift1_ne_Z (f : Bool → Bool) (x : V) : lift1 f x ≠ V.Z := by
  unfold lift1
  split <;> intro h <;> cases h
theorem lift2_ne_Z (f : Bool → Bool → Bool) (x y : V) : lift2 f x y ≠ V.Z := by
  unfold lift2
  split <;> intro h <;> cases h

/-- On a marking without marks, no formula reads Z. -/
theorem evalF_ne_Z (c : Marking) (hc : ∀ n, c n ≠ V.Z) : ∀ φ : Fm, evalF c φ ≠ V.Z
  | Fm.atom n => hc n
  | Fm.top => fun h => V.noConfusion h
  | Fm.bot => fun h => V.noConfusion h
  | Fm.neg φ => lift1_ne_Z _ _
  | Fm.conj φ ψ => lift2_ne_Z _ _ _
  | Fm.disj φ ψ => lift2_ne_Z _ _ _
  | Fm.imp φ ψ => lift2_ne_Z _ _ _
  | Fm.xor φ ψ => lift2_ne_Z _ _ _
  | Fm.xnor φ ψ => lift2_ne_Z _ _ _

/-! ### The guard and the witness -/

/-- Excluded middle at one atom: the meter of "verified". -/
def lemAt (i : Nat) : Fm := Fm.disj (Fm.atom i) (Fm.neg (Fm.atom i))

/-- The guard on the first `N` atoms. -/
def guard : Nat → Fm
  | 0 => Fm.top
  | n + 1 => Fm.conj (guard n) (lemAt n)

/-- The witness for ψ: the guard in front. -/
def witness (N : Nat) (ψ : Fm) : Fm := Fm.imp (guard N) ψ

theorem lemAt_Z (m : Marking) (i : Nat) (h : m i = V.Z) : evalF m (lemAt i) = V.F := by
  show zor (m i) (znot (m i)) = V.F
  rw [h]
  rfl

theorem lemAt_T (m : Marking) (i : Nat) (h : m i ≠ V.Z) : evalF m (lemAt i) = V.T := by
  show zor (m i) (znot (m i)) = V.T
  exact lem_grounded (m i) h

/-- The guard is F while some guarded atom is marked. -/
theorem guard_F (m : Marking) : ∀ (N i : Nat), i < N → m i = V.Z → evalF m (guard N) = V.F
  | 0, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, i, hi, hz => by
      show zand (evalF m (guard n)) (evalF m (lemAt n)) = V.F
      cases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ hi) with
      | inl hlt => rw [guard_F m n i hlt hz]; exact and_F_left _
      | inr heq => rw [← heq, lemAt_Z m i hz]; exact and_F_right _

/-- …and T once every guarded atom is verified. -/
theorem guard_T (m : Marking) : ∀ N : Nat, (∀ i, i < N → m i ≠ V.Z) → evalF m (guard N) = V.T
  | 0, _ => rfl
  | n + 1, h => by
      show zand (evalF m (guard n)) (evalF m (lemAt n)) = V.T
      rw [guard_T m n (fun i hi => h i (Nat.lt_succ_of_lt hi)), lemAt_T m n (h n (Nat.lt_succ_self n))]
      rfl

/-- At the all-marked start the witness reads T (for a guard with at least one atom). -/
theorem witness_allZ (n : Nat) (ψ : Fm) : evalF allZ (witness (n + 1) ψ) = V.T := by
  show zimp (evalF allZ (guard (n + 1))) (evalF allZ ψ) = V.T
  rw [guard_F allZ (n + 1) 0 (Nat.zero_lt_succ n) rfl]
  exact imp_F_left _

/-- The guard looks only at the atoms it guards. -/
theorem dependsOn_guard : ∀ (N a : Nat), dependsOn (guard N) a = true → a < N
  | 0, _, h => Bool.noConfusion h
  | n + 1, a, h => by
      have h' : (dependsOn (guard n) a || (Nat.beq n a || Nat.beq n a)) = true := h
      cases orT _ _ h' with
      | inl h1 => exact Nat.lt_succ_of_lt (dependsOn_guard n a h1)
      | inr h2 =>
          cases orT _ _ h2 with
          | inl h3 => rw [← Nat.eq_of_beq_eq_true h3]; exact Nat.lt_succ_self n
          | inr h3 => rw [← Nat.eq_of_beq_eq_true h3]; exact Nat.lt_succ_self n
where
  orT : ∀ a b : Bool, (a || b) = true → a = true ∨ b = true := by decide

/-! ### Deciding "some guarded atom is still marked", without Classical -/

def hasMark (m : Marking) : Nat → Bool
  | 0 => false
  | n + 1 => hasMark m n || decide (m n = V.Z)

theorem hasMark_true (m : Marking) : ∀ N, hasMark m N = true → ∃ i, i < N ∧ m i = V.Z
  | 0, h => Bool.noConfusion h
  | n + 1, h => by
      cases dependsOn_guard.orT _ _ h with
      | inl h1 =>
          have ⟨i, hi, hz⟩ := hasMark_true m n h1
          exact ⟨i, Nat.lt_succ_of_lt hi, hz⟩
      | inr h2 => exact ⟨n, Nat.lt_succ_self n, of_decide_eq_true h2⟩

theorem hasMark_false (m : Marking) : ∀ N, hasMark m N = false → ∀ i, i < N → m i ≠ V.Z
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
      have h' : (hasMark m n || decide (m n = V.Z)) = false := h
      have ⟨h1, h2⟩ := orF _ _ h'
      cases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ hi) with
      | inl hlt => exact hasMark_false m n h1 i hlt
      | inr heq => rw [heq]; exact of_decide_eq_false h2
where
  orF : ∀ a b : Bool, (a || b) = false → a = false ∧ b = false := by decide

/-! ### The theorem -/

/-- **HEREDITY OF THE WITNESS IS TAUTOLOGY-HOOD OF ψ.** For ψ over the first
`n+1` atoms: the T verdict of `G → ψ` at the all-marked start survives every
refinement exactly when ψ reads T at every marking without marks. -/
theorem hereditary_iff_taut (n : Nat) (ψ : Fm)
    (hψ : ∀ a, dependsOn ψ a = true → a < n + 1) :
    Hereditary (witness (n + 1) ψ) allZ ↔
      ∀ c : Marking, (∀ a, c a ≠ V.Z) → evalF c ψ = V.T := by
  constructor
  · intro h c hc
    have hr : Refines c allZ := fun a ha => absurd rfl ha
    have hv := h c hr
    rw [witness_allZ n ψ] at hv
    have hg : evalF c (guard (n + 1)) = V.T := guard_T c (n + 1) (fun i _ => hc i)
    have hv' : zimp (evalF c (guard (n + 1))) (evalF c ψ) = V.T := hv
    rw [hg, imp_T_left _ (evalF_ne_Z c hc ψ)] at hv'
    exact hv'
  · intro htaut m' _
    rw [witness_allZ n ψ]
    cases hm : hasMark m' (n + 1) with
    | true =>
        have ⟨i, hi, hz⟩ := hasMark_true m' (n + 1) hm
        show zimp (evalF m' (guard (n + 1))) (evalF m' ψ) = V.T
        rw [guard_F m' (n + 1) i hi hz]
        exact imp_F_left _
    | false =>
        have hall := hasMark_false m' (n + 1) hm
        -- every atom the witness looks at is verified in m', so m' agrees with its closure there
        have hagree : evalF (close m') (witness (n + 1) ψ) = evalF m' (witness (n + 1) ψ) := by
          apply evalF_congr_dep
          intro a ha
          have ha' : (dependsOn (guard (n + 1)) a || dependsOn ψ a) = true := ha
          have hlt : a < n + 1 := by
            cases dependsOn_guard.orT _ _ ha' with
            | inl h1 => exact dependsOn_guard (n + 1) a h1
            | inr h2 => exact hψ a h2
          exact close_fixes m' a (hall a hlt)
        rw [← hagree]
        show zimp (evalF (close m') (guard (n + 1))) (evalF (close m') ψ) = V.T
        rw [guard_T (close m') (n + 1) (fun i _ => close_grounded m' i),
            imp_T_left _ (evalF_ne_Z (close m') (close_grounded m') ψ)]
        exact htaut (close m') (close_grounded m')

/-- The other direction of the same coin, stated for the record: a ψ that is
NOT a tautology gives a T verdict that some refinement revokes — the fence
family of E33 is the case ψ = (a → a). -/
theorem not_taut_revocable (n : Nat) (ψ : Fm)
    (hψ : ∀ a, dependsOn ψ a = true → a < n + 1)
    (c : Marking) (hc : ∀ a, c a ≠ V.Z) (hF : evalF c ψ ≠ V.T) :
    ¬ Hereditary (witness (n + 1) ψ) allZ := by
  intro h
  exact hF ((hereditary_iff_taut n ψ hψ).mp h c hc)

end ZHeredTaut

#print axioms ZHeredTaut.evalF_ne_Z
#print axioms ZHeredTaut.guard_F
#print axioms ZHeredTaut.guard_T
#print axioms ZHeredTaut.witness_allZ
#print axioms ZHeredTaut.hasMark_true
#print axioms ZHeredTaut.hasMark_false
#print axioms ZHeredTaut.hereditary_iff_taut
#print axioms ZHeredTaut.not_taut_revocable
