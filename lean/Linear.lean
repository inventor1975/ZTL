import Receipt

/-!
# What the greedy register can lose, and what it cannot. Zero axioms.

`closure_coincides` settles one half: where the withheld atom occurs under no
negation, no antecedent and no exclusive-or, the kernel and completion agree.
That is a statement about POSITION.

This file settles the other half, and the axis is different — MULTIPLICITY.

    linear_no_loss :  a occurs at most once in φ,  v a = Z,
                      both completions give the same classical x
                      →  the verdict is x

Read as: **the judge can lose a truth only where the same unverified ground is
mentioned twice.** Where a ground appears once, no answer that both readings
agree on can be lost.

MEASURED FIRST, and the first formulation was killed by one example before any
census ran. I intended to claim that single occurrence makes kernel and
completion coincide outright. `¬¬p` refutes it: one occurrence, and the kernel
grants `T` while the completion `p := F` defeats it. The mark dies at the FIRST
connective (`¬Z = F`), and the outer negation then works on a settled falsehood,
so multiplicity cannot explain the over-grants. It explains only the losses.

The census that followed (`lab/losses/`): 280,118 marked cells over an
exhaustive depth-2 pool on three atoms plus 40,000 random formulas of depth ≤ 6
on four. **Zero losses at multiplicity one**, in both polarities separately —
46,431 cells where both completions give T, 28,731 where both give F, no
violation in either. Over-grants at multiplicity one: 16,586, as expected.

So the two halves of the trade have different shapes. An over-grant needs a
negation over the mark; a loss needs the mark twice.
-/

namespace V

/-- How many times the atom occurs — the axis this file is about. -/
def occCount (a : Nat) : Fm → Nat
  | .atom n => if n = a then 1 else 0
  | .top => 0
  | .bot => 0
  | .neg φ => occCount a φ
  | .conj φ ψ => occCount a φ + occCount a ψ
  | .disj φ ψ => occCount a φ + occCount a ψ
  | .imp φ ψ => occCount a φ + occCount a ψ
  | .xor φ ψ => occCount a φ + occCount a ψ
  | .xnor φ ψ => occCount a φ + occCount a ψ

/-- Zero occurrences is exactly not occurring — bridges to `eval_indep`. -/
theorem occCount_zero_iff (a : Nat) :
    ∀ φ : Fm, occCount a φ = 0 → occurs a φ = false := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      show decide (n = a) = false
      cases hn : decide (n = a) with
      | false => rfl
      | true =>
          have hq : occCount a (Fm.atom n) = 1 := by
            show (if n = a then 1 else 0) = 1
            rw [if_pos (of_decide_eq_true hn)]
          rw [hq] at h
          exact Nat.noConfusion h
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih => intro h; exact ih h
  | conj φ ψ ihφ ihψ =>
      intro h
      show (occurs a φ || occurs a ψ) = false
      have hφ : occCount a φ = 0 := Nat.eq_zero_of_add_eq_zero_right h
      have hψ : occCount a ψ = 0 := Nat.eq_zero_of_add_eq_zero_left h
      rw [ihφ hφ, ihψ hψ]; rfl
  | disj φ ψ ihφ ihψ =>
      intro h
      show (occurs a φ || occurs a ψ) = false
      have hφ : occCount a φ = 0 := Nat.eq_zero_of_add_eq_zero_right h
      have hψ : occCount a ψ = 0 := Nat.eq_zero_of_add_eq_zero_left h
      rw [ihφ hφ, ihψ hψ]; rfl
  | imp φ ψ ihφ ihψ =>
      intro h
      show (occurs a φ || occurs a ψ) = false
      have hφ : occCount a φ = 0 := Nat.eq_zero_of_add_eq_zero_right h
      have hψ : occCount a ψ = 0 := Nat.eq_zero_of_add_eq_zero_left h
      rw [ihφ hφ, ihψ hψ]; rfl
  | xor φ ψ ihφ ihψ =>
      intro h
      show (occurs a φ || occurs a ψ) = false
      have hφ : occCount a φ = 0 := Nat.eq_zero_of_add_eq_zero_right h
      have hψ : occCount a ψ = 0 := Nat.eq_zero_of_add_eq_zero_left h
      rw [ihφ hφ, ihψ hψ]; rfl
  | xnor φ ψ ihφ ihψ =>
      intro h
      show (occurs a φ || occurs a ψ) = false
      have hφ : occCount a φ = 0 := Nat.eq_zero_of_add_eq_zero_right h
      have hψ : occCount a ψ = 0 := Nat.eq_zero_of_add_eq_zero_left h
      rw [ihφ hφ, ihψ hψ]; rfl

/-! ## The finite facts the binary cases turn on -/

theorem and_absorb_r : ∀ l, zand l T = zand l F → zand l Z = zand l T := by decide
theorem and_absorb_l : ∀ r, zand T r = zand F r → zand Z r = zand T r := by decide
theorem or_absorb_r : ∀ l, zor l T = zor l F → zor l Z = zor l T := by decide
theorem or_absorb_l : ∀ r, zor T r = zor F r → zor Z r = zor T r := by decide
theorem imp_absorb_r : ∀ l, zimp l T = zimp l F → zimp l Z = zimp l T := by decide
theorem imp_absorb_l : ∀ r, zimp T r = zimp F r → zimp Z r = zimp T r := by decide
theorem xor_absorb_r : ∀ l, zxor l T = zxor l F → zxor l Z = zxor l T := by decide
theorem xor_absorb_l : ∀ r, zxor T r = zxor F r → zxor Z r = zxor T r := by decide
theorem xnor_absorb_r : ∀ l, zxnor l T = zxnor l F → zxnor l Z = zxnor l T := by decide
theorem xnor_absorb_l : ∀ r, zxnor T r = zxnor F r → zxnor Z r = zxnor T r := by decide

/-- No connective ever returns the mark — the greediness theorem, pointwise. -/
theorem znot_ne_Z : ∀ x, znot x ≠ Z := by decide
theorem zand_ne_Z : ∀ x y, zand x y ≠ Z := by decide
theorem zor_ne_Z : ∀ x y, zor x y ≠ Z := by decide
theorem zimp_ne_Z : ∀ x y, zimp x y ≠ Z := by decide
theorem zxor_ne_Z : ∀ x y, zxor x y ≠ Z := by decide
theorem zxnor_ne_Z : ∀ x y, zxnor x y ≠ Z := by decide

/-- `Z` is reachable only at a bare atom, so a subformula reading `Z` under one
completion reads `Z` under the other and under `v`. -/
theorem z_pins (a : Nat) (v : Nat → V) (hv : v a = Z) :
    ∀ φ : Fm, evalF (setA a T v) φ = Z → evalF v φ = Z ∧ evalF (setA a F v) φ = Z := by
  intro φ
  cases φ with
  | atom n =>
      intro h
      have h' : setA a T v n = Z := h
      cases hna : decide (n = a) with
      | true =>
          have hn : n = a := of_decide_eq_true hna
          rw [hn, setA_self a T v] at h'
          exact absurd h' (by decide)
      | false =>
          have hne : n ≠ a := of_decide_eq_false hna
          rw [setA_other T v hne] at h'
          exact ⟨h', by show setA a F v n = Z; rw [setA_other F v hne]; exact h'⟩
  | top =>
      intro h
      have h2 : (T : V) = Z := h
      exact absurd h2 (by decide)
  | bot =>
      intro h
      have h2 : (F : V) = Z := h
      exact absurd h2 (by decide)
  | neg φ => intro h; exact absurd h (znot_ne_Z _)
  | conj φ ψ => intro h; exact absurd h (zand_ne_Z _ _)
  | disj φ ψ => intro h; exact absurd h (zor_ne_Z _ _)
  | imp φ ψ => intro h; exact absurd h (zimp_ne_Z _ _)
  | xor φ ψ => intro h; exact absurd h (zxor_ne_Z _ _)
  | xnor φ ψ => intro h; exact absurd h (zxnor_ne_Z _ _)

/-- `Z` is reachable only at a bare atom, so a subformula reading `Z` under one
completion reads `Z` under the other and under `v`. -/
theorem z_pins' (a : Nat) (v : Nat → V) (hv : v a = Z) :
    ∀ φ : Fm, evalF (setA a F v) φ = Z → evalF v φ = Z ∧ evalF (setA a T v) φ = Z := by
  intro φ
  cases φ with
  | atom n =>
      intro h
      have h' : setA a F v n = Z := h
      cases hna : decide (n = a) with
      | true =>
          have hn : n = a := of_decide_eq_true hna
          rw [hn, setA_self a F v] at h'
          exact absurd h' (by decide)
      | false =>
          have hne : n ≠ a := of_decide_eq_false hna
          rw [setA_other F v hne] at h'
          exact ⟨h', by show setA a T v n = Z; rw [setA_other T v hne]; exact h'⟩
  | top =>
      intro h
      have h2 : (T : V) = Z := h
      exact absurd h2 (by decide)
  | bot =>
      intro h
      have h2 : (F : V) = Z := h
      exact absurd h2 (by decide)
  | neg φ => intro h; exact absurd h (znot_ne_Z _)
  | conj φ ψ => intro h; exact absurd h (zand_ne_Z _ _)
  | disj φ ψ => intro h; exact absurd h (zor_ne_Z _ _)
  | imp φ ψ => intro h; exact absurd h (zimp_ne_Z _ _)
  | xor φ ψ => intro h; exact absurd h (zxor_ne_Z _ _)
  | xnor φ ψ => intro h; exact absurd h (zxnor_ne_Z _ _)

/-! ## Nat arithmetic by hand

`omega` would settle these in one word and costs `[propext, Quot.sound]`
(measured, 2026-08-20). The corpus's own note said `omega` was the safe choice
against `Classical.choice`, which is true and not the same thing. For the empty
list it has to be done by hand. -/

theorem split_zero {n : Nat} (h : 0 + n ≤ 1) : n ≤ 1 := by
  rw [Nat.zero_add] at h; exact h

theorem split_succ {k n : Nat} (h : k + 1 + n ≤ 1) : n = 0 ∧ k = 0 := by
  rw [Nat.add_right_comm] at h
  have h0 : k + n ≤ 0 := Nat.le_of_succ_le_succ h
  have he : k + n = 0 := Nat.le_zero.mp h0
  exact ⟨Nat.eq_zero_of_add_eq_zero_left he, Nat.eq_zero_of_add_eq_zero_right he⟩

/-! ## The main theorem -/

/-- A value the judge could return as a verdict. -/
def isClassical (x : V) : Bool :=
  match x with | T => true | F => true | Z => false

/-- **The judge can lose a truth only where the same unverified ground is
mentioned twice.** Where a ground occurs at most once, no answer that both of
its readings agree on can be lost. -/
theorem linear_no_loss (a : Nat) (v : Nat → V) (hv : v a = Z) :
    ∀ φ : Fm, occCount a φ ≤ 1 → ∀ x : V, isClassical x = true →
      evalF (setA a T v) φ = x → evalF (setA a F v) φ = x → evalF v φ = x := by
  intro φ
  induction φ with
  | atom n =>
      intro _ x _ hT hF
      have eT : setA a T v n = x := hT
      have eF : setA a F v n = x := hF
      show v n = x
      cases hna : decide (n = a) with
      | false =>
          have hne : n ≠ a := of_decide_eq_false hna
          rw [setA_other T v hne] at eT
          exact eT
      | true =>
          have hn : n = a := of_decide_eq_true hna
          rw [hn, setA_self a T v] at eT
          rw [hn, setA_self a F v] at eF
          rw [← eT] at eF
          exact absurd eF (by decide)
  | top => intro _ x _ hT _; exact hT
  | bot => intro _ x _ hT _; exact hT
  | neg φ ih =>
      intro hc x hx hT hF
      have eT : znot (evalF (setA a T v) φ) = x := hT
      have eF : znot (evalF (setA a F v) φ) = x := hF
      show znot (evalF v φ) = x
      cases x with
      | Z => exact absurd hx (by decide)
      | T =>
          have gT : evalF (setA a T v) φ = F := by
            revert eT; cases evalF (setA a T v) φ <;> intro h <;> first
              | rfl | exact absurd h (by decide)
          have gF : evalF (setA a F v) φ = F := by
            revert eF; cases evalF (setA a F v) φ <;> intro h <;> first
              | rfl | exact absurd h (by decide)
          rw [ih hc F (by decide) gT gF]; rfl
      | F =>
          cases hr : evalF (setA a T v) φ with
          | F => rw [hr] at eT; exact absurd eT (by decide)
          | Z => rw [(z_pins a v hv φ hr).1]; rfl
          | T =>
              have gF : evalF (setA a F v) φ = T := by
                cases hrf : evalF (setA a F v) φ with
                | T => rfl
                | F => rw [hrf] at eF; exact absurd eF (by decide)
                | Z => exact absurd ((z_pins' a v hv φ hrf).2) (by rw [hr]; decide)
              rw [ih hc T (by decide) hr gF]; rfl
  | conj φ ψ ihφ ihψ =>
      intro hc x hx hT hF
      have eT : zand (evalF (setA a T v) φ) (evalF (setA a T v) ψ) = x := hT
      have eF : zand (evalF (setA a F v) φ) (evalF (setA a F v) ψ) = x := hF
      show zand (evalF v φ) (evalF v ψ) = x
      have hsum : occCount a φ + occCount a ψ ≤ 1 := hc
      cases hl : occCount a φ with
      | zero =>
          have lT := eval_indep a T v φ (occCount_zero_iff a φ hl)
          have lF := eval_indep a F v φ (occCount_zero_iff a φ hl)
          rw [lT] at eT
          rw [lF] at eF
          rw [hl] at hsum
          have hψ : occCount a ψ ≤ 1 := split_zero hsum
          cases hd : decide (evalF (setA a T v) ψ = evalF (setA a F v) ψ) with
          | true =>
              have heq : evalF (setA a T v) ψ = evalF (setA a F v) ψ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) ψ with
              | Z => have hp := z_pins a v hv ψ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihψ hψ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihψ hψ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) ψ ≠ evalF (setA a F v) ψ := of_decide_eq_false hd
              have hb : zand (evalF v φ) T = x ∧ zand (evalF v φ) F = x := by
                cases hrt : evalF (setA a T v) ψ <;> cases hrf : evalF (setA a F v) ψ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv ψ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv ψ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v ψ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [and_absorb_r (evalF v φ) (hb.1.trans hb.2.symm)]; exact hb.1
      | succ k =>
          rw [hl] at hsum
          have hsp := split_succ hsum
          have hψ0 : occCount a ψ = 0 := hsp.1
          have hφ : occCount a φ ≤ 1 := by
            rw [hl, hsp.2, Nat.zero_add]
            exact Nat.le_refl 1
          have rT := eval_indep a T v ψ (occCount_zero_iff a ψ hψ0)
          have rF := eval_indep a F v ψ (occCount_zero_iff a ψ hψ0)
          rw [rT] at eT
          rw [rF] at eF
          cases hd : decide (evalF (setA a T v) φ = evalF (setA a F v) φ) with
          | true =>
              have heq : evalF (setA a T v) φ = evalF (setA a F v) φ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) φ with
              | Z => have hp := z_pins a v hv φ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihφ hφ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihφ hφ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) φ ≠ evalF (setA a F v) φ := of_decide_eq_false hd
              have hb : zand T (evalF v ψ) = x ∧ zand F (evalF v ψ) = x := by
                cases hrt : evalF (setA a T v) φ <;> cases hrf : evalF (setA a F v) φ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv φ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv φ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v φ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [and_absorb_l (evalF v ψ) (hb.1.trans hb.2.symm)]; exact hb.1
  | disj φ ψ ihφ ihψ =>
      intro hc x hx hT hF
      have eT : zor (evalF (setA a T v) φ) (evalF (setA a T v) ψ) = x := hT
      have eF : zor (evalF (setA a F v) φ) (evalF (setA a F v) ψ) = x := hF
      show zor (evalF v φ) (evalF v ψ) = x
      have hsum : occCount a φ + occCount a ψ ≤ 1 := hc
      cases hl : occCount a φ with
      | zero =>
          have lT := eval_indep a T v φ (occCount_zero_iff a φ hl)
          have lF := eval_indep a F v φ (occCount_zero_iff a φ hl)
          rw [lT] at eT
          rw [lF] at eF
          rw [hl] at hsum
          have hψ : occCount a ψ ≤ 1 := split_zero hsum
          cases hd : decide (evalF (setA a T v) ψ = evalF (setA a F v) ψ) with
          | true =>
              have heq : evalF (setA a T v) ψ = evalF (setA a F v) ψ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) ψ with
              | Z => have hp := z_pins a v hv ψ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihψ hψ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihψ hψ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) ψ ≠ evalF (setA a F v) ψ := of_decide_eq_false hd
              have hb : zor (evalF v φ) T = x ∧ zor (evalF v φ) F = x := by
                cases hrt : evalF (setA a T v) ψ <;> cases hrf : evalF (setA a F v) ψ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv ψ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv ψ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v ψ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [or_absorb_r (evalF v φ) (hb.1.trans hb.2.symm)]; exact hb.1
      | succ k =>
          rw [hl] at hsum
          have hsp := split_succ hsum
          have hψ0 : occCount a ψ = 0 := hsp.1
          have hφ : occCount a φ ≤ 1 := by
            rw [hl, hsp.2, Nat.zero_add]
            exact Nat.le_refl 1
          have rT := eval_indep a T v ψ (occCount_zero_iff a ψ hψ0)
          have rF := eval_indep a F v ψ (occCount_zero_iff a ψ hψ0)
          rw [rT] at eT
          rw [rF] at eF
          cases hd : decide (evalF (setA a T v) φ = evalF (setA a F v) φ) with
          | true =>
              have heq : evalF (setA a T v) φ = evalF (setA a F v) φ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) φ with
              | Z => have hp := z_pins a v hv φ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihφ hφ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihφ hφ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) φ ≠ evalF (setA a F v) φ := of_decide_eq_false hd
              have hb : zor T (evalF v ψ) = x ∧ zor F (evalF v ψ) = x := by
                cases hrt : evalF (setA a T v) φ <;> cases hrf : evalF (setA a F v) φ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv φ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv φ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v φ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [or_absorb_l (evalF v ψ) (hb.1.trans hb.2.symm)]; exact hb.1
  | imp φ ψ ihφ ihψ =>
      intro hc x hx hT hF
      have eT : zimp (evalF (setA a T v) φ) (evalF (setA a T v) ψ) = x := hT
      have eF : zimp (evalF (setA a F v) φ) (evalF (setA a F v) ψ) = x := hF
      show zimp (evalF v φ) (evalF v ψ) = x
      have hsum : occCount a φ + occCount a ψ ≤ 1 := hc
      cases hl : occCount a φ with
      | zero =>
          have lT := eval_indep a T v φ (occCount_zero_iff a φ hl)
          have lF := eval_indep a F v φ (occCount_zero_iff a φ hl)
          rw [lT] at eT
          rw [lF] at eF
          rw [hl] at hsum
          have hψ : occCount a ψ ≤ 1 := split_zero hsum
          cases hd : decide (evalF (setA a T v) ψ = evalF (setA a F v) ψ) with
          | true =>
              have heq : evalF (setA a T v) ψ = evalF (setA a F v) ψ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) ψ with
              | Z => have hp := z_pins a v hv ψ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihψ hψ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihψ hψ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) ψ ≠ evalF (setA a F v) ψ := of_decide_eq_false hd
              have hb : zimp (evalF v φ) T = x ∧ zimp (evalF v φ) F = x := by
                cases hrt : evalF (setA a T v) ψ <;> cases hrf : evalF (setA a F v) ψ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv ψ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv ψ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v ψ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [imp_absorb_r (evalF v φ) (hb.1.trans hb.2.symm)]; exact hb.1
      | succ k =>
          rw [hl] at hsum
          have hsp := split_succ hsum
          have hψ0 : occCount a ψ = 0 := hsp.1
          have hφ : occCount a φ ≤ 1 := by
            rw [hl, hsp.2, Nat.zero_add]
            exact Nat.le_refl 1
          have rT := eval_indep a T v ψ (occCount_zero_iff a ψ hψ0)
          have rF := eval_indep a F v ψ (occCount_zero_iff a ψ hψ0)
          rw [rT] at eT
          rw [rF] at eF
          cases hd : decide (evalF (setA a T v) φ = evalF (setA a F v) φ) with
          | true =>
              have heq : evalF (setA a T v) φ = evalF (setA a F v) φ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) φ with
              | Z => have hp := z_pins a v hv φ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihφ hφ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihφ hφ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) φ ≠ evalF (setA a F v) φ := of_decide_eq_false hd
              have hb : zimp T (evalF v ψ) = x ∧ zimp F (evalF v ψ) = x := by
                cases hrt : evalF (setA a T v) φ <;> cases hrf : evalF (setA a F v) φ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv φ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv φ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v φ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [imp_absorb_l (evalF v ψ) (hb.1.trans hb.2.symm)]; exact hb.1
  | xor φ ψ ihφ ihψ =>
      intro hc x hx hT hF
      have eT : zxor (evalF (setA a T v) φ) (evalF (setA a T v) ψ) = x := hT
      have eF : zxor (evalF (setA a F v) φ) (evalF (setA a F v) ψ) = x := hF
      show zxor (evalF v φ) (evalF v ψ) = x
      have hsum : occCount a φ + occCount a ψ ≤ 1 := hc
      cases hl : occCount a φ with
      | zero =>
          have lT := eval_indep a T v φ (occCount_zero_iff a φ hl)
          have lF := eval_indep a F v φ (occCount_zero_iff a φ hl)
          rw [lT] at eT
          rw [lF] at eF
          rw [hl] at hsum
          have hψ : occCount a ψ ≤ 1 := split_zero hsum
          cases hd : decide (evalF (setA a T v) ψ = evalF (setA a F v) ψ) with
          | true =>
              have heq : evalF (setA a T v) ψ = evalF (setA a F v) ψ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) ψ with
              | Z => have hp := z_pins a v hv ψ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihψ hψ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihψ hψ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) ψ ≠ evalF (setA a F v) ψ := of_decide_eq_false hd
              have hb : zxor (evalF v φ) T = x ∧ zxor (evalF v φ) F = x := by
                cases hrt : evalF (setA a T v) ψ <;> cases hrf : evalF (setA a F v) ψ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv ψ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv ψ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v ψ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [xor_absorb_r (evalF v φ) (hb.1.trans hb.2.symm)]; exact hb.1
      | succ k =>
          rw [hl] at hsum
          have hsp := split_succ hsum
          have hψ0 : occCount a ψ = 0 := hsp.1
          have hφ : occCount a φ ≤ 1 := by
            rw [hl, hsp.2, Nat.zero_add]
            exact Nat.le_refl 1
          have rT := eval_indep a T v ψ (occCount_zero_iff a ψ hψ0)
          have rF := eval_indep a F v ψ (occCount_zero_iff a ψ hψ0)
          rw [rT] at eT
          rw [rF] at eF
          cases hd : decide (evalF (setA a T v) φ = evalF (setA a F v) φ) with
          | true =>
              have heq : evalF (setA a T v) φ = evalF (setA a F v) φ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) φ with
              | Z => have hp := z_pins a v hv φ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihφ hφ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihφ hφ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) φ ≠ evalF (setA a F v) φ := of_decide_eq_false hd
              have hb : zxor T (evalF v ψ) = x ∧ zxor F (evalF v ψ) = x := by
                cases hrt : evalF (setA a T v) φ <;> cases hrf : evalF (setA a F v) φ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv φ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv φ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v φ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [xor_absorb_l (evalF v ψ) (hb.1.trans hb.2.symm)]; exact hb.1
  | xnor φ ψ ihφ ihψ =>
      intro hc x hx hT hF
      have eT : zxnor (evalF (setA a T v) φ) (evalF (setA a T v) ψ) = x := hT
      have eF : zxnor (evalF (setA a F v) φ) (evalF (setA a F v) ψ) = x := hF
      show zxnor (evalF v φ) (evalF v ψ) = x
      have hsum : occCount a φ + occCount a ψ ≤ 1 := hc
      cases hl : occCount a φ with
      | zero =>
          have lT := eval_indep a T v φ (occCount_zero_iff a φ hl)
          have lF := eval_indep a F v φ (occCount_zero_iff a φ hl)
          rw [lT] at eT
          rw [lF] at eF
          rw [hl] at hsum
          have hψ : occCount a ψ ≤ 1 := split_zero hsum
          cases hd : decide (evalF (setA a T v) ψ = evalF (setA a F v) ψ) with
          | true =>
              have heq : evalF (setA a T v) ψ = evalF (setA a F v) ψ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) ψ with
              | Z => have hp := z_pins a v hv ψ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihψ hψ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihψ hψ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) ψ ≠ evalF (setA a F v) ψ := of_decide_eq_false hd
              have hb : zxnor (evalF v φ) T = x ∧ zxnor (evalF v φ) F = x := by
                cases hrt : evalF (setA a T v) ψ <;> cases hrf : evalF (setA a F v) ψ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv ψ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv ψ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v ψ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [xnor_absorb_r (evalF v φ) (hb.1.trans hb.2.symm)]; exact hb.1
      | succ k =>
          rw [hl] at hsum
          have hsp := split_succ hsum
          have hψ0 : occCount a ψ = 0 := hsp.1
          have hφ : occCount a φ ≤ 1 := by
            rw [hl, hsp.2, Nat.zero_add]
            exact Nat.le_refl 1
          have rT := eval_indep a T v ψ (occCount_zero_iff a ψ hψ0)
          have rF := eval_indep a F v ψ (occCount_zero_iff a ψ hψ0)
          rw [rT] at eT
          rw [rF] at eF
          cases hd : decide (evalF (setA a T v) φ = evalF (setA a F v) φ) with
          | true =>
              have heq : evalF (setA a T v) φ = evalF (setA a F v) φ := of_decide_eq_true hd
              cases hr : evalF (setA a T v) φ with
              | Z => have hp := z_pins a v hv φ hr; rw [hp.1]; rw [hr] at eT; exact eT
              | T =>
                  have hq := ihφ hφ T (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
              | F =>
                  have hq := ihφ hφ F (by decide) hr (heq ▸ hr)
                  rw [hq]; rw [hr] at eT; exact eT
          | false =>
              have hne : evalF (setA a T v) φ ≠ evalF (setA a F v) φ := of_decide_eq_false hd
              have hb : zxnor T (evalF v ψ) = x ∧ zxnor F (evalF v ψ) = x := by
                cases hrt : evalF (setA a T v) φ <;> cases hrf : evalF (setA a F v) φ <;>
                  rw [hrt] at eT <;> rw [hrf] at eF <;> first
                    | exact absurd (hrt.trans hrf.symm) hne
                    | exact ⟨eT, eF⟩
                    | exact ⟨eF, eT⟩
                    | (exact absurd ((z_pins a v hv φ hrt).2) (by rw [hrf]; decide))
                    | (exact absurd ((z_pins' a v hv φ hrf).2) (by rw [hrt]; decide))
              cases hr : evalF v φ with
              | T => exact hb.1
              | F => exact hb.2
              | Z => rw [xnor_absorb_l (evalF v ψ) (hb.1.trans hb.2.symm)]; exact hb.1

#print axioms occCount
#print axioms occCount_zero_iff
#print axioms z_pins
#print axioms linear_no_loss

end V
