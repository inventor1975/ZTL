import ZAffine

/-!
# ZAffine2 — the remainders of the nonlinear steps (min-range), sound. Zero axioms.

`zaffine._minrange`: for `f` with `f'` monotone on `[a, b]`, the slope `α` is taken at one end so that the remainder
`r = f − α·x` is MONOTONE on `[a, b]`; its range is read at the two ends. Here `Rem` for `1/x` (a positive interval,
both ends) and for `exp` (`E_slope`: exp's chord between two points lies between its slopes there, at every index).
Then `AffR` — the kernel's affine reading step by step — and `aff_sound`: its interval holds the value at every point of
the box; `boxEv_meet` for the kernel's meet with the plain reading. zaffinecert.py checks the premises in the run.
-/

namespace ZAffine

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv

theorem inv_ge_of_le {x b : QExpr} (hx : qlt qzero x) (hxb : qle x b) : qle (qinv' b) (qinv' x) :=
  (ZTrig.inv_bound hx hxb).2

theorem inv_id (x y : QExpr) (hx : ¬ qEq x qzero) (hy : ¬ qEq y qzero) :
    qEq (qsub (qinv' x) (qinv' y)) (qmul (qsub y x) (qmul (qinv' x) (qinv' y))) := by
  have cx := qmul_inv'_cancel hx
  have cy := qmul_inv'_cancel hy
  have e : qEq (qmul (qsub y x) (qmul (qinv' x) (qinv' y)))
      (qsub (qmul (qinv' x) (qmul y (qinv' y))) (qmul (qinv' y) (qmul x (qinv' x)))) := by unfold qsub; rat_ring
  have e2 := qmul_respects (qEq_refl (qinv' x)) cy
  have e3 := qmul_respects (qEq_refl (qinv' y)) cx
  unfold qsub at *
  generalize qmul (qinv' x) (qmul y (qinv' y)) = A at *
  generalize qmul (qinv' y) (qmul x (qinv' x)) = A' at *
  generalize qmul (qadd y (qneg x)) (qmul (qinv' x) (qinv' y)) = C at *
  have o1 : qEq (qmul (qinv' x) qone) (qinv' x) := by rat_ring
  have o2 : qEq (qmul (qinv' y) qone) (qinv' y) := by rat_ring
  generalize qmul (qinv' x) qone = O1 at *
  generalize qmul (qinv' y) qone = O2 at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `r(y) − r(x) = (x − y)·(1/(x y) + α)` for `r(t) = 1/t − α t`. -/
theorem r_diff (x y α : QExpr) (hx : ¬ qEq x qzero) (hy : ¬ qEq y qzero) :
    qEq (qsub (qsub (qinv' y) (qmul α y)) (qsub (qinv' x) (qmul α x)))
      (qmul (qsub x y) (qadd (qmul (qinv' y) (qinv' x)) α)) := by
  have d := inv_id y x hy hx
  have e : qEq (qmul (qsub x y) (qadd (qmul (qinv' y) (qinv' x)) α))
      (qadd (qmul (qsub x y) (qmul (qinv' y) (qinv' x))) (qmul (qsub x y) α)) := by rat_ring
  generalize qmul (qsub x y) (qmul (qinv' y) (qinv' x)) = P at *
  generalize qmul (qsub x y) (qadd (qmul (qinv' y) (qinv' x)) α) = R at *
  unfold qsub at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem half_pos : qlt qzero ZTrig.half := by
  obtain ⟨h1, h0⟩ := ZTrig.half_facts
  exact qlt_iff_le_not_le.mpr ⟨h0, fun h => (qlt_iff_le_not_le.mp qone_pos).2 (by rat_linarith)⟩

theorem nz_of_pos {x : QExpr} (h : qlt qzero x) : ¬ qEq x qzero := ne_zero_of_lt h

/-- The common frame of `1/x` on `[a, b]`, `a > 0`: `x ≥ a/2` within the slack, the reciprocals bounded by `2/a`. -/
theorem recip_frame {a b x ι : QExpr} (ha : qlt qzero a) (hab : qle a b) (ι0 : qle qzero ι)
    (ιc : qle ι (qmul a ZTrig.half)) (hxa : qle (qsub a ι) x) :
    qlt qzero x ∧ ZTrig.Ab (qinv' x) (qinv' (qmul a ZTrig.half)) ∧ ZTrig.Ab (qinv' a) (qinv' (qmul a ZTrig.half)) ∧
      ZTrig.Ab (qinv' b) (qinv' (qmul a ZTrig.half)) ∧ qlt qzero (qmul a ZTrig.half) := by
  obtain ⟨hh, h0⟩ := ZTrig.half_facts
  have cp : qlt qzero (qmul a ZTrig.half) := qmul_pos ha half_pos
  have ac : qEq a (qadd (qmul a ZTrig.half) (qmul a ZTrig.half)) := by
    have := qmul_respects (qEq_refl a) hh
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
  have c0 := qle_of_qlt cp
  have xc : qle (qmul a ZTrig.half) x := by unfold qsub at hxa; rat_linarith
  have ac' : qle (qmul a ZTrig.half) a := by rat_linarith
  have bc : qle (qmul a ZTrig.half) b := qle_trans ac' hab
  have xp : qlt qzero x := qlt_iff_le_not_le.mpr ⟨qle_trans c0 xc,
    fun h => (qlt_iff_le_not_le.mp cp).2 (qle_trans xc h)⟩
  obtain ⟨x1, x2⟩ := ZTrig.inv_bound cp xc
  obtain ⟨a1, a2⟩ := ZTrig.inv_bound cp ac'
  obtain ⟨b1, b2⟩ := ZTrig.inv_bound cp bc
  have i0 := qinv'_nonneg_of_pos cp
  exact ⟨xp, ⟨by rat_linarith, x2⟩, ⟨by rat_linarith, a2⟩, ⟨by rat_linarith, b2⟩, cp⟩

/-- `1/x` ON `[a, b]`, `a > 0`, THE SLOPE AT `b` (`α ≥ −1/b²`): the remainder `1/x − α x` DECREASES, between its values
at `b` and at `a`. -/
theorem rem_recip_b {a b α ζ δ : QExpr} (ha : qlt qzero a) (hab : qle a b)
    (hα : qle (qneg (qmul (qinv' b) (qinv' b))) α)
    (hlo : qle (qsub ζ δ) (qsub (qinv' b) (qmul α b))) (hhi : qle (qsub (qinv' a) (qmul α a)) (qadd ζ δ)) :
    Rem (fun _ x => qinv' x) a b α ζ δ := by
  obtain ⟨Aα, Aα0, hAα, _⟩ := abs_wit α
  have cp : qlt qzero (qmul a ZTrig.half) := qmul_pos ha half_pos
  have ic0 := qinv'_nonneg_of_pos cp
  refine ⟨qadd (qmul (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))) Aα, qmul a ZTrig.half,
    by have := qmul_nonneg ic0 ic0; rat_linarith, cp, fun k => ⟨0, fun n _ x ι ι0 ιc hxa hxb => ?_⟩⟩
  obtain ⟨xp, hix, hia, hib, _⟩ := recip_frame ha hab ι0 ιc hxa
  have bp : qlt qzero b := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt ha) hab,
    fun h => (qlt_iff_le_not_le.mp ha).2 (qle_trans hab h)⟩
  have Kb := ab_add (ZTrig.mul_abs hix hib) hAα
  have Ka := ab_add (ZTrig.mul_abs hix hia) hAα
  have db := r_diff b x α (nz_of_pos bp) (nz_of_pos xp)
  have da := r_diff a x α (nz_of_pos ha) (nz_of_pos xp)
  have dab := r_diff a b α (nz_of_pos ha) (nz_of_pos bp)
  have ib0 := qinv'_nonneg_of_pos bp
  have iab := inv_ge_of_le ha hab
  have L20 : qle qzero (qmul ι (qadd (qmul (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))) Aα)) :=
    qmul_nonneg ι0 (by have := qmul_nonneg ic0 ic0; rat_linarith)
  generalize hIL : qmul ι (qadd (qmul (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))) Aα) = IL at *
  have mbb : qle (qmul (qinv' b) (qinv' b)) (qmul (qinv' a) (qinv' b)) := by
    have := qmul_nonneg (show qle qzero (qsub (qinv' a) (qinv' b)) by unfold qsub; rat_linarith) ib0
    unfold qsub at this; rat_linarith
  -- r(b) ≤ r(a)
  have rba : qle (qsub (qinv' b) (qmul α b)) (qsub (qinv' a) (qmul α a)) := by
    have := qmul_nonneg (show qle qzero (qsub b a) by unfold qsub; rat_linarith)
      (show qle qzero (qadd (qmul (qinv' b) (qinv' a)) α) by
        have e : qEq (qmul (qinv' b) (qinv' a)) (qmul (qinv' a) (qinv' b)) := by rat_ring
        rat_linarith)
    have e : qEq (qmul (qsub a b) (qadd (qmul (qinv' b) (qinv' a)) α)) (qneg (qmul (qsub b a) (qadd (qmul (qinv' b) (qinv' a)) α))) := by
      unfold qsub; rat_ring
    generalize qmul (qsub b a) (qadd (qmul (qinv' b) (qinv' a)) α) = P at *
    generalize qmul (qsub a b) (qadd (qmul (qinv' b) (qinv' a)) α) = P' at *
    unfold qsub at *; rat_linarith
  have lower : qle (qsub (qsub (qinv' b) (qmul α b)) IL) (qsub (qinv' x) (qmul α x)) := by
    cases qle_total x b with
    | inl h =>
        have ixb := inv_ge_of_le xp h
        have m1 := qmul_nonneg (show qle qzero (qsub (qinv' x) (qinv' b)) by unfold qsub; rat_linarith) ib0
        have pp := qmul_nonneg (show qle qzero (qsub b x) by unfold qsub; rat_linarith)
          (show qle qzero (qadd (qmul (qinv' x) (qinv' b)) α) by unfold qsub at m1; rat_linarith)
        generalize qmul (qsub b x) (qadd (qmul (qinv' x) (qinv' b)) α) = P at *
        unfold qsub at *; rat_linarith
    | inr h =>
        have ab' : ZTrig.Ab (qsub b x) ι := ⟨by unfold qsub at *; rat_linarith, by unfold qsub; rat_linarith⟩
        obtain ⟨q1, q2⟩ := ZTrig.mul_abs ab' Kb
        rw [hIL] at q1 q2
        generalize qmul (qsub b x) (qadd (qmul (qinv' x) (qinv' b)) α) = P at *
        unfold qsub at *; rat_linarith
  have upper : qle (qsub (qinv' x) (qmul α x)) (qadd (qsub (qinv' a) (qmul α a)) IL) := by
    cases qle_total x a with
    | inl h =>
        have ab' : ZTrig.Ab (qsub a x) ι := ⟨by unfold qsub; rat_linarith, by unfold qsub at *; rat_linarith⟩
        obtain ⟨q1, q2⟩ := ZTrig.mul_abs ab' Ka
        rw [hIL] at q1 q2
        generalize qmul (qsub a x) (qadd (qmul (qinv' x) (qinv' a)) α) = P at *
        unfold qsub at *; rat_linarith
    | inr h =>
        cases qle_total x b with
        | inl h' =>
            have ixb := inv_ge_of_le xp h'
            have m1 := qmul_nonneg (show qle qzero (qsub (qinv' x) (qinv' b)) by unfold qsub; rat_linarith)
              (qinv'_nonneg_of_pos ha)
            have pp := qmul_nonneg (show qle qzero (qsub x a) by unfold qsub; rat_linarith)
              (show qle qzero (qadd (qmul (qinv' x) (qinv' a)) α) by
                have e : qEq (qmul (qinv' a) (qinv' b)) (qmul (qinv' b) (qinv' a)) := by rat_ring
                unfold qsub at m1; rat_linarith)
            have e : qEq (qmul (qsub a x) (qadd (qmul (qinv' x) (qinv' a)) α)) (qneg (qmul (qsub x a) (qadd (qmul (qinv' x) (qinv' a)) α))) := by
              unfold qsub; rat_ring
            generalize qmul (qsub x a) (qadd (qmul (qinv' x) (qinv' a)) α) = P at *
            generalize qmul (qsub a x) (qadd (qmul (qinv' x) (qinv' a)) α) = P' at *
            unfold qsub at *; rat_linarith
        | inr h' =>
            have ab' : ZTrig.Ab (qsub b x) ι := ⟨by unfold qsub at *; rat_linarith, by unfold qsub; rat_linarith⟩
            obtain ⟨q1, q2⟩ := ZTrig.mul_abs ab' Kb
            rw [hIL] at q1 q2
            generalize qmul (qsub b x) (qadd (qmul (qinv' x) (qinv' b)) α) = P at *
            unfold qsub at *; rat_linarith
  have e0 := qeps_nonneg k
  show ZTrig.Ab (qsub (qsub (qinv' x) (qmul α x)) ζ) (qadd (qadd δ IL) (qeps k))
  clear db da dab Kb Ka hix hia hib
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `1/x` ON `[a, b]`, `a > 0`, THE SLOPE AT `a` (`α ≤ −1/a²`): the remainder INCREASES, between its values at `a` and
at `b`. -/
theorem rem_recip_a {a b α ζ δ : QExpr} (ha : qlt qzero a) (hab : qle a b)
    (hα : qle α (qneg (qmul (qinv' a) (qinv' a))))
    (hlo : qle (qsub ζ δ) (qsub (qinv' a) (qmul α a))) (hhi : qle (qsub (qinv' b) (qmul α b)) (qadd ζ δ)) :
    Rem (fun _ x => qinv' x) a b α ζ δ := by
  obtain ⟨Aα, Aα0, hAα, _⟩ := abs_wit α
  have cp : qlt qzero (qmul a ZTrig.half) := qmul_pos ha half_pos
  have ic0 := qinv'_nonneg_of_pos cp
  refine ⟨qadd (qmul (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))) Aα, qmul a ZTrig.half,
    by have := qmul_nonneg ic0 ic0; rat_linarith, cp, fun k => ⟨0, fun n _ x ι ι0 ιc hxa hxb => ?_⟩⟩
  obtain ⟨xp, hix, hia, hib, _⟩ := recip_frame ha hab ι0 ιc hxa
  have bp : qlt qzero b := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt ha) hab,
    fun h => (qlt_iff_le_not_le.mp ha).2 (qle_trans hab h)⟩
  have Kb := ab_add (ZTrig.mul_abs hix hib) hAα
  have Ka := ab_add (ZTrig.mul_abs hix hia) hAα
  have db := r_diff b x α (nz_of_pos bp) (nz_of_pos xp)
  have da := r_diff a x α (nz_of_pos ha) (nz_of_pos xp)
  have dab := r_diff a b α (nz_of_pos ha) (nz_of_pos bp)
  have ia0 := qinv'_nonneg_of_pos ha
  have ib0 := qinv'_nonneg_of_pos bp
  have iab := inv_ge_of_le ha hab
  have L20 : qle qzero (qmul ι (qadd (qmul (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))) Aα)) :=
    qmul_nonneg ι0 (by have := qmul_nonneg ic0 ic0; rat_linarith)
  generalize hIL : qmul ι (qadd (qmul (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))) Aα) = IL at *
  have mba : qle (qmul (qinv' b) (qinv' a)) (qmul (qinv' a) (qinv' a)) := by
    have := qmul_nonneg (show qle qzero (qsub (qinv' a) (qinv' b)) by unfold qsub; rat_linarith) ia0
    unfold qsub at this; rat_linarith
  -- r(a) ≤ r(b)
  have rab : qle (qsub (qinv' a) (qmul α a)) (qsub (qinv' b) (qmul α b)) := by
    have := qmul_nonneg (show qle qzero (qsub b a) by unfold qsub; rat_linarith)
      (show qle qzero (qneg (qadd (qmul (qinv' b) (qinv' a)) α)) by rat_linarith)
    have e : qEq (qmul (qsub a b) (qadd (qmul (qinv' b) (qinv' a)) α)) (qmul (qsub b a) (qneg (qadd (qmul (qinv' b) (qinv' a)) α))) := by
      unfold qsub; rat_ring
    generalize qmul (qsub b a) (qneg (qadd (qmul (qinv' b) (qinv' a)) α)) = P at *
    generalize qmul (qsub a b) (qadd (qmul (qinv' b) (qinv' a)) α) = P' at *
    unfold qsub at *; rat_linarith
  have lower : qle (qsub (qsub (qinv' a) (qmul α a)) IL) (qsub (qinv' x) (qmul α x)) := by
    cases qle_total a x with
    | inl h =>
        have ixa := inv_ge_of_le ha h
        have m1 := qmul_nonneg (show qle qzero (qsub (qinv' a) (qinv' x)) by unfold qsub; rat_linarith) ia0
        have pp := qmul_nonneg (show qle qzero (qsub x a) by unfold qsub; rat_linarith)
          (show qle qzero (qneg (qadd (qmul (qinv' x) (qinv' a)) α)) by
            have e : qEq (qmul (qinv' x) (qinv' a)) (qmul (qinv' a) (qinv' x)) := by rat_ring
            unfold qsub at m1; rat_linarith)
        have e : qEq (qmul (qsub a x) (qadd (qmul (qinv' x) (qinv' a)) α)) (qmul (qsub x a) (qneg (qadd (qmul (qinv' x) (qinv' a)) α))) := by
          unfold qsub; rat_ring
        generalize qmul (qsub x a) (qneg (qadd (qmul (qinv' x) (qinv' a)) α)) = P at *
        generalize qmul (qsub a x) (qadd (qmul (qinv' x) (qinv' a)) α) = P' at *
        unfold qsub at *; rat_linarith
    | inr h =>
        have ab' : ZTrig.Ab (qsub a x) ι := ⟨by unfold qsub; rat_linarith, by unfold qsub at *; rat_linarith⟩
        obtain ⟨q1, q2⟩ := ZTrig.mul_abs ab' Ka
        rw [hIL] at q1 q2
        generalize qmul (qsub a x) (qadd (qmul (qinv' x) (qinv' a)) α) = P at *
        unfold qsub at *; rat_linarith
  have upper : qle (qsub (qinv' x) (qmul α x)) (qadd (qsub (qinv' b) (qmul α b)) IL) := by
    cases qle_total x b with
    | inr h =>
        have ab' : ZTrig.Ab (qsub b x) ι := ⟨by unfold qsub at *; rat_linarith, by unfold qsub; rat_linarith⟩
        obtain ⟨q1, q2⟩ := ZTrig.mul_abs ab' Kb
        rw [hIL] at q1 q2
        generalize qmul (qsub b x) (qadd (qmul (qinv' x) (qinv' b)) α) = P at *
        unfold qsub at *; rat_linarith
    | inl h =>
        cases qle_total a x with
        | inl h' =>
            have ixa := inv_ge_of_le ha h'
            have m1 := qmul_nonneg (show qle qzero (qsub (qinv' a) (qinv' x)) by unfold qsub; rat_linarith) ib0
            have pp := qmul_nonneg (show qle qzero (qsub b x) by unfold qsub; rat_linarith)
              (show qle qzero (qneg (qadd (qmul (qinv' x) (qinv' b)) α)) by
                have e : qEq (qmul (qinv' b) (qinv' a)) (qmul (qinv' a) (qinv' b)) := by rat_ring
                unfold qsub at m1; rat_linarith)
            have e : qEq (qmul (qsub b x) (qadd (qmul (qinv' x) (qinv' b)) α)) (qneg (qmul (qsub b x) (qneg (qadd (qmul (qinv' x) (qinv' b)) α)))) := by
              rat_ring
            generalize qmul (qsub b x) (qneg (qadd (qmul (qinv' x) (qinv' b)) α)) = P at *
            generalize qmul (qsub b x) (qadd (qmul (qinv' x) (qinv' b)) α) = P' at *
            unfold qsub at *; rat_linarith
        | inr h' =>
            have ab' : ZTrig.Ab (qsub a x) ι := ⟨by unfold qsub; rat_linarith, by unfold qsub at *; rat_linarith⟩
            obtain ⟨q1, q2⟩ := ZTrig.mul_abs ab' Ka
            rw [hIL] at q1 q2
            generalize qmul (qsub a x) (qadd (qmul (qinv' x) (qinv' a)) α) = P at *
            unfold qsub at *; rat_linarith
  have e0 := qeps_nonneg k
  show ZTrig.Ab (qsub (qsub (qinv' x) (qmul α x)) ζ) (qadd (qadd δ IL) (qeps k))
  clear db da dab Kb Ka hix hia hib
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem eseq_nonneg (x : QExpr) (n : Nat) : qle qzero (eseq x (n + 1)) := by
  cases qle.decidable qzero x with
  | isTrue h => rw [eseq_pos h]; exact S_nonneg h (n + 1)
  | isFalse h =>
      rw [eseq_neg h]
      have hn : qle qzero (qneg x) := by
        cases qle_total qzero x with
        | inl h' => exact absurd h' h
        | inr h' => rat_linarith
      have s1 := S_ge_one hn n
      exact qinv'_nonneg_of_pos (qlt_iff_le_not_le.mpr ⟨by have := qle_of_qlt qone_pos; rat_linarith,
        fun z => (qlt_iff_le_not_le.mp qone_pos).2 (by rat_linarith)⟩)

/-- One case of the remainder at a time: `x ≥ a`, the lower side. -/
theorem exp_lo_ge {a x A X α t la ε D : QExpr} (hax : qle a x) (hxD : qle (qsub x a) D)
    (hs : qle (qmul (qsub x a) (qsub A t)) (qsub X A)) (hA : qle (qsub la ε) A) (hα : qle α la)
    (ε0 : qle qzero ε) (t0 : qle qzero t) :
    qle (qsub (qsub (qsub la (qmul α a)) ε) (qmul D (qadd ε t))) (qsub X (qmul α x)) := by
  have p1 := qmul_nonneg (show qle qzero (qsub x a) by unfold qsub; rat_linarith)
    (show qle qzero (qadd (qsub (qsub A t) α) (qadd ε t)) by unfold qsub at *; rat_linarith)
  have p2 := qmul_nonneg (show qle qzero (qsub D (qsub x a)) by unfold qsub at *; rat_linarith)
    (show qle qzero (qadd ε t) by rat_linarith)
  unfold qsub at *; rat_linarith

theorem exp_lo_lt {a x A X α ι la ua ε Aα : QExpr} (hxa : qle x a) (hι : qle (qsub a x) ι)
    (hs : qle (qsub A X) (qmul (qsub a x) A)) (hA : qle (qsub la ε) A) (hA' : qle A (qadd ua ε))
    (hAα : ZTrig.Ab α Aα) (ε1 : qle ε qone) (A0 : qle qzero A) :
    qle (qsub (qsub (qsub la (qmul α a)) ε) (qmul ι (qadd (qadd ua qone) Aα))) (qsub X (qmul α x)) := by
  have p1 := qmul_nonneg (show qle qzero (qsub ι (qsub a x)) by unfold qsub at *; rat_linarith) A0
  have ab : ZTrig.Ab (qsub a x) ι := ⟨by unfold qsub at *; rat_linarith, hι⟩
  obtain ⟨m1, m2⟩ := ZTrig.mul_abs ab hAα
  have ι0 : qle qzero ι := by unfold qsub at *; rat_linarith
  have p2 := qmul_nonneg ι0 (show qle qzero (qsub (qadd ua qone) A) by unfold qsub at *; rat_linarith)
  have e : qEq (qmul ι (qadd (qadd ua qone) Aα)) (qadd (qmul ι (qadd ua qone)) (qmul ι Aα)) := by rat_ring
  unfold qsub at *; rat_linarith

theorem exp_up_le {b x Bv X α t ub ε D σ : QExpr} (hxb : qle x b) (hbD : qle (qsub b x) D)
    (hs : qle (qmul (qsub b x) (qsub X t)) (qsub Bv X)) (hB : qle Bv (qadd ub ε)) (hX : qle (qsub α σ) (qsub X t))
    (σ0 : qle qzero σ) :
    qle (qsub X (qmul α x)) (qadd (qadd (qsub ub (qmul α b)) ε) (qmul D σ)) := by
  have p1 := qmul_nonneg (show qle qzero (qsub b x) by unfold qsub; rat_linarith)
    (show qle qzero (qadd (qsub (qsub X t) α) σ) by unfold qsub at *; rat_linarith)
  have p2 := qmul_nonneg (show qle qzero (qsub D (qsub b x)) by unfold qsub at *; rat_linarith) σ0
  unfold qsub at *; rat_linarith

theorem exp_up_gt {b x Bv X α ι ub ε Aα : QExpr} (hbx : qle b x) (hι : qle (qsub x b) ι) (ιh : qle ι ZTrig.half)
    (hs : qle (qsub X Bv) (qmul (qsub x b) X)) (hB : qle Bv (qadd ub ε)) (hAα : ZTrig.Ab α Aα) (ε1 : qle ε qone)
    (X0 : qle qzero X) (B0 : qle qzero Bv) :
    qle (qsub X (qmul α x)) (qadd (qadd (qsub ub (qmul α b)) ε) (qmul ι (qadd (qadd (qadd ub qone) (qadd ub qone)) Aα))) := by
  obtain ⟨hh, h0⟩ := ZTrig.half_facts
  have ι0 : qle qzero ι := by unfold qsub at *; rat_linarith
  have p1 := qmul_nonneg (show qle qzero (qsub ι (qsub x b)) by unfold qsub at *; rat_linarith) X0
  -- X ≤ 2 Bv: X − ιX ≤ Bv and ι ≤ 1/2
  have p2 := qmul_nonneg (show qle qzero (qsub ZTrig.half ι) by unfold qsub; rat_linarith) X0
  have hX : qle X (qadd Bv Bv) := by
    have e : qEq (qmul ZTrig.half X) (qmul ZTrig.half X) := qEq_refl _
    have e2 : qEq X (qadd (qmul ZTrig.half X) (qmul ZTrig.half X)) := by
      have := qmul_respects hh (qEq_refl X)
      exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
    unfold qsub at *; rat_linarith
  have ab : ZTrig.Ab (qsub x b) ι := ⟨by unfold qsub at *; rat_linarith, hι⟩
  obtain ⟨m1, m2⟩ := ZTrig.mul_abs ab hAα
  have p3 := qmul_nonneg ι0 (show qle qzero (qsub (qadd (qadd ub qone) (qadd ub qone)) X) by unfold qsub at *; rat_linarith)
  have e : qEq (qmul ι (qadd (qadd (qadd ub qone) (qadd ub qone)) Aα))
      (qadd (qmul ι (qadd (qadd ub qone) (qadd ub qone))) (qmul ι Aα)) := by rat_ring
  unfold qsub at *; rat_linarith

theorem sub_nonneg_le {L R P : QExpr} (h : qle L R) (hp : qle qzero P) : qle (qsub L P) R := by
  unfold qsub; rat_linarith

theorem exp_lo_fix {la α a ε ι ua Ua Aα D t V : QExpr}
    (r : qle (qsub (qsub (qsub la (qmul α a)) ε) (qmul ι (qadd (qadd ua qone) Aα))) V)
    (p : qle qzero (qmul ι (qsub Ua ua))) (p2 : qle qzero (qmul D (qadd ε t))) :
    qle (qsub (qsub (qsub (qsub la (qmul α a)) ε) (qmul D (qadd ε t))) (qmul ι (qadd (qadd Ua qone) Aα))) V := by
  unfold qsub at *; rat_linarith

theorem exp_hX_ge {A X x a α t la ε D ι Ua : QExpr} (s : qle (qmul (qsub x a) (qsub A t)) (qsub X A))
    (A0 : qle qzero A) (hxD : qle (qsub x a) D) (hax : qle a x) (A1 : qle (qsub la ε) A) (hα : qle α la)
    (t0 : qle qzero t) (ι0 : qle qzero ι) (U0 : qle qzero (qadd Ua qone)) :
    qle (qsub α (qadd (qadd ε (qmul (qadd D qone) t)) (qmul ι (qadd Ua qone)))) (qsub X t) := by
  have p := qmul_nonneg (show qle qzero (qsub x a) by unfold qsub; rat_linarith) A0
  have p2 := qmul_nonneg (show qle qzero (qsub D (qsub x a)) by unfold qsub at *; rat_linarith) t0
  have p3 := qmul_nonneg ι0 U0
  unfold qsub at *; rat_linarith

theorem exp_hX_lt {A X x a α t la ua ε D ι Ua : QExpr} (s : qle (qsub A X) (qmul (qsub a x) A))
    (hι : qle (qsub a x) ι) (hxa : qle x a) (A0 : qle qzero A) (A1 : qle (qsub la ε) A) (A2 : qle A (qadd ua ε))
    (hα : qle α la) (hU : qle ua Ua) (ε1 : qle ε qone) (t0 : qle qzero t) (D0 : qle qzero D) (ι0 : qle qzero ι) :
    qle (qsub α (qadd (qadd ε (qmul (qadd D qone) t)) (qmul ι (qadd Ua qone)))) (qsub X t) := by
  have p := qmul_nonneg (show qle qzero (qsub ι (qsub a x)) by unfold qsub at *; rat_linarith) A0
  have p2 := qmul_nonneg ι0 (show qle qzero (qsub (qadd Ua qone) A) by unfold qsub at *; rat_linarith)
  have p3 := qmul_nonneg (show qle qzero (qadd D qone) by rat_linarith) t0
  have p4 := qmul_nonneg D0 t0
  unfold qsub at *; rat_linarith

theorem exp_up_fix {X α x ub b ε ι Ub Aα D σ : QExpr}
    (r : qle (qsub X (qmul α x)) (qadd (qadd (qsub ub (qmul α b)) ε) (qmul ι (qadd (qadd (qadd ub qone) (qadd ub qone)) Aα))))
    (p : qle qzero (qmul ι (qsub Ub ub))) (p2 : qle qzero (qmul D σ)) :
    qle (qsub X (qmul α x)) (qadd (qadd (qadd (qsub ub (qmul α b)) ε) (qmul D σ)) (qmul ι (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα))) := by
  unfold qsub at *; rat_linarith

theorem exp_up_fix2 {X α x ub b ε ι Ub Aα D σ : QExpr}
    (r : qle (qsub X (qmul α x)) (qadd (qadd (qsub ub (qmul α b)) ε) (qmul D σ)))
    (p : qle qzero (qmul ι (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα))) :
    qle (qsub X (qmul α x)) (qadd (qadd (qadd (qsub ub (qmul α b)) ε) (qmul D σ)) (qmul ι (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα))) := by
  unfold qsub at *; rat_linarith

/-- The assembly: lower and upper sides, the brackets' ends, `ε` and `t` small. -/
theorem exp_assemble {V ζ δ la α a ub b ε t ι D Ua Ub Aα ek ek1 : QExpr}
    (lower : qle (qsub (qsub (qsub (qsub la (qmul α a)) ε) (qmul D (qadd ε t))) (qmul ι (qadd (qadd Ua qone) Aα))) V)
    (upper : qle V (qadd (qadd (qadd (qsub ub (qmul α b)) ε)
        (qmul D (qadd (qadd ε (qmul (qadd D qone) t)) (qmul ι (qadd Ua qone)))))
        (qmul ι (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα))))
    (hlo : qle (qsub ζ δ) (qsub la (qmul α a))) (hhi : qle (qsub ub (qmul α b)) (qadd ζ δ))
    (sc : qle (qmul ε (qadd (qmul (qadd D qone) (qadd D qone)) (qadd D qone))) ek1) (es : qEq (qadd ek1 ek1) ek)
    (tε : qle t ε) (t0 : qle qzero t) (D0 : qle qzero D) (ε0 : qle qzero ε)
    (q1 : qle qzero (qmul ι (qadd (qadd Ua qone) Aα))) (q2 : qle qzero (qmul ι (qmul D (qadd Ua qone))))
    (q3 : qle qzero (qmul ι (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα))) :
    ZTrig.Ab (qsub V ζ) (qadd (qadd δ (qmul ι (qadd (qadd (qadd (qadd Ua qone) Aα) (qmul D (qadd Ua qone)))
      (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα)))) ek) := by
  have pt := qmul_nonneg (qmul_nonneg D0 (show qle qzero (qadd D qone) by have := qle_of_qlt qone_pos; rat_linarith))
    (show qle qzero (qsub ε t) by unfold qsub; rat_linarith)
  have pt2 := qmul_nonneg D0 (show qle qzero (qsub ε t) by unfold qsub; rat_linarith)
  have pe := qmul_nonneg ε0 (qmul_nonneg D0 D0)
  have pe2 := qmul_nonneg ε0 D0
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `exp` ON `[a, b]`, THE SLOPE AT `a` (`α ≤ e^a`'s lower bracket): the remainder `e^x − α x` increases, between its
values at `a` and at `b` (the brackets certified by `ExpCert`). -/
theorem rem_exp {a b α ζ δ la ua lb ub za za' zb zb' : QExpr} (hab : qle a b)
    (cla : ExpCert a la za) (cua : ExpCert a za' ua) (clb : ExpCert b lb zb) (cub : ExpCert b zb' ub)
    (hα : qle α la) (hlo : qle (qsub ζ δ) (qsub la (qmul α a))) (hhi : qle (qsub ub (qmul α b)) (qadd ζ δ)) :
    Rem (fun n x => eseq x n) a b α ζ δ := by
  obtain ⟨Aα, Aα0, hAα, _⟩ := abs_wit α
  obtain ⟨Ua, Ua0, hUa, _⟩ := abs_wit ua
  obtain ⟨Ub, Ub0, hUb, _⟩ := abs_wit ub
  obtain ⟨hh, h0⟩ := ZTrig.half_facts
  have hp := half_pos
  obtain ⟨M, _, M0, _, ma, mb, _, _⟩ := bound4 a b a b
  have o := qle_of_qlt qone_pos
  have R0 : qle qzero (qadd M qone) := by rat_linarith
  obtain ⟨K, hg⟩ := good_exists (qadd M qone)
  have D0 : qle qzero (qadd (qsub b a) qone) := by unfold qsub; rat_linarith
  generalize hD : qadd (qsub b a) qone = D at *
  have L20 : qle qzero (qadd (qadd (qadd (qadd Ua qone) Aα) (qmul D (qadd Ua qone))) (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα)) := by
    have := qmul_nonneg D0 (show qle qzero (qadd Ua qone) by rat_linarith); rat_linarith
  refine ⟨_, ZTrig.half, L20, hp, fun k => ?_⟩
  have C0 : qle qzero (qadd (qmul (qadd D qone) (qadd D qone)) (qadd D qone)) := by
    have := qmul_nonneg (show qle qzero (qadd D qone) by rat_linarith) (show qle qzero (qadd D qone) by rat_linarith)
    rat_linarith
  obtain ⟨Bc, hBc⟩ := eps_scaled (C := qadd (qmul (qadd D qone) (qadd D qone)) (qadd D qone)) C0
  have EA : Ev (fun n => eseq a n) la ua := Ev_exp (x := fun _ => a) (Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩))
    ⟨za, cla⟩ ⟨za', cua⟩
  have EB : Ev (fun n => eseq b n) lb ub := Ev_exp (x := fun _ => b) (Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩))
    ⟨zb, clb⟩ ⟨zb', cub⟩
  obtain ⟨N1, h1⟩ := EA (k + 1 + Bc)
  obtain ⟨N2, h2⟩ := EB (k + 1 + Bc)
  obtain ⟨Nt, _, ht⟩ := tm_small R0 hg (k + 1 + Bc)
  refine ⟨N1 + N2 + Nt + 1, fun n hn x ι ι0 ιh hxa hxb => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ m =>
  have hm : N1 + N2 + Nt ≤ m := Nat.le_of_succ_le_succ hn
  obtain ⟨A1, A2⟩ := h1 (m + 1) (Nat.le_trans (Nat.le_add_right N1 (N2 + Nt)) (by
    rw [← Nat.add_assoc]; exact Nat.le_trans hm (Nat.le_succ m)))
  obtain ⟨B1, B2⟩ := h2 (m + 1) (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right (N1 + N2) Nt))
    (Nat.le_trans hm (Nat.le_succ m)))
  have tt := ht m (Nat.le_trans (Nat.le_add_left Nt (N1 + N2)) hm)
  have t0 := tm_nonneg R0 m
  have ε0 := qeps_nonneg (k + 1 + Bc)
  have ε1 := eps_le_one (k + 1 + Bc)
  have A0 := eseq_nonneg a m
  have X0 := eseq_nonneg x m
  have Bv0 := eseq_nonneg b m
  -- |a|, |b|, |x| ≤ M + 1
  obtain ⟨ma1, ma2⟩ := ma
  obtain ⟨mb1, mb2⟩ := mb
  have ra : qclose a qzero (qadd M qone) := ⟨by unfold qsub at *; rat_linarith, by unfold qsub at *; rat_linarith⟩
  have rb : qclose b qzero (qadd M qone) := ⟨by unfold qsub at *; rat_linarith, by unfold qsub at *; rat_linarith⟩
  have rx : qclose x qzero (qadd M qone) := ⟨by unfold qsub at *; rat_linarith, by unfold qsub at *; rat_linarith⟩
  have hxD : qle (qsub x a) D := by rw [← hD]; unfold qsub at *; rat_linarith
  have hbD : qle (qsub b x) D := by rw [← hD]; unfold qsub at *; rat_linarith
  have tε : qle (tm (qadd M qone) m) (qeps (k + 1 + Bc)) := by rat_linarith
  obtain ⟨u1, u2⟩ := hUa
  obtain ⟨v1, v2⟩ := hUb
  -- LOWER
  have lower : qle (qsub (qsub (qsub (qsub la (qmul α a)) (qeps (k + 1 + Bc))) (qmul D (qadd (qeps (k + 1 + Bc)) (tm (qadd M qone) m))))
      (qmul ι (qadd (qadd Ua qone) Aα))) (qsub (eseq x (m + 1)) (qmul α x)) := by
    cases qle_total a x with
    | inl h =>
        exact sub_nonneg_le (exp_lo_ge h hxD (E_slope h ra rx m).1 A1 hα ε0 t0)
          (qmul_nonneg ι0 (show qle qzero (qadd (qadd Ua qone) Aα) by rat_linarith))
    | inr h =>
        have hι : qle (qsub a x) ι := by unfold qsub at *; rat_linarith
        exact exp_lo_fix (exp_lo_lt h hι (E_slope h rx ra m).2 A1 A2 hAα ε1 A0)
          (qmul_nonneg ι0 (show qle qzero (qsub Ua ua) by unfold qsub; rat_linarith))
          (qmul_nonneg D0 (show qle qzero (qadd (qeps (k + 1 + Bc)) (tm (qadd M qone) m)) by rat_linarith))
  -- UPPER
  have σ0 : qle qzero (qadd (qadd (qeps (k + 1 + Bc)) (qmul (qadd D qone) (tm (qadd M qone) m))) (qmul ι (qadd Ua qone))) := by
    have := qmul_nonneg (show qle qzero (qadd D qone) by rat_linarith) t0
    have := qmul_nonneg ι0 (show qle qzero (qadd Ua qone) by rat_linarith); rat_linarith
  have upper : qle (qsub (eseq x (m + 1)) (qmul α x))
      (qadd (qadd (qadd (qsub ub (qmul α b)) (qeps (k + 1 + Bc)))
        (qmul D (qadd (qadd (qeps (k + 1 + Bc)) (qmul (qadd D qone) (tm (qadd M qone) m))) (qmul ι (qadd Ua qone)))))
        (qmul ι (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα))) := by
    cases qle_total x b with
    | inl h =>
        have hX : qle (qsub α (qadd (qadd (qeps (k + 1 + Bc)) (qmul (qadd D qone) (tm (qadd M qone) m))) (qmul ι (qadd Ua qone))))
            (qsub (eseq x (m + 1)) (tm (qadd M qone) m)) := by
          cases qle_total a x with
          | inl h' => exact exp_hX_ge (E_slope h' ra rx m).1 A0 hxD h' A1 hα t0 ι0 (by rat_linarith)
          | inr h' =>
              have hι : qle (qsub a x) ι := by unfold qsub at *; rat_linarith
              exact exp_hX_lt (E_slope h' rx ra m).2 hι h' A0 A1 A2 hα (by rat_linarith) ε1 t0 D0 ι0
        exact exp_up_fix2 (exp_up_le h hbD (E_slope h rx rb m).1 B2 hX σ0)
          (qmul_nonneg ι0 (show qle qzero (qadd (qadd (qadd Ub qone) (qadd Ub qone)) Aα) by rat_linarith))
    | inr h =>
        have hι : qle (qsub x b) ι := by unfold qsub at *; rat_linarith
        exact exp_up_fix (exp_up_gt h hι ιh (E_slope h rb rx m).2 B2 hAα ε1 X0 Bv0)
          (qmul_nonneg ι0 (show qle qzero (qsub Ub ub) by unfold qsub; rat_linarith)) (qmul_nonneg D0 σ0)
  show ZTrig.Ab (qsub (qsub (eseq x (m + 1)) (qmul α x)) ζ) _
  exact exp_assemble lower upper hlo hhi (hBc (k + 1)) (qeps_succ_add k) tε t0 D0 ε0
    (qmul_nonneg ι0 (by rat_linarith)) (qmul_nonneg ι0 (qmul_nonneg D0 (by rat_linarith)))
    (qmul_nonneg ι0 (by rat_linarith))

/-! ## The affine reading -/

/-- THE KERNEL'S AFFINE READING (`zaffine.read`), step by step: constants, a point variable, a basis element (a variable
of the box, or a subtree read plainly — `opaque`), `+`, `−`, `×`, the grid rounding (`widen`), and a nonlinear step
`φ` with its min-range remainder (`1/x`: `rem_recip_a/b`; `exp`: `rem_exp`). -/
inductive AffR (E : Env) (B : Box QExpr) : (Nat → Point QExpr → QExpr) → Form → Prop where
  | const (v : QExpr) : AffR E B (fun _ _ => v) ⟨v, fun _ => qzero, qzero⟩
  | point {i : Nat} {v : QExpr} : qEq (B i).1 v → qEq (B i).2 v → AffR E B (fun _ p => p i) ⟨v, fun _ => qzero, qzero⟩
  | basis {j : Nat} : j < E.S → AffR E B (fun n p => evalN n p (E.Γ j)) ⟨E.m j, upd (fun _ => qzero) j qone, qzero⟩
  | add {f g : Nat → Point QExpr → QExpr} {F G : Form} : AffR E B f F → AffR E B g G →
      AffR E B (fun n p => qadd (f n p) (g n p)) ⟨qadd F.c G.c, fun j => qadd (F.s j) (G.s j), qadd F.e G.e⟩
  | sub {f g : Nat → Point QExpr → QExpr} {F G : Form} : AffR E B f F → AffR E B g G →
      AffR E B (fun n p => qsub (f n p) (g n p)) ⟨qsub F.c G.c, fun j => qsub (F.s j) (G.s j), qadd F.e G.e⟩
  | mul {f g : Nat → Point QExpr → QExpr} {F G : Form} {cf cg e : QExpr} {ax ay : Nat → QExpr} :
      AffR E B f F → AffR E B g G → qle qzero F.e → qle qzero G.e → ZTrig.Ab F.c cf → ZTrig.Ab G.c cg →
      (∀ j, j < E.S → ZTrig.Ab (F.s j) (ax j)) → (∀ j, j < E.S → ZTrig.Ab (G.s j) (ay j)) →
      qle (qadd (qadd (qmul cf G.e) (qmul cg F.e))
        (qmul (qadd (ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S) F.e) (qadd (ZTrig.bs (fun j => qmul (ay j) (E.r j)) E.S) G.e))) e →
      AffR E B (fun n p => qmul (f n p) (g n p)) ⟨qmul F.c G.c, fun j => qadd (qmul G.c (F.s j)) (qmul F.c (G.s j)), e⟩
  | widen {f : Nat → Point QExpr → QExpr} {F G : Form} {w0 : QExpr} {w : Nat → QExpr} : AffR E B f F →
      ZTrig.Ab (qsub F.c G.c) w0 → (∀ j, j < E.S → ZTrig.Ab (qsub (F.s j) (G.s j)) (w j)) →
      qle (qadd (qadd F.e w0) (ZTrig.bs (fun j => qmul (w j) (E.r j)) E.S)) G.e → AffR E B f G
  | nl {f : Nat → Point QExpr → QExpr} {F : Form} {φ : Nat → QExpr → QExpr} {a b α ζ δ aα e : QExpr}
      {ax : Nat → QExpr} : AffR E B f F → qle qzero F.e → (∀ j, j < E.S → ZTrig.Ab (F.s j) (ax j)) →
      Rem φ a b α ζ δ → qle a (qsub F.c (qadd (ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S) F.e)) →
      qle (qadd F.c (qadd (ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S) F.e)) b →
      ZTrig.Ab α aα → qle (qadd (qmul aα F.e) δ) e →
      AffR E B (fun n p => φ n (f n p)) ⟨qadd (qmul α F.c) ζ, fun j => qmul α (F.s j), e⟩

theorem aff_enc {E : Env} {B : Box QExpr} (hr : ∀ j, j < E.S → qle qzero (E.r j)) :
    ∀ {f : Nat → Point QExpr → QExpr} {F : Form}, AffR E B f F → Enc E B f F := by
  intro f F h
  induction h with
  | const v => exact enc_const E B v
  | point h1 h2 => exact enc_point E B h1 h2
  | basis hj => exact enc_basis E B hj
  | add _ _ ih1 ih2 => exact enc_add ih1 ih2
  | sub _ _ ih1 ih2 => exact enc_sub ih1 ih2
  | mul _ _ fe ge hcf hcg hax hay he ih1 ih2 => exact enc_mul ih1 ih2 hr fe ge hcf hcg hax hay he
  | widen _ hc hs he ih => exact enc_widen ih hc hs he
  | nl _ fe hax hrem ha hb hα he ih => exact enc_rem ih hr fe hax hrem ha hb hα he

/-- THE AFFINE READING OF AN EXPRESSION IS SOUND: its basis read in its boxes, the value of `e` at every point of the
box is eventually in `[c − R, c + R]`, `R ≥ Σ |s_j|·r_j + e`. -/
theorem aff_sound {E : Env} {B : Box QExpr} {e : G} {F : Form} (hr : ∀ j, j < E.S → qle qzero (E.r j))
    (h : AffR E B (fun n p => evalN n p e) F)
    (hb : ∀ j, j < E.S → BoxEv B (E.Γ j) (qsub (E.m j) (E.r j)) (qadd (E.m j) (E.r j)))
    {a : Nat → QExpr} (ha : ∀ j, j < E.S → ZTrig.Ab (F.s j) (a j)) {R : QExpr}
    (hR : qle (qadd (ZTrig.bs (fun j => qmul (a j) (E.r j)) E.S) F.e) R) :
    BoxEv B e (qsub F.c R) (qadd F.c R) :=
  fun p hp => enc_sound (aff_enc hr h) hb ha hR p hp

/-- Two box bounds: their meet (the kernel meets the plain reading with the affine one). -/
theorem boxEv_meet {B : Box QExpr} {e : G} {l1 h1 l2 h2 l h : QExpr} (r1 : BoxEv B e l1 h1) (r2 : BoxEv B e l2 h2)
    (hl : qle l l1 ∨ qle l l2) (hh : qle h1 h ∨ qle h2 h) : BoxEv B e l h := fun p hp k => by
  obtain ⟨N1, a⟩ := r1 p hp k
  obtain ⟨N2, b⟩ := r2 p hp k
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := a n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  obtain ⟨b1, b2⟩ := b n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  unfold qsub at *
  refine ⟨?_, ?_⟩
  · cases hl with
    | inl h' => rat_linarith
    | inr h' => rat_linarith
  · cases hh with
    | inl h' => rat_linarith
    | inr h' => rat_linarith

/-! ## ln's remainder -/

/-- `α ≤ 1/b` from `α·b ≤ 1`, `b > 0`. -/
theorem le_inv_of_mul {α b : QExpr} (hb : qlt qzero b) (h : qle (qmul α b) qone) : qle α (qinv' b) := by
  have ib0 := qinv'_nonneg_of_pos hb
  have c := qmul_inv'_cancel (ne_zero_of_lt hb)
  have m := ZExp.scale h ib0
  have e : qEq (qmul (qmul α b) (qinv' b)) (qmul α (qmul b (qinv' b))) := by rat_ring
  have e2 := qmul_respects (qEq_refl α) c
  have o : qEq (qmul qone (qinv' b)) (qinv' b) := by rat_ring
  generalize qmul (qmul α b) (qinv' b) = P at *
  generalize qmul α (qmul b (qinv' b)) = P' at *
  generalize qmul qone (qinv' b) = Q at *
  have o2 : qEq (qmul α qone) α := by rat_ring
  generalize qmul α qone = R at *
  rat_linarith

/-- Lower side, `x ≥ a`: `r(x) ≥ r(a) − e − (x − a)·(x − b)⁺/c²`, written with the bound `(x − a)·(ix − α) ≥ −K`. -/
theorem ln_low_case {lx la x a α ix e K : QExpr} (ch : qle (qsub (qmul (qsub x a) ix) e) (qsub lx la))
    (hK : qle (qneg K) (qmul (qsub x a) (qsub ix α))) :
    qle (qsub (qsub (qsub la (qmul α a)) e) K) (qsub lx (qmul α x)) := by
  unfold qsub at *; rat_linarith

theorem ln_high_case {lx lb x b α ib e K : QExpr} (ch : qle (qsub (qmul (qsub b x) ib) e) (qsub lb lx))
    (hK : qle (qneg K) (qmul (qsub b x) (qsub ib α))) :
    qle (qsub lx (qmul α x)) (qadd (qadd (qsub lb (qmul α b)) e) K) := by
  unfold qsub at *; rat_linarith

/-- `ln` ON `[a, b]`, `a > 0`, THE SLOPE AT `b` (`α·b ≤ 1`): the remainder `ln x − α x` increases; its ends bracketed
by `ExpCert` (`e^La ≤ a`, `e^Hb ≥ b`). -/
theorem rem_ln {a b α ζ δ La Hb zl wl wh zh : QExpr} (ha : qlt qzero a) (hab : qle a b) (α0 : qle qzero α)
    (hα : qle (qmul α b) qone) (cl : ExpCert La zl wl) (hwl : qle wl a) (ch : ExpCert Hb wh zh) (hwh : qle b wh)
    (hlo : qle (qsub ζ δ) (qsub La (qmul α a))) (hhi : qle (qsub Hb (qmul α b)) (qadd ζ δ)) :
    Rem (fun n x => lnseq x n) a b α ζ δ := by
  obtain ⟨hh, h0⟩ := ZTrig.half_facts
  have cp : qlt qzero (qmul a ZTrig.half) := qmul_pos ha half_pos
  have ac : qEq a (qadd (qmul a ZTrig.half) (qmul a ZTrig.half)) := by
    have := qmul_respects (qEq_refl a) hh
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
  have c0 := qle_of_qlt cp
  have a0 := qle_of_qlt ha
  have bp : qlt qzero b := qlt_iff_le_not_le.mpr ⟨qle_trans a0 hab, fun h => (qlt_iff_le_not_le.mp ha).2 (qle_trans hab h)⟩
  have ic0 := qinv'_nonneg_of_pos cp
  have αb := le_inv_of_mul bp hα
  have Cb0 : qle qzero (qadd b a) := by rat_linarith
  refine ⟨qadd (qmul (qadd b a) (qmul (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))))
      (qadd (qinv' (qmul a ZTrig.half)) (qinv' (qmul a ZTrig.half))), qmul a ZTrig.half,
    by have := qmul_nonneg Cb0 (qmul_nonneg ic0 ic0); rat_linarith, cp, fun k => ?_⟩
  have EA : Ev (fun n => lnseq a n) La Hb := Ev_ln (y := fun _ => a) (Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩))
    ha cl hwl ch (qle_trans hab hwh)
  have EB : Ev (fun n => lnseq b n) La Hb := Ev_ln (y := fun _ => b) (Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩))
    bp cl (qle_trans hwl hab) ch hwh
  obtain ⟨N1, h1⟩ := EA (k + 2)
  obtain ⟨N2, h2⟩ := EB (k + 2)
  obtain ⟨N3, h3⟩ := ZLnStep.chord2 cp Cb0 (k + 2)
  refine ⟨N1 + N2 + N3, fun n hn x ι ι0 ιc hxa hxb => ?_⟩
  obtain ⟨A1, _⟩ := h1 n (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N3)) hn)
  obtain ⟨_, B2⟩ := h2 n (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N3)) hn)
  have hc := h3 n (Nat.le_trans (Nat.le_add_left N3 (N1 + N2)) hn)
  have xc : qle (qmul a ZTrig.half) x := by unfold qsub at hxa; rat_linarith
  have xC : qle x (qadd b a) := by rat_linarith
  have ac' : qle (qmul a ZTrig.half) a := by rat_linarith
  have bC : qle b (qadd b a) := by rat_linarith
  have bc : qle (qmul a ZTrig.half) b := qle_trans ac' hab
  have xp : qlt qzero x := qlt_iff_le_not_le.mpr ⟨qle_trans c0 xc, fun h => (qlt_iff_le_not_le.mp cp).2 (qle_trans xc h)⟩
  obtain ⟨ix0, ixc⟩ := ZTrig.inv_bound cp xc
  obtain ⟨ia0, iac⟩ := ZTrig.inv_bound cp ac'
  obtain ⟨ib0, ibc⟩ := ZTrig.inv_bound cp bc
  have e0 := qeps_nonneg (k + 2)
  have es := qeps_succ_add k
  have es1 := qeps_succ_add (k + 1)
  have ιIC := qmul_nonneg ι0 ic0
  have IC2 := qmul_nonneg ic0 ic0
  generalize hic : qinv' (qmul a ZTrig.half) = ic at *
  -- LOWER: r(x) ≥ r(a) − e − ι(Cb/c² + 2/c)
  have lower : qle (qsub (qsub (qsub (lnseq a n) (qmul α a)) (qeps (k + 2)))
      (qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic)))) (qsub (lnseq x n) (qmul α x)) := by
    have bnd : qle qzero (qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic))) :=
      qmul_nonneg ι0 (by have := qmul_nonneg Cb0 IC2; rat_linarith)
    cases qle_total a x with
    | inl h =>
        have c1 := (hc a x ac' h xC).1
        have K : qle (qneg (qmul (qmul (qadd b a) ι) (qmul ic ic))) (qmul (qsub x a) (qsub (qinv' x) α)) := by
          cases qle_total x b with
          | inl h' =>
              have ixb := ZAffine.inv_ge_of_le xp h'
              have := qmul_nonneg (show qle qzero (qsub x a) by unfold qsub; rat_linarith)
                (show qle qzero (qsub (qinv' x) α) by unfold qsub; rat_linarith)
              have := qmul_nonneg (qmul_nonneg Cb0 ι0) IC2
              rat_linarith
          | inr h' =>
              have dx := ZLnStep.inv_diff (ne_zero_of_lt xp) (ne_zero_of_lt bp)
              have m := ZLnStep.mul_le4 (show qle qzero (qsub x a) by unfold qsub; rat_linarith)
                (show qle qzero (qsub x b) by unfold qsub; rat_linarith) ix0 ib0
                (show qle (qsub x a) (qadd b a) by unfold qsub; rat_linarith)
                (show qle (qsub x b) ι by unfold qsub at *; rat_linarith) ixc ibc
              have p := qmul_nonneg (show qle qzero (qsub x a) by unfold qsub; rat_linarith)
                (show qle qzero (qsub (qinv' b) α) by unfold qsub; rat_linarith)
              have e1 : qEq (qmul (qsub x a) (qsub (qinv' x) α))
                  (qadd (qmul (qsub x a) (qsub (qinv' b) α)) (qneg (qmul (qmul (qsub x a) (qsub x b)) (qmul (qinv' x) (qinv' b))))) := by
                have := qmul_respects (qEq_refl (qsub x a)) dx
                have e2 : qEq (qmul (qsub x a) (qsub (qinv' x) α))
                    (qadd (qmul (qsub x a) (qsub (qinv' x) (qinv' b))) (qmul (qsub x a) (qsub (qinv' b) α))) := by unfold qsub; rat_ring
                have e3 : qEq (qmul (qsub x a) (qmul (qsub b x) (qmul (qinv' x) (qinv' b))))
                    (qneg (qmul (qmul (qsub x a) (qsub x b)) (qmul (qinv' x) (qinv' b)))) := by unfold qsub; rat_ring
                exact qEq_trans e2 (by
                  generalize qmul (qsub x a) (qsub (qinv' x) (qinv' b)) = P at *
                  generalize qmul (qsub x a) (qmul (qsub b x) (qmul (qinv' x) (qinv' b))) = P' at *
                  generalize qmul (qsub x a) (qsub (qinv' b) α) = Q at *
                  generalize qmul (qmul (qsub x a) (qsub x b)) (qmul (qinv' x) (qinv' b)) = R at *
                  exact qle_antisymm (by rat_linarith) (by rat_linarith))
              have e4 : qEq (qmul (qmul (qadd b a) ι) (qmul ic ic)) (qmul (qmul (qadd b a) ι) (qmul ic ic)) := qEq_refl _
              clear e4
              generalize qmul (qsub x a) (qsub (qinv' x) α) = T at *
              generalize qmul (qsub x a) (qsub (qinv' b) α) = Q at *
              generalize qmul (qmul (qsub x a) (qsub x b)) (qmul (qinv' x) (qinv' b)) = R at *
              generalize qmul (qmul (qadd b a) ι) (qmul ic ic) = Kv at *
              exact by rat_linarith
        have r := ln_low_case c1 K
        have e5 : qEq (qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic)))
            (qadd (qmul (qmul (qadd b a) ι) (qmul ic ic)) (qadd (qmul ι ic) (qmul ι ic))) := by rat_ring
        have iic := qmul_nonneg ι0 ic0
        unfold qsub at *
        generalize qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic)) = W at *
        generalize qmul (qmul (qadd b a) ι) (qmul ic ic) = Kv at *
        generalize qmul ι ic = I1 at *
        rat_linarith
    | inr h =>
        have c2 := (hc x a xc h (qle_trans hab bC)).2
        have m := ZLnStep.mul_le4 (show qle qzero (qsub a x) by unfold qsub; rat_linarith) (qle_of_qlt qone_pos) ix0 (qle_of_qlt qone_pos)
          (show qle (qsub a x) ι by unfold qsub at *; rat_linarith) (qle_refl qone) ixc (qle_refl qone)
        have p := qmul_nonneg α0 (show qle qzero (qsub a x) by unfold qsub; rat_linarith)
        have e1 : qEq (qmul (qmul (qsub a x) qone) (qmul (qinv' x) qone)) (qmul (qsub a x) (qinv' x)) := by rat_ring
        have e2 : qEq (qmul (qmul ι qone) (qmul ic qone)) (qmul ι ic) := by rat_ring
        have e5 : qEq (qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic)))
            (qadd (qmul (qmul (qadd b a) ι) (qmul ic ic)) (qadd (qmul ι ic) (qmul ι ic))) := by rat_ring
        have pk := qmul_nonneg (qmul_nonneg Cb0 ι0) IC2
        have iic := qmul_nonneg ι0 ic0
        unfold qsub at *
        generalize qmul (qmul (qadd a (qneg x)) qone) (qmul (qinv' x) qone) = M1 at *
        generalize qmul (qadd a (qneg x)) (qinv' x) = M2 at *
        generalize qmul (qmul ι qone) (qmul ic qone) = M3 at *
        generalize qmul ι ic = I1 at *
        generalize qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic)) = W at *
        generalize qmul (qmul (qadd b a) ι) (qmul ic ic) = Kv at *
        rat_linarith
  -- UPPER: r(x) ≤ r(b) + e + ι/c
  have upper : qle (qsub (lnseq x n) (qmul α x)) (qadd (qadd (qsub (lnseq b n) (qmul α b)) (qeps (k + 2))) (qmul ι ic)) := by
    have iic := qmul_nonneg ι0 ic0
    cases qle_total x b with
    | inl h =>
        have c1 := (hc x b xc h bC).1
        have p := qmul_nonneg (show qle qzero (qsub b x) by unfold qsub; rat_linarith)
          (show qle qzero (qsub (qinv' b) α) by unfold qsub; rat_linarith)
        have r := ln_high_case c1 (show qle (qneg qzero) (qmul (qsub b x) (qsub (qinv' b) α)) by rat_linarith)
        unfold qsub at *; rat_linarith
    | inr h =>
        have c2 := (hc b x bc h xC).2
        have m := ZLnStep.mul_le4 (show qle qzero (qsub x b) by unfold qsub; rat_linarith) (qle_of_qlt qone_pos) ib0 (qle_of_qlt qone_pos)
          (show qle (qsub x b) ι by unfold qsub at *; rat_linarith) (qle_refl qone) ibc (qle_refl qone)
        have p := qmul_nonneg α0 (show qle qzero (qsub x b) by unfold qsub; rat_linarith)
        have e1 : qEq (qmul (qmul (qsub x b) qone) (qmul (qinv' b) qone)) (qmul (qsub x b) (qinv' b)) := by rat_ring
        have e2 : qEq (qmul (qmul ι qone) (qmul ic qone)) (qmul ι ic) := by rat_ring
        unfold qsub at *
        generalize qmul (qmul (qadd x (qneg b)) qone) (qmul (qinv' b) qone) = M1 at *
        generalize qmul (qadd x (qneg b)) (qinv' b) = M2 at *
        generalize qmul (qmul ι qone) (qmul ic qone) = M3 at *
        generalize qmul ι ic = I1 at *
        rat_linarith
  -- assemble
  have pw : qle (qmul ι ic) (qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic))) := by
    have := qmul_nonneg ι0 (show qle qzero (qadd (qmul (qadd b a) (qmul ic ic)) ic) by have := qmul_nonneg Cb0 IC2; rat_linarith)
    have e : qEq (qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic)))
        (qadd (qmul ι ic) (qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) ic))) := by rat_ring
    rat_linarith
  show ZTrig.Ab (qsub (qsub (lnseq x n) (qmul α x)) ζ) _
  clear hc h1 h2
  unfold qsub at *
  generalize qmul ι (qadd (qmul (qadd b a) (qmul ic ic)) (qadd ic ic)) = W at *
  generalize qmul ι ic = I1 at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZAffine

#print axioms ZAffine.r_diff
#print axioms ZAffine.rem_recip_b
#print axioms ZAffine.rem_recip_a
#print axioms ZAffine.exp_lo_ge
#print axioms ZAffine.exp_lo_lt
#print axioms ZAffine.exp_up_le
#print axioms ZAffine.exp_up_gt
#print axioms ZAffine.rem_exp
#print axioms ZAffine.aff_enc
#print axioms ZAffine.aff_sound
#print axioms ZAffine.boxEv_meet
#print axioms ZAffine.rem_ln
