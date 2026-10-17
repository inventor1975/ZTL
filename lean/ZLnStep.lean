import ZTaylor2

/-!
# ZLnStep — the uniform step of the grid logarithm. Zero axioms.

`ln` on VR's operational reals is the grid inverse of `exp` (`ZLn.lnseq`). Its first-order step,
`ln(x + d) − ln(x) − d/x` within `ε + d²·H` uniformly for `x, x + d ≥ c > 0`, from `ZLn.ln_sigma_pt` (the grid logs'
difference between `(b − a)/E(Y + ε)` and `(b − a)/(E(X + ε) − t)`) — no mean value theorem. `ZDeriv` composes it with
the inner function (`comp_step_on`).
-/

namespace ZLnStep

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow

theorem eps_scaled' {C : QExpr} (hC : qle qzero C) : ∃ B, ∀ k, qle (qmul (qeps (k + B)) C) (qeps k) := by
  obtain ⟨B, hB1, _⟩ := qexpr_bound C
  have hc : qle C (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  refine ⟨B, fun k => ?_⟩
  have s := scale_l hc (qeps_nonneg (k + B))
  have e := qpow2_mul_eps B k
  have c := qmul_comm (qofInt (pow2 B)) (qeps (k + B))
  generalize qmul (qeps (k + B)) C = P at *; generalize qmul (qeps (k + B)) (qofInt (pow2 B)) = Q at *
  generalize qmul (qofInt (pow2 B)) (qeps (k + B)) = Q' at *
  rat_linarith

theorem inv_diff {x y : QExpr} (hx : ¬ qEq x qzero) (hy : ¬ qEq y qzero) :
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

theorem mul_le4 {x y z w X Y Z W : QExpr} (x0 : qle qzero x) (y0 : qle qzero y) (z0 : qle qzero z) (w0 : qle qzero w)
    (hx : qle x X) (hy : qle y Y) (hz : qle z Z) (hw : qle w W) :
    qle (qmul (qmul x y) (qmul z w)) (qmul (qmul X Y) (qmul Z W)) := by
  have m1 := ZExp.scale hx y0
  have Y0 := qle_trans y0 hy
  have X0 := qle_trans x0 hx
  have m2 := scale_l hy X0
  have p1 : qle (qmul x y) (qmul X Y) := qle_trans m1 m2
  have zw0 := qmul_nonneg z0 w0
  have m3 := ZExp.scale hz w0
  have Z0 := qle_trans z0 hz
  have m4 := scale_l hw Z0
  have p2 : qle (qmul z w) (qmul Z W) := qle_trans m3 m4
  have q1 := ZExp.scale p1 zw0
  have q2 := scale_l p2 (qmul_nonneg X0 Y0)
  exact qle_trans q1 q2

/-- One order (`a ≤ b`): the grid logs' difference is `(b − a)/a` within `(b − a)(b − a + γ + t)/c² + e`. -/
theorem ln_alg {a b Δ EY EX c e γ t : QExpr} (hc : qlt qzero c) (ha : qle c a) (hab : qle a b)
    (hEY1 : qle b EY) (hEY2 : qle EY (qadd b γ)) (hEX1 : qle (qsub a t) EX) (hEXc : qle c EX)
    (L : qle (qmul (qsub b a) (qinv' EY)) (qadd Δ e)) (U : qle Δ (qadd (qmul (qsub b a) (qinv' EX)) e))
    (γ0 : qle qzero γ) (t0 : qle qzero t) (e0 : qle qzero e) :
    ZTrig.Ab (qsub Δ (qmul (qsub b a) (qinv' a)))
      (qadd (qmul (qmul (qsub b a) (qadd (qadd (qsub b a) γ) t)) (qmul (qinv' c) (qinv' c))) e) := by
  have c0 := qle_of_qlt hc
  have ap : qlt qzero a := qlt_iff_le_not_le.mpr ⟨qle_trans c0 ha, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans ha h)⟩
  have EYc : qle c EY := qle_trans ha (qle_trans hab hEY1)
  have EYp : qlt qzero EY := qlt_iff_le_not_le.mpr ⟨qle_trans c0 EYc, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans EYc h)⟩
  have EXp : qlt qzero EX := qlt_iff_le_not_le.mpr ⟨qle_trans c0 hEXc, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hEXc h)⟩
  obtain ⟨ia0, iac⟩ := ZTrig.inv_bound hc ha
  obtain ⟨iY0, iYc⟩ := ZTrig.inv_bound hc EYc
  obtain ⟨iX0, iXc⟩ := ZTrig.inv_bound hc hEXc
  have dY := inv_diff (ne_zero_of_lt EYp) (ne_zero_of_lt ap)
  have dX := inv_diff (ne_zero_of_lt EXp) (ne_zero_of_lt ap)
  have d0 : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  -- lower: d·(1/EY − 1/a) = −d·(EY − a)/(EY·a) ≥ −d(d + γ)/c²
  have m1 := mul_le4 d0 (show qle qzero (qsub EY a) by unfold qsub; rat_linarith) iY0 ia0
    (qle_refl (qsub b a)) (show qle (qsub EY a) (qadd (qadd (qsub b a) γ) t) by unfold qsub at *; rat_linarith) iYc iac
  -- upper: d·(1/EX − 1/a) = d·(a − EX)/(EX·a) ≤ d·t/c²
  have m2 := mul_le4 d0 t0 iX0 ia0
    (qle_refl (qsub b a)) (show qle t (qadd (qadd (qsub b a) γ) t) by unfold qsub at *; rat_linarith) iXc iac
  have tp := qmul_nonneg (qmul_nonneg d0 (show qle qzero (qsub t (qsub a EX)) by unfold qsub at *; rat_linarith))
    (qmul_nonneg iX0 ia0)
  have eY : qEq (qsub (qmul (qsub b a) (qinv' EY)) (qmul (qsub b a) (qinv' a)))
      (qneg (qmul (qmul (qsub b a) (qsub EY a)) (qmul (qinv' EY) (qinv' a)))) := by
    have h := qmul_respects (qEq_refl (qsub b a)) dY
    have h1 : qEq (qsub (qmul (qsub b a) (qinv' EY)) (qmul (qsub b a) (qinv' a))) (qmul (qsub b a) (qsub (qinv' EY) (qinv' a))) := by
      unfold qsub; rat_ring
    have h2 : qEq (qmul (qsub b a) (qmul (qsub a EY) (qmul (qinv' EY) (qinv' a))))
        (qneg (qmul (qmul (qsub b a) (qsub EY a)) (qmul (qinv' EY) (qinv' a)))) := by unfold qsub; rat_ring
    exact qEq_trans h1 (qEq_trans h h2)
  have eX : qEq (qsub (qmul (qsub b a) (qinv' EX)) (qmul (qsub b a) (qinv' a)))
      (qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a))) := by
    have h := qmul_respects (qEq_refl (qsub b a)) dX
    have h1 : qEq (qsub (qmul (qsub b a) (qinv' EX)) (qmul (qsub b a) (qinv' a))) (qmul (qsub b a) (qsub (qinv' EX) (qinv' a))) := by
      unfold qsub; rat_ring
    have h2 : qEq (qmul (qsub b a) (qmul (qsub a EX) (qmul (qinv' EX) (qinv' a))))
        (qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a))) := by rat_ring
    exact qEq_trans h1 (qEq_trans h h2)
  have eX2 : qEq (qmul (qmul (qsub b a) (qsub t (qsub a EX))) (qmul (qinv' EX) (qinv' a)))
      (qsub (qmul (qmul (qsub b a) t) (qmul (qinv' EX) (qinv' a))) (qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a)))) := by
    unfold qsub; rat_ring
  generalize qmul (qsub b a) (qinv' EY) = dY' at *
  generalize qmul (qsub b a) (qinv' EX) = dX' at *
  generalize qmul (qsub b a) (qinv' a) = da at *
  generalize qmul (qmul (qsub b a) (qsub EY a)) (qmul (qinv' EY) (qinv' a)) = PY at *
  generalize qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a)) = PX at *
  generalize qmul (qmul (qsub b a) (qsub t (qsub a EX))) (qmul (qinv' EX) (qinv' a)) = PX' at *
  generalize qmul (qmul (qsub b a) t) (qmul (qinv' EX) (qinv' a)) = PT at *
  generalize qmul (qmul (qsub b a) (qadd (qadd (qsub b a) γ) t)) (qmul (qinv' c) (qinv' c)) = BB at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem fin_pos {Δ d ia Hc e γ t R ek : QExpr}
    (h : ZTrig.Ab (qsub Δ (qmul d ia)) (qadd (qmul (qmul d (qadd (qadd d γ) t)) Hc) e))
    (d0 : qle qzero d) (dR : qle d R) (Hc0 : qle qzero Hc) (γ0 : qle qzero γ) (t0 : qle qzero t)
    (sm : qle (qadd (qmul (qmul R (qadd γ t)) Hc) e) ek) :
    ZTrig.Ab (qsub Δ (qmul d ia)) (qadd ek (qmul (qmul d d) (qadd Hc Hc))) := by
  have p1 := qmul_nonneg (qmul_nonneg (show qle qzero (qsub R d) by unfold qsub; rat_linarith)
    (show qle qzero (qadd γ t) by rat_linarith)) Hc0
  have p2 := qmul_nonneg (qmul_nonneg d0 d0) Hc0
  obtain ⟨h1, h2⟩ := h
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem fin_neg {Δ' a' ia ib Hc e γ t R ek : QExpr}
    (h : ZTrig.Ab (qsub Δ' (qmul a' ib)) (qadd (qmul (qmul a' (qadd (qadd a' γ) t)) Hc) e))
    (hdiff : qEq (qmul a' (qsub ib ia)) (qmul (qmul a' a') (qmul ib ia)))
    (m : qle (qmul (qmul a' a') (qmul ib ia)) (qmul (qmul a' a') Hc)) (n0 : qle qzero (qmul (qmul a' a') (qmul ib ia)))
    (a0 : qle qzero a') (aR : qle a' R) (Hc0 : qle qzero Hc) (γ0 : qle qzero γ) (t0 : qle qzero t)
    (sm : qle (qadd (qmul (qmul R (qadd γ t)) Hc) e) ek) :
    ZTrig.Ab (qsub (qneg Δ') (qmul (qneg a') ia)) (qadd ek (qmul (qmul a' a') (qadd Hc Hc))) := by
  have p1 := qmul_nonneg (qmul_nonneg (show qle qzero (qsub R a') by unfold qsub; rat_linarith)
    (show qle qzero (qadd γ t) by rat_linarith)) Hc0
  have p2 := qmul_nonneg (qmul_nonneg a0 a0) Hc0
  obtain ⟨h1, h2⟩ := h
  unfold qsub at *
  generalize qmul (qmul a' a') (qmul ib ia) = P at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- To the form of a uniform step: `b − a = d`. -/
theorem ab_conv {Δ d d' ia ek H : QExpr} (h : ZTrig.Ab (qsub Δ (qmul d' ia)) (qadd ek (qmul (qmul d' d') H)))
    (e : qEq d' d) : ZTrig.Ab (qsub Δ (qmul d ia)) (qadd ek (qmul (qmul d d) H)) := by
  have e1 := qmul_respects e (qEq_refl ia)
  have e2 := qmul_respects (qmul_respects e e) (qEq_refl H)
  obtain ⟨h1, h2⟩ := h
  unfold qsub at *
  generalize qmul d' ia = A at *
  generalize qmul d ia = A' at *
  generalize qmul (qmul d' d') H = B at *
  generalize qmul (qmul d d) H = B' at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem ab_conv2 {Δ Δ' d a' ia ek H : QExpr}
    (h : ZTrig.Ab (qsub (qneg Δ') (qmul (qneg a') ia)) (qadd ek (qmul (qmul a' a') H)))
    (eΔ : qEq Δ (qneg Δ')) (ed : qEq d (qneg a')) : ZTrig.Ab (qsub Δ (qmul d ia)) (qadd ek (qmul (qmul d d) H)) := by
  have e1 := qmul_respects ed (qEq_refl ia)
  have e2 := qmul_respects (qmul_respects ed ed) (qEq_refl H)
  have e3 : qEq (qmul (qmul (qneg a') (qneg a')) H) (qmul (qmul a' a') H) := by rat_ring
  obtain ⟨h1, h2⟩ := h
  unfold qsub at *
  generalize qmul (qneg a') ia = A at *
  generalize qmul d ia = A' at *
  generalize qmul (qmul a' a') H = B at *
  generalize qmul (qmul d d) H = B' at *
  generalize qmul (qmul (qneg a') (qneg a')) H = B'' at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem half_pos' : qlt qzero ZTrig.half := by
  obtain ⟨h1, h0⟩ := ZTrig.half_facts
  exact qlt_iff_le_not_le.mpr ⟨h0, fun h => (qlt_iff_le_not_le.mp qone_pos).2 (by rat_linarith)⟩

/-- THE UNIFORM STEP OF `ln`: for `x, x + d ≥ c > 0`, `|x| ≤ A`, `|d| ≤ R`, from some index on (one for all of them),
`ln(x + d) − ln(x) − d/x` within `ε_k + d²·H`. (The form of `ZDeriv.UStepOn`.) -/
theorem ustep_ln {c : QExpr} (hc : qlt qzero c) : ∀ {A R : QExpr}, qle qzero A → qle qzero R →
    ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x d, ZTrig.Ab x A → ZTrig.Ab d R → qle c x → qle c (qadd x d) →
      ZTrig.Ab (qsub (qsub (lnseq (qadd x d) n) (lnseq x n)) (qmul d (qinv' x))) (qadd (qeps k) (qmul (qmul d d) H)) := by
  intro A R hA hR
  obtain ⟨hh, h0⟩ := ZTrig.half_facts
  have c'p : qlt qzero (qmul c ZTrig.half) := qmul_pos hc half_pos'
  have c0 := qle_of_qlt hc
  have cc' : qEq c (qadd (qmul c ZTrig.half) (qmul c ZTrig.half)) := by
    have := qmul_respects (qEq_refl c) hh
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
  have ic0 := qinv'_nonneg_of_pos c'p
  have Hc0 : qle qzero (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half))) := qmul_nonneg ic0 ic0
  refine ⟨qadd (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half))) (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half))),
    by rat_linarith, fun k => ?_⟩
  -- the frame (as ZLn.Ev_ln_slope)
  obtain ⟨N0, hN0⟩ := ln_bracket_unif (yhi := qadd (qadd A R) qone) hc
  obtain ⟨Mr, _, hMr0, _, r1, r2, _, _⟩ := bound4 (qadd (qinv' c) qone) (qadd (qadd A R) qone) qzero qzero
  have hR1 : qle qone (qadd (qadd Mr qone) qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have hR0 : qle qzero (qadd (qadd Mr qone) qone) := qle_trans (qle_of_qlt qone_pos) hR1
  obtain ⟨C, Ng, hgC⟩ := gap_const hR1
  obtain ⟨HS, hHS⟩ := S_bounded hR0
  have HS0 : qle qzero HS := qle_trans (S_nonneg hR0 0) (hHS 0)
  obtain ⟨Kg, hgK⟩ := good_exists (qadd (qadd Mr qone) qone)
  obtain ⟨Bt, hBt⟩ := ZTrig.pos_floor c'p
  obtain ⟨Bc, hBc⟩ := eps_scaled' (C := qadd (qmul (qmul R (qadd HS qone)) (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)))) qone)
    (by have := qmul_nonneg (qmul_nonneg hR (show qle qzero (qadd HS qone) by have := qle_of_qlt qone_pos; rat_linarith)) Hc0
        have := qle_of_qlt qone_pos; rat_linarith)
  obtain ⟨Nt, _, hNt⟩ := tm_small hR0 hgK (k + Bc + Bt)
  refine ⟨N0 + Ng + Nt + (k + Bc) + 2, fun n hn x d hx hd hcx hcy => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 2 := by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n1 =>
        cases n1 with
        | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
        | succ m' => exact ⟨m', rfl⟩
  have hm : N0 + Ng + Nt + (k + Bc) ≤ m' := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hn)
  have q0 : N0 ≤ m' := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N0 Ng) (Nat.le_add_right _ Nt))
    (Nat.le_add_right _ (k + Bc))) hm
  have qg : Ng ≤ m' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left Ng N0) (Nat.le_add_right _ Nt))
    (Nat.le_trans (Nat.le_add_right _ (k + Bc)) hm)) (Nat.le_succ m')
  have qt : Nt ≤ m' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_add_left Nt (N0 + Ng)) (Nat.le_trans (Nat.le_add_right _ (k + Bc)) hm))
    (Nat.le_succ m')
  have qk : k + Bc ≤ m' + 2 := Nat.le_trans (Nat.le_trans (Nat.le_add_left (k + Bc) (N0 + Ng + Nt)) hm) (Nat.le_add_right m' 2)
  obtain ⟨xA1, xA2⟩ := hx
  obtain ⟨dR1, dR2⟩ := hd
  have ya : qle x (qadd (qadd A R) qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have yb : qle (qadd x d) (qadd (qadd A R) qone) := by have := qle_of_qlt qone_pos; rat_linarith
  obtain ⟨xa1, xa2⟩ := hN0 x hcx ya m' q0
  obtain ⟨xb1, xb2⟩ := hN0 (qadd x d) hcy yb m' q0
  obtain ⟨ra1, ra2⟩ := ln_range hc hcx ya ⟨xa1, xa2⟩
  obtain ⟨rb1, rb2⟩ := ln_range hc hcy yb ⟨xb1, xb2⟩
  generalize hX : lnseq x (m' + 2) = X at xa1 xa2 ra1 ra2
  generalize hY : lnseq (qadd x d) (m' + 2) = Y at xb1 xb2 rb1 rb2
  obtain ⟨u1, u2⟩ := r1
  obtain ⟨v1, v2⟩ := r2
  unfold qsub at u1 u2 v1 v2
  have en0 := qeps_nonneg (m' + 2)
  have en1 := eps_le_one (m' + 2)
  have o1 := qle_of_qlt qone_pos
  have XR : qclose X qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have YR : qclose Y qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have XeR : qclose (qadd X (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have YeR : qclose (qadd Y (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have xa2' : qle x (eseq (qadd X (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total x (eseq (qadd X (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h xa2
  have xb2' : qle (qadd x d) (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total (qadd x d) (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h xb2
  have cl : qclose (qadd X (qeps (m' + 2))) X (qeps (m' + 2)) := by constructor <;> (unfold qsub; rat_linarith)
  have clb : qclose (qadd Y (qeps (m' + 2))) Y (qeps (m' + 2)) := by constructor <;> (unfold qsub; rat_linarith)
  obtain ⟨la0, _⟩ := E_lip XeR XR cl (m' + 1)
  obtain ⟨lb0, _⟩ := E_lip YeR YR clb (m' + 1)
  have la : qle (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (eseq X (m' + 2)))
      (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) := la0
  have lb : qle (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (eseq Y (m' + 2)))
      (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) := lb0
  have gC := hgC (m' + 1) qg
  have tt := hNt (m' + 1) qt
  have t0 := tm_nonneg hR0 (m' + 1)
  have eA : qle (qeps (k + Bc + Bt)) (qeps (k + Bc)) := qeps_le_add (k + Bc) Bt
  have eB : qle (qeps (k + Bc + Bt)) (qeps Bt) := by
    have := qeps_le_add Bt (k + Bc); rw [Nat.add_comm Bt (k + Bc)] at this; exact this
  have eC := eps_anti qk
  have t1 : qle (tm (qadd (qadd Mr qone) qone) (m' + 1)) (qeps (k + Bc + Bt)) := by rat_linarith
  have tc' : qle (tm (qadd (qadd Mr qone) qone) (m' + 1)) (qmul c ZTrig.half) := by rat_linarith
  have S0 := S_nonneg hR0 (m' + 2)
  have SH := hHS (m' + 2)
  have γ0 := qmul_nonneg en0 S0
  have γle : qle (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) (qmul (qeps (k + Bc)) HS) := by
    have m1 := ZExp.scale eC S0
    have m2 := scale_l SH (qeps_nonneg (k + Bc))
    exact qle_trans m1 m2
  have sc := hBc k
  have sm : qle (qadd (qmul (qmul R (qadd (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)))
      (tm (qadd (qadd Mr qone) qone) (m' + 1)))) (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half))))
      (qeps (m' + 2))) (qeps k) := by
    have df := qmul_nonneg (show qle qzero (qsub (qmul (qeps (k + Bc)) (qadd HS qone))
        (qadd (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) (tm (qadd (qadd Mr qone) qone) (m' + 1))))
        by have e1 : qEq (qmul (qeps (k + Bc)) (qadd HS qone)) (qadd (qmul (qeps (k + Bc)) HS) (qeps (k + Bc))) := by rat_ring
           unfold qsub; rat_linarith)
      (qmul_nonneg hR Hc0)
    have e2 : qEq (qmul (qeps (k + Bc)) (qadd (qmul (qmul R (qadd HS qone)) (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)))) qone))
        (qadd (qmul (qmul (qeps (k + Bc)) (qadd HS qone)) (qmul R (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)))))
          (qeps (k + Bc))) := by rat_ring
    unfold qsub at df
    generalize qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)) = Hc at *
    generalize qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)) = γ at *
    generalize tm (qadd (qadd Mr qone) qone) (m' + 1) = t at *
    generalize qmul (qeps (k + Bc)) (qadd HS qone) = EH at *
    rat_linarith
  have hEXc : qle (qmul c ZTrig.half) (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) := by
    unfold qsub; rat_linarith
  have hEYc : qle (qmul c ZTrig.half) (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) := by
    unfold qsub; rat_linarith
  have hDX : qlt qzero (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) :=
    qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt c'p) hEXc, fun h => (qlt_iff_le_not_le.mp c'p).2 (qle_trans hEXc h)⟩
  have hDY : qlt qzero (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) :=
    qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt c'p) hEYc, fun h => (qlt_iff_le_not_le.mp c'p).2 (qle_trans hEYc h)⟩
  have c'x : qle (qmul c ZTrig.half) x := by rat_linarith
  have c'y : qle (qmul c ZTrig.half) (qadd x d) := by rat_linarith
  have pa : qlt qzero x := qlt_iff_le_not_le.mpr ⟨qle_trans c0 hcx, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hcx h)⟩
  have pb : qlt qzero (qadd x d) := qlt_iff_le_not_le.mpr ⟨qle_trans c0 hcy, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hcy h)⟩
  have EYb : qle (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (qadd (qadd x d) (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)))) := by
    unfold qsub at lb; rat_linarith
  have EXa : qle (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (qadd x (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)))) := by
    unfold qsub at la; rat_linarith
  have gpos := qeps_pos C
  cases qle_total x (qadd x d) with
  | inl hab =>
      obtain ⟨L0, U0⟩ := ln_sigma_pt (n := m' + 1) hR1 XR YR XeR YeR xa1 xa2' xb1 xb2' hab pb gpos gC hDX
      have al := ln_alg (c := qmul c ZTrig.half) (Δ := qsub Y X) c'p c'x hab xb2' EYb
        (show qle (qsub x (tm (qadd (qadd Mr qone) qone) (m' + 1)))
          (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) by unfold qsub; rat_linarith)
        hEXc L0 U0 γ0 t0 en0
      have fp := fin_pos al (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith) Hc0 γ0 t0 sm
      exact ab_conv fp (by unfold qsub; rat_ring)
  | inr hba =>
      obtain ⟨L0, U0⟩ := ln_sigma_pt (n := m' + 1) hR1 YR XR YeR XeR xb1 xb2' xa1 xa2' hba pa gpos gC hDY
      have al := ln_alg (c := qmul c ZTrig.half) (Δ := qsub X Y) c'p c'y hba xa2' EXa
        (show qle (qsub (qadd x d) (tm (qadd (qadd Mr qone) qone) (m' + 1)))
          (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) by unfold qsub; rat_linarith)
        hEYc L0 U0 γ0 t0 en0
      have a0 : qle qzero (qsub x (qadd x d)) := by unfold qsub; rat_linarith
      obtain ⟨ia0, iac⟩ := ZTrig.inv_bound c'p c'x
      obtain ⟨ib0, ibc⟩ := ZTrig.inv_bound c'p c'y
      have dd := inv_diff (ne_zero_of_lt pb) (ne_zero_of_lt pa)
      have hdiff : qEq (qmul (qsub x (qadd x d)) (qsub (qinv' (qadd x d)) (qinv' x)))
          (qmul (qmul (qsub x (qadd x d)) (qsub x (qadd x d))) (qmul (qinv' (qadd x d)) (qinv' x))) :=
        qEq_trans (qmul_respects (qEq_refl _) dd) (by rat_ring)
      have mm := mul_le4 a0 a0 ib0 ia0 (qle_refl _) (qle_refl _) ibc iac
      have n0 := qmul_nonneg (qmul_nonneg a0 a0) (qmul_nonneg ib0 ia0)
      have fn := fin_neg al hdiff mm n0 a0 (by unfold qsub; rat_linarith) Hc0 γ0 t0 sm
      exact ab_conv2 fn (by unfold qsub; rat_ring) (by unfold qsub; rat_ring)

theorem cnt_respects {y y' : QExpr} (e : qEq y y') (n : Nat) : ∀ j, cnt y n j = cnt y' n j
  | 0 => rfl
  | j + 1 => by
      cases qle.decidable (eseq (gpt n (j + 1)) n) y with
      | isTrue h =>
          have h' : qle (eseq (gpt n (j + 1)) n) y' := qle_trans h (qle_of_qEq e)
          rw [cnt_true h, cnt_true h', cnt_respects e n j]
      | isFalse h =>
          have h' : ¬ qle (eseq (gpt n (j + 1)) n) y' := fun h2 => h (qle_trans h2 (qle_of_qEq (qEq_symm e)))
          rw [cnt_false h, cnt_false h', cnt_respects e n j]

theorem lnseq_respects {y y' : QExpr} (e : qEq y y') (n : Nat) : qEq (lnseq y n) (lnseq y' n) := by
  show qEq (gpt n (cnt y n (gridK n))) (gpt n (cnt y' n (gridK n)))
  rw [cnt_respects e n (gridK n)]; exact qEq_refl _

/-- The chord, algebra only: `(b − a)/b − ε ≤ Δ ≤ (b − a)/a + ε` from the grid logs' bounds. -/
theorem chord_alg {a b Δ EY EX c e γ t ek C : QExpr} (hc : qlt qzero c) (ha : qle c a) (hab : qle a b)
    (hbC : qle (qsub b a) C) (hEY1 : qle b EY) (hEY2 : qle EY (qadd b γ)) (hEX1 : qle (qsub a t) EX) (hEXc : qle c EX)
    (L : qle (qmul (qsub b a) (qinv' EY)) (qadd Δ e)) (U : qle Δ (qadd (qmul (qsub b a) (qinv' EX)) e))
    (γ0 : qle qzero γ) (t0 : qle qzero t) (e0 : qle qzero e)
    (sm : qle (qadd (qmul (qmul C (qadd γ t)) (qmul (qinv' c) (qinv' c))) e) ek) :
    qle (qsub (qmul (qsub b a) (qinv' b)) ek) Δ ∧ qle Δ (qadd (qmul (qsub b a) (qinv' a)) ek) := by
  have c0 := qle_of_qlt hc
  have ap : qlt qzero a := qlt_iff_le_not_le.mpr ⟨qle_trans c0 ha, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans ha h)⟩
  have bc : qle c b := qle_trans ha hab
  have bp : qlt qzero b := qlt_iff_le_not_le.mpr ⟨qle_trans c0 bc, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans bc h)⟩
  have EYc : qle c EY := qle_trans bc hEY1
  have EYp : qlt qzero EY := qlt_iff_le_not_le.mpr ⟨qle_trans c0 EYc, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans EYc h)⟩
  have EXp : qlt qzero EX := qlt_iff_le_not_le.mpr ⟨qle_trans c0 hEXc, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hEXc h)⟩
  obtain ⟨ia0, iac⟩ := ZTrig.inv_bound hc ha
  obtain ⟨ib0, ibc⟩ := ZTrig.inv_bound hc bc
  obtain ⟨iY0, iYc⟩ := ZTrig.inv_bound hc EYc
  obtain ⟨iX0, iXc⟩ := ZTrig.inv_bound hc hEXc
  have dY := inv_diff (ne_zero_of_lt EYp) (ne_zero_of_lt bp)
  have dX := inv_diff (ne_zero_of_lt EXp) (ne_zero_of_lt ap)
  have d0 : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  have m1 := mul_le4 d0 (show qle qzero (qsub EY b) by unfold qsub; rat_linarith) iY0 ib0
    hbC (show qle (qsub EY b) γ by unfold qsub at *; rat_linarith) iYc ibc
  have m2 := mul_le4 d0 t0 iX0 ia0 hbC (qle_refl t) iXc iac
  have tp := qmul_nonneg (qmul_nonneg d0 (show qle qzero (qsub t (qsub a EX)) by unfold qsub at *; rat_linarith))
    (qmul_nonneg iX0 ia0)
  have eY : qEq (qsub (qmul (qsub b a) (qinv' EY)) (qmul (qsub b a) (qinv' b)))
      (qneg (qmul (qmul (qsub b a) (qsub EY b)) (qmul (qinv' EY) (qinv' b)))) := by
    have h := qmul_respects (qEq_refl (qsub b a)) dY
    have h1 : qEq (qsub (qmul (qsub b a) (qinv' EY)) (qmul (qsub b a) (qinv' b))) (qmul (qsub b a) (qsub (qinv' EY) (qinv' b))) := by
      unfold qsub; rat_ring
    have h2 : qEq (qmul (qsub b a) (qmul (qsub b EY) (qmul (qinv' EY) (qinv' b))))
        (qneg (qmul (qmul (qsub b a) (qsub EY b)) (qmul (qinv' EY) (qinv' b)))) := by unfold qsub; rat_ring
    exact qEq_trans h1 (qEq_trans h h2)
  have eX : qEq (qsub (qmul (qsub b a) (qinv' EX)) (qmul (qsub b a) (qinv' a)))
      (qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a))) := by
    have h := qmul_respects (qEq_refl (qsub b a)) dX
    have h1 : qEq (qsub (qmul (qsub b a) (qinv' EX)) (qmul (qsub b a) (qinv' a))) (qmul (qsub b a) (qsub (qinv' EX) (qinv' a))) := by
      unfold qsub; rat_ring
    have h2 : qEq (qmul (qsub b a) (qmul (qsub a EX) (qmul (qinv' EX) (qinv' a))))
        (qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a))) := by rat_ring
    exact qEq_trans h1 (qEq_trans h h2)
  have eX2 : qEq (qmul (qmul (qsub b a) (qsub t (qsub a EX))) (qmul (qinv' EX) (qinv' a)))
      (qsub (qmul (qmul (qsub b a) t) (qmul (qinv' EX) (qinv' a))) (qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a)))) := by
    unfold qsub; rat_ring
  have sp : qEq (qmul (qmul C (qadd γ t)) (qmul (qinv' c) (qinv' c)))
      (qadd (qmul (qmul C γ) (qmul (qinv' c) (qinv' c))) (qmul (qmul C t) (qmul (qinv' c) (qinv' c)))) := by rat_ring
  have q1 := qmul_nonneg (qmul_nonneg (qle_trans d0 hbC) γ0) (qmul_nonneg (qinv'_nonneg_of_pos hc) (qinv'_nonneg_of_pos hc))
  have q2 := qmul_nonneg (qmul_nonneg (qle_trans d0 hbC) t0) (qmul_nonneg (qinv'_nonneg_of_pos hc) (qinv'_nonneg_of_pos hc))
  generalize qmul (qsub b a) (qinv' EY) = dY' at *
  generalize qmul (qsub b a) (qinv' EX) = dX' at *
  generalize qmul (qsub b a) (qinv' a) = da at *
  generalize qmul (qsub b a) (qinv' b) = db at *
  generalize qmul (qmul (qsub b a) (qsub EY b)) (qmul (qinv' EY) (qinv' b)) = PY at *
  generalize qmul (qmul (qsub b a) (qsub a EX)) (qmul (qinv' EX) (qinv' a)) = PX at *
  generalize qmul (qmul (qsub b a) (qsub t (qsub a EX))) (qmul (qinv' EX) (qinv' a)) = PX' at *
  generalize qmul (qmul (qsub b a) t) (qmul (qinv' EX) (qinv' a)) = PT at *
  generalize qmul (qmul C γ) (qmul (qinv' c) (qinv' c)) = Cg at *
  generalize qmul (qmul C t) (qmul (qinv' c) (qinv' c)) = Ct at *
  generalize qmul (qmul C (qadd γ t)) (qmul (qinv' c) (qinv' c)) = Cgt at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem chord_conv {x d Δ ib ia ek : QExpr}
    (h : qle (qsub (qmul (qsub (qadd x d) x) ib) ek) Δ ∧ qle Δ (qadd (qmul (qsub (qadd x d) x) ia) ek))
    (e : qEq (qsub (qadd x d) x) d) : qle (qsub (qmul d ib) ek) Δ ∧ qle Δ (qadd (qmul d ia) ek) := by
  obtain ⟨c1, c2⟩ := h
  have e1 := qmul_respects e (qEq_refl ib)
  have e2 := qmul_respects e (qEq_refl ia)
  unfold qsub at *
  generalize qmul (qadd (qadd x d) (qneg x)) ib = A at *
  generalize qmul (qadd (qadd x d) (qneg x)) ia = A' at *
  generalize qmul d ib = B at *
  generalize qmul d ia = B' at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE CHORD OF `ln`: for `c ≤ x ≤ x + d ≤ C`, from some index on (one for all of them),
`d/(x + d) − ε_k ≤ ln(x + d) − ln x ≤ d/x + ε_k`. -/
theorem ln_chord {c : QExpr} (hc : qlt qzero c) {C : QExpr} (hC : qle qzero C) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x d, qle c x → qle qzero d → qle (qadd x d) C →
      qle (qsub (qmul d (qinv' (qadd x d))) (qeps k)) (qsub (lnseq (qadd x d) n) (lnseq x n)) ∧
      qle (qsub (lnseq (qadd x d) n) (lnseq x n)) (qadd (qmul d (qinv' x)) (qeps k)) := by
  intro k
  obtain ⟨hh, h0⟩ := ZTrig.half_facts
  have c'p : qlt qzero (qmul c ZTrig.half) := qmul_pos hc half_pos'
  have c0 := qle_of_qlt hc
  have cc' : qEq c (qadd (qmul c ZTrig.half) (qmul c ZTrig.half)) := by
    have := qmul_respects (qEq_refl c) hh
    exact qEq_trans (by rat_ring) (qEq_trans (qEq_symm this) (by rat_ring))
  have ic0 := qinv'_nonneg_of_pos c'p
  have Hc0 : qle qzero (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half))) := qmul_nonneg ic0 ic0
  -- the frame (as ZLn.Ev_ln_slope)
  obtain ⟨N0, hN0⟩ := ln_bracket_unif (yhi := qadd C qone) hc
  obtain ⟨Mr, _, hMr0, _, r1, r2, _, _⟩ := bound4 (qadd (qinv' c) qone) (qadd C qone) qzero qzero
  have hR1 : qle qone (qadd (qadd Mr qone) qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have hR0 : qle qzero (qadd (qadd Mr qone) qone) := qle_trans (qle_of_qlt qone_pos) hR1
  obtain ⟨Cg, Ng, hgC⟩ := gap_const hR1
  obtain ⟨HS, hHS⟩ := S_bounded hR0
  have HS0 : qle qzero HS := qle_trans (S_nonneg hR0 0) (hHS 0)
  obtain ⟨Kg, hgK⟩ := good_exists (qadd (qadd Mr qone) qone)
  obtain ⟨Bt, hBt⟩ := ZTrig.pos_floor c'p
  obtain ⟨Bc, hBc⟩ := eps_scaled' (C := qadd (qmul (qmul C (qadd HS qone)) (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)))) qone)
    (by have := qmul_nonneg (qmul_nonneg hC (show qle qzero (qadd HS qone) by have := qle_of_qlt qone_pos; rat_linarith)) Hc0
        have := qle_of_qlt qone_pos; rat_linarith)
  obtain ⟨Nt, _, hNt⟩ := tm_small hR0 hgK (k + Bc + Bt)
  refine ⟨N0 + Ng + Nt + (k + Bc) + 2, fun n hn x d hcx hd0 hxC => ?_⟩
  have hcy : qle c (qadd x d) := by rat_linarith
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 2 := by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n1 =>
        cases n1 with
        | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
        | succ m' => exact ⟨m', rfl⟩
  have hm : N0 + Ng + Nt + (k + Bc) ≤ m' := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hn)
  have q0 : N0 ≤ m' := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N0 Ng) (Nat.le_add_right _ Nt))
    (Nat.le_add_right _ (k + Bc))) hm
  have qg : Ng ≤ m' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left Ng N0) (Nat.le_add_right _ Nt))
    (Nat.le_trans (Nat.le_add_right _ (k + Bc)) hm)) (Nat.le_succ m')
  have qt : Nt ≤ m' + 1 := Nat.le_trans (Nat.le_trans (Nat.le_add_left Nt (N0 + Ng)) (Nat.le_trans (Nat.le_add_right _ (k + Bc)) hm))
    (Nat.le_succ m')
  have qk : k + Bc ≤ m' + 2 := Nat.le_trans (Nat.le_trans (Nat.le_add_left (k + Bc) (N0 + Ng + Nt)) hm) (Nat.le_add_right m' 2)
  have ya : qle x (qadd C qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have yb : qle (qadd x d) (qadd C qone) := by have := qle_of_qlt qone_pos; rat_linarith
  obtain ⟨xa1, xa2⟩ := hN0 x hcx ya m' q0
  obtain ⟨xb1, xb2⟩ := hN0 (qadd x d) hcy yb m' q0
  obtain ⟨ra1, ra2⟩ := ln_range hc hcx ya ⟨xa1, xa2⟩
  obtain ⟨rb1, rb2⟩ := ln_range hc hcy yb ⟨xb1, xb2⟩
  generalize hX : lnseq x (m' + 2) = X at xa1 xa2 ra1 ra2
  generalize hY : lnseq (qadd x d) (m' + 2) = Y at xb1 xb2 rb1 rb2
  obtain ⟨u1, u2⟩ := r1
  obtain ⟨v1, v2⟩ := r2
  unfold qsub at u1 u2 v1 v2
  have en0 := qeps_nonneg (m' + 2)
  have en1 := eps_le_one (m' + 2)
  have o1 := qle_of_qlt qone_pos
  have XR : qclose X qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have YR : qclose Y qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have XeR : qclose (qadd X (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have YeR : qclose (qadd Y (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have xa2' : qle x (eseq (qadd X (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total x (eseq (qadd X (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h xa2
  have xb2' : qle (qadd x d) (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total (qadd x d) (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h xb2
  have cl : qclose (qadd X (qeps (m' + 2))) X (qeps (m' + 2)) := by constructor <;> (unfold qsub; rat_linarith)
  have clb : qclose (qadd Y (qeps (m' + 2))) Y (qeps (m' + 2)) := by constructor <;> (unfold qsub; rat_linarith)
  obtain ⟨la0, _⟩ := E_lip XeR XR cl (m' + 1)
  obtain ⟨lb0, _⟩ := E_lip YeR YR clb (m' + 1)
  have la : qle (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (eseq X (m' + 2)))
      (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) := la0
  have lb : qle (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (eseq Y (m' + 2)))
      (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) := lb0
  have gC := hgC (m' + 1) qg
  have tt := hNt (m' + 1) qt
  have t0 := tm_nonneg hR0 (m' + 1)
  have eA : qle (qeps (k + Bc + Bt)) (qeps (k + Bc)) := qeps_le_add (k + Bc) Bt
  have eB : qle (qeps (k + Bc + Bt)) (qeps Bt) := by
    have := qeps_le_add Bt (k + Bc); rw [Nat.add_comm Bt (k + Bc)] at this; exact this
  have eC := eps_anti qk
  have t1 : qle (tm (qadd (qadd Mr qone) qone) (m' + 1)) (qeps (k + Bc + Bt)) := by rat_linarith
  have tc' : qle (tm (qadd (qadd Mr qone) qone) (m' + 1)) (qmul c ZTrig.half) := by rat_linarith
  have S0 := S_nonneg hR0 (m' + 2)
  have SH := hHS (m' + 2)
  have γ0 := qmul_nonneg en0 S0
  have γle : qle (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) (qmul (qeps (k + Bc)) HS) := by
    have m1 := ZExp.scale eC S0
    have m2 := scale_l SH (qeps_nonneg (k + Bc))
    exact qle_trans m1 m2
  have sc := hBc k
  have sm : qle (qadd (qmul (qmul C (qadd (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)))
      (tm (qadd (qadd Mr qone) qone) (m' + 1)))) (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half))))
      (qeps (m' + 2))) (qeps k) := by
    have df := qmul_nonneg (show qle qzero (qsub (qmul (qeps (k + Bc)) (qadd HS qone))
        (qadd (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) (tm (qadd (qadd Mr qone) qone) (m' + 1))))
        by have e1 : qEq (qmul (qeps (k + Bc)) (qadd HS qone)) (qadd (qmul (qeps (k + Bc)) HS) (qeps (k + Bc))) := by rat_ring
           unfold qsub; rat_linarith)
      (qmul_nonneg hC Hc0)
    have e2 : qEq (qmul (qeps (k + Bc)) (qadd (qmul (qmul C (qadd HS qone)) (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)))) qone))
        (qadd (qmul (qmul (qeps (k + Bc)) (qadd HS qone)) (qmul C (qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)))))
          (qeps (k + Bc))) := by rat_ring
    unfold qsub at df
    generalize qmul (qinv' (qmul c ZTrig.half)) (qinv' (qmul c ZTrig.half)) = Hc at *
    generalize qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)) = γ at *
    generalize tm (qadd (qadd Mr qone) qone) (m' + 1) = t at *
    generalize qmul (qeps (k + Bc)) (qadd HS qone) = EH at *
    rat_linarith
  have hEXc : qle (qmul c ZTrig.half) (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) := by
    unfold qsub; rat_linarith
  have hEYc : qle (qmul c ZTrig.half) (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) := by
    unfold qsub; rat_linarith
  have hDX : qlt qzero (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) :=
    qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt c'p) hEXc, fun h => (qlt_iff_le_not_le.mp c'p).2 (qle_trans hEXc h)⟩
  have hDY : qlt qzero (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) :=
    qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt c'p) hEYc, fun h => (qlt_iff_le_not_le.mp c'p).2 (qle_trans hEYc h)⟩
  have c'x : qle (qmul c ZTrig.half) x := by rat_linarith
  have c'y : qle (qmul c ZTrig.half) (qadd x d) := by rat_linarith
  have pa : qlt qzero x := qlt_iff_le_not_le.mpr ⟨qle_trans c0 hcx, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hcx h)⟩
  have pb : qlt qzero (qadd x d) := qlt_iff_le_not_le.mpr ⟨qle_trans c0 hcy, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hcy h)⟩
  have EYb : qle (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (qadd (qadd x d) (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)))) := by
    unfold qsub at lb; rat_linarith
  have EXa : qle (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (qadd x (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2)))) := by
    unfold qsub at la; rat_linarith
  have gpos := qeps_pos Cg
  have hab : qle x (qadd x d) := by rat_linarith
  obtain ⟨L0, U0⟩ := ln_sigma_pt (n := m' + 1) hR1 XR YR XeR YeR xa1 xa2' xb1 xb2' hab pb gpos gC hDX
  have ch := chord_alg (c := qmul c ZTrig.half) (Δ := qsub Y X) (C := C) c'p c'x hab
    (show qle (qsub (qadd x d) x) C by unfold qsub; rat_linarith) xb2' EYb
    (show qle (qsub x (tm (qadd (qadd Mr qone) qone) (m' + 1)))
      (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) by unfold qsub; rat_linarith)
    hEXc L0 U0 γ0 t0 en0 sm
  exact chord_conv ch (show qEq (qsub (qadd x d) x) d by unfold qsub; rat_ring)

/-- The chord by its ends: `c ≤ y₁ ≤ y₂ ≤ C`, `(y₂ − y₁)/y₂ − ε ≤ ln y₂ − ln y₁ ≤ (y₂ − y₁)/y₁ + ε`. -/
theorem chord2 {c : QExpr} (hc : qlt qzero c) {C : QExpr} (hC : qle qzero C) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∀ y1 y2, qle c y1 → qle y1 y2 → qle y2 C →
      qle (qsub (qmul (qsub y2 y1) (qinv' y2)) (qeps k)) (qsub (lnseq y2 n) (lnseq y1 n)) ∧
      qle (qsub (lnseq y2 n) (lnseq y1 n)) (qadd (qmul (qsub y2 y1) (qinv' y1)) (qeps k)) := by
  intro k
  obtain ⟨N, hN⟩ := ln_chord hc hC k
  refine ⟨N, fun n hn y1 y2 h1 h12 h2 => ?_⟩
  have e : qEq (qadd y1 (qsub y2 y1)) y2 := by unfold qsub; rat_ring
  obtain ⟨a1, a2⟩ := hN n hn y1 (qsub y2 y1) h1 (by unfold qsub; rat_linarith) (by
    have := qle_of_qEq e; exact qle_trans this h2)
  have l := lnseq_respects e n
  have iv := qinv'_respects e
  have m := qmul_respects (qEq_refl (qsub y2 y1)) iv
  generalize lnseq (qadd y1 (qsub y2 y1)) n = A at *
  generalize lnseq y2 n = A' at *
  generalize qmul (qsub y2 y1) (qinv' (qadd y1 (qsub y2 y1))) = P at *
  generalize qmul (qsub y2 y1) (qinv' y2) = P' at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZLnStep


#print axioms ZLnStep.ln_alg
#print axioms ZLnStep.fin_pos
#print axioms ZLnStep.fin_neg
#print axioms ZLnStep.ab_conv
#print axioms ZLnStep.ustep_ln
#print axioms ZLnStep.lnseq_respects
#print axioms ZLnStep.chord_alg
#print axioms ZLnStep.ln_chord
#print axioms ZLnStep.chord2
