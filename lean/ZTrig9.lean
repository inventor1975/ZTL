import ZTrig8

/-!
# ZTrig9 — the period `4ρ`; the windows between extrema of `cos`. Zero axioms.

Stage 9 of the full sine.

  * `four_shift`, `period_unif` — `cos(y + 4ρ) = cos y`, and `cos(x + j·4ρ) = cos x`, uniformly;
  * `cos_win_up` — no maximum inside: `0 ≤ a0 ≤ z ≤ a1 ≤ 4ρ` ⇒ `cos z ≤ cos a0 + ε` or `cos z ≤ cos a1 + ε`;
  * `cos_win_lo` — no minimum inside: `−2ρ ≤ a0 ≤ z ≤ a1 ≤ 2ρ` ⇒ `cos z ≥ cos a0 − ε` or `cos z ≥ cos a1 − ε`.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-- `4ρ_n`. -/
def four (n : Nat) : QExpr := qadd (qadd (qadd (rho n) (rho n)) (rho n)) (rho n)

theorem bnd4 {y A r : QExpr} (hy : Ab y A) (r0 : qle qzero r) (r2 : qle r (qadd qone qone)) :
    Ab y (qadd A (qadd (qadd qone qone) (qadd (qadd qone qone) (qadd qone qone)))) ∧
    Ab (qadd y r) (qadd A (qadd (qadd qone qone) (qadd (qadd qone qone) (qadd qone qone)))) ∧
    Ab (qadd (qadd y r) r) (qadd A (qadd (qadd qone qone) (qadd (qadd qone qone) (qadd qone qone)))) ∧
    Ab (qadd (qadd (qadd y r) r) r) (qadd A (qadd (qadd qone qone) (qadd (qadd qone qone) (qadd qone qone)))) := by
  obtain ⟨y1, y2⟩ := hy
  have := qle_of_qlt qone_pos
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩,
    ⟨by rat_linarith, by rat_linarith⟩⟩

theorem four_combine {C4 S3 C2 S1 C0 e : QExpr} (a : Ab (qadd C4 S3) e) (b : Ab (qsub S3 C2) e) (c : Ab (qadd C2 S1) e)
    (d : Ab (qsub S1 C0) e) : Ab (qsub C4 C0) (qadd (qadd e e) (qadd e e)) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem four_eps (k : Nat) : qle (qadd (qadd (qeps (k + 2)) (qeps (k + 2))) (qadd (qeps (k + 2)) (qeps (k + 2)))) (qeps k) := by
  have e1 := qeps_succ_add (k + 1); have e0 := qeps_succ_add k
  rat_linarith

/-- `cos(y + 4ρ) = cos y`, uniformly for `|y| ≤ A`. -/
theorem four_shift {A : QExpr} (hA : qle qzero A) (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ y, Ab y A →
    Ab (qsub (Cn (qadd y (four n)) n) (Cn y n)) (qeps k) := by
  obtain ⟨R, hR⟩ := rho_facts
  have hA2 : qle qzero (qadd A (qadd (qadd qone qone) (qadd (qadd qone qone) (qadd qone qone)))) := by
    have := two_pos; rat_linarith
  obtain ⟨N1, hN1⟩ := shift_unif hA2 (k + 2)
  refine ⟨R + N1, fun n hn y hy => ?_⟩
  obtain ⟨r1, r2, _, _⟩ := hR n (le_l' hn)
  have r0 : qle qzero (rho n) := by have := qle_of_qlt qone_pos; rat_linarith
  have r2' : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  obtain ⟨b0, b1, b2, b3⟩ := bnd4 hy r0 r2'
  obtain ⟨_, a⟩ := hN1 n (le_r' hn) _ b3
  obtain ⟨b, _⟩ := hN1 n (le_r' hn) _ b2
  obtain ⟨_, c⟩ := hN1 n (le_r' hn) _ b1
  obtain ⟨d, _⟩ := hN1 n (le_r' hn) _ b0
  have e := Cn_respects (show qEq (qadd (qadd (qadd (qadd y (rho n)) (rho n)) (rho n)) (rho n)) (qadd y (four n)) by
    unfold four; rat_ring) n
  obtain ⟨g1, g2⟩ := four_combine a b c d
  have t := four_eps k
  generalize Cn (qadd (qadd (qadd (qadd y (rho n)) (rho n)) (rho n)) (rho n)) n = C4 at *
  generalize Cn (qadd y (four n)) n = C4' at *
  generalize Sn (qadd (qadd (qadd y (rho n)) (rho n)) (rho n)) n = S3 at *
  generalize Cn (qadd (qadd y (rho n)) (rho n)) n = C2 at *
  generalize Sn (qadd y (rho n)) n = S1 at *; generalize Cn y n = C0 at *
  generalize qadd (qadd (qeps (k + 2)) (qeps (k + 2))) (qadd (qeps (k + 2)) (qeps (k + 2))) = E at *
  clear a b c d hR hN1 b0 b1 b2 b3 r1 r2 r2' r0 hy
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

def eight : QExpr := qadd (qadd (qadd qone qone) (qadd qone qone)) (qadd (qadd qone qone) (qadd qone qone))

theorem four_facts {n : Nat} (r0 : qle qzero (rho n)) (r2 : qle (rho n) (qadd qone qone)) :
    qle qzero (four n) ∧ qle (four n) eight := by
  unfold four eight; exact ⟨by rat_linarith, by rat_linarith⟩

theorem bnd_shift {x A f : QExpr} {j : Nat} (hx : Ab x A) (f0 : qle qzero f) (f8 : qle f eight) :
    Ab (qadd x (qmul (qnat j) f)) (qadd A (qmul (qnat j) eight)) := by
  obtain ⟨x1, x2⟩ := hx
  have a := qmul_nonneg (qnat_nonneg j) f0
  have b := scale_l f8 (qnat_nonneg j)
  generalize qmul (qnat j) f = u at *; generalize qmul (qnat j) eight = w at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE PERIOD: `cos(x + j·4ρ) = cos x`, uniformly for `|x| ≤ A`. -/
theorem period_unif {A : QExpr} (hA : qle qzero A) : ∀ (j k : Nat), ∃ N, ∀ n, N ≤ n → ∀ x, Ab x A →
    Ab (qsub (Cn (qadd x (qmul (qnat j) (four n))) n) (Cn x n)) (qeps k)
  | 0, k => ⟨0, fun n _ x _ => by
      have e := Cn_respects (show qEq (qadd x (qmul (qnat 0) (four n))) x by
        have := qEq_trans (qmul_respects qnat_zero (qEq_refl (four n))) (qzero_mul (four n))
        exact qEq_trans (qadd_respects (qEq_refl x) this) (qadd_zero x)) n
      have p := qeps_nonneg k
      generalize Cn (qadd x (qmul (qnat 0) (four n))) n = C at *; generalize Cn x n = C0 at *
      unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩⟩
  | j + 1, k => by
      obtain ⟨R, hR⟩ := rho_facts
      obtain ⟨N1, hN1⟩ := period_unif hA j (k + 1)
      have hA2 : qle qzero (qadd A (qmul (qnat j) eight)) := by
        have := qmul_nonneg (qnat_nonneg j) (show qle qzero eight by unfold eight; have := qle_of_qlt qone_pos; rat_linarith)
        rat_linarith
      obtain ⟨N2, hN2⟩ := four_shift hA2 (k + 1)
      refine ⟨R + (N1 + N2), fun n hn x hx => ?_⟩
      obtain ⟨r1, r2, _, _⟩ := hR n (le_l' hn)
      have r0 : qle qzero (rho n) := by have := qle_of_qlt qone_pos; rat_linarith
      have r2' : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
      obtain ⟨f0, f8⟩ := four_facts r0 r2'
      have by' := bnd_shift (j := j) hx f0 f8
      obtain ⟨a1, a2⟩ := hN2 n (le_r' (le_r' hn)) _ by'
      obtain ⟨b1, b2⟩ := hN1 n (le_l' (le_r' hn)) x hx
      have e := Cn_respects (show qEq (qadd x (qmul (qnat (j + 1)) (four n))) (qadd (qadd x (qmul (qnat j) (four n))) (four n)) by
        have := qmul_respects (qnat_succ j) (qEq_refl (four n))
        exact qEq_trans (qadd_respects (qEq_refl x) this) (by rat_ring)) n
      have e0 := qeps_succ_add k
      generalize Cn (qadd x (qmul (qnat (j + 1)) (four n))) n = C1 at *
      generalize Cn (qadd (qadd x (qmul (qnat j) (four n))) (four n)) n = C1' at *
      generalize Cn (qadd x (qmul (qnat j) (four n))) n = Cj at *
      generalize Cn x n = C0 at *
      clear hR hN1 hN2 by' r1 r2 r2' r0 f0 f8 hx
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- NO MAXIMUM INSIDE: `0 ≤ a0 ≤ z ≤ a1 ≤ 4ρ_n` ⇒ `cos z ≤ cos a0 + ε` or `cos z ≤ cos a1 + ε`. -/
theorem cos_win_up (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ a0 z a1, qle qzero a0 → qle a0 z → qle z a1 → qle a1 (four n) →
    qle (Cn z n) (qadd (Cn a0 n) (qeps k)) ∨ qle (Cn z n) (qadd (Cn a1 n) (qeps k)) := by
  obtain ⟨N1, hN1⟩ := cos_dec_win k
  obtain ⟨N2, hN2⟩ := cos_inc_win k
  refine ⟨N1 + N2, fun n hn a0 z a1 h0 h1 h2 h3 => ?_⟩
  cases qle_total z (qadd (rho n) (rho n)) with
  | inl h => exact Or.inl (hN1 n (le_l' hn) a0 z h0 h1 h)
  | inr h => exact Or.inr (hN2 n (le_r' hn) z a1 h h2 (by unfold four at h3; rat_linarith))

/-- NO MINIMUM INSIDE: `−2ρ_n ≤ a0 ≤ z ≤ a1 ≤ 2ρ_n` ⇒ `cos a0 ≤ cos z + ε` or `cos a1 ≤ cos z + ε`. -/
theorem cos_win_lo (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ a0 z a1, qle (qneg (qadd (rho n) (rho n))) a0 → qle a0 z → qle z a1 →
    qle a1 (qadd (rho n) (rho n)) →
    qle (Cn a0 n) (qadd (Cn z n) (qeps k)) ∨ qle (Cn a1 n) (qadd (Cn z n) (qeps k)) := by
  obtain ⟨N1, hN1⟩ := cos_dec_win k
  refine ⟨N1, fun n hn a0 z a1 h0 h1 h2 h3 => ?_⟩
  cases qle_total z qzero with
  | inl h =>
      -- on [−2ρ, 0]: cos(−·) falls on [0, 2ρ]
      have c := hN1 n hn (qneg z) (qneg a0) (by rat_linarith) (by rat_linarith) (by rat_linarith)
      have e1 := Cn_neg a0 n; have e2 := Cn_neg z n
      left
      generalize Cn (qneg a0) n = A' at *; generalize Cn (qneg z) n = Z' at *
      generalize Cn a0 n = A0 at *; generalize Cn z n = Z0 at *
      rat_linarith
  | inr h => exact Or.inr (hN1 n hn z a1 h h2 h3)

end ZTrig

#print axioms ZTrig.four_shift
#print axioms ZTrig.period_unif
#print axioms ZTrig.cos_win_up
#print axioms ZTrig.cos_win_lo
