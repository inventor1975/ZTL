import ZTrig7

/-!
# ZTrig8 — `cos` falls on `[0, 2ρ]`, rises on `[2ρ, 4ρ]`, uniformly. Zero axioms.

Stage 8 of the full sine.

  * `cos_dec_win` — `0 ≤ u ≤ v ≤ 2ρ_n` ⇒ `C_n(v) ≤ C_n(u) + ε_k` (`cos u = −sin(u − ρ)`, `sin` rises on `[−ρ, ρ]`);
  * `cos_inc_win` — `2ρ_n ≤ u ≤ v ≤ 4ρ_n` ⇒ `C_n(u) ≤ C_n(v) + ε_k` (`cos u = sin(u − 3ρ)`, three shifts).
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

theorem le_l' {a b n : Nat} (h : a + b ≤ n) : a ≤ n := Nat.le_trans (Nat.le_add_right a b) h
theorem le_r' {a b n : Nat} (h : a + b ≤ n) : b ≤ n := Nat.le_trans (Nat.le_add_left b a) h

/-- `cos` FALLS ON `[0, 2ρ]`, uniformly. -/
theorem cos_dec_win (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ u v, qle qzero u → qle u v → qle v (qadd (rho n) (rho n)) →
    qle (Cn v n) (qadd (Cn u n) (qeps k)) := by
  obtain ⟨R, hR⟩ := rho_bnd
  obtain ⟨Ns, hNs⟩ := shift_unif two_pos (k + 2)
  obtain ⟨Nu, hNu⟩ := sin_up_unif (k + 2)
  refine ⟨R + (Ns + Nu), fun n hn u v hu huv hv => ?_⟩
  obtain ⟨r1, r2⟩ := hR n (le_l' hn)
  have rr : qle qzero (rho n) := by rat_linarith
  -- y = u − ρ, z = v − ρ in [−ρ, ρ] ⊆ [−2, 2]
  have yu : Ab (qsub u (rho n)) (qadd qone qone) := by unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  have yv : Ab (qsub v (rho n)) (qadd qone qone) := by unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨_, ⟨a1, a2⟩⟩ := hNs n (le_l' (le_r' hn)) _ yu
  obtain ⟨_, ⟨b1, b2⟩⟩ := hNs n (le_l' (le_r' hn)) _ yv
  have up := hNu n (le_r' (le_r' hn)) (qsub u (rho n)) (qsub v (rho n))
    (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
  have eu := Cn_respects (show qEq (qadd (qsub u (rho n)) (rho n)) u by unfold qsub; rat_ring) n
  have ev := Cn_respects (show qEq (qadd (qsub v (rho n)) (rho n)) v by unfold qsub; rat_ring) n
  have e1 := qeps_succ_add (k + 1); have e0 := qeps_succ_add k
  have p := qeps_nonneg (k + 2)
  generalize Cn (qadd (qsub u (rho n)) (rho n)) n = Cu' at *; generalize Cn (qadd (qsub v (rho n)) (rho n)) n = Cv' at *
  generalize Sn (qsub u (rho n)) n = Su at *; generalize Sn (qsub v (rho n)) n = Sv at *
  generalize Cn u n = Cu at *; generalize Cn v n = Cv at *
  clear hR hNs hNu yu yv r1 r2 hu huv hv rr
  rat_linarith

/-- `|y| ≤ A`, `0 ≤ r ≤ 2` ⇒ `|y + j·r| ≤ A + 4` for `j = 0, 1, 2`. -/
theorem bnd3 {y A r : QExpr} (hy : Ab y A) (r0 : qle qzero r) (r2 : qle r (qadd qone qone)) :
    Ab y (qadd A (qadd (qadd qone qone) (qadd qone qone))) ∧
    Ab (qadd y r) (qadd A (qadd (qadd qone qone) (qadd qone qone))) ∧
    Ab (qadd (qadd y r) r) (qadd A (qadd (qadd qone qone) (qadd qone qone))) := by
  obtain ⟨y1, y2⟩ := hy
  have := qle_of_qlt qone_pos
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩

theorem three_combine {C3 S2 C1 S0 e : QExpr} (c : Ab (qadd C3 S2) e) (d : Ab (qsub S2 C1) e) (f : Ab (qadd C1 S0) e) :
    Ab (qsub C3 S0) (qadd (qadd e e) e) := by
  obtain ⟨c1, c2⟩ := c; obtain ⟨d1, d2⟩ := d; obtain ⟨f1, f2⟩ := f
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem three_eps (k : Nat) : qle (qadd (qadd (qeps (k + 2)) (qeps (k + 2))) (qeps (k + 2))) (qeps k) := by
  have e1 := qeps_succ_add (k + 1); have e0 := qeps_succ_add k; have p := qeps_nonneg (k + 2)
  rat_linarith

/-- `cos(y + 3ρ) = sin y`, uniformly for `|y| ≤ A`. -/
theorem three_shift {A : QExpr} (hA : qle qzero A) (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ y, Ab y A →
    Ab (qsub (Cn (qadd (qadd (qadd y (rho n)) (rho n)) (rho n)) n) (Sn y n)) (qeps k) := by
  obtain ⟨R, hR⟩ := rho_facts
  have hA2 : qle qzero (qadd A (qadd (qadd qone qone) (qadd qone qone))) := by have := two_pos; rat_linarith
  obtain ⟨N1, hN1⟩ := shift_unif hA2 (k + 2)
  refine ⟨R + N1, fun n hn y hy => ?_⟩
  obtain ⟨r1, r2, _, _⟩ := hR n (le_l' hn)
  have r0 : qle qzero (rho n) := by have := qle_of_qlt qone_pos; rat_linarith
  have r2' : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  obtain ⟨b0, b1, b2⟩ := bnd3 hy r0 r2'
  obtain ⟨_, c⟩ := hN1 n (le_r' hn) _ b2
  obtain ⟨d, _⟩ := hN1 n (le_r' hn) _ b1
  obtain ⟨_, f⟩ := hN1 n (le_r' hn) _ b0
  obtain ⟨g1, g2⟩ := three_combine c d f
  have t := three_eps k
  exact ⟨qle_trans (by have := t; rat_linarith : qle (qneg (qeps k)) (qneg (qadd (qadd (qeps (k + 2)) (qeps (k + 2))) (qeps (k + 2))))) g1,
         qle_trans g2 t⟩

/-- `cos` RISES ON `[2ρ, 4ρ]`, uniformly. -/
theorem cos_inc_win (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ u v,
    qle (qadd (rho n) (rho n)) u → qle u v → qle v (qadd (qadd (rho n) (rho n)) (qadd (rho n) (rho n))) →
    qle (Cn u n) (qadd (Cn v n) (qeps k)) := by
  obtain ⟨R, hR⟩ := rho_facts
  obtain ⟨N3, hN3⟩ := three_shift two_pos (k + 2)
  obtain ⟨Nu, hNu⟩ := sin_up_unif (k + 2)
  refine ⟨R + (N3 + Nu), fun n hn u v hu huv hv => ?_⟩
  obtain ⟨r1, r2', _, _⟩ := hR n (le_l' hn)
  have r2 : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  have rr : qle qzero (rho n) := by have := qle_of_qlt qone_pos; rat_linarith
  have yu : Ab (qsub u (qadd (qadd (rho n) (rho n)) (rho n))) (qadd qone qone) := by
    unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  have yv : Ab (qsub v (qadd (qadd (rho n) (rho n)) (rho n))) (qadd qone qone) := by
    unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨a1, a2⟩ := hN3 n (le_l' (le_r' hn)) _ yu
  obtain ⟨b1, b2⟩ := hN3 n (le_l' (le_r' hn)) _ yv
  have up := hNu n (le_r' (le_r' hn)) (qsub u (qadd (qadd (rho n) (rho n)) (rho n))) (qsub v (qadd (qadd (rho n) (rho n)) (rho n)))
    (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
  have eu := Cn_respects (show qEq (qadd (qadd (qadd (qsub u (qadd (qadd (rho n) (rho n)) (rho n))) (rho n)) (rho n)) (rho n)) u by
    unfold qsub; rat_ring) n
  have ev := Cn_respects (show qEq (qadd (qadd (qadd (qsub v (qadd (qadd (rho n) (rho n)) (rho n))) (rho n)) (rho n)) (rho n)) v by
    unfold qsub; rat_ring) n
  have e1 := qeps_succ_add (k + 1); have e0 := qeps_succ_add k
  have p := qeps_nonneg (k + 2)
  generalize Cn (qadd (qadd (qadd (qsub u (qadd (qadd (rho n) (rho n)) (rho n))) (rho n)) (rho n)) (rho n)) n = Cu' at *
  generalize Cn (qadd (qadd (qadd (qsub v (qadd (qadd (rho n) (rho n)) (rho n))) (rho n)) (rho n)) (rho n)) n = Cv' at *
  generalize Sn (qsub u (qadd (qadd (rho n) (rho n)) (rho n))) n = Su at *
  generalize Sn (qsub v (qadd (qadd (rho n) (rho n)) (rho n))) n = Sv at *
  generalize Cn u n = Cu at *; generalize Cn v n = Cv at *
  clear hR hN3 hNu yu yv r1 r2 r2' hu huv hv rr
  unfold qsub at *
  rat_linarith

end ZTrig

#print axioms ZTrig.cos_dec_win
#print axioms ZTrig.three_combine
#print axioms ZTrig.three_shift
#print axioms ZTrig.cos_inc_win
