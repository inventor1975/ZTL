import ZTrig6

/-!
# ZTrig7 — uniform in the argument: `sin` rises on `[−ρ, ρ]`; the shifts by `ρ`. Zero axioms.

Stage 7 of the full sine. The kernel's interval rule needs case analysis at each index (is the point left or right of
the minimum?), so the facts are stated UNIFORMLY: from some index on, for every argument in a range, with one error.

  * `sin_up_unif` — `−ρ_n ≤ a ≤ b ≤ ρ_n` ⇒ `S_n(a) ≤ S_n(b) + ε_k` (sum to product: `cos m ≥ −K4` on `|m| ≤ ρ_n`,
    `sin d ∈ [0, H]`);
  * `shift_unif` — `|x| ≤ A` ⇒ `|S_n(x + ρ_n) − C_n(x)|, |C_n(x + ρ_n) + S_n(x)| ≤ ε_k`.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

theorem K4_nonneg (n : Nat) : qle qzero (K4 n) := by
  have c := corner_nonneg (tm_nonneg two_pos) n (tm (qadd qone qone)) (tm_nonneg two_pos)
  unfold K4; generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) n = K at *; rat_linarith

/-- `cos m ≥ −K4` for `|m| ≤ ρ_n` (at large `n`). -/
theorem cos_ge {m : QExpr} {n : Nat} (h5 : 5 ≤ n) (hr : qle qzero (Cn (rho n) n)) (hr2 : qle (rho n) (qadd qone qone))
    (h1 : qle (qneg (rho n)) m) (h2 : qle m (rho n)) : qle (qneg (K4 n)) (Cn m n) := by
  cases qle_total qzero m with
  | inl h0 =>
      have c := cos_mono h0 h2 hr2 h5
      generalize Cn m n = C at *; generalize Cn (rho n) n = R at *; generalize K4 n = K at *
      unfold qsub at *; rat_linarith
  | inr h0 =>
      have c := cos_mono (a := qneg m) (b := rho n) (by rat_linarith) (by rat_linarith) hr2 h5
      have e := Cn_neg m n
      generalize Cn m n = C at *; generalize Cn (qneg m) n = C' at *; generalize Cn (rho n) n = R at *
      generalize K4 n = K at *
      unfold qsub at *; rat_linarith

theorem half_le {dd a b r : QExpr} (hdif : qEq (qadd dd dd) (qsub b a)) (ha : qle (qneg r) a) (hb : qle b r) :
    qle dd r := by unfold qsub at hdif; rat_linarith

theorem mid_le {mm a b r : QExpr} (hs : qEq (qadd mm mm) (qadd a b)) (ha : qle (qneg r) a) (hab : qle a b) (hb : qle b r) :
    qle (qneg r) mm ∧ qle mm r := ⟨by rat_linarith, by rat_linarith⟩

/-- `sin` RISES ON `[−ρ, ρ]`, uniformly. -/
theorem sin_up_unif (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ a b, qle (qneg (rho n)) a → qle a b → qle b (rho n) →
    qle (Sn a n) (qadd (Sn b n) (qeps k)) := by
  obtain ⟨N0, hN0⟩ := rho_facts
  have h2 := two_pos
  obtain ⟨H, hH⟩ := S_bounded h2
  have H0 : qle qzero H := qle_trans (S_nonneg h2 0) (hH 0)
  obtain ⟨B, hB1, _⟩ := qexpr_bound (qadd (qadd H H) qone)
  have hB : qle (qadd (qadd H H) qone) (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  obtain ⟨Nk, hNk⟩ := K4_small (k + B)
  refine ⟨N0 + (Nk + 5), fun n hn a b ha hab hb => ?_⟩
  obtain ⟨r1, r2, r3, _⟩ := hN0 n (Nat.le_trans (Nat.le_add_right N0 _) hn)
  have kk := hNk n (Nat.le_trans (Nat.le_trans (Nat.le_add_right Nk 5) (Nat.le_add_left _ N0)) hn)
  have n5 : 5 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left 5 Nk) (Nat.le_add_left _ N0)) hn
  have rr : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  obtain ⟨hh, h0⟩ := half_facts
  -- m = (a+b)/2, d = (b−a)/2
  have em : qEq (qadd (qmul (qadd a b) half) (qmul (qsub b a) half)) b := by
    have := qmul_respects (qEq_refl b) hh
    exact qEq_trans (show qEq _ (qmul b (qadd half half)) by unfold qsub; rat_ring) (qEq_trans this (qmul_one b))
  have ed : qEq (qsub (qmul (qadd a b) half) (qmul (qsub b a) half)) a := by
    have := qmul_respects (qEq_refl a) hh
    exact qEq_trans (show qEq _ (qmul a (qadd half half)) by unfold qsub; rat_ring) (qEq_trans this (qmul_one a))
  -- |m| ≤ ρ, 0 ≤ d ≤ ρ
  have hsum : qEq (qadd (qmul (qadd a b) half) (qmul (qadd a b) half)) (qadd a b) := by
    have := qmul_respects (qEq_refl (qadd a b)) hh
    exact qEq_trans (show qEq _ (qmul (qadd a b) (qadd half half)) by rat_ring) (qEq_trans this (qmul_one _))
  have hdif : qEq (qadd (qmul (qsub b a) half) (qmul (qsub b a) half)) (qsub b a) := by
    have := qmul_respects (qEq_refl (qsub b a)) hh
    exact qEq_trans (show qEq _ (qmul (qsub b a) (qadd half half)) by rat_ring) (qEq_trans this (qmul_one _))
  have d0 : qle qzero (qmul (qsub b a) half) := qmul_nonneg (by unfold qsub; rat_linarith) h0
  obtain ⟨m1, m2⟩ := mid_le hsum ha hab hb
  have d2 := half_le hdif ha hb
  have hm : Ab (qmul (qadd a b) half) (qadd qone qone) := ⟨by rat_linarith, by rat_linarith⟩
  have hd : Ab (qmul (qsub b a) half) (qadd qone qone) := ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨_, ⟨q1, q2⟩⟩ := sum_to_product hm hd n
  have sb := Sn_respects em n
  have sa := Sn_respects ed n
  have cg := cos_ge n5 r3 rr m1 m2
  have sd0 := nonneg_of_scaled (sin_lower d0 (qle_trans d2 rr) n5) d0
  obtain ⟨_, ⟨sh1, sh2⟩⟩ := CS_abs hd n
  have sH := hH n
  -- C(m)·S(d) ≥ −K4·H
  have p1 := qmul_nonneg (show qle qzero (qadd (Cn (qmul (qadd a b) half) n) (K4 n)) by rat_linarith) sd0
  have p2 := scale_l (show qle (Sn (qmul (qsub b a) half) n) H by rat_linarith) (K4_nonneg n)
  have f := ZExp.scale hB (qeps_nonneg (k + B))
  have f2 := scale_l kk (show qle qzero (qadd (qadd H H) qone) by rat_linarith)
  have pb := qpow2_mul_eps B k
  unfold K4 at *
  generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) n = K at *
  generalize Sn (qadd (qmul (qadd a b) half) (qmul (qsub b a) half)) n = S1 at *
  generalize Sn (qsub (qmul (qadd a b) half) (qmul (qsub b a) half)) n = S2 at *
  generalize Cn (qmul (qadd a b) half) n = Cm at *; generalize Sn (qmul (qsub b a) half) n = Sd at *
  generalize Sn a n = Sa at *; generalize Sn b n = Sb at *
  generalize qmul (qofInt (pow2 B)) (qeps (k + B)) = P at *
  generalize qmul (qadd (qadd H H) qone) (qeps (k + B)) = Q at *
  clear em ed hsum hdif hh h0 hm hd sh1 sh2 m1 m2 d2 cg r1 r2 r3 hB1 hB hH
  have g1 : qle (qsub Sa Sb) (qadd (qadd (qadd K K) (qadd K K)) (qadd (qmul (qadd (qadd K K) (qadd K K)) H) (qmul (qadd (qadd K K) (qadd K K)) H))) := by
    clear f f2 pb kk; unfold qsub at *; rat_linarith
  have g2 : qle (qadd (qadd (qadd K K) (qadd K K)) (qadd (qmul (qadd (qadd K K) (qadd K K)) H) (qmul (qadd (qadd K K) (qadd K K)) H))) Q := by
    clear g1 f pb kk q1 q2 sb sa sd0 sH p1 p2; rat_linarith
  have g3 : qle Q (qeps k) := by clear g1 g2 f2 kk q1 q2 sb sa sd0 sH p1 p2; rat_linarith
  have g := qle_trans g1 (qle_trans g2 g3)
  clear g1 g2 g3 f f2 pb kk q1 q2 sb sa sd0 sH p1 p2
  unfold qsub at g; rat_linarith

/-- THE SHIFTS BY `ρ`, uniformly: `|x| ≤ A` ⇒ `|S_n(x + ρ_n) − C_n(x)|, |C_n(x + ρ_n) + S_n(x)| ≤ ε_k`. -/
theorem shift_unif {A : QExpr} (hA : qle qzero A) (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ x, Ab x A →
    Ab (qsub (Sn (qadd x (rho n)) n) (Cn x n)) (qeps k) ∧ Ab (qadd (Cn (qadd x (rho n)) n) (Sn x n)) (qeps k) := by
  obtain ⟨HA, hHA⟩ := S_bounded hA
  have HA0 : qle qzero HA := qle_trans (S_nonneg hA 0) (hHA 0)
  obtain ⟨B, hB1, _⟩ := qexpr_bound HA
  have hB : qle HA (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  obtain ⟨Nc, hNc⟩ := corner_small hA two_pos (k + 2)
  obtain ⟨Ns, hNs⟩ := sin_rho (k + 2 + B)
  obtain ⟨Nr, hNr⟩ := cos_rho (k + 2 + B)
  obtain ⟨R, hR⟩ := rho_bnd
  refine ⟨Nc + (Ns + (Nr + R)), fun n hn x hx => ?_⟩
  have kc := hNc n (Nat.le_trans (Nat.le_add_right Nc _) hn)
  obtain ⟨sr1, sr2⟩ := hNs n (Nat.le_trans (Nat.le_trans (Nat.le_add_right Ns _) (Nat.le_add_left _ Nc)) hn)
  obtain ⟨cr1, cr2⟩ := hNr n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right Nr R) (Nat.le_add_left _ Ns))
    (Nat.le_add_left _ Nc)) hn)
  have hr := hR n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left R Nr) (Nat.le_add_left _ Ns))
    (Nat.le_add_left _ Nc)) hn)
  obtain ⟨⟨c1, c2⟩, ⟨s1, s2⟩⟩ := add_bounds hx hr n
  obtain ⟨⟨x1, x2⟩, ⟨y1, y2⟩⟩ := CS_abs hx n
  have hh := hHA n
  have δ := qeps (k + 2 + B)
  -- the deviations of sin ρ from 1 and cos ρ from 0
  have dS : Ab (qsub (Sn (rho n) n) qone) (qeps (k + 2 + B)) := by
    have a : qle (qsub qone (qeps (k + 2 + B))) (Sn (rho n) n) := sr1
    have b : qle (Sn (rho n) n) (qadd qone (qeps (k + 2 + B))) := sr2
    generalize Sn (rho n) n = S at *; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have dC : Ab (Cn (rho n) n) (qeps (k + 2 + B)) := by
    have a : qle (qsub qzero (qeps (k + 2 + B))) (Cn (rho n) n) := cr1
    have b : qle (Cn (rho n) n) (qadd qzero (qeps (k + 2 + B))) := cr2
    generalize Cn (rho n) n = C at *; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have aC : Ab (Cn x n) HA := ⟨by rat_linarith, by rat_linarith⟩
  have aS : Ab (Sn x n) HA := ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨m1, m2⟩ := mul_abs aC dS
  obtain ⟨m3, m4⟩ := mul_abs aS dC
  obtain ⟨m5, m6⟩ := mul_abs aC dC
  obtain ⟨m7, m8⟩ := mul_abs aS dS
  have f := scale_l hB (qeps_nonneg (k + 2 + B))
  have pb := qpow2_mul_eps B (k + 2)
  have hδ : qle (qmul HA (qeps (k + 2 + B))) (qeps (k + 2)) := by
    have c : qEq (qmul (qofInt (pow2 B)) (qeps (k + 2 + B))) (qmul (qeps (k + 2 + B)) (qofInt (pow2 B))) := qmul_comm _ _
    have f' := ZExp.scale hB (qeps_nonneg (k + 2 + B))
    generalize qmul HA (qeps (k + 2 + B)) = u at *
    generalize qmul (qofInt (pow2 B)) (qeps (k + 2 + B)) = v at *
    generalize qmul (qeps (k + 2 + B)) (qofInt (pow2 B)) = w at *
    generalize qmul HA (qofInt (pow2 B)) = w' at *
    clear f; rat_linarith
  have e1 := qeps_succ_add (k + 1); have e0 := qeps_succ_add k
  have i1 : qEq (qsub (Sn (qadd x (rho n)) n) (Cn x n))
      (qadd (qadd (qsub (Sn (qadd x (rho n)) n) (qadd (qmul (Cn x n) (Sn (rho n) n)) (qmul (Sn x n) (Cn (rho n) n))))
        (qmul (Cn x n) (qsub (Sn (rho n) n) qone))) (qmul (Sn x n) (Cn (rho n) n))) := by unfold qsub; rat_ring
  have i2 : qEq (qadd (Cn (qadd x (rho n)) n) (Sn x n))
      (qadd (qadd (qsub (Cn (qadd x (rho n)) n) (qsub (qmul (Cn x n) (Cn (rho n) n)) (qmul (Sn x n) (Sn (rho n) n))))
        (qmul (Cn x n) (Cn (rho n) n))) (qneg (qmul (Sn x n) (qsub (Sn (rho n) n) qone)))) := by unfold qsub; rat_ring
  generalize corner (tm A) (tm (qadd qone qone)) n = K at *
  generalize qsub (Sn (qadd x (rho n)) n) (qadd (qmul (Cn x n) (Sn (rho n) n)) (qmul (Sn x n) (Cn (rho n) n))) = E1 at *
  generalize qsub (Cn (qadd x (rho n)) n) (qsub (qmul (Cn x n) (Cn (rho n) n)) (qmul (Sn x n) (Sn (rho n) n))) = E2 at *
  generalize qmul (Cn x n) (qsub (Sn (rho n) n) qone) = P1 at *
  generalize qmul (Sn x n) (Cn (rho n) n) = P2 at *
  generalize qmul (Cn x n) (Cn (rho n) n) = P3 at *
  generalize qmul (Sn x n) (qsub (Sn (rho n) n) qone) = P4 at *
  generalize qmul HA (qeps (k + 2 + B)) = W at *
  generalize qsub (Sn (qadd x (rho n)) n) (Cn x n) = D1 at *
  generalize qadd (Cn (qadd x (rho n)) n) (Sn x n) = D2 at *
  clear sr1 sr2 cr1 cr2 hr x1 x2 y1 y2 hh dS dC aC aS f pb hB hB1 hHA hNc hNs hNr hR
  have p := qeps_nonneg (k + 2)
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩

end ZTrig

#print axioms ZTrig.K4_nonneg
#print axioms ZTrig.cos_ge
#print axioms ZTrig.sin_up_unif
#print axioms ZTrig.shift_unif
