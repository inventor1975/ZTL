import ZTrig14

/-!
# ZTrig15 — the slope of `tan`: the kernel's `(tan u)' = (1 + V²)·Du`. Zero axioms.

Stage 15 of the full sine. As for `sin`/`cos` (`ZTrig12`), a chord on a `2^K` grid — here only where `cos` is
bounded below (`chord_gen_P`): one step `tan(x + δ) − tan x − δ·(1 + tan² x) = (1/C)²(1/C')·B`,
`B = C·(S(δ) − δ) + δ·(C − C')` plus the formulas' corners — `O(δ²)` with `C, C' ≥ c > 0`.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-- THE CHORD ON A DOMAIN: as `chord_gen`, the steps needed only where `P` holds, `P` eventual along any reading in
`[lu, hu]` (`tan`: `cos` bounded below).  a value function `F` whose grid steps are `δ·D + O(δ²)` (plus a vanishing part), `D`
read in `[dl, dh]` over `[lu, hu]`: from some index on, `F(b) − F(a) = (b − a)·χ` up to `ε_k`, `χ ∈ [dl, dh] ± ε_k`. -/
theorem chord_gen_P (F D : QExpr → Nat → QExpr) (P : QExpr → Nat → Prop) (hF : ∀ x y n, qEq x y → qEq (F x n) (F y n))
    (hPr : ∀ x y n, qEq x y → P x n → P y n)
    (step : ∀ {A : QExpr}, qle qzero A → ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x δ a, Ab x A → Ab δ qone →
      Ab δ a → qle a qone → P x n → P (qadd x δ) n →
      Ab (qsub (qsub (F (qadd x δ) n) (F x n)) (qmul δ (D x n))) (qadd (qeps k) (qmul (qmul a a) H)))
    {a b : Nat → QExpr} {lu hu dl dh : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu)
    (hP : ∀ y : Nat → QExpr, Ev y lu hu → ∃ N, ∀ n, N ≤ n → P (y n) n)
    (hD : ∀ x : Nat → QExpr, Ev x lu hu → Ev (fun n => D (x n) n) dl dh) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub dl (qeps k)) χ ∧ qle χ (qadd dh (qeps k)) ∧
      Ab (qsub (qsub (F (b n) n) (F (a n) n)) (qmul (qsub (b n) (a n)) χ)) (qeps k) := by
  intro k
  obtain ⟨M, _, hM0, _, ml, mh, _, _⟩ := bound4 lu hu lu hu
  have o := qle_of_qlt qone_pos
  have hA0 : qle qzero (qadd M qone) := by rat_linarith
  obtain ⟨H, hH0, hH⟩ := step hA0
  have hD0 : qle qzero (qadd (qadd M qone) (qadd M qone)) := by rat_linarith
  generalize hAd : qadd M qone = A at hA0 hD0 hH
  generalize hDd : qadd A A = Dm at hD0
  obtain ⟨Bc, hB1, _⟩ := qexpr_bound (qadd (qmul (qmul Dm Dm) H) Dm)
  have hX0 : qle qzero (qmul (qmul Dm Dm) H) := qmul_nonneg (qmul_nonneg hD0 hD0) hH0
  have hC : qle (qadd (qmul (qmul Dm Dm) H) Dm) (qofInt (pow2 Bc)) := by unfold qsub at hB1; rat_linarith
  -- K: the grid's depth
  have pe := qpow2_mul_eps Bc (k + 1)
  have sK := ZExp.scale hC (qeps_nonneg ((k + 1) + Bc))
  have c1 := qmul_comm (qofInt (pow2 Bc)) (qeps ((k + 1) + Bc))
  have d1 : qEq (qmul (qadd (qmul (qmul Dm Dm) H) Dm) (qeps ((k + 1) + Bc)))
      (qadd (qmul (qmul (qmul Dm Dm) H) (qeps ((k + 1) + Bc))) (qmul Dm (qeps ((k + 1) + Bc)))) := by rat_ring
  have p1 := qmul_nonneg hX0 (qeps_nonneg ((k + 1) + Bc))
  have p2 := qmul_nonneg hD0 (qeps_nonneg ((k + 1) + Bc))
  have ek := qeps_succ_add k
  have e1 := qeps_le_one (k + 1)
  have bK1 : qle (qmul (qmul (qmul Dm Dm) H) (qeps ((k + 1) + Bc))) (qeps (k + 1)) := by
    generalize qmul (qadd (qmul (qmul Dm Dm) H) Dm) (qeps ((k + 1) + Bc)) = P at *
    generalize qmul (qofInt (pow2 Bc)) (qeps ((k + 1) + Bc)) = Q at *
    generalize qmul (qeps ((k + 1) + Bc)) (qofInt (pow2 Bc)) = Q' at *
    rat_linarith
  have bK2 : qle (qmul Dm (qeps ((k + 1) + Bc))) qone := by
    generalize qmul (qadd (qmul (qmul Dm Dm) H) Dm) (qeps ((k + 1) + Bc)) = P at *
    generalize qmul (qofInt (pow2 Bc)) (qeps ((k + 1) + Bc)) = Q at *
    generalize qmul (qeps ((k + 1) + Bc)) (qofInt (pow2 Bc)) = Q' at *
    rat_linarith
  generalize hK : (k + 1) + Bc = K at bK1 bK2 p2
  -- the step's precision: 2^K·ε' = ε_{k+1}
  have pS := qpow2_mul_eps K (k + 1)
  have qn := qnat_pow2 K
  have eS : qEq (qmul (qnat (2 ^ K)) (qeps ((k + 1) + K))) (qeps (k + 1)) :=
    qEq_trans (qmul_respects qn (qEq_refl _)) pS
  obtain ⟨Ns, hNs⟩ := hH ((k + 1) + K)
  -- the derivative at every grid point
  obtain ⟨Nd, hNd⟩ := fin_N (P := fun j n => j < 2 ^ K →
      qle (qsub dl (qeps k)) (D (xg (a n) (b n) K j) n) ∧ qle (D (xg (a n) (b n) K j) n) (qadd dh (qeps k)))
    (fun j => by
      cases Nat.lt_or_ge j (2 ^ K) with
      | inl hj =>
        obtain ⟨N, hN⟩ := hD _ (Ev_xg ha hb (Nat.le_of_lt hj)) k
        exact ⟨N, fun n hn _ => hN n hn⟩
      | inr hj => exact ⟨0, fun _ _ h => absurd h (Nat.not_lt_of_ge hj)⟩) (2 ^ K)
  obtain ⟨Np, hNp⟩ := fin_N (P := fun j n => j < 2 ^ K + 1 → P (xg (a n) (b n) K j) n)
    (fun j => by
      cases Nat.lt_or_ge j (2 ^ K + 1) with
      | inl hj =>
        obtain ⟨N, hN⟩ := hP _ (Ev_xg ha hb (Nat.le_of_lt_succ hj))
        exact ⟨N, fun n hn _ => hN n hn⟩
      | inr hj => exact ⟨0, fun _ _ h => absurd h (Nat.not_lt_of_ge hj)⟩) (2 ^ K + 1)
  obtain ⟨Na, hNa⟩ := ha 0
  obtain ⟨Nb, hNb⟩ := hb 0
  refine ⟨Ns + (Nd + (Na + (Nb + Np))), fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := hNa n (le_l' (le_r' (le_r' hn)))
  obtain ⟨b1, b2⟩ := hNb n (le_l' (le_r' (le_r' (le_r' hn))))
  have hPg := hNp n (le_r' (le_r' (le_r' (le_r' hn))))
  have z := qeps_zero
  obtain ⟨m1, m2⟩ := ml; obtain ⟨m3, m4⟩ := mh
  unfold qsub at m1 m2 m3 m4 a1 b1
  -- the grid's points within `A`, the step within `Dm·ε_K ≤ 1`
  have lo1 : qle (qneg A) (qsub lu qone) := by rw [← hAd]; unfold qsub; rat_linarith
  have hi1 : qle (qadd hu qone) A := by rw [← hAd]; rat_linarith
  have aL : qle (qsub lu qone) (a n) := by unfold qsub; rat_linarith
  have aU : qle (a n) (qadd hu qone) := by rat_linarith
  have bL : qle (qsub lu qone) (b n) := by unfold qsub; rat_linarith
  have bU : qle (b n) (qadd hu qone) := by rat_linarith
  have gA : ∀ j, j ≤ 2 ^ K → Ab (xg (a n) (b n) K j) A := fun j hj => by
    obtain ⟨t0, t1⟩ := T_unit hj
    obtain ⟨c1, c2⟩ := conv t0 t1 aL aU bL bU
    have e := xg_T (a n) (b n) K j
    generalize xg (a n) (b n) K j = X at *
    generalize qadd (a n) (qmul (qmul (qnat j) (qeps K)) (qsub (b n) (a n))) = Y at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  have hΔ : Ab (qsub (b n) (a n)) Dm := by
    rw [← hDd]; obtain ⟨x1, x2⟩ := gA 0 (Nat.zero_le _)
    have e0 := xg_zero (a n) (b n) K
    generalize xg (a n) (b n) K 0 = X at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have hδ : Ab (qmul (qsub (b n) (a n)) (qeps K)) (qmul Dm (qeps K)) :=
    mul_abs hΔ ⟨by have := qeps_nonneg K; rat_linarith, qle_refl _⟩
  have hδ1 : Ab (qmul (qsub (b n) (a n)) (qeps K)) qone := by
    obtain ⟨d1, d2⟩ := hδ; exact ⟨by rat_linarith, by rat_linarith⟩
  -- each step
  have st : ∀ j, j < 2 ^ K → Ab (qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)))
      (qadd (qeps ((k + 1) + K)) (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)) := fun j hj => by
    have s := hNs n (le_l' hn) _ _ _ (gA j (Nat.le_of_lt hj)) hδ1 hδ bK2 (hPg j (Nat.lt_succ_of_lt hj) (Nat.lt_succ_of_lt hj))
      (hPr _ _ n (xg_succ (a n) (b n) K j) (hPg (j + 1) (Nat.succ_lt_succ hj) (Nat.succ_lt_succ hj)))
    have r := hF _ _ n (qEq_symm (xg_succ (a n) (b n) K j))
    obtain ⟨s1, s2⟩ := s
    generalize F (qadd (xg (a n) (b n) K j) (qmul (qsub (b n) (a n)) (qeps K))) n = P at *
    generalize F (xg (a n) (b n) K (j + 1)) n = P' at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨S1, S2⟩ := bs_abs_c (2 ^ K) st
  -- the sum, rearranged
  have tl := bs_tele (fun j => F (xg (a n) (b n) K j) n) (2 ^ K)
  have sb := bs_sub (fun j => qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
    (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)) (2 ^ K)
  have sc := bs_scale (qmul (qsub (b n) (a n)) (qeps K)) (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)
  have fT := hF _ _ n (xg_top (a n) (b n) K)
  have f0 := hF _ _ n (xg_zero (a n) (b n) K)
  have et := err_total (qeps ((k + 1) + K)) Dm H K
  have bd := hNd n (le_l' (le_r' hn))
  obtain ⟨χ1, χ2⟩ := avg_in (K := K) (bs_in_c (2 ^ K) (fun j hj => bd j hj hj))
  refine ⟨qmul (qeps K) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)), χ1, χ2, ?_⟩
  have re : qEq (qmul (qmul (qsub (b n) (a n)) (qeps K)) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)))
      (qmul (qsub (b n) (a n)) (qmul (qeps K) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)))) := by rat_ring
  generalize bs (fun j => qsub (qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n))
      (qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n))) (2 ^ K) = Tot at *
  generalize bs (fun j => qsub (F (xg (a n) (b n) K (j + 1)) n) (F (xg (a n) (b n) K j) n)) (2 ^ K) = Tl at *
  generalize bs (fun j => qmul (qmul (qsub (b n) (a n)) (qeps K)) (D (xg (a n) (b n) K j) n)) (2 ^ K) = Sd at *
  generalize qmul (qmul (qsub (b n) (a n)) (qeps K)) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K)) = Sd' at *
  generalize qmul (qsub (b n) (a n)) (qmul (qeps K) (bs (fun j => D (xg (a n) (b n) K j) n) (2 ^ K))) = W at *
  generalize F (xg (a n) (b n) K (2 ^ K)) n = Fb' at *; generalize F (xg (a n) (b n) K 0) n = Fa' at *
  generalize F (b n) n = Fb at *; generalize F (a n) n = Fa at *
  generalize qmul (qnat (2 ^ K)) (qadd (qeps ((k + 1) + K)) (qmul (qmul (qmul Dm (qeps K)) (qmul Dm (qeps K))) H)) = E at *
  generalize qmul (qnat (2 ^ K)) (qeps ((k + 1) + K)) = E1 at *
  generalize qmul (qmul (qmul Dm Dm) H) (qeps K) = E2 at *
  clear hNs hNd hNa hNb hNp hPg hH hD st gA bd χ1 χ2
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem inv_bound {y c : QExpr} (hc : qlt qzero c) (hy : qle c y) : qle qzero (qinv' y) ∧ qle (qinv' y) (qinv' c) := by
  have yp : qlt qzero y := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hc) hy,
    fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hy h)⟩
  have i0 := qinv'_nonneg_of_pos yp
  have ic0 := qinv'_nonneg_of_pos hc
  have u := qmul_inv'_cancel (ne_zero_of_lt yp)
  have w := qmul_inv'_cancel (ne_zero_of_lt hc)
  have s1 := ZExp.scale hy i0
  have s2 := ZExp.scale (show qle (qmul c (qinv' y)) qone by rat_linarith) ic0
  have e1 : qEq (qmul (qmul c (qinv' y)) (qinv' c)) (qmul (qinv' y) (qmul c (qinv' c))) := by rat_ring
  have e2 := qmul_respects (qEq_refl (qinv' y)) w
  have o1 : qEq (qmul (qinv' y) qone) (qinv' y) := by rat_ring
  have o2 : qEq (qmul qone (qinv' c)) (qinv' c) := by rat_ring
  refine ⟨i0, ?_⟩
  generalize qmul (qmul c (qinv' y)) (qinv' c) = P at *
  generalize qmul (qinv' y) (qmul c (qinv' c)) = Q at *
  generalize qmul (qinv' y) qone = R at *
  generalize qmul qone (qinv' c) = T at *
  rat_linarith

/-- The step of `tan`, exactly: `tan(x + δ) − tan x − δ·(1 + tan² x) = (1/C)²(1/C')·B`. -/
theorem tan_id {C S C' S' iC iC' δ : QExpr} (hu : qEq (qmul C iC) qone) (hv : qEq (qmul C' iC') qone) :
    qEq (qsub (qsub (qmul S' iC') (qmul S iC)) (qmul δ (qadd qone (qmul (qmul S iC) (qmul S iC)))))
      (qmul (qmul (qmul iC iC) iC')
        (qsub (qmul (qsub (qmul S' C) (qmul S C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul S S))) C'))) := by
  have R : qEq (qmul (qmul (qmul iC iC) iC')
        (qsub (qmul (qsub (qmul S' C) (qmul S C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul S S))) C')))
      (qsub (qsub (qsub (qmul (qmul (qmul S' iC') (qmul C iC)) (qmul C iC))
        (qmul (qmul (qmul S iC) (qmul C iC)) (qmul C' iC')))
        (qmul (qmul (qmul δ (qmul C iC)) (qmul C iC)) (qmul C' iC')))
        (qmul (qmul δ (qmul (qmul S iC) (qmul S iC))) (qmul C' iC'))) := by unfold qsub; rat_ring
  have a1 := qmul_respects (qmul_respects (qEq_refl (qmul S' iC')) hu) hu
  have a2 := qmul_respects (qmul_respects (qEq_refl (qmul S iC)) hu) hv
  have a3 := qmul_respects (qmul_respects (qmul_respects (qEq_refl δ) hu) hu) hv
  have a4 := qmul_respects (qEq_refl (qmul δ (qmul (qmul S iC) (qmul S iC)))) hv
  have o1 : qEq (qmul (qmul (qmul S' iC') qone) qone) (qmul S' iC') := by rat_ring
  have o2 : qEq (qmul (qmul (qmul S iC) qone) qone) (qmul S iC) := by rat_ring
  have o3 : qEq (qmul (qmul (qmul δ qone) qone) qone) δ := by rat_ring
  have o4 : qEq (qmul (qmul δ (qmul (qmul S iC) (qmul S iC))) qone) (qmul δ (qmul (qmul S iC) (qmul S iC))) := by rat_ring
  have l : qEq (qmul δ (qadd qone (qmul (qmul S iC) (qmul S iC)))) (qadd δ (qmul δ (qmul (qmul S iC) (qmul S iC)))) := by rat_ring
  generalize qmul (qmul (qmul iC iC) iC')
        (qsub (qmul (qsub (qmul S' C) (qmul S C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul S S))) C')) = Rr at *
  generalize qmul (qmul (qmul S' iC') (qmul C iC)) (qmul C iC) = T1 at *
  generalize qmul (qmul (qmul S iC) (qmul C iC)) (qmul C' iC') = T2 at *
  generalize qmul (qmul (qmul δ (qmul C iC)) (qmul C iC)) (qmul C' iC') = T3 at *
  generalize qmul (qmul δ (qmul (qmul S iC) (qmul S iC))) (qmul C' iC') = T4 at *
  generalize qmul (qmul (qmul S' iC') qone) qone = U1 at *
  generalize qmul (qmul (qmul S iC) qone) qone = U2 at *
  generalize qmul (qmul (qmul δ qone) qone) qone = U3 at *
  generalize qmul (qmul δ (qmul (qmul S iC) (qmul S iC))) qone = U4 at *
  generalize qmul δ (qadd qone (qmul (qmul S iC) (qmul S iC))) = W at *
  generalize qmul δ (qmul (qmul S iC) (qmul S iC)) = W4 at *
  generalize qmul S' iC' = X1 at *; generalize qmul S iC = X2 at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- ONE GRID STEP OF `tan` (index `m + 2`), `cos ≥ c > 0` at both points: within `(1/c)³·(T1 + T2 + T3 + T4)`. -/
theorem tan_step {x δ A a c : QExpr} (hx : Ab x A) (h1 : Ab δ qone) (hδ : Ab δ a) (hc : qlt qzero c) (m : Nat)
    (cx : qle c (Cn x (m + 2))) (cx' : qle c (Cn (qadd x δ) (m + 2))) :
    Ab (qsub (qsub (qmul (Sn (qadd x δ) (m + 2)) (qinv' (Cn (qadd x δ) (m + 2))))
        (qmul (Sn x (m + 2)) (qinv' (Cn x (m + 2)))))
        (qmul δ (qadd qone (qmul (qmul (Sn x (m + 2)) (qinv' (Cn x (m + 2)))) (qmul (Sn x (m + 2)) (qinv' (Cn x (m + 2))))))))
      (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c))
        (qadd (qadd (qmul (S A (m + 2)) (qmul (qmul a a) (S a m))) (qmul a (qmul a (S (qadd A qone) (m + 2)))))
          (qadd (qmul (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) (S A (m + 2)))
            (qmul (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2)))) (S (qadd A qone) (m + 2)))))) := by
  have o := qle_of_qlt qone_pos
  obtain ⟨x1, x2⟩ := hx
  obtain ⟨d1, d2⟩ := h1
  have hx1 : Ab (qadd x δ) (qadd A qone) := ⟨by rat_linarith, by rat_linarith⟩
  have hxA1 : Ab x (qadd A qone) := ⟨by rat_linarith, by rat_linarith⟩
  have hnx : Ab (qneg x) A := ⟨by rat_linarith, by rat_linarith⟩
  have hd : Ab (qsub (qadd x δ) x) a := by
    obtain ⟨e1, e2⟩ := hδ; unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  -- the pieces
  obtain ⟨_, eA⟩ := add_bounds hx1 hnx (m + 2)
  obtain ⟨eB1, eB2⟩ := pyth ⟨x1, x2⟩ (m + 1)
  have nS := near_S hδ m
  have lip := (CS_lip hx1 hxA1 hd (m + 2)).1
  have cA := (CS_abs ⟨x1, x2⟩ (m + 2)).1
  have cA1 := (CS_abs hx1 (m + 2)).1
  have r1 := Sn_respects (show qEq (qadd (qadd x δ) (qneg x)) δ by rat_ring) (m + 2)
  have r2 := Sn_neg x (m + 2)
  have r3 := Cn_neg x (m + 2)
  -- the reciprocals
  have cp : qlt qzero (Cn x (m + 2)) := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hc) cx,
    fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans cx h)⟩
  have cp' : qlt qzero (Cn (qadd x δ) (m + 2)) := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hc) cx',
    fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans cx' h)⟩
  have hu := qmul_inv'_cancel (ne_zero_of_lt cp)
  have hv := qmul_inv'_cancel (ne_zero_of_lt cp')
  obtain ⟨i0, i1⟩ := inv_bound hc cx
  obtain ⟨j0, j1⟩ := inv_bound hc cx'
  have id := tan_id (S := Sn x (m + 2)) (S' := Sn (qadd x δ) (m + 2)) (δ := δ) hu hv
  -- |B|
  generalize Sn x (m + 2) = Sv at *; generalize Cn x (m + 2) = C at *
  generalize Sn (qadd x δ) (m + 2) = S' at *; generalize Cn (qadd x δ) (m + 2) = C' at *
  generalize Sn δ (m + 2) = Sd at *
  generalize Sn (qadd (qadd x δ) (qneg x)) (m + 2) = Sx at *
  generalize Sn (qneg x) (m + 2) = Snx at *; generalize Cn (qneg x) (m + 2) = Cnx at *
  have E1 : Ab (qsub (qsub (qmul S' C) (qmul Sv C')) Sd)
      (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) := by
    obtain ⟨g1, g2⟩ := eA
    have q1 : qEq (qmul C' Snx) (qneg (qmul C' Sv)) := by
      have := qmul_respects (qEq_refl C') r2; exact qEq_trans this (by rat_ring)
    have q2 : qEq (qmul S' Cnx) (qmul S' C) := qmul_respects (qEq_refl S') r3
    have q3 : qEq (qmul Sv C') (qmul C' Sv) := qmul_comm _ _
    generalize qmul C' Snx = P1 at *; generalize qmul S' Cnx = P2 at *
    generalize qmul S' C = P3 at *; generalize qmul Sv C' = P4 at *; generalize qmul C' Sv = P5 at *
    generalize corner (tm (qadd A qone)) (tm A) (m + 2) = K at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have Bid : qEq (qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C'))
      (qadd (qsub (qmul C (qsub Sd δ)) (qmul δ (qsub C' C)))
        (qadd (qmul (qsub (qsub (qmul S' C) (qmul Sv C')) Sd) C) (qmul (qmul δ (qsub qone (qadd (qmul C C) (qmul Sv Sv)))) C'))) := by
    unfold qsub; rat_ring
  obtain ⟨t1, t2⟩ := mul_abs cA nS
  obtain ⟨t3, t4⟩ := mul_abs hδ lip
  obtain ⟨t5, t6⟩ := mul_abs E1 cA
  obtain ⟨t7, t8⟩ := mul_abs (mul_abs ⟨d1, d2⟩ ⟨eB1, eB2⟩) cA1
  have hB : Ab (qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C'))
      (qadd (qadd (qmul (S A (m + 2)) (qmul (qmul a a) (S a m))) (qmul a (qmul a (S (qadd A qone) (m + 2)))))
          (qadd (qmul (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) (S A (m + 2)))
            (qmul (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2)))) (S (qadd A qone) (m + 2))))) := by
    generalize qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C') = B at *
    generalize qmul C (qsub Sd δ) = U1 at *; generalize qmul δ (qsub C' C) = U2 at *
    generalize qmul (qsub (qsub (qmul S' C) (qmul Sv C')) Sd) C = U3 at *
    generalize qmul (qmul δ (qsub qone (qadd (qmul C C) (qmul Sv Sv)))) C' = U4 at *
    generalize qmul (S A (m + 2)) (qmul (qmul a a) (S a m)) = V1 at *
    generalize qmul a (qmul a (S (qadd A qone) (m + 2))) = V2 at *
    generalize qmul (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) (S A (m + 2)) = V3 at *
    generalize qmul (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2)))) (S (qadd A qone) (m + 2)) = V4 at *
    unfold qsub at Bid; exact ⟨by rat_linarith, by rat_linarith⟩
  have hI : Ab (qmul (qmul (qinv' C) (qinv' C)) (qinv' C')) (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) :=
    mul_abs (mul_abs ⟨by rat_linarith, i1⟩ ⟨by rat_linarith, i1⟩) ⟨by rat_linarith, j1⟩
  obtain ⟨f1, f2⟩ := mul_abs hI hB
  generalize qmul (qmul (qmul (qinv' C) (qinv' C)) (qinv' C'))
    (qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C')) = Z at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- The `tan` step made uniform: `cos ≥ c > 0` at both points, `|x| ≤ A`. -/
theorem tan_step_unif {A c : QExpr} (hA : qle qzero A) (hc : qlt qzero c) : ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n →
    ∀ x δ a, Ab x A → Ab δ qone → Ab δ a → qle a qone → qle c (Cn x n) → qle c (Cn (qadd x δ) n) →
    Ab (qsub (qsub (qmul (Sn (qadd x δ) n) (qinv' (Cn (qadd x δ) n))) (qmul (Sn x n) (qinv' (Cn x n))))
        (qmul δ (qadd qone (qmul (qmul (Sn x n) (qinv' (Cn x n))) (qmul (Sn x n) (qinv' (Cn x n)))))))
      (qadd (qeps k) (qmul (qmul a a) H)) := by
  have o := qle_of_qlt qone_pos
  have hA1 : qle qzero (qadd A qone) := by rat_linarith
  obtain ⟨HA, hHA⟩ := S_bounded hA
  obtain ⟨HA1, hHA1⟩ := S_bounded hA1
  obtain ⟨H1, hH1⟩ := S_bounded o
  have HA0 : qle qzero HA := qle_trans (S_nonneg hA 0) (hHA 0)
  have HA10 : qle qzero HA1 := qle_trans (S_nonneg hA1 0) (hHA1 0)
  have H10 : qle qzero H1 := qle_trans (S_nonneg o 0) (hH1 0)
  have ic0 := qinv'_nonneg_of_pos hc
  have ic3 : qle qzero (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) := qmul_nonneg (qmul_nonneg ic0 ic0) ic0
  have Hn := qmul_nonneg ic3 (show qle qzero (qadd (qmul HA H1) HA1) by have := qmul_nonneg HA0 H10; rat_linarith)
  refine ⟨qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qmul HA H1) HA1), Hn, fun k => ?_⟩
  have Y0 := qmul_nonneg ic3 (show qle qzero (qadd (qadd HA HA) (qadd HA1 HA1)) by rat_linarith)
  obtain ⟨Bc, hB1, _⟩ := qexpr_bound (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qadd HA HA) (qadd HA1 HA1)))
  have hY : qle (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qadd HA HA) (qadd HA1 HA1))) (qofInt (pow2 Bc)) := by
    unfold qsub at hB1; rat_linarith
  obtain ⟨N1, h1⟩ := corner_small hA1 hA (k + Bc)
  obtain ⟨N2, h2⟩ := corner_small hA hA (k + Bc)
  refine ⟨(N1 + N2) + 2, fun n hn x δ a hx hd1 hδ a1 cx cx' => ?_⟩
  have a0 : qle qzero a := by obtain ⟨d1, d2⟩ := hδ; rat_linarith
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n' => cases n' with
    | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
    | succ m =>
      have hm : N1 + N2 ≤ m + 2 := Nat.le_trans (Nat.le_add_right _ 2) hn
      obtain ⟨s1, s2⟩ := tan_step hx hd1 hδ hc m cx cx'
      have K1 := h1 (m + 2) (le_l' hm)
      have K2 := h2 (m + 2) (le_r' hm)
      have K10 := corner_nonneg (tm_nonneg hA) (m + 2) (tm (qadd A qone)) (tm_nonneg hA1)
      have K20 := corner_nonneg (tm_nonneg hA) (m + 2) (tm A) (tm_nonneg hA)
      have sA := hHA (m + 2); have sA1 := hHA1 (m + 2)
      have sA0 := S_nonneg hA (m + 2); have sA10 := S_nonneg hA1 (m + 2)
      have sa := qle_trans (S_mono_x a0 a1 m) (hH1 m)
      have sa0 := S_nonneg a0 m
      have aa := qmul_nonneg a0 a0
      -- the four terms against their constants
      have u1 := qle_trans (scale_l (scale_l sa aa) sA0) (ZExp.scale sA (qmul_nonneg aa H10))
      have u2 := scale_l (scale_l sA1 a0) a0
      have u3 := scale_l sA (show qle qzero (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) by rat_linarith)
      have u3' : qEq (qmul (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) (S A (m + 2)))
          (qmul (S A (m + 2)) (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2)))) := qmul_comm _ _
      have u4 := scale_l sA1 (show qle qzero (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2)))) by
        have := qmul_nonneg o (show qle qzero (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2))) by rat_linarith); exact this)
      have u4' : qEq (qmul (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2)))) (S (qadd A qone) (m + 2)))
          (qmul (S (qadd A qone) (m + 2)) (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2))))) := qmul_comm _ _
      have K1' : qle (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2)))
          (qadd (qeps (k + Bc)) (qeps (k + Bc))) := by rat_linarith
      have K2' : qle (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2))))
          (qmul qone (qadd (qeps (k + Bc)) (qeps (k + Bc)))) := scale_l (by rat_linarith) o
      have w1 := ZExp.scale K1' HA0
      have w2 := ZExp.scale K2' HA10
      have W0 : qEq (qadd (qmul (qadd (qeps (k + Bc)) (qeps (k + Bc))) HA) (qmul (qmul qone (qadd (qeps (k + Bc)) (qeps (k + Bc)))) HA1))
          (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qadd HA1 HA1))) := by rat_ring
      have e0 := qeps_nonneg (k + Bc)
      have w4 := scale_l hY e0
      have pe := qpow2_mul_eps Bc k
      have cm := qmul_comm (qofInt (pow2 Bc)) (qeps (k + Bc))
      generalize hI3 : qmul (qmul (qinv' c) (qinv' c)) (qinv' c) = I3 at *
      generalize hT1 : qmul (S A (m + 2)) (qmul (qmul a a) (S a m)) = T1 at *
      generalize hT2 : qmul a (qmul a (S (qadd A qone) (m + 2))) = T2 at *
      generalize hT3 : qmul (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) (S A (m + 2)) = T3 at *
      generalize hT4 : qmul (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2)))) (S (qadd A qone) (m + 2)) = T4 at *
      have id2 : qEq (qmul I3 (qadd (qmul HA (qmul (qmul a a) H1)) (qmul a (qmul a HA1))))
          (qmul (qmul a a) (qmul I3 (qadd (qmul HA H1) HA1))) := by rat_ring
      generalize qmul HA (qmul (qmul a a) H1) = P1 at *
      generalize qmul a (qmul a HA1) = P2 at *
      generalize qmul (qadd (corner (tm (qadd A qone)) (tm A) (m + 2)) (corner (tm (qadd A qone)) (tm A) (m + 2))) HA = P3 at *
      generalize qmul (qmul qone (qadd (corner (tm A) (tm A) (m + 2)) (corner (tm A) (tm A) (m + 2)))) HA1 = P4 at *
      have v1 : qle (qadd (qadd T1 T2) (qadd T3 T4)) (qadd (qadd P1 P2) (qadd P3 P4)) := by rat_linarith
      have v2 := scale_l v1 ic3
      have v3 : qle (qadd P3 P4) (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qadd HA1 HA1))) := by
        generalize qmul (qadd (qeps (k + Bc)) (qeps (k + Bc))) HA = Q1 at *
        generalize qmul (qmul qone (qadd (qeps (k + Bc)) (qeps (k + Bc)))) HA1 = Q2 at *
        rat_linarith
      have v4 := scale_l v3 ic3
      have id1 : qEq (qmul I3 (qadd (qadd P1 P2) (qadd P3 P4))) (qadd (qmul I3 (qadd P1 P2)) (qmul I3 (qadd P3 P4))) := by rat_ring
      have id3 : qEq (qmul I3 (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qadd HA1 HA1))))
          (qmul (qeps (k + Bc)) (qmul I3 (qadd (qadd HA HA) (qadd HA1 HA1)))) := by rat_ring
      generalize qmul I3 (qadd (qadd T1 T2) (qadd T3 T4)) = IT at *
      generalize qmul I3 (qadd (qadd P1 P2) (qadd P3 P4)) = IP at *
      generalize qmul I3 (qadd P1 P2) = IP12 at *
      generalize qmul I3 (qadd P3 P4) = IP34 at *
      generalize qmul (qmul a a) (qmul I3 (qadd (qmul HA H1) HA1)) = AH at *
      generalize qmul I3 (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qadd HA1 HA1))) = Z1 at *
      generalize qmul (qeps (k + Bc)) (qmul I3 (qadd (qadd HA HA) (qadd HA1 HA1))) = Z2 at *
      generalize qmul (qeps (k + Bc)) (qofInt (pow2 Bc)) = Z3 at *
      generalize qmul (qofInt (pow2 Bc)) (qeps (k + Bc)) = Z4 at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- `cos` over the `tan` window, for every reading in `[lu, hu]`. -/
theorem TanVal.cos_all {lu hu Tl Th : QExpr} (t : TanVal lu hu Tl Th) :
    ∃ c0 c1, qlt qzero c0 ∧ ∀ y : Nat → QExpr, Ev y lu hu → Ev (fun n => Cn (y n) n) c0 c1 := by
  obtain ⟨q0, q1, c0, c1, r1, r2, h0, h1, hq, cL, cH, cp, _⟩ := t
  exact ⟨c0, c1, cp, fun y hy => Ev_cos (Ev_widen hy h0 h1) hq cH cL⟩

/-- THE CHORD OF `tan` lies in the kernel's `1 + V²` (`V` its `tan` reading, `V²` at the corners). -/
theorem chord_tan {a b : Nat → QExpr} {lu hu Tl Th v1 v2 : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu)
    (t : TanVal lu hu Tl Th) (cv : Corners v1 v2 Tl Th Tl Th) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∃ χ, qle (qsub (qadd qone v1) (qeps k)) χ ∧ qle χ (qadd (qadd qone v2) (qeps k)) ∧
      Ab (qsub (qsub (qmul (Sn (b n) n) (qinv' (Cn (b n) n))) (qmul (Sn (a n) n) (qinv' (Cn (a n) n))))
        (qmul (qsub (b n) (a n)) χ)) (qeps k) := by
  obtain ⟨c0, c1, c0p, hC⟩ := TanVal.cos_all t
  obtain ⟨B, hB⟩ := pos_floor c0p
  have one : Ev (fun _ => qone) qone qone := Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
  exact chord_gen_P (fun x n => qmul (Sn x n) (qinv' (Cn x n)))
    (fun x n => qadd qone (qmul (qmul (Sn x n) (qinv' (Cn x n))) (qmul (Sn x n) (qinv' (Cn x n)))))
    (fun x n => qle (qeps (B + 1)) (Cn x n))
    (fun _ _ n e => qmul_respects (Sn_respects e n) (qinv'_respects (Cn_respects e n)))
    (fun _ _ n e h => qle_trans h (qle_of_qEq (Cn_respects e n)))
    (fun hA => tan_step_unif hA (qeps_pos (B + 1))) ha hb
    (fun y hy => by
      obtain ⟨N, hN⟩ := hC y hy (B + 1)
      exact ⟨N, fun n hn => by
        obtain ⟨g, _⟩ := hN n hn; have e := qeps_succ_add B; unfold qsub at g; rat_linarith⟩)
    (fun y hy => by
      have T := Ev_tan hy t
      exact Ev_add one (Ev_mul T T cv))

/-- THE KERNEL'S `(tan u)' = (1 + V²)·Du` IS SOUND for slopes. -/
theorem Ev_tan_slope {a b : Nat → QExpr} {lu hu Tl Th v1 v2 t1 t2 m M : QExpr} (ha : Ev a lu hu) (hb : Ev b lu hu)
    (t : TanVal lu hu Tl Th) (cv : Corners v1 v2 Tl Th Tl Th)
    (hΔ : Ev (fun n => qsub (b n) (a n)) t1 t2) (hc : Corners m M (qadd qone v1) (qadd qone v2) t1 t2) :
    Ev (fun n => qsub (qmul (Sn (b n) n) (qinv' (Cn (b n) n))) (qmul (Sn (a n) n) (qinv' (Cn (a n) n)))) m M :=
  Ev_chord_mul (chord_tan ha hb t cv) hΔ hc

end ZTrig

#print axioms ZTrig.chord_gen_P
#print axioms ZTrig.inv_bound
#print axioms ZTrig.tan_id
#print axioms ZTrig.tan_step
#print axioms ZTrig.tan_step_unif
#print axioms ZTrig.TanVal.cos_all
#print axioms ZTrig.chord_tan
#print axioms ZTrig.Ev_tan_slope
