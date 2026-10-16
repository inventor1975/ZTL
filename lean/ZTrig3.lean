import ZTrig2

/-!
# ZTrig3 — signs and monotonicity of `cos`, `sin` near `0`, at every index. Zero axioms.

Stage 3 of the full sine. Everything here holds at a FIXED index `N` (past a small one), with the corner of `exp`'s
series as the only error — so the limits come later and cheaply:

  * `sin_lower` — `3·5·S_N(x) ≥ x` on `[0, 2]` (from `x − x³/6` and the tail `x⁵/60`; equality at `x = 2`);
  * `cos_two` — `5·3·3·C_N(2) ≤ −7`; `cos_one` — `C_N(1) > 0`;
  * `sum_to_product` — `C_N(m+d) − C_N(m−d) = −2·S_N(m)·S_N(d)` and `S_N(m+d) − S_N(m−d) = 2·C_N(m)·S_N(d)`, up to
    four corners (the addition formulas at `±d`, parity exact).
-/

namespace ZTrig


open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn

/-! ## The first terms -/

theorem qnat_val : qEq (qnat 1) qone ∧ qEq (qnat 2) (qadd qone qone) ∧ qEq (qnat 3) (qadd (qadd qone qone) qone) ∧
    qEq (qnat 4) (qadd (qadd (qadd qone qone) qone) qone) ∧ qEq (qnat 5) (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) ∧
    qEq (qnat 6) (qadd (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) qone) := by
  have h0 := qnat_zero; have h1 := qnat_succ 0; have h2 := qnat_succ 1; have h3 := qnat_succ 2
  have h4 := qnat_succ 3; have h5 := qnat_succ 4; have h6 := qnat_succ 5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The relations of the first six terms: `cr_0 = 1`, `ci_0 = 0`, `(m+1)·cr_{m+1} = −x·ci_m`, `(m+1)·ci_{m+1} = x·cr_m`. -/
theorem first_terms (x : QExpr) :
    qEq (cr x 0) qone ∧ qEq (ci x 0) qzero ∧
    qEq (qmul (qnat 1) (cr x 1)) (qmul (qneg x) (ci x 0)) ∧ qEq (qmul (qnat 1) (ci x 1)) (qmul x (cr x 0)) ∧
    qEq (qmul (qnat 2) (cr x 2)) (qmul (qneg x) (ci x 1)) ∧ qEq (qmul (qnat 2) (ci x 2)) (qmul x (cr x 1)) ∧
    qEq (qmul (qnat 3) (cr x 3)) (qmul (qneg x) (ci x 2)) ∧ qEq (qmul (qnat 3) (ci x 3)) (qmul x (cr x 2)) ∧
    qEq (qmul (qnat 4) (cr x 4)) (qmul (qneg x) (ci x 3)) ∧ qEq (qmul (qnat 4) (ci x 4)) (qmul x (cr x 3)) ∧
    qEq (qmul (qnat 5) (cr x 5)) (qmul (qneg x) (ci x 4)) := by
  refine ⟨qEq_refl _, qEq_refl _, qEq_symm (cr_D x 0), qEq_symm (ci_D x 0), qEq_symm (cr_D x 1), qEq_symm (ci_D x 1),
    qEq_symm (cr_D x 2), qEq_symm (ci_D x 2), qEq_symm (cr_D x 3), qEq_symm (ci_D x 3), qEq_symm (cr_D x 4)⟩

/-- `S_5(x) = x + ci_3` with `6·ci_3 = −x³`; `C_6(x) = 1 + cr_2 + cr_4` with `2·cr_2 = −x²`, `24·cr_4 = x⁴`. -/
theorem low_sums (x : QExpr) :
    qEq (Sn x 5) (qadd x (ci x 3)) ∧ qEq (qmul (qnat 6) (ci x 3)) (qneg (qmul x (qmul x x))) ∧
    qEq (Cn x 6) (qadd (qadd qone (cr x 2)) (cr x 4)) ∧ qEq (qmul (qnat 2) (cr x 2)) (qneg (qmul x x)) ∧
    qEq (qmul (qnat 6) (qmul (qnat 4) (cr x 4))) (qmul x (qmul x (qmul x x))) := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := qnat_val
  obtain ⟨c0, s0, c1, s1, c2, s2, c3, s3, c4, s4, c5⟩ := first_terms x
  -- the vanishing terms
  have z1 : qEq (cr x 1) qzero := by
    have e := qmul_respects (qEq_refl (qneg x)) s0
    have := qmul_respects n1 (qEq_refl (cr x 1))
    generalize cr x 1 = u at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have v1 : qEq (ci x 1) x := by
    have e := qmul_respects (qEq_refl x) c0
    have := qmul_respects n1 (qEq_refl (ci x 1))
    generalize ci x 1 = u at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have z2 : qEq (ci x 2) qzero := by
    have e := qmul_respects (qEq_refl x) z1
    have := qmul_respects n2 (qEq_refl (ci x 2))
    generalize ci x 2 = u at *; generalize cr x 1 = w at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have z3 : qEq (cr x 3) qzero := by
    have e := qmul_respects (qEq_refl (qneg x)) z2
    have := qmul_respects n3 (qEq_refl (cr x 3))
    generalize cr x 3 = u at *; generalize ci x 2 = w at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have z4 : qEq (ci x 4) qzero := by
    have e := qmul_respects (qEq_refl x) z3
    have := qmul_respects n4 (qEq_refl (ci x 4))
    generalize ci x 4 = u at *; generalize cr x 3 = w at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have z5 : qEq (cr x 5) qzero := by
    have e := qmul_respects (qEq_refl (qneg x)) z4
    have := qmul_respects n5 (qEq_refl (cr x 5))
    generalize cr x 5 = u at *; generalize ci x 4 = w at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  -- 2·cr_2 = −x²
  have w2 : qEq (qmul (qnat 2) (cr x 2)) (qneg (qmul x x)) := by
    have e := qmul_respects (qEq_refl (qneg x)) v1
    exact qEq_trans c2 (qEq_trans e (by rat_ring))
  -- 6·ci_3 = 2·x·cr_2 = −x³
  have w3 : qEq (qmul (qnat 6) (ci x 3)) (qneg (qmul x (qmul x x))) := by
    have e1 := qmul_respects n3 (qEq_refl (ci x 3))
    have e2 := qmul_respects n6 (qEq_refl (ci x 3))
    have e3 := qmul_respects n2 (qEq_refl (cr x 2))
    have e4 := qmul_respects (qEq_refl x) w2
    have e5 := qmul_respects (qEq_refl x) e3
    generalize ci x 3 = u at *; generalize cr x 2 = w at *
    generalize qnat 2 = t2 at *; generalize qnat 3 = t3 at *; generalize qnat 6 = t6 at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  -- 24·cr_4 = x⁴
  have w4 : qEq (qmul (qnat 6) (qmul (qnat 4) (cr x 4))) (qmul x (qmul x (qmul x x))) := by
    have e1 := qmul_respects (qEq_refl (qnat 6)) c4
    have e2 := qmul_respects (qEq_refl (qneg x)) w3
    have e3 : qEq (qmul (qnat 6) (qmul (qneg x) (ci x 3))) (qmul (qneg x) (qmul (qnat 6) (ci x 3))) := by rat_ring
    exact qEq_trans e1 (qEq_trans e3 (qEq_trans e2 (by rat_ring)))
  refine ⟨?_, w3, ?_, w2, w4⟩
  · show qEq (qadd (qadd (qadd (qadd (qadd qzero (ci x 0)) (ci x 1)) (ci x 2)) (ci x 3)) (ci x 4)) (qadd x (ci x 3))
    generalize ci x 0 = a at *; generalize ci x 1 = b at *; generalize ci x 2 = c at *
    generalize ci x 3 = d at *; generalize ci x 4 = f at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · show qEq (qadd (qadd (qadd (qadd (qadd (qadd qzero (cr x 0)) (cr x 1)) (cr x 2)) (cr x 3)) (cr x 4)) (cr x 5))
      (qadd (qadd qone (cr x 2)) (cr x 4))
    generalize cr x 0 = a at *; generalize cr x 1 = b at *; generalize cr x 2 = c at *
    generalize cr x 3 = d at *; generalize cr x 4 = f at *; generalize cr x 5 = g at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## Bounds at a fixed index -/

/-! Numerals: `qnat k` as an explicit sum of ones, so that linear arithmetic sees it inside products. -/

theorem nlit1 : qEq (qnat 1) qone := by
  have := qnat_zero; have := qnat_succ 0
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem nlit2 : qEq (qnat 2) (qadd qone qone) := by
  have := qnat_zero; have := qnat_succ 0; have := qnat_succ 1
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem nlit3 : qEq (qnat 3) (qadd (qadd qone qone) qone) := by
  have := qnat_zero; have := qnat_succ 0; have := qnat_succ 1; have := qnat_succ 2
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem nlit4 : qEq (qnat 4) (qadd (qadd (qadd qone qone) qone) qone) := by
  have := qnat_zero; have := qnat_succ 0; have := qnat_succ 1; have := qnat_succ 2; have := qnat_succ 3
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem nlit5 : qEq (qnat 5) (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) := by
  have := qnat_zero; have := qnat_succ 0; have := qnat_succ 1; have := qnat_succ 2; have := qnat_succ 3; have := qnat_succ 4
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem nlit6 : qEq (qnat 6) (qadd (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) qone) := by
  have := qnat_zero; have := qnat_succ 0; have := qnat_succ 1; have := qnat_succ 2; have := qnat_succ 3; have := qnat_succ 4; have := qnat_succ 5
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem nlit9 : qEq (qnat 9) (qadd (qadd (qadd (qadd (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) qone) qone) qone) qone) := by
  have := qnat_zero; have := qnat_succ 0; have := qnat_succ 1; have := qnat_succ 2; have := qnat_succ 3; have := qnat_succ 4; have := qnat_succ 5; have := qnat_succ 6; have := qnat_succ 7; have := qnat_succ 8
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem nlit7 : qEq (qnat 7) (qadd (qadd (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) qone) qone) := by
  have := qnat_zero; have := qnat_succ 0; have := qnat_succ 1; have := qnat_succ 2; have := qnat_succ 3; have := qnat_succ 4; have := qnat_succ 5; have := qnat_succ 6
  exact qle_antisymm (by rat_linarith) (by rat_linarith)


/-- One step of the chain `(k+1)·t_{k+1} = t_k·x ≤ 2·t_k`. -/
theorem step_le {t t' x c : QExpr} (e : qEq (qmul c t') (qmul t x)) (h2 : qle x (qadd qone qone)) (ht : qle qzero t) :
    qle (qmul c t') (qadd t t) := by
  have w := scale_l h2 ht
  generalize qmul c t' = u at *; rat_linarith

set_option maxRecDepth 4000 in
/-- The last step of `sin_lower`, as linear arithmetic with small coefficients (VR's numerals are unary). -/
theorem sin_lower_step {x SN c3 a5 : QExpr} (A : qle (qsub (qadd x c3) (qadd a5 a5)) SN)
    (B : qle (qneg (qadd x x)) (qmul (qadd (qadd qone qone) qone) c3)) (C : qle (qmul (qadd (qadd qone qone) qone) (qmul (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) a5)) (qadd x x)) :
    qle x (qmul (qadd (qadd qone qone) qone) (qmul (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) SN)) := by
  unfold qsub at *; rat_linarith

theorem halve_c3 {x c3 : QExpr} (C3 : qle (qneg (qmul (qadd qone qone) (qadd x x))) (qmul (qadd (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) qone) c3)) :
    qle (qneg (qadd x x)) (qmul (qadd (qadd qone qone) qone) c3) := by
  rat_linarith

/-- `sin x ≥ x/15` (`15 = 3·5`) on `[0, 2]`, at every index past `5`. -/
theorem sin_lower {x : QExpr} (h0 : qle qzero x) (h2 : qle x (qadd qone qone)) {N : Nat} (hN : 5 ≤ N) :
    qle x (qmul (qnat 3) (qmul (qnat 5) (Sn x N))) := by
  have hx : Ab x x := ⟨by rat_linarith, qle_refl x⟩
  have g : Good x 5 := by
    show qle (qadd x x) (qnat (5 + 1))
    have := nlit6; rat_linarith
  obtain ⟨_, ⟨t1, t2⟩⟩ := CS_tail hx g N hN
  obtain ⟨l5, l3, _, _, _⟩ := low_sums x
  -- the chain: t1 = x, 2t2 ≤ 2t1, 3t3 ≤ 2t2, 4t4 ≤ 2t3, 5t5 ≤ 2t4
  have e1 : qEq (tm x 1) x := by
    have u := tm_succ x 0
    have v := qmul_respects nlit1 (qEq_refl (tm x 1))
    have w : qEq (qmul (tm x 0) x) x := by show qEq (qmul qone x) x; rat_ring
    generalize tm x 1 = a at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have s2 := step_le (qEq_trans (qmul_respects (qEq_symm nlit2) (qEq_refl _)) (tm_succ x 1)) h2 (tm_nonneg h0 1)
  have s3 := step_le (qEq_trans (qmul_respects (qEq_symm nlit3) (qEq_refl _)) (tm_succ x 2)) h2 (tm_nonneg h0 2)
  have s4 := step_le (qEq_trans (qmul_respects (qEq_symm nlit4) (qEq_refl _)) (tm_succ x 3)) h2 (tm_nonneg h0 3)
  have s5 := step_le (qEq_trans (qmul_respects (qEq_symm nlit5) (qEq_refl _)) (tm_succ x 4)) h2 (tm_nonneg h0 4)
  have T5 : qle (qmul (qnat 3) (qmul (qnat 5) (tm x 5))) (qadd x x) := by
    refine qle_respects (qmul_respects (qEq_symm nlit3) (qmul_respects (qEq_symm nlit5) (qEq_refl _))) (qEq_refl _) ?_
    generalize tm x 1 = a1 at *; generalize tm x 2 = a2 at *; generalize tm x 3 = a3 at *
    generalize tm x 4 = a4 at *; generalize tm x 5 = a5 at *
    clear l5 l3 t1 t2 g hx
    rat_linarith
  -- 6·ci_3 = −x³ ≥ −4x
  have C3 : qle (qneg (qmul (qadd qone qone) (qadd x x))) (qmul (qnat 6) (ci x 3)) := by
    have q1 := scale_l h2 h0
    have q3 := scale_l (show qle (qmul x x) (qmul x (qadd qone qone)) from q1) h0
    generalize qmul (qnat 6) (ci x 3) = c at *
    clear l5 t1 t2 g hx T5 s2 s3 s4 s5 e1
    rat_linarith
  refine qle_respects (qEq_refl x) (qmul_respects (qEq_symm nlit3) (qmul_respects (qEq_symm nlit5) (qEq_refl _))) ?_
  have C3' := qle_respects (qneg_respects (qEq_refl _)) (qmul_respects nlit6 (qEq_refl _)) C3
  have T5' := qle_respects (qmul_respects nlit3 (qmul_respects nlit5 (qEq_refl _))) (qEq_refl _) T5
  have A : qle (qsub (qadd x (ci x 3)) (qadd (tm x 5) (tm x 5))) (Sn x N) := by
    generalize Sn x N = SN at *; generalize Sn x 5 = S5 at *; generalize ci x 3 = c3 at *; generalize tm x 5 = a5 at *
    clear l3 C3 T5 C3' T5' s2 s3 s4 s5 e1 g hx t2
    unfold qsub at *; rat_linarith
  exact sin_lower_step A (halve_c3 C3') T5'

/-- `cos 2 ≤ −1/9`, at every index past `6`. -/
theorem cos_two {N : Nat} (hN : 6 ≤ N) : qle (qmul (qnat 9) (Cn (qadd qone qone) N)) (qneg qone) := by
  have hx : Ab (qadd qone qone) (qadd qone qone) := ⟨by have := qle_of_qlt qone_pos; rat_linarith, qle_refl _⟩
  have g : Good (qadd qone qone) 6 := by
    show qle (qadd (qadd qone qone) (qadd qone qone)) (qnat (6 + 1))
    have := nlit7; rat_linarith
  obtain ⟨⟨t1, t2⟩, _⟩ := CS_tail hx g N hN
  obtain ⟨_, _, l6, l2, l4⟩ := low_sums (qadd qone qone)
  -- the even terms: c2 = −2, 3·c4 = 2
  have c2 : qEq (cr (qadd qone qone) 2) (qneg (qadd qone qone)) := by
    have e := qEq_trans (qmul_respects (qEq_symm nlit2) (qEq_refl _)) l2
    generalize cr (qadd qone qone) 2 = u at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have c4 : qEq (qmul (qadd (qadd qone qone) qone) (cr (qadd qone qone) 4)) (qadd qone qone) := by
    have e := qEq_trans (qmul_respects (qEq_symm nlit6) (qmul_respects (qEq_symm nlit4) (qEq_refl _))) l4
    generalize cr (qadd qone qone) 4 = u at *
    set_option maxRecDepth 4000 in exact qle_antisymm (by rat_linarith) (by rat_linarith)
  -- the tail: tm6 ≤ 1/9
  have e1 : qEq (tm (qadd qone qone) 1) (qadd qone qone) := by
    have u := tm_succ (qadd qone qone) 0
    have v := qmul_respects nlit1 (qEq_refl (tm (qadd qone qone) 1))
    have w : qEq (qmul (tm (qadd qone qone) 0) (qadd qone qone)) (qadd qone qone) := by
      show qEq (qmul qone (qadd qone qone)) (qadd qone qone); rat_ring
    generalize tm (qadd qone qone) 1 = a at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have e2 := qEq_trans (qmul_respects (qEq_symm nlit2) (qEq_refl _)) (tm_succ (qadd qone qone) 1)
  have e3 := qEq_trans (qmul_respects (qEq_symm nlit3) (qEq_refl _)) (tm_succ (qadd qone qone) 2)
  have e4 := qEq_trans (qmul_respects (qEq_symm nlit4) (qEq_refl _)) (tm_succ (qadd qone qone) 3)
  have e5 := qEq_trans (qmul_respects (qEq_symm nlit5) (qEq_refl _)) (tm_succ (qadd qone qone) 4)
  have e6 := qEq_trans (qmul_respects (qEq_symm nlit6) (qEq_refl _)) (tm_succ (qadd qone qone) 5)
  generalize tm (qadd qone qone) 1 = a1 at *; generalize tm (qadd qone qone) 2 = a2 at *
  generalize tm (qadd qone qone) 3 = a3 at *; generalize tm (qadd qone qone) 4 = a4 at *
  generalize tm (qadd qone qone) 5 = a5 at *; generalize tm (qadd qone qone) 6 = a6 at *
  have b2 : qEq a2 (qadd qone qone) := by clear t1 t2 l6 l2 l4 c4 e3 e4 e5 e6; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have b3 : qEq (qmul (qadd (qadd qone qone) qone) a3) (qadd (qadd qone qone) (qadd qone qone)) := by
    clear t1 t2 l6 l2 l4 c4 e2 e4 e5 e6; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have b4 : qle (qmul (qadd (qadd qone qone) qone) a4) (qadd qone qone) := by clear t1 t2 l6 l2 l4 c4 e2 e5 e6; rat_linarith
  have b5 : qle (qmul (qadd (qadd qone qone) qone) a5) qone := by clear t1 t2 l6 l2 l4 c4 e2 e3 e6 b3; rat_linarith
  have b6 : qle (qmul (qadd (qadd (qadd (qadd (qadd (qadd (qadd (qadd qone qone) qone) qone) qone) qone) qone) qone) qone) a6) qone := by clear t1 t2 l6 l2 l4 c4 e2 e3 e4 b3 b4; rat_linarith
  refine qle_respects (qmul_respects (qEq_symm nlit9) (qEq_refl _)) (qEq_refl _) ?_
  generalize Cn (qadd qone qone) N = CN at *; generalize Cn (qadd qone qone) 6 = C6 at *
  generalize cr (qadd qone qone) 2 = r2 at *; generalize cr (qadd qone qone) 4 = r4 at *
  clear l2 l4 e2 e3 e4 e5 e6 b2 b3 b4 b5 t1 g hx
  unfold qsub at *
  set_option maxRecDepth 4000 in rat_linarith

/-- `cos 1 ≥ 1/3`, at every index past `6`. -/
theorem cos_one {N : Nat} (hN : 6 ≤ N) : qle qone (qmul (qnat 3) (Cn qone N)) := by
  have hx : Ab qone qone := ⟨by have := qle_of_qlt qone_pos; rat_linarith, qle_refl _⟩
  have g : Good qone 6 := by
    show qle (qadd qone qone) (qnat (6 + 1))
    have := nlit7; rat_linarith
  obtain ⟨⟨t1, t2⟩, _⟩ := CS_tail hx g N hN
  obtain ⟨_, _, l6, l2, l4⟩ := low_sums qone
  have c2 := qEq_trans (qmul_respects (qEq_symm nlit2) (qEq_refl _)) l2
  have c4 := qEq_trans (qmul_respects (qEq_symm nlit6) (qmul_respects (qEq_symm nlit4) (qEq_refl _))) l4
  have e1 : qEq (tm qone 1) qone := by
    have u := tm_succ qone 0
    have v := qmul_respects nlit1 (qEq_refl (tm qone 1))
    have w : qEq (qmul (tm qone 0) qone) qone := by show qEq (qmul qone qone) qone; rat_ring
    generalize tm qone 1 = a at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have e2 := qEq_trans (qmul_respects (qEq_symm nlit2) (qEq_refl _)) (tm_succ qone 1)
  have e3 := qEq_trans (qmul_respects (qEq_symm nlit3) (qEq_refl _)) (tm_succ qone 2)
  have e4 := qEq_trans (qmul_respects (qEq_symm nlit4) (qEq_refl _)) (tm_succ qone 3)
  have e5 := qEq_trans (qmul_respects (qEq_symm nlit5) (qEq_refl _)) (tm_succ qone 4)
  have e6 := qEq_trans (qmul_respects (qEq_symm nlit6) (qEq_refl _)) (tm_succ qone 5)
  have v4 := tm_nonneg (qle_of_qlt qone_pos) 4; have v5 := tm_nonneg (qle_of_qlt qone_pos) 5
  have v6 := tm_nonneg (qle_of_qlt qone_pos) 6
  generalize tm qone 1 = a1 at *; generalize tm qone 2 = a2 at *; generalize tm qone 3 = a3 at *
  generalize tm qone 4 = a4 at *; generalize tm qone 5 = a5 at *; generalize tm qone 6 = a6 at *
  -- 2a2 = 1, 3a3 = a2, 4a4 = a3: 24·a4 = 1; a5 ≤ a4, a6 ≤ a5
  have b4 : qEq (qmul (qadd (qadd qone qone) qone) (qmul (qadd qone qone) (qmul (qadd qone qone) (qmul (qadd qone qone) a4)))) qone := by
    clear t1 t2 l6 l2 l4 c2 c4 e5 e6 v4 v5 v6
    set_option maxRecDepth 4000 in exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have b6 : qle a6 a4 := by clear t1 t2 l6 l2 l4 c2 c4 e1 e2 e3 e4 b4; rat_linarith
  have f12 : qle (qmul (qadd (qadd qone qone) qone) (qmul (qadd qone qone) (qmul (qadd qone qone) a4))) qone := by
    clear t1 t2 l6 l2 l4 c2 c4 e1 e2 e3 e4 e5 e6 v5 v6 b6; rat_linarith
  refine qle_respects (qEq_refl qone) (qmul_respects (qEq_symm nlit3) (qEq_refl _)) ?_
  generalize Cn qone N = CN at *; generalize Cn qone 6 = C6 at *
  generalize cr qone 2 = r2 at *; generalize cr qone 4 = r4 at *
  have r4p : qle qzero r4 := by clear t1 t2 l6 l2 c2 e1 e2 e3 e4 e5 e6 v4 v5 v6 b4 b6 f12; rat_linarith
  clear l2 l4 c4 b4 e1 e2 e3 e4 e5 e6 v4 v5 v6 t2 g hx
  unfold qsub at *
  set_option maxRecDepth 4000 in rat_linarith

/-! ## Sum to product -/

/-- `C(m+d) − C(m−d) = −2·S(m)·S(d)` and `S(m+d) − S(m−d) = 2·C(m)·S(d)`, at every index, up to four corners. -/
theorem sum_to_product {m d a b : QExpr} (hm : Ab m a) (hd : Ab d b) (N : Nat) :
    Ab (qadd (qsub (Cn (qadd m d) N) (Cn (qsub m d) N)) (qmul (qadd qone qone) (qmul (Sn m N) (Sn d N))))
       (qadd (qadd (corner (tm a) (tm b) N) (corner (tm a) (tm b) N)) (qadd (corner (tm a) (tm b) N) (corner (tm a) (tm b) N))) ∧
    Ab (qsub (qsub (Sn (qadd m d) N) (Sn (qsub m d) N)) (qmul (qadd qone qone) (qmul (Cn m N) (Sn d N))))
       (qadd (qadd (corner (tm a) (tm b) N) (corner (tm a) (tm b) N)) (qadd (corner (tm a) (tm b) N) (corner (tm a) (tm b) N))) := by
  have hnd : Ab (qneg d) b := by obtain ⟨h1, h2⟩ := hd; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ := add_bounds hm hd N
  obtain ⟨⟨r1, r2⟩, ⟨s1, s2⟩⟩ := add_bounds hm hnd N
  have e : qEq (qsub m d) (qadd m (qneg d)) := qEq_refl _
  have ec := Cn_neg d N
  have es := Sn_neg d N
  have u1 := qmul_respects (qEq_refl (Cn m N)) ec
  have u2 := qmul_respects (qEq_refl (Sn m N)) es
  have u3 := qmul_respects (qEq_refl (Cn m N)) es
  have u4 := qmul_respects (qEq_refl (Sn m N)) ec
  show Ab (qadd (qsub (Cn (qadd m d) N) (Cn (qadd m (qneg d)) N)) (qmul (qadd qone qone) (qmul (Sn m N) (Sn d N)))) _ ∧
    Ab (qsub (qsub (Sn (qadd m d) N) (Sn (qadd m (qneg d)) N)) (qmul (qadd qone qone) (qmul (Cn m N) (Sn d N)))) _
  generalize corner (tm a) (tm b) N = K at *
  generalize Cn (qadd m d) N = A1 at *; generalize Cn (qadd m (qneg d)) N = A2 at *
  generalize Sn (qadd m d) N = B1 at *; generalize Sn (qadd m (qneg d)) N = B2 at *
  generalize Cn (qneg d) N = Cnd at *; generalize Sn (qneg d) N = Snd at *
  generalize Cn m N = Cm at *; generalize Sn m N = Sm at *; generalize Cn d N = Cd at *; generalize Sn d N = Sd at *
  unfold qsub at *
  exact ⟨⟨by rat_linarith, by rat_linarith⟩, ⟨by rat_linarith, by rat_linarith⟩⟩

end ZTrig

#print axioms ZTrig.first_terms
#print axioms ZTrig.low_sums
#print axioms ZTrig.sin_lower
#print axioms ZTrig.cos_two
#print axioms ZTrig.cos_one
#print axioms ZTrig.sum_to_product
