import ZTrig13

/-!
# ZTrig14 — the kernel's `tan` over an interval is sound (`zfunc.iv_tan`). Zero axioms.

Stage 14 of the full sine. `tan = S·(1/C)`; the kernel reads it on `|x| ≤ 1.5`, increasing, by the ends' brackets
(`tan_pt`: the ratios of `sin`/`cos` brackets, the ends rounded outward to `q0 ≤ lu`, `hu ≤ q1`). Here:

  * the lower end: `S(x)·C(q0) − C(x)·S(q0) ≈ sin(x − q0) ≥ 0` (`x − q0 ∈ [0, q1 − q0]`, `sin ≥ 0` there by the
    kernel's own `sin` rule, `ZTrig11`), and `S(q0) ≥ Tl·C(q0)` (the end's certificates), so
    `Q = (S − Tl·C)·C(q0) ≥ −ε`; then `tan − Tl = Q·(1/C)·(1/C(q0))` — a product of things eventually `≥ 0`;
  * the upper end alike with `q1`; `cos` on the window bounded below by `c0 > 0` (`ZTrig10`).
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

theorem ev_congr_ev {x y : Nat → QExpr} {l h : QExpr} (N0 : Nat) (e : ∀ n, N0 ≤ n → qEq (x n) (y n))
    (hx : Ev x l h) : Ev y l h := fun k => by
  obtain ⟨N, hN⟩ := hx k
  refine ⟨N + N0, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n (le_l' hn)
  have := e n (le_r' hn)
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- A box with both lower ends `0` and `r ≥ 0`: the corners lie in `[0, K·r1 + K·r2]`. -/
theorem corners_nn {K r1 r2 : QExpr} (hK : qle qzero K) (hr : qle qzero r1) (hr2 : qle qzero r2) :
    Corners qzero (qadd (qmul K r1) (qmul K r2)) qzero K r1 r2 := by
  have z1 : qEq (qmul qzero r1) qzero := by rat_ring
  have z2 : qEq (qmul qzero r2) qzero := by rat_ring
  have p1 := qmul_nonneg hK hr; have p2 := qmul_nonneg hK hr2
  unfold Corners
  generalize qmul qzero r1 = A at *; generalize qmul qzero r2 = B at *
  generalize qmul K r1 = C at *; generalize qmul K r2 = D at *
  exact ⟨⟨by rat_linarith, by rat_linarith, by rat_linarith, by rat_linarith⟩,
         ⟨by rat_linarith, by rat_linarith, by rat_linarith, by rat_linarith⟩⟩


/-- `Z = Q·I·J`, `Q` eventually in `[0, K]`, `I`, `J` eventually in non-negative readings: `Z ≥ −ε_k` eventually. -/
theorem nonneg_prod {Z Q I J : Nat → QExpr} {K r1 r2 p1 p2 : QExpr} (hQ : Ev Q qzero K) (hK : qle qzero K)
    (hI : Ev I r1 r2) (r0 : qle qzero r1) (r2n : qle qzero r2) (hJ : Ev J p1 p2) (p0 : qle qzero p1) (q2n : qle qzero p2)
    (N0 : Nat) (hz : ∀ n, N0 ≤ n → qEq (Z n) (qmul (qmul (Q n) (I n)) (J n))) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (qneg (qeps k)) (Z n) := by
  have H1 : qle qzero (qadd (qmul K r1) (qmul K r2)) := by
    have := qmul_nonneg hK r0; have := qmul_nonneg hK r2n; rat_linarith
  have P1 := Ev_mul hQ hI (corners_nn hK r0 r2n)
  have P2 := Ev_mul P1 hJ (corners_nn H1 p0 q2n)
  have P3 := ev_congr_ev N0 (fun n hn => qEq_symm (hz n hn)) P2
  intro k
  obtain ⟨N, hN⟩ := P3 k
  exact ⟨N, fun n hn => by obtain ⟨a, _⟩ := hN n hn; unfold qsub at a; rat_linarith⟩

/-- A reading eventually above a positive bound is eventually positive, with a margin `ε_{B+1}`. -/
theorem ev_pos {y : Nat → QExpr} {l h : QExpr} (hy : Ev y l h) (hl : qlt qzero l) :
    ∃ B N, ∀ n, N ≤ n → qle (qeps (B + 1)) (y n) ∧ qlt qzero (y n) := by
  obtain ⟨B, hB⟩ := pos_floor hl
  obtain ⟨N, hN⟩ := hy (B + 1)
  refine ⟨B, N, fun n hn => ?_⟩
  obtain ⟨a, _⟩ := hN n hn
  have e := qeps_succ_add B
  have p := qeps_pos (B + 1)
  have s : qle (qeps (B + 1)) (y n) := by unfold qsub at a; rat_linarith
  refine ⟨s, qlt_iff_le_not_le.mpr ⟨by have := qle_of_qlt p; rat_linarith, fun h' => ?_⟩⟩
  exact (qlt_iff_le_not_le.mp p).2 (qle_trans s h')

theorem recip_hi_nonneg {li hi lv hv : QExpr} (h : RecipOK li hi lv hv) (hp : qlt qzero lv) : qle qzero hi := by
  obtain ⟨hlh, ⟨_, _, b⟩ | ⟨hn, _, _⟩⟩ := h
  · cases qle_total qzero hi with
    | inl h => exact h
    | inr h =>
      have s := ZExp.scale h (qle_of_qlt hp)
      have z : qEq (qmul qzero lv) qzero := by rat_ring
      generalize qmul hi lv = P at *; generalize qmul qzero lv = Z at *
      exact absurd (show qle qone qzero by rat_linarith) (qlt_iff_le_not_le.mp qone_pos).2
  · exact absurd (qle_trans (qle_of_qlt hp) hlh) (qlt_iff_le_not_le.mp hn).2

/-- `t·c ≤ s` at both ends of `c`'s interval gives it inside. -/
theorem lin_end {t c cl ch s : QExpr} (c1 : qle cl c) (c2 : qle c ch) (a : qle (qmul t cl) s) (b : qle (qmul t ch) s) :
    qle (qmul t c) s := by
  cases qle_total qzero t with
  | inl h => have := scale_l c2 h; exact qle_trans this b
  | inr h =>
    have := scale_l c1 (show qle qzero (qneg t) by rat_linarith)
    have e1 : qEq (qmul (qneg t) cl) (qneg (qmul t cl)) := by rat_ring
    have e2 : qEq (qmul (qneg t) c) (qneg (qmul t c)) := by rat_ring
    generalize qmul (qneg t) cl = P at *; generalize qmul (qneg t) c = Q at *
    generalize qmul t cl = R at *; generalize qmul t c = T at *
    rat_linarith

/-- THE LOWER END OF `tan`: from some index on, `tan x_n ≥ Tl − ε_k`. -/
theorem tan_low {x : Nat → QExpr} {lu hu q0 d c0 c1 r1 r2 s0l s0h c0l c0h ρl ρh Tl : QExpr}
    (hx : Ev x lu hu) (h0 : qle q0 lu) (hd : qle (qsub hu q0) d) (d0 : qle qzero d)
    (hC : Ev (fun n => Cn (x n) n) c0 c1) (c0p : qlt qzero c0) (rc : RecipOK r1 r2 c0 c1) (r10 : qle qzero r1)
    (sw : SinLo qzero d qzero)
    (S0 : SinCert q0 s0l s0h) (C0 : CosCert q0 c0l c0h) (c0lp : qlt qzero c0l) (R0 : RecipOK ρl ρh c0l c0h)
    (ρ0 : qle qzero ρl) (T1 : qle (qmul Tl c0l) s0l) (T2 : qle (qmul Tl c0h) s0l) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub Tl (qeps k)) (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) := by
  have o := qle_of_qlt qone_pos
  -- the reciprocals
  have hI := Ev_recip hC rc
  have r2n := recip_hi_nonneg rc c0p
  obtain ⟨M0, hM0⟩ := cert_cos C0
  obtain ⟨M1, hM1⟩ := cert_sin S0
  have hC0 : Ev (fun n => Cn q0 n) c0l c0h := Ev_of_exact M0 hM0
  have hJ := Ev_recip hC0 R0
  have ρhn := recip_hi_nonneg R0 c0lp
  -- sin(x − q0) ≥ 0
  have hy : Ev (fun n => qsub (x n) q0) qzero d := fun k => by
    obtain ⟨N, hN⟩ := hx k
    exact ⟨N, fun n hn => by
      obtain ⟨a, b⟩ := hN n hn; show qle _ (qsub (x n) q0) ∧ qle (qsub (x n) q0) _
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩
  have hS := Ev_sin hy d0 (Or.inl (qle_refl qone)) sw
  -- bounds
  obtain ⟨A, hA, NA, hNA⟩ := ev_bound hx
  obtain ⟨MB, _, hMB0, _, mq, mt, mc1, mc2⟩ := bound4 q0 Tl c0l c0h
  have hA0 : qle qzero MB := hMB0
  obtain ⟨mq1, mq2⟩ := mq
  have aq : Ab (qneg q0) MB := by unfold qsub at mq1 mq2; exact ⟨by rat_linarith, by rat_linarith⟩
  -- Q = (S − Tl·C)·C(q0) is eventually in [0, K]
  have Kd : qle qzero (qmul (qadd (qadd qone qone) (qmul MB (qadd qone qone))) MB) :=
    qmul_nonneg (by have := qmul_nonneg hA0 two_pos; rat_linarith) hA0
  have hQ : Ev (fun n => qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n)) qzero
      (qmul (qadd (qadd qone qone) (qmul MB (qadd qone qone))) MB) := by
    refine Ev_of_sides (fun k => ?_) (fun k => ?_)
    · obtain ⟨Nc, hNc⟩ := corner_small hA hA0 (k + 2)
      obtain ⟨Ns, hNs⟩ := hS (k + 2)
      obtain ⟨Bp, Np, hNp⟩ := ev_pos hC c0p
      refine ⟨NA + (Nc + (Ns + (Np + (M0 + M1)))), fun n hn => ?_⟩
      have ax := hNA n (le_l' hn)
      obtain ⟨_, ⟨f1, f2⟩⟩ := add_bounds ax aq n
      have cs := hNc n (le_l' (le_r' hn))
      obtain ⟨s1, _⟩ := hNs n (le_l' (le_r' (le_r' hn)))
      obtain ⟨_, cp⟩ := hNp n (le_l' (le_r' (le_r' (le_r' hn))))
      obtain ⟨g1, g2⟩ := hM0 n (le_l' (le_r' (le_r' (le_r' (le_r' hn)))))
      obtain ⟨t1, _⟩ := hM1 n (le_r' (le_r' (le_r' (le_r' (le_r' hn)))))
      have sn := Sn_neg q0 n; have cn := Cn_neg q0 n
      have ys : qEq (Sn (qadd (x n) (qneg q0)) n) (Sn (qsub (x n) q0) n) := qEq_refl _
      have le1 := lin_end g1 g2 T1 T2
      have sc := scale_l (qle_trans le1 t1) (qle_of_qlt cp)
      have e1 : qEq (qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n))
          (qsub (qmul (Sn (x n) n) (Cn q0 n)) (qmul (Cn (x n) n) (qmul Tl (Cn q0 n)))) := by unfold qsub; rat_ring
      have e2 : qEq (qmul (Cn (x n) n) (Sn (qneg q0) n)) (qneg (qmul (Cn (x n) n) (Sn q0 n))) := by
        have := qmul_respects (qEq_refl (Cn (x n) n)) sn; have r : qEq (qmul (Cn (x n) n) (qneg (Sn q0 n))) (qneg (qmul (Cn (x n) n) (Sn q0 n))) := by rat_ring
        exact qEq_trans this r
      have e3 : qEq (qmul (Sn (x n) n) (Cn (qneg q0) n)) (qmul (Sn (x n) n) (Cn q0 n)) := qmul_respects (qEq_refl _) cn
      have ek := qeps_succ_add k; have ek1 := qeps_succ_add (k + 1); have ep := qeps_nonneg (k + 2)
      show qle (qsub qzero (qeps k)) (qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n))
      generalize qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n) = Q at *
      generalize Sn (qadd (x n) (qneg q0)) n = Y at *
      generalize qmul (Cn (x n) n) (Sn (qneg q0) n) = P1 at *
      generalize qmul (Sn (x n) n) (Cn (qneg q0) n) = P2 at *
      generalize qmul (Cn (x n) n) (qmul Tl (Cn q0 n)) = P3 at *
      generalize qmul (Cn (x n) n) (Sn q0 n) = P4 at *
      generalize qmul (Sn (x n) n) (Cn q0 n) = P5 at *
      generalize corner (tm A) (tm MB) n = Kc at *
      clear hNA hNc hNs hNp hM0 hM1 hI hJ hS
      unfold qsub at *; rat_linarith
    · obtain ⟨N1, h1⟩ := sin_pm1 hx 0
      obtain ⟨N2, h2⟩ := cos_pm1 hx 0
      refine ⟨N1 + (N2 + M0), fun n hn => ?_⟩
      have z := qeps_zero
      obtain ⟨u1, u2⟩ := h1 n (le_l' hn)
      obtain ⟨v1, v2⟩ := h2 n (le_l' (le_r' hn))
      obtain ⟨g1, g2⟩ := hM0 n (le_r' (le_r' hn))
      obtain ⟨w1, w2⟩ := mt; obtain ⟨x1, x2⟩ := mc1; obtain ⟨x3, x4⟩ := mc2
      unfold qsub at w1 w2 x1 x2 x3 x4
      have aS : Ab (Sn (x n) n) (qadd qone qone) := ⟨by rat_linarith, by rat_linarith⟩
      have aC : Ab (Cn (x n) n) (qadd qone qone) := ⟨by rat_linarith, by rat_linarith⟩
      have aT : Ab Tl MB := ⟨by rat_linarith, by rat_linarith⟩
      have aC0 : Ab (Cn q0 n) MB := ⟨by rat_linarith, by rat_linarith⟩
      obtain ⟨p1, p2⟩ := mul_abs aT aC
      have aD : Ab (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (qadd (qadd qone qone) (qmul MB (qadd qone qone))) := by
        obtain ⟨s1, s2⟩ := aS; unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
      obtain ⟨_, q2⟩ := mul_abs aD aC0
      have ep := qeps_nonneg k
      show qle (qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n)) _
      rat_linarith
  -- tan − Tl = Q·(1/C)·(1/C(q0))
  obtain ⟨Bp, Np, hNp⟩ := ev_pos hC c0p
  have hz : ∀ n, Np + M0 ≤ n → qEq (qsub (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) Tl)
      (qmul (qmul (qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n)) (qinv' (Cn (x n) n))) (qinv' (Cn q0 n))) := by
    intro n hn
    obtain ⟨_, cp⟩ := hNp n (le_l' hn)
    obtain ⟨g1, _⟩ := hM0 n (le_r' hn)
    have c0n : qlt qzero (Cn q0 n) := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt c0lp) g1,
      fun h' => (qlt_iff_le_not_le.mp c0lp).2 (qle_trans g1 h')⟩
    have u := qmul_inv'_cancel (ne_zero_of_lt cp)
    have v := qmul_inv'_cancel (ne_zero_of_lt c0n)
    have r : qEq (qmul (qmul (qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n)) (qinv' (Cn (x n) n))) (qinv' (Cn q0 n)))
        (qsub (qmul (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) (qmul (Cn q0 n) (qinv' (Cn q0 n))))
          (qmul (qmul Tl (qmul (Cn (x n) n) (qinv' (Cn (x n) n)))) (qmul (Cn q0 n) (qinv' (Cn q0 n))))) := by
      unfold qsub; rat_ring
    have r1 := qmul_respects (qEq_refl (qmul (Sn (x n) n) (qinv' (Cn (x n) n)))) v
    have r2 := qmul_respects (qmul_respects (qEq_refl Tl) u) v
    have o1 : qEq (qmul (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) qone) (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) := by rat_ring
    have o2 : qEq (qmul (qmul Tl qone) qone) Tl := by rat_ring
    generalize qmul (qmul (qmul (qsub (Sn (x n) n) (qmul Tl (Cn (x n) n))) (Cn q0 n)) (qinv' (Cn (x n) n))) (qinv' (Cn q0 n)) = L at *
    generalize qmul (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) (qmul (Cn q0 n) (qinv' (Cn q0 n))) = P at *
    generalize qmul (qmul Tl (qmul (Cn (x n) n) (qinv' (Cn (x n) n)))) (qmul (Cn q0 n) (qinv' (Cn q0 n))) = Q at *
    generalize qmul (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) qone = P' at *
    generalize qmul (qmul Tl qone) qone = Q' at *
    generalize qmul (Sn (x n) n) (qinv' (Cn (x n) n)) = T at *
    unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have fin := nonneg_prod hQ Kd hI r10 r2n hJ ρ0 ρhn (Np + M0) hz
  intro k
  obtain ⟨N, hN⟩ := fin k
  exact ⟨N, fun n hn => by have := hN n hn; unfold qsub at *; rat_linarith⟩

theorem sincert_neg {x lo hi : QExpr} (h : SinCert x lo hi) : SinCert (qneg x) (qneg hi) (qneg lo) := by
  obtain ⟨a, M, ⟨x1, x2⟩, g, h1, h2⟩ := h
  have e := Sn_neg x M
  refine ⟨a, M, ⟨by rat_linarith, by rat_linarith⟩, g, ?_, ?_⟩ <;>
  · generalize Sn (qneg x) M = P at *; generalize Sn x M = Q at *; unfold qsub at *; rat_linarith

theorem coscert_neg {x lo hi : QExpr} (h : CosCert x lo hi) : CosCert (qneg x) lo hi := by
  obtain ⟨a, M, ⟨x1, x2⟩, g, h1, h2⟩ := h
  have e := Cn_neg x M
  refine ⟨a, M, ⟨by rat_linarith, by rat_linarith⟩, g, ?_, ?_⟩ <;>
  · generalize Cn (qneg x) M = P at *; generalize Cn x M = Q at *; unfold qsub at *; rat_linarith

/-- THE UPPER END OF `tan`, by `tan(−x) = −tan x` and the lower end. -/
theorem tan_high {x : Nat → QExpr} {lu hu q1 d c0 c1 r1 r2 s1l s1h c1l c1h ρl ρh Th : QExpr}
    (hx : Ev x lu hu) (h1 : qle hu q1) (hd : qle (qsub q1 lu) d) (d0 : qle qzero d)
    (hC : Ev (fun n => Cn (x n) n) c0 c1) (c0p : qlt qzero c0) (rc : RecipOK r1 r2 c0 c1) (r10 : qle qzero r1)
    (sw : SinLo qzero d qzero)
    (S1 : SinCert q1 s1l s1h) (C1 : CosCert q1 c1l c1h) (c1lp : qlt qzero c1l) (R1 : RecipOK ρl ρh c1l c1h)
    (ρ0 : qle qzero ρl) (T1 : qle s1h (qmul Th c1l)) (T2 : qle s1h (qmul Th c1h)) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (qmul (Sn (x n) n) (qinv' (Cn (x n) n))) (qadd Th (qeps k)) := by
  have hx' : Ev (fun n => qneg (x n)) (qneg hu) (qneg lu) := Ev_negate hx
  have hC' : Ev (fun n => Cn (qneg (x n)) n) c0 c1 := Ev_congr (fun n => qEq_symm (Cn_neg (x n) n)) hC
  have L := tan_low (q0 := qneg q1) (Tl := qneg Th) hx' (by rat_linarith) (by unfold qsub at *; rat_linarith) d0 hC' c0p rc r10 sw
    (sincert_neg S1) (coscert_neg C1) c1lp R1 ρ0
    (by have e : qEq (qmul (qneg Th) c1l) (qneg (qmul Th c1l)) := by rat_ring
        generalize qmul (qneg Th) c1l = P at *; generalize qmul Th c1l = Q at *; rat_linarith)
    (by have e : qEq (qmul (qneg Th) c1h) (qneg (qmul Th c1h)) := by rat_ring
        generalize qmul (qneg Th) c1h = P at *; generalize qmul Th c1h = Q at *; rat_linarith)
  intro k
  obtain ⟨N, hN⟩ := L k
  refine ⟨N, fun n hn => ?_⟩
  have a := hN n hn
  have e1 := Sn_neg (x n) n
  have e2 := qinv'_respects (Cn_neg (x n) n)
  have e3 := qmul_respects e1 e2
  have e4 : qEq (qmul (qneg (Sn (x n) n)) (qinv' (Cn (x n) n))) (qneg (qmul (Sn (x n) n) (qinv' (Cn (x n) n)))) := by rat_ring
  generalize qmul (Sn (qneg (x n)) n) (qinv' (Cn (qneg (x n)) n)) = P at *
  generalize qmul (qneg (Sn (x n) n)) (qinv' (Cn (x n) n)) = P' at *
  generalize qmul (Sn (x n) n) (qinv' (Cn (x n) n)) = T at *
  unfold qsub at *; rat_linarith

/-- The kernel's `tan` reading over `[lu, hu]` (`zfunc.iv_tan`): the ends rounded outward to `q0 ≤ lu`, `hu ≤ q1`;
`cos ≥ c0 > 0` on `[q0, q1]` (its reading, and `1/cos` read); `sin ≥ 0` on `[0, q1 − q0]`; at each end the
certified `sin`, `cos` brackets with `Tl·c ≤ s` (resp. `s ≤ Th·c`) at both ends of `c`'s bracket — what
`tan_pt`'s ratios give. -/
def TanVal (lu hu Tl Th : QExpr) : Prop :=
  ∃ q0 q1 c0 c1 r1 r2, qle q0 lu ∧ qle hu q1 ∧ qle q0 q1 ∧ CosLo q0 q1 c0 ∧ CosHi q0 q1 c1 ∧ qlt qzero c0 ∧
    RecipOK r1 r2 c0 c1 ∧ qle qzero r1 ∧ SinLo qzero (qsub q1 q0) qzero ∧
    (∃ s0l s0h c0l c0h ρl ρh, SinCert q0 s0l s0h ∧ CosCert q0 c0l c0h ∧ qlt qzero c0l ∧ RecipOK ρl ρh c0l c0h ∧
      qle qzero ρl ∧ qle (qmul Tl c0l) s0l ∧ qle (qmul Tl c0h) s0l) ∧
    (∃ s1l s1h c1l c1h ρl ρh, SinCert q1 s1l s1h ∧ CosCert q1 c1l c1h ∧ qlt qzero c1l ∧ RecipOK ρl ρh c1l c1h ∧
      qle qzero ρl ∧ qle s1h (qmul Th c1l) ∧ qle s1h (qmul Th c1h))

/-- The window's `cos` reading and its reciprocal, from a `TanVal`. -/
theorem TanVal.cos {x : Nat → QExpr} {lu hu Tl Th : QExpr} (hx : Ev x lu hu) (t : TanVal lu hu Tl Th) :
    ∃ c0 c1 r1 r2, Ev (fun n => Cn (x n) n) c0 c1 ∧ qlt qzero c0 ∧ RecipOK r1 r2 c0 c1 := by
  obtain ⟨q0, q1, c0, c1, r1, r2, h0, h1, hq, cL, cH, cp, rc, _, _, _, _⟩ := t
  exact ⟨c0, c1, r1, r2, Ev_cos (Ev_widen hx h0 h1) hq cH cL, cp, rc⟩

/-- THE KERNEL'S `tan` OVER AN INTERVAL IS SOUND (`zfunc.iv_tan`). -/
theorem Ev_tan {x : Nat → QExpr} {lu hu Tl Th : QExpr} (hx : Ev x lu hu) (t : TanVal lu hu Tl Th) :
    Ev (fun n => qmul (Sn (x n) n) (qinv' (Cn (x n) n))) Tl Th := by
  obtain ⟨q0, q1, c0, c1, r1, r2, h0, h1, hq, cL, cH, cp, rc, r10, sw,
    ⟨s0l, s0h, c0l, c0h, ρ0l, ρ0h, S0, C0, c0lp, R0, ρ0, T1, T2⟩,
    ⟨s1l, s1h, c1l, c1h, ρ1l, ρ1h, S1, C1, c1lp, R1, ρ1, U1, U2⟩⟩ := t
  have hC := Ev_cos (Ev_widen hx h0 h1) hq cH cL
  have d0 : qle qzero (qsub q1 q0) := by unfold qsub; rat_linarith
  refine Ev_of_sides (tan_low hx h0 (by unfold qsub; rat_linarith) d0 hC cp rc r10 sw S0 C0 c0lp R0 ρ0 T1 T2)
    (tan_high hx h1 (by unfold qsub; rat_linarith) d0 hC cp rc r10 sw S1 C1 c1lp R1 ρ1 U1 U2)

end ZTrig

#print axioms ZTrig.corners_nn
#print axioms ZTrig.nonneg_prod
#print axioms ZTrig.ev_pos
#print axioms ZTrig.recip_hi_nonneg
#print axioms ZTrig.lin_end
#print axioms ZTrig.tan_low
#print axioms ZTrig.sincert_neg
#print axioms ZTrig.coscert_neg
#print axioms ZTrig.tan_high
#print axioms ZTrig.TanVal.cos
#print axioms ZTrig.Ev_tan
