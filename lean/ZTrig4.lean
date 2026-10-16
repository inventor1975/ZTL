import ZTrig3

/-!
# ZTrig4 — `cos` falls on `[0, 2]`; its first zero `ρ` (`π = 2ρ`), found on a grid. Zero axioms.

Stage 4 of the full sine.

  * `cos_mono` — on `[0, 2]`, at every index: `C(b) − C(a) ≤ 4·corner` for `a ≤ b`; and for `1 ≤ a`,
    `b − a ≤ 225·(C(a) − C(b) + 4·corner)` (`sum_to_product` with `sin m ≥ 1/15`, `sin d ≥ d/15`). The constant
    `225 = 15·15` is kept as an atom: VR's numerals are unary, so linear arithmetic never multiplies by it.
  * `rl` — at index `n`, the length of the INITIAL RUN of grid points `j·2^−n`, `1 ≤ j ≤ 2^(n+1)`, where `C_n ≥ 0`:
    no monotonicity of `C_n` is needed — the first failure is taken, as `ZLn` takes the count.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-! ## `cos` falls on `[0, 2]` -/

/-- `225` as an atom: `(3·5)·(3·5)`, the same atoms as `sin_lower`'s. -/
def c225 : QExpr := qmul (qmul (qnat 3) (qnat 5)) (qmul (qnat 3) (qnat 5))

theorem c225_nonneg : qle qzero c225 :=
  qmul_nonneg (qmul_nonneg (qnat_nonneg 3) (qnat_nonneg 5)) (qmul_nonneg (qnat_nonneg 3) (qnat_nonneg 5))

/-- Four corners of `exp`'s series at `2`. -/
def K4 (N : Nat) : QExpr :=
  qadd (qadd (corner (tm (qadd qone qone)) (tm (qadd qone qone)) N) (corner (tm (qadd qone qone)) (tm (qadd qone qone)) N))
    (qadd (corner (tm (qadd qone qone)) (tm (qadd qone qone)) N) (corner (tm (qadd qone qone)) (tm (qadd qone qone)) N))

theorem two_pos : qle qzero (qadd qone qone) := by have := qle_of_qlt qone_pos; rat_linarith

/-- `m = (a+b)/2`, `d = (b−a)/2` as `m ± d`: written with `h = 1/2`. -/
def half : QExpr := qinv' (qadd qone qone)

theorem half_facts : qEq (qadd half half) qone ∧ qle qzero half := by
  have hp : qlt qzero (qadd qone qone) := by
    have := qone_pos; exact qlt_respects (qEq_refl _) (by rat_ring) (qadd_pos this this)
  have c := qmul_inv'_cancel (ne_zero_of_lt hp)
  have n := qinv'_nonneg_of_pos hp
  unfold half
  exact ⟨by
    have e : qEq (qadd (qinv' (qadd qone qone)) (qinv' (qadd qone qone))) (qmul (qadd qone qone) (qinv' (qadd qone qone))) := by
      rat_ring
    exact qEq_trans e c, n⟩

/-- `0 ≤ x ≤ 3·5·S` gives `S ≥ 0`. -/
theorem nonneg_of_scaled {x S : QExpr} (h : qle x (qmul (qnat 3) (qmul (qnat 5) S))) (hx : qle qzero x) : qle qzero S := by
  have e := qmul_respects nlit3 (qmul_respects nlit5 (qEq_refl S))
  have h' := qle_trans h (qle_of_qEq e)
  generalize S = s at *
  rat_linarith

/-- `cos` FALLS ON `[0, 2]`, at every index past `5`, up to four corners. -/
theorem cos_mono {a b : QExpr} (ha : qle qzero a) (hab : qle a b) (hb : qle b (qadd qone qone)) {N : Nat} (hN : 5 ≤ N) :
    qle (qsub (Cn b N) (Cn a N)) (K4 N) := by
  obtain ⟨hh, h0⟩ := half_facts
  -- m = (a+b)·½, d = (b−a)·½, both in [0, 2]
  have m0 : qle qzero (qmul (qadd a b) half) := qmul_nonneg (by rat_linarith) h0
  have d0 : qle qzero (qmul (qsub b a) half) := qmul_nonneg (by unfold qsub; rat_linarith) h0
  have em : qEq (qadd (qmul (qadd a b) half) (qmul (qsub b a) half)) b := by
    have := qmul_respects (qEq_refl b) hh
    exact qEq_trans (show qEq _ (qmul b (qadd half half)) by unfold qsub; rat_ring) (qEq_trans this (qmul_one b))
  have ed : qEq (qsub (qmul (qadd a b) half) (qmul (qsub b a) half)) a := by
    have := qmul_respects (qEq_refl a) hh
    exact qEq_trans (show qEq _ (qmul a (qadd half half)) by unfold qsub; rat_ring) (qEq_trans this (qmul_one a))
  have m2 : qle (qmul (qadd a b) half) (qadd qone qone) := by
    have := ZExp.scale (show qle (qadd a b) (qadd (qadd qone qone) (qadd qone qone)) by rat_linarith) h0
    have e : qEq (qmul (qadd (qadd qone qone) (qadd qone qone)) half) (qmul (qadd qone qone) (qadd half half)) := by rat_ring
    have e2 := qmul_respects (qEq_refl (qadd qone qone)) hh
    have e3 := qmul_one (qadd qone qone)
    generalize qmul (qadd a b) half = mm at *; generalize qadd half half = hh2 at *
    generalize qmul (qadd (qadd qone qone) (qadd qone qone)) half = w at *
    exact qle_trans this (qle_of_qEq (qEq_trans e (qEq_trans e2 e3)))
  have d2 : qle (qmul (qsub b a) half) (qadd qone qone) := by
    have := ZExp.scale (show qle (qsub b a) (qadd (qadd qone qone) (qadd qone qone)) by unfold qsub; rat_linarith) h0
    have e : qEq (qmul (qadd (qadd qone qone) (qadd qone qone)) half) (qmul (qadd qone qone) (qadd half half)) := by rat_ring
    have e2 := qmul_respects (qEq_refl (qadd qone qone)) hh
    have e3 := qmul_one (qadd qone qone)
    generalize qmul (qsub b a) half = dd at *; generalize qadd half half = hh2 at *
    generalize qmul (qadd (qadd qone qone) (qadd qone qone)) half = w at *
    exact qle_trans this (qle_of_qEq (qEq_trans e (qEq_trans e2 e3)))
  have hm : Ab (qmul (qadd a b) half) (qadd qone qone) := ⟨by rat_linarith, m2⟩
  have hd : Ab (qmul (qsub b a) half) (qadd qone qone) := ⟨by rat_linarith, d2⟩
  obtain ⟨⟨p1, p2⟩, _⟩ := sum_to_product hm hd N
  have cb := Cn_respects em N
  have ca := Cn_respects ed N
  have sm := sin_lower m0 m2 hN
  have sd := sin_lower d0 d2 hN
  -- S(m), S(d) ≥ 0, so their product is
  have sm0 : qle qzero (Sn (qmul (qadd a b) half) N) := nonneg_of_scaled sm m0
  have sd0 : qle qzero (Sn (qmul (qsub b a) half) N) := nonneg_of_scaled sd d0
  have pr := qmul_nonneg sm0 sd0
  unfold K4
  generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) N = K at *
  generalize Cn (qadd (qmul (qadd a b) half) (qmul (qsub b a) half)) N = A1 at *
  generalize Cn (qsub (qmul (qadd a b) half) (qmul (qsub b a) half)) N = A2 at *
  generalize qmul (Sn (qmul (qadd a b) half) N) (Sn (qmul (qsub b a) half) N) = P at *
  generalize Cn b N = Cb at *; generalize Cn a N = Ca at *
  unfold qsub at *
  rat_linarith

/-- `cos` FALLS AT A RATE on `[1, 2]`: `b − a ≤ 225·(C(a) − C(b) + 4·corner)`, at every index past `5`. -/
theorem cos_slope {a b : QExpr} (h1 : qle qone a) (hab : qle a b) (hb : qle b (qadd qone qone)) {N : Nat} (hN : 5 ≤ N) :
    qle (qsub b a) (qmul c225 (qadd (qsub (Cn a N) (Cn b N)) (K4 N))) := by
  have ha : qle qzero a := qle_trans (qle_of_qlt qone_pos) h1
  obtain ⟨hh, h0⟩ := half_facts
  -- m = (a+b)·½, d = (b−a)·½, both in [0, 2]
  have m0 : qle qzero (qmul (qadd a b) half) := qmul_nonneg (by rat_linarith) h0
  have d0 : qle qzero (qmul (qsub b a) half) := qmul_nonneg (by unfold qsub; rat_linarith) h0
  have em : qEq (qadd (qmul (qadd a b) half) (qmul (qsub b a) half)) b := by
    have := qmul_respects (qEq_refl b) hh
    exact qEq_trans (show qEq _ (qmul b (qadd half half)) by unfold qsub; rat_ring) (qEq_trans this (qmul_one b))
  have ed : qEq (qsub (qmul (qadd a b) half) (qmul (qsub b a) half)) a := by
    have := qmul_respects (qEq_refl a) hh
    exact qEq_trans (show qEq _ (qmul a (qadd half half)) by unfold qsub; rat_ring) (qEq_trans this (qmul_one a))
  have m2 : qle (qmul (qadd a b) half) (qadd qone qone) := by
    have := ZExp.scale (show qle (qadd a b) (qadd (qadd qone qone) (qadd qone qone)) by rat_linarith) h0
    have e : qEq (qmul (qadd (qadd qone qone) (qadd qone qone)) half) (qmul (qadd qone qone) (qadd half half)) := by rat_ring
    have e2 := qmul_respects (qEq_refl (qadd qone qone)) hh
    have e3 := qmul_one (qadd qone qone)
    generalize qmul (qadd a b) half = mm at *; generalize qadd half half = hh2 at *
    generalize qmul (qadd (qadd qone qone) (qadd qone qone)) half = w at *
    exact qle_trans this (qle_of_qEq (qEq_trans e (qEq_trans e2 e3)))
  have d2 : qle (qmul (qsub b a) half) (qadd qone qone) := by
    have := ZExp.scale (show qle (qsub b a) (qadd (qadd qone qone) (qadd qone qone)) by unfold qsub; rat_linarith) h0
    have e : qEq (qmul (qadd (qadd qone qone) (qadd qone qone)) half) (qmul (qadd qone qone) (qadd half half)) := by rat_ring
    have e2 := qmul_respects (qEq_refl (qadd qone qone)) hh
    have e3 := qmul_one (qadd qone qone)
    generalize qmul (qsub b a) half = dd at *; generalize qadd half half = hh2 at *
    generalize qmul (qadd (qadd qone qone) (qadd qone qone)) half = w at *
    exact qle_trans this (qle_of_qEq (qEq_trans e (qEq_trans e2 e3)))
  have hm : Ab (qmul (qadd a b) half) (qadd qone qone) := ⟨by rat_linarith, m2⟩
  have hd : Ab (qmul (qsub b a) half) (qadd qone qone) := ⟨by rat_linarith, d2⟩
  obtain ⟨⟨p1, p2⟩, _⟩ := sum_to_product hm hd N
  have cb := Cn_respects em N
  have ca := Cn_respects ed N
  have sm := sin_lower m0 m2 hN
  have sd := sin_lower d0 d2 hN
  -- S(m), S(d) ≥ 0, so their product is
  have sm0 : qle qzero (Sn (qmul (qadd a b) half) N) := nonneg_of_scaled sm m0
  have sd0 : qle qzero (Sn (qmul (qsub b a) half) N) := nonneg_of_scaled sd d0
  have pr := qmul_nonneg sm0 sd0
  -- 1 ≤ m, so 1 ≤ 15·S(m); d ≤ 15·S(d); d ≤ 15·S(d)·15·S(m) = 225·S(m)·S(d)
  have m1 : qle qone (qmul (qadd a b) half) := by
    have := ZExp.scale (show qle (qadd qone qone) (qadd a b) by rat_linarith) h0
    have e : qEq (qmul (qadd qone qone) half) (qadd half half) := by rat_ring
    generalize qmul (qadd a b) half = mm at *; generalize qadd half half = hh2 at *
    generalize qmul (qadd qone qone) half = w at *; rat_linarith
  have X1 : qle qone (qmul (qnat 3) (qmul (qnat 5) (Sn (qmul (qadd a b) half) N))) := qle_trans m1 sm
  have Y0 : qle qzero (qmul (qnat 3) (qmul (qnat 5) (Sn (qmul (qsub b a) half) N))) := qle_trans d0 sd
  have YX := scale_l X1 Y0
  have pc := scale_l (show qle (qadd (qmul (Sn (qmul (qadd a b) half) N) (Sn (qmul (qsub b a) half) N))
      (qmul (Sn (qmul (qadd a b) half) N) (Sn (qmul (qsub b a) half) N)))
      (qadd (qsub (Cn a N) (Cn b N)) (K4 N)) by
    unfold K4
    have cb' := cb; have ca' := ca
    generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) N = K at *
    generalize Cn (qadd (qmul (qadd a b) half) (qmul (qsub b a) half)) N = A1 at *
    generalize Cn (qsub (qmul (qadd a b) half) (qmul (qsub b a) half)) N = A2 at *
    generalize qmul (Sn (qmul (qadd a b) half) N) (Sn (qmul (qsub b a) half) N) = P at *
    generalize Cn b N = Cb at *; generalize Cn a N = Ca at *
    unfold qsub at *; rat_linarith) c225_nonneg
  have twod : qEq (qadd (qmul (qsub b a) half) (qmul (qsub b a) half)) (qsub b a) := by
    have := qmul_respects (qEq_refl (qsub b a)) hh
    exact qEq_trans (show qEq _ (qmul (qsub b a) (qadd half half)) by rat_ring) (qEq_trans this (qmul_one _))
  unfold c225 at *
  generalize Sn (qmul (qadd a b) half) N = Sm at *; generalize Sn (qmul (qsub b a) half) N = Sd at *
  generalize qmul (qsub b a) half = dd at *
  generalize qadd (qsub (Cn a N) (Cn b N)) (K4 N) = R at *
  clear p1 p2 cb ca em ed hm hd m2 d2 m0 X1 sm m1 pr sm0 sd0 hh
  generalize qnat 3 = t3 at *; generalize qnat 5 = t5 at *
  rat_linarith

/-! ## The corners vanish -/

/-- `K4(n) → 0`: from some index on, `K4(n) ≤ ε_k`. -/
theorem K4_small (k : Nat) : ∃ N0, ∀ n, N0 ≤ n → qle (K4 n) (qeps k) := by
  have h2 := two_pos
  obtain ⟨H, hH⟩ := S_bounded h2
  have H0 : qle qzero H := qle_trans (S_nonneg h2 0) (hH 0)
  obtain ⟨B, hB1, _⟩ := qexpr_bound (qadd (qadd (qadd H H) (qadd H H)) (qadd (qadd H H) (qadd H H)))
  have hB : qle (qadd (qadd (qadd H H) (qadd H H)) (qadd (qadd H H) (qadd H H))) (qofInt (pow2 B)) := by
    unfold qsub at hB1; rat_linarith
  obtain ⟨K0, hg⟩ := good_exists (qadd qone qone)
  obtain ⟨M, hKM, hM⟩ := tm_small h2 hg (k + B)
  have gM : Good (qadd qone qone) M := good_mono hg hKM
  refine ⟨M + M, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := le_ex hn
  have c := corner_exp h2 h2 hH hH gM gM j
  have t := hM M (Nat.le_refl M)
  have t0 := tm_nonneg h2 M
  have pb := qpow2_mul_eps B k
  have f1 := ZExp.scale t H0
  have f2 := scale_l t H0
  have f3 := ZExp.scale hB (qeps_nonneg (k + B))
  unfold K4
  generalize corner (tm (qadd qone qone)) (tm (qadd qone qone)) (M + M + j) = K at *
  generalize tm (qadd qone qone) M = T at *
  rat_linarith

/-! ## The grid on `[0, 2]` and the initial run where `cos ≥ 0` -/

/-- The top index: `gq n (top n) = 2`. -/
def top (n : Nat) : Nat := 2 ^ n * 2

theorem gq_pow (n : Nat) : qEq (gq n (2 ^ n)) qone := by
  unfold gq
  have h2 := qnat_pow2 n
  have m : qEq (qmul (qofInt (pow2 n)) (qeps (0 + n))) (qeps 0) := qpow2_mul_eps n 0
  rw [Nat.zero_add] at m
  exact qEq_trans (qmul_respects h2 (qEq_refl _)) (qEq_trans m qeps_zero)

theorem gq_top (n : Nat) : qEq (gq n (top n)) (qadd qone qone) := by
  unfold gq top
  have h1 := qnat_mul (2 ^ n) 2
  have p := gq_pow n
  unfold gq at p
  have e : qEq (qmul (qmul (qnat (2 ^ n)) (qnat 2)) (qeps n)) (qmul (qmul (qnat (2 ^ n)) (qeps n)) (qnat 2)) := by rat_ring
  have e2 := qmul_respects p (qEq_refl (qnat 2))
  exact qEq_trans (qmul_respects h1 (qEq_refl _)) (qEq_trans e (qEq_trans e2 (qEq_trans (qone_mul _) nlit2)))

theorem gq_mono (n : Nat) {i j : Nat} (h : i ≤ j) : qle (gq n i) (gq n j) := ZExp.scale (qnat_mono h) (qeps_nonneg n)

/-- One step of the run: extend it by the next point if it is unbroken and the point has `C_n ≥ 0`. -/
def rlstep (n j r : Nat) : Nat :=
  match Nat.decEq r j, qle.decidable qzero (Cn (gq n (j + 1)) n) with
  | .isTrue _, .isTrue _ => j + 1
  | _, _ => r

/-- At index `n`, the length of the initial run of grid points `1..j` where `C_n ≥ 0`. -/
def rl (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => rlstep n j (rl n j)

theorem rl_step_t {n j : Nat} (h1 : rl n j = j) (h2 : qle qzero (Cn (gq n (j + 1)) n)) : rl n (j + 1) = j + 1 := by
  show rlstep n j (rl n j) = j + 1
  unfold rlstep
  cases Nat.decEq (rl n j) j with
  | isTrue _ => cases qle.decidable qzero (Cn (gq n (j + 1)) n) with
    | isTrue _ => rfl
    | isFalse h => exact absurd h2 h
  | isFalse h => exact absurd h1 h

theorem rl_step_f {n j : Nat} (h : ¬ (rl n j = j ∧ qle qzero (Cn (gq n (j + 1)) n))) : rl n (j + 1) = rl n j := by
  show rlstep n j (rl n j) = rl n j
  unfold rlstep
  cases Nat.decEq (rl n j) j with
  | isTrue h1 => cases qle.decidable qzero (Cn (gq n (j + 1)) n) with
    | isTrue h2 => exact absurd ⟨h1, h2⟩ h
    | isFalse _ => rfl
  | isFalse _ => rfl

/-- THE RUN: `rl ≤ j`; every point `1..rl` has `C_n ≥ 0`; if the run stops early, the next point has `C_n < 0`. -/
theorem rl_spec (n : Nat) : ∀ j,
    rl n j ≤ j ∧ (∀ i, 1 ≤ i → i ≤ rl n j → qle qzero (Cn (gq n i) n)) ∧
    (rl n j < j → ¬ qle qzero (Cn (gq n (rl n j + 1)) n))
  | 0 => ⟨Nat.le_refl 0, fun i h1 h2 => absurd (Nat.le_trans h1 h2) (Nat.not_succ_le_zero 0),
          fun h => absurd h (Nat.lt_irrefl 0)⟩
  | j + 1 => by
      obtain ⟨c1, c2, c3⟩ := rl_spec n j
      cases Nat.decEq (rl n j) j with
      | isTrue e =>
          cases qle.decidable qzero (Cn (gq n (j + 1)) n) with
          | isTrue p =>
              rw [rl_step_t e p]
              refine ⟨Nat.le_refl _, fun i h1 h2 => ?_, fun h => absurd h (Nat.lt_irrefl _)⟩
              cases Nat.lt_or_eq_of_le h2 with
              | inl lt => exact c2 i h1 (by rw [e]; exact Nat.le_of_lt_succ lt)
              | inr eq => rw [eq]; exact p
          | isFalse p =>
              rw [rl_step_f (fun h => p h.2)]
              refine ⟨Nat.le_succ_of_le c1, c2, fun _ => ?_⟩
              rw [e]; exact p
      | isFalse e =>
          rw [rl_step_f (fun h => e h.1)]
          have lt : rl n j < j := Nat.lt_of_le_of_ne c1 e
          exact ⟨Nat.le_succ_of_le c1, c2, fun _ => c3 lt⟩

/-! ## `ρ`: the run's end, at large indices -/

/-- `ρ_n`: the last grid point of the run. -/
def rho (n : Nat) : QExpr := gq n (rl n (top n))

theorem pow_le_top (n : Nat) : 2 ^ n ≤ top n := by
  show 2 ^ n ≤ 2 ^ n * 2; rw [Nat.mul_two]; exact Nat.le_add_right _ _

/-- AT LARGE INDICES the run reaches `1` and stops before `2`: `1 ≤ ρ_n`, `ρ_n + 2^−n ≤ 2`, `C_n(ρ_n) ≥ 0`,
`C_n(ρ_n + 2^−n) < 0`. -/
theorem rho_facts : ∃ N0, ∀ n, N0 ≤ n →
    qle qone (rho n) ∧ qle (qadd (rho n) (qeps n)) (qadd qone qone) ∧
    qle qzero (Cn (rho n) n) ∧ ¬ qle qzero (Cn (qadd (rho n) (qeps n)) n) := by
  obtain ⟨N1, hN1⟩ := K4_small 2
  refine ⟨N1 + 6, fun n hn => ?_⟩
  have hn6 : 6 ≤ n := Nat.le_trans (Nat.le_add_left 6 N1) hn
  have hn5 : 5 ≤ n := Nat.le_trans (Nat.le_succ 5) hn6
  have hK := hN1 n (Nat.le_trans (Nat.le_add_right N1 6) hn)
  have e2 : qEq (qeps 2) (qmul (qeps 1) (qeps 1)) := qEq_symm (qeps_mul 1 1)
  have q1 := qeps_succ_add 1; have q0 := qeps_succ_add 0; have z := qeps_zero
  -- every point up to 1 has C_n ≥ 0
  have up : ∀ i, 1 ≤ i → i ≤ 2 ^ n → qle qzero (Cn (gq n i) n) := by
    intro i _ hi
    have g0 := gq_nonneg n i
    have g1 : qle (gq n i) qone := qle_trans (gq_mono n hi) (qle_of_qEq (gq_pow n))
    have cm := cos_mono g0 g1 (by have := qle_of_qlt qone_pos; rat_linarith) hn5
    have c1 := cos_one hn6
    have c1' := qle_trans c1 (qle_of_qEq (qmul_respects nlit3 (qEq_refl _)))
    generalize Cn (gq n i) n = Ci at *; generalize Cn qone n = C1 at *; generalize K4 n = K at *
    clear e2
    unfold qsub at *; rat_linarith
  -- the point 2 has C_n < 0
  have down : ¬ qle qzero (Cn (gq n (top n)) n) := by
    intro h
    have c2 := cos_two hn6
    have c2' := qle_trans (qle_of_qEq (qEq_symm (qmul_respects nlit9 (qEq_refl _)))) c2
    have e := Cn_respects (gq_top n) n
    generalize Cn (gq n (top n)) n = Ct at *; generalize Cn (qadd qone qone) n = C2 at *
    have := qle_of_qlt qone_pos
    have h' : qle qzero C2 := by rat_linarith
    have : qle qone qzero := by rat_linarith
    exact (qlt_iff_le_not_le.mp qone_pos).2 this
  obtain ⟨c1, c2, c3⟩ := rl_spec n (top n)
  have ge : 2 ^ n ≤ rl n (top n) := by
    cases Nat.lt_or_ge (rl n (top n)) (2 ^ n) with
    | inl lt =>
        have lt' : rl n (top n) < top n := Nat.lt_of_lt_of_le lt (pow_le_top n)
        exact absurd (up _ (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt lt)) (c3 lt')
    | inr ge => exact ge
  have lt : rl n (top n) < top n := by
    cases Nat.lt_or_eq_of_le c1 with
    | inl l => exact l
    | inr e => exact absurd (c2 (top n) (Nat.le_trans (Nat.two_pow_pos n) (pow_le_top n)) (Nat.le_of_eq e.symm)) down
  have pos : 1 ≤ rl n (top n) := Nat.le_trans (Nat.two_pow_pos n) ge
  refine ⟨qle_trans (qle_of_qEq (qEq_symm (gq_pow n))) (gq_mono n ge), ?_, c2 _ pos (Nat.le_refl _), ?_⟩
  · have s := gq_succ n (rl n (top n))
    exact qle_trans (qle_of_qEq (qEq_symm s)) (qle_trans (gq_mono n (Nat.succ_le_of_lt lt)) (qle_of_qEq (gq_top n)))
  · intro h
    exact c3 lt (qle_respects (qEq_refl _) (Cn_respects (qEq_symm (gq_succ n (rl n (top n)))) n) h)

/-! ## `ρ` is an operational real -/

/-- UNIFORM ON `[−2, 2]`: from some index on, `|C_m(x) − C_n(x)| ≤ ε_k` for every such `x`. -/
theorem C_unif (k : Nat) : ∃ M, ∀ m n, M ≤ m → M ≤ n → ∀ x, Ab x (qadd qone qone) →
    Ab (qsub (Cn x m) (Cn x n)) (qeps k) := by
  have h2 := two_pos
  obtain ⟨K0, hg⟩ := good_exists (qadd qone qone)
  obtain ⟨M, hKM, hM⟩ := tm_small h2 hg (k + 1)
  have gM : Good (qadd qone qone) M := good_mono hg hKM
  refine ⟨M, fun m n hm hn x hx => ?_⟩
  obtain ⟨⟨a1, a2⟩, _⟩ := CS_tail hx gM m hm
  obtain ⟨⟨b1, b2⟩, _⟩ := CS_tail hx gM n hn
  have t := hM M (Nat.le_refl M)
  have e := qeps_succ_add k
  generalize Cn x m = Cm at *; generalize Cn x n = Cnn at *; generalize Cn x M = CM at *
  generalize tm (qadd qone qone) M = T at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- One side of the trap: `ρ_m ≤ ρ_n + 2^−n + 225·(τ + K4(n))`. -/
theorem rho_side {m n : Nat} {τ : QExpr} (hm : qle qone (rho m) ∧ qle (qadd (rho m) (qeps m)) (qadd qone qone) ∧
      qle qzero (Cn (rho m) m) ∧ ¬ qle qzero (Cn (qadd (rho m) (qeps m)) m))
    (hn : qle qone (rho n) ∧ qle (qadd (rho n) (qeps n)) (qadd qone qone) ∧
      qle qzero (Cn (rho n) n) ∧ ¬ qle qzero (Cn (qadd (rho n) (qeps n)) n))
    (hτ : Ab (qsub (Cn (rho m) m) (Cn (rho m) n)) τ) (h5 : 5 ≤ n) :
    qle (rho m) (qadd (qadd (rho n) (qeps n)) (qmul c225 (qadd τ (K4 n)))) := by
  obtain ⟨m1, m2, m3, _⟩ := hm
  obtain ⟨n1, n2, _, n4⟩ := hn
  obtain ⟨t1, t2⟩ := hτ
  have τ0 : qle qzero τ := by rat_linarith
  have K0 : qle qzero (K4 n) := by
    -- K4 ≥ 0: from cos_mono at a = b
    have := cos_mono (a := qone) (b := qone) (qle_of_qlt qone_pos) (qle_refl _) (by have := qle_of_qlt qone_pos; rat_linarith) h5
    unfold qsub at this; rat_linarith
  have e0 := qeps_nonneg n
  have m0 : qle (rho m) (qadd qone qone) := by have := qeps_nonneg m; rat_linarith
  have nn : qle (Cn (qadd (rho n) (qeps n)) n) qzero := by
    cases qle_total qzero (Cn (qadd (rho n) (qeps n)) n) with
    | inl h => exact absurd h n4
    | inr h => exact h
  have cp := qmul_nonneg c225_nonneg (show qle qzero (qadd τ (K4 n)) by rat_linarith)
  cases qle_total (rho m) (qadd (rho n) (qeps n)) with
  | inl h => rat_linarith
  | inr h =>
      have sl := cos_slope (a := qadd (rho n) (qeps n)) (b := rho m) (by rat_linarith) h m0 h5
      have f := scale_l (show qle (qadd (qsub (Cn (qadd (rho n) (qeps n)) n) (Cn (rho m) n)) (K4 n)) (qadd τ (K4 n)) by
        unfold qsub at *; rat_linarith) c225_nonneg
      unfold qsub at *; rat_linarith

theorem tl {a b n : Nat} (h : a + b ≤ n) : a ≤ n := Nat.le_trans (Nat.le_add_right a b) h
theorem tr {a b n : Nat} (h : a + b ≤ n) : b ≤ n := Nat.le_trans (Nat.le_add_left b a) h

/-- The trap's arithmetic: two sides, each within `2·ε_{k+2}`. -/
theorem close_of_sides {rm rn en em X Y e2 e1 e0 : QExpr} (s1 : qle rm (qadd (qadd rn en) X))
    (s2 : qle rn (qadd (qadd rm em) Y)) (b1 : qle X e2) (b2 : qle Y e2) (hen : qle en e2) (hem : qle em e2)
    (h1 : qEq (qadd e2 e2) e1) (h0 : qEq (qadd e1 e1) e0) (p1 : qle qzero e1) :
    qle (qsub rm rn) e0 ∧ qle (qneg e0) (qsub rm rn) := by
  have A : qle (qsub rm rn) (qadd en X) := by clear s2 b1 b2 hen hem h1 h0 p1; unfold qsub; rat_linarith
  have A' : qle (qsub rn rm) (qadd em Y) := by clear s1 b1 b2 hen hem h1 h0 p1 A; unfold qsub; rat_linarith
  have B : qle (qadd en X) e1 := by clear s1 s2 b2 hem h0 p1 A A'; rat_linarith
  have B' : qle (qadd em Y) e1 := by clear s1 s2 b1 hen h0 p1 A A' B; rat_linarith
  have C : qle e1 e0 := by clear s1 s2 b1 b2 hen hem h1 A A' B B'; rat_linarith
  have D := qle_trans A (qle_trans B C)
  have D' := qle_trans A' (qle_trans B' C)
  clear s1 s2 b1 b2 hen hem h1 h0 p1 A A' B B' C
  unfold qsub at *; exact ⟨D, by rat_linarith⟩

/-- `ρ` IS AN OPERATIONAL REAL: the run's ends at two large indices are close. -/
theorem rho_cauchy : ZRecip.Cauchy rho := fun k => by
  obtain ⟨N0, hN0⟩ := rho_facts
  obtain ⟨B, hB1, _⟩ := qexpr_bound c225
  have hB : qle c225 (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  obtain ⟨Mu, hMu⟩ := C_unif (k + 3 + B)
  obtain ⟨Nk, hNk⟩ := K4_small (k + 3 + B)
  refine ⟨N0 + (Mu + (Nk + ((k + 2) + 5))), fun m n hm hn => ?_⟩
  have fm := hN0 m (tl hm)
  have fn := hN0 n (tl hn)
  have Ab_m : Ab (rho m) (qadd qone qone) := by
    obtain ⟨a1, a2, _, _⟩ := fm; have := qeps_nonneg m; have := qle_of_qlt qone_pos
    exact ⟨by rat_linarith, by rat_linarith⟩
  have Ab_n : Ab (rho n) (qadd qone qone) := by
    obtain ⟨a1, a2, _, _⟩ := fn; have := qeps_nonneg n; have := qle_of_qlt qone_pos
    exact ⟨by rat_linarith, by rat_linarith⟩
  have τ1 := hMu m n (tl (tr hm)) (tl (tr hn)) (rho m) Ab_m
  have τ2 := hMu n m (tl (tr hn)) (tl (tr hm)) (rho n) Ab_n
  have s1 := rho_side fm fn τ1 (tr (tr (tr (tr hn))))
  have s2 := rho_side fn fm τ2 (tr (tr (tr (tr hm))))
  have kn := hNk n (tl (tr (tr hn)))
  have km := hNk m (tl (tr (tr hm)))
  have en : qle (qeps n) (qeps (k + 2)) := eps_anti (tl (tr (tr (tr hn))))
  have em : qle (qeps m) (qeps (k + 2)) := eps_anti (tl (tr (tr (tr hm))))
  have ep := qeps_nonneg (k + 3 + B)
  have pB := qpow2_mul_eps B (k + 3)
  have bound : ∀ K, qle K (qeps (k + 3 + B)) → qle (qmul c225 (qadd (qeps (k + 3 + B)) K)) (qeps (k + 2)) := by
    intro K hK
    have f1 := scale_l (show qle (qadd (qeps (k + 3 + B)) K) (qadd (qeps (k + 3 + B)) (qeps (k + 3 + B))) by rat_linarith)
      c225_nonneg
    have f2 := ZExp.scale hB (show qle qzero (qadd (qeps (k + 3 + B)) (qeps (k + 3 + B))) by rat_linarith)
    have e3 := qeps_succ_add (k + 2)
    have e4 : qEq (qmul (qofInt (pow2 B)) (qadd (qeps (k + 3 + B)) (qeps (k + 3 + B))))
        (qadd (qmul (qofInt (pow2 B)) (qeps (k + 3 + B))) (qmul (qofInt (pow2 B)) (qeps (k + 3 + B)))) := by rat_ring
    have e5 : k + 3 + B = (k + 2) + 1 + B := rfl
    rw [e5] at e4 f1 f2 ⊢ pB
    rat_linarith
  have b1 := bound (K4 n) kn
  have b2 := bound (K4 m) km
  have e1 := qeps_succ_add (k + 1); have e0 := qeps_succ_add k
  have p1 := qeps_nonneg (k + 1); have p2 := qeps_nonneg (k + 2)
  exact close_of_sides s1 s2 b1 b2 en em e1 e0 p1

end ZTrig

#print axioms ZTrig.half_facts
#print axioms ZTrig.cos_mono
#print axioms ZTrig.cos_slope
#print axioms ZTrig.K4_small
#print axioms ZTrig.gq_top
#print axioms ZTrig.rl_spec
#print axioms ZTrig.rho_facts
#print axioms ZTrig.C_unif
#print axioms ZTrig.rho_side
#print axioms ZTrig.rho_cauchy
