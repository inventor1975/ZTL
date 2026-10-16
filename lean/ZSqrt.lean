import ZLn

/-!
# ZSqrt — the square root on VR's operational reals, found on a grid. Zero axioms.

As `ZLn` does for the logarithm: a value of `√y` is not "the `x` that exists" — at index `n` it is COMPUTED, the last
point of the grid `0, 2^−n, …, n + 1` whose square is `≤ y` (`rsqrt`, a count over the grid; squares rise on it, so
the true points form an initial run). Then `s² ≤ y < (s + 2^−n)²` (`sqrt_bracket`).

  * `Ev_sqrt` — the value: the kernel's rational fork `[SL, SH]` (`SL² ≤ lo`, `hi ≤ SH²`, both `≥ 0`, as
    `znum._rat_sqrt` builds it) holds `√` of an argument read in `[lo, hi]`;
  * `Ev_sqrt_slope` — the slope, with no mean value theorem: `s_b − s_a = (s_b² − s_a²) · 1/(s_a + s_b)` exactly,
    `s² ` is the argument up to the grid's gap, and `1/(s_a + s_b)` is near the kernel's reading of `1/(2·√U)`;
  * `sqrt_cauchy` — the answers at two indices are close: `√` of an operational real.
-/

namespace ZSqrt

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn

/-- `x²`. -/
def sq (x : QExpr) : QExpr := qmul x x

theorem sq_respects {x x' : QExpr} (h : qEq x x') : qEq (sq x) (sq x') := qmul_respects h h

/-- Squares rise on `[0, ∞)`. -/
theorem sq_mono {x y : QExpr} (hx : qle qzero x) (hxy : qle x y) : qle (sq x) (sq y) :=
  qle_trans (ZExp.scale hxy hx) (scale_l hxy (qle_trans hx hxy))

/-! ## The grid and the count -/

/-- The `j`-th point of the grid of step `ε_n` from `0`. -/
def gq (n j : Nat) : QExpr := qmul (qnat j) (qeps n)

/-- Its last index: `gq n (sqK n) = n + 1`. -/
def sqK (n : Nat) : Nat := 2 ^ n * (n + 1)

theorem gq_nonneg (n j : Nat) : qle qzero (gq n j) := qmul_nonneg (qnat_nonneg j) (qeps_nonneg n)

theorem gq_succ (n j : Nat) : qEq (gq n (j + 1)) (qadd (gq n j) (qeps n)) := by
  unfold gq
  have h := qnat_succ j
  have e : qEq (qmul (qnat (j + 1)) (qeps n)) (qmul (qadd (qnat j) qone) (qeps n)) := qmul_respects h (qEq_refl _)
  have e2 : qEq (qmul (qadd (qnat j) qone) (qeps n)) (qadd (qmul (qnat j) (qeps n)) (qeps n)) := by rat_ring
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gq_zero (n : Nat) : qEq (gq n 0) qzero := by
  unfold gq
  have e : qEq (qmul (qnat 0) (qeps n)) (qmul qzero (qeps n)) := qmul_respects qnat_zero (qEq_refl _)
  have e2 := qzero_mul (qeps n)
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gq_last (n : Nat) : qEq (gq n (sqK n)) (qnat (n + 1)) := by
  unfold gq sqK
  have h1 := qnat_mul (2 ^ n) (n + 1)
  have h2 := qnat_pow2 n
  have m : qEq (qmul (qofInt (pow2 n)) (qeps (0 + n))) (qeps 0) := qpow2_mul_eps n 0
  rw [Nat.zero_add] at m
  have z := qeps_zero
  have e1 : qEq (qmul (qnat (2 ^ n * (n + 1))) (qeps n)) (qmul (qmul (qnat (2 ^ n)) (qnat (n + 1))) (qeps n)) :=
    qmul_respects h1 (qEq_refl _)
  have e2 : qEq (qmul (qmul (qnat (2 ^ n)) (qnat (n + 1))) (qeps n))
      (qmul (qmul (qnat (2 ^ n)) (qeps n)) (qnat (n + 1))) := by rat_ring
  have e3 : qEq (qmul (qmul (qnat (2 ^ n)) (qeps n)) (qnat (n + 1)))
      (qmul (qmul (qofInt (pow2 n)) (qeps n)) (qnat (n + 1))) :=
    qmul_respects (qmul_respects h2 (qEq_refl _)) (qEq_refl _)
  have e4 : qEq (qmul (qmul (qofInt (pow2 n)) (qeps n)) (qnat (n + 1))) (qmul qone (qnat (n + 1))) :=
    qmul_respects (qEq_trans m z) (qEq_refl _)
  have e5 := qone_mul (qnat (n + 1))
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- How many grid points `1..j` have their square `≤ y`. -/
def scnt (y : QExpr) (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      match qle.decidable (sq (gq n (j + 1))) y with
      | .isTrue _ => scnt y n j + 1
      | .isFalse _ => scnt y n j

theorem scnt_true {y : QExpr} {n j : Nat} (h : qle (sq (gq n (j + 1))) y) : scnt y n (j + 1) = scnt y n j + 1 := by
  show (match qle.decidable (sq (gq n (j + 1))) y with
      | .isTrue _ => scnt y n j + 1
      | .isFalse _ => scnt y n j) = scnt y n j + 1
  cases qle.decidable (sq (gq n (j + 1))) y with
  | isTrue _ => rfl
  | isFalse hp => exact absurd h hp

theorem scnt_false {y : QExpr} {n j : Nat} (h : ¬ qle (sq (gq n (j + 1))) y) : scnt y n (j + 1) = scnt y n j := by
  show (match qle.decidable (sq (gq n (j + 1))) y with
      | .isTrue _ => scnt y n j + 1
      | .isFalse _ => scnt y n j) = scnt y n j
  cases qle.decidable (sq (gq n (j + 1))) y with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

/-- `√y` at index `n`: the last grid point whose square is `≤ y`. -/
def rsqrt (y : QExpr) (n : Nat) : QExpr := gq n (scnt y n (sqK n))

theorem rsqrt_nonneg (y : QExpr) (n : Nat) : qle qzero (rsqrt y n) := gq_nonneg _ _

/-- Squares rise along the grid: a point whose square is `≤ y` has every earlier point so. -/
theorem Q_down {y : QExpr} {n : Nat} {i j : Nat} (hij : i ≤ j) (h : qle (sq (gq n j)) y) : qle (sq (gq n i)) y := by
  have hg : qle (gq n i) (gq n j) := ZExp.scale (qnat_mono hij) (qeps_nonneg n)
  exact qle_trans (sq_mono (gq_nonneg n i) hg) h

/-- THE COUNT. Over `1..j`, the true points are an initial run: all up to the count, and the next one false. -/
theorem scnt_spec (y : QExpr) (n : Nat) : ∀ j,
    scnt y n j ≤ j ∧
    (∀ i, 1 ≤ i → i ≤ scnt y n j → qle (sq (gq n i)) y) ∧
    (scnt y n j < j → ¬ qle (sq (gq n (scnt y n j + 1))) y)
  | 0 => ⟨Nat.le_refl 0, fun i h1 h2 => absurd (Nat.le_trans h1 h2) (Nat.not_succ_le_zero 0),
          fun h => absurd h (Nat.lt_irrefl 0)⟩
  | j + 1 => by
      obtain ⟨c1, c2, c3⟩ := scnt_spec y n j
      cases qle.decidable (sq (gq n (j + 1))) y with
      | isTrue hp =>
          rw [scnt_true hp]
          have hc : scnt y n j = j := by
            cases Nat.lt_or_eq_of_le c1 with
            | inl lt => exact absurd (Q_down (Nat.succ_le_succ (Nat.le_of_lt lt)) hp) (c3 lt)
            | inr eq => exact eq
          refine ⟨by rw [hc]; exact Nat.le_refl _, fun i _ hi => Q_down (by rw [hc] at hi; exact hi) hp,
            fun h => absurd (by rw [hc] at h; exact h) (Nat.lt_irrefl (j + 1))⟩
      | isFalse hp =>
          rw [scnt_false hp]
          refine ⟨Nat.le_succ_of_le c1, c2, fun _ => ?_⟩
          cases Nat.lt_or_eq_of_le c1 with
          | inl lt => exact c3 lt
          | inr eq => rw [eq]; exact hp

/-- AT EACH INDEX, THE GRID BRACKETS `√y`: `s² ≤ y` (or the count is `0`, `s = 0`) and `y < (s + ε_n)²`, once
`y < (n + 1)²`. -/
theorem sqrt_bracket {y : QExpr} {n : Nat} (h2 : ¬ qle (sq (qnat (n + 1))) y) :
    (qEq (rsqrt y n) qzero ∨ qle (sq (rsqrt y n)) y) ∧ ¬ qle (sq (qadd (rsqrt y n) (qeps n))) y := by
  obtain ⟨c1, c2, c3⟩ := scnt_spec y n (sqK n)
  have last : ¬ qle (sq (gq n (sqK n))) y := fun h =>
    h2 (qle_respects (sq_respects (gq_last n)) (qEq_refl y) h)
  have Kpos : 0 < sqK n := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) (Nat.succ_pos n)
  have lt : scnt y n (sqK n) < sqK n := by
    cases Nat.lt_or_eq_of_le c1 with
    | inl l => exact l
    | inr e => exact absurd (c2 _ Kpos (Nat.le_of_eq e.symm)) last
  refine ⟨?_, ?_⟩
  · cases Nat.lt_or_eq_of_le (Nat.zero_le (scnt y n (sqK n))) with
    | inl pos => exact Or.inr (c2 _ pos (Nat.le_refl _))
    | inr z =>
        refine Or.inl ?_
        unfold rsqrt; rw [← z]; exact gq_zero n
  · unfold rsqrt
    intro h
    have e := gq_succ n (scnt y n (sqK n))
    exact c3 lt (qle_respects (sq_respects (qEq_symm e)) (qEq_refl y) h)

/-- From some index on, every `y ≤ Y` lies below `(n + 1)²`. -/
theorem sq_big (Y : QExpr) : ∃ N0, ∀ y, qle y Y → ∀ n, N0 ≤ n → ¬ qle (sq (qnat (n + 1))) y := by
  obtain ⟨K, hK⟩ := exists_nat_bound Y
  refine ⟨K + 1, fun y hy n hn h => ?_⟩
  have hK1 : qle Y (qnat K) := by have := hK.1; unfold qsub at this; rat_linarith
  have m1 : qle (qnat (K + 1)) (qnat (n + 1)) := qnat_mono (Nat.le_trans hn (Nat.le_succ n))
  have s1 := qnat_succ K
  have one : qle qone (qnat (n + 1)) := by
    have := qnat_mono (Nat.succ_le_succ (Nat.zero_le n)); have := qnat_succ 0; have := qnat_zero; rat_linarith
  have q : qle (qmul (qnat (n + 1)) qone) (sq (qnat (n + 1))) := scale_l one (qnat_nonneg _)
  have e := qmul_one (qnat (n + 1))
  have p := qone_pos
  have hf : qle qone qzero := by unfold sq at *; rat_linarith
  exact (qlt_iff_le_not_le.mp qone_pos).2 hf

/-! ## The value -/

theorem nat_le_a (k : Nat) : k + k + 1 ≤ k + 1 + (k + 1) + 1 :=
  Nat.add_le_add_right (Nat.add_le_add (Nat.le_succ k) (Nat.le_succ k)) 1

/-- THE VALUE OF `√`. The argument eventually in `[lo, hi]`; the kernel's fork `SL² ≤ lo`, `hi ≤ SH²`, both ends
`≥ 0`: then `√` of it is eventually in `[SL, SH]`, to every precision. -/
theorem Ev_sqrt {y : Nat → QExpr} {lo hi SL SH : QExpr} (hy : Ev y lo hi)
    (hSL : qle qzero SL) (hSL2 : qle (sq SL) lo) (hSH : qle qzero SH) (hSH2 : qle hi (sq SH)) :
    Ev (fun n => rsqrt (y n) n) SL SH := fun k => by
  obtain ⟨N1, h1⟩ := hy (k + 1 + (k + 1) + 1)
  obtain ⟨N0, h0⟩ := sq_big (qadd hi qone)
  refine ⟨N1 + N0 + (k + 1), fun n hn => ?_⟩
  have n1 : N1 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N0) (Nat.le_add_right _ (k + 1))) hn
  have n0 : N0 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N0 N1) (Nat.le_add_right _ (k + 1))) hn
  have nk : k + 1 ≤ n := Nat.le_trans (Nat.le_add_left (k + 1) (N1 + N0)) hn
  obtain ⟨ylo, yhi⟩ := h1 n n1
  have eP1 : qle (qeps (k + 1 + (k + 1) + 1)) (qeps 0) := eps_anti (Nat.zero_le _)
  have z := qeps_zero
  have yb : qle (y n) (qadd hi qone) := by unfold qsub at *; rat_linarith
  obtain ⟨bl, bh⟩ := sqrt_bracket (h0 (y n) yb n n0)
  have s0 := rsqrt_nonneg (y n) n
  have δk : qle (qeps n) (qeps (k + 1)) := eps_anti nk
  have δ0 := qeps_nonneg n
  have ek := qeps_succ_add k
  have pk := qeps_pos (k + k + 1)
  have ekk := qeps_succ_add (k + k)
  have m1 := qeps_mul k k
  have m2 := qeps_mul (k + 1) (k + 1)
  have eA : qle (qeps (k + 1 + (k + 1) + 1)) (qeps (k + k + 1)) := eps_anti (nat_le_a k)
  have eB : qle (qeps (k + 1 + (k + 1) + 1)) (qeps (k + 1 + (k + 1))) := qeps_succ_le _
  refine ⟨?_, ?_⟩
  · -- from below: else (s + ε_n)² ≤ (SL − ε_{k+1})² ≤ SL² − ε_{2k+2} ≤ y
    cases qle_total (qsub SL (qeps k)) (rsqrt (y n) n) with
    | inl h => exact h
    | inr h =>
        have c0 : qle qzero (qsub SL (qeps (k + 1))) := by unfold qsub at *; rat_linarith
        have sc : qle (qadd (rsqrt (y n) n) (qeps n)) (qsub SL (qeps (k + 1))) := by unfold qsub at *; rat_linarith
        have q := sq_mono (by rat_linarith : qle qzero (qadd (rsqrt (y n) n) (qeps n))) sc
        have SLge : qle (qeps (k + 1)) SL := by unfold qsub at c0; rat_linarith
        have f := scale_l SLge (qeps_nonneg (k + 1))
        have ex : qEq (sq (qsub SL (qeps (k + 1))))
            (qadd (qsub (sq SL) (qadd (qmul (qeps (k + 1)) SL) (qmul (qeps (k + 1)) SL))) (qmul (qeps (k + 1)) (qeps (k + 1)))) := by
          unfold sq qsub; rat_ring
        have hf : qle (sq (qadd (rsqrt (y n) n) (qeps n))) (y n) := by unfold qsub at *; rat_linarith
        exact absurd hf bh
  · -- from above: else (SH + ε_k)² ≤ s² ≤ y ≤ SH² + ε_{2k+3}
    cases qle_total (rsqrt (y n) n) (qadd SH (qeps k)) with
    | inl h => exact h
    | inr h =>
        cases bl with
        | inl e0 => exact qle_respects (qEq_symm e0) (qEq_refl _) (by have := qeps_nonneg k; rat_linarith)
        | inr bl =>
            have q := sq_mono (by have := qeps_nonneg k; rat_linarith : qle qzero (qadd SH (qeps k))) h
            have f := qmul_nonneg hSH (qeps_nonneg k)
            have ex : qEq (sq (qadd SH (qeps k)))
                (qadd (qadd (sq SH) (qadd (qmul SH (qeps k)) (qmul SH (qeps k)))) (qmul (qeps k) (qeps k))) := by
              unfold sq; rat_ring
            have hf : qle (qeps (k + k + 1)) qzero := by unfold qsub at *; rat_linarith
            exact absurd hf (qlt_iff_le_not_le.mp pk).2

/-! ## The grid's gap: `y − s²` goes to `0` -/

/-- THE GAP. The argument eventually in `[lo, hi]`, `lo ≥ 0`, `hi ≤ SH²`: then `y − s²` is eventually near `0`
(`s² ≤ y < (s + ε_n)²`, and `s` stays below `SH + 1`). -/
theorem gap_ev {y : Nat → QExpr} {lo hi SH : QExpr} (hy : Ev y lo hi) (hlo : qle qzero lo)
    (hSH : qle qzero SH) (hSH2 : qle hi (sq SH)) :
    Ev (fun n => qsub (y n) (sq (rsqrt (y n) n))) qzero qzero := fun k => by
  obtain ⟨C, hC1, _⟩ := qexpr_bound (qadd (qadd SH SH) (qnat 3))
  have hC : qle (qadd (qadd SH SH) (qnat 3)) (qofInt (pow2 C)) := by unfold qsub at hC1; rat_linarith
  have pc := qpow2_mul_eps C k
  obtain ⟨N1, h1⟩ := hy k
  obtain ⟨N2, h2⟩ := Ev_sqrt hy (qle_refl qzero) (by unfold sq; have := qmul_zero qzero; rat_linarith) hSH hSH2 0
  obtain ⟨N0, h0⟩ := sq_big (qadd hi qone)
  refine ⟨N1 + N2 + N0 + (k + C), fun n hn => ?_⟩
  have n1 : N1 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N0))
    (Nat.le_add_right _ (k + C))) hn
  have n2 : N2 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N0))
    (Nat.le_add_right _ (k + C))) hn
  have n0 : N0 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N0 (N1 + N2)) (Nat.le_add_right _ (k + C))) hn
  have nk : k + C ≤ n := Nat.le_trans (Nat.le_add_left (k + C) (N1 + N2 + N0)) hn
  obtain ⟨ylo, yhi⟩ := h1 n n1
  obtain ⟨_, sh⟩ := h2 n n2
  have z := qeps_zero
  have ek0 : qle (qeps k) (qeps 0) := eps_anti (Nat.zero_le k)
  have yb : qle (y n) (qadd hi qone) := by unfold qsub at *; rat_linarith
  obtain ⟨bl, bh⟩ := sqrt_bracket (h0 (y n) yb n n0)
  have s0 := rsqrt_nonneg (y n) n
  have δ0 := qeps_nonneg n
  have δC : qle (qeps n) (qeps (k + C)) := eps_anti nk
  have δ1 : qle (qeps n) qone := by have := eps_anti (Nat.zero_le n); rat_linarith
  have ek := qeps_nonneg k
  refine ⟨?_, ?_⟩
  · -- from below: s² ≤ y, or s = 0 and y ≥ lo − ε ≥ −ε
    cases bl with
    | inl e0 =>
        have e1 : qEq (sq (rsqrt (y n) n)) qzero := by
          have h1 := sq_respects e0; have h2 := qmul_zero qzero; unfold sq at *; exact qEq_trans h1 h2
        show qle (qsub qzero (qeps k)) (qsub (y n) (sq (rsqrt (y n) n)))
        unfold qsub at *; rat_linarith
    | inr b =>
        show qle (qsub qzero (qeps k)) (qsub (y n) (sq (rsqrt (y n) n)))
        unfold qsub at *; rat_linarith
  · -- from above: y < (s + δ)² = s² + (2s + δ)·δ ≤ s² + (2·SH + 3)·δ ≤ s² + ε_k
    have yl : qle (y n) (sq (qadd (rsqrt (y n) n) (qeps n))) := by
      cases qle_total (y n) (sq (qadd (rsqrt (y n) n) (qeps n))) with
      | inl h => exact h
      | inr h => exact absurd h bh
    have ex : qEq (sq (qadd (rsqrt (y n) n) (qeps n)))
        (qadd (sq (rsqrt (y n) n)) (qmul (qadd (qadd (rsqrt (y n) n) (rsqrt (y n) n)) (qeps n)) (qeps n))) := by
      unfold sq; rat_ring
    have c1 : qle (qadd (qadd (rsqrt (y n) n) (rsqrt (y n) n)) (qeps n)) (qadd (qadd SH SH) (qnat 3)) := by
      have := qnat_succ 2; have := qnat_succ 1; have := qnat_succ 0; have := qnat_zero
      rat_linarith
    have m1 := ZExp.scale c1 δ0
    have m2 := ZExp.scale hC δ0
    have m3 := scale_l δC (qofInt_le (pow2_nonneg C))
    show qle (qsub (y n) (sq (rsqrt (y n) n))) (qadd qzero (qeps k))
    unfold qsub at *; rat_linarith

/-! ## The slope -/

/-- Eventually equal sequences have the same eventual bounds (as `ZSlopeDiv.Ev_congr_ev`). -/
theorem Ev_congr_from {x y : Nat → QExpr} {l h : QExpr} (N0 : Nat) (e : ∀ n, N0 ≤ n → qEq (x n) (y n))
    (hx : Ev x l h) : Ev y l h := fun k => by
  obtain ⟨N, hN⟩ := hx k
  refine ⟨N + N0, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n (Nat.le_trans (Nat.le_add_right N N0) hn)
  have := e n (Nat.le_trans (Nat.le_add_left N0 N) hn)
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- The exact step: `s_b − s_a = (s_b² − s_a²) · 1/(s_a + s_b)`, the sum clear of zero. -/
theorem sqrt_diff {sa sb : QExpr} (hw : ¬ qEq (qadd sa sb) qzero) :
    qEq (qmul (qsub (sq sb) (sq sa)) (qinv' (qadd sa sb))) (qsub sb sa) := by
  have c := qmul_inv'_cancel hw
  have e1 : qEq (qmul (qsub (sq sb) (sq sa)) (qinv' (qadd sa sb)))
      (qmul (qsub sb sa) (qmul (qadd sa sb) (qinv' (qadd sa sb)))) := by unfold sq qsub; rat_ring
  have e2 := qmul_respects (qEq_refl (qsub sb sa)) c
  have e3 := qmul_one (qsub sb sa)
  exact qEq_trans e1 (qEq_trans e2 e3)

/-- THE SLOPE OF `√`, no intermediate point: `a`, `b` eventually in `[lo, hi]` (`lo ≥ 0`, the fork `[SL, SH]`), the
step `b − a` eventually in `[t1, t2]`, the kernel's `2·√U` read in `[w1, w2]` and its reciprocal `[r1, r2]`
(`RecipOK`, so clear of zero), the product at its corners `[m, M]`: then `√b − √a` is eventually in `[m, M]`. -/
theorem Ev_sqrt_slope {a b : Nat → QExpr} {lo hi SL SH w1 w2 r1 r2 t1 t2 m M : QExpr}
    (ha : Ev a lo hi) (hb : Ev b lo hi) (hlo : qle qzero lo)
    (hSL : qle qzero SL) (hSL2 : qle (sq SL) lo) (hSH : qle qzero SH) (hSH2 : qle hi (sq SH))
    (hw1 : qle w1 (qadd SL SL)) (hw2 : qle (qadd SH SH) w2) (hR : RecipOK r1 r2 w1 w2)
    (hΔ : Ev (fun n => qsub (b n) (a n)) t1 t2) (hc : Corners m M t1 t2 r1 r2) :
    Ev (fun n => qsub (rsqrt (b n) n) (rsqrt (a n) n)) m M := by
  have sa := Ev_sqrt ha hSL hSL2 hSH hSH2
  have sb := Ev_sqrt hb hSL hSL2 hSH hSH2
  have W := Ev_widen (Ev_add sa sb) hw1 hw2
  have Wr := Ev_recip W hR
  have ga := gap_ev ha hlo hSH hSH2
  have gb := gap_ev hb hlo hSH hSH2
  have G := Ev_sub gb ga
  have Num := Ev_widen (Ev_sub hΔ G) (l' := t1) (h' := t2)
    (by have := qzero_add qzero; unfold qsub; have := qadd_neg qzero; rat_linarith)
    (by have := qzero_add qzero; unfold qsub; have := qadd_neg qzero; rat_linarith)
  have Q := Ev_mul Num Wr hc
  obtain ⟨J, hJ⟩ := recip_near hR 0
  obtain ⟨N, hN⟩ := W J
  refine Ev_congr_from N (fun n hn => ?_) Q
  obtain ⟨x1, x2⟩ := hN n hn
  obtain ⟨hz, _, _⟩ := hJ _ x1 x2
  have e1 : qEq (qsub (qsub (b n) (a n)) (qsub (qsub (b n) (sq (rsqrt (b n) n))) (qsub (a n) (sq (rsqrt (a n) n)))))
      (qsub (sq (rsqrt (b n) n)) (sq (rsqrt (a n) n))) := by unfold sq qsub; rat_ring
  exact qEq_trans (qmul_respects e1 (qEq_refl _)) (sqrt_diff hz)

/-! ## `√` of an operational real -/

/-- One side of closeness: `s_m − s_n ≥ ε_k` would make `s_m² − s_n² ≥ ε_{2k}`, while it is
`(y_m − y_n) − gap_m + gap_n`, small. -/
theorem sqrt_side {sm sn ym yn e3 : QExpr} {k : Nat} (hsn : qle qzero sn)
    (hy : qle (qsub ym yn) e3) (gm : qle (qsub qzero e3) (qsub ym (sq sm))) (gn : qle (qsub yn (sq sn)) (qadd qzero e3))
    (he : qle (qadd (qadd e3 e3) e3) (qeps (k + k + 1))) : qle (qsub sm sn) (qeps k) := by
  cases qle_total (qsub sm sn) (qeps k) with
  | inl h => exact h
  | inr h =>
      have ge : qle (qadd sn (qeps k)) sm := by unfold qsub at h; rat_linarith
      have q := sq_mono (by have := qeps_nonneg k; rat_linarith : qle qzero (qadd sn (qeps k))) ge
      have f := qmul_nonneg hsn (qeps_nonneg k)
      have ex : qEq (sq (qadd sn (qeps k)))
          (qadd (qadd (sq sn) (qadd (qmul sn (qeps k)) (qmul sn (qeps k)))) (qmul (qeps k) (qeps k))) := by
        unfold sq; rat_ring
      have m1 := qeps_mul k k
      have ekk := qeps_succ_add (k + k)
      have pk := qeps_pos (k + k + 1)
      have hf : qle (qeps (k + k + 1)) qzero := by unfold qsub at *; rat_linarith
      exact absurd hf (qlt_iff_le_not_le.mp pk).2

/-- THE ANSWERS AT TWO INDICES ARE CLOSE: `√` of a Cauchy sequence eventually in `[lo, hi]`, `lo ≥ 0`, is Cauchy. -/
theorem sqrt_cauchy {y : Nat → QExpr} {lo hi : QExpr} (hc : ZRecip.Cauchy y) (hy : Ev y lo hi) (hlo : qle qzero lo) :
    ZRecip.Cauchy (fun n => rsqrt (y n) n) := fun k => by
  obtain ⟨K, hK⟩ := exists_nat_bound hi
  -- SH = K + 1 ≥ 1, so SH² ≥ SH > hi
  have one : qle qone (qadd (qnat K) qone) := by have := qnat_nonneg K; rat_linarith
  have hSH : qle qzero (qadd (qnat K) qone) := by have := qnat_nonneg K; rat_linarith
  have hSH2 : qle hi (sq (qadd (qnat K) qone)) := by
    have q := scale_l one hSH
    have e := qmul_one (qadd (qnat K) qone)
    have := hK.1
    unfold sq qsub at *; rat_linarith
  have g := gap_ev hy hlo hSH hSH2 (k + k + 3)
  obtain ⟨Ng, hg⟩ := g
  obtain ⟨Nc, hcN⟩ := hc (k + k + 3)
  refine ⟨Ng + Nc, fun m n hm hn => ?_⟩
  have gm := hg m (Nat.le_trans (Nat.le_add_right Ng Nc) hm)
  have gn := hg n (Nat.le_trans (Nat.le_add_right Ng Nc) hn)
  have cl := hcN m n (Nat.le_trans (Nat.le_add_left Nc Ng) hm) (Nat.le_trans (Nat.le_add_left Nc Ng) hn)
  -- 3·ε_{2k+3} ≤ ε_{2k+1}
  have a1 := qeps_succ_add (k + k + 1)
  have a2 := qeps_succ_add (k + k + 2)
  have p3 := qeps_nonneg (k + k + 3)
  have he : qle (qadd (qadd (qeps (k + k + 3)) (qeps (k + k + 3))) (qeps (k + k + 3))) (qeps (k + k + 1)) := by
    rat_linarith
  have s1 := sqrt_side (sm := rsqrt (y m) m) (sn := rsqrt (y n) n) (rsqrt_nonneg _ _) cl.1 gm.1 gn.2 he
  have cl2 : qle (qsub (y n) (y m)) (qeps (k + k + 3)) := by have := cl.2; unfold qsub at *; rat_linarith
  have s2 := sqrt_side (sm := rsqrt (y n) n) (sn := rsqrt (y m) m) (rsqrt_nonneg _ _) cl2 gn.1 gm.2 he
  show qclose (rsqrt (y m) m) (rsqrt (y n) n) (qeps k)
  exact ⟨s1, by unfold qsub at *; rat_linarith⟩

end ZSqrt

#print axioms ZSqrt.sq_mono
#print axioms ZSqrt.scnt_spec
#print axioms ZSqrt.sqrt_bracket
#print axioms ZSqrt.sq_big
#print axioms ZSqrt.Ev_sqrt
#print axioms ZSqrt.gap_ev
#print axioms ZSqrt.sqrt_diff
#print axioms ZSqrt.Ev_sqrt_slope
#print axioms ZSqrt.sqrt_side
#print axioms ZSqrt.sqrt_cauchy
