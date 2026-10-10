import ZRecip

/-!
# ZLn — the logarithm on VR's operational reals, as the inverse of `exp`, found on a grid. Zero axioms.

A value of `ln y` cannot be defined by "the `N` that exists" — an existence in `Prop` gives no number to compute
with. So at index `n` the answer is computed: the last point of the grid `−n, −n + 2^−n, …, n` where `E_n ≤ y`
(`lnseq`, a count over the grid — `E_n` is monotone at every index, so the true points form an initial run).
Then `E_n(x_n) ≤ y < E_n(x_n + 2^−n)` exactly (`ln_bracket`), uniformly for `y` in a range clear of zero.

Everything else comes from `exp`'s exact slopes (`ZExp.E_slope`) through one "trap": `E(b) − E(a) ≥ (b − a)·g` on
`[−R, R]` (`E_gap`, `gap_const`), so the grid's answer cannot sit far from where `E` crosses `y`:
  * `Ev_ln` — the value: brackets for `ln` are certified through `exp`'s (`exp(Ll) ≤ lu`, `exp(Lh) ≥ hu`);
  * `Ev_ln_slope` — the slope `ln b − ln a` between `(b − a)/E(Y + ε)` and `(b − a)/(E(X + ε) − t)`, both near
    `1/U` — the kernel's derivative reading `u'/u = Du × [1/U]`;
  * `ln_cauchy` — the answers at two indices are close: `ln` of an operational real.
The functional equation of `exp` is not needed, here either.
-/

namespace ZLn

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip

/-! ## `E_n` respects equality of its argument -/

theorem tm_respects {x x' : QExpr} (h : qEq x x') : ∀ k, qEq (tm x k) (tm x' k)
  | 0 => qEq_refl _
  | k + 1 => qmul_respects (qmul_respects (tm_respects h k) h) (qEq_refl _)

theorem S_respects {x x' : QExpr} (h : qEq x x') : ∀ n, qEq (S x n) (S x' n)
  | 0 => qEq_refl _
  | n + 1 => qadd_respects (S_respects h n) (tm_respects h n)

theorem eseq_respects {x x' : QExpr} (h : qEq x x') (n : Nat) : qEq (eseq x n) (eseq x' n) := by
  cases qle.decidable qzero x with
  | isTrue hx =>
      have hx' : qle qzero x' := qle_respects (qEq_refl _) h hx
      rw [eseq_pos hx, eseq_pos hx']; exact S_respects h n
  | isFalse hx =>
      have hx' : ¬ qle qzero x' := fun h' => hx (qle_respects (qEq_refl _) (qEq_symm h) h')
      rw [eseq_neg hx, eseq_neg hx']
      exact qinv'_respects (S_respects (qneg_respects h) n)

/-- From index 2 on, `S_n(x) ≥ 1 + x` for `x ≥ 0`. -/
theorem S_ge_lin {x : QExpr} (hx : qle qzero x) (n : Nat) : qle (qadd qone x) (S x (n + 2)) := by
  have h := S_mono hx 2 n
  have e1 : qEq (S x 2) (qadd (qadd qzero qone) (tm x 1)) := qEq_refl _
  have e2 := tm_one x
  have e3 := qzero_add qone
  rw [Nat.add_comm] at h
  rat_linarith

/-! ## Natural numbers, powers of two -/

theorem qnat_mul (a : Nat) : ∀ b, qEq (qnat (a * b)) (qmul (qnat a) (qnat b))
  | 0 => by
      show qEq (qnat 0) (qmul (qnat a) (qnat 0))
      have := qnat_zero; have := qmul_zero (qnat a)
      have e : qEq (qmul (qnat a) (qnat 0)) (qmul (qnat a) qzero) := qmul_respects (qEq_refl _) qnat_zero
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | b + 1 => by
      have ih := qnat_mul a b
      have h1 := qnat_add (a * b) a
      have h2 := qnat_succ b
      have e : qEq (qmul (qnat a) (qnat (b + 1))) (qmul (qnat a) (qadd (qnat b) qone)) := qmul_respects (qEq_refl _) h2
      have e2 : qEq (qmul (qnat a) (qadd (qnat b) qone)) (qadd (qmul (qnat a) (qnat b)) (qnat a)) := by rat_ring
      show qEq (qnat (a * b + a)) _
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem qnat_pow2 : ∀ n, qEq (qnat (2 ^ n)) (qofInt (pow2 n))
  | 0 => by
      show qEq (qnat 1) (qofInt (pow2 0))
      have := qnat_succ 0; have := qnat_zero
      have e : qEq (qofInt (pow2 0)) qone := qEq_refl _
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | n + 1 => by
      have ih := qnat_pow2 n
      have h := qnat_mul (2 ^ n) 2
      have h2 : qEq (qnat 2) (qadd qone qone) := by
        have := qnat_succ 1; have := qnat_succ 0; have := qnat_zero
        exact qle_antisymm (by rat_linarith) (by rat_linarith)
      have p : qEq (qofInt (pow2 (n + 1))) (qadd (qofInt (pow2 n)) (qofInt (pow2 n))) :=
        qEq_trans (qofInt_respects (pow2_succ n)) (qofInt_add _ _)
      have e : qEq (qmul (qnat (2 ^ n)) (qnat 2)) (qmul (qnat (2 ^ n)) (qadd qone qone)) := qmul_respects (qEq_refl _) h2
      have e2 : qEq (qmul (qnat (2 ^ n)) (qadd qone qone)) (qadd (qnat (2 ^ n)) (qnat (2 ^ n))) := by rat_ring
      rw [Nat.pow_succ]
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## The grid and the count -/

/-- The `j`-th point of the grid of step `ε_n` from `−n`. -/
def gpt (n j : Nat) : QExpr := qadd (qneg (qnat n)) (qmul (qnat j) (qeps n))

/-- Its last index: `gpt n (gridK n) = n`. -/
def gridK (n : Nat) : Nat := 2 ^ n * (n + n)

theorem gpt_succ (n j : Nat) : qEq (gpt n (j + 1)) (qadd (gpt n j) (qeps n)) := by
  unfold gpt
  have h := qnat_succ j
  have e : qEq (qmul (qnat (j + 1)) (qeps n)) (qmul (qadd (qnat j) qone) (qeps n)) := qmul_respects h (qEq_refl _)
  have e2 : qEq (qmul (qadd (qnat j) qone) (qeps n)) (qadd (qmul (qnat j) (qeps n)) (qeps n)) := by rat_ring
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gpt_zero (n : Nat) : qEq (gpt n 0) (qneg (qnat n)) := by
  unfold gpt
  have e : qEq (qmul (qnat 0) (qeps n)) (qmul qzero (qeps n)) := qmul_respects qnat_zero (qEq_refl _)
  have e2 := qzero_mul (qeps n)
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gpt_last (n : Nat) : qEq (gpt n (gridK n)) (qnat n) := by
  unfold gpt gridK
  have h1 := qnat_mul (2 ^ n) (n + n)
  have h2 := qnat_pow2 n
  have h3 := qnat_add n n
  have m : qEq (qmul (qofInt (pow2 n)) (qeps (0 + n))) (qeps 0) := qpow2_mul_eps n 0
  rw [Nat.zero_add] at m
  have z := qeps_zero
  have e1 : qEq (qmul (qnat (2 ^ n * (n + n))) (qeps n)) (qmul (qmul (qnat (2 ^ n)) (qnat (n + n))) (qeps n)) :=
    qmul_respects h1 (qEq_refl _)
  have e2 : qEq (qmul (qmul (qnat (2 ^ n)) (qnat (n + n))) (qeps n))
      (qmul (qmul (qnat (2 ^ n)) (qeps n)) (qnat (n + n))) := by rat_ring
  have e3 : qEq (qmul (qmul (qnat (2 ^ n)) (qeps n)) (qnat (n + n))) (qmul (qmul (qofInt (pow2 n)) (qeps n)) (qnat (n + n))) :=
    qmul_respects (qmul_respects h2 (qEq_refl _)) (qEq_refl _)
  have e4 : qEq (qmul (qmul (qofInt (pow2 n)) (qeps n)) (qnat (n + n))) (qmul qone (qnat (n + n))) :=
    qmul_respects (qEq_trans m z) (qEq_refl _)
  have e5 := qone_mul (qnat (n + n))
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- How many grid points `1..j` have `E_n ≤ y`. -/
def cnt (y : QExpr) (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      match qle.decidable (eseq (gpt n (j + 1)) n) y with
      | .isTrue _ => cnt y n j + 1
      | .isFalse _ => cnt y n j

/-- One step of the count (by `show`, not `unfold`: `unfold cnt` brought `Quot.sound`, measured 2026-10-10). -/
theorem cnt_true {y : QExpr} {n j : Nat} (h : qle (eseq (gpt n (j + 1)) n) y) : cnt y n (j + 1) = cnt y n j + 1 := by
  show (match qle.decidable (eseq (gpt n (j + 1)) n) y with
      | .isTrue _ => cnt y n j + 1
      | .isFalse _ => cnt y n j) = cnt y n j + 1
  cases qle.decidable (eseq (gpt n (j + 1)) n) y with
  | isTrue _ => rfl
  | isFalse hp => exact absurd h hp

theorem cnt_false {y : QExpr} {n j : Nat} (h : ¬ qle (eseq (gpt n (j + 1)) n) y) : cnt y n (j + 1) = cnt y n j := by
  show (match qle.decidable (eseq (gpt n (j + 1)) n) y with
      | .isTrue _ => cnt y n j + 1
      | .isFalse _ => cnt y n j) = cnt y n j
  cases qle.decidable (eseq (gpt n (j + 1)) n) y with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

/-- `ln y` at index `n`: the last grid point where `E_n ≤ y`. -/
def lnseq (y : QExpr) (n : Nat) : QExpr := gpt n (cnt y n (gridK n))

/-- `E_{n+1}` along the grid is monotone: a point where `E ≤ y` has every earlier point so. -/
theorem P_down {y : QExpr} {n : Nat} {i j : Nat} (hij : i ≤ j) (h : qle (eseq (gpt (n + 1) j) (n + 1)) y) :
    qle (eseq (gpt (n + 1) i) (n + 1)) y := by
  obtain ⟨k, rfl⟩ := le_ex hij
  have hg : qle (gpt (n + 1) i) (gpt (n + 1) (i + k)) := by
    unfold gpt
    have := ZExp.scale (qnat_mono (Nat.le_add_right i k)) (qeps_nonneg (n + 1))
    rat_linarith
  exact qle_trans (E_mono hg n) h

/-- THE COUNT. Over `1..j`, the true points are an initial run: all up to the count, and the next one false. -/
theorem cnt_spec (y : QExpr) (n : Nat) : ∀ j,
    cnt y (n + 1) j ≤ j ∧
    (∀ i, 1 ≤ i → i ≤ cnt y (n + 1) j → qle (eseq (gpt (n + 1) i) (n + 1)) y) ∧
    (cnt y (n + 1) j < j → ¬ qle (eseq (gpt (n + 1) (cnt y (n + 1) j + 1)) (n + 1)) y)
  | 0 => ⟨Nat.le_refl 0, fun i h1 h2 => absurd (Nat.le_trans h1 h2) (Nat.not_succ_le_zero 0),
          fun h => absurd h (Nat.lt_irrefl 0)⟩
  | j + 1 => by
      obtain ⟨c1, c2, c3⟩ := cnt_spec y n j
      cases qle.decidable (eseq (gpt (n + 1) (j + 1)) (n + 1)) y with
      | isTrue hp =>
          rw [cnt_true hp]
          -- every earlier point is true, so the count was j
          have hc : cnt y (n + 1) j = j := by
            cases Nat.lt_or_eq_of_le c1 with
            | inl lt => exact absurd (P_down (Nat.succ_le_succ (Nat.le_of_lt lt)) hp) (c3 lt)
            | inr eq => exact eq
          refine ⟨by rw [hc]; exact Nat.le_refl _, fun i _ hi => P_down (by rw [hc] at hi; exact hi) hp,
            fun h => absurd (by rw [hc] at h; exact h) (Nat.lt_irrefl (j + 1))⟩
      | isFalse hp =>
          rw [cnt_false hp]
          refine ⟨Nat.le_succ_of_le c1, c2, fun _ => ?_⟩
          cases Nat.lt_or_eq_of_le c1 with
          | inl lt => exact c3 lt
          | inr eq => rw [eq]; exact hp

/-- AT EACH INDEX, THE GRID BRACKETS `y`: `E_n(x_n) ≤ y < E_n(x_n + ε_n)`, once `1 ≤ y·(1 + n)` and `y < 1 + n`
(`E_n(−n) ≤ 1/(1+n)`, `E_n(n) ≥ 1 + n`). -/
theorem ln_bracket {y : QExpr} {n : Nat} (h1 : qle qone (qmul y (qadd qone (qnat (n + 2)))))
    (h2 : qlt y (qadd qone (qnat (n + 2)))) :
    qle (eseq (lnseq y (n + 2)) (n + 2)) y ∧ ¬ qle (eseq (qadd (lnseq y (n + 2)) (qeps (n + 2))) (n + 2)) y := by
  obtain ⟨c1, c2, c3⟩ := cnt_spec y (n + 1) (gridK (n + 2))
  have hN : qle qzero (qnat (n + 2)) := qnat_nonneg _
  have lin := S_ge_lin hN n
  -- the last grid point is false: E(n) ≥ 1 + n > y
  have last : ¬ qle (eseq (gpt (n + 2) (gridK (n + 2))) (n + 2)) y := by
    intro h
    have e := eseq_respects (gpt_last (n + 2)) (n + 2)
    rw [eseq_pos hN] at e
    obtain ⟨_, h3⟩ := qlt_iff_le_not_le.mp h2
    exact h3 (by rat_linarith)
  have Kpos : 0 < gridK (n + 2) :=
    Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) (Nat.add_pos_left (Nat.succ_pos _) _)
  have lt : cnt y (n + 2) (gridK (n + 2)) < gridK (n + 2) := by
    cases Nat.lt_or_eq_of_le c1 with
    | inl l => exact l
    | inr e => exact absurd (c2 _ Kpos (Nat.le_of_eq e.symm)) last
  refine ⟨?_, ?_⟩
  · unfold lnseq
    cases Nat.lt_or_eq_of_le (Nat.zero_le (cnt y (n + 2) (gridK (n + 2)))) with
    | inl pos => exact c2 _ pos (Nat.le_refl _)
    | inr z =>
        -- the count is 0: x_n = −n, and E_n(−n) = 1/S_n(n) ≤ 1/(1+n) ≤ y
        rw [← z]
        have e := eseq_respects (gpt_zero (n + 2)) (n + 2)
        have hn : ¬ qle qzero (qneg (qnat (n + 2))) := by
          intro h; have := qnat_succ_pos (n + 1); have q := qlt_iff_le_not_le.mp this
          exact q.2 (by rat_linarith)
        rw [eseq_neg hn] at e
        have nn : qEq (qneg (qneg (qnat (n + 2)))) (qnat (n + 2)) := by rat_ring
        have e2 := qinv'_respects (S_respects nn (n + 2))
        have one : qle qone (S (qnat (n + 2)) (n + 2)) := by have := qle_of_qlt qone_pos; rat_linarith
        obtain ⟨i0, _, ic⟩ := inv_facts one
        -- y·S ≥ y·(1+n) ≥ 1, so 1/S ≤ y
        have hy0 : qle qzero y := by
          cases qle_total qzero y with
          | inl h => exact h
          | inr h =>
              have f := scale_l (by have := qle_of_qlt qone_pos; rat_linarith : qle qzero (qadd qone (qnat (n + 2))))
                (by rat_linarith : qle qzero (qneg y))
              have e3 : qEq (qmul (qneg y) (qadd qone (qnat (n + 2)))) (qneg (qmul y (qadd qone (qnat (n + 2))))) := by
                rat_ring
              have := qle_of_qlt qone_pos
              exact absurd (by rat_linarith : qle qone qzero) (qlt_iff_le_not_le.mp qone_pos).2
        have f1 := scale_l lin hy0
        have f2 := ZExp.scale (qle_trans h1 f1) i0
        have e3 : qEq (qmul (qmul y (S (qnat (n + 2)) (n + 2))) (qinv' (S (qnat (n + 2)) (n + 2))))
            (qmul y (qmul (S (qnat (n + 2)) (n + 2)) (qinv' (S (qnat (n + 2)) (n + 2))))) := by rat_ring
        have e4 := qmul_respects (qEq_refl y) ic
        have e5 := qmul_one y
        have e6 := qone_mul (qinv' (S (qnat (n + 2)) (n + 2)))
        rat_linarith
  · -- the next point is false
    unfold lnseq
    intro h
    have e := eseq_respects (gpt_succ (n + 2) (cnt y (n + 2) (gridK (n + 2)))) (n + 2)
    exact c3 lt (by rat_linarith)

/-! ## Uniform in `y ∈ [ylo, yhi]`, `ylo > 0` -/

theorem ln_bracket_unif {ylo yhi : QExpr} (hlo : qlt qzero ylo) :
    ∃ N0, ∀ y, qle ylo y → qle y yhi → ∀ n, N0 ≤ n →
      qle (eseq (lnseq y (n + 2)) (n + 2)) y ∧ ¬ qle (eseq (qadd (lnseq y (n + 2)) (qeps (n + 2))) (n + 2)) y := by
  obtain ⟨K1, k1a, _⟩ := exists_nat_bound yhi
  obtain ⟨K2, k2a, _⟩ := exists_nat_bound (qinv' ylo)
  unfold qsub at k1a k2a
  refine ⟨K1 + K2, fun y h1 h2 n hn => ln_bracket ?_ ?_⟩
  · have m := qnat_mono (Nat.le_trans (Nat.le_trans (Nat.le_add_left K2 K1) hn) (Nat.le_add_right n 2))
    have c := qmul_inv'_cancel (ne_zero_of_lt hlo)
    have y0 : qle qzero y := qle_trans (qle_of_qlt hlo) h1
    have f1 := scale_l (qle_trans k2a m) (qle_of_qlt hlo)
    have f2 := ZExp.scale h1 (qnat_nonneg (n + 2))
    have f3 : qEq (qmul y (qadd qone (qnat (n + 2)))) (qadd y (qmul y (qnat (n + 2)))) := by rat_ring
    have f4 := qnat_nonneg (n + 2)
    have f5 : qEq (qmul ylo (qnat (n + 2))) (qmul (qnat (n + 2)) ylo) := qmul_comm _ _
    have f6 : qEq (qmul y (qnat (n + 2))) (qmul (qnat (n + 2)) y) := qmul_comm _ _
    rat_linarith
  · have m := qnat_mono (Nat.le_trans (Nat.le_trans (Nat.le_add_right K1 K2) hn) (Nat.le_add_right n 2))
    have o := qone_pos
    exact qlt_iff_le_not_le.mpr ⟨by have := qle_of_qlt o; rat_linarith,
      fun h => (qlt_iff_le_not_le.mp o).2 (by rat_linarith)⟩

/-- `1 ≤ A ≤ B`: `1/B ≤ 1/A`. -/
theorem inv_anti {A B : QExpr} (hA : qle qone A) (hAB : qle A B) : qle (qinv' B) (qinv' A) := by
  have hB := qle_trans hA hAB
  obtain ⟨a0, _, ac⟩ := inv_facts hA
  obtain ⟨b0, _, bc⟩ := inv_facts hB
  have f := ZExp.scale (scale_l hAB a0) b0
  have e1 : qEq (qmul (qmul (qinv' A) A) (qinv' B)) (qmul (qmul A (qinv' A)) (qinv' B)) := by rat_ring
  have e2 : qEq (qmul (qmul (qinv' A) B) (qinv' B)) (qmul (qinv' A) (qmul B (qinv' B))) := by rat_ring
  have e3 := qmul_respects ac (qEq_refl (qinv' B))
  have e4 := qmul_respects (qEq_refl (qinv' A)) bc
  have e5 := qone_mul (qinv' B)
  have e6 := qmul_one (qinv' A)
  rat_linarith

/-- The grid's answer stays in `[−(1/ylo + 1), yhi]`. -/
theorem ln_range {ylo yhi y : QExpr} {n : Nat} (hlo : qlt qzero ylo) (h1 : qle ylo y) (h2 : qle y yhi)
    (hb : qle (eseq (lnseq y (n + 2)) (n + 2)) y ∧ ¬ qle (eseq (qadd (lnseq y (n + 2)) (qeps (n + 2))) (n + 2)) y) :
    qle (qneg (qadd (qinv' ylo) qone)) (lnseq y (n + 2)) ∧ qle (lnseq y (n + 2)) yhi := by
  obtain ⟨b1, b2⟩ := hb
  have y0 : qle qzero y := qle_trans (qle_of_qlt hlo) h1
  have il := qinv'_nonneg_of_pos hlo
  have cl := qmul_inv'_cancel (ne_zero_of_lt hlo)
  have e1 := eps_le_one (n + 2)
  have e0 := qeps_nonneg (n + 2)
  constructor
  · cases qle.decidable qzero (qadd (lnseq y (n + 2)) (qeps (n + 2))) with
    | isTrue hz => rat_linarith
    | isFalse hz =>
        -- E(z) = 1/S(−z) ≤ 1/(1 − z), and y < E(z)
        have nz := neg_nonneg_of_not hz
        have lin := S_ge_lin nz n
        have yz : qle y (eseq (qadd (lnseq y (n + 2)) (qeps (n + 2))) (n + 2)) := by
          cases qle_total y (eseq (qadd (lnseq y (n + 2)) (qeps (n + 2))) (n + 2)) with
          | inl h => exact h
          | inr h => exact absurd h b2
        rw [eseq_neg hz] at yz
        have A1 : qle qone (S (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2)))) (n + 2)) := by rat_linarith
        obtain ⟨i0, _, ic⟩ := inv_facts A1
        -- y·A ≤ 1, A ≥ 1 − z, so ylo·(1 − z) ≤ 1
        have f1 := ZExp.scale yz (qle_trans (qle_of_qlt qone_pos) A1)
        have r1 : qEq (qmul (qinv' (S (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2)))) (n + 2)))
            (S (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2)))) (n + 2)))
            (qmul (S (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2)))) (n + 2))
              (qinv' (S (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2)))) (n + 2)))) := qmul_comm _ _
        have f2 := scale_l lin y0
        have f3 := ZExp.scale h1 (by rat_linarith : qle qzero (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2))))))
        have r2 : qEq (qmul y (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2))))))
            (qmul (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2))))) y) := qmul_comm _ _
        -- multiply ylo·(1 − z) ≤ 1 by 1/ylo
        have g : qle (qmul (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2))))) ylo) qone := by rat_linarith
        have g2 := ZExp.scale g il
        have r3 : qEq (qmul (qmul (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2))))) ylo) (qinv' ylo))
            (qmul (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2))))) (qmul ylo (qinv' ylo))) := by rat_ring
        have r4 := qmul_respects (qEq_refl (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2)))))) cl
        have r5 := qmul_one (qadd qone (qneg (qadd (lnseq y (n + 2)) (qeps (n + 2)))))
        have r6 := qone_mul (qinv' ylo)
        rat_linarith
  · cases qle.decidable qzero (lnseq y (n + 2)) with
    | isTrue hx =>
        have lin := S_ge_lin hx n
        rw [eseq_pos hx] at b1
        rat_linarith
    | isFalse hx =>
        have := neg_nonneg_of_not hx
        have := qle_trans (qle_of_qlt hlo) (qle_trans h1 h2)
        rat_linarith

/-- THE GAP. On `[−R, R]`, `R ≥ 1`, at index `n + 1`: `E(b) − E(a) ≥ (b − a)·(1/S_{n+1}(R) − t_n(R))`. -/
theorem E_gap {a b R : QExpr} (hR : qle qone R) (ha : qclose a qzero R) (hb : qclose b qzero R) (hab : qle a b)
    (n : Nat) :
    qle (qmul (qsub b a) (qsub (qinv' (S R (n + 1))) (tm R n))) (qsub (eseq b (n + 1)) (eseq a (n + 1))) := by
  obtain ⟨l, _⟩ := E_slope hab ha hb n
  obtain ⟨a1, a2⟩ := ha
  unfold qsub at a1 a2
  have nR : ¬ qle qzero (qneg R) := fun h => (qlt_iff_le_not_le.mp qone_pos).2 (by rat_linarith)
  have m := E_mono (by rat_linarith : qle (qneg R) a) n
  rw [eseq_neg nR] at m
  have nn : qEq (qneg (qneg R)) R := by rat_ring
  have e := qinv'_respects (S_respects nn (n + 1))
  have hd : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  have f := scale_l (show qle (qsub (qinv' (S R (n + 1))) (tm R n)) (qsub (eseq a (n + 1)) (tm R n)) by
    unfold qsub; rat_linarith) hd
  exact qle_trans f l

/-! ## The trap: the grid's answer cannot sit far from where `E` crosses `y` -/

theorem qeps_mul (a b : Nat) : qEq (qmul (qeps a) (qeps b)) (qeps (a + b)) := by
  have p1 := qpow2_mul_eps b a
  have p2 : qEq (qmul (qofInt (pow2 b)) (qeps (0 + b))) (qeps 0) := qpow2_mul_eps b 0
  rw [Nat.zero_add] at p2
  have z := qeps_zero
  have e1 : qEq (qmul (qeps (a + b)) (qmul (qofInt (pow2 b)) (qeps b)))
      (qmul (qmul (qofInt (pow2 b)) (qeps (a + b))) (qeps b)) := by rat_ring
  have e2 := qmul_respects (qEq_refl (qeps (a + b))) (qEq_trans p2 z)
  have e3 := qmul_respects p1 (qEq_refl (qeps b))
  have e4 := qmul_one (qeps (a + b))
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The gap's constant: on `[−R, R]`, `R ≥ 1`, eventually `1/S_{n+1}(R) − t_n(R) ≥ ε_C`. -/
theorem gap_const {R : QExpr} (hR : qle qone R) : ∃ C N, ∀ n, N ≤ n →
    qle (qeps C) (qsub (qinv' (S R (n + 1))) (tm R n)) := by
  have hR0 : qle qzero R := qle_trans (qle_of_qlt qone_pos) hR
  obtain ⟨H, hH⟩ := S_bounded hR0
  obtain ⟨C0, hC0, _⟩ := qexpr_bound H
  have hC : qle H (qofInt (pow2 C0)) := by unfold qsub at hC0; rat_linarith
  obtain ⟨K, hg⟩ := good_exists R
  obtain ⟨N, _, hN⟩ := tm_small hR0 hg (C0 + 1)
  refine ⟨C0 + 1, N, fun n hn => ?_⟩
  have s1 := S_ge_one' hR0 (Nat.le_add_left 1 n)
  have sH := hH (n + 1)
  have pinv : qEq (qinv' (qofInt (pow2 C0))) (qeps C0) := by
    have p : qEq (qmul (qofInt (pow2 C0)) (qeps (0 + C0))) (qeps 0) := qpow2_mul_eps C0 0
    rw [Nat.zero_add] at p
    have one := qle_trans s1 (qle_trans sH hC)
    have ne : ¬ qEq (qofInt (pow2 C0)) qzero := fun e => (qlt_iff_le_not_le.mp qone_pos).2 (by rat_linarith)
    exact qEq_symm (ZRecip.inv_unique ne (qEq_trans p qeps_zero))
  have ia := inv_anti s1 (qle_trans sH hC)
  have t := hN n hn
  have t0 := tm_nonneg hR0 n
  have sc := qeps_succ_add C0
  unfold qsub; rat_linarith

/-- THE TRAP. `a + δ ≤ x`, both in `[−R, R]`, `0 ≤ g ≤ 1/S_{n+1}(R) − t_n(R)`: `E(a) + δ·g ≤ E(x)`. -/
theorem trap {a x δ R g : QExpr} {n : Nat} (hR : qle qone R) (ha : qclose a qzero R) (hx : qclose x qzero R)
    (hδ : qle qzero δ) (hg0 : qle qzero g) (hg : qle g (qsub (qinv' (S R (n + 1))) (tm R n)))
    (h : qle (qadd a δ) x) :
    qle (qadd (eseq a (n + 1)) (qmul δ g)) (eseq x (n + 1)) := by
  have hδx : qle δ (qsub x a) := by unfold qsub; rat_linarith
  have hd : qle qzero (qsub x a) := qle_trans hδ hδx
  have gp := E_gap hR ha hx (by unfold qsub at hd; rat_linarith) n
  have f1 := scale_l hg hd
  have f2 := ZExp.scale hδx hg0
  have hs : qEq (qsub (eseq x (n + 1)) (eseq a (n + 1))) (qadd (eseq x (n + 1)) (qneg (eseq a (n + 1)))) := qEq_refl _
  rat_linarith

theorem le7 (a b c d e f g : Nat) :
    a ≤ a + b + c + d + e + f + g ∧ b ≤ a + b + c + d + e + f + g ∧ c ≤ a + b + c + d + e + f + g ∧
    d ≤ a + b + c + d + e + f + g ∧ e ≤ a + b + c + d + e + f + g ∧ f ≤ a + b + c + d + e + f + g ∧
    g ≤ a + b + c + d + e + f + g := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := le6 a b c d e f
  exact ⟨le_add_l g q1, le_add_l g q2, le_add_l g q3, le_add_l g q4, le_add_l g q5, le_add_l g q6,
    Nat.le_add_left g _⟩

theorem eps_anti {a b : Nat} (h : a ≤ b) : qle (qeps b) (qeps a) := by
  obtain ⟨r, rfl⟩ := le_ex h; exact qeps_le_add a r

/-- THE VALUE OF `ln`. The argument eventually in `[lu, hu]`, `lu > 0`; the reading's ends certified through
`exp`'s brackets — `exp(Ll) ≤ wl ≤ lu` and `exp(Lh) ≥ wh ≥ hu`: the grid's answer is eventually in `[Ll, Lh]`. -/
theorem Ev_ln {y : Nat → QExpr} {lu hu Ll Lh zl wl zh wh : QExpr} (hy : Ev y lu hu) (hlo : qlt qzero lu)
    (cl : ExpCert Ll zl wl) (hwl : qle wl lu) (ch : ExpCert Lh wh zh) (hwh : qle hu wh) :
    Ev (fun n => lnseq (y n) n) Ll Lh := fun k => by
  -- a floor for the argument
  have c0 := qmul_inv'_cancel (ne_zero_of_lt hlo)
  obtain ⟨B, hB⟩ := lv_floor hlo (show qle qone (qmul (qinv' lu) lu) by
    have := qmul_comm (qinv' lu) lu; rat_linarith)
  have sB := qeps_succ_add B
  have pB := qeps_pos (B + 1)
  obtain ⟨Na, hNa⟩ := hy (B + 1)
  -- the range [ylo, yhi] = [ε_{B+1}, hu + 1]
  have ylo0 : qlt qzero (qeps (B + 1)) := pB
  obtain ⟨N0, hN0⟩ := ln_bracket_unif (yhi := qadd hu qone) ylo0
  obtain ⟨M, _, hM0, _, m1, m2, m3, m4⟩ := bound4 (qadd (qinv' (qeps (B + 1))) qone) (qadd hu qone) Ll Lh
  have hR : qle qone (qadd M qone) := by rat_linarith
  obtain ⟨C, Ng, hgC⟩ := gap_const hR
  have bl := (bracket_sound cl).2
  have bh := (bracket_sound ch).1
  obtain ⟨Nl, hNl⟩ := bl ((k + 1) + C + 2)
  obtain ⟨Nh, hNh⟩ := bh ((k + 1) + C + 2)
  obtain ⟨Ny, hNy⟩ := hy ((k + 1) + C + 2)
  refine ⟨N0 + Na + Ny + Nl + Nh + Ng + k + 2, fun n hn => ?_⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := le7 N0 Na Ny Nl Nh Ng k
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n1 =>
        cases n1 with
        | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
        | succ m => exact ⟨m, rfl⟩
  have hm : N0 + Na + Ny + Nl + Nh + Ng + k ≤ m := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hn)
  have up2 : ∀ X, X ≤ N0 + Na + Ny + Nl + Nh + Ng + k → X ≤ m + 2 :=
    fun X h => Nat.le_trans (Nat.le_trans h hm) (Nat.le_add_right m 2)
  obtain ⟨ya, yb⟩ := hNa (m + 2) (up2 Na q2)
  obtain ⟨yc, yd⟩ := hNy (m + 2) (up2 Ny q3)
  have gl : qle (qsub (eseq Ll (m + 2)) wl) (qeps ((k + 1) + C + 2)) := hNl (m + 2) (up2 Nl q4)
  have gh : qle (qsub wh (eseq Lh (m + 2))) (qeps ((k + 1) + C + 2)) := hNh (m + 2) (up2 Nh q5)
  have gC := hgC (m + 1) (Nat.le_trans (Nat.le_trans q6 hm) (Nat.le_add_right m 1))
  have e1 := eps_le_one (B + 1)
  have yl : qle (qeps (B + 1)) (y (m + 2)) := by unfold qsub at ya; rat_linarith
  have yh : qle (y (m + 2)) (qadd hu qone) := by rat_linarith
  obtain ⟨b1, b2⟩ := hN0 (y (m + 2)) yl yh m (Nat.le_trans q1 hm)
  obtain ⟨r1, r2⟩ := ln_range ylo0 yl yh ⟨b1, b2⟩
  obtain ⟨u1, u2⟩ := m1
  obtain ⟨v1, v2⟩ := m2
  obtain ⟨w1, w2⟩ := m3
  obtain ⟨x1, x2⟩ := m4
  unfold qsub at u1 u2 v1 v2 w1 w2 x1 x2
  have en := eps_le_one (m + 2)
  have en0 := qeps_nonneg (m + 2)
  have ed := eps_anti (Nat.le_trans (Nat.succ_le_succ (Nat.le_trans q7 hm)) (Nat.le_succ (m + 1)) :
    k + 1 ≤ m + 2)
  have d0 := qeps_nonneg (k + 1)
  have d1 := eps_le_one (k + 1)
  have dk := qeps_succ_add k
  have gC0 := qle_of_qlt (qeps_pos C)
  -- δ·ε_C = ε_{(k+1)+C} = 4·ε'
  have pm := qeps_mul (k + 1) C
  have s1 := qeps_succ_add ((k + 1) + C)
  have s2 := qeps_succ_add ((k + 1) + C + 1)
  have ep := qeps_pos ((k + 1) + C + 2)
  have ep0 := qle_of_qlt ep
  have xR : qclose (lnseq (y (m + 2)) (m + 2)) qzero (qadd M qone) := by constructor <;> (unfold qsub; rat_linarith)
  show qle (qsub Ll (qeps k)) (lnseq (y (m + 2)) (m + 2)) ∧ qle (lnseq (y (m + 2)) (m + 2)) (qadd Lh (qeps k))
  constructor
  · cases qle_total (qadd (qadd (lnseq (y (m + 2)) (m + 2)) (qeps (m + 2))) (qeps (k + 1))) Ll with
    | inl hA =>
        have aR : qclose (qadd (lnseq (y (m + 2)) (m + 2)) (qeps (m + 2))) qzero (qadd M qone) := by
          constructor <;> (unfold qsub; rat_linarith)
        have LR : qclose Ll qzero (qadd M qone) := by constructor <;> (unfold qsub; rat_linarith)
        have t := trap hR aR LR d0 gC0 gC hA
        exact absurd (by unfold qsub at *; rat_linarith) b2
    | inr hB' => unfold qsub; rat_linarith
  · cases qle_total (qadd Lh (qeps (k + 1))) (lnseq (y (m + 2)) (m + 2)) with
    | inl hA =>
        have LR : qclose Lh qzero (qadd M qone) := by constructor <;> (unfold qsub; rat_linarith)
        have t := trap hR LR xR d0 gC0 gC hA
        exact absurd (by unfold qsub at *; rat_linarith : qle (qeps ((k + 1) + C + 2)) qzero)
          (qlt_iff_le_not_le.mp ep).2
    | inr hB' => rat_linarith

/-! ## The slope of `ln`: `(b − a)/E(Y+ε) ≤ Y − X + ε`, `Y − X ≤ (b − a)/(E(X+ε) − t) + ε` -/

/-- At one index: the grid's answers `X` (for `a`) and `Y` (for `b ≥ a`), both bracketed, inside `[−R, R]`. -/
theorem ln_sigma_pt {X Y a b R g : QExpr} {n : Nat} (hR : qle qone R)
    (hX : qclose X qzero R) (hY : qclose Y qzero R) (hXe : qclose (qadd X (qeps (n + 1))) qzero R)
    (hYe : qclose (qadd Y (qeps (n + 1))) qzero R)
    (bX1 : qle (eseq X (n + 1)) a) (bX2 : qle a (eseq (qadd X (qeps (n + 1))) (n + 1)))
    (bY1 : qle (eseq Y (n + 1)) b) (bY2 : qle b (eseq (qadd Y (qeps (n + 1))) (n + 1)))
    (hab : qle a b) (hb0 : qlt qzero b) (hg : qlt qzero g) (hgS : qle g (qsub (qinv' (S R (n + 1))) (tm R n)))
    (hD : qlt qzero (qsub (eseq (qadd X (qeps (n + 1))) (n + 1)) (tm R n))) :
    qle (qmul (qsub b a) (qinv' (eseq (qadd Y (qeps (n + 1))) (n + 1)))) (qadd (qsub Y X) (qeps (n + 1))) ∧
    qle (qsub Y X) (qadd (qmul (qsub b a) (qinv' (qsub (eseq (qadd X (qeps (n + 1))) (n + 1)) (tm R n))))
      (qeps (n + 1))) := by
  have e0 := qeps_nonneg (n + 1)
  have hd : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  have g0 := qle_of_qlt hg
  constructor
  · -- X ≤ Y + ε, by the gap
    have XY : qle X (qadd Y (qeps (n + 1))) := by
      cases qle_total X (qadd Y (qeps (n + 1))) with
      | inl h => exact h
      | inr h =>
          have gp := E_gap hR hYe hX h n
          have pos : qlt qzero (qsub (qinv' (S R (n + 1))) (tm R n)) := qlt_iff_le_not_le.mpr
            ⟨qle_trans g0 hgS, fun h' => (qlt_iff_le_not_le.mp hg).2 (qle_trans hgS h')⟩
          have c : qEq (qmul (qsub (qinv' (S R (n + 1))) (tm R n)) (qsub X (qadd Y (qeps (n + 1)))))
              (qmul (qsub X (qadd Y (qeps (n + 1)))) (qsub (qinv' (S R (n + 1))) (tm R n))) := qmul_comm _ _
          have hs : qEq (qsub (eseq X (n + 1)) (eseq (qadd Y (qeps (n + 1))) (n + 1)))
              (qadd (eseq X (n + 1)) (qneg (eseq (qadd Y (qeps (n + 1))) (n + 1)))) := qEq_refl _
          have np := nonpos_of_mul (y := qsub X (qadd Y (qeps (n + 1)))) pos (by rat_linarith)
          unfold qsub at np; rat_linarith
    obtain ⟨_, u⟩ := E_slope XY hX hYe n
    have Epos : qlt qzero (eseq (qadd Y (qeps (n + 1))) (n + 1)) := qlt_iff_le_not_le.mpr
      ⟨qle_trans (qle_of_qlt hb0) bY2, fun h => (qlt_iff_le_not_le.mp hb0).2 (qle_trans bY2 h)⟩
    have i0 := qinv'_nonneg_of_pos Epos
    have c := qmul_inv'_cancel (ne_zero_of_lt Epos)
    have f1 : qle (qsub b a) (qmul (qsub (qadd Y (qeps (n + 1))) X) (eseq (qadd Y (qeps (n + 1))) (n + 1))) := by
      unfold qsub at u ⊢; rat_linarith
    have f2 := ZExp.scale f1 i0
    have r1 : qEq (qmul (qmul (qsub (qadd Y (qeps (n + 1))) X) (eseq (qadd Y (qeps (n + 1))) (n + 1)))
        (qinv' (eseq (qadd Y (qeps (n + 1))) (n + 1))))
        (qmul (qsub (qadd Y (qeps (n + 1))) X) (qmul (eseq (qadd Y (qeps (n + 1))) (n + 1))
          (qinv' (eseq (qadd Y (qeps (n + 1))) (n + 1))))) := by rat_ring
    have r2 := qmul_respects (qEq_refl (qsub (qadd Y (qeps (n + 1))) X)) c
    have r3 := qmul_one (qsub (qadd Y (qeps (n + 1))) X)
    unfold qsub at *; rat_linarith
  · have iD0 := qinv'_nonneg_of_pos hD
    have cD := qmul_inv'_cancel (ne_zero_of_lt hD)
    have p0 := qmul_nonneg hd iD0
    cases qle_total (qadd X (qeps (n + 1))) Y with
    | inr h => unfold qsub at *; rat_linarith
    | inl h =>
        obtain ⟨l, _⟩ := E_slope h hXe hY n
        have f1 : qle (qmul (qsub Y (qadd X (qeps (n + 1)))) (qsub (eseq (qadd X (qeps (n + 1))) (n + 1)) (tm R n)))
            (qsub b a) := by unfold qsub at l ⊢; rat_linarith
        have f2 := ZExp.scale f1 iD0
        have r1 : qEq (qmul (qmul (qsub Y (qadd X (qeps (n + 1)))) (qsub (eseq (qadd X (qeps (n + 1))) (n + 1)) (tm R n)))
            (qinv' (qsub (eseq (qadd X (qeps (n + 1))) (n + 1)) (tm R n))))
            (qmul (qsub Y (qadd X (qeps (n + 1)))) (qmul (qsub (eseq (qadd X (qeps (n + 1))) (n + 1)) (tm R n))
              (qinv' (qsub (eseq (qadd X (qeps (n + 1))) (n + 1)) (tm R n))))) := by rat_ring
        have r2 := qmul_respects (qEq_refl (qsub Y (qadd X (qeps (n + 1))))) cD
        have r3 := qmul_one (qsub Y (qadd X (qeps (n + 1))))
        unfold qsub at *; rat_linarith


/-- The last arithmetic of the slope, in a small context (in the big one `rat_linarith` ran out of time). -/
theorem combine {D Δ σ1 σ2 m M eK εn ek1 ek : QExpr} (L : qle (qmul Δ σ1) (qadd D εn))
    (U : qle D (qadd (qmul Δ σ2) εn)) (p1 : qle (qsub m eK) (qmul σ1 Δ)) (p2 : qle (qmul σ2 Δ) (qadd M eK))
    (es : qle eK ek1) (en : qle εn ek1) (dk : qEq (qadd ek1 ek1) ek) :
    qle (qsub m ek) D ∧ qle D (qadd M ek) := by
  have c1 := qmul_comm Δ σ1
  have c2 := qmul_comm Δ σ2
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem flip_up {X Y a b σ e : QExpr} (h : qle (qmul (qsub a b) σ) (qadd (qsub X Y) e)) :
    qle (qsub Y X) (qadd (qmul (qsub b a) σ) e) := by
  have r1 : qEq (qmul (qsub b a) σ) (qneg (qmul (qsub a b) σ)) := by unfold qsub; rat_ring
  have r2 : qEq (qsub Y X) (qneg (qsub X Y)) := by unfold qsub; rat_ring
  rat_linarith

theorem flip_dn {X Y a b σ e : QExpr} (h : qle (qsub X Y) (qadd (qmul (qsub a b) σ) e)) :
    qle (qmul (qsub b a) σ) (qadd (qsub Y X) e) := by
  have r1 : qEq (qmul (qsub b a) σ) (qneg (qmul (qsub a b) σ)) := by unfold qsub; rat_ring
  have r2 : qEq (qsub Y X) (qneg (qsub X Y)) := by unfold qsub; rat_ring
  rat_linarith


/-- Small-context arithmetic for the slope's denominators (`rat_linarith` gave up in a 70-hypothesis context). -/
theorem near_up {EXe EX a hu e1 eJ1 eJ t : QExpr} (la : qle (qsub EXe EX) e1) (c1 : qle e1 eJ1)
    (xa : qle EX a) (a4 : qle a (qadd hu eJ1)) (sJ : qEq (qadd eJ1 eJ1) eJ) (t0 : qle qzero t) :
    qle EXe (qadd hu eJ) ∧ qle (qsub EXe t) (qadd hu eJ) := by
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem chain3 {x y z w v : QExpr} (h1 : qle x y) (h2 : qle y z) (h3 : qEq z w) (h4 : qEq w v) : qle x v :=
  qle_trans (qle_trans h1 h2) (qle_of_qEq (qEq_trans h3 h4))

theorem near_lo {EXe a lu t eJ1 eJ eB1 eB : QExpr} (xa : qle a EXe) (a3 : qle (qsub lu eJ1) a)
    (tt : qle (qadd t t) eJ1) (t0 : qle qzero t) (sJ : qEq (qadd eJ1 eJ1) eJ) (hB : qle eB lu)
    (sB : qEq (qadd eB1 eB1) eB) (eJB : qle eJ eB1) (pB : qlt qzero eB1) :
    qle (qsub lu eJ) EXe ∧ qle (qsub lu eJ) (qsub EXe t) ∧ qlt qzero (qsub EXe t) := by
  obtain ⟨p, np⟩ := qlt_iff_le_not_le.mp pB
  clear pB
  unfold qsub at *
  have g1 : qle (qadd lu (qneg eJ)) EXe := by rat_linarith
  have g2 : qle (qadd lu (qneg eJ)) (qadd EXe (qneg t)) := by rat_linarith
  have g3 : qle eB1 (qadd EXe (qneg t)) := by rat_linarith
  refine ⟨g1, g2, qlt_iff_le_not_le.mpr ⟨qle_trans p g3, fun h => np (qle_trans g3 h)⟩⟩

/-- THE SLOPE OF `ln`. The arguments at two points eventually in `[lu, hu]`, `lu > 0`, the kernel's reciprocal
reading `[Li, Hi]` of `1/U`, the arguments' difference eventually in `[t1, t2]`, the corners of
`[Li, Hi] × [t1, t2]` between `m` and `M`: the difference of the logarithms is eventually in `[m, M]`. -/
theorem Ev_ln_slope {a b : Nat → QExpr} {lu hu Li Hi t1 t2 m M : QExpr}
    (ha : Ev a lu hu) (hb : Ev b lu hu) (hlo : qlt qzero lu) (hR : RecipOK Li Hi lu hu)
    (hΔ : Ev (fun n => qsub (b n) (a n)) t1 t2) (hc : Corners m M Li Hi t1 t2) :
    Ev (fun n => qsub (lnseq (b n) n) (lnseq (a n) n)) m M := fun k => by
  obtain ⟨Mc, Bc, hMc0, hMcB, c1, c2, c3, c4⟩ := bound4 Li Hi t1 t2
  obtain ⟨J, hJ⟩ := recip_near hR ((k + 1) + (Bc + 2))
  have c0 := qmul_inv'_cancel (ne_zero_of_lt hlo)
  obtain ⟨B, hB⟩ := lv_floor hlo (show qle qone (qmul (qinv' lu) lu) by
    have := qmul_comm (qinv' lu) lu; rat_linarith)
  obtain ⟨J', hJ'⟩ : ∃ J', J' = J + (B + 1) := ⟨_, rfl⟩
  have ylo0 : qlt qzero (qeps (B + 1)) := qeps_pos (B + 1)
  obtain ⟨N0, hN0⟩ := ln_bracket_unif (yhi := qadd hu qone) ylo0
  obtain ⟨Mr, _, hMr0, _, r1, r2, _, _⟩ := bound4 (qadd (qinv' (qeps (B + 1))) qone) (qadd hu qone) qzero qzero
  have hR1 : qle qone (qadd (qadd Mr qone) qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have hR0 : qle qzero (qadd (qadd Mr qone) qone) := qle_trans (qle_of_qlt qone_pos) hR1
  obtain ⟨C, Ng, hgC⟩ := gap_const hR1
  obtain ⟨H, hH⟩ := S_bounded hR0
  obtain ⟨CH, hCH0, _⟩ := qexpr_bound H
  have hCH : qle H (qofInt (pow2 CH)) := by unfold qsub at hCH0; rat_linarith
  obtain ⟨K, hgK⟩ := good_exists (qadd (qadd Mr qone) qone)
  obtain ⟨Nt, _, hNt⟩ := tm_small hR0 hgK (J' + 1)
  obtain ⟨Na1, hNa1⟩ := ha (B + 1)
  obtain ⟨Nb1, hNb1⟩ := hb (B + 1)
  obtain ⟨Na2, hNa2⟩ := ha (J' + 1)
  obtain ⟨Nb2, hNb2⟩ := hb (J' + 1)
  obtain ⟨Nd, hNd⟩ := hΔ ((k + 1) + (Bc + 2))
  refine ⟨(N0 + Na1 + Nb1 + Na2 + Nb2 + Nd + Ng) + Nt + k + ((J' + 1) + CH) + 2, fun n hn => ?_⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := le7 N0 Na1 Nb1 Na2 Nb2 Nd Ng
  obtain ⟨m', rfl⟩ : ∃ m', n = m' + 2 := by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n1 =>
        cases n1 with
        | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
        | succ m' => exact ⟨m', rfl⟩
  show qle (qsub m (qeps k)) (qsub (lnseq (b (m' + 2)) (m' + 2)) (lnseq (a (m' + 2)) (m' + 2))) ∧
    qle (qsub (lnseq (b (m' + 2)) (m' + 2)) (lnseq (a (m' + 2)) (m' + 2))) (qadd M (qeps k))
  have hm : (N0 + Na1 + Nb1 + Na2 + Nb2 + Nd + Ng) + Nt + k + ((J' + 1) + CH) ≤ m' :=
    Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hn)
  have S7 : N0 + Na1 + Nb1 + Na2 + Nb2 + Nd + Ng ≤ m' :=
    Nat.le_trans (le_add_l _ (le_add_l _ (le_add_l _ (Nat.le_refl _)))) hm
  have qNt : Nt ≤ m' := Nat.le_trans (le_add_l _ (le_add_l _ (Nat.le_add_left Nt _))) hm
  have qk : k ≤ m' := Nat.le_trans (le_add_l _ (Nat.le_add_left k _)) hm
  have qT : (J' + 1) + CH ≤ m' := Nat.le_trans (Nat.le_add_left _ _) hm
  have up : ∀ X, X ≤ N0 + Na1 + Nb1 + Na2 + Nb2 + Nd + Ng → X ≤ m' + 2 :=
    fun X h => Nat.le_trans (Nat.le_trans h S7) (Nat.le_add_right m' 2)
  -- the arguments
  obtain ⟨a1, a2⟩ := hNa1 (m' + 2) (up _ q2)
  obtain ⟨b1, b2⟩ := hNb1 (m' + 2) (up _ q3)
  obtain ⟨a3, a4⟩ := hNa2 (m' + 2) (up _ q4)
  obtain ⟨b3, b4⟩ := hNb2 (m' + 2) (up _ q5)
  obtain ⟨d1, d2⟩ := hNd (m' + 2) (up _ q6)
  have gC := hgC (m' + 1) (Nat.le_trans (Nat.le_trans q7 S7) (Nat.le_add_right m' 1))
  have tt := hNt (m' + 1) (Nat.le_trans qNt (Nat.le_add_right m' 1))
  have e1 := eps_le_one (B + 1)
  have sB := qeps_succ_add B
  have sJ := qeps_succ_add J'
  have eJB : qle (qeps J') (qeps (B + 1)) := by
    rw [hJ']; have := qeps_le_add (B + 1) J; rw [Nat.add_comm (B + 1) J] at this; exact this
  have pJ := qeps_pos (J' + 1)
  have pJ0 := qle_of_qlt pJ
  have ya : qle (qeps (B + 1)) (a (m' + 2)) := by unfold qsub at a1; rat_linarith
  have yb : qle (qeps (B + 1)) (b (m' + 2)) := by unfold qsub at b1; rat_linarith
  have yah : qle (a (m' + 2)) (qadd hu qone) := by rat_linarith
  have ybh : qle (b (m' + 2)) (qadd hu qone) := by rat_linarith
  obtain ⟨xa1, xa2⟩ := hN0 (a (m' + 2)) ya yah m' (Nat.le_trans q1 S7)
  obtain ⟨xb1, xb2⟩ := hN0 (b (m' + 2)) yb ybh m' (Nat.le_trans q1 S7)
  obtain ⟨ra1, ra2⟩ := ln_range ylo0 ya yah ⟨xa1, xa2⟩
  obtain ⟨rb1, rb2⟩ := ln_range ylo0 yb ybh ⟨xb1, xb2⟩
  generalize lnseq (a (m' + 2)) (m' + 2) = X at xa1 xa2 ra1 ra2 ⊢
  generalize lnseq (b (m' + 2)) (m' + 2) = Y at xb1 xb2 rb1 rb2 ⊢
  obtain ⟨u1, u2⟩ := r1
  obtain ⟨v1, v2⟩ := r2
  unfold qsub at u1 u2 v1 v2
  have en0 := qeps_nonneg (m' + 2)
  have en1 := eps_le_one (m' + 2)
  have o1 := qle_of_qlt qone_pos
  have XR : qclose X qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have YR : qclose Y qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have XeR : qclose (qadd X (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have YeR : qclose (qadd Y (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  -- the brackets, as non-strict inequalities
  have xa2' : qle (a (m' + 2)) (eseq (qadd X (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total (a (m' + 2)) (eseq (qadd X (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h xa2
  have xb2' : qle (b (m' + 2)) (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total (b (m' + 2)) (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h xb2
  -- E(·+ε) is within ε_{J'+1} above E(·): Lipschitz, ε_n·S_R ≤ ε_n·2^CH ≤ ε_{J'+1}
  have cl : qclose (qadd X (qeps (m' + 2))) X (qeps (m' + 2)) := by
    constructor <;> (unfold qsub; rat_linarith)
  have clb : qclose (qadd Y (qeps (m' + 2))) Y (qeps (m' + 2)) := by
    constructor <;> (unfold qsub; rat_linarith)
  obtain ⟨la0, _⟩ := E_lip XeR XR cl (m' + 1)
  obtain ⟨lb0, _⟩ := E_lip YeR YR clb (m' + 1)
  have la : qle (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (eseq X (m' + 2)))
      (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) := la0
  have lb : qle (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (eseq Y (m' + 2)))
      (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) := lb0
  have hS := hH (m' + 2)
  have w1 := scale_l (qle_trans hS hCH) en0
  have w2 := scale_l hS en0
  have w3 := ZExp.scale (eps_anti (Nat.le_trans qT (Nat.le_add_right m' 2))) (qofInt_le (pow2_nonneg CH))
  have w4 := qpow2_mul_eps CH (J' + 1)
  have w5 : qEq (qmul (qeps (m' + 2)) (qofInt (pow2 CH))) (qmul (qofInt (pow2 CH)) (qeps (m' + 2))) := qmul_comm _ _
  have w6 : qEq (qmul (qeps ((J' + 1) + CH)) (qofInt (pow2 CH))) (qmul (qofInt (pow2 CH)) (qeps ((J' + 1) + CH))) :=
    qmul_comm _ _
  have t0 := tm_nonneg hR0 (m' + 1)
  -- the four slopes' denominators lie within ε_{J'} of [lu, hu]
  have eJ : qle (qeps J') (qeps J) := by rw [hJ']; exact eps_anti (Nat.le_add_right J (B + 1))
  have near : ∀ x, qle (qsub lu (qeps J')) x → qle x (qadd hu (qeps J')) →
      ¬ qEq x qzero ∧ qle (qsub Li (qeps ((k + 1) + (Bc + 2)))) (qinv' x) ∧ qle (qinv' x) (qadd Hi (qeps ((k + 1) + (Bc + 2)))) :=
    fun x h1 h2 => hJ x (by unfold qsub at *; rat_linarith) (by rat_linarith)
  have cX : qle (qmul (qeps (m' + 2)) (S (qadd (qadd Mr qone) qone) (m' + 2))) (qeps (J' + 1)) :=
    chain3 w1 w3 w6 w4
  obtain ⟨uX1, uX2⟩ := near_up la cX xa1 a4 sJ t0
  obtain ⟨uY1, uY2⟩ := near_up lb cX xb1 b4 sJ t0
  have ttX : qle (qadd (tm (qadd (qadd Mr qone) qone) (m' + 1)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) (qeps (J' + 1)) := tt
  obtain ⟨lX1, lX2, hDX⟩ := near_lo xa2' a3 ttX t0 sJ hB sB eJB ylo0
  obtain ⟨lY1, lY2, hDY⟩ := near_lo xb2' b3 ttX t0 sJ hB sB eJB ylo0
  obtain ⟨_, sXa, sXb⟩ := near (eseq (qadd X (qeps (m' + 2))) (m' + 2)) lX1 uX1
  obtain ⟨_, sYa, sYb⟩ := near (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) lY1 uY1
  obtain ⟨_, tXa, tXb⟩ := near (qsub (eseq (qadd X (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) lX2 uX2
  obtain ⟨_, tYa, tYb⟩ := near (qsub (eseq (qadd Y (qeps (m' + 2))) (m' + 2)) (tm (qadd (qadd Mr qone) qone) (m' + 1))) lY2 uY2
  have pa : qlt qzero (a (m' + 2)) := qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => (qlt_iff_le_not_le.mp ylo0).2 (by rat_linarith)⟩
  have pb : qlt qzero (b (m' + 2)) := qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => (qlt_iff_le_not_le.mp ylo0).2 (by rat_linarith)⟩
  have gpos := qeps_pos C
  have he := qeps_nonneg ((k + 1) + (Bc + 2))
  have he1 := eps_le_one ((k + 1) + (Bc + 2))
  have es := eps_scale hMc0 hMcB (k + 1)
  have ek := eps_anti (Nat.le_trans (Nat.succ_le_succ qk) (Nat.le_succ (m' + 1)) : k + 1 ≤ m' + 2)
  have dk := qeps_succ_add k
  have AC : ∀ σ : QExpr, qle (qsub Li (qeps ((k + 1) + (Bc + 2)))) σ → qle σ (qadd Hi (qeps ((k + 1) + (Bc + 2)))) →
      qle (qsub m (qmul (qeps ((k + 1) + (Bc + 2))) (qadd (qadd Mc Mc) qone))) (qmul σ (qsub (b (m' + 2)) (a (m' + 2)))) ∧
      qle (qmul σ (qsub (b (m' + 2)) (a (m' + 2)))) (qadd M (qmul (qeps ((k + 1) + (Bc + 2))) (qadd (qadd Mc Mc) qone))) :=
    fun σ h1 h2 => approx_corner hc c1 c2 c3 c4 he he1 h1 h2 d1 d2
  cases qle_total (a (m' + 2)) (b (m' + 2)) with
  | inl hab =>
      obtain ⟨L0, U0⟩ := ln_sigma_pt (n := m' + 1) hR1 XR YR XeR YeR xa1 xa2' xb1 xb2' hab pb gpos gC hDX
      rw [show m' + 1 + 1 = m' + 2 from rfl] at L0 U0
      obtain ⟨p1, _⟩ := AC _ sYa sYb
      obtain ⟨_, p2⟩ := AC _ tXa tXb
      exact combine L0 U0 p1 p2 es ek dk
  | inr hba =>
      obtain ⟨L0, U0⟩ := ln_sigma_pt (n := m' + 1) hR1 YR XR YeR XeR xb1 xb2' xa1 xa2' hba pa gpos gC hDY
      rw [show m' + 1 + 1 = m' + 2 from rfl] at L0 U0
      obtain ⟨p1, _⟩ := AC _ tYa tYb
      obtain ⟨_, p2⟩ := AC _ sXa sXb
      exact combine (flip_dn U0) (flip_up L0) p1 p2 es ek dk

/-! ## `ln` of an operational real: the answers at two indices are close -/

/-- One side: at indices `m + 2` and `n + 2`, `X_m` cannot sit above `X_n + ε + Δ` once `E` and `y` agree there to
within `δ` and `Δ·g > 2δ`. -/
theorem ln_side {Xm Xn ym yn R g Δ δ : QExpr} {m n : Nat} (hR : qle qone R)
    (hXn : qclose (qadd Xn (qeps (n + 2))) qzero R) (hXm : qclose Xm qzero R)
    (hg0 : qle qzero g) (hg : qle g (qsub (qinv' (S R (m + 1 + 1))) (tm R (m + 1))))
    (bm : qle (eseq Xm (m + 2)) ym) (bn : qle yn (eseq (qadd Xn (qeps (n + 2))) (n + 2)))
    (unif : qclose (eseq (qadd Xn (qeps (n + 2))) (m + 2)) (eseq (qadd Xn (qeps (n + 2))) (n + 2)) δ)
    (cy : qclose ym yn δ) (hΔ0 : qle qzero Δ) (hΔ : qlt (qadd δ δ) (qmul Δ g)) :
    qle Xm (qadd (qadd Xn (qeps (n + 2))) Δ) := by
  cases qle_total (qadd (qadd Xn (qeps (n + 2))) Δ) Xm with
  | inr h => exact h
  | inl h =>
      have t := trap (n := m + 1) hR hXn hXm hΔ0 hg0 hg h
      rw [show m + 1 + 1 = m + 2 from rfl] at t
      obtain ⟨u1, u2⟩ := unif
      obtain ⟨c1, c2⟩ := cy
      obtain ⟨_, np⟩ := qlt_iff_le_not_le.mp hΔ
      exact absurd (by unfold qsub at *; rat_linarith) np

/-- THE LOGARITHM OF AN OPERATIONAL REAL: a Cauchy argument eventually in `[lu, hu]`, `lu > 0`, has Cauchy
grid answers. -/
theorem ln_cauchy {y : Nat → QExpr} {lu hu : QExpr} (hc : ZRecip.Cauchy y) (hy : Ev y lu hu) (hlo : qlt qzero lu) :
    ZRecip.Cauchy (fun n => lnseq (y n) n) := fun k => by
  have c0 := qmul_inv'_cancel (ne_zero_of_lt hlo)
  obtain ⟨B, hB⟩ := lv_floor hlo (show qle qone (qmul (qinv' lu) lu) by
    have := qmul_comm (qinv' lu) lu; rat_linarith)
  have ylo0 : qlt qzero (qeps (B + 1)) := qeps_pos (B + 1)
  obtain ⟨Na, hNa⟩ := hy (B + 1)
  obtain ⟨N0, hN0⟩ := ln_bracket_unif (yhi := qadd hu qone) ylo0
  obtain ⟨Mr, _, hMr0, _, r1, r2, _, _⟩ := bound4 (qadd (qinv' (qeps (B + 1))) qone) (qadd hu qone) qzero qzero
  have hR1 : qle qone (qadd (qadd Mr qone) qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have hR0 : qle qzero (qadd (qadd Mr qone) qone) := qle_trans (qle_of_qlt qone_pos) hR1
  obtain ⟨C, Ng, hgC⟩ := gap_const hR1
  obtain ⟨Nu, hNu⟩ := E_unif hR0 ((k + 1) + C + 2)
  obtain ⟨Ny, hNy⟩ := hc ((k + 1) + C + 2)
  refine ⟨N0 + Na + Nu + Ny + Ng + k + 0 + 2, fun m n hm hn => ?_⟩
  obtain ⟨q1, q2, q3, q4, q5, q6, _⟩ := le7 N0 Na Nu Ny Ng k 0
  -- both indices are of the form _ + 2
  have two : ∀ p, N0 + Na + Nu + Ny + Ng + k + 0 + 2 ≤ p → ∃ p', p = p' + 2 ∧ N0 + Na + Nu + Ny + Ng + k + 0 ≤ p' := by
    intro p hp
    cases p with
    | zero => exact absurd hp (Nat.not_succ_le_zero _)
    | succ p1 =>
        cases p1 with
        | zero => exact absurd (Nat.le_of_succ_le_succ hp) (Nat.not_succ_le_zero _)
        | succ p' => exact ⟨p', rfl, Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hp)⟩
  obtain ⟨m', rfl, hm'⟩ := two m hm
  obtain ⟨n', rfl, hn'⟩ := two n hn
  have upm : ∀ X, X ≤ N0 + Na + Nu + Ny + Ng + k + 0 → X ≤ m' + 2 :=
    fun X h => Nat.le_trans (Nat.le_trans h hm') (Nat.le_add_right m' 2)
  have upn : ∀ X, X ≤ N0 + Na + Nu + Ny + Ng + k + 0 → X ≤ n' + 2 :=
    fun X h => Nat.le_trans (Nat.le_trans h hn') (Nat.le_add_right n' 2)
  obtain ⟨am1, am2⟩ := hNa (m' + 2) (upm _ q2)
  obtain ⟨an1, an2⟩ := hNa (n' + 2) (upn _ q2)
  have e1 := eps_le_one (B + 1)
  have sB := qeps_succ_add B
  have yml : qle (qeps (B + 1)) (y (m' + 2)) := by unfold qsub at am1; rat_linarith
  have ynl : qle (qeps (B + 1)) (y (n' + 2)) := by unfold qsub at an1; rat_linarith
  have ymh : qle (y (m' + 2)) (qadd hu qone) := by rat_linarith
  have ynh : qle (y (n' + 2)) (qadd hu qone) := by rat_linarith
  obtain ⟨bm1, bm2⟩ := hN0 (y (m' + 2)) yml ymh m' (Nat.le_trans q1 hm')
  obtain ⟨bn1, bn2⟩ := hN0 (y (n' + 2)) ynl ynh n' (Nat.le_trans q1 hn')
  obtain ⟨rm1, rm2⟩ := ln_range ylo0 yml ymh ⟨bm1, bm2⟩
  obtain ⟨rn1, rn2⟩ := ln_range ylo0 ynl ynh ⟨bn1, bn2⟩
  have bm2' : qle (y (m' + 2)) (eseq (qadd (lnseq (y (m' + 2)) (m' + 2)) (qeps (m' + 2))) (m' + 2)) := by
    cases qle_total (y (m' + 2)) (eseq (qadd (lnseq (y (m' + 2)) (m' + 2)) (qeps (m' + 2))) (m' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h bm2
  have bn2' : qle (y (n' + 2)) (eseq (qadd (lnseq (y (n' + 2)) (n' + 2)) (qeps (n' + 2))) (n' + 2)) := by
    cases qle_total (y (n' + 2)) (eseq (qadd (lnseq (y (n' + 2)) (n' + 2)) (qeps (n' + 2))) (n' + 2)) with
    | inl h => exact h
    | inr h => exact absurd h bn2
  show qclose (lnseq (y (m' + 2)) (m' + 2)) (lnseq (y (n' + 2)) (n' + 2)) (qeps k)
  generalize lnseq (y (m' + 2)) (m' + 2) = Xm at bm1 bm2' rm1 rm2 ⊢
  generalize lnseq (y (n' + 2)) (n' + 2) = Xn at bn1 bn2' rn1 rn2 ⊢
  obtain ⟨u1, u2⟩ := r1
  obtain ⟨v1, v2⟩ := r2
  unfold qsub at u1 u2 v1 v2
  have o1 := qle_of_qlt qone_pos
  have em1 := eps_le_one (m' + 2)
  have en1 := eps_le_one (n' + 2)
  have em0 := qeps_nonneg (m' + 2)
  have en0 := qeps_nonneg (n' + 2)
  have XmR : qclose Xm qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have XnR : qclose Xn qzero (qadd (qadd Mr qone) qone) := by constructor <;> (unfold qsub; rat_linarith)
  have XmeR : qclose (qadd Xm (qeps (m' + 2))) qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have XneR : qclose (qadd Xn (qeps (n' + 2))) qzero (qadd (qadd Mr qone) qone) := by
    constructor <;> (unfold qsub; rat_linarith)
  have gm := hgC (m' + 1) (Nat.le_trans (Nat.le_trans q5 hm') (Nat.le_add_right m' 1))
  have gn := hgC (n' + 1) (Nat.le_trans (Nat.le_trans q5 hn') (Nat.le_add_right n' 1))
  have uA := hNu (qadd Xn (qeps (n' + 2))) XneR (m' + 2) (n' + 2) (upm _ q3) (upn _ q3)
  have uB := hNu (qadd Xm (qeps (m' + 2))) XmeR (n' + 2) (m' + 2) (upn _ q3) (upm _ q3)
  have cyA := hNy (m' + 2) (n' + 2) (upm _ q4) (upn _ q4)
  have cyB := hNy (n' + 2) (m' + 2) (upn _ q4) (upm _ q4)
  -- Δ·g = ε_{(k+1)+C} > 2·ε_{(k+1)+C+2}
  have pm := qeps_mul (k + 1) C
  have s1 := qeps_succ_add ((k + 1) + C)
  have s2 := qeps_succ_add ((k + 1) + C + 1)
  have pp := qeps_pos ((k + 1) + C + 2)
  have hΔ : qlt (qadd (qeps ((k + 1) + C + 2)) (qeps ((k + 1) + C + 2))) (qmul (qeps (k + 1)) (qeps C)) := by
    obtain ⟨p0, np⟩ := qlt_iff_le_not_le.mp pp
    exact qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => np (by rat_linarith)⟩
  have gC0 := qle_of_qlt (qeps_pos C)
  have d0 := qeps_nonneg (k + 1)
  have sideA := ln_side hR1 XneR XmR gC0 gm bm1 bn2' uA cyA d0 hΔ
  have sideB := ln_side hR1 XmeR XnR gC0 gn bn1 bm2' uB cyB d0 hΔ
  have ek := qeps_succ_add k
  have em := eps_anti (Nat.le_trans (Nat.succ_le_succ (Nat.le_trans q6 hm')) (Nat.le_succ (m' + 1)) : k + 1 ≤ m' + 2)
  have en := eps_anti (Nat.le_trans (Nat.succ_le_succ (Nat.le_trans q6 hn')) (Nat.le_succ (n' + 1)) : k + 1 ≤ n' + 2)
  constructor <;> (unfold qsub; rat_linarith)

end ZLn

#print axioms ZLn.eseq_respects
#print axioms ZLn.S_ge_lin
#print axioms ZLn.qnat_pow2
#print axioms ZLn.gpt_last
#print axioms ZLn.cnt_true
#print axioms ZLn.cnt_spec
#print axioms ZLn.ln_bracket
#print axioms ZLn.ln_bracket_unif
#print axioms ZLn.inv_anti
#print axioms ZLn.ln_range
#print axioms ZLn.E_gap
#print axioms ZLn.qeps_mul
#print axioms ZLn.gap_const
#print axioms ZLn.trap
#print axioms ZLn.Ev_ln
#print axioms ZLn.ln_sigma_pt
#print axioms ZLn.Ev_ln_slope
#print axioms ZLn.ln_side
#print axioms ZLn.ln_cauchy
