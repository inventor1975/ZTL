import ZTrig15

/-!
# ZAtan — `atan` on VR's operational reals, as the grid sum of `1/(1 + t²)`. Zero axioms.

At index `n`, `atan y` is the right-end Riemann sum of `ψ(t) = 1/(1 + t²)` over the grid points of `ZLn.gpt n`
(step `ε_n`, from `−n`) in `(0, y]` (`atseq`): the prefix sum `psum` up to the count of grid points `≤ y`, minus the
same up to `0`. No `π`, no `tan`, no series: everything the kernel needs comes from the sum itself.
  * the block: between two counts the sum is `(c' − c)·ε_n` times values of `ψ` at points of `[y, y']`, and the
    length `(c' − c)·ε_n` is `y' − y` within `ε_n` (`atan_block`);
  * `ψ` is 1-Lipschitz (`psi_lip`: `ψ(t) − ψ(z) = ψ(t)ψ(z)(z + t)(z − t)`, `|ψ(t)·t| ≤ 1/2`) and in `(0, 1]`;
  * so the step `atan(x + d) − atan x − d·ψ(x)` is within `d² + ε` uniformly (`ustep_atan`) — the kernel's
    derivative `u'/(1 + u²)`; monotone with slope at most 1 (`atan_lip`); `atan 0 = 0` exactly;
  * the answers at two indices are close (`atan_cauchy`: both near one fixed Riemann sum of `ψ`);
  * the value of an operational real is bracketed by the values at the ends of its reading (`Ev_atan`) — the ends'
    values are certified elsewhere (a Taylor chain from `0`, checked in the run).
-/

namespace ZAtan

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn

def psi (t : QExpr) : QExpr := qinv' (qadd qone (qmul t t))

/-- How many grid points `1..j` are `≤ y`. -/
def acnt (y : QExpr) (n : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      match qle.decidable (gpt n (j + 1)) y with
      | .isTrue _ => acnt y n j + 1
      | .isFalse _ => acnt y n j

/-- The prefix sums `Σ_{1 ≤ i ≤ j} ε_n·ψ(t_i)`. -/
def psum (n : Nat) : Nat → QExpr
  | 0 => qzero
  | j + 1 => qadd (psum n j) (qmul (qeps n) (psi (gpt n (j + 1))))

/-- `atan y` at index `n`. -/
def atseq (y : QExpr) (n : Nat) : QExpr :=
  qsub (psum n (acnt y n (gridK n))) (psum n (acnt qzero n (gridK n)))

theorem acnt_true {y : QExpr} {n j : Nat} (h : qle (gpt n (j + 1)) y) : acnt y n (j + 1) = acnt y n j + 1 := by
  show (match qle.decidable (gpt n (j + 1)) y with
      | .isTrue _ => acnt y n j + 1
      | .isFalse _ => acnt y n j) = acnt y n j + 1
  cases qle.decidable (gpt n (j + 1)) y with
  | isTrue _ => rfl
  | isFalse hp => exact absurd h hp

theorem acnt_false {y : QExpr} {n j : Nat} (h : ¬ qle (gpt n (j + 1)) y) : acnt y n (j + 1) = acnt y n j := by
  show (match qle.decidable (gpt n (j + 1)) y with
      | .isTrue _ => acnt y n j + 1
      | .isFalse _ => acnt y n j) = acnt y n j
  cases qle.decidable (gpt n (j + 1)) y with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

theorem gpt_mono {n i j : Nat} (h : i ≤ j) : qle (gpt n i) (gpt n j) := by
  unfold gpt
  have := ZExp.scale (qnat_mono h) (qeps_nonneg n)
  rat_linarith

/-- `t_{c+k} − t_c = k·ε_n`. -/
theorem gpt_add (n c k : Nat) : qEq (qsub (gpt n (c + k)) (gpt n c)) (qmul (qnat k) (qeps n)) := by
  unfold gpt
  have h := qnat_add c k
  have e : qEq (qmul (qnat (c + k)) (qeps n)) (qmul (qadd (qnat c) (qnat k)) (qeps n)) := qmul_respects h (qEq_refl _)
  have e2 : qEq (qmul (qadd (qnat c) (qnat k)) (qeps n)) (qadd (qmul (qnat c) (qeps n)) (qmul (qnat k) (qeps n))) := by
    rat_ring
  unfold qsub
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE COUNT. The points `≤ y` are an initial run (the grid is increasing): all up to the count, the next one not. -/
theorem acnt_spec (y : QExpr) (n : Nat) : ∀ j,
    acnt y n j ≤ j ∧
    (∀ i, 1 ≤ i → i ≤ acnt y n j → qle (gpt n i) y) ∧
    (acnt y n j < j → ¬ qle (gpt n (acnt y n j + 1)) y)
  | 0 => ⟨Nat.le_refl 0, fun i h1 h2 => absurd (Nat.le_trans h1 h2) (Nat.not_succ_le_zero 0),
          fun h => absurd h (Nat.lt_irrefl 0)⟩
  | j + 1 => by
      obtain ⟨c1, c2, c3⟩ := acnt_spec y n j
      cases qle.decidable (gpt n (j + 1)) y with
      | isTrue hp =>
          rw [acnt_true hp]
          have hc : acnt y n j = j := by
            cases Nat.lt_or_eq_of_le c1 with
            | inl lt => exact absurd (qle_trans (gpt_mono (Nat.succ_le_succ (Nat.le_of_lt lt))) hp) (c3 lt)
            | inr eq => exact eq
          refine ⟨by rw [hc]; exact Nat.le_refl _,
            fun i _ hi => qle_trans (gpt_mono (by rw [hc] at hi; exact hi)) hp,
            fun h => absurd (by rw [hc] at h; exact h) (Nat.lt_irrefl (j + 1))⟩
      | isFalse hp =>
          rw [acnt_false hp]
          refine ⟨Nat.le_succ_of_le c1, c2, fun _ => ?_⟩
          cases Nat.lt_or_eq_of_le c1 with
          | inl lt => exact c3 lt
          | inr eq => rw [eq]; exact hp

/-- THE BRACKET: for `t_1 ≤ y < t_K`, the count `c` has `1 ≤ c < K` and `t_c ≤ y < t_{c+1}`. -/
theorem acnt_bracket {y : QExpr} {n : Nat} (h1 : qle (gpt n 1) y) (h2 : qlt y (gpt n (gridK n))) :
    1 ≤ acnt y n (gridK n) ∧ acnt y n (gridK n) < gridK n ∧
    qle (gpt n (acnt y n (gridK n))) y ∧ qlt y (gpt n (acnt y n (gridK n) + 1)) := by
  obtain ⟨c1, c2, c3⟩ := acnt_spec y n (gridK n)
  have h2' := qlt_iff_le_not_le.mp h2
  have lt : acnt y n (gridK n) < gridK n := by
    cases Nat.lt_or_eq_of_le c1 with
    | inl l => exact l
    | inr e =>
        have K1 : 1 ≤ gridK n := by
          cases Nat.lt_or_ge 0 (gridK n) with
          | inl p => exact p
          | inr z =>
              have z' : gridK n = 0 := Nat.le_antisymm z (Nat.zero_le _)
              have g : qle (gpt n (gridK n)) (gpt n 1) := by rw [z']; exact gpt_mono (Nat.zero_le 1)
              exact absurd (qle_trans g h1) h2'.2
        exact absurd (c2 _ K1 (Nat.le_of_eq e.symm)) h2'.2
  have one : 1 ≤ acnt y n (gridK n) := by
    cases Nat.lt_or_ge 0 (acnt y n (gridK n)) with
    | inl p => exact p
    | inr z =>
        have z' : acnt y n (gridK n) = 0 := Nat.le_antisymm z (Nat.zero_le _)
        have := c3 lt
        rw [z'] at this
        exact absurd h1 this
  refine ⟨one, lt, c2 _ one (Nat.le_refl _), ?_⟩
  have := c3 lt
  cases qle_total (gpt n (acnt y n (gridK n) + 1)) y with
  | inl h => exact absurd h this
  | inr h => exact qlt_iff_le_not_le.mpr ⟨h, this⟩

/-- The count is monotone in `y`. -/
theorem acnt_mono {y y' : QExpr} (hy : qle y y') (n j : Nat) : acnt y n j ≤ acnt y' n j := by
  obtain ⟨c1, c2, _⟩ := acnt_spec y n j
  obtain ⟨_, _, c3'⟩ := acnt_spec y' n j
  cases Nat.lt_or_ge (acnt y' n j) (acnt y n j) with
  | inr h => exact h
  | inl h =>
      have l : acnt y' n j < j := Nat.lt_of_lt_of_le h c1
      exact absurd (qle_trans (c2 _ (Nat.succ_le_succ (Nat.zero_le _)) h) hy) (c3' l)

/-! ## `ψ = 1/(1 + t²)` -/

theorem psi_facts (t : QExpr) :
    qle qzero (psi t) ∧ qle (psi t) qone ∧ qEq (qmul (qadd qone (qmul t t)) (psi t)) qone :=
  inv_facts (by have := qmul_self_nonneg t; rat_linarith)

/-- `|ψ(t)·t| ≤ 1/2`, as `2·ψ(t)·t ∈ [−1, 1]`. -/
theorem psi_t (t : QExpr) :
    qle (qadd (qmul (psi t) t) (qmul (psi t) t)) qone ∧ qle (qneg qone) (qadd (qmul (psi t) t) (qmul (psi t) t)) := by
  obtain ⟨p0, _, pc⟩ := psi_facts t
  have s1 := qmul_nonneg p0 (qmul_self_nonneg (qsub t qone))
  have s2 := qmul_nonneg p0 (qmul_self_nonneg (qadd t qone))
  have e1 : qEq (qmul (psi t) (qmul (qsub t qone) (qsub t qone)))
      (qsub (qmul (qadd qone (qmul t t)) (psi t)) (qadd (qmul (psi t) t) (qmul (psi t) t))) := by unfold qsub; rat_ring
  have e2 : qEq (qmul (psi t) (qmul (qadd t qone) (qadd t qone)))
      (qadd (qmul (qadd qone (qmul t t)) (psi t)) (qadd (qmul (psi t) t) (qmul (psi t) t))) := by rat_ring
  generalize qmul (qadd qone (qmul t t)) (psi t) = P at *
  generalize qmul (psi t) (qmul (qsub t qone) (qsub t qone)) = S1 at *
  generalize qmul (psi t) (qmul (qadd t qone) (qadd t qone)) = S2 at *
  generalize qmul (psi t) t = Q at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `ψ(t) − ψ(z) = ψ(t)ψ(z)(z + t)·(z − t)`. -/
theorem psi_diff (t z : QExpr) :
    qEq (qsub (psi t) (psi z)) (qmul (qmul (qmul (psi t) (psi z)) (qadd z t)) (qsub z t)) := by
  obtain ⟨_, _, ct⟩ := psi_facts t
  obtain ⟨_, _, cz⟩ := psi_facts z
  -- ψt = ψt·ψz·(1 + z²), ψz = ψt·ψz·(1 + t²)
  have a1 : qEq (psi t) (qmul (psi t) (qmul (qadd qone (qmul z z)) (psi z))) := by
    have := qmul_respects (qEq_refl (psi t)) cz; have e := qmul_one (psi t)
    exact qEq_trans (qEq_symm e) (qEq_symm this)
  have a2 : qEq (psi z) (qmul (psi z) (qmul (qadd qone (qmul t t)) (psi t))) := by
    have := qmul_respects (qEq_refl (psi z)) ct; have e := qmul_one (psi z)
    exact qEq_trans (qEq_symm e) (qEq_symm this)
  have e : qEq (qsub (qmul (psi t) (qmul (qadd qone (qmul z z)) (psi z))) (qmul (psi z) (qmul (qadd qone (qmul t t)) (psi t))))
      (qmul (qmul (qmul (psi t) (psi z)) (qadd z t)) (qsub z t)) := by unfold qsub; rat_ring
  have s := qadd_respects a1 (qneg_respects a2)
  unfold qsub at *
  exact qEq_trans s e

/-- `|ψ(t)ψ(z)(z + t)| ≤ 1`. -/
theorem psi_P (t z : QExpr) :
    qle (qmul (qmul (psi t) (psi z)) (qadd z t)) qone ∧ qle (qneg qone) (qmul (qmul (psi t) (psi z)) (qadd z t)) := by
  obtain ⟨t0, t1, _⟩ := psi_facts t
  obtain ⟨z0, z1, _⟩ := psi_facts z
  obtain ⟨a1, a2⟩ := psi_t t
  obtain ⟨b1, b2⟩ := psi_t z
  -- ψz·(2ψt·t) ∈ [−ψz, ψz] ⊂ [−1, 1], and ψt·(2ψz·z) likewise
  have f1 := ZExp.scale a1 z0
  have f2 := ZExp.scale a2 z0
  have f3 := ZExp.scale b1 t0
  have f4 := ZExp.scale b2 t0
  have e : qEq (qadd (qmul (qmul (psi t) (psi z)) (qadd z t)) (qmul (qmul (psi t) (psi z)) (qadd z t)))
      (qadd (qmul (qadd (qmul (psi t) t) (qmul (psi t) t)) (psi z)) (qmul (qadd (qmul (psi z) z) (qmul (psi z) z)) (psi t))) := by
    rat_ring
  have o1 : qEq (qmul qone (psi z)) (psi z) := qone_mul _
  have o2 : qEq (qmul qone (psi t)) (psi t) := qone_mul _
  have o3 : qEq (qmul (qneg qone) (psi z)) (qneg (psi z)) := by rat_ring
  have o4 : qEq (qmul (qneg qone) (psi t)) (qneg (psi t)) := by rat_ring
  generalize qmul (qmul (psi t) (psi z)) (qadd z t) = P at *
  generalize qmul (qadd (qmul (psi t) t) (qmul (psi t) t)) (psi z) = A at *
  generalize qmul (qadd (qmul (psi z) z) (qmul (psi z) z)) (psi t) = B at *
  generalize qmul qone (psi z) = A1 at *; generalize qmul qone (psi t) = B1 at *
  generalize qmul (qneg qone) (psi z) = A2 at *; generalize qmul (qneg qone) (psi t) = B2 at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `ψ` IS 1-LIPSCHITZ. -/
theorem psi_lip {t z d : QExpr} (h1 : qle (qsub t z) d) (h2 : qle (qsub z t) d) :
    ZTrig.Ab (qsub (psi t) (psi z)) d := by
  have e := psi_diff t z
  obtain ⟨p1, p2⟩ := psi_P t z
  generalize qmul (qmul (psi t) (psi z)) (qadd z t) = P at *
  cases qle_total qzero (qsub z t) with
  | inl hp =>
      have f1 := ZExp.scale p1 hp
      have f2 := ZExp.scale p2 hp
      have o : qEq (qmul qone (qsub z t)) (qsub z t) := qone_mul _
      have o2 : qEq (qmul (qneg qone) (qsub z t)) (qneg (qsub z t)) := by rat_ring
      generalize qmul P (qsub z t) = Q at *
      unfold qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | inr hn =>
      have hn' : qle qzero (qsub t z) := by unfold qsub at *; rat_linarith
      have f1 := ZExp.scale p1 hn'
      have f2 := ZExp.scale p2 hn'
      have o : qEq (qmul P (qsub z t)) (qneg (qmul P (qsub t z))) := by unfold qsub; rat_ring
      have o1 : qEq (qmul qone (qsub t z)) (qsub t z) := qone_mul _
      have o2 : qEq (qmul (qneg qone) (qsub t z)) (qneg (qsub t z)) := by rat_ring
      generalize qmul P (qsub z t) = Q at *
      generalize qmul P (qsub t z) = Q' at *
      unfold qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- `ψ` falls on `t ≥ 0`. -/
theorem psi_anti_pos {t z : QExpr} (h0 : qle qzero t) (h : qle t z) : qle (psi z) (psi t) := by
  have e := psi_diff t z
  obtain ⟨t0, _, _⟩ := psi_facts t
  obtain ⟨z0, _, _⟩ := psi_facts z
  have f := qmul_nonneg (qmul_nonneg (qmul_nonneg t0 z0) (by rat_linarith : qle qzero (qadd z t)))
    (by unfold qsub; rat_linarith : qle qzero (qsub z t))
  generalize qmul (qmul (qmul (psi t) (psi z)) (qadd z t)) (qsub z t) = Q at *
  unfold qsub at *; rat_linarith

/-- `ψ` rises on `t ≤ 0`. -/
theorem psi_mono_neg {t z : QExpr} (h0 : qle z qzero) (h : qle t z) : qle (psi t) (psi z) := by
  have e := psi_diff t z
  obtain ⟨t0, _, _⟩ := psi_facts t
  obtain ⟨z0, _, _⟩ := psi_facts z
  have f := qmul_nonneg (qmul_nonneg (qmul_nonneg t0 z0) (by rat_linarith : qle qzero (qneg (qadd z t))))
    (by unfold qsub; rat_linarith : qle qzero (qsub z t))
  have e2 : qEq (qmul (qmul (qmul (psi t) (psi z)) (qneg (qadd z t))) (qsub z t))
      (qneg (qmul (qmul (qmul (psi t) (psi z)) (qadd z t)) (qsub z t))) := by rat_ring
  generalize qmul (qmul (qmul (psi t) (psi z)) (qadd z t)) (qsub z t) = Q at *
  generalize qmul (qmul (qmul (psi t) (psi z)) (qneg (qadd z t))) (qsub z t) = Q' at *
  unfold qsub at *; rat_linarith

/-! ## The block between two counts -/

theorem psum_block (n c : Nat) {m M : QExpr} : ∀ k,
    (∀ j, c < j → j ≤ c + k → qle m (psi (gpt n j)) ∧ qle (psi (gpt n j)) M) →
    qle (qmul (qmul (qnat k) (qeps n)) m) (qsub (psum n (c + k)) (psum n c)) ∧
    qle (qsub (psum n (c + k)) (psum n c)) (qmul (qmul (qnat k) (qeps n)) M)
  | 0, _ => by
      have z := qnat_zero
      have e1 : qEq (qmul (qmul (qnat 0) (qeps n)) m) (qmul (qmul qzero (qeps n)) m) :=
        qmul_respects (qmul_respects z (qEq_refl _)) (qEq_refl _)
      have e2 : qEq (qmul (qmul (qnat 0) (qeps n)) M) (qmul (qmul qzero (qeps n)) M) :=
        qmul_respects (qmul_respects z (qEq_refl _)) (qEq_refl _)
      have e3 : qEq (qmul (qmul qzero (qeps n)) m) qzero := by rat_ring
      have e4 : qEq (qmul (qmul qzero (qeps n)) M) qzero := by rat_ring
      show qle _ (qsub (psum n c) (psum n c)) ∧ qle (qsub (psum n c) (psum n c)) _
      generalize qmul (qmul (qnat 0) (qeps n)) m = A at *
      generalize qmul (qmul (qnat 0) (qeps n)) M = B at *
      generalize qmul (qmul qzero (qeps n)) m = A' at *
      generalize qmul (qmul qzero (qeps n)) M = B' at *
      unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  | k + 1, h => by
      obtain ⟨l, u⟩ := psum_block n c k (fun j h1 h2 => h j h1 (Nat.le_succ_of_le h2))
      obtain ⟨hm, hM⟩ := h (c + k + 1) (Nat.lt_succ_of_le (Nat.le_add_right c k)) (Nat.le_refl _)
      have f1 := scale_l hm (qeps_nonneg n)
      have f2 := scale_l hM (qeps_nonneg n)
      have q := qnat_succ k
      have e1 : qEq (qmul (qmul (qnat (k + 1)) (qeps n)) m) (qadd (qmul (qmul (qnat k) (qeps n)) m) (qmul (qeps n) m)) := by
        have := qmul_respects (qmul_respects q (qEq_refl (qeps n))) (qEq_refl m)
        exact qEq_trans this (by rat_ring)
      have e2 : qEq (qmul (qmul (qnat (k + 1)) (qeps n)) M) (qadd (qmul (qmul (qnat k) (qeps n)) M) (qmul (qeps n) M)) := by
        have := qmul_respects (qmul_respects q (qEq_refl (qeps n))) (qEq_refl M)
        exact qEq_trans this (by rat_ring)
      show qle _ (qsub (qadd (psum n (c + k)) (qmul (qeps n) (psi (gpt n (c + k + 1))))) (psum n c)) ∧
        qle (qsub (qadd (psum n (c + k)) (qmul (qeps n) (psi (gpt n (c + k + 1))))) (psum n c)) _
      generalize qmul (qmul (qnat (k + 1)) (qeps n)) m = A at *
      generalize qmul (qmul (qnat (k + 1)) (qeps n)) M = B at *
      generalize qmul (qmul (qnat k) (qeps n)) m = A' at *
      generalize qmul (qmul (qnat k) (qeps n)) M = B' at *
      generalize qmul (qeps n) (psi (gpt n (c + k + 1))) = T at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `y` in the grid's range at index `n`: `t_1 ≤ y < t_K`. -/
def InR (y : QExpr) (n : Nat) : Prop := qle (gpt n 1) y ∧ qlt y (gpt n (gridK n))

/-- THE WINDOW: for `y ≤ y'` in range, `atan y' − atan y` is `L·[m, M]` where `ψ ∈ [m, M]` on `[y, y']`, the
length `L` within `ε_n` of `y' − y`. -/
theorem atan_window {y y' m M : QExpr} {n : Nat} (hy : InR y n) (hy' : InR y' n) (hyy : qle y y')
    (hψ : ∀ t, qle y t → qle t y' → qle m (psi t) ∧ qle (psi t) M) :
    ∃ L, qle qzero L ∧ qle (qsub (qsub y' y) (qeps n)) L ∧ qle L (qadd (qsub y' y) (qeps n)) ∧
      qle (qmul L m) (qsub (atseq y' n) (atseq y n)) ∧ qle (qsub (atseq y' n) (atseq y n)) (qmul L M) := by
  obtain ⟨_, _, b1, b2⟩ := acnt_bracket hy.1 hy.2
  obtain ⟨_, _, b1', b2'⟩ := acnt_bracket hy'.1 hy'.2
  have mono := acnt_mono hyy n (gridK n)
  generalize hc : acnt y n (gridK n) = c at *
  generalize hc' : acnt y' n (gridK n) = c' at *
  obtain ⟨k, rfl⟩ := le_ex mono
  have g := gpt_add n c k
  have gs := gpt_succ n c
  have gs' := gpt_succ n (c + k)
  obtain ⟨l, u⟩ := psum_block n c k (m := m) (M := M) (fun j h1 h2 => by
    have a1 : qle y (gpt n j) := by
      have := gpt_mono (n := n) (Nat.succ_le_of_lt h1)
      exact qle_trans (qle_of_qlt b2) this
    exact hψ _ a1 (qle_trans (gpt_mono h2) b1'))
  refine ⟨qmul (qnat k) (qeps n), qmul_nonneg (qnat_nonneg k) (qeps_nonneg n), ?_, ?_, ?_, ?_⟩
  · have := qle_of_qlt b2'
    unfold qsub at *; rat_linarith
  · have := qle_of_qlt b2
    unfold qsub at *; rat_linarith
  · have e : qEq (qsub (atseq y' n) (atseq y n)) (qsub (psum n (c + k)) (psum n c)) := by
      unfold atseq; rw [hc, hc']; unfold qsub; rat_ring
    exact qle_trans l (qle_of_qEq (qEq_symm e))
  · have e : qEq (qsub (atseq y' n) (atseq y n)) (qsub (psum n (c + k)) (psum n c)) := by
      unfold atseq; rw [hc, hc']; unfold qsub; rat_ring
    exact qle_trans (qle_of_qEq e) u

/-- MONOTONE, SLOPE AT MOST 1: `0 ≤ atan y' − atan y ≤ y' − y + ε_n`. -/
theorem atan_lip {y y' : QExpr} {n : Nat} (hy : InR y n) (hy' : InR y' n) (hyy : qle y y') :
    qle qzero (qsub (atseq y' n) (atseq y n)) ∧ qle (qsub (atseq y' n) (atseq y n)) (qadd (qsub y' y) (qeps n)) := by
  obtain ⟨L, L0, _, L2, l, u⟩ := atan_window hy hy' hyy (m := qzero) (M := qone)
    (fun t _ _ => ⟨(psi_facts t).1, (psi_facts t).2.1⟩)
  have e1 : qEq (qmul L qzero) qzero := qmul_zero L
  have e2 : qEq (qmul L qone) L := qmul_one L
  generalize qmul L qzero = A at *; generalize qmul L qone = B at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE STEP, at one index: `|atan y' − atan y − (y' − y)·ψ(z)| ≤ (y' − y)² + ε_n·(y' − y + 1)`, `z ∈ [y, y']`. -/
theorem atan_step_core {y y' z : QExpr} {n : Nat} (hy : InR y n) (hy' : InR y' n) (hyy : qle y y')
    (hz1 : qle y z) (hz2 : qle z y') :
    ZTrig.Ab (qsub (qsub (atseq y' n) (atseq y n)) (qmul (qsub y' y) (psi z)))
      (qadd (qmul (qsub y' y) (qsub y' y)) (qmul (qeps n) (qadd (qsub y' y) qone))) := by
  have d0 : qle qzero (qsub y' y) := by unfold qsub; rat_linarith
  obtain ⟨L, L0, L1, L2, l, u⟩ := atan_window hy hy' hyy (m := qsub (psi z) (qsub y' y)) (M := qadd (psi z) (qsub y' y))
    (fun t h1 h2 => by
      obtain ⟨a, b⟩ := psi_lip (t := t) (z := z) (d := qsub y' y) (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩)
  obtain ⟨p0, p1, _⟩ := psi_facts z
  generalize qsub y' y = d at *
  generalize qsub (atseq y' n) (atseq y n) = D at *
  generalize psi z = P at *
  generalize hh : qeps n = h at *
  have h0 : qle qzero h := by rw [← hh]; exact qeps_nonneg n
  -- (L − d)·P within h; L·d ≤ (d + h)·d
  have ld := ZExp.scale L2 d0
  have cross : qle (qmul (qsub L d) P) h ∧ qle (qneg h) (qmul (qsub L d) P) := by
    cases qle_total qzero (qsub L d) with
    | inl hp =>
        have f := scale_l p1 hp
        have f0 := qmul_nonneg hp p0
        have o := qmul_one (qsub L d)
        generalize qmul (qsub L d) P = X at *; generalize qmul (qsub L d) qone = Y at *
        unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
    | inr hn =>
        have hn' : qle qzero (qsub d L) := by unfold qsub at *; rat_linarith
        have f := scale_l p1 hn'
        have f0 := qmul_nonneg hn' p0
        have o := qmul_one (qsub d L)
        have e : qEq (qmul (qsub L d) P) (qneg (qmul (qsub d L) P)) := by unfold qsub; rat_ring
        generalize qmul (qsub d L) P = X at *; generalize qmul (qsub d L) qone = Y at *
        generalize qmul (qsub L d) P = Z at *
        unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have e1 : qEq (qmul L (qsub P d)) (qsub (qmul L P) (qmul L d)) := by unfold qsub; rat_ring
  have e2 : qEq (qmul L (qadd P d)) (qadd (qmul L P) (qmul L d)) := by rat_ring
  have e3 : qEq (qmul (qsub L d) P) (qsub (qmul L P) (qmul d P)) := by unfold qsub; rat_ring
  have e4 : qEq (qmul (qadd d h) d) (qadd (qmul d d) (qmul h d)) := by rat_ring
  have e5 : qEq (qmul h (qadd d qone)) (qadd (qmul h d) h) := by rat_ring
  have ld0 := qmul_nonneg L0 d0
  generalize qmul L (qsub P d) = A at *; generalize qmul L (qadd P d) = B at *
  generalize qmul (qsub L d) P = C at *; generalize qmul (qadd d h) d = E at *
  generalize qmul h (qadd d qone) = F at *
  generalize qmul L P = LP at *; generalize qmul L d = Ld at *; generalize qmul d P = dP at *
  generalize qmul d d = dd at *; generalize qmul h d = hd at *
  obtain ⟨c1, c2⟩ := cross
  unfold qsub at *
  have s1 : qle (qadd (qneg h) (qneg E)) (qadd C (qneg Ld)) := by rat_linarith
  have s2 : qle (qadd C (qneg Ld)) (qadd D (qneg dP)) := by rat_linarith
  have s3 : qle (qneg (qadd dd F)) (qadd (qneg h) (qneg E)) := by rat_linarith
  have t1 : qle (qadd D (qneg dP)) (qadd C Ld) := by rat_linarith
  have t2 : qle (qadd C Ld) (qadd h E) := by rat_linarith
  have t3 : qle (qadd h E) (qadd dd F) := by rat_linarith
  exact ⟨qle_trans s3 (qle_trans s1 s2), qle_trans t1 (qle_trans t2 t3)⟩

/-! ## Uniform in the point -/

theorem eps_scaledA {C : QExpr} (hC : qle qzero C) : ∃ B, ∀ k, qle (qmul (qeps (k + B)) C) (qeps k) := by
  obtain ⟨B, hB1, _⟩ := qexpr_bound C
  have hc : qle C (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  refine ⟨B, fun k => ?_⟩
  have s := scale_l hc (qeps_nonneg (k + B))
  have e := qpow2_mul_eps B k
  have c := qmul_comm (qofInt (pow2 B)) (qeps (k + B))
  generalize qmul (qeps (k + B)) C = P at *; generalize qmul (qeps (k + B)) (qofInt (pow2 B)) = Q at *
  generalize qmul (qofInt (pow2 B)) (qeps (k + B)) = Q' at *
  rat_linarith

/-- In range from index `K0 + 2` on, for `|y| ≤ K0`. -/
theorem inR_of {y : QExpr} {n K0 : Nat} (hy : ZTrig.Ab y (qnat K0)) (hn : K0 + 2 ≤ n) : InR y n := by
  have g1 : qEq (gpt n 1) (qadd (qneg (qnat n)) (qmul (qnat 1) (qeps n))) := qEq_refl _
  have o : qEq (qnat 1) qone := by have := qnat_succ 0; have := qnat_zero; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have e1 : qEq (qmul (qnat 1) (qeps n)) (qeps n) := qEq_trans (qmul_respects o (qEq_refl _)) (qone_mul _)
  have h1 := ZTrig.qeps_le_one n
  have m := qnat_mono hn
  have a2 := qnat_add K0 2
  have t2 : qEq (qnat 2) (qadd qone qone) := by
    have := qnat_succ 1; have := qnat_succ 0; have := qnat_zero
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have gl := gpt_last n
  obtain ⟨y1, y2⟩ := hy
  refine ⟨by rat_linarith, qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => ?_⟩⟩
  have := qle_of_qlt qone_pos
  exact absurd (by rat_linarith : qle qone qzero) (qlt_iff_le_not_le.mp qone_pos).2

/-- THE UNIFORM STEP: `atan(x + d) − atan x − d·ψ(x)` within `ε_k + d²` for `|x| ≤ A`, `|d| ≤ R` — the kernel's
`(atan u)' = u'/(1 + u²)`, no mean value theorem. -/
theorem ustep_atan : ∀ {A R : QExpr}, qle qzero A → qle qzero R →
    ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x d, ZTrig.Ab x A → ZTrig.Ab d R →
      ZTrig.Ab (qsub (qsub (atseq (qadd x d) n) (atseq x n)) (qmul d (psi x))) (qadd (qeps k) (qmul (qmul d d) H)) := by
  intro A R hA hR
  refine ⟨qone, qle_of_qlt qone_pos, fun k => ?_⟩
  obtain ⟨K0, c1, c2⟩ := ZExp.exists_nat_bound (qadd A R)
  obtain ⟨B, hB⟩ := eps_scaledA (by rat_linarith : qle qzero (qadd R qone))
  refine ⟨K0 + 2 + (k + B), fun n hn x d hx hd => ?_⟩
  have hn1 : K0 + 2 ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hn2 : k + B ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  have he : qle (qeps n) (qeps (k + B)) := by
    obtain ⟨j, rfl⟩ := le_ex hn2; exact qeps_le_add (k + B) j
  obtain ⟨x1, x2⟩ := hx; obtain ⟨d1, d2⟩ := hd
  unfold qsub at c1 c2
  have ax : ZTrig.Ab x (qnat K0) := ⟨by rat_linarith, by rat_linarith⟩
  have axd : ZTrig.Ab (qadd x d) (qnat K0) := ⟨by rat_linarith, by rat_linarith⟩
  have r1 := inR_of ax hn1
  have r2 := inR_of axd hn1
  have hk := hB k
  have hk' := ZExp.scale he (by rat_linarith : qle qzero (qadd R qone))
  have dd0 := qmul_self_nonneg d
  have o1 : qEq (qmul (qmul d d) qone) (qmul d d) := qmul_one _
  cases qle_total qzero d with
  | inl hp =>
      have core := atan_step_core (z := x) r1 r2 (by rat_linarith) (qle_refl x) (by rat_linarith)
      have q : qEq (qsub (qadd x d) x) d := by unfold qsub; rat_ring
      have e1 : qEq (qmul (qsub (qadd x d) x) (psi x)) (qmul d (psi x)) := qmul_respects q (qEq_refl _)
      have e2 : qEq (qmul (qsub (qadd x d) x) (qsub (qadd x d) x)) (qmul d d) := qmul_respects q q
      have e3 : qEq (qmul (qeps n) (qadd (qsub (qadd x d) x) qone)) (qmul (qeps n) (qadd d qone)) :=
        qmul_respects (qEq_refl _) (qadd_respects q (qEq_refl _))
      have f := scale_l (by rat_linarith : qle (qadd d qone) (qadd R qone)) (qeps_nonneg n)
      have c3 := qmul_comm (qeps n) (qadd R qone)
      have c4 := qmul_comm (qeps (k + B)) (qadd R qone)
      generalize qmul (qsub (qadd x d) x) (psi x) = P1 at *
      generalize qmul (qsub (qadd x d) x) (qsub (qadd x d) x) = P2 at *
      generalize qmul (qeps n) (qadd (qsub (qadd x d) x) qone) = P3 at *
      obtain ⟨k1, k2⟩ := core
      unfold qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | inr hn' =>
      have core := atan_step_core (z := x) r2 r1 (by rat_linarith) (by rat_linarith) (qle_refl x)
      have q : qEq (qsub x (qadd x d)) (qneg d) := by unfold qsub; rat_ring
      have e1 : qEq (qmul (qsub x (qadd x d)) (psi x)) (qneg (qmul d (psi x))) :=
        qEq_trans (qmul_respects q (qEq_refl _)) (by rat_ring)
      have e2 : qEq (qmul (qsub x (qadd x d)) (qsub x (qadd x d))) (qmul d d) :=
        qEq_trans (qmul_respects q q) (by rat_ring)
      have e3 : qEq (qmul (qeps n) (qadd (qsub x (qadd x d)) qone)) (qmul (qeps n) (qadd (qneg d) qone)) :=
        qmul_respects (qEq_refl _) (qadd_respects q (qEq_refl _))
      have f := scale_l (by rat_linarith : qle (qadd (qneg d) qone) (qadd R qone)) (qeps_nonneg n)
      have c3 := qmul_comm (qeps n) (qadd R qone)
      have c4 := qmul_comm (qeps (k + B)) (qadd R qone)
      generalize qmul (qsub x (qadd x d)) (psi x) = P1 at *
      generalize qmul (qsub x (qadd x d)) (qsub x (qadd x d)) = P2 at *
      generalize qmul (qeps n) (qadd (qsub x (qadd x d)) qone) = P3 at *
      obtain ⟨k1, k2⟩ := core
      unfold qsub at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- `atan 0 = 0` at every index. -/
theorem atseq_zero (n : Nat) : qEq (atseq qzero n) qzero := by
  unfold atseq; unfold qsub; rat_ring

/-- Two nearby points: `|atan y − atan y*| ≤ |y − y*| + ε_n`. -/
theorem atan_near {y ys e : QExpr} {n : Nat} (hy : InR y n) (hs : InR ys n) (h1 : qle (qsub y ys) e)
    (h2 : qle (qsub ys y) e) : ZTrig.Ab (qsub (atseq y n) (atseq ys n)) (qadd e (qeps n)) := by
  cases qle_total y ys with
  | inl l =>
      obtain ⟨a, b⟩ := atan_lip hy hs l
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  | inr l =>
      obtain ⟨a, b⟩ := atan_lip hs hy l
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem le4a {a b c d n : Nat} (h : a + (b + (c + d)) ≤ n) : a ≤ n := Nat.le_trans (Nat.le_add_right _ _) h
theorem le4b {a b c d n : Nat} (h : a + (b + (c + d)) ≤ n) : b ≤ n :=
  Nat.le_trans (Nat.le_trans (Nat.le_add_right b _) (Nat.le_add_left _ a)) h
theorem le4c {a b c d n : Nat} (h : a + (b + (c + d)) ≤ n) : c ≤ n :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right c d) (Nat.le_add_left _ b)) (Nat.le_add_left _ a)) h
theorem le4d {a b c d n : Nat} (h : a + (b + (c + d)) ≤ n) : d ≤ n :=
  Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left d c) (Nat.le_add_left _ b)) (Nat.le_add_left _ a)) h

theorem eps_of_le {j n : Nat} (h : j ≤ n) : qle (qeps n) (qeps j) := by
  obtain ⟨i, rfl⟩ := le_ex h; exact qeps_le_add j i

/-- `|y| ≤ Ka + Kb + 1` for `y ∈ [lu − 1, hu + 1]`, `|lu| ≤ Ka`, `|hu| ≤ Kb`. -/
theorem ab_window {y lu hu : QExpr} {Ka Kb : Nat} (a1 : qle (qneg (qnat Ka)) lu) (a2 : qle lu (qnat Ka))
    (b1 : qle (qneg (qnat Kb)) hu) (b2 : qle hu (qnat Kb)) (h1 : qle (qsub lu qone) y) (h2 : qle y (qadd hu qone)) :
    ZTrig.Ab y (qnat (Ka + Kb + 1)) := by
  have e1 := qnat_add Ka Kb
  have e2 := qnat_succ (Ka + Kb)
  have p1 := qnat_nonneg Ka; have p2 := qnat_nonneg Kb
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem ab_le {x : QExpr} {a b : Nat} (h : ZTrig.Ab x (qnat a)) (hab : a ≤ b) : ZTrig.Ab x (qnat b) := by
  have m := qnat_mono hab; obtain ⟨h1, h2⟩ := h; exact ⟨by rat_linarith, by rat_linarith⟩

/-- One side of `atan_near`: `atan y ≥ atan y* − (y* − y) − ε_n` once `y ≥ y* − e`. -/
theorem atan_lo {y ys e : QExpr} {n : Nat} (hy : InR y n) (hs : InR ys n) (h : qle (qsub ys y) e) (he : qle qzero e) :
    qle (qsub (atseq ys n) (qadd e (qeps n))) (atseq y n) := by
  cases qle_total y ys with
  | inl l => obtain ⟨a, b⟩ := atan_lip hy hs l; unfold qsub at *; rat_linarith
  | inr l => obtain ⟨a, b⟩ := atan_lip hs hy l; have := qeps_nonneg n; unfold qsub at *; rat_linarith

theorem atan_hi {y ys e : QExpr} {n : Nat} (hy : InR y n) (hs : InR ys n) (h : qle (qsub y ys) e) (he : qle qzero e) :
    qle (atseq y n) (qadd (atseq ys n) (qadd e (qeps n))) := by
  cases qle_total y ys with
  | inl l => obtain ⟨a, b⟩ := atan_lip hy hs l; have := qeps_nonneg n; unfold qsub at *; rat_linarith
  | inr l => obtain ⟨a, b⟩ := atan_lip hs hy l; unfold qsub at *; rat_linarith

/-- THE VALUE: an operational real read in `[lu, hu]` has its `atan` in `[Ll, Lh]` once `atan lu ≥ Ll` and
`atan hu ≤ Lh` (monotone at every index, slope at most 1). -/
theorem Ev_atan {y : Nat → QExpr} {lu hu Ll Lh : QExpr} (hy : Ev y lu hu)
    (hl : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub Ll (qeps k)) (atseq lu n))
    (hh : ∀ k, ∃ N, ∀ n, N ≤ n → qle (atseq hu n) (qadd Lh (qeps k))) :
    Ev (fun n => atseq (y n) n) Ll Lh := by
  obtain ⟨Ka, a1, a2⟩ := ZExp.exists_nat_bound lu
  obtain ⟨Kb, b1, b2⟩ := ZExp.exists_nat_bound hu
  have a1' : qle lu (qnat Ka) := by unfold qsub at a1; rat_linarith
  have a2' : qle (qneg (qnat Ka)) lu := by unfold qsub at a2; rat_linarith
  have b1' : qle hu (qnat Kb) := by unfold qsub at b1; rat_linarith
  have b2' : qle (qneg (qnat Kb)) hu := by unfold qsub at b2; rat_linarith
  have lw : ZTrig.Ab lu (qnat (Ka + Kb + 1)) :=
    ab_le ⟨a2', a1'⟩ (Nat.le_trans (Nat.le_add_right Ka Kb) (Nat.le_succ _))
  have hw : ZTrig.Ab hu (qnat (Ka + Kb + 1)) :=
    ab_le ⟨b2', b1'⟩ (Nat.le_trans (Nat.le_add_left Kb Ka) (Nat.le_succ _))
  refine ZTrig.Ev_of_sides (fun k => ?_) (fun k => ?_)
  · obtain ⟨N1, h1⟩ := hy (k + 2)
    obtain ⟨N2, h2⟩ := hl (k + 1)
    refine ⟨N1 + (N2 + ((Ka + Kb + 1 + 2) + (k + 2))), fun n hn => ?_⟩
    obtain ⟨y1, y2⟩ := h1 n (le4a hn)
    have L := h2 n (le4b hn)
    have hε := eps_of_le (le4d hn)
    have s1 := qeps_succ_add (k + 1); have s0 := qeps_succ_add k
    have q1 := ZTrig.qeps_le_one (k + 2)
    have yw : ZTrig.Ab (y n) (qnat (Ka + Kb + 1)) := ab_window a2' a1' b2' b1' (by unfold qsub at *; rat_linarith)
      (by unfold qsub at *; rat_linarith)
    have lo := atan_lo (inR_of yw (le4c hn)) (inR_of lw (le4c hn)) (e := qeps (k + 2))
      (by unfold qsub at *; rat_linarith) (qeps_nonneg _)
    show qle (qsub Ll (qeps k)) (atseq (y n) n)
    unfold qsub at *; rat_linarith
  · obtain ⟨N1, h1⟩ := hy (k + 2)
    obtain ⟨N2, h2⟩ := hh (k + 1)
    refine ⟨N1 + (N2 + ((Ka + Kb + 1 + 2) + (k + 2))), fun n hn => ?_⟩
    obtain ⟨y1, y2⟩ := h1 n (le4a hn)
    have L := h2 n (le4b hn)
    have hε := eps_of_le (le4d hn)
    have s1 := qeps_succ_add (k + 1); have s0 := qeps_succ_add k
    have q1 := ZTrig.qeps_le_one (k + 2)
    have yw : ZTrig.Ab (y n) (qnat (Ka + Kb + 1)) := ab_window a2' a1' b2' b1' (by unfold qsub at *; rat_linarith)
      (by unfold qsub at *; rat_linarith)
    have hi := atan_hi (inR_of yw (le4c hn)) (inR_of hw (le4c hn)) (e := qeps (k + 2))
      (by unfold qsub at *; rat_linarith) (qeps_nonneg _)
    show qle (atseq (y n) n) (qadd Lh (qeps k))
    unfold qsub at *; rat_linarith

/-! ## The answers at two indices are close -/

/-- The points `i·Δ`, `Δ = y*·ε_m`, and the fixed Riemann sum `Σ_{i' < i} Δ·ψ(i'Δ)`. -/
def rpt (ys : QExpr) (m : Nat) : Nat → QExpr
  | 0 => qzero
  | i + 1 => qadd (rpt ys m i) (qmul ys (qeps m))

def rsum (ys : QExpr) (m : Nat) : Nat → QExpr
  | 0 => qzero
  | i + 1 => qadd (rsum ys m i) (qmul (qmul ys (qeps m)) (psi (rpt ys m i)))

theorem rpt_eq (ys : QExpr) (m : Nat) : ∀ i, qEq (rpt ys m i) (qmul (qmul (qnat i) (qeps m)) ys)
  | 0 => by
      show qEq qzero _
      have e : qEq (qmul (qmul (qnat 0) (qeps m)) ys) (qmul (qmul qzero (qeps m)) ys) :=
        qmul_respects (qmul_respects qnat_zero (qEq_refl _)) (qEq_refl _)
      exact qEq_trans (by rat_ring) (qEq_symm e)
  | i + 1 => by
      have ih := rpt_eq ys m i
      have e : qEq (qmul (qmul (qnat (i + 1)) (qeps m)) ys) (qmul (qmul (qadd (qnat i) qone) (qeps m)) ys) :=
        qmul_respects (qmul_respects (qnat_succ i) (qEq_refl _)) (qEq_refl _)
      show qEq (qadd (rpt ys m i) (qmul ys (qeps m))) _
      have e2 : qEq (qmul (qmul (qadd (qnat i) qone) (qeps m)) ys)
          (qadd (qmul (qmul (qnat i) (qeps m)) ys) (qmul ys (qeps m))) := by rat_ring
      exact qEq_trans (qadd_respects ih (qEq_refl _)) (qEq_symm (qEq_trans e e2))

/-- `qnat (2^m)·ε_m = 1`. -/
theorem pow_eps (m : Nat) : qEq (qmul (qnat (2 ^ m)) (qeps m)) qone := by
  have h := qpow2_mul_eps m 0
  rw [Nat.zero_add] at h
  exact qEq_trans (qmul_respects (qnat_pow2 m) (qEq_refl _)) (qEq_trans h qeps_zero)

theorem rpt_ab {ys Y : QExpr} (hy : ZTrig.Ab ys Y) (Y0 : qle qzero Y) (m : Nat) {i : Nat} (hi : i ≤ 2 ^ m) :
    ZTrig.Ab (rpt ys m i) Y := by
  have e := rpt_eq ys m i
  have pe := pow_eps m
  have c0 : qle qzero (qmul (qnat i) (qeps m)) := qmul_nonneg (qnat_nonneg i) (qeps_nonneg m)
  have c1 : qle (qmul (qnat i) (qeps m)) qone := by
    have := ZExp.scale (qnat_mono hi) (qeps_nonneg m); rat_linarith
  obtain ⟨y1, y2⟩ := hy
  have f1 := scale_l y2 c0
  have f2 := scale_l y1 c0
  have f3 := ZExp.scale c1 Y0
  have o := qone_mul Y
  have o2 : qEq (qmul (qmul (qnat i) (qeps m)) (qneg Y)) (qneg (qmul (qmul (qnat i) (qeps m)) Y)) := by rat_ring
  generalize qmul (qmul (qnat i) (qeps m)) ys = P at *
  generalize qmul (qmul (qnat i) (qeps m)) Y = Q at *
  generalize qmul (qmul (qnat i) (qeps m)) (qneg Y) = Q' at *
  generalize qmul qone Y = Y1 at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem sq_le {x Y : QExpr} (h : ZTrig.Ab x Y) : qle (qmul x x) (qmul Y Y) := by
  obtain ⟨h1, h2⟩ := h
  have f := qmul_nonneg (by unfold qsub; rat_linarith : qle qzero (qsub Y x)) (by rat_linarith : qle qzero (qadd Y x))
  have e : qEq (qmul (qsub Y x) (qadd Y x)) (qsub (qmul Y Y) (qmul x x)) := by unfold qsub; rat_ring
  unfold qsub at *; rat_linarith

/-- THE FIXED RIEMANN SUM: from some index on, `atan y*` is within `ε_k + ε_n` of one rational sum. -/
theorem atan_riemann (ys : QExpr) : ∀ k, ∃ S N, ∀ n, N ≤ n →
    ZTrig.Ab (qsub (atseq ys n) S) (qadd (qadd (qeps k) (qeps k)) (qeps n)) := by
  intro k
  obtain ⟨K0, c1, c2⟩ := ZExp.exists_nat_bound ys
  have hy : ZTrig.Ab ys (qnat K0) := by unfold qsub at c1 c2; exact ⟨by rat_linarith, by rat_linarith⟩
  have Y0 := qnat_nonneg K0
  obtain ⟨H, H0, hst⟩ := ustep_atan Y0 Y0
  obtain ⟨B, hB⟩ := eps_scaledA (qmul_nonneg (qmul_self_nonneg (qnat K0)) H0)
  -- m = k + B; the step tolerance ε_{k+m}
  obtain ⟨N0, hN0⟩ := hst (k + (k + B))
  refine ⟨rsum ys (k + B) (2 ^ (k + B)), N0 + (K0 + 2), fun n hn => ?_⟩
  have hn0 : N0 ≤ n := Nat.le_trans (Nat.le_add_right _ _) hn
  have hn1 : K0 + 2 ≤ n := Nat.le_trans (Nat.le_add_left _ _) hn
  generalize hm : k + B = m at *
  have Δab : ZTrig.Ab (qmul ys (qeps m)) (qnat K0) := by
    obtain ⟨y1, y2⟩ := hy
    have q1 := ZTrig.qeps_le_one m
    have e0 := qeps_nonneg m
    have f1 := scale_l y2 e0; have f2 := scale_l y1 e0
    have f3 := ZExp.scale q1 Y0
    have c := qmul_comm ys (qeps m)
    have o := qone_mul (qnat K0)
    have o2 : qEq (qmul (qeps m) (qneg (qnat K0))) (qneg (qmul (qeps m) (qnat K0))) := by rat_ring
    have c2 := qmul_comm (qeps m) (qnat K0)
    generalize qmul ys (qeps m) = P at *; generalize qmul (qeps m) ys = P' at *
    generalize qmul (qeps m) (qnat K0) = Q at *; generalize qmul (qnat K0) (qeps m) = Q2 at *
    generalize qmul (qeps m) (qneg (qnat K0)) = Q' at *; generalize qmul qone (qnat K0) = Y1 at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  -- the induction along the points
  have ind : ∀ i, i ≤ 2 ^ m → ZTrig.Ab (qsub (atseq (rpt ys m i) n) (rsum ys m i))
      (qmul (qnat i) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H))) := by
    intro i
    induction i with
    | zero =>
        intro _
        have z := atseq_zero n
        have e : qEq (qmul (qnat 0) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H))) qzero :=
          qEq_trans (qmul_respects qnat_zero (qEq_refl _)) (by rat_ring)
        show ZTrig.Ab (qsub (atseq qzero n) qzero) _
        generalize qmul (qnat 0) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = Z at *
        unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
    | succ i ih =>
        intro hi
        have ih' := ih (Nat.le_of_succ_le hi)
        have st := hN0 n hn0 (rpt ys m i) (qmul ys (qeps m)) (rpt_ab hy Y0 m (Nat.le_of_succ_le hi)) Δab
        have q := qnat_succ i
        have e : qEq (qmul (qnat (i + 1)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)))
            (qadd (qmul (qnat i) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)))
              (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H))) :=
          qEq_trans (qmul_respects q (qEq_refl _)) (by rat_ring)
        show ZTrig.Ab (qsub (atseq (qadd (rpt ys m i) (qmul ys (qeps m))) n)
          (qadd (rsum ys m i) (qmul (qmul ys (qeps m)) (psi (rpt ys m i))))) _
        generalize qmul (qnat (i + 1)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = T1 at *
        generalize qmul (qnat i) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = T0 at *
        generalize qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H) = T at *
        obtain ⟨a1, a2⟩ := ih'; obtain ⟨b1, b2⟩ := st
        unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have top := ind (2 ^ m) (Nat.le_refl _)
  -- 2^m·ε_{k+m} = ε_k; 2^m·Δ²·H = y*²·H·ε_m ≤ ε_k
  have pe := pow_eps m
  have pk : qEq (qmul (qnat (2 ^ m)) (qeps (k + m))) (qeps k) :=
    qEq_trans (qmul_respects (qnat_pow2 m) (qEq_refl _)) (qpow2_mul_eps m k)
  have sq := sq_le hy
  have hb := hB k
  rw [hm] at hb
  have f1 := ZExp.scale sq H0
  have f2 := scale_l f1 (qeps_nonneg m)
  have e1 : qEq (qmul (qnat (2 ^ m)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)))
      (qadd (qmul (qnat (2 ^ m)) (qeps (k + m)))
        (qmul (qmul (qnat (2 ^ m)) (qeps m)) (qmul (qeps m) (qmul (qmul ys ys) H)))) := by rat_ring
  have e2 : qEq (qmul (qmul (qnat (2 ^ m)) (qeps m)) (qmul (qeps m) (qmul (qmul ys ys) H)))
      (qmul qone (qmul (qeps m) (qmul (qmul ys ys) H))) := qmul_respects pe (qEq_refl _)
  have e3 := qone_mul (qmul (qeps m) (qmul (qmul ys ys) H))
  have e4 : qEq (qmul (qeps m) (qmul (qmul (qnat K0) (qnat K0)) H)) (qmul (qeps m) (qmul (qmul (qnat K0) (qnat K0)) H)) :=
    qEq_refl _
  -- the last point is y* itself
  have last : qEq (rpt ys m (2 ^ m)) ys :=
    qEq_trans (rpt_eq ys m (2 ^ m)) (qEq_trans (qmul_respects pe (qEq_refl _)) (qone_mul ys))
  have nr := atan_near (e := qzero) (inR_of hy hn1) (inR_of (rpt_ab hy Y0 m (Nat.le_refl _)) hn1)
    (by have := qle_of_qEq last; have := qle_of_qEq (qEq_symm last); unfold qsub; rat_linarith)
    (by have := qle_of_qEq last; have := qle_of_qEq (qEq_symm last); unfold qsub; rat_linarith)
  generalize qmul (qnat (2 ^ m)) (qadd (qeps (k + m)) (qmul (qmul (qmul ys (qeps m)) (qmul ys (qeps m))) H)) = T at *
  generalize qmul (qmul (qnat (2 ^ m)) (qeps m)) (qmul (qeps m) (qmul (qmul ys ys) H)) = U at *
  generalize hV : qmul (qeps m) (qmul (qmul ys ys) H) = V at *
  obtain ⟨t1, t2⟩ := top; obtain ⟨r1, r2⟩ := nr
  have v0 : qle qzero V := by rw [← hV]; exact qmul_nonneg (qeps_nonneg m) (qmul_nonneg (qmul_self_nonneg ys) H0)
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem close_of_two {A Bv S E e : QExpr} (ha : ZTrig.Ab (qsub A S) E) (hb : ZTrig.Ab (qsub Bv S) E)
    (he : qle (qadd E E) e) : qclose A Bv e := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  unfold qclose; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `atan` OF AN OPERATIONAL REAL: the answers at two indices are close. -/
theorem atan_cauchy {y : Nat → QExpr} (hc : Cauchy y) : Cauchy (fun n => atseq (y n) n) := by
  intro k
  obtain ⟨N1, h1⟩ := hc (k + 4)
  obtain ⟨K0, c1, c2⟩ := ZExp.exists_nat_bound (y N1)
  obtain ⟨S, N2, h2⟩ := atan_riemann (y N1) (k + 4)
  have hs : ZTrig.Ab (y N1) (qnat (K0 + 1)) := by
    have := qnat_succ K0; have o := qle_of_qlt qone_pos
    unfold qsub at c1 c2; exact ⟨by rat_linarith, by rat_linarith⟩
  have e4 := qeps_succ_add (k + 3); have e3 := qeps_succ_add (k + 2)
  have e2 := qeps_succ_add (k + 1); have e1 := qeps_succ_add k
  have one := ZTrig.qeps_le_one (k + 4)
  -- each index's answer is within 5·ε_{k+4} of S
  have near : ∀ a, N1 + (N2 + ((K0 + 1 + 1 + 2) + (k + 4))) ≤ a →
      ZTrig.Ab (qsub (atseq (y a) a) S) (qadd (qadd (qadd (qeps (k + 4)) (qeps (k + 4))) (qadd (qeps (k + 4)) (qeps (k + 4))))
        (qeps (k + 4))) := by
    intro a ha
    obtain ⟨q1, q2⟩ := h1 a N1 (le4a ha) (Nat.le_refl _)
    have ya : ZTrig.Ab (y a) (qnat (K0 + 1 + 1)) := by
      have := qnat_succ (K0 + 1); obtain ⟨s1, s2⟩ := hs; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
    have hsa : ZTrig.Ab (y N1) (qnat (K0 + 1 + 1)) := ab_le hs (Nat.le_succ _)
    have ra := inR_of ya (le4c ha)
    have rs := inR_of hsa (le4c ha)
    have nr := atan_near (e := qeps (k + 4)) ra rs (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith)
    have rm := h2 a (le4b ha)
    have ea := eps_of_le (le4d ha)
    obtain ⟨n1, n2⟩ := nr; obtain ⟨m1, m2⟩ := rm
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  refine ⟨N1 + (N2 + ((K0 + 1 + 1 + 2) + (k + 4))), fun a b ha hb => ?_⟩
  obtain ⟨a1, a2⟩ := near a ha; obtain ⟨b1, b2⟩ := near b hb
  exact close_of_two ⟨a1, a2⟩ ⟨b1, b2⟩ (by
    have := qeps_nonneg (k + 4)
    rat_linarith)

theorem acnt_respects {y y' : QExpr} (e : qEq y y') (n : Nat) : ∀ j, acnt y n j = acnt y' n j
  | 0 => rfl
  | j + 1 => by
      cases qle.decidable (gpt n (j + 1)) y with
      | isTrue h =>
          have h' : qle (gpt n (j + 1)) y' := qle_trans h (qle_of_qEq e)
          rw [acnt_true h, acnt_true h', acnt_respects e n j]
      | isFalse h =>
          have h' : ¬ qle (gpt n (j + 1)) y' := fun h2 => h (qle_trans h2 (qle_of_qEq (qEq_symm e)))
          rw [acnt_false h, acnt_false h', acnt_respects e n j]

theorem atseq_respects {y y' : QExpr} (e : qEq y y') (n : Nat) : qEq (atseq y n) (atseq y' n) := by
  unfold atseq; rw [acnt_respects e n (gridK n)]; exact qEq_refl _

/-- CRUDE: `|atan y| ≤ |y|` (slope at most 1, `atan 0 = 0`) — the value reading a Taylor step needs at `k = 0`. -/
theorem atan_crude {y Y : QExpr} (h : ZTrig.Ab y Y) :
    (∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub (qneg Y) (qeps k)) (atseq y n)) ∧
    (∀ k, ∃ N, ∀ n, N ≤ n → qle (atseq y n) (qadd Y (qeps k))) := by
  obtain ⟨K0, c1, c2⟩ := ZExp.exists_nat_bound y
  have hy : ZTrig.Ab y (qnat K0) := by unfold qsub at c1 c2; exact ⟨by rat_linarith, by rat_linarith⟩
  have h0 : ZTrig.Ab qzero (qnat K0) := ⟨by have := qnat_nonneg K0; rat_linarith, qnat_nonneg K0⟩
  obtain ⟨y1, y2⟩ := h
  refine ⟨fun k => ⟨K0 + 2 + k, fun n hn => ?_⟩, fun k => ⟨K0 + 2 + k, fun n hn => ?_⟩⟩ <;>
  · have r1 := inR_of hy (Nat.le_trans (Nat.le_add_right _ _) hn)
    have r0 := inR_of h0 (Nat.le_trans (Nat.le_add_right _ _) hn)
    have z := atseq_zero n
    have he := eps_of_le (Nat.le_trans (Nat.le_add_left k (K0 + 2)) hn)
    obtain ⟨a, b⟩ := atan_near (e := Y) r1 r0 (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
    unfold qsub at *; first | rat_linarith

end ZAtan

#print axioms ZAtan.acnt_spec
#print axioms ZAtan.acnt_bracket
#print axioms ZAtan.acnt_mono
#print axioms ZAtan.psi_lip
#print axioms ZAtan.psi_anti_pos
#print axioms ZAtan.psi_mono_neg
#print axioms ZAtan.psum_block
#print axioms ZAtan.atan_window
#print axioms ZAtan.atan_lip
#print axioms ZAtan.atan_step_core
#print axioms ZAtan.inR_of
#print axioms ZAtan.ustep_atan
#print axioms ZAtan.atseq_zero
#print axioms ZAtan.Ev_atan
#print axioms ZAtan.atan_riemann
#print axioms ZAtan.atan_cauchy
#print axioms ZAtan.atseq_respects
#print axioms ZAtan.atan_crude
