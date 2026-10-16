import ZSlopeSqrt

/-!
# ZExp2 — the second-order step of `exp`, from its first-order slopes, on a grid. Zero axioms.

`R(a, b) = E(b) − E(a) − E(a)·(b − a)` — the remainder the Taylor leaf of order 2 needs for `exp`. Classically
`E(ξ)·(b − a)²/2`. Here from `ZExp.E_slope` alone (`(y − x)(E(x) − t) ≤ E(y) − E(x) ≤ (y − x)·E(y)`), summed
along `N` steps of `δ`: the steps' slopes grow at most as `E` does, so the sum is an arithmetic series —
`δ²·N(N+1)/2`. The grid lemmas below are pure algebra over any `F` with those step bounds:

  * `grid_up`, `grid_lo` — from `a` upwards: `2R ≤ M·δ²·N(N+1)`, `2R ≥ (F(a) − t)·δ²·N(N−1) − 2Nδ·t`;
  * `grid_dn_up`, `grid_dn_lo` — from `a` downwards (`b < a`).

With `Nδ = |b − a|` that is `2R ∈ [(E_min − t)(Δ² − |Δ|δ) − 2|Δ|t, E_max(Δ² + |Δ|δ) + 2|Δ|t]`: as `N` and the
index grow, `Δ²·[E_min, E_max]` — the kernel's `exp` coefficient `E·U1²/2`.
-/

namespace ZExp2

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn

/-- The grid point `a + c·δ`. -/
def gp (a δ c : QExpr) : QExpr := qadd a (qmul c δ)

/-- The grid point `a − c·δ`. -/
def gm (a δ c : QExpr) : QExpr := qsub a (qmul c δ)

def two : QExpr := qadd qone qone

theorem mul_qeq_zero {x y : QExpr} (h : qEq x qzero) : qEq (qmul x y) qzero :=
  qEq_trans (qmul_respects h (qEq_refl y)) (qzero_mul y)

theorem gp_zero (a δ : QExpr) : qEq (gp a δ (qnat 0)) a := by
  unfold gp; have := mul_qeq_zero (y := δ) qnat_zero; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gm_zero (a δ : QExpr) : qEq (gm a δ (qnat 0)) a := by
  unfold gm qsub; have := mul_qeq_zero (y := δ) qnat_zero; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- UPWARDS, FROM ABOVE: each step `F(x_{j+1}) − F(x_j) ≤ δ·F(x_{j+1})`, the climb from `a` `≤ (j+1)δ·F(x_{j+1})`,
the values `≤ M` — then `2(F(x_N) − F(a) − Nδ·F(a)) ≤ δ²M·N(N+1)`. -/
theorem grid_up (F : QExpr → QExpr) (hF : ∀ x y, qEq x y → qEq (F x) (F y)) {a δ M : QExpr} (hδ : qle qzero δ) :
    ∀ N : Nat, (∀ j, j < N →
      qle (qsub (F (gp a δ (qnat (j + 1)))) (F (gp a δ (qnat j)))) (qmul δ (F (gp a δ (qnat (j + 1))))) ∧
      qle (qsub (F (gp a δ (qnat (j + 1)))) (F a)) (qmul (qmul (qnat (j + 1)) δ) (F (gp a δ (qnat (j + 1))))) ∧
      qle (F (gp a δ (qnat (j + 1)))) M) →
    qle (qmul two (qsub (qsub (F (gp a δ (qnat N))) (F a)) (qmul (qmul (qnat N) δ) (F a))))
        (qmul (qmul (qmul δ δ) M) (qmul (qnat N) (qnat (N + 1))))
  | 0, _ => by
      have f0 := hF _ _ (gp_zero a δ)
      have z1 : qEq (qmul (qmul (qnat 0) δ) (F a)) qzero := mul_qeq_zero (mul_qeq_zero qnat_zero)
      have z2 : qEq (qmul (qmul (qmul δ δ) M) (qmul (qnat 0) (qnat (0 + 1)))) qzero :=
        qEq_trans (qmul_respects (qEq_refl _) (mul_qeq_zero qnat_zero)) (qmul_zero _)
      unfold two qsub at *; rat_linarith
  | N + 1, h => by
      have ih := grid_up F hF hδ N (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N)))
      obtain ⟨s1, s2, s3⟩ := h N (Nat.lt_succ_self N)
      have hc1 := qnat_succ N
      have hc2 := qnat_succ (N + 1)
      have c1δ : qle qzero (qmul (qnat (N + 1)) δ) := qmul_nonneg (qnat_nonneg _) hδ
      have f1 := scale_l s3 c1δ
      have hx : qle (F (gp a δ (qnat (N + 1)))) (qadd (F a) (qmul (qmul (qnat (N + 1)) δ) M)) := by
        unfold qsub at *; rat_linarith
      have f2 := scale_l hx hδ
      have i1 : qEq (qmul (qmul (qnat (N + 1)) δ) (F a)) (qmul (qmul (qadd (qnat N) qone) δ) (F a)) :=
        qmul_respects (qmul_respects hc1 (qEq_refl δ)) (qEq_refl _)
      have i2 : qEq (qmul (qmul (qmul δ δ) M) (qmul (qnat (N + 1)) (qnat (N + 1 + 1))))
          (qmul (qmul (qmul δ δ) M) (qmul (qnat (N + 1)) (qadd (qnat (N + 1)) qone))) :=
        qmul_respects (qEq_refl _) (qmul_respects (qEq_refl _) hc2)
      have i3 : qEq (qmul (qmul (qmul δ δ) M) (qmul (qnat N) (qnat (N + 1))))
          (qmul (qmul (qmul δ δ) M) (qmul (qsub (qnat (N + 1)) qone) (qnat (N + 1)))) :=
        qmul_respects (qEq_refl _) (qmul_respects (by unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith))
          (qEq_refl _))
      unfold two qsub at *; rat_linarith

/-- UPWARDS, FROM BELOW: each step `F(x_{j+1}) − F(x_j) ≥ δ·(F(x_j) − t)`, the climb `F(x_j) − F(a) ≥ jδ·(F(a) − t)`
— then `2(F(x_N) − F(a) − Nδ·F(a)) ≥ δ²(F(a) − t)·N(N−1) − 2Nδ·t`. -/
theorem grid_lo (F : QExpr → QExpr) (hF : ∀ x y, qEq x y → qEq (F x) (F y)) {a δ t : QExpr} (hδ : qle qzero δ) :
    ∀ N : Nat, (∀ j, j < N →
      qle (qmul δ (qsub (F (gp a δ (qnat j))) t)) (qsub (F (gp a δ (qnat (j + 1)))) (F (gp a δ (qnat j)))) ∧
      qle (qmul (qmul (qnat j) δ) (qsub (F a) t)) (qsub (F (gp a δ (qnat j))) (F a))) →
    qle (qsub (qmul (qmul (qmul δ δ) (qsub (F a) t)) (qmul (qnat N) (qsub (qnat N) qone)))
          (qmul two (qmul (qmul (qnat N) δ) t)))
        (qmul two (qsub (qsub (F (gp a δ (qnat N))) (F a)) (qmul (qmul (qnat N) δ) (F a))))
  | 0, _ => by
      have f0 := hF _ _ (gp_zero a δ)
      have z1 : qEq (qmul (qmul (qnat 0) δ) (F a)) qzero := mul_qeq_zero (mul_qeq_zero qnat_zero)
      have z2 : qEq (qmul (qmul (qmul δ δ) (qsub (F a) t)) (qmul (qnat 0) (qsub (qnat 0) qone))) qzero :=
        qEq_trans (qmul_respects (qEq_refl _) (mul_qeq_zero qnat_zero)) (qmul_zero _)
      have z3 : qEq (qmul (qmul (qnat 0) δ) t) qzero := mul_qeq_zero (mul_qeq_zero qnat_zero)
      unfold two qsub at *; rat_linarith
  | N + 1, h => by
      have ih := grid_lo F hF hδ N (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N)))
      obtain ⟨s1, s2⟩ := h N (Nat.lt_succ_self N)
      have hc1 := qnat_succ N
      have hy : qle (qadd (F a) (qmul (qmul (qnat N) δ) (qsub (F a) t))) (F (gp a δ (qnat N))) := by
        unfold qsub at *; rat_linarith
      have f2 := scale_l hy hδ
      have i1 : qEq (qmul (qmul (qnat (N + 1)) δ) (F a)) (qmul (qmul (qadd (qnat N) qone) δ) (F a)) :=
        qmul_respects (qmul_respects hc1 (qEq_refl δ)) (qEq_refl _)
      have i1t : qEq (qmul (qmul (qnat (N + 1)) δ) t) (qmul (qmul (qadd (qnat N) qone) δ) t) :=
        qmul_respects (qmul_respects hc1 (qEq_refl δ)) (qEq_refl _)
      have i2 : qEq (qmul (qmul (qmul δ δ) (qsub (F a) t)) (qmul (qnat (N + 1)) (qsub (qnat (N + 1)) qone)))
          (qmul (qmul (qmul δ δ) (qsub (F a) t)) (qmul (qadd (qnat N) qone) (qnat N))) :=
        qmul_respects (qEq_refl _) (qmul_respects hc1 (by unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)))
      unfold two qsub at *; rat_linarith

/-- DOWNWARDS, FROM ABOVE (`z_j = a − jδ`): each step `F(z_j) − F(z_{j+1}) ≥ δ·(F(z_{j+1}) − t)`, the drop
`F(a) − F(z_{j+1}) ≤ (j+1)δ·F(a)` — then `2(F(z_N) − F(a) + Nδ·F(a)) ≤ δ²·F(a)·N(N+1) + 2Nδ·t`. -/
theorem grid_dn_up (F : QExpr → QExpr) (hF : ∀ x y, qEq x y → qEq (F x) (F y)) {a δ t : QExpr} (hδ : qle qzero δ) :
    ∀ N : Nat, (∀ j, j < N →
      qle (qmul δ (qsub (F (gm a δ (qnat (j + 1)))) t)) (qsub (F (gm a δ (qnat j))) (F (gm a δ (qnat (j + 1))))) ∧
      qle (qsub (F a) (F (gm a δ (qnat (j + 1))))) (qmul (qmul (qnat (j + 1)) δ) (F a))) →
    qle (qmul two (qadd (qsub (F (gm a δ (qnat N))) (F a)) (qmul (qmul (qnat N) δ) (F a))))
        (qadd (qmul (qmul (qmul δ δ) (F a)) (qmul (qnat N) (qnat (N + 1)))) (qmul two (qmul (qmul (qnat N) δ) t)))
  | 0, _ => by
      have f0 := hF _ _ (gm_zero a δ)
      have z1 : qEq (qmul (qmul (qnat 0) δ) (F a)) qzero := mul_qeq_zero (mul_qeq_zero qnat_zero)
      have z2 : qEq (qmul (qmul (qmul δ δ) (F a)) (qmul (qnat 0) (qnat (0 + 1)))) qzero :=
        qEq_trans (qmul_respects (qEq_refl _) (mul_qeq_zero qnat_zero)) (qmul_zero _)
      have z3 : qEq (qmul (qmul (qnat 0) δ) t) qzero := mul_qeq_zero (mul_qeq_zero qnat_zero)
      unfold two qsub at *; rat_linarith
  | N + 1, h => by
      have ih := grid_dn_up F hF hδ N (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N)))
      obtain ⟨s1, s2⟩ := h N (Nat.lt_succ_self N)
      have hc1 := qnat_succ N
      have hc2 := qnat_succ (N + 1)
      have hz : qle (qsub (qsub (F a) (qmul (qmul (qnat (N + 1)) δ) (F a))) t)
          (qsub (F (gm a δ (qnat (N + 1)))) t) := by unfold qsub at *; rat_linarith
      have f2 := scale_l hz hδ
      have i1 : qEq (qmul (qmul (qnat (N + 1)) δ) (F a)) (qmul (qmul (qadd (qnat N) qone) δ) (F a)) :=
        qmul_respects (qmul_respects hc1 (qEq_refl δ)) (qEq_refl _)
      have i1t : qEq (qmul (qmul (qnat (N + 1)) δ) t) (qmul (qmul (qadd (qnat N) qone) δ) t) :=
        qmul_respects (qmul_respects hc1 (qEq_refl δ)) (qEq_refl _)
      have i2 : qEq (qmul (qmul (qmul δ δ) (F a)) (qmul (qnat (N + 1)) (qnat (N + 1 + 1))))
          (qmul (qmul (qmul δ δ) (F a)) (qmul (qnat (N + 1)) (qadd (qnat (N + 1)) qone))) :=
        qmul_respects (qEq_refl _) (qmul_respects (qEq_refl _) hc2)
      have i3 : qEq (qmul (qmul (qmul δ δ) (F a)) (qmul (qnat N) (qnat (N + 1))))
          (qmul (qmul (qmul δ δ) (F a)) (qmul (qsub (qnat (N + 1)) qone) (qnat (N + 1)))) :=
        qmul_respects (qEq_refl _) (qmul_respects (by unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith))
          (qEq_refl _))
      unfold two qsub at *; rat_linarith

/-- DOWNWARDS, FROM BELOW: each step `F(z_j) − F(z_{j+1}) ≤ δ·F(z_j)`, the drop `F(a) − F(z_j) ≥ jδ·(m − t)` —
then `2(F(z_N) − F(a) + Nδ·F(a)) ≥ δ²(m − t)·N(N−1)`. -/
theorem grid_dn_lo (F : QExpr → QExpr) (hF : ∀ x y, qEq x y → qEq (F x) (F y)) {a δ t m : QExpr} (hδ : qle qzero δ) :
    ∀ N : Nat, (∀ j, j < N →
      qle (qsub (F (gm a δ (qnat j))) (F (gm a δ (qnat (j + 1))))) (qmul δ (F (gm a δ (qnat j)))) ∧
      qle (qmul (qmul (qnat j) δ) (qsub m t)) (qsub (F a) (F (gm a δ (qnat j))))) →
    qle (qmul (qmul (qmul δ δ) (qsub m t)) (qmul (qnat N) (qsub (qnat N) qone)))
        (qmul two (qadd (qsub (F (gm a δ (qnat N))) (F a)) (qmul (qmul (qnat N) δ) (F a))))
  | 0, _ => by
      have f0 := hF _ _ (gm_zero a δ)
      have z1 : qEq (qmul (qmul (qnat 0) δ) (F a)) qzero := mul_qeq_zero (mul_qeq_zero qnat_zero)
      have z2 : qEq (qmul (qmul (qmul δ δ) (qsub m t)) (qmul (qnat 0) (qsub (qnat 0) qone))) qzero :=
        qEq_trans (qmul_respects (qEq_refl _) (mul_qeq_zero qnat_zero)) (qmul_zero _)
      unfold two qsub at *; rat_linarith
  | N + 1, h => by
      have ih := grid_dn_lo F hF hδ N (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N)))
      obtain ⟨s1, s2⟩ := h N (Nat.lt_succ_self N)
      have hc1 := qnat_succ N
      have hz : qle (F (gm a δ (qnat N))) (qsub (F a) (qmul (qmul (qnat N) δ) (qsub m t))) := by
        unfold qsub at *; rat_linarith
      have f2 := scale_l hz hδ
      have i1 : qEq (qmul (qmul (qnat (N + 1)) δ) (F a)) (qmul (qmul (qadd (qnat N) qone) δ) (F a)) :=
        qmul_respects (qmul_respects hc1 (qEq_refl δ)) (qEq_refl _)
      have i2 : qEq (qmul (qmul (qmul δ δ) (qsub m t)) (qmul (qnat (N + 1)) (qsub (qnat (N + 1)) qone)))
          (qmul (qmul (qmul δ δ) (qsub m t)) (qmul (qadd (qnat N) qone) (qnat N))) :=
        qmul_respects (qEq_refl _) (qmul_respects hc1 (by unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)))
      unfold two qsub at *; rat_linarith

/-! ## `exp` at a fixed index -/

theorem between_close {a b x R : QExpr} (ha : qclose a qzero R) (hb : qclose b qzero R) (h1 : qle a x) (h2 : qle x b) :
    qclose x qzero R := by
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  show qle (qsub x qzero) R ∧ qle (qneg R) (qsub x qzero)
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem gp_succ (a δ : QExpr) (j : Nat) : qEq (qsub (gp a δ (qnat (j + 1))) (gp a δ (qnat j))) δ := by
  have e := qmul_respects (qnat_succ j) (qEq_refl δ)
  unfold gp qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gp_from (a δ c : QExpr) : qEq (qsub (gp a δ c) a) (qmul c δ) := by
  unfold gp qsub; rat_ring

/-- The grid points `a + jδ`, `j ≤ N`, `Nδ = b − a`, lie in `[a, b]`. -/
theorem gp_in {a b δ : QExpr} {N j : Nat} (hδ : qle qzero δ) (hN : qEq (qmul (qnat N) δ) (qsub b a)) (hj : j ≤ N) :
    qle a (gp a δ (qnat j)) ∧ qle (gp a δ (qnat j)) b := by
  have f0 := qmul_nonneg (qnat_nonneg j) hδ
  have f1 := ZExp.scale (qnat_mono hj) hδ
  unfold gp qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `δ²·N(N+1) = (Nδ)² + (Nδ)·δ`, and `δ²·N(N−1) = (Nδ)² − (Nδ)·δ`. -/
theorem nn_succ (δ X : QExpr) (N : Nat) :
    qEq (qmul (qmul (qmul δ δ) X) (qmul (qnat N) (qnat (N + 1))))
      (qmul X (qadd (qmul (qmul (qnat N) δ) (qmul (qnat N) δ)) (qmul (qmul (qnat N) δ) δ))) := by
  have e := qmul_respects (qEq_refl (qmul (qmul δ δ) X)) (qmul_respects (qEq_refl (qnat N)) (qnat_succ N))
  exact qEq_trans e (by rat_ring)

theorem nn_pred (δ X : QExpr) (N : Nat) :
    qEq (qmul (qmul (qmul δ δ) X) (qmul (qnat N) (qsub (qnat N) qone)))
      (qmul X (qsub (qmul (qmul (qnat N) δ) (qmul (qnat N) δ)) (qmul (qmul (qnat N) δ) δ))) := by
  unfold qsub; rat_ring

/-- THE SECOND-ORDER STEP OF `exp`, UPWARDS (`a ≤ b`, `Nδ = b − a`), at index `n + 1`, `t = t_n(R)`:
`2R ≤ E(b)·(Δ² + Δδ)` and `2R ≥ (E(a) − t)(Δ² − Δδ) − 2Δt`, `R = E(b) − E(a) − E(a)·Δ`. -/
theorem exp2_up {a b R δ : QExpr} {N : Nat} (n : Nat) (hab : qle a b) (haR : qclose a qzero R) (hbR : qclose b qzero R)
    (hδ : qle qzero δ) (hN : qEq (qmul (qnat N) δ) (qsub b a)) :
    qle (qmul two (qsub (qsub (eseq b (n + 1)) (eseq a (n + 1))) (qmul (qsub b a) (eseq a (n + 1)))))
        (qmul (eseq b (n + 1)) (qadd (qmul (qsub b a) (qsub b a)) (qmul (qsub b a) δ))) ∧
    qle (qsub (qmul (qsub (eseq a (n + 1)) (tm R n)) (qsub (qmul (qsub b a) (qsub b a)) (qmul (qsub b a) δ)))
          (qmul two (qmul (qsub b a) (tm R n))))
        (qmul two (qsub (qsub (eseq b (n + 1)) (eseq a (n + 1))) (qmul (qsub b a) (eseq a (n + 1))))) := by
  have hF : ∀ x y, qEq x y → qEq (eseq x (n + 1)) (eseq y (n + 1)) := fun x y h => eseq_respects h (n + 1)
  have rng : ∀ j, j ≤ N → qclose (gp a δ (qnat j)) qzero R := fun j hj =>
    between_close haR hbR (gp_in hδ hN hj).1 (gp_in hδ hN hj).2
  have U := grid_up (fun x => eseq x (n + 1)) hF (M := eseq b (n + 1)) hδ N (fun j hj => by
    have i1 := gp_in hδ hN (Nat.le_of_lt hj)
    have i2 := gp_in hδ hN (Nat.succ_le_of_lt hj)
    have st := (gp_in hδ hN (Nat.le_of_lt hj)).1
    have sl := E_slope (qle_trans (qle_respects (qEq_refl _) (qEq_refl _) (qle_refl _)) (by
      have := gp_succ a δ j; have := hδ; unfold qsub at *; rat_linarith : qle (gp a δ (qnat j)) (gp a δ (qnat (j + 1)))))
      (rng j (Nat.le_of_lt hj)) (rng (j + 1) (Nat.succ_le_of_lt hj)) n
    have sa := E_slope i2.1 haR (rng (j + 1) (Nat.succ_le_of_lt hj)) n
    have e1 := qmul_respects (gp_succ a δ j) (qEq_refl (eseq (gp a δ (qnat (j + 1))) (n + 1)))
    have e2 := qmul_respects (gp_from a δ (qnat (j + 1))) (qEq_refl (eseq (gp a δ (qnat (j + 1))) (n + 1)))
    exact ⟨qle_respects (qEq_refl _) e1 sl.2, qle_respects (qEq_refl _) e2 sa.2, E_mono i2.2 n⟩)
  have L := grid_lo (fun x => eseq x (n + 1)) hF (t := tm R n) hδ N (fun j hj => by
    have i1 := gp_in hδ hN (Nat.le_of_lt hj)
    have sl := E_slope (by have := gp_succ a δ j; have := hδ; unfold qsub at *; rat_linarith :
        qle (gp a δ (qnat j)) (gp a δ (qnat (j + 1))))
      (rng j (Nat.le_of_lt hj)) (rng (j + 1) (Nat.succ_le_of_lt hj)) n
    have sa := E_slope i1.1 haR (rng j (Nat.le_of_lt hj)) n
    have e1 := qmul_respects (gp_succ a δ j) (qEq_refl (qsub (eseq (gp a δ (qnat j)) (n + 1)) (tm R n)))
    have e2 := qmul_respects (gp_from a δ (qnat j)) (qEq_refl (qsub (eseq a (n + 1)) (tm R n)))
    exact ⟨qle_respects e1 (qEq_refl _) sl.1, qle_respects e2 (qEq_refl _) sa.1⟩)
  -- x_N = b
  have xN : qEq (gp a δ (qnat N)) b := by unfold gp qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have FN := hF _ _ xN
  have nu := nn_succ δ (eseq b (n + 1)) N
  have nl := nn_pred δ (qsub (eseq a (n + 1)) (tm R n)) N
  -- Nδ = Δ inside the products
  have p1 := qmul_respects hN hN
  have p2 := qmul_respects hN (qEq_refl δ)
  have q1 := qmul_respects (qEq_refl (eseq b (n + 1))) (qadd_respects p1 p2)
  have q2 := qmul_respects (qEq_refl (qsub (eseq a (n + 1)) (tm R n)))
    (qadd_respects p1 (qneg_respects p2))
  have q3 := qmul_respects hN (qEq_refl (eseq a (n + 1)))
  have q4 := qmul_respects hN (qEq_refl (tm R n))
  have q5 := qmul_comm (qsub b a) (eseq a (n + 1))
  have q6 := qmul_comm (qmul (qnat N) δ) (eseq a (n + 1))
  simp only [] at U L
  unfold two qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem gm_succ (a δ : QExpr) (j : Nat) : qEq (qsub (gm a δ (qnat j)) (gm a δ (qnat (j + 1)))) δ := by
  have e := qmul_respects (qnat_succ j) (qEq_refl δ)
  unfold gm qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem gm_from (a δ c : QExpr) : qEq (qsub a (gm a δ c)) (qmul c δ) := by
  unfold gm qsub; rat_ring

theorem gm_in {a b δ : QExpr} {N j : Nat} (hδ : qle qzero δ) (hN : qEq (qmul (qnat N) δ) (qsub a b)) (hj : j ≤ N) :
    qle b (gm a δ (qnat j)) ∧ qle (gm a δ (qnat j)) a := by
  have f0 := qmul_nonneg (qnat_nonneg j) hδ
  have f1 := ZExp.scale (qnat_mono hj) hδ
  unfold gm qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE SECOND-ORDER STEP OF `exp`, DOWNWARDS (`b ≤ a`, `Nδ = a − b`): with `Δ' = a − b`,
`2R ≤ E(a)·(Δ'² + Δ'δ) + 2Δ't` and `2R ≥ (E(b) − t)(Δ'² − Δ'δ)`, `R = E(b) − E(a) + E(a)·Δ'`. -/
theorem exp2_dn {a b R δ : QExpr} {N : Nat} (n : Nat) (hba : qle b a) (haR : qclose a qzero R) (hbR : qclose b qzero R)
    (hδ : qle qzero δ) (hN : qEq (qmul (qnat N) δ) (qsub a b)) :
    qle (qmul two (qadd (qsub (eseq b (n + 1)) (eseq a (n + 1))) (qmul (qsub a b) (eseq a (n + 1)))))
        (qadd (qmul (eseq a (n + 1)) (qadd (qmul (qsub a b) (qsub a b)) (qmul (qsub a b) δ)))
          (qmul two (qmul (qsub a b) (tm R n)))) ∧
    qle (qmul (qsub (eseq b (n + 1)) (tm R n)) (qsub (qmul (qsub a b) (qsub a b)) (qmul (qsub a b) δ)))
        (qmul two (qadd (qsub (eseq b (n + 1)) (eseq a (n + 1))) (qmul (qsub a b) (eseq a (n + 1))))) := by
  have hF : ∀ x y, qEq x y → qEq (eseq x (n + 1)) (eseq y (n + 1)) := fun x y h => eseq_respects h (n + 1)
  have rng : ∀ j, j ≤ N → qclose (gm a δ (qnat j)) qzero R := fun j hj =>
    between_close hbR haR (gm_in hδ hN hj).1 (gm_in hδ hN hj).2
  have step : ∀ j, qle (gm a δ (qnat (j + 1))) (gm a δ (qnat j)) := fun j => by
    have := gm_succ a δ j; unfold qsub at *; rat_linarith
  have U := grid_dn_up (fun x => eseq x (n + 1)) hF (t := tm R n) hδ N (fun j hj => by
    have i2 := gm_in hδ hN (Nat.succ_le_of_lt hj)
    have sl := E_slope (step j) (rng (j + 1) (Nat.succ_le_of_lt hj)) (rng j (Nat.le_of_lt hj)) n
    have sa := E_slope i2.2 (rng (j + 1) (Nat.succ_le_of_lt hj)) haR n
    have e1 := qmul_respects (gm_succ a δ j) (qEq_refl (qsub (eseq (gm a δ (qnat (j + 1))) (n + 1)) (tm R n)))
    have e2 := qmul_respects (gm_from a δ (qnat (j + 1))) (qEq_refl (eseq a (n + 1)))
    exact ⟨qle_respects e1 (qEq_refl _) sl.1, qle_respects (qEq_refl _) e2 sa.2⟩)
  have L := grid_dn_lo (fun x => eseq x (n + 1)) hF (t := tm R n) (m := eseq b (n + 1)) hδ N (fun j hj => by
    have i1 := gm_in hδ hN (Nat.le_of_lt hj)
    have sl := E_slope (step j) (rng (j + 1) (Nat.succ_le_of_lt hj)) (rng j (Nat.le_of_lt hj)) n
    have sa := E_slope i1.2 (rng j (Nat.le_of_lt hj)) haR n
    have e1 := qmul_respects (gm_succ a δ j) (qEq_refl (eseq (gm a δ (qnat j)) (n + 1)))
    have e2 := qmul_respects (gm_from a δ (qnat j)) (qEq_refl (qsub (eseq (gm a δ (qnat j)) (n + 1)) (tm R n)))
    have mo := E_mono i1.1 n
    have w0 : qle qzero (qmul (qnat j) δ) := qmul_nonneg (qnat_nonneg j) hδ
    have f := scale_l (by unfold qsub; rat_linarith :
      qle (qsub (eseq b (n + 1)) (tm R n)) (qsub (eseq (gm a δ (qnat j)) (n + 1)) (tm R n))) w0
    exact ⟨qle_respects (qEq_refl _) e1 sl.2, qle_trans f (qle_respects e2 (qEq_refl _) sa.1)⟩)
  have xN : qEq (gm a δ (qnat N)) b := by unfold gm qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have FN := hF _ _ xN
  have nu := nn_succ δ (eseq a (n + 1)) N
  have nl := nn_pred δ (qsub (eseq b (n + 1)) (tm R n)) N
  have p1 := qmul_respects hN hN
  have p2 := qmul_respects hN (qEq_refl δ)
  have q1 := qmul_respects (qEq_refl (eseq a (n + 1))) (qadd_respects p1 p2)
  have q2 := qmul_respects (qEq_refl (qsub (eseq b (n + 1)) (tm R n))) (qadd_respects p1 (qneg_respects p2))
  have q3 := qmul_respects hN (qEq_refl (eseq a (n + 1)))
  have q4 := qmul_respects hN (qEq_refl (tm R n))
  have q5 := qmul_comm (qsub a b) (eseq a (n + 1))
  have q6 := qmul_comm (qmul (qnat N) δ) (eseq a (n + 1))
  simp only [] at U L
  unfold two qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## To every precision -/

/-- The constant the errors are measured against: `(M0 + 4)·Dm² + 2Dm + 1`. -/
def ctot (M0 Dm : QExpr) : QExpr := qadd (qmul (qadd M0 (qnat 4)) (qmul Dm Dm)) (qadd (qadd Dm Dm) qone)

/-- From above: `2R ≤ E·(Δ² + Δ²·ep) + 2Δt`, `E ≤ Eh + e1` — then `2R ≤ Δ²·Eh + ε_k`. -/
theorem fin_up {twoR Ex Eh Δ Dm t ep e1 ε' εk M0 P : QExpr}
    (h : qle twoR (qadd (qmul Ex (qadd (qmul Δ Δ) (qmul (qmul Δ Δ) ep))) (qmul two (qmul Δ t))))
    (hΔ : qle qzero Δ) (hΔD : qle Δ Dm) (hEx : qle Ex (qadd Eh e1)) (hEh : qle Eh M0) (hM0 : qle qzero M0)
    (he1 : qle qzero e1) (he1' : qle e1 ε') (hε1 : qle ε' qone) (ht : qle qzero t) (ht' : qle (qadd t t) ε')
    (hep : qle qzero ep) (hep' : qle ep ε') (hP : qle (ctot M0 Dm) P) (hPε : qEq (qmul P ε') εk) :
    qle twoR (qadd (qmul (qmul Δ Δ) Eh) εk) := by
  have hD0 : qle qzero Dm := qle_trans hΔ hΔD
  have hε0 : qle qzero ε' := qle_trans he1 he1'
  have d0 := qmul_self_nonneg Δ
  have dD := ZSqrt.sq_mono hΔ hΔD
  unfold ZSqrt.sq at dD
  have f1 := ZExp.scale hEx d0
  have f2' := ZExp.scale he1' d0
  have f2'' := scale_l dD hε0
  have dep : qle qzero (qmul (qmul Δ Δ) ep) := qmul_nonneg d0 hep
  have f3 := ZExp.scale (by rat_linarith : qle Ex (qadd M0 qone)) dep
  have M1 : qle qzero (qadd M0 qone) := by have := qle_of_qlt qone_pos; rat_linarith
  have f4 := scale_l (ZExp.scale dD hep) M1
  have f5 := scale_l hep' (qmul_nonneg M1 (qmul_self_nonneg Dm))
  have f6 := ZExp.scale hΔD ht
  have f7 := scale_l ht' hD0
  have f8 := ZExp.scale hP hε0
  have n4 : qEq (qnat 4) (qadd (qadd (qadd qone qone) qone) qone) := by
    have := qnat_succ 3; have := qnat_succ 2; have := qnat_succ 1; have := qnat_succ 0; have := qnat_zero
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have g := qmul_respects (qmul_respects (qadd_respects (qEq_refl M0) n4) (qEq_refl (qmul Dm Dm))) (qEq_refl ε')
  have pp1 := qmul_nonneg (qmul_self_nonneg Dm) hε0
  have pp2 := qmul_nonneg hD0 hε0
  unfold ctot two at *
  rat_linarith

set_option maxRecDepth 100000 in
/-- From below: `2R ≥ (E − t)(Δ² − Δ²·ep) − 2Δt`, `E ≥ El − e1` — then `2R ≥ Δ²·El − ε_k`. -/
theorem fin_lo {twoR Ex El Δ Dm t ep e1 ε' εk M0 P : QExpr}
    (h : qle (qsub (qmul (qsub Ex t) (qsub (qmul Δ Δ) (qmul (qmul Δ Δ) ep))) (qmul two (qmul Δ t))) twoR)
    (hΔ : qle qzero Δ) (hΔD : qle Δ Dm) (hEx : qle (qsub El e1) Ex) (hEl : qle El M0) (hM0 : qle qzero M0)
    (he1 : qle qzero e1) (he1' : qle e1 ε') (hε1 : qle ε' qone) (ht : qle qzero t) (ht' : qle (qadd t t) ε')
    (hep : qle qzero ep) (hep1 : qle ep qone) (hep' : qle ep ε') (hP : qle (ctot M0 Dm) P) (hPε : qEq (qmul P ε') εk) :
    qle (qsub (qmul (qmul Δ Δ) El) εk) twoR := by
  have hD0 : qle qzero Dm := qle_trans hΔ hΔD
  have hε0 : qle qzero ε' := qle_trans he1 he1'
  have d0 := qmul_self_nonneg Δ
  have dD := ZSqrt.sq_mono hΔ hΔD
  unfold ZSqrt.sq at dD
  have dep : qle qzero (qmul (qmul Δ Δ) ep) := qmul_nonneg d0 hep
  have x1 := scale_l hep1 d0
  have X0 : qle qzero (qsub (qmul Δ Δ) (qmul (qmul Δ Δ) ep)) := by
    have := qmul_one (qmul Δ Δ); unfold qsub; rat_linarith
  have f1 := ZExp.scale (by unfold qsub at *; rat_linarith : qle (qsub (qsub El e1) t) (qsub Ex t)) X0
  have f2 := ZExp.scale hEl dep
  have f3 := scale_l (ZExp.scale dD hep) hM0
  have f4 := scale_l hep' (qmul_nonneg hM0 (qmul_self_nonneg Dm))
  have et : qle qzero (qadd e1 t) := by rat_linarith
  have f5 := scale_l (by unfold qsub; rat_linarith : qle (qsub (qmul Δ Δ) (qmul (qmul Δ Δ) ep)) (qmul Δ Δ)) et
  have f6 := scale_l dD et
  have f7 := ZExp.scale (by rat_linarith : qle (qadd e1 t) (qadd ε' ε')) (qmul_self_nonneg Dm)
  have f8 := ZExp.scale hΔD ht
  have f9 := scale_l ht' hD0
  have f10 := ZExp.scale hP hε0
  have n4 : qEq (qnat 4) (qadd (qadd (qadd qone qone) qone) qone) := by
    have := qnat_succ 3; have := qnat_succ 2; have := qnat_succ 1; have := qnat_succ 0; have := qnat_zero
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have g := qmul_respects (qmul_respects (qadd_respects (qEq_refl M0) n4) (qEq_refl (qmul Dm Dm))) (qEq_refl ε')
  have pp1 := qmul_nonneg (qmul_self_nonneg Dm) hε0
  have pp2 := qmul_nonneg hD0 hε0
  unfold ctot two at *
  unfold qsub at *
  rat_linarith

/-- `2R` at index `n`: `2·(E(b) − E(a) − (b − a)·E(a))`. -/
def r2 (A B : Nat → QExpr) (n : Nat) : QExpr :=
  qmul two (qsub (qsub (eseq (B n) n) (eseq (A n) n)) (qmul (qsub (B n) (A n)) (eseq (A n) n)))

/-- `2^K` steps of `Δ·ε_K` make `Δ`. -/
theorem pow2_steps (Δ : QExpr) (K : Nat) : qEq (qmul (qnat (2 ^ K)) (qmul Δ (qeps K))) Δ := by
  have h1 := qnat_pow2 K
  have h2 : qEq (qmul (qofInt (pow2 K)) (qeps (0 + K))) (qeps 0) := qpow2_mul_eps K 0
  rw [Nat.zero_add] at h2
  have h3 := qeps_zero
  have e1 : qEq (qmul (qnat (2 ^ K)) (qmul Δ (qeps K))) (qmul Δ (qmul (qofInt (pow2 K)) (qeps K))) :=
    qEq_trans (qmul_respects h1 (qEq_refl _)) (by rat_ring)
  have e2 := qmul_respects (qEq_refl Δ) (qEq_trans h2 h3)
  exact qEq_trans e1 (qEq_trans e2 (qmul_one Δ))

/-- THE SECOND-ORDER STEP OF `exp`, TO EVERY PRECISION. `a_n`, `b_n` eventually in `[lu, hu]`, the kernel's `exp`
brackets `El ≤ e^lu`, `e^hu ≤ Eh` (`ExpCert`): from some index on, `Δ²·El − ε_k ≤ 2R ≤ Δ²·Eh + ε_k`. -/
theorem Ev_exp2 {A B : Nat → QExpr} {lu hu El Eh : QExpr} (hA : Ev A lu hu) (hB : Ev B lu hu)
    (cl : ∃ z, ExpCert lu El z) (ch : ∃ z, ExpCert hu z Eh) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qmul (qmul (qsub (B n) (A n)) (qsub (B n) (A n))) El) (qeps k)) (r2 A B n) ∧
      qle (r2 A B n) (qadd (qmul (qmul (qsub (B n) (A n)) (qsub (B n) (A n))) Eh) (qeps k)) := by
  intro k
  obtain ⟨M0, B0, hM0, _, m1, m2, m3, m4⟩ := bound4 lu hu El Eh
  obtain ⟨Bc, hB1, _⟩ := qexpr_bound (ctot M0 (qadd (qadd M0 qone) (qadd M0 qone)))
  have hP : qle (ctot M0 (qadd (qadd M0 qone) (qadd M0 qone))) (qofInt (pow2 Bc)) := by
    unfold qsub at hB1; rat_linarith
  have hPε := qpow2_mul_eps Bc k
  have R0 : qle qzero (qadd M0 qone) := by have := qle_of_qlt qone_pos; rat_linarith
  obtain ⟨Na, ha⟩ := hA 0
  obtain ⟨Nb, hb⟩ := hB 0
  obtain ⟨NEa, hEa⟩ := Ev_exp hA cl ch (k + Bc)
  obtain ⟨NEb, hEb⟩ := Ev_exp hB cl ch (k + Bc)
  obtain ⟨K0, hg⟩ := good_exists (qadd M0 qone)
  obtain ⟨Nt, _, ht⟩ := tm_small R0 hg (k + Bc)
  refine ⟨Na + Nb + NEa + NEb + Nt + 1, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ m =>
    have le5 : ∀ x, x ≤ Na + Nb + NEa + NEb + Nt → x ≤ m := fun x hx =>
      Nat.le_trans hx (Nat.le_of_succ_le_succ hn)
    obtain ⟨a1, a2⟩ := ha (m + 1) (Nat.le_succ_of_le (le5 Na (Nat.le_trans (Nat.le_add_right Na Nb)
      (Nat.le_trans (Nat.le_add_right _ NEa) (Nat.le_trans (Nat.le_add_right _ NEb) (Nat.le_add_right _ Nt))))))
    obtain ⟨b1, b2⟩ := hb (m + 1) (Nat.le_succ_of_le (le5 Nb (Nat.le_trans (Nat.le_add_left Nb Na)
      (Nat.le_trans (Nat.le_add_right _ NEa) (Nat.le_trans (Nat.le_add_right _ NEb) (Nat.le_add_right _ Nt))))))
    obtain ⟨ea1, ea2⟩ := hEa (m + 1) (Nat.le_succ_of_le (le5 NEa (Nat.le_trans (Nat.le_add_left NEa (Na + Nb))
      (Nat.le_trans (Nat.le_add_right _ NEb) (Nat.le_add_right _ Nt)))))
    obtain ⟨eb1, eb2⟩ := hEb (m + 1) (Nat.le_succ_of_le (le5 NEb (Nat.le_trans (Nat.le_add_left NEb (Na + Nb + NEa))
      (Nat.le_add_right _ Nt))))
    have tt := ht m (le5 Nt (Nat.le_add_left Nt _))
    have t0 := tm_nonneg R0 m
    have z := qeps_zero
    obtain ⟨l1, l2⟩ := m1
    obtain ⟨h1', h2'⟩ := m2
    obtain ⟨e1', e2'⟩ := m3
    obtain ⟨f1', f2'⟩ := m4
    have aR : qclose (A (m + 1)) qzero (qadd M0 qone) := by
      show qle (qsub (A (m + 1)) qzero) (qadd M0 qone) ∧ qle (qneg (qadd M0 qone)) (qsub (A (m + 1)) qzero)
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
    have bR : qclose (B (m + 1)) qzero (qadd M0 qone) := by
      show qle (qsub (B (m + 1)) qzero) (qadd M0 qone) ∧ qle (qneg (qadd M0 qone)) (qsub (B (m + 1)) qzero)
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
    have hε0 := qeps_nonneg (k + Bc)
    have hε1 : qle (qeps (k + Bc)) qone := by have := eps_anti (Nat.zero_le (k + Bc)); rat_linarith
    have hElM : qle El M0 := by unfold qsub at *; rat_linarith
    have hEhM : qle Eh M0 := by unfold qsub at *; rat_linarith
    show qle _ (qmul two (qsub (qsub (eseq (B (m + 1)) (m + 1)) (eseq (A (m + 1)) (m + 1)))
        (qmul (qsub (B (m + 1)) (A (m + 1))) (eseq (A (m + 1)) (m + 1))))) ∧ qle (qmul two _) _
    cases qle_total (A (m + 1)) (B (m + 1)) with
    | inl hab =>
        have hΔ : qle qzero (qsub (B (m + 1)) (A (m + 1))) := by unfold qsub; rat_linarith
        have hΔD : qle (qsub (B (m + 1)) (A (m + 1))) (qadd (qadd M0 qone) (qadd M0 qone)) := by
          unfold qsub at *; rat_linarith
        have hδ := qmul_nonneg hΔ hε0
        obtain ⟨u1, w1⟩ := exp2_up m hab aR bR hδ (pow2_steps (qsub (B (m + 1)) (A (m + 1))) (k + Bc))
        have tΔ := qmul_nonneg hΔ t0
        have U := fin_up (twoR := qmul two (qsub (qsub (eseq (B (m + 1)) (m + 1)) (eseq (A (m + 1)) (m + 1)))
            (qmul (qsub (B (m + 1)) (A (m + 1))) (eseq (A (m + 1)) (m + 1)))))
          (Ex := eseq (B (m + 1)) (m + 1)) (Eh := Eh) (t := tm (qadd M0 qone) m) (ep := qeps (k + Bc))
          (e1 := qeps (k + Bc)) (M0 := M0) (by unfold two qsub at *; rat_linarith) hΔ hΔD
          (by rat_linarith) hEhM hM0 hε0 (qle_refl _) hε1 t0 tt hε0 (qle_refl _) hP hPε
        have L := fin_lo (twoR := qmul two (qsub (qsub (eseq (B (m + 1)) (m + 1)) (eseq (A (m + 1)) (m + 1)))
            (qmul (qsub (B (m + 1)) (A (m + 1))) (eseq (A (m + 1)) (m + 1)))))
          (Ex := eseq (A (m + 1)) (m + 1)) (El := El) (t := tm (qadd M0 qone) m) (ep := qeps (k + Bc))
          (e1 := qeps (k + Bc)) (M0 := M0) (by unfold two qsub at *; rat_linarith) hΔ hΔD
          ea1 hElM hM0 hε0 (qle_refl _) hε1 t0 tt hε0 hε1 (qle_refl _) hP hPε
        exact ⟨L, U⟩
    | inr hba =>
        have hΔ : qle qzero (qsub (A (m + 1)) (B (m + 1))) := by unfold qsub; rat_linarith
        have hΔD : qle (qsub (A (m + 1)) (B (m + 1))) (qadd (qadd M0 qone) (qadd M0 qone)) := by
          unfold qsub at *; rat_linarith
        have hδ := qmul_nonneg hΔ hε0
        obtain ⟨u1, w1⟩ := exp2_dn m hba aR bR hδ (pow2_steps (qsub (A (m + 1)) (B (m + 1))) (k + Bc))
        have tΔ := qmul_nonneg hΔ t0
        have U := fin_up (twoR := qmul two (qsub (qsub (eseq (B (m + 1)) (m + 1)) (eseq (A (m + 1)) (m + 1)))
            (qmul (qsub (B (m + 1)) (A (m + 1))) (eseq (A (m + 1)) (m + 1)))))
          (Ex := eseq (A (m + 1)) (m + 1)) (Eh := Eh) (t := tm (qadd M0 qone) m) (ep := qeps (k + Bc))
          (e1 := qeps (k + Bc)) (M0 := M0) (by unfold two qsub at *; rat_linarith) hΔ hΔD
          (by rat_linarith) hEhM hM0 hε0 (qle_refl _) hε1 t0 tt hε0 (qle_refl _) hP hPε
        have L := fin_lo (twoR := qmul two (qsub (qsub (eseq (B (m + 1)) (m + 1)) (eseq (A (m + 1)) (m + 1)))
            (qmul (qsub (B (m + 1)) (A (m + 1))) (eseq (A (m + 1)) (m + 1)))))
          (Ex := eseq (B (m + 1)) (m + 1)) (El := El) (t := tm (qadd M0 qone) m) (ep := qeps (k + Bc))
          (e1 := qeps (k + Bc)) (M0 := M0) (by unfold two qsub at *; rat_linarith) hΔ hΔD
          eb1 hElM hM0 hε0 (qle_refl _) hε1 t0 tt hε0 hε1 (qle_refl _) hP hPε
        have s1 : qEq (qmul (qsub (A (m + 1)) (B (m + 1))) (qsub (A (m + 1)) (B (m + 1))))
            (qmul (qsub (B (m + 1)) (A (m + 1))) (qsub (B (m + 1)) (A (m + 1)))) := by unfold qsub; rat_ring
        have s2 := qmul_respects s1 (qEq_refl El)
        have s3 := qmul_respects s1 (qEq_refl Eh)
        unfold qsub at L U s2 s3 ⊢
        exact ⟨by rat_linarith, by rat_linarith⟩

end ZExp2

#print axioms ZExp2.grid_up
#print axioms ZExp2.grid_lo
#print axioms ZExp2.grid_dn_up
#print axioms ZExp2.grid_dn_lo
#print axioms ZExp2.exp2_up
#print axioms ZExp2.exp2_dn
#print axioms ZExp2.fin_up
#print axioms ZExp2.fin_lo
#print axioms ZExp2.Ev_exp2
