-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
/-!
# ZRound — what `zenergy.pd_ieee` concludes from a floating Cholesky, as algebra. Zero axioms.

`zenergy.pd_ieee` (2026-11-01) proves `lambda_min(K) > 0` from a floating Cholesky of `A_f = fl(K - mu I)`. Two
things are CITED there: IEEE 754 / LAPACK (a fact about the machine: no Lean can prove it) and Higham's backward
error theorem (Accuracy and Stability, Thm 10.3): the computed factor `R` has `Rᵀ R = A_f + D` with
`|D_ij| ≤ g Σ_m |R_mi| |R_mj|`. This file proves everything AFTER that theorem — so the citation shrinks to exactly
Higham 10.3 (and its rounding model), named as a premise here:
  `qf_rtr`        `xᵀ (Rᵀ R) x = Σ_m (Σ_i R_mi x_i)²` (hence ≥ 0);
  `qf_add`        the quadratic form is additive in the matrix;
  `abs_qf_le`     `|xᵀ D x| ≤ Σ_i Σ_j |x_i| |D_ij| |x_j|`;
  `backward_qf`   from `|D_ij| ≤ g Σ_m |R_mi||R_mj|`: that sum is `≤ g Σ_m (Σ_i |R_mi||x_i|)²`;
  `rows_cs`       `Σ_m (Σ_i |R_mi||x_i|)² ≤ (Σ_m Σ_i R_mi²)(Σ_i x_i²)`;
  `chol_lower`    THE STEP: `A + D = Rᵀ R`, `|D_ij| ≤ g Σ_m |R_mi||R_mj|`, `0 ≤ g`, `0 ≤ 1 − g` ⇒
                  `(1 − g)·xᵀ A x + g·tr(A)·|x|² ≥ 0` — `lambda_min(A) ≥ −g/(1 − g)·tr A`, without a division;
  `weyl_frob`     `|xᵀ E x| ≤ s |x|²` for any `s ≥ 0` with `s² ≥ Σ_ij E_ij²` (the rounding of the entries);
Stated without square roots or inverses, in ZNet's ordered field given by its laws.
VR discipline: `#print axioms` at the end — the empty list, every line.
-/
namespace ZRound
open ZNet
variable {α : Type}

/-- `xᵀ M x` over the index list `l`. -/
def qf (F : OF α) (l : List Nat) (M : Nat → Nat → α) (x : Nat → α) : α :=
  S F l (fun i => S F l (fun j => F.mul (x i) (F.mul (M i j) (x j))))

/-- `(Rᵀ R)_ij = Σ_m R_mi R_mj`. -/
def rtr (F : OF α) (l : List Nat) (R : Nat → Nat → α) : Nat → Nat → α :=
  fun i j => S F l (fun m => F.mul (R m i) (R m j))

/-- `x·((a·b)·y) = (a·x)·(b·y)`. -/
theorem r_q (F : OF α) (x a b y : α) : F.mul x (F.mul (F.mul a b) y) = F.mul (F.mul a x) (F.mul b y) := by
  rw [F.mul_assoc a b y, ← F.mul_assoc x a, F.mul_comm x a]

theorem qf_rtr (F : OF α) (l : List Nat) (R : Nat → Nat → α) (x : Nat → α) :
    qf F l (rtr F l R) x = S F l (fun m => F.mul (S F l (fun i => F.mul (R m i) (x i)))
                                                  (S F l (fun j => F.mul (R m j) (x j)))) := by
  unfold qf rtr
  -- x_i (Σ_m R_mi R_mj) x_j = Σ_m x_i (R_mi R_mj) x_j
  have h1 : ∀ i j, F.mul (x i) (F.mul (S F l (fun m => F.mul (R m i) (R m j))) (x j)) =
      S F l (fun m => F.mul (F.mul (R m i) (x i)) (F.mul (R m j) (x j))) := by
    intro i j
    rw [F.mul_comm (S F l _) (x j), ← S_mul F (x j) _ l, ← S_mul F (x i) _ l]
    exact S_congr F l (fun m _ => by
      show F.mul (x i) (F.mul (x j) (F.mul (R m i) (R m j))) = F.mul (F.mul (R m i) (x i)) (F.mul (R m j) (x j))
      rw [F.mul_comm (x j) _, r_q])
  rw [S_congr F l (fun i _ => S_congr F l (fun j _ => h1 i j))]
  -- Σ_i Σ_j Σ_m → Σ_m Σ_i Σ_j
  rw [S_congr F l (fun i _ => S_swap F (fun j m => F.mul (F.mul (R m i) (x i)) (F.mul (R m j) (x j))) l l)]
  rw [S_swap F (fun i m => S F l (fun j => F.mul (F.mul (R m i) (x i)) (F.mul (R m j) (x j)))) l l]
  exact S_congr F l (fun m _ => S_prod F (fun i => F.mul (R m i) (x i)) (fun j => F.mul (R m j) (x j)) l)

theorem qf_rtr_nonneg (F : OF α) (l : List Nat) (R : Nat → Nat → α) (x : Nat → α) :
    F.le F.zero (qf F l (rtr F l R) x) := by
  rw [qf_rtr]
  exact S_nonneg F l (fun m _ => F.sq_nonneg _)

/-! ## Small order facts -/

theorem one_mul (F : OF α) (a : α) : F.mul F.one a = a := by rw [F.mul_comm, F.mul_one]

theorem le_abs (F : OF α) (a : α) : F.le a (F.abs a) := by
  cases F.le_total F.zero a with
  | inl h => rw [F.abs_of_nonneg h]; exact F.le_refl a
  | inr h => exact F.le_trans h (F.abs_nonneg a)

theorem abs_sq (F : OF α) (a : α) : F.mul (F.abs a) (F.abs a) = F.mul a a := by
  rw [← F.abs_mul, F.abs_of_nonneg (F.sq_nonneg a)]

/-- `0 ≤ a`, `0 ≤ b`, `a² ≤ b²` ⇒ `a ≤ b` (no square root: ZNet's cancellation). -/
theorem le_of_sq_le (F : OF α) {a b : α} (ha : F.le F.zero a) (hb : F.le F.zero b)
    (h : F.le (F.mul a a) (F.mul b b)) : F.le a b := by
  cases F.le_total a b with
  | inl hle => exact hle
  | inr hba =>
    -- b ≤ a: b·b ≤ a·b, so a·a ≤ a·b, and the cancellation gives a ≤ b
    have h1 : F.le (F.mul b b) (F.mul a b) := by
      rw [F.mul_comm b b, F.mul_comm a b]; exact F.mul_le_mul_left hb hba
    have h2 : F.le (F.mul (F.mul F.one a) a) (F.mul a b) := by rw [one_mul]; exact F.le_trans h h1
    have h3 := cancel_A F (c := F.one) ha hb h2
    rw [one_mul] at h3
    exact h3

/-- `a + b = c`, `0 ≤ c`, `|b| ≤ B` ⇒ `0 ≤ a + B`. -/
theorem lower_of_sum (F : OF α) {a b c B : α} (h : F.add a b = c) (hc : F.le F.zero c)
    (hb : F.le (F.abs b) B) : F.le F.zero (F.add a B) := by
  have h1 : F.le (F.add a b) (F.add a B) := F.add_le_add (F.le_refl a) (F.le_trans (le_abs F b) hb)
  rw [h] at h1
  exact F.le_trans hc h1

/-! ## The quadratic form -/

theorem qf_add (F : OF α) (l : List Nat) (A D : Nat → Nat → α) (x : Nat → α) :
    qf F l (fun i j => F.add (A i j) (D i j)) x = F.add (qf F l A x) (qf F l D x) := by
  unfold qf
  rw [← S_add F _ _ l]
  exact S_congr F l (fun i _ => by
    rw [← S_add F _ _ l]
    exact S_congr F l (fun j _ => by
      show F.mul (x i) (F.mul (F.add (A i j) (D i j)) (x j)) =
        F.add (F.mul (x i) (F.mul (A i j) (x j))) (F.mul (x i) (F.mul (D i j) (x j)))
      rw [add_mul, F.mul_add]))

theorem qf_congr (F : OF α) (l : List Nat) {M N : Nat → Nat → α} (x : Nat → α)
    (h : ∀ i j, List.Mem i l → List.Mem j l → M i j = N i j) : qf F l M x = qf F l N x := by
  unfold qf
  exact S_congr F l (fun i hi => S_congr F l (fun j hj => by rw [h i j hi hj]))

theorem abs_qf_le (F : OF α) (l : List Nat) (D : Nat → Nat → α) (x : Nat → α) :
    F.le (F.abs (qf F l D x))
      (S F l (fun i => S F l (fun j => F.mul (F.abs (x i)) (F.mul (F.abs (D i j)) (F.abs (x j)))))) := by
  unfold qf
  apply F.le_trans (abs_S F _ l)
  exact S_le F l (fun i _ => by
    apply F.le_trans (abs_S F _ l)
    exact S_le F l (fun j _ => by
      show F.le (F.abs (F.mul (x i) (F.mul (D i j) (x j))))
        (F.mul (F.abs (x i)) (F.mul (F.abs (D i j)) (F.abs (x j))))
      rw [F.abs_mul, F.abs_mul]; exact F.le_refl _))

/-- The matrix of absolute values. -/
def absm (F : OF α) (R : Nat → Nat → α) : Nat → Nat → α := fun m i => F.abs (R m i)

/-- From Higham's componentwise bound: `Σ_ij |x_i||D_ij||x_j| ≤ g Σ_m (Σ_i |R_mi||x_i|)²`. -/
theorem backward_qf (F : OF α) (l : List Nat) (R D : Nat → Nat → α) (x : Nat → α) (g : α)
    (hD : ∀ i j, List.Mem i l → List.Mem j l → F.le (F.abs (D i j)) (F.mul g (rtr F l (absm F R) i j))) :
    F.le (S F l (fun i => S F l (fun j => F.mul (F.abs (x i)) (F.mul (F.abs (D i j)) (F.abs (x j))))))
      (F.mul g (S F l (fun m => F.mul (S F l (fun i => F.mul (F.abs (R m i)) (F.abs (x i))))
                                       (S F l (fun j => F.mul (F.abs (R m j)) (F.abs (x j))))))) := by
  have hq := qf_rtr F l (absm F R) (fun i => F.abs (x i))
  unfold absm at hq
  rw [← hq]
  unfold qf
  rw [← S_mul F g _ l]
  exact S_le F l (fun i hi => by
    rw [← S_mul F g _ l]
    exact S_le F l (fun j hj => by
      show F.le (F.mul (F.abs (x i)) (F.mul (F.abs (D i j)) (F.abs (x j))))
        (F.mul g (F.mul (F.abs (x i)) (F.mul (rtr F l (absm F R) i j) (F.abs (x j)))))
      rw [← F.mul_assoc g, F.mul_comm g (F.abs (x i)), F.mul_assoc (F.abs (x i)) g, ← F.mul_assoc g]
      apply F.mul_le_mul_left (F.abs_nonneg _)
      rw [F.mul_comm (F.abs (D i j)) _, F.mul_comm (F.mul g _) _]
      exact F.mul_le_mul_left (F.abs_nonneg _) (hD i j hi hj)))

/-- Cauchy–Schwarz on every row: `Σ_m (Σ_i a_mi b_i)² ≤ (Σ_m Σ_i a_mi²)(Σ_i b_i²)`. -/
theorem rows_cs (F : OF α) (l : List Nat) (a : Nat → Nat → α) (b : Nat → α) :
    F.le (S F l (fun m => F.mul (S F l (fun i => F.mul (a m i) (b i))) (S F l (fun i => F.mul (a m i) (b i)))))
      (F.mul (S F l (fun m => S F l (fun i => F.mul (a m i) (a m i)))) (S F l (fun i => F.mul (b i) (b i)))) := by
  rw [← S_mul_right F (S F l (fun i => F.mul (b i) (b i))) _ l]
  exact S_le F l (fun m _ => by
    have h := cs_weighted F l (fun _ => F.one) (a m) b (fun _ => by
      have := F.sq_nonneg F.one; rw [F.mul_one] at this; exact this)
    have e1 : S F l (fun i => F.mul F.one (F.mul (a m i) (b i))) = S F l (fun i => F.mul (a m i) (b i)) :=
      S_congr F l (fun i _ => one_mul F _)
    have e2 : S F l (fun i => F.mul F.one (F.mul (a m i) (a m i))) = S F l (fun i => F.mul (a m i) (a m i)) :=
      S_congr F l (fun i _ => one_mul F _)
    have e3 : S F l (fun i => F.mul F.one (F.mul (b i) (b i))) = S F l (fun i => F.mul (b i) (b i)) :=
      S_congr F l (fun i _ => one_mul F _)
    rw [e1, e2, e3] at h
    exact h)

/-- `Σ_m |R_mi|·|R_mi| = (Rᵀ R)_ii`. -/
theorem rtr_abs_diag (F : OF α) (l : List Nat) (R : Nat → Nat → α) (i : Nat) :
    rtr F l (absm F R) i i = rtr F l R i i := by
  unfold rtr absm
  exact S_congr F l (fun m _ => abs_sq F (R m i))

/-! ## The Cholesky step and the rounding of the entries -/

/-- THE CHOLESKY STEP. `A + D = Rᵀ R` and `|D_ij| ≤ g (|R|ᵀ|R|)_ij` (Higham's backward error, the premise),
`0 ≤ g`, `0 ≤ m`, `m + g = 1`: then `0 ≤ m·xᵀ A x + g·(tr A)·|x|²` for every `x` — the floating factorization's
success proves `lambda_min(A) ≥ −(g/m)·tr A`, stated without a division. -/
theorem chol_lower (F : OF α) (l : List Nat) (A D R : Nat → Nat → α) (x : Nat → α) (g m : α)
    (hA : ∀ i j, List.Mem i l → List.Mem j l → F.add (A i j) (D i j) = rtr F l R i j)
    (hD : ∀ i j, List.Mem i l → List.Mem j l → F.le (F.abs (D i j)) (F.mul g (rtr F l (absm F R) i j)))
    (hg : F.le F.zero g) (hm : F.le F.zero m) (hmg : F.add m g = F.one) :
    F.le F.zero (F.add (F.mul m (qf F l A x))
      (F.mul g (F.mul (S F l (fun i => A i i)) (S F l (fun i => F.mul (x i) (x i)))))) := by
  let X := S F l (fun i => F.mul (x i) (x i))
  let W := S F l (fun m => F.mul (S F l (fun i => F.mul (F.abs (R m i)) (F.abs (x i))))
                                 (S F l (fun j => F.mul (F.abs (R m j)) (F.abs (x j)))))
  let Fd := S F l (fun i => rtr F l R i i)
  have hX : F.le F.zero X := S_nonneg F l (fun i _ => F.sq_nonneg _)
  -- 1. qf A + qf D = qf (RᵀR) ≥ 0
  have hQ : F.add (qf F l A x) (qf F l D x) = qf F l (rtr F l R) x := by
    rw [← qf_add]; exact qf_congr F l x (fun i j hi hj => hA i j hi hj)
  -- 2. |qf D| ≤ g W
  have hDq : F.le (F.abs (qf F l D x)) (F.mul g W) :=
    F.le_trans (abs_qf_le F l D x) (backward_qf F l R D x g hD)
  -- 3. W ≤ Fd · X
  have hW : F.le W (F.mul Fd X) := by
    have h := rows_cs F l (absm F R) (fun i => F.abs (x i))
    unfold absm at h
    have e1 : S F l (fun m => S F l (fun i => F.mul (F.abs (R m i)) (F.abs (R m i)))) = Fd := by
      rw [S_congr F l (fun m _ => S_congr F l (fun i _ => abs_sq F (R m i)))]
      exact S_swap F (fun m i => F.mul (R m i) (R m i)) l l
    have e2 : S F l (fun i => F.mul (F.abs (x i)) (F.abs (x i))) = X :=
      S_congr F l (fun i _ => abs_sq F (x i))
    rw [e1, e2] at h
    exact h
  -- 4. 0 ≤ qf A + g W
  have low : F.le F.zero (F.add (qf F l A x) (F.mul g W)) := lower_of_sum F hQ (qf_rtr_nonneg F l R x) hDq
  -- 5. m Fd ≤ tr A, entry by entry: m r ≤ A_ii from A + D = r, D ≤ g r, m + g = 1
  have hdiag : F.le (F.mul m Fd) (S F l (fun i => A i i)) := by
    rw [← S_mul F m _ l]
    exact S_le F l (fun i hi => by
      show F.le (F.mul m (rtr F l R i i)) (A i i)
      have hDi : F.le (D i i) (F.mul g (rtr F l R i i)) := by
        have := hD i i hi hi; rw [rtr_abs_diag] at this; exact F.le_trans (le_abs F _) this
      have hr : F.add (F.mul m (rtr F l R i i)) (F.mul g (rtr F l R i i)) = rtr F l R i i := by
        rw [← add_mul, hmg, one_mul]
      have h2 : F.le (rtr F l R i i) (F.add (A i i) (F.mul g (rtr F l R i i))) := by
        have h := F.add_le_add (F.le_refl (A i i)) hDi
        rw [hA i i hi hi] at h
        exact h
      have h3 : F.le (F.add (F.mul m (rtr F l R i i)) (F.mul g (rtr F l R i i)))
          (F.add (A i i) (F.mul g (rtr F l R i i))) := by rw [hr]; exact h2
      rw [F.add_comm (F.mul m (rtr F l R i i)) _, F.add_comm (A i i) _] at h3
      exact add_le_cancel F h3)
  -- 6. m (g W) ≤ g (tr A · X)
  have hmgW : F.le (F.mul m (F.mul g W)) (F.mul g (F.mul (S F l (fun i => A i i)) X)) := by
    have s1 : F.le (F.mul m (F.mul g W)) (F.mul m (F.mul g (F.mul Fd X))) :=
      F.mul_le_mul_left hm (F.mul_le_mul_left hg hW)
    have s2 : F.mul m (F.mul g (F.mul Fd X)) = F.mul g (F.mul (F.mul m Fd) X) := by
      rw [← F.mul_assoc m g, F.mul_comm m g, F.mul_assoc g m, F.mul_assoc m Fd X]
    have s3 : F.le (F.mul g (F.mul (F.mul m Fd) X)) (F.mul g (F.mul (S F l (fun i => A i i)) X)) := by
      apply F.mul_le_mul_left hg
      rw [F.mul_comm (F.mul m Fd) X, F.mul_comm _ X]
      exact F.mul_le_mul_left hX hdiag
    rw [s2] at s1
    exact F.le_trans s1 s3
  -- 7. assemble
  have h7 : F.le F.zero (F.add (F.mul m (qf F l A x)) (F.mul m (F.mul g W))) := by
    rw [← F.mul_add]; exact F.mul_nonneg hm low
  exact F.le_trans h7 (F.add_le_add (F.le_refl _) hmgW)

/-- THE ROUNDING OF THE ENTRIES. `0 ≤ s`, `Σ_ij E_ij² ≤ s²`: `|xᵀ E x| ≤ s |x|²` (Weyl, by Cauchy–Schwarz twice). -/
theorem weyl_frob (F : OF α) (l : List Nat) (E : Nat → Nat → α) (x : Nat → α) (s : α) (hs : F.le F.zero s)
    (hE : F.le (S F l (fun i => S F l (fun j => F.mul (E i j) (E i j)))) (F.mul s s)) :
    F.le (F.abs (qf F l E x)) (F.mul s (S F l (fun i => F.mul (x i) (x i)))) := by
  let X := S F l (fun i => F.mul (x i) (x i))
  let c := fun i => S F l (fun j => F.mul (F.abs (E i j)) (F.abs (x j)))
  have hX : F.le F.zero X := S_nonneg F l (fun i _ => F.sq_nonneg _)
  have one_nn : F.le F.zero F.one := by have := F.sq_nonneg F.one; rw [F.mul_one] at this; exact this
  -- the sum of |x_i||E_ij||x_j| is Σ_i |x_i| c_i
  have ha : S F l (fun i => S F l (fun j => F.mul (F.abs (x i)) (F.mul (F.abs (E i j)) (F.abs (x j))))) =
      S F l (fun i => F.mul (F.abs (x i)) (c i)) :=
    S_congr F l (fun i _ => S_mul F (F.abs (x i)) _ l)
  let a := S F l (fun i => F.mul (F.abs (x i)) (c i))
  have ha0 : F.le F.zero a := S_nonneg F l (fun i _ => F.mul_nonneg (F.abs_nonneg _)
    (S_nonneg F l (fun j _ => F.mul_nonneg (F.abs_nonneg _) (F.abs_nonneg _))))
  -- a² ≤ X · Σ c_i²
  have hcs1 : F.le (F.mul a a) (F.mul X (S F l (fun i => F.mul (c i) (c i)))) := by
    have h := cs_weighted F l (fun _ => F.one) (fun i => F.abs (x i)) c (fun _ => one_nn)
    have e1 : S F l (fun i => F.mul F.one (F.mul (F.abs (x i)) (c i))) = a := S_congr F l (fun i _ => one_mul F _)
    have e2 : S F l (fun i => F.mul F.one (F.mul (F.abs (x i)) (F.abs (x i)))) = X :=
      S_congr F l (fun i _ => by rw [one_mul, abs_sq])
    have e3 : S F l (fun i => F.mul F.one (F.mul (c i) (c i))) = S F l (fun i => F.mul (c i) (c i)) :=
      S_congr F l (fun i _ => one_mul F _)
    rw [e1, e2, e3] at h
    exact h
  -- c_i² ≤ (Σ_j E_ij²) · X
  have hcs2 : ∀ i, F.le (F.mul (c i) (c i)) (F.mul (S F l (fun j => F.mul (E i j) (E i j))) X) := by
    intro i
    have h := cs_weighted F l (fun _ => F.one) (fun j => F.abs (E i j)) (fun j => F.abs (x j)) (fun _ => one_nn)
    have e1 : S F l (fun j => F.mul F.one (F.mul (F.abs (E i j)) (F.abs (x j)))) = c i :=
      S_congr F l (fun j _ => one_mul F _)
    have e2 : S F l (fun j => F.mul F.one (F.mul (F.abs (E i j)) (F.abs (E i j)))) =
        S F l (fun j => F.mul (E i j) (E i j)) := S_congr F l (fun j _ => by rw [one_mul, abs_sq])
    have e3 : S F l (fun j => F.mul F.one (F.mul (F.abs (x j)) (F.abs (x j)))) = X :=
      S_congr F l (fun j _ => by rw [one_mul, abs_sq])
    rw [e1, e2, e3] at h
    exact h
  have hsum : F.le (S F l (fun i => F.mul (c i) (c i))) (F.mul (F.mul s s) X) := by
    have h1 := S_le F l (fun i _ => hcs2 i)
    rw [S_mul_right F X _ l] at h1
    rw [F.mul_comm (F.mul s s) X, F.mul_comm _ X] at *
    exact F.le_trans h1 (F.mul_le_mul_left hX hE)
  have hsq : F.le (F.mul a a) (F.mul (F.mul s X) (F.mul s X)) := by
    have h := F.le_trans hcs1 (F.mul_le_mul_left hX hsum)
    have e : F.mul X (F.mul X (F.mul s s)) = F.mul (F.mul s X) (F.mul s X) := by
      rw [mul4 F s X s X, F.mul_comm (F.mul s s) (F.mul X X), F.mul_assoc]
    rw [F.mul_comm (F.mul s s) X] at h
    rw [← e]; exact h
  have hle : F.le a (F.mul s X) := le_of_sq_le F ha0 (F.mul_nonneg hs hX) hsq
  have h0 := abs_qf_le F l E x
  rw [ha] at h0
  exact F.le_trans h0 hle

/-- THE CONCLUSION `pd_ieee` draws. `K' = A_f + E` entrywise (`K' = K − μI` rounded: `A_f` the matrix factored,
`E` the rounding, computed exactly), Higham's premise on `A_f`, `0 ≤ s` with `Σ E_ij² ≤ s²`: then
`0 ≤ m·xᵀK'x + (g·(tr A_f)·|x|² + m·s·|x|²)` — i.e. `xᵀ K x ≥ (μ − s − (g/m) tr A_f)·|x|²`, the `lam` returned. -/
theorem pd_lower (F : OF α) (l : List Nat) (K' Af E D R : Nat → Nat → α) (x : Nat → α) (g m s : α)
    (hK : ∀ i j, List.Mem i l → List.Mem j l → F.add (Af i j) (E i j) = K' i j)
    (hA : ∀ i j, List.Mem i l → List.Mem j l → F.add (Af i j) (D i j) = rtr F l R i j)
    (hD : ∀ i j, List.Mem i l → List.Mem j l → F.le (F.abs (D i j)) (F.mul g (rtr F l (absm F R) i j)))
    (hg : F.le F.zero g) (hm : F.le F.zero m) (hmg : F.add m g = F.one) (hs : F.le F.zero s)
    (hE : F.le (S F l (fun i => S F l (fun j => F.mul (E i j) (E i j)))) (F.mul s s)) :
    F.le F.zero (F.add (F.mul m (qf F l K' x))
      (F.add (F.mul g (F.mul (S F l (fun i => Af i i)) (S F l (fun i => F.mul (x i) (x i)))))
             (F.mul m (F.mul s (S F l (fun i => F.mul (x i) (x i))))))) := by
  let X := S F l (fun i => F.mul (x i) (x i))
  have hq : qf F l K' x = F.add (qf F l Af x) (qf F l E x) := by
    rw [← qf_add]; exact qf_congr F l x (fun i j hi hj => (hK i j hi hj).symm)
  have h1 := chol_lower F l Af D R x g m hA hD hg hm hmg
  -- 0 ≤ qf E + s X
  have hEw : F.le F.zero (F.add (qf F l E x) (F.mul s X)) :=
    lower_of_sum F (F.add_neg (qf F l E x)) (F.le_refl F.zero)
      (by rw [F.abs_neg]; exact weyl_frob F l E x s hs hE)
  have h2 : F.le F.zero (F.mul m (F.add (qf F l E x) (F.mul s X))) := F.mul_nonneg hm hEw
  rw [F.mul_add] at h2
  have h3 := F.add_le_add h1 h2
  rw [F.add_zero] at h3
  rw [hq, F.mul_add]
  -- rearrange (mA + gT) + (mE + msX) into (mA + mE) + (gT + msX)
  rw [add4 F] at h3
  exact h3

end ZRound

#print axioms ZRound.r_q
#print axioms ZRound.qf_rtr
#print axioms ZRound.qf_rtr_nonneg
#print axioms ZRound.le_of_sq_le
#print axioms ZRound.lower_of_sum
#print axioms ZRound.qf_add
#print axioms ZRound.abs_qf_le
#print axioms ZRound.backward_qf
#print axioms ZRound.rows_cs
#print axioms ZRound.rtr_abs_diag
#print axioms ZRound.chol_lower
#print axioms ZRound.weyl_frob
#print axioms ZRound.pd_lower
#print axioms ZRound.one_mul
#print axioms ZRound.le_abs
#print axioms ZRound.abs_sq
#print axioms ZRound.qf_congr
