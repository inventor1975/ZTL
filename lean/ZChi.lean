-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
/-!
# ZChi — the EN 1993-1-1 buckling curves are monotone, by roots of one quadratic. Zero axioms.

EN 1993-1-1 6.3.1.2: `χ = 1/(Φ + √(Φ² − λ²))`, `Φ = (1 + a(λ − λ0) + λ²)/2`, `λ0 = 0.2`. With `S = 2Φ` the two numbers
`g = Φ − √(Φ² − λ²)` (`= χλ²`) and `R = Φ + √(Φ² − λ²)` (`= 1/χ`) are the roots of `t² − S t + λ²`: `g + R = S`,
`g·R = λ²`, `g ≤ R` (the `Roots` premise — no square root in the proof). ztl-stand's member buckling check
(`frame.judge_buckling`, 2026-11-01) rests on two directions: `χλ²` grows with `λ` (so the proved `|N|` upper bound is
the worst case) and `χ` falls (so the proved `α_cr` lower bound is). Both, without calculus:
  `one_between`  `(1 − g)(1 − R) = −a(λ − λ0) ≤ 0`, so `g ≤ 1 ≤ R` — `χ ≤ 1`;
  `gT_le`        `(2λ − gT)(2λ − RT) = −λ·a·B ≤ 0` (`T = a + 2λ`, `B = 2 + T(λ − 2λ0)`), so `g·T ≤ 2λ`;
  `R_mono`       `(R1 − g2)(R1 − R2) ≤ 0` at `λ2 = λ1 + d`: `R1 ≤ R2`;
  `g_mono`       `(g1 − g2)(g1 − R2) ≥ 0` and `g1 ≤ 1 ≤ R2`: `g1 ≤ g2` (`a > 0` rules out `g1 = R2 = 1`);
  `B_nonneg`     `B ≥ 0` from one number per curve, `(a + 4λ0)λ0 ≤ 2`;
  `chi_curves_monotone`  all of it, for `λ0 ≤ λ1 ≤ λ2`.
Below `λ0` EN sets `χ = 1`, `g = λ²`: monotone, and equal to the roots' `g` at `λ0` (roots `λ0²` and `1`). The
premises a caller checks (ztl-stand checks them exactly, per curve): `0 < a`, `0 ≤ λ0`, `(a + 4λ0)λ0 ≤ 2`.
-/
namespace ZChi
open ZNet
variable {α : Type}

theorem add_right_comm (F : OF α) (a b c : α) : F.add (F.add a b) c = F.add (F.add a c) b := by
  rw [F.add_assoc, F.add_comm b c, ← F.add_assoc]

theorem neg_add' (F : OF α) (a b : α) : F.neg (F.add a b) = F.add (F.neg a) (F.neg b) := by
  have h : F.add (F.add a b) (F.add (F.neg a) (F.neg b)) = F.zero := by
    rw [add4, F.add_neg, F.add_neg, F.add_zero]
  have h2 := eq_neg_of_add F h
  rw [h2, F.neg_neg]

/-- `(t − x)(t − y) = (t·t + x·y) − t·(x + y)`. -/
theorem prod_sub (F : OF α) (t x y : α) :
    F.mul (sub F t x) (sub F t y) = sub F (F.add (F.mul t t) (F.mul x y)) (F.mul t (F.add x y)) := by
  unfold sub
  rw [F.mul_add, add_mul, add_mul, mul_neg, F.neg_mul, F.neg_mul, mul_neg, F.neg_neg, F.mul_add, neg_add',
    F.mul_comm x t]
  -- tt + -(ty) + (-(tx) + xy) = (tt + xy) + (-(tx) + -(ty))
  rw [add4 F (F.mul t t) (F.mul x y), F.add_comm (F.neg (F.mul t y)) (F.mul x y)]

theorem sub_nonpos (F : OF α) {a b : α} (h : F.le a b) : F.le (sub F a b) F.zero := by
  have := F.add_le_add h (F.le_refl (F.neg b))
  unfold sub; rwa [F.add_neg] at this

theorem neg_nonneg (F : OF α) {a : α} (h : F.le a F.zero) : F.le F.zero (F.neg a) := by
  have := F.add_le_add h (F.le_refl (F.neg a))
  rwa [F.add_neg, zero_add] at this

theorem nonpos_nonpos (F : OF α) {a b : α} (ha : F.le a F.zero) (hb : F.le b F.zero) :
    F.le F.zero (F.mul a b) := by
  have := F.mul_nonneg (neg_nonneg F ha) (neg_nonneg F hb)
  rwa [F.neg_mul, mul_neg, F.neg_neg] at this

theorem le_of_sub_zero (F : OF α) {a b : α} (h : sub F a b = F.zero) : F.le a b :=
  le_of_sub_nonpos F (h ▸ F.le_refl _)

theorem ge_of_sub_zero (F : OF α) {a b : α} (h : sub F a b = F.zero) : F.le b a :=
  le_of_sub_nonneg F (h ▸ F.le_refl _)

/-- A point where `(t − g)(t − R) ≤ 0`, with `g ≤ R`, lies between the roots. -/
theorem between (F : OF α) {t g R : α} (hgR : F.le g R) (h : F.le (F.mul (sub F t g) (sub F t R)) F.zero) :
    F.le g t ∧ F.le t R := by
  cases F.le_total t g with
  | inl htg =>
    have h0 := F.le_antisymm h (nonpos_nonpos F (sub_nonpos F htg) (sub_nonpos F (F.le_trans htg hgR)))
    cases F.mul_eq_zero h0 with
    | inl e => exact ⟨ge_of_sub_zero F e, F.le_trans htg hgR⟩
    | inr e => exact ⟨F.le_trans hgR (ge_of_sub_zero F e), le_of_sub_zero F e⟩
  | inr hgt =>
    cases F.le_total t R with
    | inl htR => exact ⟨hgt, htR⟩
    | inr hRt =>
      have h0 := F.le_antisymm h (F.mul_nonneg (sub_nonneg_of_le F hgt) (sub_nonneg_of_le F hRt))
      cases F.mul_eq_zero h0 with
      | inl e => exact ⟨hgt, F.le_trans (le_of_sub_zero F e) hgR⟩
      | inr e => exact ⟨hgt, le_of_sub_zero F e⟩

/-- `S(λ) = (λ² + 1) + a(λ − λ0)`: twice EN 1993-1-1's `Φ` (6.3.1.2), `λ0 = 0.2`. -/
def Sx (F : OF α) (a l0 l : α) : α := F.add (F.add (F.mul l l) F.one) (F.mul a (sub F l l0))
def Tx (F : OF α) (a l : α) : α := F.add a (F.add l l)
def two (F : OF α) : α := F.add F.one F.one
def Wx (F : OF α) (a l0 l : α) : α := F.add (two F) (F.mul a (sub F l (F.add l0 l0)))

theorem mul_sub (F : OF α) (a b c : α) : F.mul a (sub F b c) = sub F (F.mul a b) (F.mul a c) := by
  unfold sub; rw [F.mul_add, mul_neg]

/-- step i: `S + S = λT + W`. -/
theorem step_i (F : OF α) (a l0 l : α) : F.add (Sx F a l0 l) (Sx F a l0 l) = F.add (F.mul l (Tx F a l)) (Wx F a l0 l) := by
  unfold Sx Tx Wx two
  rw [mul_sub, mul_sub, F.mul_add, F.mul_add, F.mul_comm l a]
  unfold sub
  rw [F.mul_add a l0 l0, neg_add']
  generalize F.mul l l = A
  generalize F.mul a l = P
  generalize F.neg (F.mul a l0) = N
  rw [add4 F (F.add A F.one), add4 F A F.one A F.one, add4 F P N P N, F.add_comm P (F.add A A),
    add4 F (F.add A A) P, ← F.add_assoc P P]

def Bx (F : OF α) (a l0 l : α) : α := F.add (two F) (F.mul (Tx F a l) (sub F l (F.add l0 l0)))

/-- step ii: `T·W = (λ + λ)·2 + a·B`. -/
theorem step_ii (F : OF α) (a l0 l : α) :
    F.mul (Tx F a l) (Wx F a l0 l) = F.add (F.mul (F.add l l) (two F)) (F.mul a (Bx F a l0 l)) := by
  unfold Bx Tx Wx
  generalize sub F l (F.add l0 l0) = d
  generalize F.add l l = L
  generalize two F = w
  rw [add_mul, F.mul_add, F.mul_add, add_mul F a L d, F.mul_add a w, F.mul_add a (F.mul a d)]
  have e : F.mul L (F.mul a d) = F.mul a (F.mul L d) := by
    rw [← F.mul_assoc, F.mul_comm L a, F.mul_assoc]
  rw [e, add4, F.add_comm (F.mul a w) (F.mul L w), F.add_assoc]

theorem one_mul' (F : OF α) (a : α) : F.mul F.one a = a := by rw [F.mul_comm, F.mul_one]

theorem one_nonneg (F : OF α) : F.le F.zero F.one := by
  have := F.sq_nonneg F.one; rw [F.mul_one] at this; exact this

theorem neg_nonpos (F : OF α) {D : α} (h : F.le F.zero D) : F.le (F.neg D) F.zero := by
  have := F.add_le_add (F.le_refl (F.neg D)) h
  rwa [F.add_zero, F.add_comm, F.add_neg] at this

theorem cancel_D (F : OF α) (x y D : α) : sub F (F.add x y) (F.add (F.add y x) D) = F.neg D := by
  unfold sub
  rw [neg_add', neg_add', ← F.add_assoc, F.add_comm (F.neg y) (F.neg x), add4, F.add_neg, F.add_neg, F.add_zero,
    zero_add]

/-- A ROOT PAIR at slenderness `λ`: `g + R = S(λ)`, `g·R = λ²`, `g ≤ R` — `g = Φ − √(Φ² − λ²)` is `χλ²` and
`R = Φ + √(Φ² − λ²)` is `1/χ`. -/
structure Roots (F : OF α) (a l0 l g R : α) : Prop where
  sum  : F.add g R = Sx F a l0 l
  prod : F.mul g R = F.mul l l
  le   : F.le g R

/-- `χ ≤ 1` and `χλ² ≤ 1`: `1` lies between the roots, since `(1 − g)(1 − R) = −a(λ − λ0) ≤ 0`. -/
theorem one_between (F : OF α) {a l0 l g R : α} (r : Roots F a l0 l g R) (ha : F.le F.zero a) (hl : F.le l0 l) :
    F.le g F.one ∧ F.le F.one R := by
  apply between F r.le
  rw [prod_sub, r.prod, r.sum, F.mul_one, one_mul']
  unfold Sx
  rw [cancel_D]
  exact neg_nonpos F (F.mul_nonneg ha (sub_nonneg_of_le F hl))

theorem le_add_nonneg (F : OF α) {a c : α} (h : F.le F.zero c) : F.le a (F.add a c) := by
  have := F.add_le_add (F.le_refl a) h
  rwa [F.add_zero] at this

theorem mul_two (F : OF α) (x : α) : F.mul x (two F) = F.add x x := by
  unfold two; rw [F.mul_add, F.mul_one]

/-- `g·T ≤ 2λ` (`T = a + 2λ`): `(2λ − gT)(2λ − RT) = −λ·a·B ≤ 0` with `B ≥ 0` — the step that makes `χλ²` grow. -/
theorem gT_le (F : OF α) {a l0 l g R : α} (r : Roots F a l0 l g R) (ha : F.le F.zero a) (hlp : F.le F.zero l)
    (hB : F.le F.zero (Bx F a l0 l)) : F.le (F.mul g (Tx F a l)) (F.add l l) := by
  have hT : F.le F.zero (Tx F a l) := by
    unfold Tx; have := F.add_le_add ha (F.add_le_add hlp hlp); rwa [F.add_zero, F.add_zero] at this
  have hX : F.le F.zero (F.add l l) := by have := F.add_le_add hlp hlp; rwa [F.add_zero] at this
  have hgR : F.le (F.mul g (Tx F a l)) (F.mul R (Tx F a l)) := by
    rw [F.mul_comm g, F.mul_comm R]; exact F.mul_le_mul_left hT r.le
  apply (between F (t := F.add l l) hgR _).1
  rw [prod_sub, mul4, r.prod, ← add_mul, r.sum]
  apply sub_nonpos
  apply F.le_of_double
  generalize hX' : F.add l l = X at hX
  -- P + P = X(ST) + X(ST) = X((S+S)T) = X((lT + W)T) = X((lT)T) + X(T W) = X((lT)T) + (X(X·2) + X(aB))
  rw [← F.mul_add, ← add_mul, step_i, add_mul, F.mul_comm (Wx F a l0 l), step_ii, hX', F.mul_add, F.mul_add,
    mul_two, F.mul_add]
  have hZ : F.le F.zero (F.mul X (F.mul a (Bx F a l0 l))) := F.mul_nonneg hX (F.mul_nonneg ha hB)
  have e1 : F.mul X (F.mul (F.mul l (Tx F a l)) (Tx F a l)) =
      F.add (F.mul (F.mul l l) (F.mul (Tx F a l) (Tx F a l))) (F.mul (F.mul l l) (F.mul (Tx F a l) (Tx F a l))) := by
    rw [← hX', add_mul, F.mul_assoc l (Tx F a l) (Tx F a l), ← F.mul_assoc l l]
  rw [e1]
  generalize F.mul (F.mul l l) (F.mul (Tx F a l) (Tx F a l)) = Y at hZ ⊢
  generalize F.mul X (F.mul a (Bx F a l0 l)) = Z at hZ ⊢
  generalize F.mul X X = XX
  rw [add4 F XX Y XX Y, ← F.add_assoc (F.add Y Y) (F.add XX XX) Z, F.add_comm (F.add Y Y) (F.add XX XX)]
  exact le_add_nonneg F hZ

/-- `(λ + d)² = λ² + d·(λ + (λ + d))`. -/
theorem sq_shift (F : OF α) (l d : α) :
    F.mul (F.add l d) (F.add l d) = F.add (F.mul l l) (F.mul d (F.add l (F.add l d))) := by
  rw [F.mul_add, add_mul, add_mul, F.mul_add, F.mul_add, F.mul_comm l d]
  rw [F.add_assoc]

/-- `S(λ + d) = S(λ) + d·((λ + (λ + d)) + a)`. -/
theorem S_shift (F : OF α) (a l0 l d : α) :
    Sx F a l0 (F.add l d) = F.add (Sx F a l0 l) (F.mul d (F.add (F.add l (F.add l d)) a)) := by
  unfold Sx
  rw [sq_shift, F.mul_add d (F.add l (F.add l d)) a, mul_sub, mul_sub, F.mul_add a l d]
  unfold sub
  generalize F.mul l l = A
  generalize F.mul d (F.add l (F.add l d)) = Q
  generalize F.mul a l = P
  generalize F.neg (F.mul a l0) = N
  rw [F.mul_comm d a]
  generalize F.mul a d = D
  rw [add_right_comm F A Q, add_right_comm F P D N, add4]

theorem root_g (F : OF α) {a l0 l g R : α} (r : Roots F a l0 l g R) :
    F.add (F.mul g g) (F.mul l l) = F.mul g (Sx F a l0 l) := by
  rw [← r.sum, F.mul_add, r.prod]

theorem root_R (F : OF α) {a l0 l g R : α} (r : Roots F a l0 l g R) :
    F.add (F.mul R R) (F.mul l l) = F.mul R (Sx F a l0 l) := by
  rw [← r.sum, F.mul_add, F.mul_comm R g, r.prod, F.add_comm]

def Mx (F : OF α) (a l d : α) : α := F.add (F.add l (F.add l d)) a

/-- `t·S(λ + d) = (t·t + λ²) + t·(d·M)` and `t·t + (λ + d)² = (t·t + λ²) + d·L` — the two sides compared. -/
theorem shift_sides (F : OF α) (a l0 l d t : α) (h : F.add (F.mul t t) (F.mul l l) = F.mul t (Sx F a l0 l)) :
    F.mul t (Sx F a l0 (F.add l d)) = F.add (F.add (F.mul t t) (F.mul l l)) (F.mul d (F.mul t (Mx F a l d))) ∧
    F.add (F.mul t t) (F.mul (F.add l d) (F.add l d)) =
      F.add (F.add (F.mul t t) (F.mul l l)) (F.mul d (F.add l (F.add l d))) := by
  constructor
  · rw [S_shift, F.mul_add, h, ← F.mul_assoc t d, F.mul_comm t d, F.mul_assoc]; rfl
  · rw [sq_shift, F.add_assoc]

/-- `χ` FALLS: `1/χ = R` grows with `λ` (`(R1 − g2)(R1 − R2) ≤ 0` since `R1 ≥ 1`). -/
theorem R_mono (F : OF α) {a l0 l d g1 R1 g2 R2 : α} (r1 : Roots F a l0 l g1 R1)
    (r2 : Roots F a l0 (F.add l d) g2 R2) (ha : F.le F.zero a) (hl : F.le l0 l) (hd : F.le F.zero d)
    (hL : F.le F.zero (F.add l (F.add l d))) : F.le R1 R2 := by
  have h1 := (one_between F r1 ha hl).2
  apply (between F (t := R1) r2.le _).2
  rw [prod_sub, r2.prod, r2.sum]
  apply sub_nonpos
  obtain ⟨e1, e2⟩ := shift_sides F a l0 l d R1 (root_R F r1)
  rw [e1, e2]
  apply F.add_le_add (F.le_refl _)
  apply F.mul_le_mul_left hd
  -- L ≤ M = L + a ≤ R1·M
  have hM : F.le F.zero (Mx F a l d) := by
    unfold Mx; have := F.add_le_add hL ha; rwa [F.add_zero] at this
  have s1 : F.le (F.add l (F.add l d)) (Mx F a l d) := le_add_nonneg F ha
  have s2 : F.le (Mx F a l d) (F.mul R1 (Mx F a l d)) := by
    have := F.mul_le_mul_left hM h1
    rwa [F.mul_one, F.mul_comm] at this
  exact F.le_trans s1 s2

theorem le_zero_of_add_le (F : OF α) {a X : α} (h : F.le (F.add a X) X) : F.le a F.zero := by
  have := F.add_le_add h (F.le_refl (F.neg X))
  rwa [F.add_assoc, F.add_neg, F.add_zero] at this

/-- `χλ²` GROWS: `g1 ≤ g2` (`(g1 − g2)(g1 − R2) ≥ 0` from `g1·T ≤ 2λ`, and `g1 ≤ 1 ≤ R2`; `a > 0` rules out the
degenerate root `g1 = R2 = 1`). -/
theorem g_mono (F : OF α) {a l0 l d g1 R1 g2 R2 : α} (r1 : Roots F a l0 l g1 R1)
    (r2 : Roots F a l0 (F.add l d) g2 R2) (ha : F.le F.zero a) (hapos : ¬ F.le a F.zero) (hl : F.le l0 l)
    (hl2 : F.le l0 (F.add l d)) (hlp : F.le F.zero l) (hd : F.le F.zero d) (hB : F.le F.zero (Bx F a l0 l)) :
    F.le g1 g2 := by
  have g1one := (one_between F r1 ha hl).1
  have oneR2 := (one_between F r2 ha hl2).2
  have hgT := gT_le F r1 ha hlp hB
  -- (g1 − g2)(g1 − R2) ≥ 0
  have hprod : F.le F.zero (F.mul (sub F g1 g2) (sub F g1 R2)) := by
    rw [prod_sub, r2.prod, r2.sum]
    apply sub_nonneg_of_le
    obtain ⟨e1, e2⟩ := shift_sides F a l0 l d g1 (root_g F r1)
    rw [e1, e2]
    apply F.add_le_add (F.le_refl _)
    apply F.mul_le_mul_left hd
    -- g1·M = g1·T + g1·d ≤ (l + l) + d = L
    have eM : Mx F a l d = F.add (Tx F a l) d := by
      unfold Mx Tx
      rw [F.add_comm (F.add l (F.add l d)) a, ← F.add_assoc l l d, F.add_assoc a]
    have eL : F.add l (F.add l d) = F.add (F.add l l) d := (F.add_assoc l l d).symm
    rw [eM, eL, F.mul_add]
    apply F.add_le_add hgT
    have := F.mul_le_mul_left hd g1one
    rwa [F.mul_one, F.mul_comm] at this
  cases F.le_total g1 g2 with
  | inl h => exact h
  | inr h21 =>
    have h0 := F.le_antisymm
      (by rw [F.mul_comm]; exact F.nonpos_mul (sub_nonpos F (F.le_trans g1one oneR2)) (sub_nonneg_of_le F h21))
      hprod
    cases F.mul_eq_zero h0 with
    | inl e => exact le_of_sub_zero F e
    | inr e =>
      -- g1 = R2 ≥ 1, so T ≤ g1·T ≤ 2λ: a ≤ 0, excluded
      exfalso; apply hapos
      have g1ge : F.le F.one g1 := F.le_trans oneR2 (ge_of_sub_zero F e)
      have hT : F.le F.zero (Tx F a l) := by
        unfold Tx; have := F.add_le_add ha (F.add_le_add hlp hlp); rwa [F.add_zero, F.add_zero] at this
      have := F.mul_le_mul_left hT g1ge
      rw [F.mul_one, F.mul_comm] at this
      exact le_zero_of_add_le F (F.le_trans this hgT)

theorem mul_le_of_nonpos (F : OF α) {x y d : α} (h : F.le x y) (hd : F.le d F.zero) :
    F.le (F.mul y d) (F.mul x d) := by
  have := F.nonpos_mul hd (sub_nonneg_of_le F h)
  rw [mul_sub] at this
  rw [F.mul_comm y, F.mul_comm x]
  exact le_of_sub_nonpos F this

theorem neg_le_neg (F : OF α) {a b : α} (h : F.le a b) : F.le (F.neg b) (F.neg a) := by
  have := F.add_le_add h (F.le_refl (F.add (F.neg a) (F.neg b)))
  rwa [← F.add_assoc a, F.add_neg, zero_add, F.add_comm (F.neg a) (F.neg b), ← F.add_assoc, F.add_neg,
    zero_add] at this

/-- `B = 2 + T(λ − 2λ0) ≥ 0` from ONE NUMBER per curve: `(a + 4λ0)·λ0 ≤ 2` (EN's `λ0 = 0.2`, `a ≤ 0.76`:
`0.192 ≤ 2`). -/
theorem B_nonneg (F : OF α) {a l0 l : α} (ha : F.le F.zero a) (h0 : F.le F.zero l0) (hl : F.le l0 l)
    (hc : F.le (F.mul (F.add a (F.add (F.add l0 l0) (F.add l0 l0))) l0) (two F)) : F.le F.zero (Bx F a l0 l) := by
  have hlp : F.le F.zero l := F.le_trans h0 hl
  have hT : F.le F.zero (Tx F a l) := by
    unfold Tx; have := F.add_le_add ha (F.add_le_add hlp hlp); rwa [F.add_zero, F.add_zero] at this
  have h2 : F.le F.zero (two F) := by
    unfold two; have := F.add_le_add (one_nonneg F) (one_nonneg F); rwa [F.add_zero] at this
  unfold Bx
  cases F.le_total (F.add l0 l0) l with
  | inl hge =>
    have := F.add_le_add h2 (F.mul_nonneg hT (sub_nonneg_of_le F hge)); rwa [F.add_zero] at this
  | inr hle =>
    generalize hM : F.add a (F.add (F.add l0 l0) (F.add l0 l0)) = M at hc
    have hTM : F.le (Tx F a l) M := by
      rw [← hM]; unfold Tx; exact F.add_le_add (F.le_refl a) (F.add_le_add hle hle)
    have hM0 : F.le F.zero M := F.le_trans hT hTM
    have hdd : F.le (sub F l (F.add l0 l0)) F.zero := sub_nonpos F hle
    have hdl : F.le (F.neg l0) (sub F l (F.add l0 l0)) := by
      have := F.add_le_add (sub_nonneg_of_le F hl) (F.le_refl (F.neg l0))
      unfold sub at this ⊢
      rwa [zero_add, F.add_assoc, ← neg_add'] at this
    -- T·dd ≥ M·dd ≥ M·(−λ0) = −(Mλ0) ≥ −2
    have c1 := mul_le_of_nonpos F hTM hdd
    have c2 := F.mul_le_mul_left hM0 hdl
    rw [mul_neg] at c2
    have c3 := neg_le_neg F hc
    have := F.add_le_add (F.le_refl (two F)) (F.le_trans c3 (F.le_trans c2 c1))
    rwa [F.add_neg] at this

/-- THE CURVES ARE MONOTONE, end to end: for `λ0 ≤ λ ≤ λ + d`, `0 < a`, `0 ≤ λ0` and the one number
`(a + 4λ0)λ0 ≤ 2`: `χλ²` does not fall and `χ` does not rise (`1/χ = R` does not fall). -/
theorem chi_curves_monotone (F : OF α) {a l0 l d g1 R1 g2 R2 : α} (r1 : Roots F a l0 l g1 R1)
    (r2 : Roots F a l0 (F.add l d) g2 R2) (ha : F.le F.zero a) (hapos : ¬ F.le a F.zero) (h0 : F.le F.zero l0)
    (hl : F.le l0 l) (hd : F.le F.zero d)
    (hc : F.le (F.mul (F.add a (F.add (F.add l0 l0) (F.add l0 l0))) l0) (two F)) :
    F.le g1 g2 ∧ F.le R1 R2 := by
  have hlp : F.le F.zero l := F.le_trans h0 hl
  have hl2 : F.le l0 (F.add l d) := by
    have := F.add_le_add hl hd; rwa [F.add_zero] at this
  have hL : F.le F.zero (F.add l (F.add l d)) := by
    have := F.add_le_add hlp (F.add_le_add hlp hd); rwa [F.add_zero, F.add_zero] at this
  exact ⟨g_mono F r1 r2 ha hapos hl hl2 hlp hd (B_nonneg F ha h0 hl hc), R_mono F r1 r2 ha hl hd hL⟩

end ZChi
#print axioms ZChi.prod_sub
#print axioms ZChi.between
#print axioms ZChi.one_between
#print axioms ZChi.gT_le
#print axioms ZChi.R_mono
#print axioms ZChi.g_mono
#print axioms ZChi.B_nonneg
#print axioms ZChi.chi_curves_monotone
