-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- The mathematics of a certified worst-case bound for resistive networks over a box of conductances.
-- The method was developed by Vitaly Reznik (circuit stand, 2026-10-08/09), prompted by a question from
-- Arkadiy Miteiko; formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik.
-- Published with A. Miteiko's consent (2026-10-12).
import ZCertify

/-!
# ZNet — the mathematics of the network certificate. Zero axioms.

The certificate bounds a branch current or a node potential of a scalar network L = SᵀGS over a box
of conductances. Proved here, for any ordered field given by its laws (nothing borrowed — the house style of
ZCertify, ZLP, ZCases: the zero axiom list is the principle of operationality, not a convenience):

  * `cw_bound`         — Collatz–Wielandt: a symmetric L with non-positive off-diagonal, `w ≥ 0` with
                         `λ w_i ≤ (L w)_i`: then `λ |x|² ≤ xᵀ L x` for every `x = w ∘ y` (the eigenvalue step);
  * `energy_bound`     — from the residual: `λ |e|² ≤ eᵀ r`, `E = eᵀ r` ⇒ `λ E ≤ |r|²` (step 3);
  * `laplacian_energy` — `xᵀ L x = Σ_e g_e (s_e · x)²` for `L = Σ_e g_e s_e s_eᵀ` (the branch form);
  * `branch_le_energy` — one branch's `g_e (s_e · x)² ≤ xᵀ L x` (the projection bound of step 3);
  * the assembly — pinning by certain signs, rounds, cuts (steps 5–6): `pin_sound`, `mono_restrict`,
                         `rounds_sound`, `split_sound`, on ZCertify's rules;
  * step 4, the energy enclosure over the box (2026-10-12): `cs_weighted` (Cauchy–Schwarz with weights, squared),
                         `kcl_orth` (Kirchhoff contracted), `energy_perturbation` / `perturbation_branch`
                         (`(1 − t)² Σ g0 Δu² ≤ Σ g0 (t u0)²`: every branch within `sqrt(1/g0) rn/(1 − t)`),
                         `target_identity` (the target's change through the reverse field, exact),
                         `target_second` (`(1 − t)² Sec² ≤ tk² rn²`), `target_first`, `target_enclosure`.

  * the pair target (2026-10-12): `pair_cs` (Cauchy–Schwarz in the energy, `(q·e)² ≤ R·E`), `reff_identity`
                         (`R = q·z0`), `quad_bound` (`(R − σ)² ≤ Rε²`, `σ + Bε ≤ B²`, `ε ≤ 2B` ⇒ `R ≤ B²`),
                         `pair_center` (`(q·e)² ≤ B²·ey²`).

Everything is stated without square roots (squared forms); no field inverse is used, so every law holds in ℤ, ℚ
and ℝ. The kernel's rational roots are CHECKED where it computes them (`r ≥ 0`, `r² ≥ q`; the pair's `B` against
`quad_bound`'s two conditions) — checked facts, not premises. PREMISES, said rather than hidden: Kirchhoff's
current law at the free nodes (the network's equations, at `g` and at `g0`); the box written as `g = g0 + g0·d`
with `|d| ≤ t`, `(1 − t)·g0 ≤ g` (the kernel's own construction of the centre); the derivative-sign formulas
`dI_k/dg_j = −g_k T_kj u_j` that justify a pin (calculus). What is proved is all the algebra the kernel's numbers
rest on and how they combine.
-/

namespace ZNet

/-- An ordered field, given by the laws these proofs use (all hold in ℚ and ℝ). -/
structure OF (α : Type) where
  zero : α
  one  : α
  add  : α → α → α
  mul  : α → α → α
  neg  : α → α
  le   : α → α → Prop
  add_comm  : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero  : ∀ a, add a zero = a
  add_neg   : ∀ a, add a (neg a) = zero
  mul_comm  : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one   : ∀ a, mul a one = a
  mul_zero  : ∀ a, mul a zero = zero
  mul_add   : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  neg_mul   : ∀ a b, mul (neg a) b = neg (mul a b)
  neg_neg   : ∀ a, neg (neg a) = a
  le_refl   : ∀ a, le a a
  le_trans  : ∀ {a b c}, le a b → le b c → le a c
  add_le_add : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d)
  mul_le_mul_left : ∀ {a b c}, le zero c → le a b → le (mul c a) (mul c b)
  mul_nonneg : ∀ {a b}, le zero a → le zero b → le zero (mul a b)
  sq_nonneg  : ∀ a, le zero (mul a a)
  nonpos_mul : ∀ {a b}, le a zero → le zero b → le (mul a b) zero
  le_of_double : ∀ {a b}, le (add a a) (add b b) → le a b
  le_total   : ∀ a b, le a b ∨ le b a
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  mul_eq_zero : ∀ {a b}, mul a b = zero → a = zero ∨ b = zero
  abs : α → α
  abs_mul : ∀ a b, abs (mul a b) = mul (abs a) (abs b)
  abs_add : ∀ a b, le (abs (add a b)) (add (abs a) (abs b))
  abs_zero : abs zero = zero
  abs_nonneg : ∀ a, le zero (abs a)
  abs_of_nonneg : ∀ {a}, le zero a → abs a = a
  abs_neg : ∀ a, abs (neg a) = abs a

variable {α : Type}

/-- Σ over a list of indices. -/
def S (F : OF α) : List Nat → (Nat → α) → α
  | [], _ => F.zero
  | i :: l, f => F.add (f i) (S F l f)

theorem add4 (F : OF α) (a b c d : α) : F.add (F.add a b) (F.add c d) = F.add (F.add a c) (F.add b d) := by
  rw [F.add_assoc, F.add_assoc]
  rw [← F.add_assoc b c d, F.add_comm b c, F.add_assoc c b d]

theorem zero_add (F : OF α) (a : α) : F.add F.zero a = a := by rw [F.add_comm, F.add_zero]

theorem S_add (F : OF α) (f g : Nat → α) : ∀ l, S F l (fun i => F.add (f i) (g i)) = F.add (S F l f) (S F l g)
  | [] => by show F.zero = F.add F.zero F.zero; rw [F.add_zero]
  | i :: l => by
      show F.add (F.add (f i) (g i)) (S F l (fun i => F.add (f i) (g i))) =
        F.add (F.add (f i) (S F l f)) (F.add (g i) (S F l g))
      rw [S_add F f g l, add4]

theorem S_mul (F : OF α) (c : α) (f : Nat → α) : ∀ l, S F l (fun i => F.mul c (f i)) = F.mul c (S F l f)
  | [] => by show F.zero = F.mul c F.zero; rw [F.mul_zero]
  | i :: l => by
      show F.add (F.mul c (f i)) (S F l (fun i => F.mul c (f i))) = F.mul c (F.add (f i) (S F l f))
      rw [S_mul F c f l, F.mul_add]

theorem S_congr (F : OF α) {f g : Nat → α} : ∀ l, (∀ i, List.Mem i l → f i = g i) → S F l f = S F l g
  | [], _ => rfl
  | i :: l, h => by
      show F.add (f i) (S F l f) = F.add (g i) (S F l g)
      rw [h i (List.Mem.head l), S_congr F l (fun j hj => h j (List.Mem.tail i hj))]

theorem S_le (F : OF α) {f g : Nat → α} : ∀ l, (∀ i, List.Mem i l → F.le (f i) (g i)) → F.le (S F l f) (S F l g)
  | [], _ => F.le_refl _
  | i :: l, h => F.add_le_add (h i (List.Mem.head l)) (S_le F l (fun j hj => h j (List.Mem.tail i hj)))

theorem S_swap (F : OF α) (a : Nat → Nat → α) (m : List Nat) :
    ∀ l, S F l (fun i => S F m (fun j => a i j)) = S F m (fun j => S F l (fun i => a i j))
  | [] => by
      show F.zero = S F m (fun _ => F.zero)
      induction m with
      | nil => rfl
      | cons j m ih => show F.zero = F.add F.zero (S F m (fun _ => F.zero)); rw [← ih, F.add_zero]
  | i :: l => by
      show F.add (S F m (fun j => a i j)) (S F l (fun i => S F m (fun j => a i j))) =
        S F m (fun j => F.add (a i j) (S F l (fun i => a i j)))
      rw [S_swap F a m l, S_add F (fun j => a i j) (fun j => S F l (fun i => a i j)) m]

theorem S_zero (F : OF α) : ∀ l : List Nat, S F l (fun _ => F.zero) = F.zero
  | [] => rfl
  | _ :: m => by show F.add F.zero (S F m (fun _ => F.zero)) = F.zero; rw [S_zero F m, F.add_zero]

theorem S_nonneg (F : OF α) {f : Nat → α} (l : List Nat) (h : ∀ i, List.Mem i l → F.le F.zero (f i)) :
    F.le F.zero (S F l f) := by
  have h2 := S_le F (f := fun _ => F.zero) (g := f) l h
  rw [S_zero F l] at h2
  exact h2

/-! ## Ring rearrangements, by hand -/

theorem zero_mul (F : OF α) (a : α) : F.mul F.zero a = F.zero := by rw [F.mul_comm, F.mul_zero]

theorem add_mul (F : OF α) (a b c : α) : F.mul (F.add a b) c = F.add (F.mul a c) (F.mul b c) := by
  rw [F.mul_comm, F.mul_add, F.mul_comm c a, F.mul_comm c b]

/-- `(a·b)·(c·d) = (a·c)·(b·d)`. -/
theorem mul4 (F : OF α) (a b c d : α) : F.mul (F.mul a b) (F.mul c d) = F.mul (F.mul a c) (F.mul b d) := by
  rw [F.mul_assoc, F.mul_assoc, ← F.mul_assoc b c d, F.mul_comm b c, F.mul_assoc c b d]

theorem mul_neg (F : OF α) (a b : α) : F.mul a (F.neg b) = F.neg (F.mul a b) := by
  rw [F.mul_comm, F.neg_mul, F.mul_comm]

/-- `(a − b)² = (a·a + −(a·b)) + (−(a·b) + b·b)`. -/
theorem sq_sub (F : OF α) (a b : α) :
    F.mul (F.add a (F.neg b)) (F.add a (F.neg b)) =
      F.add (F.add (F.mul a a) (F.neg (F.mul a b))) (F.add (F.neg (F.mul a b)) (F.mul b b)) := by
  rw [F.mul_add, add_mul, add_mul, F.neg_mul, F.mul_comm b a, mul_neg, F.neg_mul, mul_neg, F.neg_neg]

/-- `a·b + a·b + (a − b)² = a·a + b·b`. -/
theorem two_ab_sq (F : OF α) (a b : α) :
    F.add (F.add (F.mul a b) (F.mul a b)) (F.mul (F.add a (F.neg b)) (F.add a (F.neg b))) =
      F.add (F.mul a a) (F.mul b b) := by
  rw [sq_sub, F.add_comm (F.neg (F.mul a b)) (F.mul b b), add4 F (F.mul a a) (F.neg (F.mul a b)) (F.mul b b)]
  rw [← F.add_assoc, F.add_comm (F.add (F.mul a b) (F.mul a b)) (F.add (F.mul a a) (F.mul b b)), F.add_assoc]
  rw [add4 F (F.mul a b) (F.mul a b) (F.neg (F.mul a b)) (F.neg (F.mul a b)), F.add_neg, F.add_zero, F.add_zero]

/-- `x_i · (L_ij · x_j) = (L_ij · (w_i · w_j)) · (y_i · y_j)` for `x = w ∘ y`. -/
theorem pair_form (F : OF α) (wi yi L wj yj : α) :
    F.mul (F.mul wi yi) (F.mul L (F.mul wj yj)) = F.mul (F.mul L (F.mul wi wj)) (F.mul yi yj) := by
  rw [← F.mul_assoc L wj yj, mul4 F wi yi _ yj, ← F.mul_assoc wi L wj, F.mul_comm wi L, F.mul_assoc L wi wj]

/-! ## Collatz–Wielandt -/

/-- THE PAIR INEQUALITY. Off the diagonal `L_ij ≤ 0`, weights `≥ 0`: `L_ij w_i w_j (y_i² + y_j²) ≤ 2 x_i L_ij x_j`;
on the diagonal it is an equality (`y_i − y_i = 0`). -/
theorem pair_le (F : OF α) (L : Nat → Nat → α) (w y : Nat → α)
    (off : ∀ i j, i ≠ j → F.le (L i j) F.zero) (wpos : ∀ i, F.le F.zero (w i)) (i j : Nat) :
    F.le (F.mul (F.mul (L i j) (F.mul (w i) (w j))) (F.add (F.mul (y i) (y i)) (F.mul (y j) (y j))))
      (F.add (F.mul (F.mul (w i) (y i)) (F.mul (L i j) (F.mul (w j) (y j))))
             (F.mul (F.mul (w i) (y i)) (F.mul (L i j) (F.mul (w j) (y j))))) := by
  have hc : F.le (F.mul (F.mul (L i j) (F.mul (w i) (w j)))
      (F.mul (F.add (y i) (F.neg (y j))) (F.add (y i) (F.neg (y j))))) F.zero := by
    cases Nat.decEq i j with
    | isTrue h =>
        rw [h, F.add_neg, F.mul_zero, F.mul_zero]
        exact F.le_refl _
    | isFalse h =>
        exact F.nonpos_mul (F.nonpos_mul (off i j h) (F.mul_nonneg (wpos i) (wpos j))) (F.sq_nonneg _)
  rw [pair_form F (w i) (y i) (L i j) (w j) (y j), ← two_ab_sq F (y i) (y j), F.mul_add, F.mul_add]
  have h2 := F.add_le_add (F.le_refl (F.add (F.mul (F.mul (L i j) (F.mul (w i) (w j))) (F.mul (y i) (y j)))
      (F.mul (F.mul (L i j) (F.mul (w i) (w j))) (F.mul (y i) (y j))))) hc
  rw [F.add_zero] at h2
  exact h2

/-- `(L·(wi·wj))·Y = (wi·Y)·(L·wj)`. -/
theorem r1 (F : OF α) (L wi wj Y : α) :
    F.mul (F.mul L (F.mul wi wj)) Y = F.mul (F.mul wi Y) (F.mul L wj) := by
  rw [← F.mul_assoc L wi wj, F.mul_comm L wi, F.mul_assoc wi L wj, F.mul_assoc, F.mul_comm (F.mul L wj) Y,
    ← F.mul_assoc]

/-- `(wi·(yi·yi))·(λ·wi) = λ·((wi·yi)·(wi·yi))`. -/
theorem r2 (F : OF α) (wi yi lam : α) :
    F.mul (F.mul wi (F.mul yi yi)) (F.mul lam wi) = F.mul lam (F.mul (F.mul wi yi) (F.mul wi yi)) := by
  rw [F.mul_comm (F.mul wi (F.mul yi yi)) (F.mul lam wi), F.mul_assoc lam wi, mul4 F wi yi wi yi,
    F.mul_assoc wi wi (F.mul yi yi)]

/-- THE COLLATZ–WIELANDT BOUND. `L` symmetric, non-positive off the diagonal; `w ≥ 0` with `λ w_i ≤ (L w)_i` on the
index list: then `λ |x|² ≤ xᵀ L x` for every `x = w ∘ y`. (With `w > 0`, every `x` is such a product: `y = x / w`.)
Through the identity `xᵀLx = Σ_i (Lw)_i w_i y_i² − ½ Σ_ij L_ij w_i w_j (y_i − y_j)²`, here in its two halves: the
pair inequality and the row sums. -/
theorem cw_bound (F : OF α) (l : List Nat) (L : Nat → Nat → α) (w y : Nat → α) (lam : α)
    (sym : ∀ i j, L i j = L j i) (off : ∀ i j, i ≠ j → F.le (L i j) F.zero) (wpos : ∀ i, F.le F.zero (w i))
    (hw : ∀ i, List.Mem i l → F.le (F.mul lam (w i)) (S F l (fun j => F.mul (L i j) (w j)))) :
    F.le (F.mul lam (S F l (fun i => F.mul (F.mul (w i) (y i)) (F.mul (w i) (y i)))))
      (S F l (fun i => S F l (fun j => F.mul (F.mul (w i) (y i)) (F.mul (L i j) (F.mul (w j) (y j)))))) := by
  -- the pieces
  let c := fun i j => F.mul (L i j) (F.mul (w i) (w j))
  let P := fun i j => F.mul (F.mul (w i) (y i)) (F.mul (L i j) (F.mul (w j) (y j)))
  let A := S F l (fun i => S F l (fun j => F.mul (c i j) (F.mul (y i) (y i))))
  let Q := S F l (fun i => S F l (fun j => P i j))
  -- 1. Σ Σ c (y_i² + y_j²) ≤ Σ Σ (P + P) = Q + Q
  have h1 : F.le (S F l (fun i => S F l (fun j => F.mul (c i j) (F.add (F.mul (y i) (y i)) (F.mul (y j) (y j))))))
      (S F l (fun i => S F l (fun j => F.add (P i j) (P i j)))) :=
    S_le F l (fun i _ => S_le F l (fun j _ => pair_le F L w y off wpos i j))
  have hQ : S F l (fun i => S F l (fun j => F.add (P i j) (P i j))) = F.add Q Q := by
    rw [S_congr F l (fun i _ => S_add F (P i) (P i) l)]
    exact S_add F _ _ l
  -- 2. Σ Σ c (y_i² + y_j²) = A + A (the second half is the first, by the swap and the symmetry of c)
  have hc : ∀ i j, c i j = c j i := fun i j => by
    show F.mul (L i j) (F.mul (w i) (w j)) = F.mul (L j i) (F.mul (w j) (w i))
    rw [sym i j, F.mul_comm (w i) (w j)]
  have hT : S F l (fun i => S F l (fun j => F.mul (c i j) (F.add (F.mul (y i) (y i)) (F.mul (y j) (y j))))) =
      F.add A A := by
    rw [S_congr F l (fun i _ => S_congr F l (fun j _ => F.mul_add (c i j) (F.mul (y i) (y i)) (F.mul (y j) (y j))))]
    rw [S_congr F l (fun i _ => S_add F (fun j => F.mul (c i j) (F.mul (y i) (y i)))
      (fun j => F.mul (c i j) (F.mul (y j) (y j))) l)]
    rw [S_add F _ _ l]
    have hB : S F l (fun i => S F l (fun j => F.mul (c i j) (F.mul (y j) (y j)))) = A := by
      rw [S_swap F (fun i j => F.mul (c i j) (F.mul (y j) (y j))) l l]
      exact S_congr F l (fun j _ => S_congr F l (fun i _ => by
        show F.mul (c i j) (F.mul (y j) (y j)) = F.mul (c j i) (F.mul (y j) (y j))
        rw [hc i j]))
    rw [hB]
  -- 3. λ |x|² ≤ A, row by row
  have hrow : ∀ i, List.Mem i l → F.le (F.mul lam (F.mul (F.mul (w i) (y i)) (F.mul (w i) (y i))))
      (S F l (fun j => F.mul (c i j) (F.mul (y i) (y i)))) := fun i hi => by
    have e1 : S F l (fun j => F.mul (c i j) (F.mul (y i) (y i))) =
        F.mul (F.mul (w i) (F.mul (y i) (y i))) (S F l (fun j => F.mul (L i j) (w j))) := by
      rw [← S_mul F _ _ l]
      exact S_congr F l (fun j _ => r1 F (L i j) (w i) (w j) (F.mul (y i) (y i)))
    rw [e1, ← r2 F (w i) (y i) lam]
    exact F.mul_le_mul_left (F.mul_nonneg (wpos i) (F.sq_nonneg (y i))) (hw i hi)
  have h3 : F.le (F.mul lam (S F l (fun i => F.mul (F.mul (w i) (y i)) (F.mul (w i) (y i))))) A := by
    rw [← S_mul F _ _ l]
    exact S_le F l hrow
  -- 4. A + A ≤ Q + Q, so A ≤ Q
  have h4 : F.le (F.add A A) (F.add Q Q) := by
    rw [← hT, ← hQ]
    exact h1
  exact F.le_trans h3 (F.le_of_double h4)

/-! ## From the residual to the energy -/

/-- Cancel a common left summand. -/
theorem add_le_cancel (F : OF α) {a b c : α} (h : F.le (F.add c a) (F.add c b)) : F.le a b := by
  have h2 := F.add_le_add (F.le_refl (F.neg c)) h
  rw [← F.add_assoc, ← F.add_assoc, F.add_comm (F.neg c) c, F.add_neg, zero_add, zero_add] at h2
  exact h2

/-- `a·b + a·b ≤ a·a + b·b`: the square of `a − b` is non-negative. -/
theorem two_ab_le (F : OF α) (a b : α) :
    F.le (F.add (F.mul a b) (F.mul a b)) (F.add (F.mul a a) (F.mul b b)) := by
  have h := F.add_le_add (F.le_refl (F.add (F.mul a b) (F.mul a b))) (F.sq_nonneg (F.add a (F.neg b)))
  rw [F.add_zero, two_ab_sq] at h
  exact h

/-- THE ENERGY FROM THE RESIDUAL. The error `e` of the centre field and its residual `r = L e`; `E = eᵀ r` (its
energy `eᵀ L e`); the eigenvalue bound gives `λ |e|² ≤ E`; with `λ ≥ 0`: `λ E ≤ |r|²` — the kernel's
`||x0 − y||_L ≤ |r| / sqrt(λ)` squared and multiplied out (the energy step, without a square root). -/
theorem energy_bound (F : OF α) (l : List Nat) (e r : Nat → α) (lam : α) (hl : F.le F.zero lam)
    (cw : F.le (F.mul lam (S F l (fun i => F.mul (e i) (e i)))) (S F l (fun i => F.mul (e i) (r i)))) :
    F.le (F.mul lam (S F l (fun i => F.mul (e i) (r i)))) (S F l (fun i => F.mul (r i) (r i))) := by
  let E := S F l (fun i => F.mul (e i) (r i))
  -- per index: λ e r + λ e r ≤ λ(λ e e) + r r
  have hi : ∀ i, List.Mem i l → F.le (F.add (F.mul lam (F.mul (e i) (r i))) (F.mul lam (F.mul (e i) (r i))))
      (F.add (F.mul lam (F.mul lam (F.mul (e i) (e i)))) (F.mul (r i) (r i))) := fun i _ => by
    have h := two_ab_le F (F.mul lam (e i)) (r i)
    rw [F.mul_assoc lam (e i) (r i), mul4 F lam (e i) lam (e i), F.mul_assoc lam lam (F.mul (e i) (e i))] at h
    exact h
  have hs := S_le F l hi
  rw [S_add F _ _ l, S_add F _ _ l, S_mul F lam _ l, S_mul F lam _ l, S_mul F lam _ l] at hs
  -- λ(λ Σ e e) ≤ λ E, so λE + λE ≤ λE + Σ r r
  have hm : F.le (F.mul lam (F.mul lam (S F l (fun i => F.mul (e i) (e i))))) (F.mul lam E) :=
    F.mul_le_mul_left hl cw
  have h2 := F.le_trans hs (F.add_le_add hm (F.le_refl (S F l (fun i => F.mul (r i) (r i)))))
  exact add_le_cancel F h2

/-! ## The branch form of the energy, and one branch's share -/

theorem S_mul_right (F : OF α) (c : α) (f : Nat → α) (l : List Nat) :
    S F l (fun i => F.mul (f i) c) = F.mul (S F l f) c := by
  rw [F.mul_comm (S F l f) c, ← S_mul F c f l]
  exact S_congr F l (fun i _ => F.mul_comm (f i) c)

/-- `x_i·((g·(a·b))·x_j) = g·((a·x_i)·(b·x_j))`. -/
theorem r3 (F : OF α) (xi g a b xj : α) :
    F.mul xi (F.mul (F.mul g (F.mul a b)) xj) = F.mul g (F.mul (F.mul a xi) (F.mul b xj)) := by
  rw [← F.mul_assoc xi, F.mul_comm xi (F.mul g (F.mul a b)), F.mul_assoc (F.mul g (F.mul a b)) xi xj,
    F.mul_assoc g, mul4 F a b xi xj]

/-- The Laplacian of the branches: `L_ij = Σ_e g_e s_ei s_ej` (`s_e` the incidence of branch `e`). -/
def lap (F : OF α) (es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (i j : Nat) : α :=
  S F es (fun e => F.mul (g e) (F.mul (s e i) (s e j)))

/-- `s_e · x` — branch `e`'s voltage. -/
def dot (F : OF α) (l : List Nat) (s : Nat → Nat → α) (x : Nat → α) (e : Nat) : α :=
  S F l (fun i => F.mul (s e i) (x i))

/-- THE BRANCH FORM. `xᵀ L x = Σ_e g_e (s_e · x)²` for the branches' Laplacian. -/
theorem laplacian_energy (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (x : Nat → α) :
    S F l (fun i => S F l (fun j => F.mul (x i) (F.mul (lap F es g s i j) (x j)))) =
      S F es (fun e => F.mul (g e) (F.mul (dot F l s x e) (dot F l s x e))) := by
  -- the sum over branches moved outside
  have h1 : ∀ i j, F.mul (x i) (F.mul (lap F es g s i j) (x j)) =
      S F es (fun e => F.mul (x i) (F.mul (F.mul (g e) (F.mul (s e i) (s e j))) (x j))) := fun i j => by
    unfold lap
    rw [← S_mul_right F (x j) _ es, ← S_mul F (x i) _ es]
  rw [S_congr F l (fun i _ => S_congr F l (fun j _ => h1 i j))]
  rw [S_congr F l (fun i _ => S_swap F (fun j e => F.mul (x i) (F.mul (F.mul (g e) (F.mul (s e i) (s e j))) (x j))) es l)]
  rw [S_swap F (fun i e => S F l (fun j => F.mul (x i) (F.mul (F.mul (g e) (F.mul (s e i) (s e j))) (x j)))) es l]
  -- each branch: Σ_i Σ_j = g (s·x)²
  refine S_congr F es (fun e _ => ?_)
  rw [S_congr F l (fun i _ => S_congr F l (fun j _ => r3 F (x i) (g e) (s e i) (s e j) (x j)))]
  rw [S_congr F l (fun i _ => S_mul F (g e) _ l), S_mul F (g e) _ l]
  congr 1
  rw [S_congr F l (fun i _ => S_mul F (F.mul (s e i) (x i)) (fun j => F.mul (s e j) (x j)) l)]
  exact S_mul_right F (dot F l s x e) (fun i => F.mul (s e i) (x i)) l

/-- One non-negative term is at most a sum of non-negative terms. -/
theorem term_le_S (F : OF α) (f : Nat → α) : ∀ (l : List Nat), (∀ i, List.Mem i l → F.le F.zero (f i)) →
    ∀ e, List.Mem e l → F.le (f e) (S F l f)
  | a :: l, h, _, .head _ => by
      have := F.add_le_add (F.le_refl (f a)) (S_nonneg F l (fun j hj => h j (List.Mem.tail a hj)))
      rw [F.add_zero] at this
      exact this
  | a :: l, h, e, .tail _ he => by
      have := F.add_le_add (h a (List.Mem.head l)) (term_le_S F f l (fun j hj => h j (List.Mem.tail a hj)) e he)
      rw [zero_add] at this
      exact this

/-- THE KERNEL'S BRANCH ERROR. The error `e` of the centre field, its residual `r = L e` with `L` the branches'
Laplacian (`g ≥ 0`), the eigenvalue bound `λ |e|² ≤ eᵀ r`, `λ ≥ 0`: for every branch `b`,
`λ · g_b (s_b · e)² ≤ |r|²` — that is `|u_b − uy_b| ≤ sqrt(1/g_b) · |r| / sqrt(λ)`, the bound the certificate puts on every
branch voltage of the centre field (steps 1–3). -/
theorem branch_error (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (e r : Nat → α) (lam : α)
    (hl : F.le F.zero lam) (gpos : ∀ b, F.le F.zero (g b))
    (res : ∀ i, r i = S F l (fun j => F.mul (lap F es g s i j) (e j)))
    (cw : F.le (F.mul lam (S F l (fun i => F.mul (e i) (e i)))) (S F l (fun i => F.mul (e i) (r i))))
    (b : Nat) (hb : List.Mem b es) :
    F.le (F.mul lam (F.mul (g b) (F.mul (dot F l s e b) (dot F l s e b)))) (S F l (fun i => F.mul (r i) (r i))) := by
  have hE : S F l (fun i => F.mul (e i) (r i)) =
      S F es (fun c => F.mul (g c) (F.mul (dot F l s e c) (dot F l s e c))) := by
    rw [← laplacian_energy F l es g s e]
    exact S_congr F l (fun i _ => by rw [res i, ← S_mul F (e i) _ l])
  have hterm := term_le_S F (fun c => F.mul (g c) (F.mul (dot F l s e c) (dot F l s e c))) es
    (fun c _ => F.mul_nonneg (gpos c) (F.sq_nonneg _)) b hb
  rw [← hE] at hterm
  exact F.le_trans (F.mul_le_mul_left hl hterm) (energy_bound F l e r lam hl cw)

/-! ## The assembly: pinning by certain signs, rounds, cuts on ZCertify's rules -/

section Assembly
open ZCertify (Point Box InBox upd endOf Mono cutLo cutHi cut_cover)

variable {β : Type}

/-- The box with quantity `i` pinned at the end its sign `s` names. -/
def pin1 (B : Box α) (i : Nat) (s : Bool) : Box α :=
  fun j => match Nat.decEq j i with
    | isTrue _  => (endOf B s i, endOf B s i)
    | isFalse _ => B j

/-- ONE PIN IS SOUND. Monotone toward `s` in quantity `i` on the box (the sign the round read for branch `i`'s
influence — the derivative formula, a premise): a bound on the pinned box holds on the whole box. -/
theorem pin_sound (O : ZCertify.Ord α) (V : ZCertify.Ord β) (f : Point α → β) (B : Box α) (i : Nat) (s : Bool)
    (c : β) (mono : Mono O V f B i s) (hbound : ∀ q, InBox O (pin1 B i s) q → V.le (f q) c) :
    ∀ p, InBox O B p → V.le (f p) c := by
  intro p hp
  apply V.trans (mono p hp)
  apply hbound
  intro j
  unfold pin1 upd
  cases Nat.decEq j i with
  | isTrue e => subst e; exact ⟨O.refl _, O.refl _⟩
  | isFalse _ => exact hp j

/-- A sign read on the box stays true on a box with ANOTHER quantity pinned (a well-formed box: low ≤ high). -/
theorem mono_restrict (O : ZCertify.Ord α) (V : ZCertify.Ord β) (f : Point α → β) (B : Box α) (wf : ∀ j, O.le (B j).1 (B j).2)
    (i j : Nat) (t s : Bool) (hji : j ≠ i) (mono : Mono O V f B j s) : Mono O V f (pin1 B i t) j s := by
  intro p hp
  have hB : InBox O B p := by
    intro k
    have hk := hp k
    revert hk
    unfold pin1
    cases Nat.decEq k i with
    | isTrue e =>
        subst e
        intro hk
        cases t with
        | true  => exact ⟨O.trans (wf k) hk.1, hk.2⟩
        | false => exact ⟨hk.1, O.trans hk.2 (wf k)⟩
    | isFalse _ => exact id
  have he : endOf (pin1 B i t) s j = endOf B s j := by
    unfold endOf pin1
    cases Nat.decEq j i with
    | isTrue e => exact absurd e hji
    | isFalse _ => rfl
  rw [he]
  exact mono p hB

/-- The box after a list of pins, in order. -/
def pinAll : Box α → List (Nat × Bool) → Box α
  | B, [] => B
  | B, (i, s) :: rest => pinAll (pin1 B i s) rest

/-- Each pin monotone on the box it is applied to. -/
def MonoChain (O : ZCertify.Ord α) (V : ZCertify.Ord β) (f : Point α → β) : Box α → List (Nat × Bool) → Prop
  | _, [] => True
  | B, (i, s) :: rest => Mono O V f B i s ∧ MonoChain O V f (pin1 B i s) rest

/-- THE ROUNDS ARE SOUND. A bound on the finally pinned box holds on the original box. (The exact value at a
point box — an exact solve — is a reading that encloses, as every reading.) -/
theorem rounds_sound (O : ZCertify.Ord α) (V : ZCertify.Ord β) (f : Point α → β) (c : β) :
    ∀ (pins : List (Nat × Bool)) (B : Box α), MonoChain O V f B pins →
      (∀ q, InBox O (pinAll B pins) q → V.le (f q) c) → ∀ p, InBox O B p → V.le (f p) c
  | [], _, _, h => h
  | (i, s) :: rest, B, hm, h =>
      pin_sound O V f B i s c hm.1 (rounds_sound O V f c rest (pin1 B i s) hm.2 h)

/-- A CUT IS SOUND: bounds on the two halves hold on the piece (the split certificate). -/
theorem split_sound (O : ZCertify.Ord α) (V : ZCertify.Ord β) (f : Point α → β) (B : Box α) (i : Nat) (t : α) (c : β)
    (hlo : ∀ q, InBox O (cutLo B i t) q → V.le (f q) c) (hhi : ∀ q, InBox O (cutHi B i t) q → V.le (f q) c) :
    ∀ p, InBox O B p → V.le (f p) c := by
  intro p hp
  cases cut_cover O i t hp with
  | inl h => exact hlo p h
  | inr h => exact hhi p h

end Assembly

/-! ## Step 4: Cauchy–Schwarz with weights, squared (no square root) -/

/-- Σ_i Σ_j f_i g_j = (Σ f)(Σ g). -/
theorem S_prod (F : OF α) (f g : Nat → α) (l : List Nat) :
    S F l (fun i => S F l (fun j => F.mul (f i) (g j))) = F.mul (S F l f) (S F l g) := by
  rw [S_congr F l (fun i _ => S_mul F (f i) g l)]
  exact S_mul_right F (S F l g) f l

/-- `(wi·wj)·((ai·bj)·(aj·bi)) = (wi·(ai·bi))·(wj·(aj·bj))`. -/
theorem r_cross (F : OF α) (wi wj ai bi aj bj : α) :
    F.mul (F.mul wi wj) (F.mul (F.mul ai bj) (F.mul aj bi)) = F.mul (F.mul wi (F.mul ai bi)) (F.mul wj (F.mul aj bj)) := by
  rw [F.mul_comm aj bi, mul4 F ai bj bi aj, F.mul_comm bj aj, mul4 F wi wj _ _]

/-- `(wi·wj)·((ai·bj)·(ai·bj)) = (wi·(ai·ai))·(wj·(bj·bj))`. -/
theorem r_sq (F : OF α) (wi wj ai bj : α) :
    F.mul (F.mul wi wj) (F.mul (F.mul ai bj) (F.mul ai bj)) = F.mul (F.mul wi (F.mul ai ai)) (F.mul wj (F.mul bj bj)) := by
  rw [mul4 F ai bj ai bj, mul4 F wi wj _ _]

/-- CAUCHY–SCHWARZ, weighted, squared: `(Σ w a b)² ≤ (Σ w a²)(Σ w b²)` for `w ≥ 0`. -/
theorem cs_weighted (F : OF α) (l : List Nat) (w a b : Nat → α) (wpos : ∀ i, F.le F.zero (w i)) :
    F.le (F.mul (S F l (fun i => F.mul (w i) (F.mul (a i) (b i)))) (S F l (fun i => F.mul (w i) (F.mul (a i) (b i)))))
      (F.mul (S F l (fun i => F.mul (w i) (F.mul (a i) (a i)))) (S F l (fun i => F.mul (w i) (F.mul (b i) (b i))))) := by
  let P := fun i => F.mul (w i) (F.mul (a i) (b i))
  let Q := fun i => F.mul (w i) (F.mul (a i) (a i))
  let R := fun i => F.mul (w i) (F.mul (b i) (b i))
  have pair : ∀ i j, F.le (F.add (F.mul (P i) (P j)) (F.mul (P i) (P j)))
      (F.add (F.mul (Q i) (R j)) (F.mul (Q j) (R i))) := fun i j => by
    have h := F.mul_le_mul_left (F.mul_nonneg (wpos i) (wpos j)) (two_ab_le F (F.mul (a i) (b j)) (F.mul (a j) (b i)))
    rw [F.mul_add, F.mul_add, r_cross F (w i) (w j) (a i) (b i) (a j) (b j), r_sq F (w i) (w j) (a i) (b j),
      F.mul_comm (w i) (w j), r_sq F (w j) (w i) (a j) (b i)] at h
    exact h
  have hs := S_le F l (fun i _ => S_le F l (fun j _ => pair i j))
  rw [S_congr F l (fun i _ => S_add F (fun j => F.mul (P i) (P j)) (fun j => F.mul (P i) (P j)) l), S_add F _ _ l,
    S_congr F l (fun i _ => S_add F (fun j => F.mul (Q i) (R j)) (fun j => F.mul (Q j) (R i)) l), S_add F _ _ l,
    S_prod F P P l, S_prod F Q R l, S_swap F (fun i j => F.mul (Q j) (R i)) l l, S_prod F Q R l] at hs
  exact F.le_of_double hs

/-! ## Step 4 (a): the energy of the perturbation -/

/-- `a + b = 0 ⇒ a = −b`. -/
theorem eq_neg_of_add (F : OF α) {a b : α} (h : F.add a b = F.zero) : a = F.neg b := by
  have h2 : F.add (F.add a b) (F.neg b) = F.add F.zero (F.neg b) := by rw [h]
  rw [F.add_assoc, F.add_neg, F.add_zero, zero_add] at h2
  exact h2

/-- `0 ≤ a ≤ b ⇒ a·a ≤ b·b`. -/
theorem sq_le_sq (F : OF α) {a b : α} (ha : F.le F.zero a) (hab : F.le a b) : F.le (F.mul a a) (F.mul b b) := by
  have hb : F.le F.zero b := F.le_trans ha hab
  have h1 := F.mul_le_mul_left ha hab
  have h2 := F.mul_le_mul_left hb hab
  rw [F.mul_comm b a] at h2
  exact F.le_trans h1 h2

theorem neg_sq (F : OF α) (a : α) : F.mul (F.neg a) (F.neg a) = F.mul a a := by
  rw [F.neg_mul, mul_neg, F.neg_neg]

/-- THE CANCELLATION. `0 ≤ A`, `0 ≤ c`, `0 ≤ B`: `(c·A)·A ≤ A·B ⇒ c·A ≤ B` (constructive: on the totality law). -/
theorem cancel_A (F : OF α) {c A B : α} (hA : F.le F.zero A) (hB : F.le F.zero B)
    (h : F.le (F.mul (F.mul c A) A) (F.mul A B)) : F.le (F.mul c A) B := by
  cases F.le_total (F.mul c A) B with
  | inl hle => exact hle
  | inr hge =>
      have h2 : F.le (F.mul A B) (F.mul (F.mul c A) A) := by
        rw [F.mul_comm (F.mul c A) A]
        exact F.mul_le_mul_left hA hge
      have heq : F.mul A (F.add (F.mul c A) (F.neg B)) = F.zero := by
        rw [F.mul_add, mul_neg, F.mul_comm A (F.mul c A), F.le_antisymm h h2, F.add_neg]
      cases F.mul_eq_zero heq with
      | inl h0 => rw [h0, F.mul_zero]; exact hB
      | inr h0 => rw [eq_neg_of_add F h0, F.neg_neg]; exact F.le_refl B

/-- KIRCHHOFF, contracted. If the branch quantity `h` meets the current law at every free node
(`Σ_e s_ei h_e = 0`), it is orthogonal to every branch voltage `s_e · δ` of a node difference `δ`. -/
theorem kcl_orth (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (δ h : Nat → α)
    (kcl : ∀ i, List.Mem i l → S F es (fun e => F.mul (s e i) (h e)) = F.zero) :
    S F es (fun e => F.mul (dot F l s δ e) (h e)) = F.zero := by
  unfold dot
  rw [S_congr F es (fun e _ => (S_mul_right F (h e) (fun i => F.mul (s e i) (δ i)) l).symm)]
  rw [S_swap F (fun e i => F.mul (F.mul (s e i) (δ i)) (h e)) l es]
  have h1 : ∀ i, List.Mem i l → S F es (fun e => F.mul (F.mul (s e i) (δ i)) (h e)) = F.zero := fun i hi => by
    rw [S_congr F es (fun e _ => by rw [F.mul_comm (s e i) (δ i), F.mul_assoc]), S_mul F (δ i) _ es, kcl i hi,
      F.mul_zero]
  rw [S_congr F l h1]
  exact S_zero F l

/-- `du·(g·du) = g·(du·du)`. -/
theorem r_gdu (F : OF α) (du g : α) : F.mul du (F.mul g du) = F.mul g (F.mul du du) := by
  rw [← F.mul_assoc, F.mul_comm du g, F.mul_assoc]

/-- `du·((g0·d)·u0) = g0·(du·(d·u0))`. -/
theorem r_cross2 (F : OF α) (du g0 d u0 : α) :
    F.mul du (F.mul (F.mul g0 d) u0) = F.mul g0 (F.mul du (F.mul d u0)) := by
  rw [F.mul_assoc g0 d u0, ← F.mul_assoc du g0, F.mul_comm du g0, F.mul_assoc]

/-- THE ENERGY OF THE PERTURBATION (step 4 (a), squared). At conductances `g` with `(1 − t)·g0 ≤ g` (here `m = 1 − t`)
and `g − g0 = g0·d`, `d² ≤ t_e²`: the difference `δ` of the node potentials, through Kirchhoff's current law at
the free nodes for `G·Δu + (G − G0)·u0` (the network's equations at `g` and at `g0`), satisfies
`m² · Σ_e g0_e Δu_e² ≤ Σ_e g0_e (t_e u0_e)²` — `||Δu||_{G0} ≤ rn / (1 − t)` without the square roots. -/
theorem energy_perturbation (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (δ u0 g0 g d tt : Nat → α) (m : α)
    (hm : F.le F.zero m) (g0pos : ∀ e, F.le F.zero (g0 e))
    (glow : ∀ e, F.le (F.mul m (g0 e)) (g e))
    (dt : ∀ e, F.le (F.mul (d e) (d e)) (F.mul (tt e) (tt e)))
    (kcl : ∀ i, List.Mem i l → S F es (fun e => F.mul (s e i)
      (F.add (F.mul (g e) (dot F l s δ e)) (F.mul (F.mul (g0 e) (d e)) (u0 e)))) = F.zero) :
    F.le (F.mul (F.mul m m) (S F es (fun e => F.mul (g0 e) (F.mul (dot F l s δ e) (dot F l s δ e)))))
      (S F es (fun e => F.mul (g0 e) (F.mul (F.mul (tt e) (u0 e)) (F.mul (tt e) (u0 e))))) := by
  let du := fun e => dot F l s δ e
  let A := S F es (fun e => F.mul (g0 e) (F.mul (du e) (du e)))
  let X := S F es (fun e => F.mul (g0 e) (F.mul (du e) (F.mul (d e) (u0 e))))
  let G2 := S F es (fun e => F.mul (g e) (F.mul (du e) (du e)))
  let Bs := S F es (fun e => F.mul (g0 e) (F.mul (F.mul (tt e) (u0 e)) (F.mul (tt e) (u0 e))))
  have hA : F.le F.zero A := S_nonneg F es (fun e _ => F.mul_nonneg (g0pos e) (F.sq_nonneg _))
  have hBs : F.le F.zero Bs := S_nonneg F es (fun e _ => F.mul_nonneg (g0pos e) (F.sq_nonneg _))
  -- Kirchhoff: G2 + X = 0
  have h0 := kcl_orth F l es s δ (fun e => F.add (F.mul (g e) (du e)) (F.mul (F.mul (g0 e) (d e)) (u0 e))) kcl
  have hGX : F.add G2 X = F.zero := by
    rw [← h0, ← S_add F _ _ es]
    exact S_congr F es (fun e _ => by
      show F.add (F.mul (g e) (F.mul (du e) (du e))) (F.mul (g0 e) (F.mul (du e) (F.mul (d e) (u0 e)))) =
        F.mul (du e) (F.add (F.mul (g e) (du e)) (F.mul (F.mul (g0 e) (d e)) (u0 e)))
      rw [F.mul_add, r_gdu, r_cross2])
  -- 0 ≤ m A ≤ G2 = −X
  have hmA : F.le (F.mul m A) (F.neg X) := by
    rw [← eq_neg_of_add F hGX, ← S_mul F m _ es]
    exact S_le F es (fun e _ => by
      rw [← F.mul_assoc, F.mul_comm (F.mul m (g0 e)) _, F.mul_comm (g e) _]
      exact F.mul_le_mul_left (F.sq_nonneg _) (glow e))
  have hsq : F.le (F.mul (F.mul m A) (F.mul m A)) (F.mul X X) := by
    rw [← neg_sq F X]
    exact sq_le_sq F (F.mul_nonneg hm hA) hmA
  -- Cauchy–Schwarz: X² ≤ A · Σ g0 (d u0)² ≤ A · Bs
  have hcs := cs_weighted F es g0 du (fun e => F.mul (d e) (u0 e)) g0pos
  have hdu : F.le (S F es (fun e => F.mul (g0 e) (F.mul (F.mul (d e) (u0 e)) (F.mul (d e) (u0 e))))) Bs :=
    S_le F es (fun e _ => F.mul_le_mul_left (g0pos e) (by
      rw [mul4 F (d e) (u0 e) (d e) (u0 e), mul4 F (tt e) (u0 e) (tt e) (u0 e), F.mul_comm (F.mul (d e) (d e)) _,
        F.mul_comm (F.mul (tt e) (tt e)) _]
      exact F.mul_le_mul_left (F.sq_nonneg _) (dt e)))
  have hX : F.le (F.mul X X) (F.mul A Bs) := F.le_trans hcs (F.mul_le_mul_left hA hdu)
  have hfin := F.le_trans hsq hX
  rw [mul4 F m A m A, ← F.mul_assoc (F.mul m m) A A] at hfin
  exact cancel_A F hA hBs hfin

/-- ONE BRANCH (step 4 (a), the branch voltage): `m² · g0_b Δu_b² ≤ Σ_e g0_e (t_e u0_e)²` — the certificate's
`|Δu_b| ≤ sqrt(1/g0_b) · rn / (1 − t)`, squared. -/
theorem perturbation_branch (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (δ u0 g0 g d tt : Nat → α) (m : α)
    (hm : F.le F.zero m) (g0pos : ∀ e, F.le F.zero (g0 e))
    (glow : ∀ e, F.le (F.mul m (g0 e)) (g e))
    (dt : ∀ e, F.le (F.mul (d e) (d e)) (F.mul (tt e) (tt e)))
    (kcl : ∀ i, List.Mem i l → S F es (fun e => F.mul (s e i)
      (F.add (F.mul (g e) (dot F l s δ e)) (F.mul (F.mul (g0 e) (d e)) (u0 e)))) = F.zero)
    (b : Nat) (hb : List.Mem b es) :
    F.le (F.mul (F.mul m m) (F.mul (g0 b) (F.mul (dot F l s δ b) (dot F l s δ b))))
      (S F es (fun e => F.mul (g0 e) (F.mul (F.mul (tt e) (u0 e)) (F.mul (tt e) (u0 e))))) := by
  have ht := term_le_S F (fun e => F.mul (g0 e) (F.mul (dot F l s δ e) (dot F l s δ e))) es
    (fun e _ => F.mul_nonneg (g0pos e) (F.sq_nonneg _)) b hb
  exact F.le_trans (F.mul_le_mul_left (F.sq_nonneg m) ht)
    (energy_perturbation F l es s δ u0 g0 g d tt m hm g0pos glow dt kcl)

/-! ## Step 4 (b): the target, through the reverse field -/

/-- THE BILINEAR BRANCH FORM. `xᵀ L y = Σ_e g_e (s_e · x)(s_e · y)`. -/
theorem laplacian_bilinear (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (x y : Nat → α) :
    S F l (fun i => S F l (fun j => F.mul (x i) (F.mul (lap F es g s i j) (y j)))) =
      S F es (fun e => F.mul (g e) (F.mul (dot F l s x e) (dot F l s y e))) := by
  have h1 : ∀ i j, F.mul (x i) (F.mul (lap F es g s i j) (y j)) =
      S F es (fun e => F.mul (x i) (F.mul (F.mul (g e) (F.mul (s e i) (s e j))) (y j))) := fun i j => by
    unfold lap
    rw [← S_mul_right F (y j) _ es, ← S_mul F (x i) _ es]
  rw [S_congr F l (fun i _ => S_congr F l (fun j _ => h1 i j))]
  rw [S_congr F l (fun i _ => S_swap F (fun j e => F.mul (x i) (F.mul (F.mul (g e) (F.mul (s e i) (s e j))) (y j))) es l)]
  rw [S_swap F (fun i e => S F l (fun j => F.mul (x i) (F.mul (F.mul (g e) (F.mul (s e i) (s e j))) (y j)))) es l]
  refine S_congr F es (fun e _ => ?_)
  rw [S_congr F l (fun i _ => S_congr F l (fun j _ => r3 F (x i) (g e) (s e i) (s e j) (y j)))]
  rw [S_congr F l (fun i _ => S_mul F (g e) _ l), S_mul F (g e) _ l]
  congr 1
  rw [S_congr F l (fun i _ => S_mul F (F.mul (s e i) (x i)) (fun j => F.mul (s e j) (y j)) l)]
  exact S_mul_right F (dot F l s y e) (fun i => F.mul (s e i) (x i)) l

/-- The Laplacian of branches is symmetric. -/
theorem lap_symm (F : OF α) (es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (i j : Nat) :
    lap F es g s i j = lap F es g s j i := by
  unfold lap
  exact S_congr F es (fun e _ => by rw [F.mul_comm (s e i) (s e j)])

/-- Kirchhoff's law in the two forms: with `g = g0 + g0·d`, `g·Δu + (g0·d)·u0 = g0·Δu + (g0·d)·(u0 + Δu)`. -/
theorem kcl_form (F : OF α) (g g0 d du u0 : α) (hg : g = F.add g0 (F.mul g0 d)) :
    F.add (F.mul g du) (F.mul (F.mul g0 d) u0) = F.add (F.mul g0 du) (F.mul (F.mul g0 d) (F.add u0 du)) := by
  rw [hg, add_mul, F.mul_add (F.mul g0 d) u0 du, F.add_assoc, F.add_comm (F.mul (F.mul g0 d) du) _]

/-- `T·(g0·du) = g0·(du·T)`. -/
theorem r_t1 (F : OF α) (T g0 du : α) : F.mul T (F.mul g0 du) = F.mul g0 (F.mul du T) := by
  rw [← F.mul_assoc, F.mul_comm T g0, F.mul_assoc, F.mul_comm T du]

/-- `T·((g0·d)·(u0 + du)) = g0·(d·(T·u0)) + g0·(d·(T·du))`. -/
theorem r_t2 (F : OF α) (T g0 d u0 du : α) :
    F.mul T (F.mul (F.mul g0 d) (F.add u0 du)) = F.add (F.mul g0 (F.mul d (F.mul T u0))) (F.mul g0 (F.mul d (F.mul T du))) := by
  rw [← F.mul_assoc, F.mul_comm T (F.mul g0 d), F.mul_assoc (F.mul g0 d) T, F.mul_add T u0 du, F.mul_add,
    F.mul_assoc g0 d, F.mul_assoc g0 d]

/-- THE TARGET THROUGH THE REVERSE FIELD (step 4 (b), exact). `z0` solves `L0 z0 = q` at the free nodes (`q` the
target's injection: a branch's `s_k`, or `e_p − e_q` for a potential); `T0 = S z0`. With Kirchhoff's law for the
difference in the form `g0·Δu + (g0·d)·(u0 + Δu)`: the target's change `q · δ` is
`−(Σ_e g0_e d_e T0_e u0_e + Σ_e g0_e d_e T0_e Δu_e)` — the first order read exactly, the second left to bound. -/
theorem target_identity (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (δ z0 q u0 g0 d : Nat → α)
    (rev : ∀ i, List.Mem i l → q i = S F l (fun j => F.mul (lap F es g0 s i j) (z0 j)))
    (kcl : ∀ i, List.Mem i l → S F es (fun e => F.mul (s e i)
      (F.add (F.mul (g0 e) (dot F l s δ e)) (F.mul (F.mul (g0 e) (d e)) (F.add (u0 e) (dot F l s δ e))))) = F.zero) :
    S F l (fun i => F.mul (q i) (δ i)) =
      F.neg (F.add (S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (dot F l s z0 e) (u0 e)))))
                   (S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (dot F l s z0 e) (dot F l s δ e)))))) := by
  have hb : S F l (fun i => F.mul (q i) (δ i)) =
      S F es (fun e => F.mul (g0 e) (F.mul (dot F l s δ e) (dot F l s z0 e))) := by
    rw [← laplacian_bilinear F l es g0 s δ z0]
    exact S_congr F l (fun i hi => by rw [rev i hi, F.mul_comm, ← S_mul F (δ i) _ l])
  have h0 := kcl_orth F l es s z0 (fun e => F.add (F.mul (g0 e) (dot F l s δ e))
    (F.mul (F.mul (g0 e) (d e)) (F.add (u0 e) (dot F l s δ e)))) kcl
  rw [S_congr F es (fun e _ => by rw [F.mul_add, r_t1, r_t2]), S_add F _ _ es, S_add F _ _ es] at h0
  rw [hb]
  exact eq_neg_of_add F h0

/-- THE SECOND ORDER (step 4 (b), squared). Under step 4 (a)'s premises, the second-order term of the target,
`Sec = Σ_e g0_e d_e T0_e Δu_e`, satisfies `m² · Sec² ≤ (Σ_e g0_e (t_e T0_e)²) · (Σ_e g0_e (t_e u0_e)²)` — the certificate's
`tk · rn / (1 − t)`, squared. -/
theorem target_second (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (δ z0 u0 g0 g d tt : Nat → α) (m : α)
    (hm : F.le F.zero m) (g0pos : ∀ e, F.le F.zero (g0 e))
    (glow : ∀ e, F.le (F.mul m (g0 e)) (g e))
    (dt : ∀ e, F.le (F.mul (d e) (d e)) (F.mul (tt e) (tt e)))
    (kcl : ∀ i, List.Mem i l → S F es (fun e => F.mul (s e i)
      (F.add (F.mul (g e) (dot F l s δ e)) (F.mul (F.mul (g0 e) (d e)) (u0 e)))) = F.zero) :
    F.le (F.mul (F.mul m m) (F.mul (S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (dot F l s z0 e) (dot F l s δ e)))))
                                   (S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (dot F l s z0 e) (dot F l s δ e)))))))
      (F.mul (S F es (fun e => F.mul (g0 e) (F.mul (F.mul (tt e) (dot F l s z0 e)) (F.mul (tt e) (dot F l s z0 e)))))
             (S F es (fun e => F.mul (g0 e) (F.mul (F.mul (tt e) (u0 e)) (F.mul (tt e) (u0 e)))))) := by
  let T0 := fun e => dot F l s z0 e
  let du := fun e => dot F l s δ e
  let A := S F es (fun e => F.mul (g0 e) (F.mul (du e) (du e)))
  let Tk := S F es (fun e => F.mul (g0 e) (F.mul (F.mul (tt e) (T0 e)) (F.mul (tt e) (T0 e))))
  have hA : F.le F.zero A := S_nonneg F es (fun e _ => F.mul_nonneg (g0pos e) (F.sq_nonneg _))
  have hTk : F.le F.zero Tk := S_nonneg F es (fun e _ => F.mul_nonneg (g0pos e) (F.sq_nonneg _))
  -- Sec² ≤ Σ g0 (d T0)² · A ≤ Tk · A
  have hform : S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (T0 e) (du e)))) =
      S F es (fun e => F.mul (g0 e) (F.mul (F.mul (d e) (T0 e)) (du e))) :=
    S_congr F es (fun e _ => by rw [F.mul_assoc (d e) (T0 e) (du e)])
  have hcs := cs_weighted F es g0 (fun e => F.mul (d e) (T0 e)) du g0pos
  have hdT : F.le (S F es (fun e => F.mul (g0 e) (F.mul (F.mul (d e) (T0 e)) (F.mul (d e) (T0 e))))) Tk :=
    S_le F es (fun e _ => F.mul_le_mul_left (g0pos e) (by
      rw [mul4 F (d e) (T0 e) (d e) (T0 e), mul4 F (tt e) (T0 e) (tt e) (T0 e), F.mul_comm (F.mul (d e) (d e)) _,
        F.mul_comm (F.mul (tt e) (tt e)) _]
      exact F.mul_le_mul_left (F.sq_nonneg _) (dt e)))
  have hsec : F.le (F.mul (S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (T0 e) (du e)))))
      (S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (T0 e) (du e)))))) (F.mul Tk A) := by
    rw [hform]
    have h2 : F.le (F.mul (S F es (fun e => F.mul (g0 e) (F.mul (F.mul (d e) (T0 e)) (F.mul (d e) (T0 e))))) A)
        (F.mul Tk A) := by
      rw [F.mul_comm _ A, F.mul_comm Tk A]
      exact F.mul_le_mul_left hA hdT
    exact F.le_trans hcs h2
  -- m² · Sec² ≤ Tk · (m² A) ≤ Tk · Bs
  have hE := energy_perturbation F l es s δ u0 g0 g d tt m hm g0pos glow dt kcl
  have h3 := F.mul_le_mul_left (F.sq_nonneg m) hsec
  have h4 : F.mul (F.mul m m) (F.mul Tk A) = F.mul Tk (F.mul (F.mul m m) A) := by
    rw [← F.mul_assoc, F.mul_comm (F.mul m m) Tk, F.mul_assoc]
  rw [h4] at h3
  exact F.le_trans h3 (F.mul_le_mul_left hTk hE)

/-! ## Step 4 (b): the first order, and the target's enclosure -/

theorem abs_S (F : OF α) (f : Nat → α) : ∀ l, F.le (F.abs (S F l f)) (S F l (fun i => F.abs (f i)))
  | [] => by show F.le (F.abs F.zero) F.zero; rw [F.abs_zero]; exact F.le_refl _
  | i :: l => F.le_trans (F.abs_add _ _) (F.add_le_add (F.le_refl _) (abs_S F f l))

/-- THE FIRST ORDER (step 4 (b)). `|d_e| ≤ t_e`, `g0 ≥ 0`: `|Σ_e g0_e d_e T0_e u0_e| ≤ Σ_e g0_e t_e |T0_e| |u0_e|` —
The first-order term, read with enclosures of `|T0|` and `|u0|` (which `branch_error` provides). -/
theorem target_first (F : OF α) (es : List Nat) (T0 u0 g0 d tt : Nat → α)
    (g0pos : ∀ e, F.le F.zero (g0 e)) (dt : ∀ e, F.le (F.abs (d e)) (tt e)) :
    F.le (F.abs (S F es (fun e => F.mul (g0 e) (F.mul (d e) (F.mul (T0 e) (u0 e))))))
      (S F es (fun e => F.mul (g0 e) (F.mul (tt e) (F.mul (F.abs (T0 e)) (F.abs (u0 e)))))) := by
  apply F.le_trans (abs_S F _ es)
  exact S_le F es (fun e _ => by
    show F.le (F.abs (F.mul (g0 e) (F.mul (d e) (F.mul (T0 e) (u0 e)))))
      (F.mul (g0 e) (F.mul (tt e) (F.mul (F.abs (T0 e)) (F.abs (u0 e)))))
    rw [F.abs_mul, F.abs_mul, F.abs_mul, F.abs_of_nonneg (g0pos e)]
    apply F.mul_le_mul_left (g0pos e)
    rw [F.mul_comm (F.abs (d e)) _, F.mul_comm (tt e) _]
    exact F.mul_le_mul_left (F.mul_nonneg (F.abs_nonneg _) (F.abs_nonneg _)) (dt e))

/-- THE TARGET'S ENCLOSURE. From the exact identity (`target_identity`): `|q · δ| ≤ |first| + |second|`. -/
theorem target_enclosure (F : OF α) {qd F1 Sec : α} (h : qd = F.neg (F.add F1 Sec)) :
    F.le (F.abs qd) (F.add (F.abs F1) (F.abs Sec)) := by
  rw [h, F.abs_neg]
  exact F.abs_add F1 Sec

/-! ## The pair target: its centre error through the effective resistance -/

/-- CAUCHY–SCHWARZ IN THE ENERGY. `z0` solves `L0 z0 = q` at the free nodes; then for every node vector `e`
(the centre's error): `(q · e)² ≤ (Σ_b g0_b (s_b · z0)²) · (Σ_b g0_b (s_b · e)²)` — the effective resistance
`R = z0ᵀ L0 z0` times the error's energy. -/
theorem pair_cs (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (g0 q z0 e : Nat → α)
    (g0pos : ∀ b, F.le F.zero (g0 b))
    (rev : ∀ i, List.Mem i l → q i = S F l (fun j => F.mul (lap F es g0 s i j) (z0 j))) :
    F.le (F.mul (S F l (fun i => F.mul (q i) (e i))) (S F l (fun i => F.mul (q i) (e i))))
      (F.mul (S F es (fun b => F.mul (g0 b) (F.mul (dot F l s z0 b) (dot F l s z0 b))))
             (S F es (fun b => F.mul (g0 b) (F.mul (dot F l s e b) (dot F l s e b))))) := by
  have hb : S F l (fun i => F.mul (q i) (e i)) =
      S F es (fun b => F.mul (g0 b) (F.mul (dot F l s z0 b) (dot F l s e b))) := by
    rw [← laplacian_bilinear F l es g0 s z0 e]
    -- Σ_i q_i e_i = Σ_i e_i (L0 z0)_i = z0ᵀ L0 e, by the symmetry of L0
    have h1 : S F l (fun i => F.mul (q i) (e i)) =
        S F l (fun i => S F l (fun j => F.mul (e i) (F.mul (lap F es g0 s i j) (z0 j)))) :=
      S_congr F l (fun i hi => by rw [rev i hi, F.mul_comm, ← S_mul F (e i) _ l])
    rw [h1, S_swap F (fun i j => F.mul (e i) (F.mul (lap F es g0 s i j) (z0 j))) l l]
    exact S_congr F l (fun j _ => S_congr F l (fun i _ => by
      rw [lap_symm F es g0 s i j, ← F.mul_assoc, F.mul_comm (e i) _, F.mul_assoc, F.mul_comm (e i) (z0 j),
        ← F.mul_assoc, F.mul_comm (lap F es g0 s j i) (z0 j), F.mul_assoc]))
  rw [hb]
  exact cs_weighted F es g0 (fun b => dot F l s z0 b) (fun b => dot F l s e b) g0pos

/-- `a − b`, written with the laws. -/
def sub (F : OF α) (a b : α) : α := F.add a (F.neg b)

theorem sub_self (F : OF α) (a : α) : sub F a a = F.zero := F.add_neg a

theorem sub_nonneg_of_le (F : OF α) {a b : α} (h : F.le b a) : F.le F.zero (sub F a b) := by
  have h2 := F.add_le_add h (F.le_refl (F.neg b))
  rw [F.add_neg] at h2
  exact h2

theorem le_of_sub_nonneg (F : OF α) {a b : α} (h : F.le F.zero (sub F a b)) : F.le b a := by
  have h2 := F.add_le_add h (F.le_refl b)
  unfold sub at h2
  rw [zero_add, F.add_assoc, F.add_comm (F.neg b) b, F.add_neg, F.add_zero] at h2
  exact h2

theorem le_of_sub_nonpos (F : OF α) {a b : α} (h : F.le (sub F a b) F.zero) : F.le a b := by
  have h2 := F.add_le_add h (F.le_refl b)
  unfold sub at h2
  rw [zero_add, F.add_assoc, F.add_comm (F.neg b) b, F.add_neg, F.add_zero] at h2
  exact h2

/-- `a·a = b·b + (a − b)·(a + b)`. -/
theorem sq_diff (F : OF α) (a b : α) : F.mul a a = F.add (F.mul b b) (F.mul (sub F a b) (F.add a b)) := by
  unfold sub
  rw [add_mul, F.mul_add, F.mul_add, F.neg_mul, F.neg_mul, F.mul_comm a b]
  -- bb + ((aa + ba) + (−ba + −bb))
  rw [F.add_assoc (F.mul a a), ← F.add_assoc (F.mul b a) (F.neg (F.mul b a)), F.add_neg, zero_add,
    F.add_comm (F.mul b b), F.add_assoc, F.add_comm (F.neg (F.mul b b)) (F.mul b b), F.add_neg, F.add_zero]

/-- `(R − σ) − (B − σ) = R − B`. -/
theorem sub_sub_cancel (F : OF α) (R B σ : α) : sub F (sub F R σ) (sub F B σ) = sub F R B := by
  unfold sub
  have hn : F.neg (F.add B (F.neg σ)) = F.add (F.neg B) σ := by
    have h : F.add (F.add B (F.neg σ)) (F.add (F.neg B) σ) = F.zero := by
      rw [add4, F.add_neg, F.add_comm (F.neg σ) σ, F.add_neg, F.add_zero]
    have h2 := eq_neg_of_add F h
    rw [h2, F.neg_neg]
  rw [hn, add4, F.add_comm (F.neg σ) σ, F.add_neg, F.add_zero]

/-- `c·x + (R − c)·x = R·x`. -/
theorem split_mul (F : OF α) (c R x : α) : F.add (F.mul c x) (F.mul (sub F R c) x) = F.mul R x := by
  unfold sub
  rw [← add_mul, F.add_comm R (F.neg c), ← F.add_assoc, F.add_neg, zero_add]

/-- THE QUADRATIC STEP (the pair target's `sqrt(R) ≤ (ε + sqrt(ε² + 4σ⁺)) / 2`, squared). `R ≥ 0` the effective
resistance, `σ` the approximate field's `q · z`, `ε ≥ 0` its energy error, `(R − σ)² ≤ R·ε²` (Cauchy–Schwarz in
the energy); `B ≥ 0` with `σ + B·ε ≤ B²` and `ε ≤ 2B` (what the kernel's root gives): then `R ≤ B²`. -/
theorem quad_bound (F : OF α) {R σ ε B : α} (hR : F.le F.zero R) (hε : F.le F.zero ε) (hB : F.le F.zero B)
    (h : F.le (F.mul (sub F R σ) (sub F R σ)) (F.mul R (F.mul ε ε)))
    (hBq : F.le (F.add σ (F.mul B ε)) (F.mul B B)) (hB2 : F.le ε (F.add B B)) :
    F.le R (F.mul B B) := by
  cases F.le_total R (F.mul B B) with
  | inl hle => exact hle
  | inr hge =>
      let a := sub F R σ
      let b := sub F (F.mul B B) σ
      have hBe : F.le (F.mul B ε) b := by
        have := F.add_le_add hBq (F.le_refl (F.neg σ))
        rw [F.add_comm σ, F.add_assoc, F.add_neg, F.add_zero] at this
        exact this
      have hb0 : F.le F.zero b := F.le_trans (F.mul_nonneg hB hε) hBe
      have hD : F.le F.zero (sub F R (F.mul B B)) := sub_nonneg_of_le F hge
      have hab : sub F a b = sub F R (F.mul B B) := sub_sub_cancel F R (F.mul B B) σ
      have ha0 : F.le b a := le_of_sub_nonneg F (by rw [hab]; exact hD)
      -- a + b ≥ 2Bε ≥ ε²
      have hsum : F.le (F.mul ε ε) (F.add a b) := by
        have e1 : F.le (F.mul ε ε) (F.add (F.mul B ε) (F.mul B ε)) := by
          rw [← add_mul, F.mul_comm (F.add B B) ε]
          exact F.mul_le_mul_left hε hB2
        exact F.le_trans e1 (F.add_le_add (F.le_trans hBe ha0) hBe)
      -- b² ≥ B² ε²
      have hbb : F.le (F.mul (F.mul B B) (F.mul ε ε)) (F.mul b b) := by
        rw [← mul4 F B ε B ε]
        exact sq_le_sq F (F.mul_nonneg hB hε) hBe
      -- a² = b² + (R − B²)(a + b) ≥ B²ε² + (R − B²)ε² = Rε²
      have hlow : F.le (F.mul R (F.mul ε ε)) (F.mul a a) := by
        rw [sq_diff F a b, hab, ← split_mul F (F.mul B B) R (F.mul ε ε)]
        exact F.add_le_add hbb (F.mul_le_mul_left hD hsum)
      -- so a² = Rε², and (R − B²)(a + b − ε²) = 0
      have heq := F.le_antisymm h hlow
      rw [sq_diff F a b, hab, ← split_mul F (F.mul B B) R (F.mul ε ε)] at heq
      -- b² + (R−B²)(a+b) = B²ε² + (R−B²)ε², with b² ≥ B²ε² and (R−B²)(a+b) ≥ (R−B²)ε²: both equal
      have hpart : F.le (F.mul (sub F R (F.mul B B)) (F.add a b)) (F.mul (sub F R (F.mul B B)) (F.mul ε ε)) := by
        have h2 := F.add_le_add hbb (F.le_refl (F.mul (sub F R (F.mul B B)) (F.add a b)))
        rw [heq] at h2
        exact add_le_cancel F h2
      have hzero : F.mul (sub F R (F.mul B B)) (sub F (F.add a b) (F.mul ε ε)) = F.zero := by
        have e2 := F.le_antisymm hpart (F.mul_le_mul_left hD hsum)
        show F.mul (sub F R (F.mul B B)) (F.add (F.add a b) (F.neg (F.mul ε ε))) = F.zero
        rw [F.mul_add, mul_neg, e2, F.add_neg]
      cases F.mul_eq_zero hzero with
      | inl h0 => exact le_of_sub_nonpos F (by rw [h0]; exact F.le_refl _)
      | inr h0 =>
          -- a + b = ε² ≤ 2Bε and b ≥ Bε, so a ≤ Bε ≤ b, a = b, R = B²
          have hae : F.add a b = F.mul ε ε := by
            have := eq_neg_of_add F h0
            rw [this, F.neg_neg]
          have hle2 : F.le (F.add a b) (F.add (F.mul B ε) (F.mul B ε)) := by
            rw [hae, ← add_mul, F.mul_comm (F.add B B) ε]
            exact F.mul_le_mul_left hε hB2
          have hale : F.le a (F.mul B ε) := by
            have h3 := F.le_trans hle2 (F.add_le_add (F.le_refl (F.mul B ε)) hBe)
            rw [F.add_comm a b, F.add_comm (F.mul B ε) b] at h3
            exact add_le_cancel F h3
          have haeqb : F.le a b := F.le_trans hale hBe
          have hsub : sub F a b = F.zero := by
            rw [F.le_antisymm haeqb ha0]
            exact sub_self F b
          rw [hab] at hsub
          exact le_of_sub_nonpos F (by rw [hsub]; exact F.le_refl _)

theorem neg_add (F : OF α) (a b : α) : F.neg (F.add a b) = F.add (F.neg a) (F.neg b) := by
  have h : F.add (F.add a b) (F.add (F.neg a) (F.neg b)) = F.zero := by
    rw [add4, F.add_neg, F.add_neg, F.add_zero]
  rw [eq_neg_of_add F h, F.neg_neg]

theorem neg_zero (F : OF α) : F.neg F.zero = F.zero := by
  have h := F.add_neg F.zero
  rw [zero_add] at h
  exact h

theorem S_neg (F : OF α) (f : Nat → α) : ∀ l, S F l (fun i => F.neg (f i)) = F.neg (S F l f)
  | [] => (neg_zero F).symm
  | i :: l => by
      show F.add (F.neg (f i)) (S F l (fun i => F.neg (f i))) = F.neg (F.add (f i) (S F l f))
      rw [S_neg F f l, neg_add]

/-- The effective resistance as the reverse field's energy: `q · z0 = Σ_b g0_b (s_b · z0)²` when `L0 z0 = q`. -/
theorem reff_identity (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (g0 q z0 : Nat → α)
    (rev : ∀ i, List.Mem i l → q i = S F l (fun j => F.mul (lap F es g0 s i j) (z0 j))) :
    S F l (fun i => F.mul (q i) (z0 i)) = S F es (fun b => F.mul (g0 b) (F.mul (dot F l s z0 b) (dot F l s z0 b))) := by
  rw [← laplacian_energy F l es g0 s z0]
  exact S_congr F l (fun i hi => by rw [rev i hi, F.mul_comm, ← S_mul F (z0 i) _ l])

/-- THE PAIR TARGET'S CENTRE ERROR (`|s · (x0 − y)| ≤ sqrt(R) · ey` with `sqrt(R)` bounded through the
approximate reverse field `z`), squared. `L0 z0 = q`; the approximate field's error energy
`Σ g0 (s · (z0 − z))² ≤ ε²`; `σ = q · z`; the kernel's `B` (`σ + Bε ≤ B²`, `ε ≤ 2B`, `B ≥ 0`); the centre's error
`e` with energy `Σ g0 (s · e)² ≤ ey²`: then `(q · e)² ≤ B² · ey²`. -/
theorem pair_center (F : OF α) (l es : List Nat) (s : Nat → Nat → α) (g0 q z0 z e : Nat → α) (ε B ey : α)
    (g0pos : ∀ b, F.le F.zero (g0 b)) (hε : F.le F.zero ε) (hB : F.le F.zero B)
    (rev : ∀ i, List.Mem i l → q i = S F l (fun j => F.mul (lap F es g0 s i j) (z0 j)))
    (hEz : F.le (S F es (fun b => F.mul (g0 b) (F.mul (dot F l s (fun i => sub F (z0 i) (z i)) b)
                                                   (dot F l s (fun i => sub F (z0 i) (z i)) b)))) (F.mul ε ε))
    (hBq : F.le (F.add (S F l (fun i => F.mul (q i) (z i))) (F.mul B ε)) (F.mul B B))
    (hB2 : F.le ε (F.add B B))
    (hE : F.le (S F es (fun b => F.mul (g0 b) (F.mul (dot F l s e b) (dot F l s e b)))) (F.mul ey ey)) :
    F.le (F.mul (S F l (fun i => F.mul (q i) (e i))) (S F l (fun i => F.mul (q i) (e i))))
      (F.mul (F.mul B B) (F.mul ey ey)) := by
  let R := S F es (fun b => F.mul (g0 b) (F.mul (dot F l s z0 b) (dot F l s z0 b)))
  let σ := S F l (fun i => F.mul (q i) (z i))
  have hR : F.le F.zero R := S_nonneg F es (fun b _ => F.mul_nonneg (g0pos b) (F.sq_nonneg _))
  -- q · (z0 − z) = R − σ
  have hdiff : S F l (fun i => F.mul (q i) (sub F (z0 i) (z i))) = sub F R σ := by
    unfold sub
    rw [S_congr F l (fun i _ => by rw [F.mul_add, mul_neg]), S_add F _ _ l, S_neg F _ l,
      reff_identity F l es s g0 q z0 rev]
  -- (R − σ)² ≤ R · Ez ≤ R · ε²
  have h1 := pair_cs F l es s g0 q z0 (fun i => sub F (z0 i) (z i)) g0pos rev
  rw [hdiff] at h1
  have h2 := F.le_trans h1 (F.mul_le_mul_left hR hEz)
  have hRB := quad_bound F hR hε hB h2 hBq hB2
  -- (q · e)² ≤ R · E ≤ B² · ey²
  have h3 := pair_cs F l es s g0 q z0 e g0pos rev
  have h4 : F.le (F.mul R (S F es (fun b => F.mul (g0 b) (F.mul (dot F l s e b) (dot F l s e b)))))
      (F.mul (F.mul B B) (F.mul ey ey)) := by
    have hE0 : F.le F.zero (S F es (fun b => F.mul (g0 b) (F.mul (dot F l s e b) (dot F l s e b)))) :=
      S_nonneg F es (fun b _ => F.mul_nonneg (g0pos b) (F.sq_nonneg _))
    have a1 := F.mul_le_mul_left hE0 hRB
    rw [F.mul_comm _ R, F.mul_comm _ (F.mul B B)] at a1
    exact F.le_trans a1 (F.mul_le_mul_left (F.sq_nonneg B) hE)
  exact F.le_trans h3 h4


end ZNet

#print axioms ZNet.add4
#print axioms ZNet.S_add
#print axioms ZNet.S_mul
#print axioms ZNet.S_congr
#print axioms ZNet.S_le
#print axioms ZNet.S_swap
#print axioms ZNet.S_zero
#print axioms ZNet.S_nonneg
#print axioms ZNet.sq_sub
#print axioms ZNet.two_ab_sq
#print axioms ZNet.pair_form
#print axioms ZNet.pair_le
#print axioms ZNet.r1
#print axioms ZNet.r2
#print axioms ZNet.cw_bound
#print axioms ZNet.add_le_cancel
#print axioms ZNet.two_ab_le
#print axioms ZNet.energy_bound
#print axioms ZNet.S_mul_right
#print axioms ZNet.r3
#print axioms ZNet.laplacian_energy
#print axioms ZNet.term_le_S
#print axioms ZNet.branch_error
#print axioms ZNet.pin_sound
#print axioms ZNet.mono_restrict
#print axioms ZNet.rounds_sound
#print axioms ZNet.split_sound
#print axioms ZNet.S_prod
#print axioms ZNet.r_cross
#print axioms ZNet.r_sq
#print axioms ZNet.cs_weighted
#print axioms ZNet.eq_neg_of_add
#print axioms ZNet.sq_le_sq
#print axioms ZNet.neg_sq
#print axioms ZNet.cancel_A
#print axioms ZNet.kcl_orth
#print axioms ZNet.r_gdu
#print axioms ZNet.r_cross2
#print axioms ZNet.energy_perturbation
#print axioms ZNet.perturbation_branch
#print axioms ZNet.laplacian_bilinear
#print axioms ZNet.lap_symm
#print axioms ZNet.kcl_form
#print axioms ZNet.r_t1
#print axioms ZNet.r_t2
#print axioms ZNet.target_identity
#print axioms ZNet.target_second
#print axioms ZNet.abs_S
#print axioms ZNet.target_first
#print axioms ZNet.target_enclosure
#print axioms ZNet.pair_cs
#print axioms ZNet.sub_nonneg_of_le
#print axioms ZNet.le_of_sub_nonneg
#print axioms ZNet.le_of_sub_nonpos
#print axioms ZNet.sq_diff
#print axioms ZNet.sub_sub_cancel
#print axioms ZNet.split_mul
#print axioms ZNet.quad_bound
#print axioms ZNet.neg_add
#print axioms ZNet.neg_zero
#print axioms ZNet.S_neg
#print axioms ZNet.reff_identity
#print axioms ZNet.pair_center
