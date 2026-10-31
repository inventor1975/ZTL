-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
import ZRound
import ZEnergy
/-!
# ZFloatPath — the centre of `zenergy.certify_output_fp`, from float solves. Zero axioms.

The floating path (2026-11-01) does not solve `K0 u0 = f`, `K0 y0 = e` exactly: it takes approximations `ũ`, `ỹ`,
computes the residuals `r_u = f − K0 ũ`, `r_y = e − K0 ỹ` exactly, and a proved `λ` with `λ|v|² ≤ vᵀK0v`
(`ZRound.pd_lower`). Here, for `K0 = Σ_e g_e s_e s_eᵀ` (ZNet's `lap`; `g_e ≥ 0`) and its energy form
`B(a, b) = Σ_e g_e (s_e·a)(s_e·b)`:
  `residual_energy`  `K0 ε = r` and `λ|v|² ≤ B(v, v)` for every `v` ⇒ `λ·B(ε, ε) ≤ |r|²`;
  `centre_identity`  `e·u0 = e·ũ + ỹ·r_u + B(y0 − ỹ, u0 − ũ)` — exact;
  `cs_B`             `B(a, b)² ≤ B(a, a) B(b, b)`;
  `centre_bound`     with `λ e_y² ≥ |r_y|²`, `λ e_u² ≥ |r_u|²`, `λ ≠ 0`, `e_y, e_u ≥ 0`: `|B(ε_y, ε_u)| ≤ e_y e_u` —
                     so `e·u0` lies within `e_y e_u` of `e·ũ + ỹ·r_u`, the kernel's `centre ± cerr`.
VR discipline: `#print axioms` at the end — the empty list, every line.
-/
namespace ZFloatPath
open ZNet
variable {α : Type}

/-- The energy form `B(a, b) = Σ_e g_e (s_e·a)(s_e·b)`. -/
def B (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α) : α :=
  S F es (fun e => F.mul (g e) (F.mul (dot F l s a e) (dot F l s b e)))

/-- `(K0 x)_i = Σ_j lap_ij x_j`. -/
def Kx (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (x : Nat → α) (i : Nat) : α :=
  S F l (fun j => F.mul (lap F es g s i j) (x j))

def vsub (F : OF α) (a b : Nat → α) : Nat → α := fun i => F.add (a i) (F.neg (b i))

theorem S_neg (F : OF α) (f : Nat → α) (l : List Nat) : S F l (fun i => F.neg (f i)) = F.neg (S F l f) := by
  have h : F.add (S F l f) (S F l (fun i => F.neg (f i))) = F.zero := by
    rw [← S_add F _ _ l]
    rw [S_congr F l (fun i _ => F.add_neg (f i))]
    exact S_zero F l
  have h2 := eq_neg_of_add F (by rw [F.add_comm]; exact h)
  exact h2

/-- `Σ_i v_i (K0 x)_i = B(v, x)`. -/
theorem weak (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (v x : Nat → α) :
    S F l (fun i => F.mul (v i) (Kx F l es g s x i)) = B F l es g s v x := by
  unfold Kx B
  rw [← laplacian_bilinear F l es g s v x]
  exact S_congr F l (fun i _ => by rw [← S_mul F (v i) _ l])

theorem B_symm (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α) :
    B F l es g s a b = B F l es g s b a := by
  unfold B; exact S_congr F es (fun e _ => by rw [F.mul_comm (dot F l s a e) _])

theorem dot_sub (F : OF α) (l : List Nat) (s : Nat → Nat → α) (a b : Nat → α) (e : Nat) :
    dot F l s (vsub F a b) e = F.add (dot F l s a e) (F.neg (dot F l s b e)) := by
  unfold dot vsub
  rw [← S_neg F _ l, ← S_add F _ _ l]
  exact S_congr F l (fun i _ => by rw [F.mul_add, mul_neg])

theorem B_sub_left (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b c : Nat → α) :
    B F l es g s (vsub F a b) c = F.add (B F l es g s a c) (F.neg (B F l es g s b c)) := by
  unfold B
  rw [← S_neg F _ es, ← S_add F _ _ es]
  exact S_congr F es (fun e _ => by
    rw [dot_sub, add_mul, F.mul_add, F.neg_mul, mul_neg])

theorem Kx_sub (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α) (i : Nat) :
    Kx F l es g s (vsub F a b) i = F.add (Kx F l es g s a i) (F.neg (Kx F l es g s b i)) := by
  unfold Kx vsub
  rw [← S_neg F _ l, ← S_add F _ _ l]
  exact S_congr F l (fun j _ => by rw [F.mul_add, mul_neg])

/-- `K0 ε = r`, `λ|v|² ≤ B(v, v)` for all `v`, `0 ≤ λ`: `λ·B(ε, ε) ≤ |r|²`. -/
theorem residual_energy (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (eps r : Nat → α)
    (lam : α) (hl : F.le F.zero lam)
    (hKe : ∀ i, List.Mem i l → r i = Kx F l es g s eps i)
    (hpd : ∀ v : Nat → α, F.le (F.mul lam (S F l (fun i => F.mul (v i) (v i)))) (B F l es g s v v)) :
    F.le (F.mul lam (B F l es g s eps eps)) (S F l (fun i => F.mul (r i) (r i))) := by
  have hE : S F l (fun i => F.mul (eps i) (r i)) = B F l es g s eps eps := by
    rw [← weak F l es g s eps eps]
    exact S_congr F l (fun i hi => by rw [hKe i hi])
  have h := energy_bound F l eps r lam hl (by rw [hE]; exact hpd eps)
  rw [hE] at h
  exact h

/-- THE CENTRE, exact: `e·u0 = e·ũ + ỹ·r_u + B(y0 − ỹ, u0 − ũ)`. -/
theorem centre_identity (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α)
    (e f u0 y0 ut yt ru : Nat → α)
    (hy : ∀ i, List.Mem i l → e i = Kx F l es g s y0 i)
    (hu : ∀ i, List.Mem i l → f i = Kx F l es g s u0 i)
    (hr : ∀ i, List.Mem i l → ru i = F.add (f i) (F.neg (Kx F l es g s ut i))) :
    S F l (fun i => F.mul (e i) (u0 i)) =
      F.add (F.add (S F l (fun i => F.mul (e i) (ut i))) (S F l (fun i => F.mul (yt i) (ru i))))
            (B F l es g s (vsub F y0 yt) (vsub F u0 ut)) := by
  let eu := vsub F u0 ut
  -- r_u = K0 (u0 − ũ)
  have hr' : ∀ i, List.Mem i l → ru i = Kx F l es g s eu i := fun i hi => by
    rw [hr i hi, hu i hi]; exact (Kx_sub F l es g s u0 ut i).symm
  -- ỹ·r_u = B(ỹ, ε_u)
  have h1 : S F l (fun i => F.mul (yt i) (ru i)) = B F l es g s yt eu := by
    rw [← weak F l es g s yt eu]; exact S_congr F l (fun i hi => by rw [hr' i hi])
  -- e·ε_u = B(y0, ε_u)
  have h2 : S F l (fun i => F.mul (e i) (eu i)) = B F l es g s y0 eu := by
    rw [B_symm, ← weak F l es g s eu y0]
    exact S_congr F l (fun i hi => by rw [hy i hi, F.mul_comm])
  -- e·u0 = e·ũ + e·ε_u
  have h3 : S F l (fun i => F.mul (e i) (u0 i)) =
      F.add (S F l (fun i => F.mul (e i) (ut i))) (S F l (fun i => F.mul (e i) (eu i))) := by
    rw [← S_add F _ _ l]
    exact S_congr F l (fun i _ => by
      show F.mul (e i) (u0 i) = F.add (F.mul (e i) (ut i)) (F.mul (e i) (F.add (u0 i) (F.neg (ut i))))
      rw [← F.mul_add, F.add_comm (u0 i) (F.neg (ut i)), ← F.add_assoc, F.add_neg, zero_add])
  -- B(y0, ε) = B(ỹ, ε) + B(y0 − ỹ, ε)
  have h4 : B F l es g s y0 eu = F.add (B F l es g s yt eu) (B F l es g s (vsub F y0 yt) eu) := by
    rw [B_sub_left, F.add_comm (B F l es g s y0 eu) _, ← F.add_assoc, F.add_neg, zero_add]
  rw [h3, h2, h4, ← h1, F.add_assoc]

/-- Cauchy–Schwarz in the energy: `B(a, b)² ≤ B(a, a)·B(b, b)`. -/
theorem cs_B (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α)
    (gpos : ∀ e, F.le F.zero (g e)) :
    F.le (F.mul (B F l es g s a b) (B F l es g s a b)) (F.mul (B F l es g s a a) (B F l es g s b b)) :=
  cs_weighted F es g (fun e => dot F l s a e) (fun e => dot F l s b e) gpos

/-- `0 ≤ λ`, `λ ≠ 0`, `λa ≤ λb` ⇒ `a ≤ b`. -/
theorem cancel_pos (F : OF α) {lam a b : α} (hl : F.le F.zero lam) (hne : lam ≠ F.zero)
    (h : F.le (F.mul lam a) (F.mul lam b)) : F.le a b := by
  cases F.le_total a b with
  | inl hab => exact hab
  | inr hba =>
    have h2 := F.le_antisymm h (F.mul_le_mul_left hl hba)
    have h3 : F.mul lam (F.add a (F.neg b)) = F.zero := by
      rw [F.mul_add, mul_neg, h2, F.add_neg]
    cases F.mul_eq_zero h3 with
    | inl h0 => exact absurd h0 hne
    | inr h0 =>
      have := eq_neg_of_add F h0
      rw [F.neg_neg] at this
      rw [this]; exact F.le_refl b

/-- THE CENTRE'S ERROR. `λ e_y² ≥ |r_y|²`, `λ e_u² ≥ |r_u|²` (the kernel's rounded-up roots), `K0 ε_y = r_y`,
`K0 ε_u = r_u`, `λ` proved (`λ|v|² ≤ B(v,v)`), `λ ≠ 0`: `|B(ε_y, ε_u)| ≤ e_y·e_u`. -/
theorem centre_bound (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α)
    (epy epu ry ru : Nat → α) (lam ey eu : α) (gpos : ∀ e, F.le F.zero (g e))
    (hl : F.le F.zero lam) (hne : lam ≠ F.zero) (hey : F.le F.zero ey) (heu : F.le F.zero eu)
    (hKy : ∀ i, List.Mem i l → ry i = Kx F l es g s epy i)
    (hKu : ∀ i, List.Mem i l → ru i = Kx F l es g s epu i)
    (hpd : ∀ v : Nat → α, F.le (F.mul lam (S F l (fun i => F.mul (v i) (v i)))) (B F l es g s v v))
    (hry : F.le (S F l (fun i => F.mul (ry i) (ry i))) (F.mul lam (F.mul ey ey)))
    (hru : F.le (S F l (fun i => F.mul (ru i) (ru i))) (F.mul lam (F.mul eu eu))) :
    F.le (F.abs (B F l es g s epy epu)) (F.mul ey eu) := by
  have by_ : F.le (B F l es g s epy epy) (F.mul ey ey) :=
    cancel_pos F hl hne (F.le_trans (residual_energy F l es g s epy ry lam hl hKy hpd) hry)
  have bu_ : F.le (B F l es g s epu epu) (F.mul eu eu) :=
    cancel_pos F hl hne (F.le_trans (residual_energy F l es g s epu ru lam hl hKu hpd) hru)
  have hBy0 : F.le F.zero (B F l es g s epy epy) :=
    S_nonneg F es (fun e _ => F.mul_nonneg (gpos e) (F.sq_nonneg _))
  have hsq : F.le (F.mul (F.abs (B F l es g s epy epu)) (F.abs (B F l es g s epy epu)))
      (F.mul (F.mul ey eu) (F.mul ey eu)) := by
    rw [ZRound.abs_sq, mul4 F ey eu ey eu]
    apply F.le_trans (cs_B F l es g s epy epu gpos)
    apply F.le_trans (F.mul_le_mul_left hBy0 bu_)
    rw [F.mul_comm (B F l es g s epy epy) _, F.mul_comm (F.mul ey ey) _]
    exact F.mul_le_mul_left (F.mul_nonneg heu heu) by_
  exact ZRound.le_of_sq_le F (F.abs_nonneg _) (F.mul_nonneg hey heu) hsq

/-! ## The norms: from the residual, and Minkowski -/

def vadd (F : OF α) (a b : Nat → α) : Nat → α := fun i => F.add (a i) (b i)

theorem dot_add (F : OF α) (l : List Nat) (s : Nat → Nat → α) (a b : Nat → α) (e : Nat) :
    dot F l s (vadd F a b) e = F.add (dot F l s a e) (dot F l s b e) := by
  unfold dot vadd
  rw [← S_add F _ _ l]
  exact S_congr F l (fun i _ => F.mul_add _ _ _)

/-- `B(a + b, a + b) = B(a,a) + (B(a,b) + B(a,b)) + B(b,b)` — the expansion, term by term. -/
theorem B_expand (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α) :
    B F l es g s (vadd F a b) (vadd F a b) =
      F.add (F.add (B F l es g s a a) (F.add (B F l es g s a b) (B F l es g s a b))) (B F l es g s b b) := by
  unfold B
  rw [← S_add F _ _ es, ← S_add F _ _ es, ← S_add F _ _ es]
  exact S_congr F es (fun e _ => by
    rw [dot_add]
    show F.mul (g e) (F.mul (F.add (dot F l s a e) (dot F l s b e)) (F.add (dot F l s a e) (dot F l s b e))) =
      F.add (F.add (F.mul (g e) (F.mul (dot F l s a e) (dot F l s a e)))
        (F.add (F.mul (g e) (F.mul (dot F l s a e) (dot F l s b e))) (F.mul (g e) (F.mul (dot F l s a e) (dot F l s b e)))))
        (F.mul (g e) (F.mul (dot F l s b e) (dot F l s b e)))
    rw [← F.mul_add, ← F.mul_add, ← F.mul_add]
    congr 1
    rw [add_mul, F.mul_add, F.mul_add, F.mul_comm (dot F l s b e) (dot F l s a e), F.add_assoc, F.add_assoc,
      F.add_assoc])

/-- MINKOWSKI in the energy, squared: `B(a,a) ≤ A²`, `B(b,b) ≤ C²`, `A, C ≥ 0` ⇒ `B(a+b, a+b) ≤ (A + C)²`. -/
theorem minkowski (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α) (A C : α)
    (gpos : ∀ e, F.le F.zero (g e)) (hA0 : F.le F.zero A) (hC0 : F.le F.zero C)
    (ha : F.le (B F l es g s a a) (F.mul A A)) (hb : F.le (B F l es g s b b) (F.mul C C)) :
    F.le (B F l es g s (vadd F a b) (vadd F a b)) (F.mul (F.add A C) (F.add A C)) := by
  have hBa : F.le F.zero (B F l es g s a a) := S_nonneg F es (fun e _ => F.mul_nonneg (gpos e) (F.sq_nonneg _))
  have hBb : F.le F.zero (B F l es g s b b) := S_nonneg F es (fun e _ => F.mul_nonneg (gpos e) (F.sq_nonneg _))
  -- |B(a,b)| ≤ A C
  have hab : F.le (F.abs (B F l es g s a b)) (F.mul A C) := by
    apply ZRound.le_of_sq_le F (F.abs_nonneg _) (F.mul_nonneg hA0 hC0)
    rw [ZRound.abs_sq, mul4 F A C A C]
    apply F.le_trans (cs_B F l es g s a b gpos)
    apply F.le_trans (F.mul_le_mul_left hBa hb)
    rw [F.mul_comm (B F l es g s a a) _, F.mul_comm (F.mul A A) _]
    exact F.mul_le_mul_left (F.mul_nonneg hC0 hC0) ha
  have hab' : F.le (B F l es g s a b) (F.mul A C) := F.le_trans (ZRound.le_abs F _) hab
  rw [B_expand]
  -- (A + C)² = A² + (AC + AC) + C²
  have e : F.mul (F.add A C) (F.add A C) = F.add (F.add (F.mul A A) (F.add (F.mul A C) (F.mul A C))) (F.mul C C) := by
    rw [add_mul, F.mul_add, F.mul_add, F.mul_comm C A, F.add_assoc, F.add_assoc, F.add_assoc]
  rw [e]
  exact F.add_le_add (F.add_le_add ha (F.add_le_add hab' hab')) hb

/-! ## The first order and the rest, from the approximations -/

/-- A part's coefficient `c_P(a, b) = Σ_{e∈P} g_e (s_e·a)(s_e·b)`. -/
def cP (F : OF α) (l : List Nat) (tl : Nat → List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α)
    (P : Nat) : α :=
  S F (tl P) (fun e => F.mul (g e) (F.mul (dot F l s a e) (dot F l s b e)))

/-- `G·((A + D)(Bv + H)) = G·(A Bv) + (G·(D (Bv + H)) + G·(A H))`. -/
theorem ring5 (F : OF α) (G A D Bv H : α) :
    F.mul G (F.mul (F.add A D) (F.add Bv H)) =
      F.add (F.mul G (F.mul A Bv)) (F.add (F.mul G (F.mul D (F.add Bv H))) (F.mul G (F.mul A H))) := by
  rw [add_mul, F.mul_add A Bv H, F.mul_add G (F.add (F.mul A Bv) (F.mul A H)) (F.mul D (F.add Bv H)),
    F.mul_add G (F.mul A Bv) (F.mul A H), F.add_assoc, F.add_comm (F.mul G (F.mul A H)) _]

/-- `c(a + d, b + h) = c(a, b) + (c(d, b + h) + c(a, h))` — the change splits in two. -/
theorem cP_split (F : OF α) (l : List Nat) (tl : Nat → List Nat) (g : Nat → α) (s : Nat → Nat → α)
    (a d b h : Nat → α) (P : Nat) :
    cP F l tl g s (vadd F a d) (vadd F b h) P =
      F.add (cP F l tl g s a b P) (F.add (cP F l tl g s d (vadd F b h) P) (cP F l tl g s a h P)) := by
  unfold cP
  rw [← S_add F _ _ (tl P), ← S_add F _ _ (tl P)]
  exact S_congr F (tl P) (fun e _ => by
    rw [dot_add F l s a d e, dot_add F l s b h e]
    exact ring5 F (g e) (dot F l s a e) (dot F l s d e) (dot F l s b e) (dot F l s h e))

/-- `|c_P(a, b)| ≤ Σ_{e∈P} g_e |s_e·a| |s_e·b|`. -/
theorem cP_abs (F : OF α) (l : List Nat) (tl : Nat → List Nat) (g : Nat → α) (s : Nat → Nat → α)
    (a b : Nat → α) (P : Nat) (gpos : ∀ e, F.le F.zero (g e)) :
    F.le (F.abs (cP F l tl g s a b P))
      (S F (tl P) (fun e => F.mul (g e) (F.mul (F.abs (dot F l s a e)) (F.abs (dot F l s b e))))) := by
  unfold cP
  apply F.le_trans (abs_S F _ (tl P))
  exact S_le F (tl P) (fun e _ => by
    rw [F.abs_mul, F.abs_mul, F.abs_of_nonneg (gpos e)]; exact F.le_refl _)

/-- Over all terms: `Σ_e g_e |s_e·a||s_e·b| ≤ A·C` when `B(a,a) ≤ A²`, `B(b,b) ≤ C²`. -/
theorem abs_cs (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (a b : Nat → α) (A C : α)
    (gpos : ∀ e, F.le F.zero (g e)) (hA0 : F.le F.zero A) (hC0 : F.le F.zero C)
    (ha : F.le (B F l es g s a a) (F.mul A A)) (hb : F.le (B F l es g s b b) (F.mul C C)) :
    F.le (S F es (fun e => F.mul (g e) (F.mul (F.abs (dot F l s a e)) (F.abs (dot F l s b e))))) (F.mul A C) := by
  apply ZRound.le_of_sq_le F (S_nonneg F es (fun e _ => F.mul_nonneg (gpos e)
    (F.mul_nonneg (F.abs_nonneg _) (F.abs_nonneg _)))) (F.mul_nonneg hA0 hC0)
  have h := cs_weighted F es g (fun e => F.abs (dot F l s a e)) (fun e => F.abs (dot F l s b e)) gpos
  have e1 : S F es (fun e => F.mul (g e) (F.mul (F.abs (dot F l s a e)) (F.abs (dot F l s a e)))) = B F l es g s a a :=
    S_congr F es (fun e _ => by rw [ZRound.abs_sq])
  have e2 : S F es (fun e => F.mul (g e) (F.mul (F.abs (dot F l s b e)) (F.abs (dot F l s b e)))) = B F l es g s b b :=
    S_congr F es (fun e _ => by rw [ZRound.abs_sq])
  rw [e1, e2] at h
  apply F.le_trans h
  have hBa : F.le F.zero (B F l es g s a a) := S_nonneg F es (fun e _ => F.mul_nonneg (gpos e) (F.sq_nonneg _))
  rw [mul4 F A C A C]
  apply F.le_trans (F.mul_le_mul_left hBa hb)
  rw [F.mul_comm (B F l es g s a a) _, F.mul_comm (F.mul A A) _]
  exact F.mul_le_mul_left (F.mul_nonneg hC0 hC0) ha

/-- Over the parts: `Σ_P |c_P(a, b)| ≤ A·C` (the terms of all parts are `flat tl pl`). -/
theorem parts_abs_cs (F : OF α) (l : List Nat) (tl : Nat → List Nat) (pl : List Nat) (g : Nat → α)
    (s : Nat → Nat → α) (a b : Nat → α) (A C : α)
    (gpos : ∀ e, F.le F.zero (g e)) (hA0 : F.le F.zero A) (hC0 : F.le F.zero C)
    (ha : F.le (B F l (ZEnergy.flat tl pl) g s a a) (F.mul A A))
    (hb : F.le (B F l (ZEnergy.flat tl pl) g s b b) (F.mul C C)) :
    F.le (S F pl (fun P => F.abs (cP F l tl g s a b P))) (F.mul A C) := by
  apply F.le_trans (S_le F pl (fun P _ => cP_abs F l tl g s a b P gpos))
  rw [← ZEnergy.S_flat F tl _ pl]
  exact abs_cs F l (ZEnergy.flat tl pl) g s a b A C gpos hA0 hC0 ha hb

/-- THE FIRST ORDER FROM THE APPROXIMATIONS (`D1` of the floating path). `y0 = ỹ + ε_y`, `u0 = ũ + ε_u`; norms bounded
in the energy: `B(ε_y) ≤ e_y²`, `B(u0) ≤ N_u²`, `B(ỹ) ≤ n_y²`, `B(ε_u) ≤ e_u²`; `0 ≤ t_P ≤ T`:
`Σ_P t_P |c_P(y0, u0)| ≤ Σ_P t_P |c_P(ỹ, ũ)| + T·(e_y N_u + n_y e_u)`. -/
theorem first_order_fp (F : OF α) (l : List Nat) (tl : Nat → List Nat) (pl : List Nat) (g : Nat → α)
    (s : Nat → Nat → α) (yt epy ut epu t : Nat → α) (T ey Nu ny eu : α)
    (gpos : ∀ e, F.le F.zero (g e)) (hT : ∀ P, List.Mem P pl → F.le F.zero (t P))
    (htT : ∀ P, List.Mem P pl → F.le (t P) T) (hT0 : F.le F.zero T)
    (h0 : F.le F.zero ey) (h1 : F.le F.zero Nu) (h2 : F.le F.zero ny) (h3 : F.le F.zero eu)
    (hey : F.le (B F l (ZEnergy.flat tl pl) g s epy epy) (F.mul ey ey))
    (hNu : F.le (B F l (ZEnergy.flat tl pl) g s (vadd F ut epu) (vadd F ut epu)) (F.mul Nu Nu))
    (hny : F.le (B F l (ZEnergy.flat tl pl) g s yt yt) (F.mul ny ny))
    (heu : F.le (B F l (ZEnergy.flat tl pl) g s epu epu) (F.mul eu eu)) :
    F.le (S F pl (fun P => F.mul (t P) (F.abs (cP F l tl g s (vadd F yt epy) (vadd F ut epu) P))))
      (F.add (S F pl (fun P => F.mul (t P) (F.abs (cP F l tl g s yt ut P))))
             (F.mul T (F.add (F.mul ey Nu) (F.mul ny eu)))) := by
  let c1 := fun P => F.abs (cP F l tl g s epy (vadd F ut epu) P)
  let c2 := fun P => F.abs (cP F l tl g s yt epu P)
  -- per part: t|c(y0,u0)| ≤ t|c(ỹ,ũ)| + T(|c1| + |c2|)
  have hper : ∀ P, List.Mem P pl → F.le (F.mul (t P) (F.abs (cP F l tl g s (vadd F yt epy) (vadd F ut epu) P)))
      (F.add (F.mul (t P) (F.abs (cP F l tl g s yt ut P))) (F.mul T (F.add (c1 P) (c2 P)))) := by
    intro P hP
    rw [cP_split]
    have ha : F.le (F.abs (F.add (cP F l tl g s yt ut P) (F.add (cP F l tl g s epy (vadd F ut epu) P)
        (cP F l tl g s yt epu P)))) (F.add (F.abs (cP F l tl g s yt ut P)) (F.add (c1 P) (c2 P))) :=
      F.le_trans (F.abs_add _ _) (F.add_le_add (F.le_refl _) (F.abs_add _ _))
    apply F.le_trans (F.mul_le_mul_left (hT P hP) ha)
    rw [F.mul_add]
    apply F.add_le_add (F.le_refl _)
    rw [F.mul_comm (t P) _, F.mul_comm T _]
    have hc0 : F.le F.zero (F.add (c1 P) (c2 P)) := by
      have h := F.add_le_add (F.abs_nonneg (cP F l tl g s epy (vadd F ut epu) P)) (F.abs_nonneg (cP F l tl g s yt epu P))
      rw [F.add_zero] at h; exact h
    exact F.mul_le_mul_left hc0 (htT P hP)
  apply F.le_trans (S_le F pl hper)
  rw [S_add F _ _ pl, S_mul F T _ pl, S_add F _ _ pl]
  apply F.add_le_add (F.le_refl _)
  apply F.mul_le_mul_left hT0
  exact F.add_le_add (parts_abs_cs F l tl pl g s epy (vadd F ut epu) ey Nu gpos h0 h1 hey hNu)
    (parts_abs_cs F l tl pl g s yt epu ny eu gpos h2 h3 hny heu)

/-- THE REST FROM THE APPROXIMATIONS. ZNet's `target_second` gives `m²·Sec² ≤ (Σ g (t T0)²)(Σ g (t u0)²)` with
`T0_e = s_e·y0`, `u0_e = s_e·u0`; with `t_e² ≤ T²`, `B(y0) ≤ N_y²`, `B(u0) ≤ N_u²`: `m·|Sec| ≤ T²·N_y·N_u`. -/
theorem rest_fp (F : OF α) (l es : List Nat) (g : Nat → α) (s : Nat → Nat → α) (y0 u0 t : Nat → α)
    (m Sec T Ny Nu : α) (gpos : ∀ e, F.le F.zero (g e)) (hm : F.le F.zero m)
    (hNy : F.le F.zero Ny) (hNu : F.le F.zero Nu)
    (ht : ∀ e, List.Mem e es → F.le (F.mul (t e) (t e)) (F.mul T T))
    (h2 : F.le (F.mul (F.mul m m) (F.mul Sec Sec))
      (F.mul (S F es (fun e => F.mul (g e) (F.mul (F.mul (t e) (dot F l s y0 e)) (F.mul (t e) (dot F l s y0 e)))))
             (S F es (fun e => F.mul (g e) (F.mul (F.mul (t e) (dot F l s u0 e)) (F.mul (t e) (dot F l s u0 e)))))))
    (hy : F.le (B F l es g s y0 y0) (F.mul Ny Ny)) (hu : F.le (B F l es g s u0 u0) (F.mul Nu Nu)) :
    F.le (F.mul m (F.abs Sec)) (F.mul (F.mul T T) (F.mul Ny Nu)) := by
  -- Σ g (t x)² ≤ T² B(x, x)
  have hw : ∀ x : Nat → α, F.le (S F es (fun e => F.mul (g e) (F.mul (F.mul (t e) (dot F l s x e))
      (F.mul (t e) (dot F l s x e))))) (F.mul (F.mul T T) (B F l es g s x x)) := by
    intro x
    unfold B
    rw [← S_mul F (F.mul T T) _ es]
    exact S_le F es (fun e he => by
      rw [mul4 F (t e) (dot F l s x e) (t e) (dot F l s x e), ← F.mul_assoc (g e), F.mul_comm (g e) _,
        F.mul_assoc, ← F.mul_assoc (F.mul T T)]
      rw [F.mul_comm (F.mul T T) (g e), F.mul_assoc (g e) (F.mul T T)]
      rw [F.mul_comm (F.mul (t e) (t e)) _, F.mul_assoc (g e)]
      apply F.mul_le_mul_left (gpos e)
      rw [F.mul_comm (F.mul T T) _]
      exact F.mul_le_mul_left (F.sq_nonneg _) (ht e he))
  have hBy : F.le F.zero (B F l es g s y0 y0) := S_nonneg F es (fun e _ => F.mul_nonneg (gpos e) (F.sq_nonneg _))
  have hBu : F.le F.zero (B F l es g s u0 u0) := S_nonneg F es (fun e _ => F.mul_nonneg (gpos e) (F.sq_nonneg _))
  have hTT : F.le F.zero (F.mul T T) := F.sq_nonneg T
  apply ZRound.le_of_sq_le F (F.mul_nonneg hm (F.abs_nonneg _)) (F.mul_nonneg hTT (F.mul_nonneg hNy hNu))
  rw [mul4 F m (F.abs Sec) m (F.abs Sec), ZRound.abs_sq]
  let P := S F es (fun e => F.mul (g e) (F.mul (F.mul (t e) (dot F l s y0 e)) (F.mul (t e) (dot F l s y0 e))))
  have hP0 : F.le F.zero P := S_nonneg F es (fun e _ => F.mul_nonneg (gpos e) (F.sq_nonneg _))
  have s1 := F.mul_le_mul_left hP0 (hw u0)
  have s2 : F.le (F.mul P (F.mul (F.mul T T) (B F l es g s u0 u0)))
      (F.mul (F.mul (F.mul T T) (B F l es g s y0 y0)) (F.mul (F.mul T T) (B F l es g s u0 u0))) := by
    rw [F.mul_comm P _, F.mul_comm (F.mul (F.mul T T) (B F l es g s y0 y0)) _]
    exact F.mul_le_mul_left (F.mul_nonneg hTT hBu) (hw y0)
  have s3 : F.le (F.mul (F.mul (F.mul T T) (B F l es g s y0 y0)) (F.mul (F.mul T T) (B F l es g s u0 u0)))
      (F.mul (F.mul (F.mul T T) (F.mul Ny Nu)) (F.mul (F.mul T T) (F.mul Ny Nu))) := by
    rw [mul4 F (F.mul T T) (B F l es g s y0 y0) (F.mul T T) (B F l es g s u0 u0),
      mul4 F (F.mul T T) (F.mul Ny Nu) (F.mul T T) (F.mul Ny Nu), mul4 F Ny Nu Ny Nu]
    apply F.mul_le_mul_left (F.mul_nonneg hTT hTT)
    apply F.le_trans (F.mul_le_mul_left hBy hu)
    rw [F.mul_comm (B F l es g s y0 y0) _, F.mul_comm (F.mul Ny Ny) _]
    exact F.mul_le_mul_left (F.mul_nonneg hNu hNu) hy
  exact F.le_trans h2 (F.le_trans s1 (F.le_trans s2 s3))

end ZFloatPath

#print axioms ZFloatPath.S_neg
#print axioms ZFloatPath.weak
#print axioms ZFloatPath.B_symm
#print axioms ZFloatPath.dot_sub
#print axioms ZFloatPath.B_sub_left
#print axioms ZFloatPath.Kx_sub
#print axioms ZFloatPath.residual_energy
#print axioms ZFloatPath.centre_identity
#print axioms ZFloatPath.cs_B
#print axioms ZFloatPath.cancel_pos
#print axioms ZFloatPath.centre_bound
#print axioms ZFloatPath.dot_add
#print axioms ZFloatPath.B_expand
#print axioms ZFloatPath.minkowski
#print axioms ZFloatPath.cP_split
#print axioms ZFloatPath.cP_abs
#print axioms ZFloatPath.abs_cs
#print axioms ZFloatPath.ring5
#print axioms ZFloatPath.parts_abs_cs
#print axioms ZFloatPath.first_order_fp
#print axioms ZFloatPath.rest_fp
