-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
/-!
# ZHypercircle — the skeleton of ztl-stand's continuum bounds (Prager–Synge), in an abstract energy space. Zero axioms.

ztl-stand's `ustand/hypercircle.py` (2026-11-01) brackets the compliance `f(u)` of an elastic plate — the CONTINUUM,
not its mesh — and any linear output by polarisation. Every step after the two classical premises is algebra in an
inner-product space, proved here:
  `cs`           Cauchy–Schwarz for a symmetric bilinear form with `a(w,w) ≥ 0`: `a(x,y)² ≤ a(x,x)·a(y,y)`;
  `lower`        `a(u,v) = f(v)` (the weak form), `a(u,u) = f(u)`: `f(v)² ≤ f(u)·a(v,v)` — any admissible `v`;
  `upper`        `(τ,σ) = f(u)` (Green, `τ` equilibrated), `(σ,σ) = f(u)`: `f(u) ≤ (τ,τ)` — any admissible `τ`;
  `polarise`     `w± = s·u ± r·z`, `s·r = 1`: `a(w+,w+) − a(w−,w−) = 4·a(u,z)` — so brackets on the two compliances
                 bracket the output `a(u,z) = J(u)`;
  `lower_box`, `upper_box`  a modulus anywhere in `E(1 ± t)`: the bounds carry over with `1 + t` and `1 − t`.
PREMISES, named and NOT proved here: linear elasticity is the model (the weak form `a(u,v) = f(v)` for every
admissible `v`), and Green's formula (`(τ, σ) = f(u)` for an equilibrated `τ`). VR discipline: the empty axiom list.
-/
namespace ZHypercircle
open ZNet
variable {α : Type}

/-- An energy space: vectors with addition and scaling, and a symmetric bilinear form that is never negative on
the diagonal (the strain energy, or the complementary energy). -/
structure ESpace (F : OF α) (V : Type) where
  add : V → V → V
  smul : α → V → V
  a : V → V → α
  symm : ∀ x y, a x y = a y x
  add_left : ∀ x y z, a (add x y) z = F.add (a x z) (a y z)
  smul_left : ∀ c x y, a (smul c x) y = F.mul c (a x y)
  nonneg : ∀ x, F.le F.zero (a x x)

variable {V : Type}

theorem add_right (F : OF α) (E : ESpace F V) (x y z : V) : E.a z (E.add x y) = F.add (E.a z x) (E.a z y) := by
  rw [E.symm, E.add_left, E.symm x z, E.symm y z]

theorem smul_right (F : OF α) (E : ESpace F V) (c : α) (x y : V) : E.a y (E.smul c x) = F.mul c (E.a y x) := by
  rw [E.symm, E.smul_left, E.symm x y]

/-- `a(px + qy, px + qy) = p²a(x,x) + (pq·a(x,y) + pq·a(x,y)) + q²a(y,y)`, grouped. -/
theorem expand (F : OF α) (E : ESpace F V) (p q : α) (x y : V) :
    E.a (E.add (E.smul p x) (E.smul q y)) (E.add (E.smul p x) (E.smul q y)) =
      F.add (F.add (F.mul p (F.mul p (E.a x x))) (F.mul p (F.mul q (E.a x y))))
            (F.add (F.mul q (F.mul p (E.a x y))) (F.mul q (F.mul q (E.a y y)))) := by
  rw [E.add_left, add_right, add_right, E.smul_left, E.smul_left, E.smul_left, E.smul_left, smul_right,
    smul_right, smul_right, smul_right, E.symm y x]

theorem neg_mul' (F : OF α) (a b : α) : F.mul a (F.neg b) = F.neg (F.mul a b) := by
  rw [F.mul_comm, F.neg_mul, F.mul_comm]

theorem cancel_pos (F : OF α) {lam a b : α} (hl : F.le F.zero lam) (hne : lam ≠ F.zero)
    (h : F.le (F.mul lam a) (F.mul lam b)) : F.le a b := by
  cases F.le_total a b with
  | inl hab => exact hab
  | inr hba =>
    have h2 := F.le_antisymm h (F.mul_le_mul_left hl hba)
    have h3 : F.mul lam (F.add a (F.neg b)) = F.zero := by
      rw [F.mul_add, neg_mul', h2, F.add_neg]
    cases F.mul_eq_zero h3 with
    | inl h0 => exact absurd h0 hne
    | inr h0 =>
      have := eq_neg_of_add F h0
      rw [F.neg_neg] at this
      rw [this]; exact F.le_refl b

/-- CAUCHY–SCHWARZ, without square roots: `a(x,y)² ≤ a(x,x)·a(y,y)` when `a(y,y) ≠ 0`. With `B = a(y,y)`,
`X = a(x,y)`: `0 ≤ a(Bx − Xy, Bx − Xy) = B·(B·a(x,x)) − B·X²`, and `B > 0` cancels. -/
theorem cs_weak (F : OF α) (E : ESpace F V) (x y : V) :
    F.le (F.mul (E.a y y) (F.mul (E.a x y) (E.a x y))) (F.mul (E.a y y) (F.mul (E.a y y) (E.a x x))) := by
  generalize hA : E.a x x = A
  generalize hB : E.a y y = B
  generalize hX : E.a x y = X
  have h0 := E.nonneg (E.add (E.smul B x) (E.smul (F.neg X) y))
  rw [expand, hA, hB, hX] at h0
  rw [F.neg_mul, F.neg_mul, neg_mul'] at h0
  rw [F.neg_mul X (F.mul (F.neg X) B), F.neg_mul X B, neg_mul', F.neg_neg] at h0
  have e : F.mul X (F.mul B X) = F.mul B (F.mul X X) := by rw [← F.mul_assoc, F.mul_comm X B, F.mul_assoc]
  have e2 : F.mul X (F.mul X B) = F.mul B (F.mul X X) := by rw [← F.mul_assoc, F.mul_comm (F.mul X X) B]
  rw [e, e2] at h0
  rw [F.add_comm (F.neg (F.mul B (F.mul X X))) (F.mul B (F.mul X X)), F.add_neg, F.add_zero] at h0
  exact le_of_sub_nonneg F h0

theorem cs (F : OF α) (E : ESpace F V) (x y : V) (hB0 : E.a y y ≠ F.zero) :
    F.le (F.mul (E.a x y) (E.a x y)) (F.mul (E.a x x) (E.a y y)) := by
  have h2 := cancel_pos F (E.nonneg y) hB0 (cs_weak F E x y)
  rw [F.mul_comm (E.a y y) (E.a x x)] at h2
  exact h2

/-- THE LOWER BOUND. The weak form at `v` (`a(u,v) = f(v)`) and at `u` (`a(u,u) = f(u)`), `a(v,v) ≠ 0`:
`f(v)² ≤ f(u)·a(v,v)` — the stand's `f(v)²/a(v,v) ≤ f(u)`, for ANY admissible `v`. -/
theorem lower (F : OF α) (E : ESpace F V) (u v : V) (fu fv : α) (hv : E.a u v = fv) (hu : E.a u u = fu)
    (hB0 : E.a v v ≠ F.zero) : F.le (F.mul fv fv) (F.mul fu (E.a v v)) := by
  have := cs F E u v hB0
  rwa [hv, hu] at this

/-- `0 ≤ c`, `0 ≤ T`, `c·(c·c) ≤ c·(c·T)`: `c ≤ T` (no case on `c = 0`: `mul_eq_zero` decides it). -/
theorem le_of_cube (F : OF α) {c T : α} (hc : F.le F.zero c) (hT : F.le F.zero T)
    (h : F.le (F.mul c (F.mul c c)) (F.mul c (F.mul c T))) : F.le c T := by
  cases F.le_total c T with
  | inl h' => exact h'
  | inr hTc =>
    have hcc : F.le F.zero (F.mul c c) := F.mul_nonneg hc hc
    have h' : F.le (F.mul (F.mul c c) c) (F.mul (F.mul c c) T) := by
      rw [F.mul_assoc, F.mul_assoc]; exact h
    have h2 := F.le_antisymm h' (F.mul_le_mul_left hcc hTc)
    have h3 : F.mul (F.mul c c) (F.add c (F.neg T)) = F.zero := by
      rw [F.mul_add, neg_mul', h2, F.add_neg]
    cases F.mul_eq_zero h3 with
    | inl h0 =>
      cases F.mul_eq_zero h0 with
      | inl e => rw [e]; exact hT
      | inr e => rw [e]; exact hT
    | inr h0 =>
      have := eq_neg_of_add F h0
      rw [F.neg_neg] at this
      rw [this]; exact F.le_refl T

/-- THE UPPER BOUND. `σ` the true stress, `(σ,σ) = f(u)` (the energy); `τ` equilibrated, `(τ,σ) = f(u)` (Green's
formula): `f(u) ≤ (τ,τ)` — the stand's `‖τ‖²`, for ANY statically admissible `τ`. -/
theorem upper (F : OF α) (S : ESpace F V) (tau sig : V) (fu : α) (hs : S.a sig sig = fu) (ht : S.a tau sig = fu) :
    F.le fu (S.a tau tau) := by
  have hfu : F.le F.zero fu := hs ▸ S.nonneg sig
  have h := cs_weak F S tau sig
  rw [ht, hs] at h
  exact le_of_cube F hfu (S.nonneg tau) h

/-- POLARISATION. `w+ = s·u + r·z`, `w− = s·u + (−r)·z`, `s·r = 1`: `a(w−,w−) + 4·a(u,z) = a(w+,w+)`. -/
theorem polarise (F : OF α) (E : ESpace F V) (u z : V) (s r : α) (hsr : F.mul s r = F.one) :
    F.add (E.a (E.add (E.smul s u) (E.smul (F.neg r) z)) (E.add (E.smul s u) (E.smul (F.neg r) z)))
          (F.add (F.add (E.a u z) (E.a u z)) (F.add (E.a u z) (E.a u z))) =
      E.a (E.add (E.smul s u) (E.smul r z)) (E.add (E.smul s u) (E.smul r z)) := by
  rw [expand, expand]
  have h1 : F.mul s (F.mul r (E.a u z)) = E.a u z := by rw [← F.mul_assoc, hsr, F.mul_comm, F.mul_one]
  have h2 : F.mul r (F.mul s (E.a u z)) = E.a u z := by
    rw [← F.mul_assoc, F.mul_comm r s, hsr, F.mul_comm, F.mul_one]
  have h3 : F.mul (F.neg r) (F.mul (F.neg r) (E.a z z)) = F.mul r (F.mul r (E.a z z)) := by
    rw [F.neg_mul, F.neg_mul, neg_mul', F.neg_neg]
  rw [h3, F.neg_mul, neg_mul', F.neg_mul, h1, h2]
  generalize F.mul s (F.mul s (E.a u u)) = P
  generalize F.mul r (F.mul r (E.a z z)) = Q
  generalize E.a u z = X
  -- ((P + −X) + (−X + Q)) + ((X + X) + (X + X)) = (P + X) + (X + Q)
  have cx : ∀ Y, F.add (F.neg X) (F.add X Y) = Y := fun Y => by
    rw [← F.add_assoc, F.add_comm (F.neg X) X, F.add_neg, zero_add]
  have lc : ∀ a b c : α, F.add a (F.add b c) = F.add b (F.add a c) := fun a b c => by
    rw [← F.add_assoc, F.add_comm a b, F.add_assoc]
  rw [F.add_assoc P (F.neg X), F.add_assoc P, F.add_assoc (F.neg X) (F.add (F.neg X) Q), F.add_assoc (F.neg X) Q,
    F.add_assoc X X (F.add X X)]
  rw [lc Q X, cx, lc (F.neg X) Q, cx]
  rw [F.add_assoc P X, ← F.add_assoc X X Q, F.add_comm (F.add X X) Q]

/-- THE OUTPUT'S BRACKET. With the two compliances bracketed, `lo+ ≤ a(w+,w+) ≤ hi+`, `lo− ≤ a(w−,w−) ≤ hi−`:
`lo+ ≤ hi− + 4J` and `4J + lo− ≤ hi+`, `J = a(u,z)` — the stand's `[(lo+ − hi−)/4, (hi+ − lo−)/4]`. -/
theorem output_bracket (F : OF α) (E : ESpace F V) (u z : V) (s r lp hp lm hm : α) (hsr : F.mul s r = F.one)
    (hlp : F.le lp (E.a (E.add (E.smul s u) (E.smul r z)) (E.add (E.smul s u) (E.smul r z))))
    (hhp : F.le (E.a (E.add (E.smul s u) (E.smul r z)) (E.add (E.smul s u) (E.smul r z))) hp)
    (hlm : F.le lm (E.a (E.add (E.smul s u) (E.smul (F.neg r) z)) (E.add (E.smul s u) (E.smul (F.neg r) z))))
    (hhm : F.le (E.a (E.add (E.smul s u) (E.smul (F.neg r) z)) (E.add (E.smul s u) (E.smul (F.neg r) z))) hm) :
    F.le lp (F.add hm (F.add (F.add (E.a u z) (E.a u z)) (F.add (E.a u z) (E.a u z)))) ∧
    F.le (F.add lm (F.add (F.add (E.a u z) (E.a u z)) (F.add (E.a u z) (E.a u z)))) hp := by
  have e := polarise F E u z s r hsr
  constructor
  · rw [← e] at hlp
    exact F.le_trans hlp (F.add_le_add hhm (F.le_refl _))
  · rw [← e] at hhp
    exact F.le_trans (F.add_le_add hlm (F.le_refl _)) hhp

/-- THE BOX, below: `f(v)² ≤ f(u_E)·a_E(v,v)`, `a_E(v,v) ≤ m·a_0(v,v)` (`m = 1 + t`, the modulus at most `m` times
nominal), `0 ≤ f(u_E)`: `f(v)² ≤ f(u_E)·(m·a_0(v,v))`. -/
theorem lower_box (F : OF α) {fv fu aE a0 m : α} (h : F.le (F.mul fv fv) (F.mul fu aE)) (hm : F.le aE (F.mul m a0))
    (hfu : F.le F.zero fu) : F.le (F.mul fv fv) (F.mul fu (F.mul m a0)) :=
  F.le_trans h (F.mul_le_mul_left hfu hm)

/-- THE BOX, above: `f(u_E) ≤ ‖τ‖²_E`, `m·‖τ‖²_E ≤ ‖τ‖²_0` (`m = 1 − t ≥ 0`, the compliance at most `1/m` times
nominal): `m·f(u_E) ≤ ‖τ‖²_0`. -/
theorem upper_box (F : OF α) {fu tE t0 m : α} (h : F.le fu tE) (hm0 : F.le F.zero m) (hm : F.le (F.mul m tE) t0) :
    F.le (F.mul m fu) t0 :=
  F.le_trans (F.mul_le_mul_left hm0 h) hm

end ZHypercircle

#print axioms ZHypercircle.cs_weak
#print axioms ZHypercircle.cs
#print axioms ZHypercircle.lower
#print axioms ZHypercircle.upper
#print axioms ZHypercircle.polarise
#print axioms ZHypercircle.output_bracket
#print axioms ZHypercircle.lower_box
#print axioms ZHypercircle.upper_box
