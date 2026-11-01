-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Formalised in Lean by Claude (Anthropic, an AI model) under the curation of Vitaly Reznik, 2026-11-01.
import ZNet
import ZRound
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
  `lower_box`, `upper_box`  a modulus anywhere in `E(1 ± t)`: the bounds carry over with `1 + t` and `1 − t`;
  `perturb_identity`  an output under the box, exactly: `J(u_E) − J(u_0) = −d(u_E, z_0)` (`a_E = a_0 + d`);
  `perturb_split`     `|d(u_E, z_0)| ≤ |d(u_0, z_0)| + |d(u_E − u_0, z_0)|` — first order + rest;
  `form_cs`      Cauchy–Schwarz for a perturbation bounded by the energy (`−t·a ≤ d ≤ t·a`): `d(x,y)² ≤ t²a(x,x)a(y,y)`;
  `rest_bound`   the rest: `(1 − t)²·d(u_E − u_0, z_0)² ≤ t⁴·a(u_0,u_0)·a(z_0,z_0)`.
  The first-order term `|d(u_0, z_0)| ≤ t·∫|σ(u_0) : C⁻¹σ(z_0)|` and its bound through the hypercircle centres are
  inequalities between INTEGRALS (pointwise triangle, Cauchy–Schwarz) — named premises, as Green's formula.
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

/-- THE BOX FOR AN OUTPUT, EXACTLY: `a_E = a_0 + d` (the modulus field's energy), `u_E`, `u_0` the weak solutions
under the same load `f`, `z_0` the nominal dual (`J(v) = a_0(z_0, v)`): `J(u_E) − J(u_0) = −d(u_E, z_0)`.
`w = u_E − u_0` is written `u_E + (−1)·u_0`. -/
theorem perturb_identity (F : OF α) (E : ESpace F V) (aE d : V → V → α) (f J : V → α) (uE u0 z0 : V)
    (hd : ∀ x y, aE x y = F.add (E.a x y) (d x y)) (huE : ∀ v, aE uE v = f v) (hu0 : ∀ v, E.a u0 v = f v)
    (hJ : ∀ v, J v = E.a z0 v) :
    F.add (J uE) (F.neg (J u0)) = F.neg (d uE z0) := by
  rw [hJ, hJ, E.symm z0 uE, E.symm z0 u0, hu0]
  have h := huE z0
  rw [hd] at h
  -- a0(uE,z0) + d(uE,z0) = f(z0)  =>  a0(uE,z0) − f(z0) = −d(uE,z0)
  rw [← h, F.add_comm (E.a uE z0) (d uE z0), neg_add, ← F.add_assoc, F.add_comm (E.a uE z0) (F.neg (d uE z0)),
    F.add_assoc, F.add_neg, F.add_zero]

/-- The split, for a `d` additive in its first argument: `d(u_E, z) = d(u_0, z) + d(u_E − u_0, z)` — so
`|J(u_E) − J(u_0)| ≤ |d(u_0, z_0)| + |d(u_E − u_0, z_0)|` (first order + rest). -/
theorem perturb_split (F : OF α) (E : ESpace F V) (d : V → V → α) (uE u0 z0 : V)
    (hadd : ∀ x y z, d (E.add x y) z = F.add (d x z) (d y z))
    (hrecon : E.add u0 (E.add uE (E.smul (F.neg F.one) u0)) = uE) :
    F.le (F.abs (d uE z0)) (F.add (F.abs (d u0 z0)) (F.abs (d (E.add uE (E.smul (F.neg F.one) u0)) z0))) := by
  have e : d uE z0 = F.add (d u0 z0) (d (E.add uE (E.smul (F.neg F.one) u0)) z0) := by
    rw [← hadd, hrecon]
  rw [e]
  exact F.abs_add _ _

/-- A symmetric bilinear form on the same vectors (the energy's perturbation `d`; not signed). -/
structure BForm (F : OF α) (E : ESpace F V) where
  b : V → V → α
  symm : ∀ x y, b x y = b y x
  add_left : ∀ x y z, b (E.add x y) z = F.add (b x z) (b y z)
  smul_left : ∀ c x y, b (E.smul c x) y = F.mul c (b x y)

theorem bexpand (F : OF α) (E : ESpace F V) (D : BForm F E) (p q : α) (x y : V) :
    D.b (E.add (E.smul p x) (E.smul q y)) (E.add (E.smul p x) (E.smul q y)) =
      F.add (F.add (F.mul p (F.mul p (D.b x x))) (F.mul p (F.mul q (D.b x y))))
            (F.add (F.mul q (F.mul p (D.b x y))) (F.mul q (F.mul q (D.b y y)))) := by
  have ar : ∀ x y z, D.b z (E.add x y) = F.add (D.b z x) (D.b z y) := fun x y z => by
    rw [D.symm, D.add_left, D.symm x z, D.symm y z]
  have sr : ∀ c x y, D.b y (E.smul c x) = F.mul c (D.b y x) := fun c x y => by
    rw [D.symm, D.smul_left, D.symm x y]
  rw [D.add_left, ar, ar, D.smul_left, D.smul_left, D.smul_left, D.smul_left, sr, sr, sr, sr, D.symm y x]

/-- The energy itself as a `BForm`. -/
def ofE (F : OF α) (E : ESpace F V) : BForm F E := ⟨E.a, E.symm, E.add_left, E.smul_left⟩

theorem lcomm (F : OF α) (a b c : α) : F.mul a (F.mul b c) = F.mul b (F.mul a c) := by
  rw [← F.mul_assoc, F.mul_comm a b, F.mul_assoc]

theorem addlc (F : OF α) (a b c : α) : F.add a (F.add b c) = F.add b (F.add a c) := by
  rw [← F.add_assoc, F.add_comm a b, F.add_assoc]

/-- The two expansions at `±q`, in four atoms: `b(px+qy) = (P + M) + (M + Q)`, `b(px−qy) = (P + −M) + (−M + Q)`. -/
theorem bexpand_pm (F : OF α) (E : ESpace F V) (D : BForm F E) (p q : α) (x y : V) :
    D.b (E.add (E.smul p x) (E.smul q y)) (E.add (E.smul p x) (E.smul q y)) =
      F.add (F.add (F.mul p (F.mul p (D.b x x))) (F.mul p (F.mul q (D.b x y))))
            (F.add (F.mul p (F.mul q (D.b x y))) (F.mul q (F.mul q (D.b y y)))) ∧
    D.b (E.add (E.smul p x) (E.smul (F.neg q) y)) (E.add (E.smul p x) (E.smul (F.neg q) y)) =
      F.add (F.add (F.mul p (F.mul p (D.b x x))) (F.neg (F.mul p (F.mul q (D.b x y)))))
            (F.add (F.neg (F.mul p (F.mul q (D.b x y)))) (F.mul q (F.mul q (D.b y y)))) := by
  constructor
  · rw [bexpand, lcomm F q p]
  · rw [bexpand, lcomm F (F.neg q) p, F.neg_mul, neg_mul', F.neg_mul, F.neg_mul, neg_mul', F.neg_neg]

/-- PARALLELOGRAM: `b(px+qy) + b(px−qy) = (P + P) + (Q + Q)`. -/
theorem para (F : OF α) (E : ESpace F V) (D : BForm F E) (p q : α) (x y : V) :
    F.add (D.b (E.add (E.smul p x) (E.smul q y)) (E.add (E.smul p x) (E.smul q y)))
          (D.b (E.add (E.smul p x) (E.smul (F.neg q) y)) (E.add (E.smul p x) (E.smul (F.neg q) y))) =
      F.add (F.add (F.mul p (F.mul p (D.b x x))) (F.mul p (F.mul p (D.b x x))))
            (F.add (F.mul q (F.mul q (D.b y y))) (F.mul q (F.mul q (D.b y y)))) := by
  obtain ⟨e1, e2⟩ := bexpand_pm F E D p q x y
  rw [e1, e2]
  generalize F.mul p (F.mul p (D.b x x)) = P
  generalize F.mul p (F.mul q (D.b x y)) = M
  generalize F.mul q (F.mul q (D.b y y)) = Q
  have cm : ∀ Y, F.add M (F.add (F.neg M) Y) = Y := fun Y => by
    rw [← F.add_assoc, F.add_neg, zero_add]
  -- ((P+M)+(M+Q)) + ((P+−M)+(−M+Q))
  rw [add4 F (F.add P M) (F.add M Q) (F.add P (F.neg M)) (F.add (F.neg M) Q)]
  rw [add4 F P M P (F.neg M), F.add_neg, F.add_zero, add4 F M Q (F.neg M) Q, F.add_neg, zero_add]

/-- POLARISATION, general: `b(px+qy) = b(px−qy) + ((M + M) + (M + M))`, `M = p·q·b(x,y)`. -/
theorem bpol (F : OF α) (E : ESpace F V) (D : BForm F E) (p q : α) (x y : V) :
    D.b (E.add (E.smul p x) (E.smul q y)) (E.add (E.smul p x) (E.smul q y)) =
      F.add (D.b (E.add (E.smul p x) (E.smul (F.neg q) y)) (E.add (E.smul p x) (E.smul (F.neg q) y)))
            (F.add (F.add (F.mul p (F.mul q (D.b x y))) (F.mul p (F.mul q (D.b x y))))
                   (F.add (F.mul p (F.mul q (D.b x y))) (F.mul p (F.mul q (D.b x y))))) := by
  obtain ⟨e1, e2⟩ := bexpand_pm F E D p q x y
  rw [e1, e2]
  generalize F.mul p (F.mul p (D.b x x)) = P
  generalize F.mul p (F.mul q (D.b x y)) = M
  generalize F.mul q (F.mul q (D.b y y)) = Q
  -- (P + −M) + (−M + Q) + ((M+M)+(M+M)) = (P+M)+(M+Q)
  have cx : ∀ Y, F.add (F.neg M) (F.add M Y) = Y := fun Y => by
    rw [← F.add_assoc, F.add_comm (F.neg M) M, F.add_neg, zero_add]
  rw [F.add_assoc P (F.neg M) (F.add (F.neg M) Q)]
  rw [F.add_assoc P (F.add (F.neg M) (F.add (F.neg M) Q)), F.add_assoc (F.neg M) (F.add (F.neg M) Q),
    F.add_assoc (F.neg M) Q, F.add_assoc M M (F.add M M), addlc F Q M, cx, addlc F (F.neg M) Q, cx]
  rw [F.add_assoc P M, ← F.add_assoc M M Q, F.add_comm (F.add M M) Q]

/-- CAUCHY–SCHWARZ FOR A BOUNDED PERTURBATION. `d` symmetric bilinear with `−t·a(w,w) ≤ d(w,w) ≤ t·a(w,w)` for every
`w` (the modulus field within `E0(1 ± t)`), `t·a(x,x) ≠ 0`: `d(x,y)² ≤ (t·a(x,x))·(t·a(y,y))`. With `K = d(x,y)`,
`c = t·a(x,x)`, `w± = Kx ± cy`: `0 ≤ (t·a(w−) + d(w−)) + (t·a(w+) − d(w+)) = 2(c·(c·(t·a(y,y))) − c·K²)`. -/
theorem form_cs (F : OF α) (E : ESpace F V) (D : BForm F E) (t : α) (x y : V) (ht : F.le F.zero t)
    (hne : F.mul t (E.a x x) ≠ F.zero)
    (hP : ∀ w, F.le F.zero (F.add (F.mul t (E.a w w)) (D.b w w)))
    (hM : ∀ w, F.le F.zero (F.add (F.mul t (E.a w w)) (F.neg (D.b w w)))) :
    F.le (F.mul (D.b x y) (D.b x y)) (F.mul (F.mul t (E.a x x)) (F.mul t (E.a y y))) := by
  have hc0 : F.le F.zero (F.mul t (E.a x x)) := F.mul_nonneg ht (E.nonneg x)
  generalize hK : D.b x y = K
  generalize hc : F.mul t (E.a x x) = c at hne hc0
  have h := F.add_le_add (hP (E.add (E.smul K x) (E.smul (F.neg c) y))) (hM (E.add (E.smul K x) (E.smul c y)))
  rw [F.add_zero] at h
  have pa : F.add (E.a (E.add (E.smul K x) (E.smul c y)) (E.add (E.smul K x) (E.smul c y)))
      (E.a (E.add (E.smul K x) (E.smul (F.neg c) y)) (E.add (E.smul K x) (E.smul (F.neg c) y))) =
      F.add (F.add (F.mul K (F.mul K (E.a x x))) (F.mul K (F.mul K (E.a x x))))
            (F.add (F.mul c (F.mul c (E.a y y))) (F.mul c (F.mul c (E.a y y)))) := para F E (ofE F E) K c x y
  have po := bpol F E D K c x y
  rw [hK] at po
  rw [po] at h
  generalize E.a (E.add (E.smul K x) (E.smul c y)) (E.add (E.smul K x) (E.smul c y)) = ap at h pa
  generalize E.a (E.add (E.smul K x) (E.smul (F.neg c) y)) (E.add (E.smul K x) (E.smul (F.neg c) y)) = am at h pa
  generalize D.b (E.add (E.smul K x) (E.smul (F.neg c) y)) (E.add (E.smul K x) (E.smul (F.neg c) y)) = dm at h
  rw [lcomm F K c K] at h
  -- h : 0 ≤ (t·am + dm) + (t·ap + −(dm + 4G)), G = c·K²   ==>   0 ≤ t·(ap + am) + −4G
  have e1 : ∀ G, F.add (F.add (F.mul t am) dm) (F.add (F.mul t ap) (F.neg (F.add dm (F.add (F.add G G) (F.add G G))))) =
      F.add (F.mul t (F.add ap am)) (F.neg (F.add (F.add G G) (F.add G G))) := fun G => by
    rw [neg_add, F.mul_add, add4, F.add_comm (F.mul t am) (F.mul t ap), F.add_assoc, ← F.add_assoc dm (F.neg dm),
      F.add_neg, zero_add, ← F.add_assoc]
  rw [e1, pa, F.mul_add, F.mul_add, F.mul_add] at h
  have tK : F.mul t (F.mul K (F.mul K (E.a x x))) = F.mul c (F.mul K K) := by
    rw [lcomm F t K, lcomm F t K, hc, ← F.mul_assoc K K c, F.mul_comm (F.mul K K) c]
  have tc : F.mul t (F.mul c (F.mul c (E.a y y))) = F.mul c (F.mul c (F.mul t (E.a y y))) := by
    rw [lcomm F t c, lcomm F t c]
  rw [tK, tc] at h
  have h2 := le_of_sub_nonneg F h
  have h3 := add_le_cancel F h2
  have h4 := F.le_of_double h3
  exact cancel_pos F hc0 hne h4

/-- `0 ≤ W`, `0 ≤ Y`, `W·(m·W) ≤ W·Y`, `0 ≤ m`: `m·W ≤ Y` (`W = 0` decided by `mul_eq_zero`, no case split). -/
theorem cancel_W (F : OF α) {W m Y : α} (hW : F.le F.zero W) (hY : F.le F.zero Y) (_hm : F.le F.zero m)
    (h : F.le (F.mul W (F.mul m W)) (F.mul W Y)) : F.le (F.mul m W) Y := by
  cases F.le_total (F.mul m W) Y with
  | inl h' => exact h'
  | inr hYm =>
    have h2 := F.le_antisymm h (F.mul_le_mul_left hW hYm)
    have h3 : F.mul W (F.add (F.mul m W) (F.neg Y)) = F.zero := by rw [F.mul_add, neg_mul', h2, F.add_neg]
    cases F.mul_eq_zero h3 with
    | inl e => rw [e, F.mul_zero]; exact hY
    | inr e =>
      have := eq_neg_of_add F e
      rw [F.neg_neg] at this
      rw [this]; exact F.le_refl Y

/-- THE REST, PROVED. `a_E = a_0 + d` with `−t·a_0 ≤ d ≤ t·a_0` on the diagonal, `u_E`, `u_0` the weak solutions,
`w = u_E − u_0` (`u_0 + w = u_E`), `s = 1 − t ≥ 0`, `t·a_0(u_0,u_0) ≠ 0`, `t·a_0(z_0,z_0) ≠ 0`:
`s²·d(z_0,w)² ≤ (t·a_0(z_0,z_0))·(t·(t·(t·a_0(u_0,u_0))))` — `|d(u_E − u_0, z_0)| ≤ t²/(1−t)·‖u_0‖‖z_0‖`, the stand's rest. -/
theorem rest_bound (F : OF α) (E : ESpace F V) (D : BForm F E) (f : V → α) (t s : α) (uE u0 z0 : V)
    (ht : F.le F.zero t) (hs : F.le F.zero s) (hst : F.add s t = F.one)
    (hP : ∀ w, F.le F.zero (F.add (F.mul t (E.a w w)) (D.b w w)))
    (hM : ∀ w, F.le F.zero (F.add (F.mul t (E.a w w)) (F.neg (D.b w w))))
    (huE : ∀ v, F.add (E.a uE v) (D.b uE v) = f v) (hu0 : ∀ v, E.a u0 v = f v)
    (hrecon : E.add u0 (E.add uE (E.smul (F.neg F.one) u0)) = uE)
    (hU : F.mul t (E.a u0 u0) ≠ F.zero) (hZ : F.mul t (E.a z0 z0) ≠ F.zero) :
    F.le (F.mul (F.mul s s) (F.mul (D.b z0 (E.add uE (E.smul (F.neg F.one) u0)))
                                    (D.b z0 (E.add uE (E.smul (F.neg F.one) u0)))))
         (F.mul (F.mul t (E.a z0 z0)) (F.mul t (F.mul t (F.mul t (E.a u0 u0))))) := by
  generalize hw : E.add uE (E.smul (F.neg F.one) u0) = w at hrecon ⊢
  -- a0(w, v) = −d(uE, v)
  have om : ∀ a, F.mul F.one a = a := fun a => by rw [F.mul_comm, F.mul_one]
  have aw : ∀ v, E.a w v = F.neg (D.b uE v) := fun v => by
    rw [← hw, E.add_left, E.smul_left, F.neg_mul, om, hu0, ← huE v, neg_add, ← F.add_assoc, F.add_neg, zero_add]
  -- d(uE, v) = d(u0, v) + d(w, v)
  have dsplit : ∀ v, D.b uE v = F.add (D.b u0 v) (D.b w v) := fun v => by rw [← D.add_left, hrecon]
  have hW0 : F.le F.zero (E.a w w) := E.nonneg w
  have hdw : F.le (F.neg (D.b w w)) (F.mul t (E.a w w)) := by
    have h2 := F.add_le_add (hP w) (F.le_refl (F.neg (D.b w w)))
    rwa [zero_add, F.add_assoc, F.add_neg, F.add_zero] at h2
  have e : E.a w w = F.add (F.neg (D.b u0 w)) (F.neg (D.b w w)) := by rw [aw, dsplit, neg_add]
  generalize hW : E.a w w = W at hW0 hdw e
  -- s·W ≤ −d(u0, w)
  have h1 := F.add_le_add (F.le_refl (F.neg (D.b u0 w))) hdw
  rw [← e] at h1
  have h2 := F.add_le_add h1 (F.le_refl (F.neg (F.mul t W)))
  rw [F.add_assoc (F.neg (D.b u0 w)), F.add_neg, F.add_zero] at h2
  have hW1 : F.add (F.mul s W) (F.mul t W) = W := by rw [← add_mul, hst, om]
  have hx : F.add W (F.neg (F.mul t W)) = F.mul s W := by
    conv => lhs; arg 2; rw [← hW1]
    rw [F.add_assoc, F.add_neg, F.add_zero]
  rw [hx] at h2
  have hsW0 : F.le F.zero (F.mul s W) := F.mul_nonneg hs hW0
  have habs : F.le (F.neg (D.b u0 w)) (F.abs (D.b u0 w)) := by
    have := ZRound.le_abs F (F.neg (D.b u0 w)); rwa [F.abs_neg] at this
  have sq1 := sq_le_sq F hsW0 (F.le_trans h2 habs)
  rw [ZRound.abs_sq] at sq1
  have fcs1 := form_cs F E D t u0 w ht hU hP hM
  rw [hW] at fcs1
  have c1 := F.le_trans sq1 fcs1
  -- (sW)(sW) = W·((s s)W),  (t U0)(t W) = W·(t (t U0))
  have r1 : F.mul (F.mul s W) (F.mul s W) = F.mul W (F.mul (F.mul s s) W) := by
    rw [F.mul_assoc s s W, ← F.mul_assoc W s (F.mul s W), F.mul_comm W s]
  have r2 : F.mul (F.mul t (E.a u0 u0)) (F.mul t W) = F.mul W (F.mul t (F.mul t (E.a u0 u0))) := by
    rw [F.mul_comm (F.mul t (E.a u0 u0)) (F.mul t W), F.mul_assoc t W, lcomm F t W]
  have c2 : F.le (F.mul W (F.mul (F.mul s s) W)) (F.mul W (F.mul t (F.mul t (E.a u0 u0)))) := by
    rw [← r1, ← r2]; exact c1
  have hY : F.le F.zero (F.mul t (F.mul t (E.a u0 u0))) := F.mul_nonneg ht (F.mul_nonneg ht (E.nonneg u0))
  have hm : F.le F.zero (F.mul s s) := F.mul_nonneg hs hs
  have key := cancel_W F hW0 hY hm c2
  have fcs2 := form_cs F E D t z0 w ht hZ hP hM
  rw [hW] at fcs2
  have s1 := F.mul_le_mul_left hm fcs2
  rw [lcomm F (F.mul s s) (F.mul t (E.a z0 z0)), lcomm F (F.mul s s) t] at s1
  have hZ0 : F.le F.zero (F.mul t (E.a z0 z0)) := F.mul_nonneg ht (E.nonneg z0)
  exact F.le_trans s1 (F.mul_le_mul_left hZ0 (F.mul_le_mul_left ht key))

end ZHypercircle

#print axioms ZHypercircle.cs_weak
#print axioms ZHypercircle.cs
#print axioms ZHypercircle.lower
#print axioms ZHypercircle.upper
#print axioms ZHypercircle.polarise
#print axioms ZHypercircle.output_bracket
#print axioms ZHypercircle.lower_box
#print axioms ZHypercircle.upper_box
#print axioms ZHypercircle.perturb_identity
#print axioms ZHypercircle.perturb_split
#print axioms ZHypercircle.para
#print axioms ZHypercircle.bpol
#print axioms ZHypercircle.form_cs
#print axioms ZHypercircle.rest_bound
