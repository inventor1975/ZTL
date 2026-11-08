import ZNone
/-!
# ZRoot — a sign change of a polynomial GIVES a root, on a complete constructive field. Zero axioms.

`ZImplicit` proves that the kernel never misplaces a root, and leaves EXISTENCE (the intermediate value
theorem) a named premise. Here it is proved for polynomials with dyadic coefficients:

  `f(a) ≤ 0 ≤ f(b)` at dyadic `a ≤ b`  ⟹  `∃ x ∈ [a, b], f(x) = 0`

on any constructive ordered field that has NESTED DYADIC INTERVALS and is ARCHIMEDEAN (`Complete`) — VR's
operational continuum is one (`ZRootVR`), ℝ another. Not on every field: ℚ has `x² − 2` with no root.

The root is BUILT, not assumed: halving `[a, b]`, the sign of `f` at a dyadic midpoint is an exact dyadic
(`evalD`, no rounding), so each step is decided — no constructive trap. The nested intervals meet in `x`. That
`f(x) = 0` comes from a LIPSCHITZ bound with no derivative: `f(x) − f(y) = (x − y)·Q(x, y)` for an explicit
polynomial `Q = dd f` (a divided difference, `dd_ident`), and `Q` is bounded on `[a, b]²` by the kernel's own
interval reading. What the kernel checks is small: the two signs and that reading.
-/

namespace ZRoot
open VR.CSR ZNumBin ZField ZPoly ZIv ZNone

/-! ## Exact dyadic evaluation of a polynomial in one variable -/

def dpow (d : D) : Nat → D
  | 0 => ⟨⟨1, 0⟩, 0⟩
  | n + 1 => dmul d (dpow d n)

def evalD (d : D) : PE → D
  | .var _ => d
  | .cst c => c
  | .add p q => dadd (evalD d p) (evalD d q)
  | .sub p q => dadd (evalD d p) (dneg (evalD d q))
  | .mul p q => dmul (evalD d p) (evalD d q)
  | .pow p n => dpow (evalD d p) n

variable {α : Type} (S : CF α)

theorem dv_one : S.r (dv S.toOH (⟨⟨1, 0⟩, 0⟩ : D)) S.one := by
  show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) S.one; cr_ring S.toCR

theorem dv_dpow (d : D) : ∀ n, S.r (dv S.toOH (dpow d n)) (powS S.toOH (dv S.toOH d) n)
  | 0 => dv_one S
  | n + 1 => S.trans (dv_mul S.toOH _ _) (S.mul_congr (S.refl _) (dv_dpow d n))

/-- The exact dyadic value IS the value at the dyadic point. -/
theorem evalD_sound (d : D) : ∀ p : PE, S.r (dv S.toOH (evalD d p)) (eval S.toOH (fun _ => dv S.toOH d) p)
  | .var _ => S.refl _
  | .cst _ => S.refl _
  | .add p q => S.trans (dv_add S.toOH _ _) (S.add_congr (evalD_sound d p) (evalD_sound d q))
  | .sub p q => S.trans (dv_add S.toOH _ _) (S.add_congr (evalD_sound d p) (S.trans (dv_neg S.toOH _) (S.neg_congr (evalD_sound d q))))
  | .mul p q => S.trans (dv_mul S.toOH _ _) (S.mul_congr (evalD_sound d p) (evalD_sound d q))
  | .pow p n => S.trans (dv_dpow S _ n) (powS_congr S.toOH (evalD_sound d p) n)

/-! ## The divided difference: `f(x) − f(y) = (x − y)·Q(x, y)` -/

def at0 (p : PE) : PE := p.subst (fun _ => .var 0)
def at1 (p : PE) : PE := p.subst (fun _ => .var 1)
def c0 : PE := .cst ⟨⟨0, 0⟩, 0⟩
def c1 : PE := .cst ⟨⟨1, 0⟩, 0⟩

/-- `dd` of `pᵏ`, given `p` and `dd p`: `pᵏ⁺¹ = p · pᵏ`. -/
def ddPow (p dp : PE) : Nat → PE
  | 0 => c0
  | k + 1 => .add (.mul dp (at0 (.pow p k))) (.mul (at1 p) (ddPow p dp k))

/-- The divided difference, in `x = var 0`, `y = var 1`. -/
def dd : PE → PE
  | .var _ => c1
  | .cst _ => c0
  | .add p q => .add (dd p) (dd q)
  | .sub p q => .sub (dd p) (dd q)
  | .mul p q => .add (.mul (dd p) (at0 q)) (.mul (at1 p) (dd q))
  | .pow p k => ddPow p (dd p) k

section
variable (x y : α)

def e2 : Nat → α := fun i => cond (Nat.beq i 0) x y

theorem eval_at0 (p : PE) : S.r (eval S.toOH (e2 x y) (at0 p)) (eval S.toOH (fun _ => x) p) :=
  eval_subst S.toOH (e2 x y) _ p
theorem eval_at1 (p : PE) : S.r (eval S.toOH (e2 x y) (at1 p)) (eval S.toOH (fun _ => y) p) :=
  eval_subst S.toOH (e2 x y) _ p

theorem dv_c0 : S.r (eval S.toOH (e2 x y) c0) S.zero := by
  show S.r (S.mul (S.add S.zero (S.neg S.zero)) S.one) S.zero; cr_ring S.toCR
theorem dv_c1 : S.r (eval S.toOH (e2 x y) c1) S.one := dv_one S

theorem ddPow_ident (p dp : PE)
    (hp : S.r (S.add (eval S.toOH (fun _ => x) p) (S.neg (eval S.toOH (fun _ => y) p)))
      (S.mul (S.add x (S.neg y)) (eval S.toOH (e2 x y) dp))) :
    ∀ k, S.r (S.add (powS S.toOH (eval S.toOH (fun _ => x) p) k) (S.neg (powS S.toOH (eval S.toOH (fun _ => y) p) k)))
      (S.mul (S.add x (S.neg y)) (eval S.toOH (e2 x y) (ddPow p dp k)))
  | 0 => by
      have z := dv_c0 S x y
      show S.r (S.add S.one (S.neg S.one)) (S.mul (S.add x (S.neg y)) (eval S.toOH (e2 x y) c0))
      have h1 : S.r (S.add S.one (S.neg S.one)) S.zero := by cr_ring S.toCR
      have h2 : S.r (S.mul (S.add x (S.neg y)) S.zero) S.zero := by cr_ring S.toCR
      exact S.trans h1 (S.symm (S.trans (S.mul_congr (S.refl _) z) h2))
  | k + 1 => by
      have ih := ddPow_ident p dp hp k
      have a0 := eval_at0 S x y (.pow p k)
      have a1 := eval_at1 S x y p
      show S.r (S.add (S.mul (eval S.toOH (fun _ => x) p) (powS S.toOH (eval S.toOH (fun _ => x) p) k))
          (S.neg (S.mul (eval S.toOH (fun _ => y) p) (powS S.toOH (eval S.toOH (fun _ => y) p) k))))
        (S.mul (S.add x (S.neg y)) (S.add (S.mul (eval S.toOH (e2 x y) dp) (eval S.toOH (e2 x y) (at0 (.pow p k))))
          (S.mul (eval S.toOH (e2 x y) (at1 p)) (eval S.toOH (e2 x y) (ddPow p dp k)))))
      have a0' : S.r (eval S.toOH (e2 x y) (at0 (.pow p k))) (powS S.toOH (eval S.toOH (fun _ => x) p) k) := a0
      generalize eval S.toOH (fun _ => x) p = X at *
      generalize eval S.toOH (fun _ => y) p = Y at *
      generalize eval S.toOH (e2 x y) dp = DP at *
      generalize eval S.toOH (e2 x y) (ddPow p dp k) = DK at *
      generalize powS S.toOH X k = XK at *
      generalize powS S.toOH Y k = YK at *
      refine S.trans ?_ (S.symm (S.mul_congr (S.refl _) (S.add_congr (S.mul_congr (S.refl _) a0') (S.mul_congr a1 (S.refl _)))))
      -- X·XK − Y·YK = (X − Y)·XK + Y·(XK − YK), and both differences are (x − y)·…
      have t : S.r (S.add (S.mul X XK) (S.neg (S.mul Y YK)))
          (S.add (S.mul (S.add X (S.neg Y)) XK) (S.mul Y (S.add XK (S.neg YK)))) := by cr_ring S.toCR
      refine S.trans t (S.trans (S.add_congr (S.mul_congr hp (S.refl _)) (S.mul_congr (S.refl _) ih)) ?_)
      cr_ring S.toCR

/-- **THE DIVIDED DIFFERENCE**: `f(x) − f(y) = (x − y) · (dd f)(x, y)`, in every `OH`. -/
theorem dd_ident : ∀ f : PE, S.r (S.add (eval S.toOH (fun _ => x) f) (S.neg (eval S.toOH (fun _ => y) f)))
    (S.mul (S.add x (S.neg y)) (eval S.toOH (e2 x y) (dd f)))
  | .var _ => by
      have o := dv_c1 S x y
      show S.r (S.add x (S.neg y)) (S.mul (S.add x (S.neg y)) (eval S.toOH (e2 x y) c1))
      have h : S.r (S.mul (S.add x (S.neg y)) S.one) (S.add x (S.neg y)) := by cr_ring S.toCR
      exact S.symm (S.trans (S.mul_congr (S.refl _) o) h)
  | .cst c => by
      have z := dv_c0 S x y
      show S.r (S.add (dv S.toOH c) (S.neg (dv S.toOH c))) (S.mul (S.add x (S.neg y)) (eval S.toOH (e2 x y) c0))
      have h1 : S.r (S.add (dv S.toOH c) (S.neg (dv S.toOH c))) S.zero := by cr_ring S.toCR
      have h2 : S.r (S.mul (S.add x (S.neg y)) S.zero) S.zero := by cr_ring S.toCR
      exact S.trans h1 (S.symm (S.trans (S.mul_congr (S.refl _) z) h2))
  | .add p q => by
      have hp := dd_ident p; have hq := dd_ident q
      show S.r (S.add (S.add (eval S.toOH (fun _ => x) p) (eval S.toOH (fun _ => x) q))
          (S.neg (S.add (eval S.toOH (fun _ => y) p) (eval S.toOH (fun _ => y) q))))
        (S.mul (S.add x (S.neg y)) (S.add (eval S.toOH (e2 x y) (dd p)) (eval S.toOH (e2 x y) (dd q))))
      exact S.trans (by cr_ring S.toCR) (S.trans (S.add_congr hp hq) (by cr_ring S.toCR))
  | .sub p q => by
      have hp := dd_ident p; have hq := dd_ident q
      show S.r (S.add (S.add (eval S.toOH (fun _ => x) p) (S.neg (eval S.toOH (fun _ => x) q)))
          (S.neg (S.add (eval S.toOH (fun _ => y) p) (S.neg (eval S.toOH (fun _ => y) q)))))
        (S.mul (S.add x (S.neg y)) (S.add (eval S.toOH (e2 x y) (dd p)) (S.neg (eval S.toOH (e2 x y) (dd q)))))
      exact S.trans (by cr_ring S.toCR) (S.trans (S.add_congr hp (S.neg_congr hq)) (by cr_ring S.toCR))
  | .mul p q => by
      have hp := dd_ident p; have hq := dd_ident q
      have a0 := eval_at0 S x y q; have a1 := eval_at1 S x y p
      show S.r (S.add (S.mul (eval S.toOH (fun _ => x) p) (eval S.toOH (fun _ => x) q))
          (S.neg (S.mul (eval S.toOH (fun _ => y) p) (eval S.toOH (fun _ => y) q))))
        (S.mul (S.add x (S.neg y)) (S.add (S.mul (eval S.toOH (e2 x y) (dd p)) (eval S.toOH (e2 x y) (at0 q)))
          (S.mul (eval S.toOH (e2 x y) (at1 p)) (eval S.toOH (e2 x y) (dd q)))))
      generalize eval S.toOH (fun _ => x) p = PX at *
      generalize eval S.toOH (fun _ => y) p = PY at *
      generalize eval S.toOH (fun _ => x) q = QX at *
      generalize eval S.toOH (fun _ => y) q = QY at *
      generalize eval S.toOH (e2 x y) (dd p) = DP at *
      generalize eval S.toOH (e2 x y) (dd q) = DQ at *
      refine S.trans ?_ (S.symm (S.mul_congr (S.refl _) (S.add_congr (S.mul_congr (S.refl _) a0) (S.mul_congr a1 (S.refl _)))))
      have t : S.r (S.add (S.mul PX QX) (S.neg (S.mul PY QY)))
          (S.add (S.mul (S.add PX (S.neg PY)) QX) (S.mul PY (S.add QX (S.neg QY)))) := by cr_ring S.toCR
      refine S.trans t (S.trans (S.add_congr (S.mul_congr hp (S.refl _)) (S.mul_congr (S.refl _) hq)) ?_)
      cr_ring S.toCR
  | .pow p k => ddPow_ident S x y p (dd p) (dd_ident p) k
end


/-! ## Completeness: nested dyadic intervals, and Archimedes -/

/-- What a field needs for a sign change to give a root. VR's operational continuum has it (`ZRootVR`). -/
structure Complete (S : CF α) : Prop where
  nest : ∀ (lo hi : Nat → D) (W : D), (∀ k, S.le (dv S.toOH (lo k)) (dv S.toOH (lo (k + 1)))) →
    (∀ k, S.le (dv S.toOH (hi (k + 1))) (dv S.toOH (hi k))) → (∀ k, S.le (dv S.toOH (lo k)) (dv S.toOH (hi k))) →
    (∀ k, S.le (S.add (dv S.toOH (hi k)) (S.neg (dv S.toOH (lo k)))) (S.mul (dv S.toOH W) (hp S.toOH k))) →
    ∃ x, ∀ k, S.le (dv S.toOH (lo k)) x ∧ S.le x (dv S.toOH (hi k))
  arch : ∀ {y : α}, S.pos y → ∃ k, S.le (hp S.toOH k) y

/-! ## Halving -/

def dz : D := ⟨⟨0, 0⟩, 0⟩
def dhalf : D := ⟨⟨1, 0⟩, 1⟩
def mid (lo hi : D) : D := dmul (dadd lo hi) dhalf

/-- The bracket after `k` halvings: keep the half where the sign changes (`f(m) ≤ 0` → `[m, hi]`). -/
def bis (f : PE) (a b : D) : Nat → D × D
  | 0 => (a, b)
  | k + 1 =>
      (cond (dle (evalD (mid (bis f a b k).1 (bis f a b k).2) f) dz) (mid (bis f a b k).1 (bis f a b k).2) (bis f a b k).1,
       cond (dle (evalD (mid (bis f a b k).1 (bis f a b k).2) f) dz) (bis f a b k).2 (mid (bis f a b k).1 (bis f a b k).2))

theorem dv_dz : S.r (dv S.toOH dz) S.zero := by
  show S.r (S.mul (S.add S.zero (S.neg S.zero)) S.one) S.zero; cr_ring S.toCR

theorem dv_mid (lo hi : D) : S.r (dv S.toOH (mid lo hi)) (S.mul (S.add (dv S.toOH lo) (dv S.toOH hi)) S.half) := by
  have e1 := dv_mul S.toOH (dadd lo hi) dhalf
  have e2 := dv_add S.toOH lo hi
  have e3 : S.r (dv S.toOH dhalf) S.half := by
    show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) (S.mul S.half S.one)) S.half; cr_ring S.toCR
  exact S.trans e1 (S.mul_congr e2 e3)

/-- The value of `f` at a dyadic point, as an element. -/
def fv (f : PE) (d : D) : α := eval S.toOH (fun _ => dv S.toOH d) f

structure Inv (f : PE) (a b : D) (lo hi : D) (k : Nat) : Prop where
  ord : S.le (dv S.toOH lo) (dv S.toOH hi)
  flo : S.le (fv S f lo) S.zero
  fhi : S.le S.zero (fv S f hi)
  wid : S.r (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (hp S.toOH k))

theorem bis_step (f : PE) (a b : D) (k : Nat) (lo hi : D) (I : Inv S f a b lo hi k) :
    let m := mid lo hi
    Inv S f a b (cond (dle (evalD m f) dz) m lo) (cond (dle (evalD m f) dz) hi m) (k + 1) ∧
    S.le (dv S.toOH lo) (dv S.toOH (cond (dle (evalD m f) dz) m lo)) ∧
    S.le (dv S.toOH (cond (dle (evalD m f) dz) hi m)) (dv S.toOH hi) := by
  intro m
  have em := dv_mid S lo hi
  have h0 := half_nonneg S.toOH
  have hh : S.r (S.add S.half S.half) S.one := S.half_spec
  have d0 : S.le S.zero (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) := OCR.sub_nonneg_of_le S.toOCR I.ord
  have pm := S.mul_nonneg d0 h0
  -- m − lo = hi − m = (hi − lo)/2
  have w1 : S.r (S.add (dv S.toOH m) (S.neg (dv S.toOH lo))) (S.mul (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) S.half) := by
    have t : S.r (dv S.toOH lo) (S.mul (dv S.toOH lo) (S.add S.half S.half)) :=
      S.trans (by cr_ring S.toCR) (S.mul_congr (S.refl _) (S.symm hh))
    refine S.trans (S.add_congr em (S.neg_congr t)) ?_
    cr_ring S.toCR
  have w2 : S.r (S.add (dv S.toOH hi) (S.neg (dv S.toOH m))) (S.mul (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) S.half) := by
    have t : S.r (dv S.toOH hi) (S.mul (dv S.toOH hi) (S.add S.half S.half)) :=
      S.trans (by cr_ring S.toCR) (S.mul_congr (S.refl _) (S.symm hh))
    refine S.trans (S.add_congr t (S.neg_congr em)) ?_
    cr_ring S.toCR
  have wk : S.r (S.mul (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) S.half)
      (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (hp S.toOH (k + 1))) := by
    show S.r _ (S.mul _ (S.mul S.half (hp S.toOH k)))
    refine S.trans (S.mul_congr I.wid (S.refl _)) ?_
    cr_ring S.toCR
  have lm : S.le (dv S.toOH lo) (dv S.toOH m) := by
    have := S.le_respects (S.refl _) (S.symm w1) pm; cr_linarith S.toOCR [this]
  have mh : S.le (dv S.toOH m) (dv S.toOH hi) := by
    have := S.le_respects (S.refl _) (S.symm w2) pm; cr_linarith S.toOCR [this]
  have fm := evalD_sound S m f
  cases hs : dle (evalD m f) dz with
  | true =>
      have fle : S.le (fv S f m) S.zero := by
        have := dle_sound S.toOH hs
        exact S.le_respects fm (dv_dz S) this
      exact ⟨⟨mh, fle, I.fhi, S.trans w2 wk⟩, lm, S.le_refl _⟩
  | false =>
      have fge : S.le S.zero (fv S f m) := by
        have := dle_sound S.toOH (dle_swap hs)
        exact S.le_respects (dv_dz S) fm this
      exact ⟨⟨lm, I.flo, fge, S.trans w1 wk⟩, S.le_refl _, mh⟩

theorem bis_inv (f : PE) (a b : D) (hab : S.le (dv S.toOH a) (dv S.toOH b)) (hfa : S.le (fv S f a) S.zero)
    (hfb : S.le S.zero (fv S f b)) : ∀ k, Inv S f a b (bis f a b k).1 (bis f a b k).2 k
  | 0 => ⟨hab, hfa, hfb, by
      show S.r (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) S.one)
      cr_ring S.toCR⟩
  | k + 1 => (bis_step S f a b k _ _ (bis_inv f a b hab hfa hfb k)).1

theorem bis_mono (f : PE) (a b : D) (hab : S.le (dv S.toOH a) (dv S.toOH b)) (hfa : S.le (fv S f a) S.zero)
    (hfb : S.le S.zero (fv S f b)) (k : Nat) :
    S.le (dv S.toOH (bis f a b k).1) (dv S.toOH (bis f a b (k + 1)).1) ∧
    S.le (dv S.toOH (bis f a b (k + 1)).2) (dv S.toOH (bis f a b k).2) :=
  (bis_step S f a b k _ _ (bis_inv S f a b hab hfa hfb k)).2


/-! ## The root -/

/-- The square `[a, b]²` for the divided difference. -/
def B2 (a b : D) : Box := fun i => cond (Nat.beq i 0 || Nat.beq i 1) (some (a, b)) none

theorem inbox2 {a b : D} {u v : α} (hu : S.le (dv S.toOH a) u ∧ S.le u (dv S.toOH b))
    (hv : S.le (dv S.toOH a) v ∧ S.le v (dv S.toOH b)) : InBox S (B2 a b) (e2 u v) := by
  intro i I hI
  cases h0 : Nat.beq i 0 with
  | true =>
      have : B2 a b i = some (a, b) := by unfold B2; rw [h0]; rfl
      rw [this] at hI; cases hI
      show S.le _ (cond (Nat.beq i 0) u v) ∧ S.le (cond (Nat.beq i 0) u v) _
      rw [h0]; exact hu
  | false =>
      cases h1 : Nat.beq i 1 with
      | true =>
          have : B2 a b i = some (a, b) := by unfold B2; rw [h0, h1]; rfl
          rw [this] at hI; cases hI
          show S.le _ (cond (Nat.beq i 0) u v) ∧ S.le (cond (Nat.beq i 0) u v) _
          rw [h0]; exact hv
      | false =>
          have : B2 a b i = none := by unfold B2; rw [h0, h1]; rfl
          rw [this] at hI; cases hI

theorem mul_le_l {d q M : α} (h0 : S.le S.zero d) (hq : S.le q M) : S.le (S.mul d q) (S.mul d M) := by
  have h := S.mul_nonneg h0 (OCR.sub_nonneg_of_le S.toOCR hq)
  exact OCR.le_of_sub_nonneg S.toOCR (S.le_respects (S.refl _) (by cr_ring S.toCR) h)

theorem dv_nat (n : Nat) : S.r (dv S.toOH (⟨⟨n, 0⟩, 0⟩ : D)) (nI S.toOH n) := by
  show S.r (S.mul (S.add (nI S.toOH n) (S.neg (nI S.toOH 0))) S.one) (nI S.toOH n)
  have z := nI_zero S.toOH
  refine S.trans (S.mul_congr (S.add_congr (S.refl _) (S.neg_congr z)) (S.refl _)) ?_
  cr_ring S.toCR

/-- One side of the squeeze: `f(u) − f(v) ≤ 2^(−(j+1))` for `v ≤ u` in the `k`-th bracket, `k = j+1+C+B`. -/
theorem squeeze {a b : D} {f : PE} {cB cC j : Nat} {K : Iv} (hK : ivE (B2 a b) (dd f) = some K)
    (hK2 : dle K.2 ⟨⟨2 ^ cC, 0⟩, 0⟩ = true) (hW : dle (dadd b (dneg a)) ⟨⟨2 ^ cB, 0⟩, 0⟩ = true)
    {u v lo hi : α} (hu : S.le (dv S.toOH a) u ∧ S.le u (dv S.toOH b)) (hv : S.le (dv S.toOH a) v ∧ S.le v (dv S.toOH b))
    (hvu : S.le v u) (hlo : S.le lo v) (hhi : S.le u hi)
    (hw : S.r (S.add hi (S.neg lo)) (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (hp S.toOH ((j + 1) + (cC + cB))))) :
    S.le (S.add (eval S.toOH (fun _ => u) f) (S.neg (eval S.toOH (fun _ => v) f))) (hp S.toOH (j + 1)) := by
  have Q := (ivE_sound S (inbox2 S hu hv) (dd f) K hK).2
  have QM := S.le_trans Q (S.le_respects (S.refl _) (dv_nat S _) (dle_sound S.toOH hK2))
  have id := dd_ident S u v f
  have d0 := OCR.sub_nonneg_of_le S.toOCR hvu
  have m1 := mul_le_l S d0 QM
  -- (u − v)·M ≤ (hi − lo)·M ≤ (b − a)·hp k·M ≤ 2^B·hp k·M
  have M0 := nI_nonneg S.toOH (2 ^ cC)
  have dlh : S.le (S.add u (S.neg v)) (S.add hi (S.neg lo)) := by cr_linarith S.toOCR [hlo, hhi]
  have m2 := le_mul_right S.toOH dlh M0
  have Wb := S.le_respects (S.trans (dv_add S.toOH _ _) (S.add_congr (S.refl _) (dv_neg S.toOH _))) (dv_nat S _) (dle_sound S.toOH hW)
  have hk0 := hp_nonneg S.toOH ((j + 1) + (cC + cB))
  have m3 := le_mul_right S.toOH (le_mul_right S.toOH Wb hk0) M0
  have e1 := S.mul_congr hw (S.refl (nI S.toOH (2 ^ cC)))
  -- 2^B · hp(j+1+C+B) · 2^C = hp(j+1)
  have hk := S.trans (hp_add S.toOH (j + 1) (cC + cB)) (S.mul_congr (S.refl _) (hp_add S.toOH cC cB))
  have tC := two_hp S.toOH cC
  have tB := two_hp S.toOH cB
  have fin : S.r (S.mul (S.mul (nI S.toOH (2 ^ cB)) (hp S.toOH ((j + 1) + (cC + cB)))) (nI S.toOH (2 ^ cC))) (hp S.toOH (j + 1)) := by
    refine S.trans (S.mul_congr (S.mul_congr (S.refl _) hk) (S.refl _)) ?_
    have r1 : S.r (S.mul (S.mul (nI S.toOH (2 ^ cB)) (S.mul (hp S.toOH (j + 1)) (S.mul (hp S.toOH cC) (hp S.toOH cB)))) (nI S.toOH (2 ^ cC)))
        (S.mul (hp S.toOH (j + 1)) (S.mul (S.mul (nI S.toOH (2 ^ cC)) (hp S.toOH cC)) (S.mul (nI S.toOH (2 ^ cB)) (hp S.toOH cB)))) := by
      cr_ring S.toCR
    refine S.trans r1 (S.trans (S.mul_congr (S.refl _) (S.mul_congr tC tB)) ?_)
    cr_ring S.toCR
  have c1 := S.le_trans m1 (S.le_trans m2 (S.le_respects (S.refl _) e1 (S.le_refl _)))
  have c2 := S.le_trans c1 (S.le_respects (S.refl _) fin m3)
  exact S.le_respects (S.symm id) (S.refl _) c2

theorem hp_succ_half (j : Nat) : S.r (S.add (hp S.toOH (j + 1)) (hp S.toOH (j + 1))) (hp S.toOH j) := by
  show S.r (S.add (S.mul S.half (hp S.toOH j)) (S.mul S.half (hp S.toOH j))) (hp S.toOH j)
  have hh : S.r (S.add S.half S.half) S.one := S.half_spec
  exact S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add S.half S.half) (hp S.toOH j)))
    (S.trans (S.mul_congr hh (S.refl _)) (by cr_ring S.toCR))

/-- **A SIGN CHANGE GIVES A ROOT.** `f` a polynomial in one variable with dyadic coefficients, `a ≤ b` dyadic,
`f(a) ≤ 0 ≤ f(b)` (exact dyadic values), `b − a ≤ 2^B`, and the interval reading of the divided difference on
`[a, b]²` below `2^C`: on a complete field there is `x ∈ [a, b]` with `f(x) = 0`. -/
theorem root_exists (C : Complete S) (f : PE) (a b : D) (cB cC : Nat) (K : Iv)
    (hab : dle a b = true) (hfa : dle (evalD a f) dz = true) (hfb : dle dz (evalD b f) = true)
    (hW : dle (dadd b (dneg a)) ⟨⟨2 ^ cB, 0⟩, 0⟩ = true)
    (hK : ivE (B2 a b) (dd f) = some K) (hK2 : dle K.2 ⟨⟨2 ^ cC, 0⟩, 0⟩ = true) :
    ∃ x, S.le (dv S.toOH a) x ∧ S.le x (dv S.toOH b) ∧ S.r (eval S.toOH (fun _ => x) f) S.zero := by
  have hab' := dle_sound S.toOH hab
  have hfa' : S.le (fv S f a) S.zero := S.le_respects (evalD_sound S a f) (dv_dz S) (dle_sound S.toOH hfa)
  have hfb' : S.le S.zero (fv S f b) := S.le_respects (dv_dz S) (evalD_sound S b f) (dle_sound S.toOH hfb)
  have inv := bis_inv S f a b hab' hfa' hfb'
  have mono := bis_mono S f a b hab' hfa' hfb'
  have We : S.r (dv S.toOH (dadd b (dneg a))) (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) :=
    S.trans (dv_add S.toOH _ _) (S.add_congr (S.refl _) (dv_neg S.toOH _))
  obtain ⟨x, hx⟩ := C.nest (fun k => (bis f a b k).1) (fun k => (bis f a b k).2) (dadd b (dneg a))
    (fun k => (mono k).1) (fun k => (mono k).2) (fun k => (inv k).ord)
    (fun k => S.le_respects (S.refl _) (S.symm (S.mul_congr We (S.refl _))) (S.le_respects (S.refl _) (inv k).wid (S.le_refl _)))
  have xa : S.le (dv S.toOH a) x := (hx 0).1
  have xb : S.le x (dv S.toOH b) := (hx 0).2
  refine ⟨x, xa, xb, S.ap_tight ?_⟩
  intro hap
  have br : ∀ k, (S.le (dv S.toOH a) (dv S.toOH (bis f a b k).1) ∧ S.le (dv S.toOH (bis f a b k).1) (dv S.toOH b)) ∧
      (S.le (dv S.toOH a) (dv S.toOH (bis f a b k).2) ∧ S.le (dv S.toOH (bis f a b k).2) (dv S.toOH b)) := by
    intro k
    have l1 := (hx k).1; have l2 := (hx k).2; have l3 := (hx 0).1; have l4 := (hx 0).2
    have m1 := (hx k).1
    have o := (inv k).ord
    -- lo_k ≥ a and hi_k ≤ b by monotonicity from step 0
    have ga : ∀ n, S.le (dv S.toOH a) (dv S.toOH (bis f a b n).1) := by
      intro n; induction n with
      | zero => exact S.le_refl _
      | succ n ih => exact S.le_trans ih (mono n).1
    have gb : ∀ n, S.le (dv S.toOH (bis f a b n).2) (dv S.toOH b) := by
      intro n; induction n with
      | zero => exact S.le_refl _
      | succ n ih => exact S.le_trans (mono n).2 ih
    exact ⟨⟨ga k, S.le_trans o (gb k)⟩, ⟨S.le_trans (ga k) o, gb k⟩⟩
  cases hap with
  | inl hp' =>
      obtain ⟨j, hj⟩ := C.arch hp'
      let k := (j + 1) + (cC + cB)
      have sq := squeeze S hK hK2 hW ⟨xa, xb⟩ (br k).1 (hx k).1 (S.le_refl _) (hx k).2 (inv k).wid
      have fl := (inv k).flo
      have hs := hp_succ_half S j
      have pp := pos_hp S (j + 1)
      exact S.pos_not_le pp (by
        show S.le (hp S.toOH (j + 1)) S.zero
        have : S.le (fv S f (bis f a b k).1) S.zero := fl
        unfold fv at this
        cr_linarith S.toOCR [sq, this, hj, hs])
  | inr hn =>
      obtain ⟨j, hj⟩ := C.arch hn
      let k := (j + 1) + (cC + cB)
      have sq := squeeze S hK hK2 hW (br k).2 ⟨xa, xb⟩ (hx k).2 (hx k).1 (S.le_refl _) (inv k).wid
      have fh := (inv k).fhi
      have hs := hp_succ_half S j
      have pp := pos_hp S (j + 1)
      exact S.pos_not_le pp (by
        show S.le (hp S.toOH (j + 1)) S.zero
        have : S.le S.zero (fv S f (bis f a b k).2) := fh
        unfold fv at this
        cr_linarith S.toOCR [sq, this, hj, hs])

end ZRoot

#print axioms ZRoot.root_exists

#print axioms ZRoot.bis_inv

#print axioms ZRoot.evalD_sound
#print axioms ZRoot.dd_ident
