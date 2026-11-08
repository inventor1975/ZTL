import ZRootP
import ZRootVR
/-!
# ZRootPVR — the root of `g(x, p) = 0` at EVERY real parameter point, on VR's continuum. Zero axioms.

`ZRootVR` gives a root when the coefficients are dyadic: the sign at a midpoint is decided. At a REAL parameter
point it is not — and VR's reals carry their Cauchy moduli as propositions, so no program can pick the index
that a given precision needs. The root is built anyway, from what IS computable: the `n`-th approximants of
the parameters. Its `n`-th term is `n` halvings of the RATIONAL polynomial `t ↦ g(t, p⁽ⁿ⁾)` (`p⁽ⁿ⁾ᵢ = (pᵢ).seq n`),
every sign a rational comparison. That these terms converge, and to a root, is proved from bounds the kernel
reads off `g` by interval arithmetic: the slope in `x` at least `c > 0`, the slope in `x` at most `Lx`, and the
divided difference in each parameter within `[−Lᵢ, Lᵢ]` (`ZRootP`). The moduli are used in the proof only.

What is proved, all on the empty axiom list:
  * `root` — for a certificate `RC` (kernel-checked signs at `a`, `b`; slope readings; parameter Lipschitz readings)
    and a parameter point strictly inside the box (`InnerIn`), the left ends of the brackets are Cauchy
    (`t_cauchy`): a VR real in `[a, b]` (`root_in`);
  * `root_is_root` — `g(root, p) = 0`; `root_unique` — the only root in `[a, b]`;
  * `sqrt_exists` — every VR real `p ∈ [1¼, 3¾]` has a square root in `[1, 2]`; and a refused bracket.
This is the existence premise `ZImplicit` names ("a sign change gives a root"), discharged for polynomial laws
on VR's continuum: the root function `U p` it takes as input exists, and is unique.
-/

namespace ZRootPVR
open VR VR.Numbers VR.CSR ZNumBin ZField ZPoly ZIv ZRealCF ZExp ZRealExp ZRoot ZRootP

/-! ## The rational value is the `n`-th term -/

def qpowN (x : QExpr) : Nat → QExpr
  | 0 => qone
  | k + 1 => qmul x (qpowN x k)

def evalQ (q : Nat → QExpr) : PE → QExpr
  | .var i => q i
  | .cst c => qD c
  | .add p r => qadd (evalQ q p) (evalQ q r)
  | .sub p r => qadd (evalQ q p) (qneg (evalQ q r))
  | .mul p r => qmul (evalQ q p) (evalQ q r)
  | .pow p k => qpowN (evalQ q p) k

theorem pow_seq (x : RExpr) (n : Nat) : ∀ k, qEq ((powS rOH x k).seq n) (qpowN (x.seq n) k)
  | 0 => qEq_refl _
  | k + 1 => qmul_respects (qEq_refl _) (pow_seq x n k)

/-- **`(f(e)).seq n = f(e.seq n)`**: VR's operations are termwise. -/
theorem eval_seq (e : Nat → RExpr) (n : Nat) : ∀ f : PE, qEq ((eval rOH e f).seq n) (evalQ (fun i => (e i).seq n) f)
  | .var _ => qEq_refl _
  | .cst c => dv_seq c n
  | .add p r => qadd_respects (eval_seq e n p) (eval_seq e n r)
  | .sub p r => qadd_respects (eval_seq e n p) (qneg_respects (eval_seq e n r))
  | .mul p r => qmul_respects (eval_seq e n p) (eval_seq e n r)
  | .pow p k => qEq_trans (pow_seq _ n k) (qpowN_respects (eval_seq e n p) k)
where
  qpowN_respects {x y : QExpr} (h : qEq x y) : ∀ k, qEq (qpowN x k) (qpowN y k)
    | 0 => qEq_refl _
    | k + 1 => qmul_respects h (qpowN_respects h k)

/-- At a point of constants, the VR value IS the constant of the rational value. -/
theorem eval_const (q : Nat → QExpr) (f : PE) : rEq (eval rOH (fun i => rofQ (q i)) f) (rofQ (evalQ q f)) :=
  rEq_of_seq (fun n => eval_seq _ n f)

/-! ## Rational halving -/

def qleB (x y : QExpr) : Bool :=
  match qle.decidable x y with
  | .isTrue _ => true
  | .isFalse _ => false

theorem qleB_true {x y : QExpr} (h : qleB x y = true) : qle x y := by
  unfold qleB at h
  cases hd : qle.decidable x y with
  | isTrue p => exact p
  | isFalse _ => rw [hd] at h; cases h

theorem qleB_false {x y : QExpr} (h : qleB x y = false) : qle y x := by
  unfold qleB at h
  cases hd : qle.decidable x y with
  | isTrue _ => rw [hd] at h; cases h
  | isFalse np =>
      cases qle_total x y with
      | inl l => exact absurd l np
      | inr r => exact r

/-- `k` halvings of `[a, b]` at DYADIC midpoints, the sign read on the rational `g`: keep `[m, hi]` when
`g(m) ≤ 0`, else `[lo, m]`. -/
def bisD (g : QExpr → QExpr) (a b : D) : Nat → D × D
  | 0 => (a, b)
  | k + 1 =>
      (cond (qleB (g (qD (mid (bisD g a b k).1 (bisD g a b k).2))) qzero) (mid (bisD g a b k).1 (bisD g a b k).2) (bisD g a b k).1,
       cond (qleB (g (qD (mid (bisD g a b k).1 (bisD g a b k).2))) qzero) (bisD g a b k).2 (mid (bisD g a b k).1 (bisD g a b k).2))

section
variable {α : Type} (S : CF α)

/-- One halving keeps the order, halves the width, and nests — whichever half is kept. -/
theorem half_step (lo hi a b : D) (k : Nat) (cb : Bool) (ord : S.le (dv S.toOH lo) (dv S.toOH hi))
    (wid : S.r (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (hp S.toOH k))) :
    S.le (dv S.toOH (cond cb (mid lo hi) lo)) (dv S.toOH (cond cb hi (mid lo hi))) ∧
    S.r (S.add (dv S.toOH (cond cb hi (mid lo hi))) (S.neg (dv S.toOH (cond cb (mid lo hi) lo))))
      (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (hp S.toOH (k + 1))) ∧
    S.le (dv S.toOH lo) (dv S.toOH (cond cb (mid lo hi) lo)) ∧ S.le (dv S.toOH (cond cb hi (mid lo hi))) (dv S.toOH hi) := by
  have em := dv_mid S lo hi
  have h0 := half_nonneg S.toOH
  have hh : S.r (S.add S.half S.half) S.one := S.half_spec
  have d0 : S.le S.zero (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) := OCR.sub_nonneg_of_le S.toOCR ord
  have pm := S.mul_nonneg d0 h0
  have w1 : S.r (S.add (dv S.toOH (mid lo hi)) (S.neg (dv S.toOH lo))) (S.mul (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) S.half) := by
    have t : S.r (dv S.toOH lo) (S.mul (dv S.toOH lo) (S.add S.half S.half)) :=
      S.trans (by cr_ring S.toCR) (S.mul_congr (S.refl _) (S.symm hh))
    refine S.trans (S.add_congr em (S.neg_congr t)) ?_
    cr_ring S.toCR
  have w2 : S.r (S.add (dv S.toOH hi) (S.neg (dv S.toOH (mid lo hi)))) (S.mul (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) S.half) := by
    have t : S.r (dv S.toOH hi) (S.mul (dv S.toOH hi) (S.add S.half S.half)) :=
      S.trans (by cr_ring S.toCR) (S.mul_congr (S.refl _) (S.symm hh))
    refine S.trans (S.add_congr t (S.neg_congr em)) ?_
    cr_ring S.toCR
  have wk : S.r (S.mul (S.add (dv S.toOH hi) (S.neg (dv S.toOH lo))) S.half)
      (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (hp S.toOH (k + 1))) := by
    show S.r _ (S.mul _ (S.mul S.half (hp S.toOH k)))
    refine S.trans (S.mul_congr wid (S.refl _)) ?_
    cr_ring S.toCR
  have lm : S.le (dv S.toOH lo) (dv S.toOH (mid lo hi)) := by
    have := S.le_respects (S.refl _) (S.symm w1) pm; cr_linarith S.toOCR [this]
  have mh : S.le (dv S.toOH (mid lo hi)) (dv S.toOH hi) := by
    have := S.le_respects (S.refl _) (S.symm w2) pm; cr_linarith S.toOCR [this]
  cases cb with
  | true => exact ⟨mh, S.trans w2 wk, lm, S.le_refl _⟩
  | false => exact ⟨lm, S.trans w1 wk, S.le_refl _, mh⟩

theorem bisD_ord (g : QExpr → QExpr) (a b : D) (hab : S.le (dv S.toOH a) (dv S.toOH b)) : ∀ k,
    S.le (dv S.toOH (bisD g a b k).1) (dv S.toOH (bisD g a b k).2) ∧
    S.r (S.add (dv S.toOH (bisD g a b k).2) (S.neg (dv S.toOH (bisD g a b k).1)))
      (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (hp S.toOH k))
  | 0 => ⟨hab, by
      show S.r (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) (S.mul (S.add (dv S.toOH b) (S.neg (dv S.toOH a))) S.one)
      cr_ring S.toCR⟩
  | k + 1 => by
      obtain ⟨o, w⟩ := bisD_ord g a b hab k
      obtain ⟨o', w', _, _⟩ := half_step S _ _ a b k _ o w
      exact ⟨o', w'⟩

theorem bisD_nest (g : QExpr → QExpr) (a b : D) (hab : S.le (dv S.toOH a) (dv S.toOH b)) (k : Nat) :
    S.le (dv S.toOH (bisD g a b k).1) (dv S.toOH (bisD g a b (k + 1)).1) ∧
    S.le (dv S.toOH (bisD g a b (k + 1)).2) (dv S.toOH (bisD g a b k).2) := by
  obtain ⟨o, w⟩ := bisD_ord S g a b hab k
  obtain ⟨_, _, n1, n2⟩ := half_step S _ _ a b k _ o w
  exact ⟨n1, n2⟩

theorem bisD_in (g : QExpr → QExpr) (a b : D) (hab : S.le (dv S.toOH a) (dv S.toOH b)) : ∀ k,
    S.le (dv S.toOH a) (dv S.toOH (bisD g a b k).1) ∧ S.le (dv S.toOH (bisD g a b k).2) (dv S.toOH b)
  | 0 => ⟨S.le_refl _, S.le_refl _⟩
  | k + 1 => by
      obtain ⟨i1, i2⟩ := bisD_in g a b hab k
      obtain ⟨n1, n2⟩ := bisD_nest S g a b hab k
      exact ⟨S.le_trans i1 n1, S.le_trans n2 i2⟩
end

/-- The signs: kept by every halving, once they hold at the ends. -/
theorem bisD_sign (g : QExpr → QExpr) (a b : D) (ha : qle (g (qD a)) qzero) (hb : qle qzero (g (qD b))) : ∀ k,
    qle (g (qD (bisD g a b k).1)) qzero ∧ qle qzero (g (qD (bisD g a b k).2))
  | 0 => ⟨ha, hb⟩
  | k + 1 => by
      obtain ⟨s1, s2⟩ := bisD_sign g a b ha hb k
      show qle (g (qD (cond (qleB (g (qD (mid (bisD g a b k).1 (bisD g a b k).2))) qzero) _ _))) qzero ∧
        qle qzero (g (qD (cond (qleB (g (qD (mid (bisD g a b k).1 (bisD g a b k).2))) qzero) _ _)))
      cases hc : qleB (g (qD (mid (bisD g a b k).1 (bisD g a b k).2))) qzero with
      | true => exact ⟨qleB_true hc, s2⟩
      | false => exact ⟨s1, qleB_false hc⟩


/-! ## The certificate's data: `[a, b]`, and per parameter its index, its interval, its Lipschitz constant -/

abbrev PS := List (Nat × Iv × D)

def isP (j : Nat) : PS → Bool
  | [] => false
  | c :: cs => Nat.beq j c.1 || isP j cs

def lookI (j : Nat) : PS → Option Iv
  | [] => none
  | c :: cs => cond (Nat.beq j c.1) (some c.2.1) (lookI j cs)

def csOf : PS → List (Nat × D)
  | [] => []
  | c :: cs => (c.1, c.2.2) :: csOf cs

/-- The reading box: `x ∈ [a, b]` at variable `0`, each parameter on its interval, nothing else. -/
def BoxOf (a b : D) (ps : PS) : Box := fun j => cond (Nat.beq j 0) (some (a, b)) (lookI j ps)

theorem notIn_csOf {j : Nat} : ∀ {ps : PS}, ZRootP.notIn j (csOf ps) = true → isP j ps = false
  | [], _ => rfl
  | c :: cs, h => by
      have h' : (!(Nat.beq j c.1) && ZRootP.notIn j (csOf cs)) = true := h
      obtain ⟨h1, h2⟩ := ZNumBin.and_true_split h'
      show (Nat.beq j c.1 || isP j cs) = false
      cases hb : Nat.beq j c.1 with
      | true => rw [hb] at h1; cases h1
      | false => exact notIn_csOf h2

theorem lookI_none {j : Nat} : ∀ {ps : PS}, isP j ps = false → lookI j ps = none
  | [], _ => rfl
  | c :: cs, h => by
      have h' : (Nat.beq j c.1 || isP j cs) = false := h
      obtain ⟨h1, h2⟩ := ZRootP.or_false_split h'
      show cond (Nat.beq j c.1) _ (lookI j cs) = none
      rw [h1]; exact lookI_none h2

/-- The parameter point `q` with `x` at `dv a` (any point of `[a, b]` would do), zero off the parameters. -/
def envOf (a : D) (ps : PS) (q : Nat → RExpr) : Nat → RExpr :=
  fun i => cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (q i) rzero)

/-- Every parameter of `q` on its interval. -/
def ParIn (q : Nat → RExpr) : PS → Prop
  | [] => True
  | c :: cs => (rle (dv rOH c.2.1.1) (q c.1) ∧ rle (q c.1) (dv rOH c.2.1.2)) ∧ ParIn q cs

theorem lookI_mem {q : Nat → RExpr} {j : Nat} {I : Iv} : ∀ {ps : PS}, ParIn q ps → lookI j ps = some I →
    rle (dv rOH I.1) (q j) ∧ rle (q j) (dv rOH I.2)
  | [], _, h => by cases h
  | c :: cs, ⟨hc, hcs⟩, h => by
      have h' : cond (Nat.beq j c.1) (some c.2.1) (lookI j cs) = some I := h
      cases hb : Nat.beq j c.1 with
      | true =>
          rw [hb] at h'; cases h'
          have := Nat.eq_of_beq_eq_true hb; subst this; exact hc
      | false => rw [hb] at h'; exact lookI_mem hcs h'

theorem isP_of_lookI {j : Nat} {I : Iv} : ∀ {ps : PS}, lookI j ps = some I → isP j ps = true
  | [], h => by cases h
  | c :: cs, h => by
      have h' : cond (Nat.beq j c.1) (some c.2.1) (lookI j cs) = some I := h
      show (Nat.beq j c.1 || isP j cs) = true
      cases hb : Nat.beq j c.1 with
      | true => rfl
      | false => rw [hb] at h'; show (false || isP j cs) = true; exact isP_of_lookI h'

/-- **The point in the reading box**: parameters on their intervals, `x` anywhere in `[a, b]`. -/
theorem inbox_env {a b : D} {ps : PS} {q : Nat → RExpr} (hq : ParIn q ps) {s : RExpr}
    (hs : rle (dv rOH a) s ∧ rle s (dv rOH b)) : InBox rCF (BoxOf a b ps) (ZRootP.setv (envOf a ps q) 0 s) := by
  intro j J hJ
  show rle (dv rOH J.1) (cond (Nat.beq j 0) s (envOf a ps q j)) ∧ rle (cond (Nat.beq j 0) s (envOf a ps q j)) (dv rOH J.2)
  cases h0 : Nat.beq j 0 with
  | true =>
      have : BoxOf a b ps j = some (a, b) := by unfold BoxOf; rw [h0]; rfl
      rw [this] at hJ; cases hJ; exact hs
  | false =>
      have hB : BoxOf a b ps j = lookI j ps := by unfold BoxOf; rw [h0]; rfl
      rw [hB] at hJ
      show rle _ (cond (Nat.beq j 0) (dv rOH a) (cond (isP j ps) (q j) rzero)) ∧ rle (cond (Nat.beq j 0) (dv rOH a) (cond (isP j ps) (q j) rzero)) _
      rw [h0, isP_of_lookI hJ]
      exact lookI_mem hq hJ

/-! ## A VR real is near its own terms -/

theorem rle_const {x : RExpr} {q : QExpr} {k N : Nat} (h : ∀ m, N ≤ m → qle (qsub (x.seq m) q) (qeps k)) :
    rle (radd x (rneg (rofQ q))) (hp rOH k) :=
  rle_of_eventually N (fun m hm => by
    have := h m hm; have e := hp_seq k m
    change qle (qadd (x.seq m) (qneg q)) ((hp rOH k).seq m)
    unfold qsub at this; rat_linarith)

/-- `|z − z.seq n| ≤ 2⁻ʲ` from some `N` on — the modulus is used, inside the proof. -/
theorem approx_close (z : RExpr) (j : Nat) : ∃ N, ∀ n, N ≤ n →
    ZKron.Bd rCF.toOH (radd z (rneg (rofQ (z.seq n)))) (hp rOH j) := by
  obtain ⟨N, hN⟩ := z.cauchy j
  refine ⟨N, fun n hn => ⟨?_, rle_const (fun m hm => (hN m n hm hn).1)⟩⟩
  -- the lower side: −2⁻ʲ ≤ z − z_n
  refine rle_of_eventually N (fun m hm => ?_)
  have h2 := (hN m n hm hn).2
  have e := hp_seq j m
  change qle (qneg ((hp rOH j).seq m)) (qadd (z.seq m) (qneg (z.seq n)))
  unfold qsub at h2; rat_linarith

/-- One index past which a property of every parameter holds. -/
theorem common_N {P : Nat → Nat → Prop} : ∀ (ps : PS), (∀ c, List.Mem c ps → ∃ N, ∀ n, N ≤ n → P c.1 n) →
    ∃ N, ∀ n, N ≤ n → ∀ c, List.Mem c ps → P c.1 n
  | [], _ => ⟨0, fun _ _ c h => by cases h⟩
  | c :: cs, h => by
      obtain ⟨N1, h1⟩ := h c (List.Mem.head _)
      obtain ⟨N2, h2⟩ := common_N cs (fun d hd => h d (List.Mem.tail _ hd))
      refine ⟨N1 + N2, fun n hn d hd => ?_⟩
      cases hd with
      | head => exact h1 n (Nat.le_trans (Nat.le_add_right _ _) hn)
      | tail _ hd' => exact h2 n (Nat.le_trans (Nat.le_add_left _ _) hn) d hd'


/-! ## `G q x = g(x, q)`, and what the readings say about it -/

theorem mem_isP {c : Nat × Iv × D} : ∀ {ps : PS}, List.Mem c ps → isP c.1 ps = true
  | _ :: _, .head _ => by show (Nat.beq c.1 c.1 || _) = true; rw [ZKron.beq_self]; rfl
  | d :: _, .tail _ h => by
      show (Nat.beq c.1 d.1 || _) = true
      cases Nat.beq c.1 d.1 with
      | true => rfl
      | false => exact mem_isP h

section
variable (f : PE) (a b : D) (ps : PS)

def G (q : Nat → RExpr) (x : RExpr) : RExpr := eval rOH (ZRootP.setv (envOf a ps q) 0 x) f

theorem G_congr {q : Nat → RExpr} {x x' : RExpr} (h : rEq x x') : rEq (G f a ps q x) (G f a ps q x') :=
  ZNone.eval_congr_env rCF (fun i => by
    show rEq (cond (Nat.beq i 0) x _) (cond (Nat.beq i 0) x' _)
    cases Nat.beq i 0 with
    | true => exact h
    | false => exact rEq_refl _) f

/-- The slope in `x`, read: `G q x − G q y = (x − y)·Q`, `Q ∈ Kx`. -/
theorem G_slope {Y : Nat} {Kx : Iv} (hY0 : Nat.beq 0 Y = false) (hY : ZRootP.uses Y f = false)
    (hK : ivE (ZRootP.BY (BoxOf a b ps) 0 Y) (ZRootP.ddv 0 Y f) = some Kx) {q : Nat → RExpr} (hq : ParIn q ps)
    (hab : rle (dv rOH a) (dv rOH b)) {x y : RExpr} (hx : rle (dv rOH a) x ∧ rle x (dv rOH b))
    (hy : rle (dv rOH a) y ∧ rle y (dv rOH b)) :
    ∃ Q, Mem rCF Q Kx ∧ rEq (radd (G f a ps q x) (rneg (G f a ps q y))) (rmul (radd x (rneg y)) Q) := by
  have he := inbox_env hq (s := dv rOH a) ⟨rle_refl _, hab⟩
  have hB0 : BoxOf a b ps 0 = some (a, b) := rfl
  obtain ⟨Q, hQ, hd⟩ := ZRootP.diff_read rCF hY0 hY hK hB0 he hx hy
  refine ⟨Q, hQ, rEq_trans ?_ hd⟩
  have c : ∀ z, rEq (G f a ps q z) (eval rOH (ZRootP.setv (ZRootP.setv (envOf a ps q) 0 (dv rOH a)) 0 z) f) := fun z =>
    ZNone.eval_congr_env rCF (fun i => by rw [ZRootP.setv_setv_same]; exact rEq_refl _) f
  exact radd_respects (c x) (rneg_respects (c y))

/-- Continuity in the parameters, read. -/
theorem G_lip {Y : Nat} (hY : ZRootP.uses Y f = false) (h0 : isP 0 ps = false)
    (hok : ZRootP.allOK f (BoxOf a b ps) Y (csOf ps) = true) {q q' δ : Nat → RExpr} (hq : ParIn q ps) (hq' : ParIn q' ps)
    {x : RExpr} (hx : rle (dv rOH a) x ∧ rle x (dv rOH b))
    (hδ : ZRootP.AllBd rCF q q' δ (csOf ps)) :
    ZKron.Bd rCF.toOH (radd (G f a ps q x) (rneg (G f a ps q' x))) (ZRootP.sumL rCF δ (csOf ps)) := by
  refine ZRootP.lip_params rCF f (BoxOf a b ps) Y hY (csOf ps) _ _ δ hok (inbox_env hq hx) (inbox_env hq' hx) ?_ ?_
  · intro j hj
    have hp := notIn_csOf hj
    show rEq (cond (Nat.beq j 0) x (envOf a ps q j)) (cond (Nat.beq j 0) x (envOf a ps q' j))
    cases Nat.beq j 0 with
    | true => exact rEq_refl _
    | false =>
        show rEq (cond (Nat.beq j 0) (dv rOH a) (cond (isP j ps) (q j) rzero)) (cond (Nat.beq j 0) (dv rOH a) (cond (isP j ps) (q' j) rzero))
        rw [hp]; cases Nat.beq j 0 <;> exact rEq_refl _
  · -- the parameter entries of the two points are those of q, q'
    have key : ∀ (cs : PS), (∀ c, List.Mem c cs → isP c.1 ps = true) → ZRootP.AllBd rCF q q' δ (csOf cs) →
        ZRootP.AllBd rCF (ZRootP.setv (envOf a ps q) 0 x) (ZRootP.setv (envOf a ps q') 0 x) δ (csOf cs) := by
      intro cs
      induction cs with
      | nil => intro _ _; trivial
      | cons c cs ih =>
          intro hP ⟨b1, b2⟩
          refine ⟨?_, ih (fun d hd => hP d (List.Mem.tail _ hd)) b2⟩
          have hc := hP c (List.Mem.head _)
          have hc0 : Nat.beq c.1 0 = false := by
            cases h : Nat.beq c.1 0 with
            | false => rfl
            | true => have := Nat.eq_of_beq_eq_true h; rw [this] at hc; rw [h0] at hc; cases hc
          show ZKron.Bd rCF.toOH (radd (cond (Nat.beq c.1 0) x (cond (Nat.beq c.1 0) (dv rOH a) (cond (isP c.1 ps) (q c.1) rzero)))
            (rneg (cond (Nat.beq c.1 0) x (cond (Nat.beq c.1 0) (dv rOH a) (cond (isP c.1 ps) (q' c.1) rzero))))) (δ c.1)
          rw [hc0, hc]; exact b1
    exact key ps (fun c hc => mem_isP hc) hδ

/-- The signs at the ends, read: `G q a ≤ 0`, `G q b ≥ 0` for every parameter point in the box. -/
theorem G_ends {Ka Kb : Iv} (hKa : ivE (BoxOf a a ps) f = some Ka) (hKb : ivE (BoxOf b b ps) f = some Kb)
    (ha : dle Ka.2 dz = true) (hb : dle dz Kb.1 = true) {q : Nat → RExpr} (hq : ParIn q ps) :
    rle (G f a ps q (dv rOH a)) rzero ∧ rle rzero (G f a ps q (dv rOH b)) := by
  have ea : InBox rCF (BoxOf a a ps) (ZRootP.setv (envOf a ps q) 0 (dv rOH a)) := inbox_env hq ⟨rle_refl _, rle_refl _⟩
  have eb : InBox rCF (BoxOf b b ps) (ZRootP.setv (envOf b ps q) 0 (dv rOH b)) := inbox_env hq ⟨rle_refl _, rle_refl _⟩
  have ma := ivE_sound rCF ea f Ka hKa
  have mb := ivE_sound rCF eb f Kb hKb
  have za := dv_dz rCF
  -- envOf b … and envOf a … differ only at 0, which setv overrides
  have same : rEq (eval rOH (ZRootP.setv (envOf b ps q) 0 (dv rOH b)) f) (G f a ps q (dv rOH b)) :=
    ZNone.eval_congr_env rCF (fun i => by
      show rEq (cond (Nat.beq i 0) _ (cond (Nat.beq i 0) (dv rOH b) _)) (cond (Nat.beq i 0) _ (cond (Nat.beq i 0) (dv rOH a) _))
      cases Nat.beq i 0 <;> exact rEq_refl _) f
  exact ⟨rCF.le_trans ma.2 (rCF.le_respects (rEq_refl _) za (dle_sound rCF.toOH ha)),
    rCF.le_respects (rEq_refl _) same (rCF.le_trans (rCF.le_respects za (rEq_refl _) (dle_sound rCF.toOH hb)) mb.1)⟩
end


/-! ## The certificate, and the approximants -/

/-- Everything the kernel checks (each field closed by `decide` on a concrete certificate). -/
structure RC (f : PE) (a b : D) (ps : PS) (Y s C B : Nat) (Lx : D) : Prop where
  hab : dle a b = true
  h0 : isP 0 ps = false
  hY0 : Nat.beq 0 Y = false
  hY : ZRootP.uses Y f = false
  ends_a : ∃ K, ivE (BoxOf a a ps) f = some K ∧ dle K.2 dz = true
  ends_b : ∃ K, ivE (BoxOf b b ps) f = some K ∧ dle dz K.1 = true
  slope : ∃ K, ivE (ZRootP.BY (BoxOf a b ps) 0 Y) (ZRootP.ddv 0 Y f) = some K ∧
    dle ⟨⟨1, 0⟩, s⟩ K.1 = true ∧ dle K.2 Lx = true
  lip : ZRootP.allOK f (BoxOf a b ps) Y (csOf ps) = true
  lsum : dle (ZRootP.Lsum (csOf ps)) ⟨⟨2 ^ C, 0⟩, 0⟩ = true
  lx : dle Lx ⟨⟨2 ^ C, 0⟩, 0⟩ = true
  wid : dle (dadd b (dneg a)) ⟨⟨2 ^ B, 0⟩, 0⟩ = true

section
variable (f : PE) (a b : D) (ps : PS) (p : Nat → RExpr)

/-- The `n`-th approximants of the parameters, as constants. -/
def pn (n : Nat) : Nat → RExpr := fun i => rofQ ((p i).seq n)

/-- The rational polynomial `t ↦ g(t, p⁽ⁿ⁾)`. -/
def qenv (n : Nat) (t : QExpr) : Nat → QExpr := fun i => cond (Nat.beq i 0) t (cond (isP i ps) ((p i).seq n) qzero)
def gq (n : Nat) (t : QExpr) : QExpr := evalQ (qenv ps p n t) f

/-- The bracket of the `n`-th approximation after `n` halvings. -/
def br (n : Nat) : D × D := bisD (gq f ps p n) a b n

theorem G_gq (n : Nat) (t : QExpr) : rEq (G f a ps (pn p n) (rofQ t)) (rofQ (gq f ps p n t)) := by
  refine rEq_trans (ZNone.eval_congr_env rCF (fun i => ?_) f) (eval_const (qenv ps p n t) f)
  show rEq (cond (Nat.beq i 0) (rofQ t) (cond (Nat.beq i 0) (dv rOH a) (cond (isP i ps) (rofQ ((p i).seq n)) rzero)))
    (rofQ (cond (Nat.beq i 0) t (cond (isP i ps) ((p i).seq n) qzero)))
  cases Nat.beq i 0 with
  | true => exact rEq_refl _
  | false => cases isP i ps <;> exact rEq_refl _

theorem dv_rofQ (d : D) : rEq (dv rOH d) (rofQ (qD d)) := rEq_of_seq (fun n => dv_seq d n)

/-- The rational signs are the VR signs at the approximants. -/
theorem sign_le {n : Nat} {d : D} (h : qle (gq f ps p n (qD d)) qzero) : rle (G f a ps (pn p n) (dv rOH d)) rzero :=
  rCF.le_respects (rEq_symm (rEq_trans (G_congr f a ps (dv_rofQ d)) (G_gq f a ps p n (qD d)))) (rEq_refl _)
    (rle_of_eventually 0 (fun _ _ => h))

theorem sign_ge {n : Nat} {d : D} (h : qle qzero (gq f ps p n (qD d))) : rle rzero (G f a ps (pn p n) (dv rOH d)) :=
  rCF.le_respects (rEq_refl _) (rEq_symm (rEq_trans (G_congr f a ps (dv_rofQ d)) (G_gq f a ps p n (qD d))))
    (rle_of_eventually 0 (fun _ _ => h))

theorem sign_back_le {n : Nat} {d : D} (h : rle (G f a ps (pn p n) (dv rOH d)) rzero) : qle (gq f ps p n (qD d)) qzero :=
  const_le (fun _ => qEq_refl _) (fun _ => qEq_refl _)
    (rCF.le_respects (rEq_trans (G_congr f a ps (dv_rofQ d)) (G_gq f a ps p n (qD d))) (rEq_refl _) h)

theorem sign_back_ge {n : Nat} {d : D} (h : rle rzero (G f a ps (pn p n) (dv rOH d))) : qle qzero (gq f ps p n (qD d)) :=
  const_le (fun _ => qEq_refl _) (fun _ => qEq_refl _)
    (rCF.le_respects (rEq_refl _) (rEq_trans (G_congr f a ps (dv_rofQ d)) (G_gq f a ps p n (qD d))) h)

/-- At an approximation inside the box, the halving keeps the sign change. -/
theorem br_sign {Y s C B : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) {n : Nat} (hn : ParIn (pn p n) ps) :
    rle (G f a ps (pn p n) (dv rOH (br f a b ps p n).1)) rzero ∧ rle rzero (G f a ps (pn p n) (dv rOH (br f a b ps p n).2)) := by
  obtain ⟨Ka, hKa, ha⟩ := R.ends_a
  obtain ⟨Kb, hKb, hb⟩ := R.ends_b
  obtain ⟨e1, e2⟩ := G_ends f a b ps hKa hKb ha hb hn
  obtain ⟨s1, s2⟩ := bisD_sign (gq f ps p n) a b (sign_back_le f a ps p e1) (sign_back_ge f a ps p e2) n
  exact ⟨sign_le f a ps p s1, sign_ge f a ps p s2⟩
end


section
variable (f : PE) (a b : D) (ps : PS) (p : Nat → RExpr)

theorem br_in {Y s C B : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) (n : Nat) :
    (rle (dv rOH a) (dv rOH (br f a b ps p n).1) ∧ rle (dv rOH (br f a b ps p n).1) (dv rOH b)) ∧
    (rle (dv rOH a) (dv rOH (br f a b ps p n).2) ∧ rle (dv rOH (br f a b ps p n).2) (dv rOH b)) := by
  have hab := dle_sound rOH R.hab
  obtain ⟨i1, i2⟩ := bisD_in rCF (gq f ps p n) a b hab n
  obtain ⟨o, _⟩ := bisD_ord rCF (gq f ps p n) a b hab n
  exact ⟨⟨i1, rle_trans o i2⟩, ⟨rle_trans i1 o, i2⟩⟩

theorem dv_hp_gen {α : Type} (S : CF α) (s : Nat) : S.r (dv S.toOH (⟨⟨1, 0⟩, s⟩ : D)) (hp S.toOH s) := by
  show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) (hp S.toOH s)) (hp S.toOH s); cr_ring S.toCR

theorem bd_nonneg {α : Type} (S : CF α) {x d : α} (h : ZKron.Bd S.toOH x d) : S.le S.zero d := by
  obtain ⟨h1, h2⟩ := h; cr_linarith S.toOCR [h1, h2]

theorem dv_hp (s : Nat) : rEq (dv rOH (⟨⟨1, 0⟩, s⟩ : D)) (hp rOH s) := dv_hp_gen rCF s

/-- **THE CORE ESTIMATE**: the left end at `m` exceeds the right end at `n` by at most `2^s·2⁻ʲ·ΣL`. -/
theorem core {Y s C B : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) {n m j : Nat}
    (hn : ParIn (pn p n) ps) (hm : ParIn (pn p m) ps)
    (hδ : ZRootP.AllBd rCF (pn p n) (pn p m) (fun _ => hp rOH j) (csOf ps)) :
    rle (rmul (radd (dv rOH (br f a b ps p m).1) (rneg (dv rOH (br f a b ps p n).2))) (hp rOH s))
      (rmul (hp rOH j) (dv rOH (ZRootP.Lsum (csOf ps)))) := by
  obtain ⟨Kx, hKx, hc, _⟩ := R.slope
  have hab := dle_sound rOH R.hab
  obtain ⟨⟨tm1, tm2⟩, _⟩ := br_in f a b ps p R m
  obtain ⟨_, ⟨hn1, hn2⟩⟩ := br_in f a b ps p R n
  obtain ⟨Q, hQ, hid⟩ := G_slope f a b ps R.hY0 R.hY hKx hm hab ⟨tm1, tm2⟩ ⟨hn1, hn2⟩
  have cQ : rle (dv rOH (⟨⟨1, 0⟩, s⟩ : D)) Q := rle_trans (dle_sound rOH hc) hQ.1
  have pc : rCF.pos (dv rOH (⟨⟨1, 0⟩, s⟩ : D)) := rCF.pos_congr (rEq_symm (dv_hp s)) (ZNone.pos_hp rCF s)
  obtain ⟨g1, g2⟩ := G_lip f a b ps R.hY R.h0 R.lip hn hm ⟨hn1, hn2⟩ hδ
  have hs := ZRootP.sumL_const rCF (hp rOH j) (hp_nonneg rOH j) (csOf ps)
  have D0 : rle rzero (ZRootP.sumL rCF (fun _ => hp rOH j) (csOf ps)) := bd_nonneg rCF ⟨g1, g2⟩
  have sn := (br_sign f a b ps p R hn).2
  have sm := (br_sign f a b ps p R hm).1
  have bc := ZRootP.bracket_close_s rCF (G := G f a ps (pn p n)) (G' := G f a ps (pn p m)) pc D0 Q cQ hid g2 sn sm
  exact rCF.le_respects (rmul_respects (rEq_refl _) (dv_hp s)) hs bc
end


/-! ## From the core estimate to convergence — arithmetic in any field -/

section
variable {α : Type} (S : CF α)

theorem hp_le_one : ∀ r, S.le (hp S.toOH r) S.one
  | 0 => S.le_refl _
  | r + 1 => by
      have ih := hp_le_one r
      have h0 := half_nonneg S.toOH
      have hh : S.r (S.add S.half S.half) S.one := S.half_spec
      have n0 := hp_nonneg S.toOH r
      have m := le_mul_right S.toOH ih h0
      show S.le (S.mul S.half (hp S.toOH r)) S.one
      have e : S.r (S.mul S.one S.half) S.half := by cr_ring S.toCR
      have m' : S.le (S.mul (hp S.toOH r) S.half) S.half := S.le_respects (S.refl _) e m
      have c : S.r (S.mul (hp S.toOH r) S.half) (S.mul S.half (hp S.toOH r)) := by cr_ring S.toCR
      have m'' := S.le_respects c (S.refl _) m'
      cr_linarith S.toOCR [m'', hh, h0]

theorem hp_anti (a r : Nat) : S.le (hp S.toOH (a + r)) (hp S.toOH a) := by
  have e := hp_add S.toOH a r
  have m := le_mul_right S.toOH (hp_le_one S r) (hp_nonneg S.toOH a)
  have c1 : S.r (S.mul (hp S.toOH r) (hp S.toOH a)) (S.mul (hp S.toOH a) (hp S.toOH r)) := by cr_ring S.toCR
  have c2 : S.r (S.mul S.one (hp S.toOH a)) (hp S.toOH a) := by cr_ring S.toCR
  exact S.le_respects (S.symm e) (S.refl _) (S.le_respects c1 c2 m)

/-- **The step to convergence.** `(tm − hn)·2⁻ˢ ≤ 2⁻ʲ·L`, `L ≤ 2^C`, `hn − tn = W·2⁻ⁿ`, `0 ≤ W ≤ 2^B`,
`j = k+2+C+s`, `n = k+2+B+r`: then `tm − tn ≤ 2⁻⁽ᵏ⁺¹⁾`. -/
theorem conv_step {tm hn tn L W : α} {s C B k r : Nat}
    (hcore : S.le (S.mul (S.add tm (S.neg hn)) (hp S.toOH s)) (S.mul (hp S.toOH ((k + 2) + (C + s))) L))
    (hL : S.le L (nI S.toOH (2 ^ C)))
    (hw : S.r (S.add hn (S.neg tn)) (S.mul W (hp S.toOH ((k + 2 + B) + r))))
    (hW : S.le W (nI S.toOH (2 ^ B))) :
    S.le (S.add tm (S.neg tn)) (hp S.toOH (k + 1)) := by
  -- A: tm − hn ≤ hp(k+2)
  have Ns := nI_nonneg S.toOH (2 ^ s)
  have m1 := le_mul_right S.toOH hcore Ns
  have hj0 := hp_nonneg S.toOH ((k + 2) + (C + s))
  have m2 := le_mul_right S.toOH (mul_le_l S hj0 hL) Ns
  have tS := two_hp S.toOH s
  have tC := two_hp S.toOH C
  have tB := two_hp S.toOH B
  have hj := S.trans (hp_add S.toOH (k + 2) (C + s)) (S.mul_congr (S.refl _) (hp_add S.toOH C s))
  have A1 : S.r (S.mul (S.mul (S.add tm (S.neg hn)) (hp S.toOH s)) (nI S.toOH (2 ^ s))) (S.add tm (S.neg hn)) := by
    refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add tm (S.neg hn)) (S.mul (nI S.toOH (2 ^ s)) (hp S.toOH s)))) ?_
    exact S.trans (S.mul_congr (S.refl _) tS) (by cr_ring S.toCR)
  have A2 : S.r (S.mul (S.mul (hp S.toOH ((k + 2) + (C + s))) (nI S.toOH (2 ^ C))) (nI S.toOH (2 ^ s))) (hp S.toOH (k + 2)) := by
    refine S.trans (S.mul_congr (S.mul_congr hj (S.refl _)) (S.refl _)) ?_
    refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (hp S.toOH (k + 2)) (S.mul (S.mul (nI S.toOH (2 ^ C)) (hp S.toOH C)) (S.mul (nI S.toOH (2 ^ s)) (hp S.toOH s))))) ?_
    exact S.trans (S.mul_congr (S.refl _) (S.mul_congr tC tS)) (by cr_ring S.toCR)
  have A : S.le (S.add tm (S.neg hn)) (hp S.toOH (k + 2)) :=
    S.le_respects A1 A2 (S.le_trans m1 m2)
  -- B: hn − tn ≤ hp(k+2)
  have hn0 := hp_nonneg S.toOH ((k + 2 + B) + r)
  have b1 := le_mul_right S.toOH hW hn0
  have b2 := mul_le_l S (nI_nonneg S.toOH (2 ^ B)) (hp_anti S (k + 2 + B) r)
  have b3 : S.r (S.mul (nI S.toOH (2 ^ B)) (hp S.toOH (k + 2 + B))) (hp S.toOH (k + 2)) := by
    have e := hp_add S.toOH (k + 2) B
    refine S.trans (S.mul_congr (S.refl _) e) ?_
    refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (hp S.toOH (k + 2)) (S.mul (nI S.toOH (2 ^ B)) (hp S.toOH B)))) ?_
    exact S.trans (S.mul_congr (S.refl _) tB) (by cr_ring S.toCR)
  have Bh : S.le (S.add hn (S.neg tn)) (hp S.toOH (k + 2)) :=
    S.le_respects (S.symm hw) b3 (S.le_trans b1 b2)
  have h2 := hp_succ_half S (k + 1)
  cr_linarith S.toOCR [A, Bh, h2]
end


/-! ## The approximants enter the box, and approach each other -/

/-- The point strictly inside the box, by the margin `2⁻ᵘ`. -/
def InnerIn (μ : Nat) (q : Nat → RExpr) : PS → Prop
  | [] => True
  | c :: cs => (rle (dv rOH (dadd c.2.1.1 ⟨⟨1, 0⟩, μ⟩)) (q c.1) ∧ rle (q c.1) (dv rOH (dadd c.2.1.2 (dneg ⟨⟨1, 0⟩, μ⟩)))) ∧
      InnerIn μ q cs

section
variable {α : Type} (S : CF α)
theorem margin_lo {x y lo h : α} (hb : ZKron.Bd S.toOH (S.add x (S.neg y)) h) (hx : S.le (S.add lo h) x) : S.le lo y := by
  obtain ⟨_, b2⟩ := hb; cr_linarith S.toOCR [b2, hx]
theorem margin_hi {x y hi h : α} (hb : ZKron.Bd S.toOH (S.add x (S.neg y)) h) (hx : S.le x (S.add hi (S.neg h))) : S.le y hi := by
  obtain ⟨b1, _⟩ := hb; cr_linarith S.toOCR [b1, hx]
theorem dv_dadd_m (d : D) (μ : Nat) : S.r (dv S.toOH (dadd d ⟨⟨1, 0⟩, μ⟩)) (S.add (dv S.toOH d) (hp S.toOH μ)) :=
  S.trans (dv_add S.toOH _ _) (S.add_congr (S.refl _) (dv_hp_gen S μ))
theorem dv_dsub_m (d : D) (μ : Nat) : S.r (dv S.toOH (dadd d (dneg ⟨⟨1, 0⟩, μ⟩))) (S.add (dv S.toOH d) (S.neg (hp S.toOH μ))) :=
  S.trans (dv_add S.toOH _ _) (S.add_congr (S.refl _) (S.trans (dv_neg S.toOH _) (S.neg_congr (dv_hp_gen S μ))))
end

theorem innerIn_mem {μ : Nat} {q : Nat → RExpr} {c : Nat × Iv × D} : ∀ {ps : PS}, InnerIn μ q ps → List.Mem c ps →
    rle (dv rOH (dadd c.2.1.1 ⟨⟨1, 0⟩, μ⟩)) (q c.1) ∧ rle (q c.1) (dv rOH (dadd c.2.1.2 (dneg ⟨⟨1, 0⟩, μ⟩)))
  | _ :: _, ⟨h, _⟩, .head _ => h
  | _ :: _, ⟨_, hs⟩, .tail _ hm => innerIn_mem hs hm

theorem parIn_of {q : Nat → RExpr} : ∀ {ps : PS}, (∀ c, List.Mem c ps → rle (dv rOH c.2.1.1) (q c.1) ∧ rle (q c.1) (dv rOH c.2.1.2)) →
    ParIn q ps
  | [], _ => trivial
  | c :: cs, h => ⟨h c (List.Mem.head _), parIn_of (fun d hd => h d (List.Mem.tail _ hd))⟩

theorem allBd_of {q q' δ : Nat → RExpr} : ∀ {ps : PS},
    (∀ c, List.Mem c ps → ZKron.Bd rCF.toOH (radd (q c.1) (rneg (q' c.1))) (δ c.1)) → ZRootP.AllBd rCF q q' δ (csOf ps)
  | [], _ => trivial
  | c :: cs, h => ⟨h c (List.Mem.head _), allBd_of (fun d hd => h d (List.Mem.tail _ hd))⟩

/-- **The approximants enter the box.** -/
theorem approx_in (ps : PS) (p : Nat → RExpr) {μ : Nat} (hin : InnerIn μ p ps) : ∃ N, ∀ n, N ≤ n → ParIn (pn p n) ps := by
  obtain ⟨N, hN⟩ := common_N (P := fun i n => ZKron.Bd rCF.toOH (radd (p i) (rneg (rofQ ((p i).seq n)))) (hp rOH μ)) ps
    (fun c _ => approx_close (p c.1) μ)
  refine ⟨N, fun n hn => parIn_of (fun c hc => ?_)⟩
  obtain ⟨i1, i2⟩ := innerIn_mem hin hc
  have hb := hN n hn c hc
  exact ⟨margin_lo rCF hb (rCF.le_respects (dv_dadd_m rCF _ μ) (rEq_refl _) i1),
         margin_hi rCF hb (rCF.le_respects (rEq_refl _) (dv_dsub_m rCF _ μ) i2)⟩

/-- **Two approximants are close.** -/
theorem approx_pair (ps : PS) (p : Nat → RExpr) (j : Nat) : ∃ N, ∀ n m, N ≤ n → N ≤ m →
    ZRootP.AllBd rCF (pn p n) (pn p m) (fun _ => hp rOH j) (csOf ps) := by
  obtain ⟨N, hN⟩ := common_N (P := fun i n => ∀ n' m', n ≤ n' → n ≤ m' →
      ZKron.Bd rCF.toOH (radd (rofQ ((p i).seq n')) (rneg (rofQ ((p i).seq m')))) (hp rOH j)) ps (fun c _ => by
    obtain ⟨Nc, hc⟩ := (p c.1).cauchy j
    refine ⟨Nc, fun n hn n' m' h1 h2 => ?_⟩
    obtain ⟨q1, q2⟩ := hc n' m' (Nat.le_trans hn h1) (Nat.le_trans hn h2)
    exact ⟨rle_of_eventually 0 (fun k _ => by
        have e := hp_seq j k
        change qle (qneg ((hp rOH j).seq k)) (qadd ((p c.1).seq n') (qneg ((p c.1).seq m')))
        unfold qsub at q2; rat_linarith),
      rle_of_eventually 0 (fun k _ => by
        have e := hp_seq j k
        change qle (qadd ((p c.1).seq n') (qneg ((p c.1).seq m'))) ((hp rOH j).seq k)
        unfold qsub at q1; rat_linarith)⟩)
  exact ⟨N, fun n m hn hm => allBd_of (fun c hc => hN N (Nat.le_refl _) c hc n m hn hm)⟩


/-! ## The left ends converge: the root as a VR real -/

section
variable (f : PE) (a b : D) (ps : PS) (p : Nat → RExpr)

theorem side {Y s C B : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) {n m k r : Nat}
    (hn : ParIn (pn p n) ps) (hm : ParIn (pn p m) ps) (hnr : n = (k + 2 + B) + r)
    (hδ : ZRootP.AllBd rCF (pn p n) (pn p m) (fun _ => hp rOH ((k + 2) + (C + s))) (csOf ps)) :
    rle (radd (dv rOH (br f a b ps p m).1) (rneg (dv rOH (br f a b ps p n).1))) (hp rOH (k + 1)) := by
  have hc := core f a b ps p R hn hm hδ
  have hL : rle (dv rOH (ZRootP.Lsum (csOf ps))) (nI rOH (2 ^ C)) :=
    rCF.le_respects (rEq_refl _) (dv_nat rCF _) (dle_sound rOH R.lsum)
  have hW : rle (radd (dv rOH b) (rneg (dv rOH a))) (nI rOH (2 ^ B)) :=
    rCF.le_respects (rEq_trans (dv_add rOH _ _) (radd_respects (rEq_refl _) (dv_neg rOH _))) (dv_nat rCF _) (dle_sound rOH R.wid)
  have hab := dle_sound rOH R.hab
  have hw := (bisD_ord rCF (gq f ps p n) a b hab n).2
  have e : hp rCF.toOH n = hp rCF.toOH (k + 2 + B + r) := congrArg (hp rCF.toOH) hnr
  rw [e] at hw
  exact conv_step rCF hc hL hw hW

/-- **The left ends are Cauchy.** -/
theorem t_cauchy {Y s C B μ : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) (hin : InnerIn μ p ps) :
    ∀ k, ∃ N, ∀ m n, N ≤ m → N ≤ n → qclose (qD (br f a b ps p m).1) (qD (br f a b ps p n).1) (qeps k) := by
  intro k
  obtain ⟨N1, h1⟩ := approx_in ps p hin
  obtain ⟨N2, h2⟩ := approx_pair ps p ((k + 2) + (C + s))
  refine ⟨N1 + N2 + (k + 2 + B), fun m n hm hn => ?_⟩
  have le1 : ∀ x, N1 + N2 + (k + 2 + B) ≤ x → N1 ≤ x := fun x h =>
    Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ _)) h
  have le2 : ∀ x, N1 + N2 + (k + 2 + B) ≤ x → N2 ≤ x := fun x h =>
    Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ _)) h
  have le3 : ∀ x, N1 + N2 + (k + 2 + B) ≤ x → k + 2 + B ≤ x := fun x h => Nat.le_trans (Nat.le_add_left _ _) h
  obtain ⟨rn, hrn⟩ := le_ex (le3 n hn)
  obtain ⟨rm, hrm⟩ := le_ex (le3 m hm)
  have s1 := side f a b ps p R (h1 n (le1 n hn)) (h1 m (le1 m hm)) hrn (h2 n m (le2 n hn) (le2 m hm))
  have s2 := side f a b ps p R (h1 m (le1 m hm)) (h1 n (le1 n hn)) hrm (h2 m n (le2 m hm) (le2 n hn))
  have q1 := const_le (fun i => qadd_respects (dv_seq _ i) (qneg_respects (dv_seq _ i))) (fun i => hp_seq (k + 1) i) s1
  have q2 := const_le (fun i => qadd_respects (dv_seq _ i) (qneg_respects (dv_seq _ i))) (fun i => hp_seq (k + 1) i) s2
  have e := qeps_succ_le k
  constructor <;> (unfold qsub; rat_linarith)

/-- The root, as a VR real: the left ends of the brackets. -/
def root {Y s C B μ : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) (hin : InnerIn μ p ps) : RExpr :=
  ⟨fun n => qD (br f a b ps p n).1, t_cauchy f a b ps p R hin⟩
end


/-! ## The limit is a root -/

section
variable {α : Type} (S : CF α)

theorem lo_drop {lo x h : α} (h0 : S.le S.zero h) (hx : S.le (S.add lo h) x) : S.le lo x := by
  cr_linarith S.toOCR [h0, hx]
theorem hi_drop {hi x h : α} (h0 : S.le S.zero h) (hx : S.le x (S.add hi (S.neg h))) : S.le x hi := by
  cr_linarith S.toOCR [h0, hx]

/-- `V` is within `D₁ + ε·M` above a non-positive value (or below a non-negative one). -/
theorem vbound_le {V A Gu x u Q D1 M ε : α} (h1 : ZKron.Bd S.toOH (S.add V (S.neg A)) D1)
    (hid : S.r (S.add A (S.neg Gu)) (S.mul (S.add x (S.neg u)) Q)) (hQ : ZKron.Bd S.toOH Q M)
    (hx : ZKron.Bd S.toOH (S.add x (S.neg u)) ε) (hG : S.le Gu S.zero) :
    S.le V (S.add D1 (S.mul ε M)) := by
  obtain ⟨_, p2⟩ := ZKron.bd_congr S.toOH (S.symm hid) (S.refl _) (ZKron.bd_mul S.toOH hx hQ)
  obtain ⟨_, a2⟩ := h1
  cr_linarith S.toOCR [p2, a2, hG]

theorem vbound_ge {V A Gu x u Q D1 M ε : α} (h1 : ZKron.Bd S.toOH (S.add V (S.neg A)) D1)
    (hid : S.r (S.add A (S.neg Gu)) (S.mul (S.add x (S.neg u)) Q)) (hQ : ZKron.Bd S.toOH Q M)
    (hx : ZKron.Bd S.toOH (S.add x (S.neg u)) ε) (hG : S.le S.zero Gu) :
    S.le (S.neg V) (S.add D1 (S.mul ε M)) := by
  obtain ⟨p1, _⟩ := ZKron.bd_congr S.toOH (S.symm hid) (S.refl _) (ZKron.bd_mul S.toOH hx hQ)
  obtain ⟨a1, _⟩ := h1
  cr_linarith S.toOCR [p1, a1, hG]

/-- With `D₁ ≤ 2⁻ʲ·M`, `ε ≤ 2·2⁻ʲ`, `M = 2^C` and `j = J+2+C`: the bound is `≤ 2⁻ᴶ`. -/
theorem vbound_fin {D1 ε : α} {J C : Nat} (hD : S.le D1 (S.mul (hp S.toOH ((J + 2) + C)) (nI S.toOH (2 ^ C))))
    (he : S.le ε (S.add (hp S.toOH ((J + 2) + C)) (hp S.toOH ((J + 2) + C)))) :
    S.le (S.add D1 (S.mul ε (nI S.toOH (2 ^ C)))) (hp S.toOH J) := by
  have M0 := nI_nonneg S.toOH (2 ^ C)
  have m := le_mul_right S.toOH he M0
  have e1 : S.r (S.mul (hp S.toOH ((J + 2) + C)) (nI S.toOH (2 ^ C))) (hp S.toOH (J + 2)) := by
    refine S.trans (S.mul_congr (hp_add S.toOH (J + 2) C) (S.refl _)) ?_
    refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (hp S.toOH (J + 2)) (S.mul (nI S.toOH (2 ^ C)) (hp S.toOH C)))) ?_
    exact S.trans (S.mul_congr (S.refl _) (two_hp S.toOH C)) (by cr_ring S.toCR)
  have h1 : S.r (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (hp S.toOH (J + 1)) := hp_succ_half S (J + 1)
  have h0 : S.r (S.add (hp S.toOH (J + 1)) (hp S.toOH (J + 1))) (hp S.toOH J) := hp_succ_half S J
  have p2 := hp_nonneg S.toOH (J + 2)
  have m' : S.le (S.mul ε (nI S.toOH (2 ^ C))) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) :=
    S.le_respects (S.refl _) (S.trans (by cr_ring S.toCR) (S.add_congr e1 e1)) m
  have hD' := S.le_respects (S.refl _) e1 hD
  have sum : S.le (S.add D1 (S.mul ε (nI S.toOH (2 ^ C))))
      (S.add (hp S.toOH (J + 2)) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) := by
    cr_linarith S.toOCR [hD', m']
  -- 3·h ≤ 4·h = hp J
  have four : S.r (S.add (hp S.toOH (J + 2)) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) (S.add (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (hp S.toOH (J + 2))) := by
    cr_ring S.toCR
  have q : S.le (S.add (hp S.toOH (J + 2)) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) (hp S.toOH J) := by
    have t1 : S.r (S.add (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) (hp S.toOH J) :=
      S.trans (S.add_congr h1 h1) h0
    have t2 : S.le (S.add (hp S.toOH (J + 2)) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))))
        (S.add (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) := by
      cr_linarith S.toOCR [p2]
    exact S.le_respects (S.refl _) t1 t2
  exact S.le_trans sum q
end

section
variable (f : PE) (a b : D) (ps : PS) (p : Nat → RExpr)

theorem parIn_inner {μ : Nat} : ∀ {ps : PS}, InnerIn μ p ps → ParIn p ps
  | [], _ => trivial
  | c :: cs, ⟨⟨i1, i2⟩, hs⟩ => by
      have m0 := hp_nonneg rOH μ
      refine ⟨⟨?_, ?_⟩, parIn_inner hs⟩
      · exact lo_drop rCF m0 (rCF.le_respects (dv_dadd_m rCF _ μ) (rEq_refl _) i1)
      · exact hi_drop rCF m0 (rCF.le_respects (rEq_refl _) (dv_dsub_m rCF _ μ) i2)
end


section
variable {α : Type} (S : CF α)
theorem contra_hp {V : α} {J : Nat} (h1 : S.le (hp S.toOH J) V) (h2 : S.le V (hp S.toOH (J + 1))) : False := by
  have e : S.r (S.add (hp S.toOH (J + 1)) (hp S.toOH (J + 1))) (hp S.toOH J) := hp_succ_half S J
  exact S.pos_not_le (ZNone.pos_hp S (J + 1)) (by cr_linarith S.toOCR [h1, h2, e])
theorem contra_hp' {V : α} {J : Nat} (h1 : S.le (hp S.toOH J) (S.neg V)) (h2 : S.le (S.neg V) (hp S.toOH (J + 1))) : False :=
  contra_hp S h1 h2
theorem bd_widen {x e e' : α} (h : ZKron.Bd S.toOH x e) (he : S.le e e') : ZKron.Bd S.toOH x e' := by
  obtain ⟨h1, h2⟩ := h; exact ⟨by cr_linarith S.toOCR [h1, he], by cr_linarith S.toOCR [h2, he]⟩
theorem bd_shift {x t h e : α} (h1 : ZKron.Bd S.toOH (S.add x (S.neg t)) e) (hw0 : S.le S.zero (S.add h (S.neg t)))
    (hw : S.le (S.add h (S.neg t)) e) : ZKron.Bd S.toOH (S.add x (S.neg h)) (S.add e e) := by
  obtain ⟨a1, a2⟩ := h1; exact ⟨by cr_linarith S.toOCR [a1, hw], by cr_linarith S.toOCR [a2, hw0]⟩
theorem le_two {e : α} (h0 : S.le S.zero e) : S.le e (S.add e e) := by cr_linarith S.toOCR [h0]
theorem bd_Q {Q c L M : α} (hc0 : S.le S.zero c) (h1 : S.le c Q) (h2 : S.le Q L) (hL : S.le L M) : ZKron.Bd S.toOH Q M := by
  exact ⟨by cr_linarith S.toOCR [hc0, h1, h2, hL], S.le_trans h2 hL⟩
/-- `W·2⁻⁽ʲ⁺ᴮ⁺ʳ⁾ ≤ 2⁻ʲ` when `W ≤ 2^B`. -/
theorem wid_small {W : α} {j B r : Nat} (hW : S.le W (nI S.toOH (2 ^ B))) :
    S.le (S.mul W (hp S.toOH ((j + B) + r))) (hp S.toOH j) := by
  have hn0 := hp_nonneg S.toOH ((j + B) + r)
  have b1 := le_mul_right S.toOH hW hn0
  have b2 := mul_le_l S (nI_nonneg S.toOH (2 ^ B)) (hp_anti S (j + B) r)
  have b3 : S.r (S.mul (nI S.toOH (2 ^ B)) (hp S.toOH (j + B))) (hp S.toOH j) := by
    refine S.trans (S.mul_congr (S.refl _) (hp_add S.toOH j B)) ?_
    refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (hp S.toOH j) (S.mul (nI S.toOH (2 ^ B)) (hp S.toOH B)))) ?_
    exact S.trans (S.mul_congr (S.refl _) (two_hp S.toOH B)) (by cr_ring S.toCR)
  exact S.le_respects (S.refl _) b3 (S.le_trans b1 b2)
end

section
variable (f : PE) (a b : D) (ps : PS) (p : Nat → RExpr)

theorem root_in {Y s C B μ : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) (hin : InnerIn μ p ps) :
    rle (dv rOH a) (root f a b ps p R hin) ∧ rle (root f a b ps p R hin) (dv rOH b) := by
  have hab := dle_sound rOH R.hab
  refine ⟨rle_of_eventually 0 (fun n _ => ?_), rle_of_eventually 0 (fun n _ => ?_)⟩
  · have h0 : qle (qD a) (qD (br f a b ps p n).1) :=
      const_le (fun i => dv_seq _ i) (fun i => dv_seq _ i) (bisD_in rCF (gq f ps p n) a b hab n).1
    have e := dv_seq a n
    change qle ((dv rOH a).seq n) (qD (br f a b ps p n).1)
    rat_linarith
  · obtain ⟨o, _⟩ := bisD_ord rCF (gq f ps p n) a b hab n
    have h0 : qle (qD (br f a b ps p n).1) (qD b) :=
      const_le (fun i => dv_seq _ i) (fun i => dv_seq _ i) (rle_trans o (bisD_in rCF (gq f ps p n) a b hab n).2)
    have e := dv_seq b n
    change qle (qD (br f a b ps p n).1) ((dv rOH b).seq n)
    rat_linarith

theorem root_close {Y s C B μ : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) (hin : InnerIn μ p ps) (j : Nat) :
    ∃ N, ∀ n, N ≤ n → ZKron.Bd rCF.toOH (radd (root f a b ps p R hin) (rneg (dv rOH (br f a b ps p n).1))) (hp rOH j) := by
  obtain ⟨N, hN⟩ := approx_close (root f a b ps p R hin) j
  exact ⟨N, fun n hn => ZKron.bd_congr rCF.toOH (radd_respects (rEq_refl _) (rneg_respects (rEq_symm (dv_rofQ _)))) (rEq_refl _) (hN n hn)⟩

/-- **THE ROOT AT A REAL PARAMETER POINT.** On VR's continuum, for every parameter point `p` strictly inside the
certificate's box, `g(root, p) = 0` with `root ∈ [a, b]`. -/
theorem root_is_root {Y s C B μ : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx) (hin : InnerIn μ p ps) :
    rEq (G f a ps p (root f a b ps p R hin)) rzero := by
  obtain ⟨Kx, hKx, hc, hL⟩ := R.slope
  have hab := dle_sound rOH R.hab
  have hpin := parIn_inner p hin
  have xin := root_in f a b ps p R hin
  apply rCF.ap_tight
  intro hap
  -- the common index for precision j = (J+2)+C
  have mk : ∀ J : Nat, ∃ n, ParIn (pn p n) ps ∧
      ZRootP.AllBd rCF p (pn p n) (fun _ => hp rOH ((J + 2) + C)) (csOf ps) ∧
      ZKron.Bd rCF.toOH (radd (root f a b ps p R hin) (rneg (dv rOH (br f a b ps p n).1))) (hp rOH ((J + 2) + C)) ∧
      rle (radd (dv rOH (br f a b ps p n).2) (rneg (dv rOH (br f a b ps p n).1))) (hp rOH ((J + 2) + C)) := by
    intro J
    let j := (J + 2) + C
    obtain ⟨N1, h1⟩ := approx_in ps p hin
    obtain ⟨N2, h2⟩ := common_N (P := fun i n => ZKron.Bd rCF.toOH (radd (p i) (rneg (rofQ ((p i).seq n)))) (hp rOH j)) ps
      (fun c _ => approx_close (p c.1) j)
    obtain ⟨N3, h3⟩ := root_close f a b ps p R hin j
    let n := N1 + N2 + N3 + (j + B)
    have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N3)) (Nat.le_add_right _ _)) (Nat.le_refl _)
    have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N3)) (Nat.le_add_right _ _)) (Nat.le_refl _)
    have hn3 : N3 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N3 (N1 + N2)) (Nat.le_add_right _ _)) (Nat.le_refl _)
    refine ⟨n, h1 n hn1, allBd_of (fun c hc => h2 n hn2 c hc), h3 n hn3, ?_⟩
    have hW : rle (radd (dv rOH b) (rneg (dv rOH a))) (nI rOH (2 ^ B)) :=
      rCF.le_respects (rEq_trans (dv_add rOH _ _) (radd_respects (rEq_refl _) (dv_neg rOH _))) (dv_nat rCF _) (dle_sound rOH R.wid)
    have hw := (bisD_ord rCF (gq f ps p n) a b hab n).2
    have e : hp rCF.toOH n = hp rCF.toOH ((j + B) + (N1 + N2 + N3)) := by
      congr 1; show N1 + N2 + N3 + (j + B) = j + B + (N1 + N2 + N3); exact Nat.add_comm _ _
    rw [e] at hw
    exact rCF.le_respects (rEq_symm hw) (rEq_refl _) (wid_small rCF hW)
  have hLs : ∀ j, rle (ZRootP.sumL rCF (fun _ => hp rOH j) (csOf ps)) (rmul (hp rOH j) (nI rOH (2 ^ C))) := fun j =>
    rle_trans (rCF.le_respects (rEq_symm (ZRootP.sumL_const rCF (hp rOH j) (hp_nonneg rOH j) (csOf ps))) (rEq_refl _) (rle_refl _))
      (mul_le_l rCF (hp_nonneg rOH j) (rCF.le_respects (rEq_refl _) (dv_nat rCF _) (dle_sound rOH R.lsum)))
  have hc0 : rle rzero (dv rOH (⟨⟨1, 0⟩, s⟩ : D)) := rCF.le_respects (rEq_refl _) (rEq_symm (dv_hp s)) (hp_nonneg rOH s)
  have hLC : rle (dv rOH Lx) (nI rOH (2 ^ C)) := rCF.le_respects (rEq_refl _) (dv_nat rCF _) (dle_sound rOH R.lx)
  cases hap with
  | inl hpos =>
      obtain ⟨J0, hJ0⟩ := ZRootVR.vr_complete.arch hpos
      obtain ⟨n, hn, hδ, hx, _⟩ := mk (J0 + 1)
      obtain ⟨⟨t1, t2⟩, _⟩ := br_in f a b ps p R n
      have g1 := G_lip f a b ps R.hY R.h0 R.lip hpin hn xin hδ
      obtain ⟨Q, hQ, hid⟩ := G_slope f a b ps R.hY0 R.hY hKx hn hab xin ⟨t1, t2⟩
      have bQ := bd_Q rCF hc0 (rle_trans (dle_sound rOH hc) hQ.1) (rle_trans hQ.2 (dle_sound rOH hL)) hLC
      have vb := vbound_le rCF g1 hid bQ (bd_widen rCF hx (le_two rCF (hp_nonneg rOH _))) (br_sign f a b ps p R hn).1
      have fin := vbound_fin rCF (J := J0 + 1) (C := C) (hLs _) (rle_refl _)
      exact contra_hp rCF hJ0 (rle_trans vb fin)
  | inr hneg =>
      obtain ⟨J0, hJ0⟩ := ZRootVR.vr_complete.arch hneg
      obtain ⟨n, hn, hδ, hx, hw⟩ := mk (J0 + 1)
      obtain ⟨_, ⟨u1, u2⟩⟩ := br_in f a b ps p R n
      have g1 := G_lip f a b ps R.hY R.h0 R.lip hpin hn xin hδ
      obtain ⟨Q, hQ, hid⟩ := G_slope f a b ps R.hY0 R.hY hKx hn hab xin ⟨u1, u2⟩
      have bQ := bd_Q rCF hc0 (rle_trans (dle_sound rOH hc) hQ.1) (rle_trans hQ.2 (dle_sound rOH hL)) hLC
      have o := (bisD_ord rCF (gq f ps p n) a b hab n).1
      have hw0 : rle rzero (radd (dv rOH (br f a b ps p n).2) (rneg (dv rOH (br f a b ps p n).1))) := OCR.sub_nonneg_of_le rCF.toOCR o
      have hxh := bd_shift rCF hx hw0 hw
      have vb := vbound_ge rCF g1 hid bQ hxh (br_sign f a b ps p R hn).2
      have fin := vbound_fin rCF (J := J0 + 1) (C := C) (hLs _) (rle_refl _)
      exact contra_hp' rCF hJ0 (rle_trans vb fin)
end


/-! ## Unique, and a first example -/

section
variable {α : Type} (S : CF α)
/-- `(u − v)·Q = 0` with `Q > 0`: `u = v`. -/
theorem cancel_pos {u v Q : α} (hQ : S.pos Q) (h : S.r (S.mul (S.add u (S.neg v)) Q) S.zero) : S.r u v := by
  obtain ⟨Qi, hi⟩ := S.inv (Or.inl hQ)
  have e : S.r (S.add u (S.neg v)) S.zero := by
    have t : S.r (S.add u (S.neg v)) (S.mul (S.mul (S.add u (S.neg v)) Q) Qi) :=
      S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add u (S.neg v)) S.one))
        (S.trans (S.mul_congr (S.refl _) (S.symm hi)) (by cr_ring S.toCR))
    exact S.trans t (S.trans (S.mul_congr h (S.refl _)) (by cr_ring S.toCR))
  exact S.trans (by cr_ring S.toCR : S.r u (S.add (S.add u (S.neg v)) v)) (S.trans (S.add_congr e (S.refl _)) (by cr_ring S.toCR))
end

/-- **UNIQUE**: two roots in `[a, b]` at the same point are equal. -/
theorem root_unique (f : PE) (a b : D) (ps : PS) {Y s C B : Nat} {Lx : D} (R : RC f a b ps Y s C B Lx)
    {q : Nat → RExpr} (hq : ParIn q ps) {u v : RExpr} (hu : rle (dv rOH a) u ∧ rle u (dv rOH b))
    (hv : rle (dv rOH a) v ∧ rle v (dv rOH b)) (ru : rEq (G f a ps q u) rzero) (rv : rEq (G f a ps q v) rzero) : rEq u v := by
  obtain ⟨Kx, hKx, hc, _⟩ := R.slope
  obtain ⟨Q, hQ, hid⟩ := G_slope f a b ps R.hY0 R.hY hKx hq (dle_sound rOH R.hab) hu hv
  have pc : rCF.pos (dv rOH (⟨⟨1, 0⟩, s⟩ : D)) := rCF.pos_congr (rEq_symm (dv_hp s)) (ZNone.pos_hp rCF s)
  have pQ : rCF.pos Q := rCF.pos_mono pc (rle_trans (dle_sound rOH hc) hQ.1)
  have z : rEq (rmul (radd u (rneg v)) Q) rzero :=
    rEq_trans (rEq_symm hid) (rEq_trans (radd_respects ru (rneg_respects rv)) (by show rCF.r (rCF.add rCF.zero (rCF.neg rCF.zero)) rCF.zero; exact rCF.add_neg _))
  exact cancel_pos rCF pQ z

/-! `√p` for EVERY VR real `p` in `[1 + 2⁻², 4 − 2⁻²]`: `g(x, p) = x² − p` on `x ∈ [1, 2]`, `p` read on `[1, 4]`
(`g(1, ·) ≤ 0`, `g(2, ·) ≥ 0`, slope in `x` the reading of `x + y ∈ [2, 4]`, in `p` the constant `−1`). -/
def sqP : PE := .sub (.pow (.var 0) 2) (.var 1)
def ex_ps : PS := [(1, (⟨⟨1, 0⟩, 0⟩, ⟨⟨4, 0⟩, 0⟩), ⟨⟨1, 0⟩, 0⟩)]

theorem sq_cert : RC sqP ⟨⟨1, 0⟩, 0⟩ ⟨⟨2, 0⟩, 0⟩ ex_ps 2 0 2 0 ⟨⟨4, 0⟩, 0⟩ where
  hab := by decide +kernel
  h0 := rfl
  hY0 := rfl
  hY := rfl
  ends_a := by
    obtain ⟨K, hK⟩ : ∃ K, ivE (BoxOf ⟨⟨1, 0⟩, 0⟩ ⟨⟨1, 0⟩, 0⟩ ex_ps) sqP = some K := ⟨_, rfl⟩
    exact ⟨K, hK, by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel⟩
  ends_b := by
    obtain ⟨K, hK⟩ : ∃ K, ivE (BoxOf ⟨⟨2, 0⟩, 0⟩ ⟨⟨2, 0⟩, 0⟩ ex_ps) sqP = some K := ⟨_, rfl⟩
    exact ⟨K, hK, by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel⟩
  slope := by
    obtain ⟨K, hK⟩ : ∃ K, ivE (ZRootP.BY (BoxOf ⟨⟨1, 0⟩, 0⟩ ⟨⟨2, 0⟩, 0⟩ ex_ps) 0 2) (ZRootP.ddv 0 2 sqP) = some K := ⟨_, rfl⟩
    exact ⟨K, hK, by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel,
      by rw [show K = _ from (Option.some.inj hK).symm]; decide +kernel⟩
  lip := by decide +kernel
  lsum := by decide +kernel
  lx := by decide +kernel
  wid := by decide +kernel

/-- **Every VR real `p ∈ [1¼, 3¾]` has a square root in `[1, 2]`, unique there.** -/
theorem sqrt_exists (p : Nat → RExpr) (hin : InnerIn 2 p ex_ps) :
    ∃ x, (rle (dv rOH ⟨⟨1, 0⟩, 0⟩) x ∧ rle x (dv rOH ⟨⟨2, 0⟩, 0⟩)) ∧ rEq (G sqP ⟨⟨1, 0⟩, 0⟩ ex_ps p x) rzero :=
  ⟨root sqP _ _ ex_ps p sq_cert hin, root_in sqP _ _ ex_ps p sq_cert hin, root_is_root sqP _ _ ex_ps p sq_cert hin⟩

/-- The other side of the fork: on `[1, 1½]` the end check fails (`1½² − p < 0` for `p` near 4). -/
example : (match ivE (BoxOf ⟨⟨3, 0⟩, 1⟩ ⟨⟨3, 0⟩, 1⟩ ex_ps) sqP with | some K => dle dz K.1 | none => false) = false := by
  decide +kernel

end ZRootPVR

#print axioms ZRootPVR.root_unique
#print axioms ZRootPVR.sqrt_exists

#print axioms ZRootPVR.root_in
#print axioms ZRootPVR.root_is_root

#print axioms ZRootPVR.vbound_fin
#print axioms ZRootPVR.parIn_inner

#print axioms ZRootPVR.t_cauchy

#print axioms ZRootPVR.approx_in
#print axioms ZRootPVR.approx_pair

#print axioms ZRootPVR.conv_step

#print axioms ZRootPVR.core

#print axioms ZRootPVR.br_sign

#print axioms ZRootPVR.G_slope
#print axioms ZRootPVR.G_lip
#print axioms ZRootPVR.G_ends

#print axioms ZRootPVR.inbox_env
#print axioms ZRootPVR.approx_close
#print axioms ZRootPVR.common_N

#print axioms ZRootPVR.eval_const
#print axioms ZRootPVR.bisD_ord
#print axioms ZRootPVR.bisD_sign
