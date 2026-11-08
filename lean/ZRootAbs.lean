import ZRootPVR
/-!
# ZRootAbs — the root of a family of increasing functions, from an approximate sign oracle. Zero axioms.

`ZRootPVR` builds the root of a POLYNOMIAL law: the sign of `g(t, p⁽ⁿ⁾)` at a rational point is an exact rational.
With `exp` it is not — `exp` of a rational is a real. What is computable is its `n`-th term, with an error that
goes to zero UNIFORMLY over the box. This file proves the root theorem for any family that has:

  * `Fₙ x`, `F x` (the law at the approximants and at the point), each increasing on `[a, b]` in the ORDERED form
    `c·(y − x) ≤ F y − F x ≤ L·(y − x)` for `x ≤ y` (`Mono`) — no divided difference needed;
  * `Fₙ → F` uniformly on `[a, b]`;
  * a rational ORACLE `gₙ t` with `|Fₙ t − gₙ t| → 0` uniformly over dyadic `t ∈ [a, b]`;
  * the end signs `Fₙ a ≤ 0 ≤ Fₙ b`.

The order of two points is never decided: the bounds are used inside proofs of `≤`, where a sign may be split on
(`ZField.sign_case`, constructive: it is a proof of `False`).

Part 1: the ordered slope, and what it gives without deciding an order.
-/

namespace ZRootAbs
open VR.CSR ZNumBin ZField

variable {α : Type} (S : CF α)

/-- Increasing on `[a, b]` with slope between `c` and `L`, in the ordered form. -/
def Mono (F : α → α) (a b c L : α) : Prop :=
  ∀ x y, S.le a x → S.le x y → S.le y b →
    S.le (S.mul c (S.add y (S.neg x))) (S.add (F y) (S.neg (F x))) ∧
    S.le (S.add (F y) (S.neg (F x))) (S.mul L (S.add y (S.neg x)))

theorem neg_le_zero {h : α} (h0 : S.le S.zero h) : S.le (S.neg h) S.zero := by cr_linarith S.toOCR [h0]
/-- `F − g ≤ e` and `g ≤ 0` give `F ≤ e`. -/
theorem up_err {Fv gv e : α} (hb : S.le (S.add Fv (S.neg gv)) e) (hg : S.le gv S.zero) : S.le Fv e := by
  cr_linarith S.toOCR [hb, hg]
/-- `−e ≤ F − g` and `g ≥ 0` give `−e ≤ F`. -/
theorem lo_err {Fv gv e : α} (hb : S.le (S.neg e) (S.add Fv (S.neg gv))) (hg : S.le S.zero gv) : S.le (S.neg e) Fv := by
  cr_linarith S.toOCR [hb, hg]


theorem nonneg4 {h : α} (h0 : S.le S.zero h) : S.le S.zero (S.add (S.add h h) (S.add h h)) := by cr_linarith S.toOCR [h0]

theorem two_bd {A B P e : α} (h1 : ZKron.Bd S.toOH (S.add A (S.neg P)) e) (h2 : ZKron.Bd S.toOH (S.add B (S.neg P)) e) :
    S.le (S.add A (S.neg B)) (S.add e e) := by
  obtain ⟨_, a2⟩ := h1; obtain ⟨b1, _⟩ := h2; cr_linarith S.toOCR [a2, b1]

/-- `(tm − hn)·2⁻ˢ ≤ 4·2⁻ʲ` with `j = k+4+s`, and `hn − tn ≤ 2⁻⁽ᵏ⁺²⁾`: `tm − tn ≤ 2⁻⁽ᵏ⁺¹⁾`. -/
theorem fam_step {tm hn tn : α} {k s : Nat}
    (hc : S.le (S.mul (S.add tm (S.neg hn)) (hp S.toOH s))
      (S.add (S.add (hp S.toOH ((k + 4) + s)) (hp S.toOH ((k + 4) + s))) (S.add (hp S.toOH ((k + 4) + s)) (hp S.toOH ((k + 4) + s)))))
    (hw : S.le (S.add hn (S.neg tn)) (hp S.toOH (k + 2))) : S.le (S.add tm (S.neg tn)) (hp S.toOH (k + 1)) := by
  have Ns := nI_nonneg S.toOH (2 ^ s)
  have m1 := le_mul_right S.toOH hc Ns
  have tS := two_hp S.toOH s
  have hj := hp_add S.toOH (k + 4) s
  have A1 : S.r (S.mul (S.mul (S.add tm (S.neg hn)) (hp S.toOH s)) (nI S.toOH (2 ^ s))) (S.add tm (S.neg hn)) := by
    refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (S.add tm (S.neg hn)) (S.mul (nI S.toOH (2 ^ s)) (hp S.toOH s)))) ?_
    exact S.trans (S.mul_congr (S.refl _) tS) (by cr_ring S.toCR)
  have one : S.r (S.mul (hp S.toOH ((k + 4) + s)) (nI S.toOH (2 ^ s))) (hp S.toOH (k + 4)) := by
    refine S.trans (S.mul_congr hj (S.refl _)) ?_
    refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (hp S.toOH (k + 4)) (S.mul (nI S.toOH (2 ^ s)) (hp S.toOH s)))) ?_
    exact S.trans (S.mul_congr (S.refl _) tS) (by cr_ring S.toCR)
  have A2 : S.r (S.mul (S.add (S.add (hp S.toOH ((k + 4) + s)) (hp S.toOH ((k + 4) + s))) (S.add (hp S.toOH ((k + 4) + s)) (hp S.toOH ((k + 4) + s)))) (nI S.toOH (2 ^ s)))
      (S.add (S.add (hp S.toOH (k + 4)) (hp S.toOH (k + 4))) (S.add (hp S.toOH (k + 4)) (hp S.toOH (k + 4)))) :=
    S.trans (by cr_ring S.toCR) (S.add_congr (S.add_congr one one) (S.add_congr one one))
  have A := S.le_respects A1 A2 m1
  have h3 : S.r (S.add (hp S.toOH (k + 3 + 1)) (hp S.toOH (k + 3 + 1))) (hp S.toOH (k + 3)) := ZRoot.hp_succ_half S (k + 3)
  have h2 : S.r (S.add (hp S.toOH (k + 2 + 1)) (hp S.toOH (k + 2 + 1))) (hp S.toOH (k + 2)) := ZRoot.hp_succ_half S (k + 2)
  have h1 : S.r (S.add (hp S.toOH (k + 1 + 1)) (hp S.toOH (k + 1 + 1))) (hp S.toOH (k + 1)) := ZRoot.hp_succ_half S (k + 1)
  have e4 : hp S.toOH (k + 4) = hp S.toOH (k + 3 + 1) := rfl
  have e3 : hp S.toOH (k + 3) = hp S.toOH (k + 2 + 1) := rfl
  have e2 : hp S.toOH (k + 2) = hp S.toOH (k + 1 + 1) := rfl
  rw [e4] at A; rw [e3] at h3; rw [e2] at hw h2
  cr_linarith S.toOCR [A, hw, h3, h2, h1]

/-- The final squeeze: `V − A ≤ e`, `A − Gu ≤ M·δ`, `Gu ≤ e`, with `e = 2⁻ʲ`, `M·δ ≤ 2·2⁻⁽ᴶ⁺²⁾`, `j ≥ J+2`:
`V ≤ 2⁻ᴶ`. -/
theorem fam_fin {V A Gu e Md : α} {J : Nat} (h1 : S.le (S.add V (S.neg A)) e) (h2 : S.le (S.add A (S.neg Gu)) Md)
    (h3 : S.le Gu e) (he : S.le e (hp S.toOH (J + 2))) (hM : S.le Md (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) :
    S.le V (hp S.toOH J) := by
  have hb : S.r (S.add (hp S.toOH (J + 1 + 1)) (hp S.toOH (J + 1 + 1))) (hp S.toOH (J + 1)) := ZRoot.hp_succ_half S (J + 1)
  have ha : S.r (S.add (hp S.toOH (J + 1)) (hp S.toOH (J + 1))) (hp S.toOH J) := ZRoot.hp_succ_half S J
  have s1 : S.le V (S.add (S.add e e) Md) := by cr_linarith S.toOCR [h1, h2, h3]
  have s2 : S.le (S.add (S.add e e) Md)
      (S.add (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) := by
    cr_linarith S.toOCR [he, hM]
  have hb' : S.r (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (hp S.toOH (J + 1)) := hb
  have s3 : S.r (S.add (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2))) (S.add (hp S.toOH (J + 2)) (hp S.toOH (J + 2)))) (hp S.toOH J) :=
    S.trans (S.add_congr hb' hb') ha
  exact S.le_trans s1 (S.le_respects (S.refl _) s3 s2)


theorem pow_hp (J C : Nat) : S.r (S.mul (nI S.toOH (2 ^ C)) (hp S.toOH ((J + 2) + C))) (hp S.toOH (J + 2)) := by
  refine S.trans (S.mul_congr (S.refl _) (hp_add S.toOH (J + 2) C)) ?_
  refine S.trans (by cr_ring S.toCR : S.r _ (S.mul (hp S.toOH (J + 2)) (S.mul (nI S.toOH (2 ^ C)) (hp S.toOH C)))) ?_
  exact S.trans (S.mul_congr (S.refl _) (two_hp S.toOH C)) (by cr_ring S.toCR)

theorem mul_two_add (m h : α) : S.r (S.mul m (S.add h h)) (S.add (S.mul m h) (S.mul m h)) := by cr_ring S.toCR
theorem le_twice {h : α} (h0 : S.le S.zero h) : S.le h (S.add h h) := by cr_linarith S.toOCR [h0]
theorem neg_sub_le {A B M : α} (h : S.le (S.neg M) (S.add A (S.neg B))) : S.le (S.add (S.neg A) (S.neg (S.neg B))) M := by
  cr_linarith S.toOCR [h]
theorem neg_up {A e : α} (h : S.le (S.neg e) A) : S.le (S.neg A) e := by cr_linarith S.toOCR [h]
theorem conv_lo {A P e : α} (h : ZKron.Bd S.toOH (S.add A (S.neg P)) e) : S.le (S.add P (S.neg A)) e := by
  obtain ⟨h1, _⟩ := h; cr_linarith S.toOCR [h1]
theorem conv_hi {A P e : α} (h : ZKron.Bd S.toOH (S.add A (S.neg P)) e) : S.le (S.add (S.neg P) (S.neg (S.neg A))) e := by
  obtain ⟨_, h2⟩ := h; cr_linarith S.toOCR [h2]
/-- Two roots of a strictly increasing function are equal. -/
theorem mono_unique {F : α → α} {a b c L u v : α} (hF : Mono S F a b c L) (hc : S.pos c)
    (hu : S.le a u ∧ S.le u b) (hv : S.le a v ∧ S.le v b) (ru : S.r (F u) S.zero) (rv : S.r (F v) S.zero) : S.le u v := by
  apply S.le_of_not_pos
  intro hp
  have hvu : S.le v u := by have := S.pos_nonneg hp; cr_linarith S.toOCR [this]
  obtain ⟨m1, _⟩ := hF v u hv.1 hvu hu.2
  have pm := S.pos_mul hc hp
  have z : S.r (S.add (F u) (S.neg (F v))) S.zero := S.trans (S.add_congr ru (S.neg_congr rv)) (by cr_ring S.toCR)
  exact S.pos_not_le pm (S.le_respects (S.refl _) z m1)

/-- **Two-sided from ordered**: `|y − x| ≤ δ` gives `|F y − F x| ≤ L·δ`, whatever the order of `x, y`. -/
theorem mono_bd {F : α → α} {a b c L : α} (hF : Mono S F a b c L) (hc : S.le S.zero c) (hL : S.le S.zero L)
    {x y δ : α} (hx : S.le a x ∧ S.le x b) (hy : S.le a y ∧ S.le y b) (hxy : ZKron.Bd S.toOH (S.add y (S.neg x)) δ) :
    ZKron.Bd S.toOH (S.add (F y) (S.neg (F x))) (S.mul L δ) := by
  obtain ⟨d1, d2⟩ := hxy
  have d0 : S.le S.zero δ := by cr_linarith S.toOCR [d1, d2]
  have Lδ : S.le S.zero (S.mul L δ) := S.mul_nonneg hL d0
  constructor
  · apply S.le_of_not_pos
    intro hp
    apply sign_case S (S.add y (S.neg x))
    · intro hyx
      have hxy' : S.le x y := by cr_linarith S.toOCR [hyx]
      obtain ⟨m1, _⟩ := hF x y hx.1 hxy' hy.2
      have cm := S.mul_nonneg hc hyx
      exact S.pos_not_le hp (by cr_linarith S.toOCR [m1, cm, Lδ])
    · intro hyx
      have hyx' : S.le y x := by cr_linarith S.toOCR [hyx]
      obtain ⟨_, m2⟩ := hF y x hy.1 hyx' hx.2
      -- F x − F y ≤ L(x − y) ≤ Lδ
      have l1 : S.le (S.mul L (S.add x (S.neg y))) (S.mul L δ) := ZRoot.mul_le_l S hL (by cr_linarith S.toOCR [d1])
      exact S.pos_not_le hp (by cr_linarith S.toOCR [m2, l1])
  · apply S.le_of_not_pos
    intro hp
    apply sign_case S (S.add y (S.neg x))
    · intro hyx
      have hxy' : S.le x y := by cr_linarith S.toOCR [hyx]
      obtain ⟨_, m2⟩ := hF x y hx.1 hxy' hy.2
      have l1 : S.le (S.mul L (S.add y (S.neg x))) (S.mul L δ) := ZRoot.mul_le_l S hL d2
      exact S.pos_not_le hp (by cr_linarith S.toOCR [m2, l1])
    · intro hyx
      have hyx' : S.le y x := by cr_linarith S.toOCR [hyx]
      obtain ⟨m1, _⟩ := hF y x hy.1 hyx' hx.2
      have cm := S.mul_nonneg hc (by cr_linarith S.toOCR [hyx] : S.le S.zero (S.add x (S.neg y)))
      exact S.pos_not_le hp (by cr_linarith S.toOCR [m1, cm, Lδ])

/-- **Two brackets, ordered form, with oracle errors.** `G'(t') ≤ e₁`, `G(s) ≥ −e₂`, `G(s) − G'(s) ≤ D`, `G'`
increasing with slope `≥ c ≥ 0`: then `(t' − s)·c ≤ D + e₁ + e₂`. -/
theorem bracket_ord {G G' : α → α} {a b c L D e1 e2 s t' : α} (hM : Mono S G' a b c L) (hc : S.le S.zero c)
    (hs : S.le a s ∧ S.le s b) (ht : S.le a t' ∧ S.le t' b)
    (h0 : S.le S.zero (S.add D (S.add e1 e2)))
    (hG' : S.le (G' t') e1) (hG : S.le (S.neg e2) (G s)) (hGG : S.le (S.add (G s) (S.neg (G' s))) D) :
    S.le (S.mul (S.add t' (S.neg s)) c) (S.add D (S.add e1 e2)) := by
  apply S.le_of_not_pos
  intro hp
  apply sign_case S (S.add t' (S.neg s))
  · intro h
    have hst : S.le s t' := by cr_linarith S.toOCR [h]
    obtain ⟨m1, _⟩ := hM s t' hs.1 hst ht.2
    have e : S.r (S.mul c (S.add t' (S.neg s))) (S.mul (S.add t' (S.neg s)) c) := by cr_ring S.toCR
    exact S.pos_not_le hp (by cr_linarith S.toOCR [m1, hG', hG, hGG, S.le_respects e (S.refl _) (S.le_refl _)])
  · intro h
    have m := le_mul_right S.toOH h hc
    have e : S.r (S.mul S.zero c) S.zero := by cr_ring S.toCR
    exact S.pos_not_le hp (by cr_linarith S.toOCR [S.le_respects (S.refl _) e m, h0])


/-! ## The family, on VR's continuum -/

section
open VR VR.Numbers ZPoly ZIv ZRealCF ZExp ZRealExp ZRoot ZRootP ZRootPVR

/-- What the root needs of a family: `F n` the law at the `n`-th approximants, `Fp` at the point, `g n` the
rational oracle for `F n`. -/
structure Fam (F : Nat → RExpr → RExpr) (Fp : RExpr → RExpr) (g : Nat → QExpr → QExpr) (a b : D) (s C B N0 : Nat) : Prop where
  hab : dle a b = true
  mono : ∀ n, N0 ≤ n → Mono rCF (F n) (dv rOH a) (dv rOH b) (hp rOH s) (nI rOH (2 ^ C))
  monoP : Mono rCF Fp (dv rOH a) (dv rOH b) (hp rOH s) (nI rOH (2 ^ C))
  ends : ∀ n, N0 ≤ n → rle (F n (dv rOH a)) rzero ∧ rle rzero (F n (dv rOH b))
  conv : ∀ j, ∃ N, ∀ n, N ≤ n → ∀ x, rle (dv rOH a) x → rle x (dv rOH b) →
    ZKron.Bd rCF.toOH (radd (F n x) (rneg (Fp x))) (hp rOH j)
  orac : ∀ j, ∃ N, ∀ n, N ≤ n → ∀ t : D, rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
    ZKron.Bd rCF.toOH (radd (F n (dv rOH t)) (rneg (rofQ (g n (qD t))))) (hp rOH j)
  wid : dle (dadd b (dneg a)) ⟨⟨2 ^ B, 0⟩, 0⟩ = true

variable {F : Nat → RExpr → RExpr} {Fp : RExpr → RExpr} {g : Nat → QExpr → QExpr} {a b : D} {s C B N0 : Nat}

/-- The brackets of the oracle keep the sign change up to the oracle's error. -/
theorem fam_inv (H : Fam F Fp g a b s C B N0) {n j : Nat} (hn : N0 ≤ n)
    (ho : ∀ t : D, rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
      ZKron.Bd rCF.toOH (radd (F n (dv rOH t)) (rneg (rofQ (g n (qD t))))) (hp rOH j)) :
    ∀ k, rle (F n (dv rOH (bisD (g n) a b k).1)) (hp rOH j) ∧ rle (rneg (hp rOH j)) (F n (dv rOH (bisD (g n) a b k).2)) := by
  have hab := dle_sound rOH H.hab
  have hj := hp_nonneg rOH j
  intro k
  induction k with
  | zero =>
      obtain ⟨e1, e2⟩ := H.ends n hn
      exact ⟨rle_trans e1 hj, rle_trans (show rle (rneg (hp rOH j)) rzero by
        show rCF.le (rCF.neg (hp rCF.toOH j)) rCF.zero; exact neg_le_zero rCF hj) e2⟩
  | succ k ih =>
      obtain ⟨o, _⟩ := bisD_ord rCF (g n) a b hab k
      obtain ⟨i1, i2⟩ := bisD_in rCF (g n) a b hab k
      obtain ⟨_, _, n1, n2⟩ := half_step rCF (bisD (g n) a b k).1 (bisD (g n) a b k).2 a b k true o
        (bisD_ord rCF (g n) a b hab k).2
      obtain ⟨_, _, n1', n2'⟩ := half_step rCF (bisD (g n) a b k).1 (bisD (g n) a b k).2 a b k false o
        (bisD_ord rCF (g n) a b hab k).2
      -- the midpoint is in [a, b]
      have mlo : rle (dv rOH a) (dv rOH (mid (bisD (g n) a b k).1 (bisD (g n) a b k).2)) := rle_trans i1 n1
      have mhi : rle (dv rOH (mid (bisD (g n) a b k).1 (bisD (g n) a b k).2)) (dv rOH b) := rle_trans n2' i2
      obtain ⟨b1, b2⟩ := ho _ mlo mhi
      show rle (F n (dv rOH (cond (qleB (g n (qD (mid (bisD (g n) a b k).1 (bisD (g n) a b k).2))) qzero) _ _))) _ ∧
        rle _ (F n (dv rOH (cond (qleB (g n (qD (mid (bisD (g n) a b k).1 (bisD (g n) a b k).2))) qzero) _ _)))
      cases hc : qleB (g n (qD (mid (bisD (g n) a b k).1 (bisD (g n) a b k).2))) qzero with
      | true =>
          have q := qleB_true hc
          have r : rle (rofQ (g n (qD (mid (bisD (g n) a b k).1 (bisD (g n) a b k).2)))) rzero := rle_of_eventually 0 (fun _ _ => q)
          exact ⟨up_err rCF b2 r, ih.2⟩
      | false =>
          have q := qleB_false hc
          have r : rle rzero (rofQ (g n (qD (mid (bisD (g n) a b k).1 (bisD (g n) a b k).2)))) := rle_of_eventually 0 (fun _ _ => q)
          exact ⟨ih.1, lo_err rCF b1 r⟩
end


section
open VR VR.Numbers ZPoly ZIv ZRealCF ZExp ZRealExp ZRoot ZRootP ZRootPVR
variable {F : Nat → RExpr → RExpr} {Fp : RExpr → RExpr} {g : Nat → QExpr → QExpr} {a b : D} {s C B N0 : Nat}

def fbr (g : Nat → QExpr → QExpr) (a b : D) (n : Nat) : D × D := bisD (g n) a b n

theorem fbr_in (H : Fam F Fp g a b s C B N0) (n : Nat) :
    (rle (dv rOH a) (dv rOH (fbr g a b n).1) ∧ rle (dv rOH (fbr g a b n).1) (dv rOH b)) ∧
    (rle (dv rOH a) (dv rOH (fbr g a b n).2) ∧ rle (dv rOH (fbr g a b n).2) (dv rOH b)) := by
  have hab := dle_sound rOH H.hab
  obtain ⟨i1, i2⟩ := bisD_in rCF (g n) a b hab n
  obtain ⟨o, _⟩ := bisD_ord rCF (g n) a b hab n
  exact ⟨⟨i1, rle_trans o i2⟩, ⟨rle_trans i1 o, i2⟩⟩

theorem fbr_wid (H : Fam F Fp g a b s C B N0) {n k r : Nat} (hnr : n = (k + 2 + B) + r) :
    rle (radd (dv rOH (fbr g a b n).2) (rneg (dv rOH (fbr g a b n).1))) (hp rOH (k + 2)) := by
  have hab := dle_sound rOH H.hab
  have hW : rle (radd (dv rOH b) (rneg (dv rOH a))) (nI rOH (2 ^ B)) :=
    rCF.le_respects (rEq_trans (dv_add rOH _ _) (radd_respects (rEq_refl _) (dv_neg rOH _))) (dv_nat rCF _) (dle_sound rOH H.wid)
  have hw := (bisD_ord rCF (g n) a b hab n).2
  have e : hp rCF.toOH n = hp rCF.toOH ((k + 2 + B) + r) := congrArg (hp rCF.toOH) hnr
  rw [e] at hw
  exact rCF.le_respects (rEq_symm hw) (rEq_refl _) (wid_small rCF hW)

theorem fam_side (H : Fam F Fp g a b s C B N0) {n m k r : Nat} (hn : N0 ≤ n) (hm : N0 ≤ m) (hnr : n = (k + 2 + B) + r)
    (on : ∀ t : D, rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
      ZKron.Bd rCF.toOH (radd (F n (dv rOH t)) (rneg (rofQ (g n (qD t))))) (hp rOH ((k + 4) + s)))
    (om : ∀ t : D, rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
      ZKron.Bd rCF.toOH (radd (F m (dv rOH t)) (rneg (rofQ (g m (qD t))))) (hp rOH ((k + 4) + s)))
    (cn : ∀ x, rle (dv rOH a) x → rle x (dv rOH b) → ZKron.Bd rCF.toOH (radd (F n x) (rneg (Fp x))) (hp rOH ((k + 4) + s)))
    (cm : ∀ x, rle (dv rOH a) x → rle x (dv rOH b) → ZKron.Bd rCF.toOH (radd (F m x) (rneg (Fp x))) (hp rOH ((k + 4) + s))) :
    rle (radd (dv rOH (fbr g a b m).1) (rneg (dv rOH (fbr g a b n).1))) (hp rOH (k + 1)) := by
  have hj := hp_nonneg rOH ((k + 4) + s)
  obtain ⟨_, ⟨h1, h2⟩⟩ := fbr_in H n
  obtain ⟨⟨t1, t2⟩, _⟩ := fbr_in H m
  have In := fam_inv H hn on n
  have Im := fam_inv H hm om m
  have hGG := two_bd rCF (cn _ h1 h2) (cm _ h1 h2)
  have h0 : rle rzero (radd (radd (hp rOH ((k + 4) + s)) (hp rOH ((k + 4) + s))) (radd (hp rOH ((k + 4) + s)) (hp rOH ((k + 4) + s)))) :=
    nonneg4 rCF hj
  have bo := bracket_ord rCF (H.mono m hm) (hp_nonneg rOH s) ⟨h1, h2⟩ ⟨t1, t2⟩ h0 Im.1 In.2 hGG
  exact fam_step rCF bo (fbr_wid H hnr)

/-- **The left ends are Cauchy.** -/
theorem fam_cauchy (H : Fam F Fp g a b s C B N0) :
    ∀ k, ∃ N, ∀ m n, N ≤ m → N ≤ n → qclose (qD (fbr g a b m).1) (qD (fbr g a b n).1) (qeps k) := by
  intro k
  obtain ⟨N1, h1⟩ := H.orac ((k + 4) + s)
  obtain ⟨N2, h2⟩ := H.conv ((k + 4) + s)
  refine ⟨N0 + N1 + N2 + (k + 2 + B), fun m n hm hn => ?_⟩
  have l0 : ∀ x, N0 + N1 + N2 + (k + 2 + B) ≤ x → N0 ≤ x := fun x h =>
    Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N0 N1) (Nat.le_add_right _ N2)) (Nat.le_add_right _ _)) h
  have l1 : ∀ x, N0 + N1 + N2 + (k + 2 + B) ≤ x → N1 ≤ x := fun x h =>
    Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N1 N0) (Nat.le_add_right _ N2)) (Nat.le_add_right _ _)) h
  have l2 : ∀ x, N0 + N1 + N2 + (k + 2 + B) ≤ x → N2 ≤ x := fun x h =>
    Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 (N0 + N1)) (Nat.le_add_right _ _)) h
  have l3 : ∀ x, N0 + N1 + N2 + (k + 2 + B) ≤ x → k + 2 + B ≤ x := fun x h => Nat.le_trans (Nat.le_add_left _ _) h
  obtain ⟨rn, hrn⟩ := le_ex (l3 n hn)
  obtain ⟨rm, hrm⟩ := le_ex (l3 m hm)
  have s1 := fam_side H (l0 n hn) (l0 m hm) hrn (h1 n (l1 n hn)) (h1 m (l1 m hm)) (h2 n (l2 n hn)) (h2 m (l2 m hm))
  have s2 := fam_side H (l0 m hm) (l0 n hn) hrm (h1 m (l1 m hm)) (h1 n (l1 n hn)) (h2 m (l2 m hm)) (h2 n (l2 n hn))
  have q1 := const_le (fun i => qadd_respects (dv_seq _ i) (qneg_respects (dv_seq _ i))) (fun i => hp_seq (k + 1) i) s1
  have q2 := const_le (fun i => qadd_respects (dv_seq _ i) (qneg_respects (dv_seq _ i))) (fun i => hp_seq (k + 1) i) s2
  have e := qeps_succ_le k
  constructor <;> (unfold qsub; rat_linarith)

/-- The root: the limit of the oracle's left ends. -/
def froot (H : Fam F Fp g a b s C B N0) : RExpr := ⟨fun n => qD (fbr g a b n).1, fam_cauchy H⟩
end


section
open VR VR.Numbers ZPoly ZIv ZRealCF ZExp ZRealExp ZRoot ZRootP ZRootPVR
variable {F : Nat → RExpr → RExpr} {Fp : RExpr → RExpr} {g : Nat → QExpr → QExpr} {a b : D} {s C B N0 : Nat}

theorem froot_in (H : Fam F Fp g a b s C B N0) : rle (dv rOH a) (froot H) ∧ rle (froot H) (dv rOH b) := by
  have hab := dle_sound rOH H.hab
  refine ⟨rle_of_eventually 0 (fun n _ => ?_), rle_of_eventually 0 (fun n _ => ?_)⟩
  · have h0 : qle (qD a) (qD (fbr g a b n).1) := const_le (fun i => dv_seq _ i) (fun i => dv_seq _ i) (bisD_in rCF (g n) a b hab n).1
    have e := dv_seq a n
    change qle ((dv rOH a).seq n) (qD (fbr g a b n).1); rat_linarith
  · obtain ⟨o, _⟩ := bisD_ord rCF (g n) a b hab n
    have h0 : qle (qD (fbr g a b n).1) (qD b) := const_le (fun i => dv_seq _ i) (fun i => dv_seq _ i) (rle_trans o (bisD_in rCF (g n) a b hab n).2)
    have e := dv_seq b n
    change qle (qD (fbr g a b n).1) ((dv rOH b).seq n); rat_linarith

/-- **THE ROOT.** -/
theorem froot_is_root (H : Fam F Fp g a b s C B N0) : rEq (Fp (froot H)) rzero := by
  have xin := froot_in H
  apply rCF.ap_tight
  intro hap
  have mk : ∀ J : Nat, ∃ n, N0 ≤ n ∧
      (∀ t : D, rle (dv rOH a) (dv rOH t) → rle (dv rOH t) (dv rOH b) →
        ZKron.Bd rCF.toOH (radd (F n (dv rOH t)) (rneg (rofQ (g n (qD t))))) (hp rOH ((J + 2) + C))) ∧
      ZKron.Bd rCF.toOH (radd (F n (froot H)) (rneg (Fp (froot H)))) (hp rOH ((J + 2) + C)) ∧
      ZKron.Bd rCF.toOH (radd (froot H) (rneg (dv rOH (fbr g a b n).1))) (hp rOH ((J + 2) + C)) ∧
      rle (radd (dv rOH (fbr g a b n).2) (rneg (dv rOH (fbr g a b n).1))) (hp rOH ((J + 2) + C)) := by
    intro J
    let j := (J + 2) + C
    obtain ⟨N1, h1⟩ := H.orac j
    obtain ⟨N2, h2⟩ := H.conv j
    obtain ⟨N3, h3⟩ := approx_close (froot H) j
    let n := N0 + N1 + N2 + N3 + (j + B)
    have hn0 : N0 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N0 N1) (Nat.le_add_right _ N2)) (Nat.le_add_right _ N3)) (Nat.le_add_right _ _)
    have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N1 N0) (Nat.le_add_right _ N2)) (Nat.le_add_right _ N3)) (Nat.le_add_right _ _)
    have hn2 : N2 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 (N0 + N1)) (Nat.le_add_right _ N3)) (Nat.le_add_right _ _)
    have hn3 : N3 ≤ n := Nat.le_trans (Nat.le_add_left N3 (N0 + N1 + N2)) (Nat.le_add_right _ _)
    refine ⟨n, hn0, h1 n hn1, h2 n hn2 _ xin.1 xin.2,
      ZKron.bd_congr rCF.toOH (radd_respects (rEq_refl _) (rneg_respects (rEq_symm (dv_rofQ _)))) (rEq_refl _) (h3 n hn3), ?_⟩
    have hab := dle_sound rOH H.hab
    have hW : rle (radd (dv rOH b) (rneg (dv rOH a))) (nI rOH (2 ^ B)) :=
      rCF.le_respects (rEq_trans (dv_add rOH _ _) (radd_respects (rEq_refl _) (dv_neg rOH _))) (dv_nat rCF _) (dle_sound rOH H.wid)
    have hw := (bisD_ord rCF (g n) a b hab n).2
    have e : hp rCF.toOH n = hp rCF.toOH ((j + B) + (N0 + N1 + N2 + N3)) := by
      congr 1; show N0 + N1 + N2 + N3 + (j + B) = j + B + (N0 + N1 + N2 + N3); exact Nat.add_comm _ _
    rw [e] at hw
    exact rCF.le_respects (rEq_symm hw) (rEq_refl _) (wid_small rCF hW)
  have hL0 := nI_nonneg rOH (2 ^ C)
  cases hap with
  | inl hpos =>
      obtain ⟨J0, hJ0⟩ := ZRootVR.vr_complete.arch hpos
      obtain ⟨n, hn, ho, hc, hx, _⟩ := mk (J0 + 1)
      obtain ⟨⟨t1, t2⟩, _⟩ := fbr_in H n
      have md := mono_bd rCF (H.mono n hn) (hp_nonneg rOH s) hL0 ⟨t1, t2⟩ xin hx
      have inv := (fam_inv H hn ho n).1
      have he := hp_anti rCF (J0 + 1 + 2) C
      have hM : rle (rmul (nI rOH (2 ^ C)) (hp rOH ((J0 + 1 + 2) + C))) (radd (hp rOH (J0 + 1 + 2)) (hp rOH (J0 + 1 + 2))) :=
        rCF.le_respects (rEq_symm (pow_hp rCF (J0 + 1) C)) (rEq_refl _) (le_twice rCF (hp_nonneg rOH _))
      have fin := fam_fin rCF (conv_lo rCF hc) md.2 inv he hM
      exact contra_hp rCF hJ0 fin
  | inr hneg =>
      obtain ⟨J0, hJ0⟩ := ZRootVR.vr_complete.arch hneg
      obtain ⟨n, hn, ho, hc, hx, hw⟩ := mk (J0 + 1)
      obtain ⟨⟨t1, t2⟩, ⟨u1, u2⟩⟩ := fbr_in H n
      have o := (bisD_ord rCF (g n) a b (dle_sound rOH H.hab) n).1
      have hw0 : rle rzero (radd (dv rOH (fbr g a b n).2) (rneg (dv rOH (fbr g a b n).1))) := OCR.sub_nonneg_of_le rCF.toOCR o
      have hxh := bd_shift rCF hx hw0 hw
      have md := mono_bd rCF (H.mono n hn) (hp_nonneg rOH s) hL0 ⟨u1, u2⟩ xin hxh
      have inv := (fam_inv H hn ho n).2
      have he := hp_anti rCF (J0 + 1 + 2) C
      have hM : rle (rmul (nI rOH (2 ^ C)) (radd (hp rOH ((J0 + 1 + 2) + C)) (hp rOH ((J0 + 1 + 2) + C))))
          (radd (hp rOH (J0 + 1 + 2)) (hp rOH (J0 + 1 + 2))) := by
        have p1 := pow_hp rCF (J0 + 1) C
        exact rCF.le_respects (rEq_symm (rEq_trans (mul_two_add rCF _ _) (radd_respects p1 p1))) (rEq_refl _) (rle_refl _)
      have fin := fam_fin rCF (conv_hi rCF hc) (neg_sub_le rCF md.1) (neg_up rCF inv) he hM
      exact contra_hp' rCF hJ0 fin

theorem froot_unique (H : Fam F Fp g a b s C B N0) {u v : RExpr}
    (hu : rle (dv rOH a) u ∧ rle u (dv rOH b)) (hv : rle (dv rOH a) v ∧ rle v (dv rOH b))
    (ru : rEq (Fp u) rzero) (rv : rEq (Fp v) rzero) : rEq u v :=
  rle_antisymm (mono_unique rCF H.monoP (ZNone.pos_hp rCF s) hu hv ru rv) (mono_unique rCF H.monoP (ZNone.pos_hp rCF s) hv hu rv ru)
end

end ZRootAbs

#print axioms ZRootAbs.froot_is_root
#print axioms ZRootAbs.froot_unique

#print axioms ZRootAbs.fam_cauchy

#print axioms ZRootAbs.fam_inv

#print axioms ZRootAbs.mono_bd
#print axioms ZRootAbs.bracket_ord
