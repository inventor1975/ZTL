import VR.Meta.CSRNorm

/-!
# ZQuad — `znumsolve._parabola_pieces`: one unknown under a quadratic constraint. Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема» («токены есть, работаем»). The solver narrows
x by `q·x² + p·x + c ⋈ 0` from the discriminant `d = p² − 4qc`: for `q > 0` and `≤ 0` it keeps x BETWEEN the roots,
for `q < 0` OUTSIDE them, for `= 0` the roots themselves, each root enclosed by a rational clamp `s_lo ≤ √d ≤ s_hi`.
Until today the rule was measured (`test_quadratic.py`); `ZParabola` proved only the refutation by d < 0.

THE HEART, proved over VR's ordered commutative ring (`OCR`: no totality, no division — every instance qualifies, ℚ
among them), with `t = 2q·x + p`:
  `completed_square`  4q·(q·x² + p·x + c) + d = t²                     (the identity; VR's `cr_ring`)
  `quad_le_pos`       q ≥ 0 and q·x² + p·x + c ≤ 0  ⇒  t² ≤ d           (inside: |t| ≤ √d)
  `quad_le_neg`       q ≤ 0 and q·x² + p·x + c ≤ 0  ⇒  d ≤ t²           (outside: |t| ≥ √d)
  `quad_eq`           q·x² + p·x + c = 0            ⇒  t² = d           (on a root)
With the ORDER OF A FIELD as named laws (`TF`: totality, products of non-negatives, the square cancelling on the
non-negatives — all true in ℚ):
  `quad_piece_pos`    q ≥ 0, f(x) ≤ 0, a clamp s ≥ 0 with d ≤ s²  ⇒  −s ≤ 2q·x + p ≤ s   (the piece, before ÷ 2q)
  `qsqrt_sign_pos`    `znum.QSqrt.sign`'s opposite-sign case: q²·d ≤ p² ⇒ 0 ≤ p + q·√d
Dividing by 2q is exact rational arithmetic the solver runs. The stand `inventory/zquad_bridge.py` checks that the
code's pieces are exactly these intervals and that the clamp `_rat_sqrt` holds where it is used.
-/

namespace ZQuad
open VR.CSR

variable {α : Type} (S : OCR α)

/-- 2 and 4, written as sums of one (so that the ring normaliser reads them as numbers, not as atoms). -/
def two : α := S.add S.one S.one
def four : α := S.add (two S) (two S)

theorem four_nonneg : S.le S.zero (four S) :=
  OCR.nonneg_add S (OCR.nonneg_add S S.zero_le_one S.zero_le_one) (OCR.nonneg_add S S.zero_le_one S.zero_le_one)

/-- The quadratic form, the discriminant, the half-derivative t = 2q·x + p. -/
def form (q p c x : α) : α := S.add (S.add (S.mul q (S.mul x x)) (S.mul p x)) c
def disc (q p c : α) : α := S.add (S.mul p p) (S.neg (S.mul (four S) (S.mul q c)))
def tee (q p x : α) : α := S.add (S.mul (two S) (S.mul q x)) p

/-- THE IDENTITY: 4q·f(x) + d = (2qx + p)². -/
theorem completed_square (q p c x : α) :
    S.r (S.add (S.mul (four S) (S.mul q (form S q p c x))) (disc S q p c)) (S.mul (tee S q p x) (tee S q p x)) := by
  unfold form disc tee four two
  cr_ring S.toCR

/-- q ≥ 0, f ≤ 0 ⇒ 4q·f ≤ 0. -/
theorem four_q_f_nonpos (mul_nonneg : ∀ {a b : α}, S.le S.zero a → S.le S.zero b → S.le S.zero (S.mul a b))
    (q f : α) (hq : S.le S.zero q) (hf : S.le f S.zero) : S.le (S.mul (four S) (S.mul q f)) S.zero := by
  have hnf : S.le S.zero (S.neg f) := by
    have := S.le_add_right (S.neg f) hf
    exact S.le_respects (S.add_neg f) (S.zero_add _) this
  have h4 : S.le S.zero (four S) := four_nonneg S
  have hp : S.le S.zero (S.mul (four S) (S.mul q (S.neg f))) := mul_nonneg h4 (mul_nonneg hq hnf)
  -- 4q·(−f) = −(4q·f), so 0 ≤ −(4q·f), so 4q·f ≤ 0
  have e : S.r (S.mul (four S) (S.mul q (S.neg f))) (S.neg (S.mul (four S) (S.mul q f))) := by
    unfold four two; cr_ring S.toCR
  have h2 : S.le S.zero (S.neg (S.mul (four S) (S.mul q f))) := S.le_respects (S.refl _) e hp
  have h3 := S.le_add_right (S.mul (four S) (S.mul q f)) h2
  refine S.le_respects ?_ ?_ h3
  · exact S.zero_add _
  · cr_ring S.toCR

/-- q ≤ 0, f ≤ 0 ⇒ 0 ≤ 4q·f. -/
theorem four_q_f_nonneg (mul_nonneg : ∀ {a b : α}, S.le S.zero a → S.le S.zero b → S.le S.zero (S.mul a b))
    (q f : α) (hq : S.le q S.zero) (hf : S.le f S.zero) : S.le S.zero (S.mul (four S) (S.mul q f)) := by
  have neg0 : ∀ {y : α}, S.le y S.zero → S.le S.zero (S.neg y) := fun {y} hy =>
    S.le_respects (S.add_neg y) (S.zero_add _) (S.le_add_right (S.neg y) hy)
  have hp := mul_nonneg (four_nonneg S) (mul_nonneg (neg0 hq) (neg0 hf))
  refine S.le_respects (S.refl _) ?_ hp
  unfold four two; cr_ring S.toCR

/-- a + b ≤ b when a ≤ 0, and b ≤ a + b when 0 ≤ a. -/
theorem add_le_self {a b : α} (h : S.le a S.zero) : S.le (S.add a b) b :=
  S.le_respects (S.refl _) (S.zero_add b) (S.le_add_right b h)
theorem self_le_add {a b : α} (h : S.le S.zero a) : S.le b (S.add a b) :=
  S.le_respects (S.zero_add b) (S.refl _) (S.le_add_right b h)

/-- INSIDE: q ≥ 0 and f(x) ≤ 0 ⇒ t² ≤ d. -/
theorem quad_le_pos (mul_nonneg : ∀ {a b : α}, S.le S.zero a → S.le S.zero b → S.le S.zero (S.mul a b))
    (q p c x : α) (hq : S.le S.zero q) (hf : S.le (form S q p c x) S.zero) :
    S.le (S.mul (tee S q p x) (tee S q p x)) (disc S q p c) :=
  S.le_respects (completed_square S q p c x) (S.refl _)
    (add_le_self S (four_q_f_nonpos S mul_nonneg q _ hq hf))

/-- OUTSIDE: q ≤ 0 and f(x) ≤ 0 ⇒ d ≤ t². -/
theorem quad_le_neg (mul_nonneg : ∀ {a b : α}, S.le S.zero a → S.le S.zero b → S.le S.zero (S.mul a b))
    (q p c x : α) (hq : S.le q S.zero) (hf : S.le (form S q p c x) S.zero) :
    S.le (disc S q p c) (S.mul (tee S q p x) (tee S q p x)) :=
  S.le_respects (S.refl _) (completed_square S q p c x)
    (self_le_add S (four_q_f_nonneg S mul_nonneg q _ hq hf))

/-- ON A ROOT: f(x) = 0 ⇒ t² = d. -/
theorem quad_eq (q p c x : α) (hf : S.r (form S q p c x) S.zero) :
    S.r (S.mul (tee S q p x) (tee S q p x)) (disc S q p c) := by
  have e := completed_square S q p c x
  refine S.trans (S.symm e) ?_
  have h0 : S.r (S.mul (four S) (S.mul q (form S q p c x))) S.zero :=
    S.trans (S.mul_congr (S.refl _) (S.mul_congr (S.refl _) hf))
      (S.trans (S.mul_congr (S.refl _) (CSR.mul_zero S.toCSR q)) (CSR.mul_zero S.toCSR _))
  exact S.trans (S.add_congr h0 (S.refl _)) (S.zero_add _)

/-! ## With the order of a field: the intervals themselves

`TF` adds to `OCR` the two facts of ℚ's order this step uses, as LAWS (named, not hidden): the product of
non-negatives is non-negative, and the SQUARE CANCELS on the non-negatives (0 ≤ t, 0 ≤ s, t² ≤ s² ⇒ t ≤ s) —
true in every ordered field; plus totality of ≤ (ℚ decides it). -/
structure TF (α : Type) extends OCR α where
  le_total : ∀ a b, le a b ∨ le b a
  mul_nonneg : ∀ {a b : α}, le zero a → le zero b → le zero (mul a b)
  sq_cancel : ∀ {t s : α}, le zero t → le zero s → le (mul t t) (mul s s) → le t s

variable (T : TF α)

theorem neg_nonneg_of_nonpos {y : α} (h : T.le y T.zero) : T.le T.zero (T.neg y) :=
  T.le_respects (T.add_neg y) (T.zero_add _) (T.le_add_right (T.neg y) h)

theorem nonpos_of_neg_nonneg {y : α} (h : T.le T.zero (T.neg y)) : T.le y T.zero := by
  have h2 := T.le_add_right y h
  refine T.le_respects (T.zero_add y) ?_ h2
  cr_ring T.toCR

/-- |t| ≤ s from t² ≤ s², s ≥ 0: −s ≤ t ≤ s. -/
theorem abs_le_of_sq_le {t s : α} (hs : T.le T.zero s) (h : T.le (T.mul t t) (T.mul s s)) :
    T.le (T.neg s) t ∧ T.le t s := by
  have hns : T.le (T.neg s) T.zero := nonpos_of_neg_nonneg T (T.le_respects (T.refl _) (T.symm (T.neg_neg s)) hs)
  cases T.le_total T.zero t with
  | inl ht => exact ⟨T.le_trans hns ht, T.sq_cancel ht hs h⟩
  | inr ht =>
      have hnt := neg_nonneg_of_nonpos T ht
      have hsq : T.le (T.mul (T.neg t) (T.neg t)) (T.mul s s) :=
        T.le_respects (by cr_ring T.toCR) (T.refl _) h
      have hle := T.sq_cancel hnt hs hsq          -- −t ≤ s
      have h3 := T.le_add_right (T.add t (T.neg s)) hle
      refine ⟨T.le_respects ?_ ?_ h3, T.le_trans ht hs⟩
      · cr_ring T.toCR
      · cr_ring T.toCR

/-- **THE PIECE (inside).** q ≥ 0, f(x) ≤ 0, and a clamp s ≥ 0 with d ≤ s²: −s ≤ 2q·x + p ≤ s. -/
theorem quad_piece_pos (q p c x s : α) (hq : T.le T.zero q) (hf : T.le (form T.toOCR q p c x) T.zero)
    (hs : T.le T.zero s) (hd : T.le (disc T.toOCR q p c) (T.mul s s)) :
    T.le (T.neg s) (tee T.toOCR q p x) ∧ T.le (tee T.toOCR q p x) s :=
  abs_le_of_sq_le T hs (T.le_trans (quad_le_pos T.toOCR T.mul_nonneg q p c x hq hf) hd)

/-- **THE SIGN OF p + q·√d** (`znum.QSqrt.sign`, opposite signs): p ≥ 0, q ≤ 0, s ≥ 0 with s² = d:
q²·d ≤ p² ⇒ 0 ≤ p + q·s. -/
theorem qsqrt_sign_pos (p q d s : α) (hp : T.le T.zero p) (hq : T.le q T.zero) (hs : T.le T.zero s)
    (hsd : T.r (T.mul s s) d) (h : T.le (T.mul (T.mul q q) d) (T.mul p p)) : T.le T.zero (T.add p (T.mul q s)) := by
  have hnq := neg_nonneg_of_nonpos T hq
  have hqs : T.le T.zero (T.mul (T.neg q) s) := T.mul_nonneg hnq hs
  have hsq : T.le (T.mul (T.mul (T.neg q) s) (T.mul (T.neg q) s)) (T.mul p p) := by
    refine T.le_respects ?_ (T.refl _) h
    exact T.trans (T.mul_congr (T.refl _) (T.symm hsd)) (by cr_ring T.toCR)
  have hle := T.sq_cancel hqs hp hsq            -- −q·s ≤ p
  have h3 := T.le_add_right (T.mul q s) hle
  refine T.le_respects ?_ (T.refl _) h3
  cr_ring T.toCR

end ZQuad

#print axioms ZQuad.four_nonneg
#print axioms ZQuad.completed_square
#print axioms ZQuad.four_q_f_nonpos
#print axioms ZQuad.four_q_f_nonneg
#print axioms ZQuad.add_le_self
#print axioms ZQuad.self_le_add
#print axioms ZQuad.quad_le_pos
#print axioms ZQuad.quad_le_neg
#print axioms ZQuad.quad_eq
#print axioms ZQuad.neg_nonneg_of_nonpos
#print axioms ZQuad.nonpos_of_neg_nonneg
#print axioms ZQuad.abs_le_of_sq_le
#print axioms ZQuad.quad_piece_pos
#print axioms ZQuad.qsqrt_sign_pos
