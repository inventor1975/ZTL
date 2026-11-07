import ZNumBin
/-!
# ZField — what `check_none` needs of the continuum, constructively, and the two covers. Zero axioms.

Module 2 of the Lean-checked `check_none` (curator, 2026-11-07: "Б"). The claim "no point of the box solves
the system" is stated over an abstract structure `CF`: VR's ordered ring with a half (`ZNumBin.OH`) plus
STRICT POSITIVITY `pos` and the laws of a constructive ordered field (Bridges' axioms, the ones used):
apartness `ap x := pos x ∨ pos (−x)` splits over sums and products, an apart element has an inverse, and
COTRANSITIVITY replaces the undecidable `x ≤ t ∨ t ≤ x`: if `a < b`, every `x` has `x ≤ b` or `a ≤ x`.
Nothing decides `≤` on the target. VR's operational reals and Mathlib's ℝ are meant as instances.

What is proved here, from the laws alone:
  * `split_cover` — a coordinate in `[lo, hi]` lies in `[lo, t + δ]` or in `[t − δ, hi]` (δ > 0): the cut
                    the kernel's bisection uses, with overlap — the constructive price of a cut;
  * `chart_cover` — a point near a centre `(a, b)` and APART from it is `(a + r, b + r·s)` or `(a + r·s, b + r)`
                    with `|r| ≤ ρ` and `−2 ≤ s ≤ 2`: the two blow-up charts cover, with no `≤`-decision.
-/

namespace ZField
open VR.CSR ZNumBin

/-- A constructive ordered field (the laws `check_none` uses) over VR's ordered ring with a half. -/
structure CF (α : Type) extends OH α where
  pos : α → Prop
  pos_congr : ∀ {a b}, r a b → pos a → pos b
  pos_nonneg : ∀ {a}, pos a → le zero a
  pos_not_le : ∀ {a}, pos a → le a zero → False
  pos_mono : ∀ {a b}, pos a → le a b → pos b
  pos_mul : ∀ {a b}, pos a → pos b → pos (mul a b)
  pos_half : pos half
  ap_add : ∀ {a b}, (pos (add a b) ∨ pos (neg (add a b))) → (pos a ∨ pos (neg a)) ∨ (pos b ∨ pos (neg b))
  ap_mul : ∀ {a b}, (pos (mul a b) ∨ pos (neg (mul a b))) → (pos a ∨ pos (neg a))
  inv : ∀ {a}, (pos a ∨ pos (neg a)) → ∃ b, r (mul a b) one
  cotrans : ∀ {a b}, pos (add b (neg a)) → ∀ x, le x b ∨ le a x
  le_of_not_pos : ∀ {a b}, ¬ pos (add a (neg b)) → le a b
  ap_tight : ∀ {a}, ¬ (pos a ∨ pos (neg a)) → r a zero

variable {α : Type} (S : CF α)

/-- Apartness from zero. -/
def ap (x : α) : Prop := S.pos x ∨ S.pos (S.neg x)

theorem ap_ne {x : α} (h : ap S x) (e : S.r x S.zero) : False := by
  cases h with
  | inl p => exact S.pos_not_le p (S.le_respects (S.refl _) e (S.le_refl x))
  | inr p =>
      have e' : S.r (S.neg x) S.zero := S.trans (S.neg_congr e) S.neg_zero
      exact S.pos_not_le p (S.le_respects (S.refl _) e' (S.le_refl _))

theorem pos_add {a b : α} (ha : S.pos a) (hb : S.pos b) : S.pos (S.add a b) := by
  have h0 := S.pos_nonneg hb
  exact S.pos_mono ha (by cr_linarith S.toOCR [h0])

theorem pos_one : S.pos S.one :=
  S.pos_congr S.half_spec (pos_add S S.pos_half S.pos_half)

/-- A square of an apart element is positive. -/
theorem sq_pos {x : α} (h : ap S x) : S.pos (S.mul x x) := by
  cases h with
  | inl p => exact S.pos_mul p p
  | inr p => exact S.pos_congr (by cr_ring S.toCR) (S.pos_mul p p)

theorem sq_nonneg (x : α) : S.le S.zero (S.mul x x) := by
  apply S.le_of_not_pos
  intro hp
  have hp' : S.pos (S.neg (S.mul x x)) := S.pos_congr (by cr_ring S.toCR) hp
  have hx : ap S x := S.ap_mul (Or.inr hp')
  have hs := sq_pos S hx
  have h2 := pos_add S hs hp'
  have e : S.r S.zero (S.add (S.mul x x) (S.neg (S.mul x x))) := by cr_ring S.toCR
  exact S.pos_not_le h2 (S.le_respects e (S.refl _) (S.le_refl S.zero))

/-- THE NEGATIVE CASE SPLIT. A proof of `False` may split on ANY proposition: `P → False` is `¬P`, and then
`¬P → False` gives `False`. Every soundness proof of `check_none` ends in `False` (a solution contradicted),
so sign cases are free there, although `≤` is not decided. -/
theorem nn_case (P : Prop) (k1 : P → False) (k2 : ¬ P → False) : False := k2 k1

/-- Inside a proof of `False`, a sign: `x ≥ 0` or `x ≤ 0`. -/
theorem sign_case (x : α) (k1 : S.le S.zero x → False) (k2 : S.le x S.zero → False) : False :=
  nn_case (S.pos x) (fun h => k1 (S.pos_nonneg h))
    (fun h => k2 (S.le_of_not_pos (fun h' => h (S.pos_congr (by cr_ring S.toCR) h'))))

/-! ## The cut, with overlap -/

/-- `x ∈ [lo, hi]` lies in `[lo, t + δ]` or in `[t − δ, hi]` when `δ > 0` — no `≤`-decision. -/
theorem split_cover {lo hi t δ x : α} (hδ : S.pos δ) (h1 : S.le lo x) (h2 : S.le x hi) :
    (S.le lo x ∧ S.le x (S.add t δ)) ∨ (S.le (S.add t (S.neg δ)) x ∧ S.le x hi) := by
  have g : S.pos (S.add (S.add t δ) (S.neg (S.add t (S.neg δ)))) :=
    S.pos_congr (by cr_ring S.toCR) (pos_add S hδ hδ)
  cases S.cotrans g x with
  | inl h => exact Or.inl ⟨h1, h⟩
  | inr h => exact Or.inr ⟨h, h2⟩

/-! ## The two charts cover a neighbourhood of a centre, constructively -/

/-- Four times: `u + (u + (u + u))`. -/
def four (u : α) : α := S.add u (S.add u (S.add u u))

theorem ap_of_four {u : α} (h : ap S (four S u)) : ap S u := by
  rcases S.ap_add h with h1 | h1
  · exact h1
  rcases S.ap_add h1 with h2 | h2
  · exact h2
  rcases S.ap_add h2 with h3 | h3
  · exact h3
  · exact h3

theorem pos_four_one : S.pos (four S S.one) := by
  have p := pos_one S
  exact pos_add S p (pos_add S p (pos_add S p p))

/-- With `d·i = 1`: `(e·i)·(e·i)·(d·d) = e·e`. -/
theorem sq_ratio {d e i : α} (hi : S.r (S.mul d i) S.one) :
    S.r (S.mul (S.mul (S.mul e i) (S.mul e i)) (S.mul d d)) (S.mul e e) := by
  have e1 : S.r (S.mul (S.mul (S.mul e i) (S.mul e i)) (S.mul d d))
      (S.mul (S.mul e e) (S.mul (S.mul d i) (S.mul d i))) := by cr_ring S.toCR
  exact S.trans e1 (S.trans (S.mul_congr (S.refl _) (S.mul_congr hi hi)) (by cr_ring S.toCR))

/-- `s² · u = v`, `v ≤ 3u` (or `≤ u`), `u > 0`: then `−2 ≤ s ≤ 2`. -/
theorem s_bound {s u v : α} (hu : S.pos u) (hsv : S.r (S.mul (S.mul s s) u) v)
    (hv : S.le v (S.add u (S.add u u))) :
    S.le (S.neg (S.add S.one S.one)) s ∧ S.le s (S.add S.one S.one) := by
  have hu0 := S.pos_nonneg hu
  have p4 := pos_four_one S
  have key : ∀ t : α, S.pos t → S.pos (S.add t (four S S.one)) →
      S.r (S.mul (S.mul t (S.add t (four S S.one))) u) (S.add v (S.neg (four S u))) → False := by
    intro t ht ht4 e
    have pp := S.pos_congr e (S.pos_mul (S.pos_mul ht ht4) hu)
    exact S.pos_not_le pp (by unfold four; cr_linarith S.toOCR [hv, hu0])
  constructor
  · apply S.le_of_not_pos
    intro hp
    refine key _ hp (pos_add S hp p4) ?_
    refine S.trans ?_ (S.add_congr hsv (S.refl _))
    unfold four; cr_ring S.toCR
  · apply S.le_of_not_pos
    intro hp
    refine key _ hp (pos_add S hp p4) ?_
    refine S.trans ?_ (S.add_congr hsv (S.refl _))
    unfold four; cr_ring S.toCR

/-- THE CHART COVER. A point within `ρ` of the centre `(a, b)` and apart from it lies in the X chart
`(a + r, b + r·s)` or the Y chart `(a + r·s, b + r)`, `|r| ≤ ρ`, `|s| ≤ 2` — decided by cotransitivity on
`4·dy²` against `2·w` and `3·w`, `w = dx² + dy² > 0`, never by `≤`. -/
theorem chart_cover {x y a b ρ : α}
    (hx1 : S.le (S.add a (S.neg ρ)) x) (hx2 : S.le x (S.add a ρ))
    (hy1 : S.le (S.add b (S.neg ρ)) y) (hy2 : S.le y (S.add b ρ))
    (hap : ap S (S.add x (S.neg a)) ∨ ap S (S.add y (S.neg b))) :
    (∃ r s, ap S r ∧ S.le (S.neg ρ) r ∧ S.le r ρ ∧ S.le (S.neg (S.add S.one S.one)) s ∧
        S.le s (S.add S.one S.one) ∧ S.r x (S.add a r) ∧ S.r y (S.add b (S.mul r s))) ∨
    (∃ r s, ap S r ∧ S.le (S.neg ρ) r ∧ S.le r ρ ∧ S.le (S.neg (S.add S.one S.one)) s ∧
        S.le s (S.add S.one S.one) ∧ S.r x (S.add a (S.mul r s)) ∧ S.r y (S.add b r)) := by
  have hu0 := sq_nonneg S (S.add x (S.neg a))
  have hv0 := sq_nonneg S (S.add y (S.neg b))
  -- w > 0
  have hw : S.pos (S.add (S.mul (S.add x (S.neg a)) (S.add x (S.neg a))) (S.mul (S.add y (S.neg b)) (S.add y (S.neg b)))) := by
    cases hap with
    | inl h => exact S.pos_mono (sq_pos S h) (by cr_linarith S.toOCR [hv0])
    | inr h => exact S.pos_mono (sq_pos S h) (by cr_linarith S.toOCR [hu0])
  have g : S.pos (S.add (S.add (S.add (S.add (S.mul (S.add x (S.neg a)) (S.add x (S.neg a))) (S.mul (S.add y (S.neg b)) (S.add y (S.neg b))))
        (S.add (S.mul (S.add x (S.neg a)) (S.add x (S.neg a))) (S.mul (S.add y (S.neg b)) (S.add y (S.neg b)))))
        (S.add (S.mul (S.add x (S.neg a)) (S.add x (S.neg a))) (S.mul (S.add y (S.neg b)) (S.add y (S.neg b)))))
      (S.neg (S.add (S.add (S.mul (S.add x (S.neg a)) (S.add x (S.neg a))) (S.mul (S.add y (S.neg b)) (S.add y (S.neg b))))
        (S.add (S.mul (S.add x (S.neg a)) (S.add x (S.neg a))) (S.mul (S.add y (S.neg b)) (S.add y (S.neg b))))))) :=
    S.pos_congr (by cr_ring S.toCR) hw
  cases S.cotrans g (four S (S.mul (S.add y (S.neg b)) (S.add y (S.neg b)))) with
  | inl h =>
      -- 4v ≤ 3w: v ≤ 3u and 4u ≥ w > 0
      have h4 : S.pos (four S (S.mul (S.add x (S.neg a)) (S.add x (S.neg a)))) :=
        S.pos_mono hw (by unfold four at h ⊢; cr_linarith S.toOCR [h])
      have hdx : ap S (S.add x (S.neg a)) := S.ap_mul (ap_of_four S (Or.inl h4))
      have hu := sq_pos S hdx
      obtain ⟨i, hi⟩ := S.inv hdx
      left
      refine ⟨S.add x (S.neg a), S.mul (S.add y (S.neg b)) i, hdx, by cr_linarith S.toOCR [hx1], by cr_linarith S.toOCR [hx2], ?_⟩
      have sb := s_bound S hu (sq_ratio S (e := S.add y (S.neg b)) hi) (by unfold four at h; cr_linarith S.toOCR [h])
      refine ⟨sb.1, sb.2, by cr_ring S.toCR, ?_⟩
      have e1 : S.r (S.add b (S.mul (S.add x (S.neg a)) (S.mul (S.add y (S.neg b)) i)))
          (S.add b (S.mul (S.add y (S.neg b)) (S.mul (S.add x (S.neg a)) i))) := by cr_ring S.toCR
      refine S.symm (S.trans e1 (S.trans (S.add_congr (S.refl _) (S.mul_congr (S.refl _) hi)) (by cr_ring S.toCR)))
  | inr h =>
      -- 2w ≤ 4v: u ≤ v and 4v ≥ 2w > 0
      have h4 : S.pos (four S (S.mul (S.add y (S.neg b)) (S.add y (S.neg b)))) :=
        S.pos_mono hw (by unfold four at h ⊢; cr_linarith S.toOCR [h, hu0, hv0])
      have hdy : ap S (S.add y (S.neg b)) := S.ap_mul (ap_of_four S (Or.inl h4))
      have hv := sq_pos S hdy
      obtain ⟨j, hj⟩ := S.inv hdy
      right
      refine ⟨S.add y (S.neg b), S.mul (S.add x (S.neg a)) j, hdy, by cr_linarith S.toOCR [hy1], by cr_linarith S.toOCR [hy2], ?_⟩
      have sb := s_bound S hv (sq_ratio S (e := S.add x (S.neg a)) hj) (by unfold four at h; cr_linarith S.toOCR [h, hv0])
      refine ⟨sb.1, sb.2, ?_, by cr_ring S.toCR⟩
      have e1 : S.r (S.add a (S.mul (S.add y (S.neg b)) (S.mul (S.add x (S.neg a)) j)))
          (S.add a (S.mul (S.add x (S.neg a)) (S.mul (S.add y (S.neg b)) j))) := by cr_ring S.toCR
      refine S.symm (S.trans e1 (S.trans (S.add_congr (S.refl _) (S.mul_congr (S.refl _) hj)) (by cr_ring S.toCR)))

end ZField

#print axioms ZField.ap_ne
#print axioms ZField.pos_add
#print axioms ZField.pos_one
#print axioms ZField.sq_pos
#print axioms ZField.sq_nonneg
#print axioms ZField.split_cover
#print axioms ZField.ap_of_four
#print axioms ZField.sq_ratio
#print axioms ZField.s_bound
#print axioms ZField.chart_cover
#print axioms ZField.nn_case
#print axioms ZField.sign_case
