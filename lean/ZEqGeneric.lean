/-
  ZEqGeneric.lean — E31c: the POSITIVE half of zero-trust identity, for an
  ARBITRARY domain instead of the five named individuals.

  WHAT THIS CLOSES. ZEq, ZIndisc and ZFreeUI all live on `Indiv`, five
  individuals, and every proof there is `by decide` — exhaustion. For the
  NEGATIVE results that is already enough: refuting a law needs one
  countermodel, and a countermodel is what those files build. The positive
  results are the ones that were only checked, never proved:

      an earned equality is genuine identity
      substitution through an earned equality is congruence
      equality is never earned through a mark
      indiscernibility forces identity among grounded references

  Here they are proved for ANY type with decidable equality and ANY choice of
  which references are marked. No enumeration: the domain is a variable.

  WHY IT GOES THROUGH AT ALL. Because zero-trust identity is not a relation
  invented on top of a domain — it is the SAME rule at every point: if either
  side is unverified the verdict is Z, otherwise it is decided by the
  underlying equality. Nothing in that rule counts individuals. The five-point
  version was never a special case; it was a witness that the rule is
  consistent.

  WHAT IS STILL NOT HERE. The failures — indiscernibles that are not
  identical, classical instantiation collapsing — are properties of a domain
  that HAS marks. Stated over an arbitrary domain they are false: a domain
  with no marked reference is a classical one, and there the laws hold. So
  those keep living in the witness files, which is where a countermodel
  belongs. This file is the half that generalises; the other half is the half
  that must not.
-/
import ZTL

namespace ZEqGeneric

open V

variable {α : Type} [DecidableEq α]

/-- Zero-trust identity over an arbitrary domain: `marked` says which
references are unverified, and the verdict is Z wherever either side is. The
rule is pointwise — it never looks at the domain as a whole. -/
def eqG (marked : α → Bool) (a b : α) : V :=
  match marked a || marked b, a == b with
  | true,  _     => Z
  | false, true  => T
  | false, false => F

/-! ### An earned equality is genuine identity

    ФОРМА ОПРЕДЕЛЕНИЯ ВЫБРАНА ПОД ПУСТОЙ СПИСОК АКСИОМ. Первая редакция шла
    через `if … then` и доказывалась `simp`/`by_cases`: собралась, и
    `#print axioms` показал `propext` у всех шести теорем. Правило дома —
    propext лечим ДО пустого списка, а не объявляем приемлемым.

    Поэтому решение принято не в тактике, а в определении: развилка идёт по
    ДВУМ БУЛЕВЫМ значениям через `match`, а не по пропозиции через `ite`.
    Тогда каждый случай редуцируется вычислением, и доказательства состоят из
    `cases` и `rfl` — сводить равенство пропозиций попросту негде. -/

/-- If the verdict is T, the two references really are the same object. -/
theorem eq_forces_same (marked : α → Bool) (a b : α) :
    eqG marked a b = T → a = b := by
  unfold eqG
  cases hm : (marked a || marked b) <;> cases hb : (a == b) <;>
    intro h <;> first
      | exact eq_of_beq hb
      | cases h

/-- Leibniz substitution is congruence — salva veritate. -/
theorem leibniz_congr (marked : α → Bool) (f : α → V) (a b : α)
    (h : eqG marked a b = T) : f a = f b :=
  congrArg f (eq_forces_same marked a b h)

/-- Equality is never earned through a mark: no laundering. -/
theorem no_laundering (marked : α → Bool) (a b : α)
    (h : marked a = true ∨ marked b = true) : eqG marked a b ≠ T := by
  unfold eqG
  have hm : (marked a || marked b) = true := by
    cases h with
    | inl ha => rw [ha]; rfl
    | inr hb => rw [hb, Bool.or_true]
  rw [hm]
  cases (a == b) <;> intro hz <;> cases hz

/-- Reflexivity is EARNED, not free: it holds exactly where the reference is
verified. Both directions, so this is the whole story and not half of it. -/
theorem refl_iff_grounded (marked : α → Bool) (a : α) :
    eqG marked a a = T ↔ marked a = false := by
  unfold eqG
  cases hm : marked a with
  | true =>
      rw [Bool.or_self]
      constructor
      · intro hz
        cases hz
      · intro hf
        cases hf
  | false =>
      rw [Bool.or_self]
      have hb : (a == a) = true := beq_self_eq_true a
      rw [hb]
      exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- On a marked reference self-identity is Z — on credit, not false. -/
theorem refl_marked (marked : α → Bool) (a : α) (h : marked a = true) :
    eqG marked a a = Z := by
  unfold eqG
  rw [h, Bool.or_self]

/-! ### Indiscernibility forces identity among grounded references -/

/-- Among verified references, agreeing on every predicate forces an earned
identity — provided the family separates points, which is what the hypothesis
says. This is the generic form of `holds_on_grounded`. -/
theorem indiscernible_grounded_identical
    (marked : α → Bool) (P : α → α → V)
    (sep : ∀ x y : α, marked x = false → marked y = false → P x x = P x y → x = y)
    (a b : α) (ha : marked a = false) (hb : marked b = false)
    (h : P a a = P a b) : eqG marked a b = T := by
  have hab : a = b := sep a b ha hb h
  unfold eqG
  rw [ha, hb, Bool.or_self, hab]
  rw [beq_self_eq_true b]

end ZEqGeneric
