/-
  ZFreeUIGeneric.lean — E32c: the POSITIVE half of the FREE INSTANTIATION
  SCHEMA, for an ARBITRARY domain instead of the five named individuals.

  WHAT THIS CLOSES. After ZEqGeneric, §25's honest caveat named exactly one
  thing still proved by exhaustion: "the positive half of the instantiation
  schema". `ZFreeUI` proves it `by decide` over five individuals and ONE
  fixed predicate `everything`. Here it is proved for ANY type with decidable
  equality, ANY choice of which references are marked, ANY V-valued
  predicate, and ANY finite carrier the quantifier ranges over.

  WHY IT GOES THROUGH. The free repair never depended on the domain. It works
  because the existence premise E!t is UNEARNED exactly where the term is
  marked, so a conjunction containing it is not designated there; and where
  it IS earned, the term is grounded and the universal already covers it.
  Both halves are facts about the mark, not about how many individuals carry
  one. The five-point version was a witness that the repair is not vacuous —
  never a special case.

  WHAT STAYS A WITNESS, AND MUST. The FAILURE of classical UI is a
  countermodel. Stated over an arbitrary domain it is false: a domain with no
  marked reference is classical, and there the schema holds. `ZFreeUI` stays
  its home, exactly as ZEq and ZIndisc stay the home of the identity
  failures. This file is the half that generalises; the other half is the
  half that must not.

  ФОРМА ДОКАЗАТЕЛЬСТВ ВЫБРАНА ПОД ПУСТОЙ СПИСОК АКСИОМ, и цена измерена, а не
  угадана. Первая редакция собралась с первого раза и дала propext в пяти
  теоремах из восьми (одна ещё и Quot.sound). Бисекция нашла ДВА источника:

    (1) ядровая `List.all_eq_true` — propext + Quot.sound. Лечится своей
        структурной рекурсией `allG`: её развёртка идёт `rfl`.
    (2) ПОДСТАНОВОЧНЫЙ `_` в определении по индуктивному типу:
        `def isT : V → Bool | T => true | _ => false` тащит propext через
        порождённый матчер. Те же три ветви, выписанные ЯВНО, чисты.
        Проверено бисекцией, а не рассуждением.

  Отсюда правило файла: всякая развилка — по БУЛЕВУ значению, все ветви
  выписаны, а противоречие закрывается `Bool.noConfusion`/`V.noConfusion`,
  не тактикой `cases` по равенству. `#print axioms` стоит внизу.
-/
import ZEqGeneric

namespace ZFreeUIGeneric

open V
open ZEqGeneric

variable {α : Type}

/-- Is the verdict earned? All three branches explicit — see the header. -/
def isT : V → Bool
  | T => true
  | F => false
  | Z => false

theorem isT_true : ∀ v : V, isT v = true → v = T
  | T, _ => rfl
  | F, h => Bool.noConfusion h
  | Z, h => Bool.noConfusion h

/-- Existence over an arbitrary domain: earned self-identity — `ZDesc.Ebang`
with the marking as a parameter rather than a fixed table. -/
def EbangG [DecidableEq α] (marked : α → Bool) (t : α) : V := eqG marked t t

/-- What one element contributes to the universal: a marked element is not in
the range at all (quantification ranges over what exists), a grounded one must
deliver T. -/
def stepG (marked : α → Bool) (φ : α → V) (x : α) : Bool :=
  match marked x with
  | true  => true
  | false => isT (φ x)

/-- Own structural recursion, so that unfolding is `rfl` and no core list
lemma is needed — see the header, source (1). -/
def allG (marked : α → Bool) (φ : α → V) : List α → Bool
  | []      => true
  | x :: xs => stepG marked φ x && allG marked φ xs

/-- The universal read strictly, over the carrier the quantifier ranges over:
T only when every GROUNDED element of `dom` gives T. -/
def forallG (marked : α → Bool) (φ : α → V) (dom : List α) : V :=
  match allG marked φ dom with
  | true  => T
  | false => F

/-! ### The bridges the schema needs -/

/-- Existence is earned exactly on the unmarked — the generic form of
`ZDesc.grounded_exists`, inherited from ZEqGeneric rather than re-proved. -/
theorem ebangG_iff [DecidableEq α] (marked : α → Bool) (t : α) :
    EbangG marked t = T ↔ marked t = false :=
  refl_iff_grounded marked t

/-- A conjunction is earned only if both halves are. -/
theorem zand_T_left : ∀ x y : V, zand x y = T → x = T := by decide

theorem zand_T_right : ∀ x y : V, zand x y = T → y = T := by decide

/-- An earned universal really does hold of every element of its range. -/
theorem allG_mem (marked : α → Bool) (φ : α → V) :
    ∀ (l : List α), allG marked φ l = true → ∀ x, x ∈ l → stepG marked φ x = true
  | [],      _, _, hx => nomatch hx
  | y :: ys, h, x, hx => by
      unfold allG at h
      cases hy : stepG marked φ y with
      | false =>
          exact Bool.noConfusion (hy ▸ h : (false && allG marked φ ys) = true)
      | true  =>
          have hrest : allG marked φ ys = true :=
            (hy ▸ h : (true && allG marked φ ys) = true)
          cases hx with
          | head      => exact hy
          | tail _ h' => exact allG_mem marked φ ys hrest x h'

/-- T for the universal means the underlying test passed. -/
theorem forallG_T (marked : α → Bool) (φ : α → V) (dom : List α)
    (h : forallG marked φ dom = T) : allG marked φ dom = true := by
  unfold forallG at h
  cases hb : allG marked φ dom with
  | true  => rfl
  | false => rw [hb] at h; exact V.noConfusion h

/-- What `forallGrounded` asserted by a hand-written conjunction over
g0, g1, g2: an earned universal delivers every GROUNDED element of its range. -/
theorem forallG_delivers (marked : α → Bool) (φ : α → V) (dom : List α)
    (h : forallG marked φ dom = T) (x : α) (hx : x ∈ dom)
    (hg : marked x = false) : φ x = T := by
  have hs : stepG marked φ x = true :=
    allG_mem marked φ dom (forallG_T marked φ dom h) x hx
  unfold stepG at hs
  rw [hg] at hs
  exact isT_true (φ x) hs

/-! ### The free-logic repair, over an arbitrary domain -/

/-- THE SCHEMA. Wherever the premise `∀ᴳφ ∧ E!t` is earned, `φ(t)` is earned
too — for any domain, any marking, any predicate, any range. No individual
escapes it, and no finiteness of the DOMAIN is used: only finiteness of the
range the quantifier was read over. -/
theorem free_ui_valid_generic [DecidableEq α] (marked : α → Bool) (φ : α → V)
    (dom : List α) (t : α) (ht : t ∈ dom)
    (h : zand (forallG marked φ dom) (EbangG marked t) = T) : φ t = T :=
  forallG_delivers marked φ dom
    (zand_T_left _ _ h) t ht
    ((ebangG_iff marked t).mp (zand_T_right _ _ h))

/-- And it is valid FOR THE RIGHT REASON: on a marked term the premise is
never designated, so the schema licenses nothing there. The generic
`free_ui_premise_undesignated`. -/
theorem premise_undesignated_generic [DecidableEq α] (marked : α → Bool)
    (φ : α → V) (dom : List α) (t : α) (hm : marked t = true) :
    zand (forallG marked φ dom) (EbangG marked t) ≠ T := by
  intro h
  have hf : marked t = false := (ebangG_iff marked t).mp (zand_T_right _ _ h)
  exact Bool.noConfusion (hm.symm.trans hf)

/-- Nor is it vacuous: on a grounded term inside an earned universal the
premise IS earned, so the schema licenses something. -/
theorem not_vacuous_generic [DecidableEq α] (marked : α → Bool) (φ : α → V)
    (dom : List α) (t : α) (hg : marked t = false)
    (h : forallG marked φ dom = T) :
    zand (forallG marked φ dom) (EbangG marked t) = T := by
  have he : EbangG marked t = T := (ebangG_iff marked t).mpr hg
  rw [h, he]; rfl

/-- The empty range is not a loophole: with nothing to quantify over the
universal is vacuously earned, and the schema STILL refuses every marked
term. The refusal comes from the mark, not from the range being inhabited. -/
theorem empty_range_still_refuses [DecidableEq α] (marked : α → Bool)
    (φ : α → V) (t : α) (hm : marked t = true) :
    zand (forallG marked φ []) (EbangG marked t) ≠ T :=
  premise_undesignated_generic marked φ [] t hm

end ZFreeUIGeneric

#print axioms ZFreeUIGeneric.isT_true
#print axioms ZFreeUIGeneric.ebangG_iff
#print axioms ZFreeUIGeneric.zand_T_left
#print axioms ZFreeUIGeneric.zand_T_right
#print axioms ZFreeUIGeneric.allG_mem
#print axioms ZFreeUIGeneric.forallG_T
#print axioms ZFreeUIGeneric.forallG_delivers
#print axioms ZFreeUIGeneric.free_ui_valid_generic
#print axioms ZFreeUIGeneric.premise_undesignated_generic
#print axioms ZFreeUIGeneric.not_vacuous_generic
#print axioms ZFreeUIGeneric.empty_range_still_refuses
