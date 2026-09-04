/-
  ZFreeUI.lean — E32b: UNIVERSAL INSTANTIATION under the mark, promoted from
  measurement to theorems on the EMPTY axiom list.

  WHY. The published caveat named two results as measured rather than proved:
  the identity-of-indiscernibles failure (now ZIndisc.lean) and the free
  instantiation law. This file is the second half. What zdesc.py enumerates in
  its §7 is proved here for the same domain, with no axioms.

  THE TWO CLAIMS, and they pull in opposite directions:

    CLASSICAL UI FAILS.  From "everything grounded is φ" one may not conclude
    φ of a term that denotes nothing. The premise is T, the conclusion is Z on
    a non-denoting reference, and T → Z is F. So the classical schema is not
    valid — the arrow itself reports the failure rather than a side condition.

    THE FREE-LOGIC REPAIR HOLDS.  Add the existence premise: ∀xφ together with
    E!t does license φ(t). It holds for a reason worth stating plainly — the
    conjunction is never designated when t is non-denoting, because E!t is
    itself Z there. The repair does not patch the conclusion; it withholds the
    licence.

  Existence here is not a primitive: E! is EARNED SELF-IDENTITY from E31, so
  "quantifiers range over what exists" reduces to "over what has earned its
  own identity". That is the whole free-logic signature of ZTL.

  WHAT IS NOT PROVED. The same bound as ZIndisc: this is the five-individual
  domain. Nothing here says the schema fails in every domain — only that in
  this one it is a theorem rather than a measurement.
-/
import ZDesc

namespace ZFreeUI

open V
open ZEq
open ZEq.Indiv
open ZDesc

/-- The non-denoting term: "the F" where nothing is F. By `iota_empty_marked`
it is a marked reference, so every atom about it is Z. -/
def theKing : Indiv := theIota pEmpty

/-- A predicate true of every grounded individual, Z on a mark — the `φ` of
the schema, chosen so the universal premise is as strong as it can be. -/
def everything (x : Indiv) : V :=
  if marked x then Z else T

/-- The universal over the GROUNDED domain, read strictly: T only when every
grounded individual gives T. Quantification ranges over what exists, which is
the point at issue. -/
def forallGrounded (φ : Indiv → V) : V :=
  if φ g0 = T && φ g1 = T && φ g2 = T then T else F

/-! ### The premise really is as strong as claimed -/

theorem universal_holds : forallGrounded everything = T := by decide

/-- The term denotes nothing, and the predicate reports that with a mark. -/
theorem king_is_marked : Ebang theKing = Z ∧ everything theKing = Z := by decide

/-! ### Classical universal instantiation fails -/

/-- `∀xφ → φ(t)` is F for a non-denoting `t`: the premise is earned, the
conclusion is on credit, and the arrow refuses. This is the failure the
caveat reported. -/
theorem classical_ui_fails :
    zimp (forallGrounded everything) (everything theKing) = F := by decide

/-- It is not that the arrow dislikes this predicate: on a grounded term the
same schema goes through. -/
theorem classical_ui_holds_grounded :
    zimp (forallGrounded everything) (everything g0) = T := by decide

/-! ### The free-logic repair holds -/

/-- With the existence premise added, the schema is valid — and valid because
the premise is never designated for a non-denoting term, not because the
conclusion improved. -/
theorem free_ui_premise_undesignated :
    zand (forallGrounded everything) (Ebang theKing) ≠ T := by decide

/-- The repaired schema, stated over the whole domain: wherever the premise
`∀xφ ∧ E!t` is earned, `φ(t)` is earned too. No individual escapes it. -/
theorem free_ui_valid :
    ∀ t : Indiv,
      zand (forallGrounded everything) (Ebang t) = T → everything t = T := by
  decide

/-- And the repair is not vacuous: for grounded terms the premise IS earned,
so the schema licenses something. -/
theorem free_ui_not_vacuous :
    zand (forallGrounded everything) (Ebang g0) = T := by decide

end ZFreeUI
