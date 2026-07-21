/-
  ZDesc.lean — E32: FREE LOGIC and definite DESCRIPTIONS, zero-trust.

  ZTL's answer to a non-denoting singular term is the mark: an atomic
  statement about it is Z, and the greedy lift propagates it. This makes
  ZTL a free logic distinct from the negative (F), positive (T) and
  supervaluational (gap) schools — measured in full in zdesc.py.

  This file carries the first-order core on the EMPTY axiom list, standing
  on E31 (ZEq): a definite description ιx.φ(x) denotes the unique grounded
  satisfier of φ, otherwise it is a marked (non-denoting) reference; and
  existence is EARNED SELF-IDENTITY (Quine) — E!(t) := eqI t t.

  Lean pitfall (again, cf. ZEq): every match on `Indiv` here is exhaustive
  and non-overlapping — a wildcard `_` would drag propext through the
  matcher and lift the theorems off [].
-/
import ZEq

namespace ZDesc

open V
open ZEq
open ZEq.Indiv

/-- Existence is earned self-identity — the individual-level detector built
literally on E31's `=`. Grounded → T; a non-denoting reference → Z (never
asserted absent, only marked). -/
def Ebang (t : Indiv) : V := eqI t t

theorem exists_is_self_identity : ∀ t : Indiv, Ebang t = eqI t t :=
  fun _ => rfl

theorem grounded_exists : Ebang g0 = T ∧ Ebang g1 = T ∧ Ebang g2 = T := by decide

/-- Non-existence is Z, not a free F: ZTL marks the missing reference. -/
theorem nonexist_marked : Ebang m1 = Z ∧ Ebang m2 = Z := by decide

/-- The definite description operator. Given a grounded satisfaction
predicate `p`, `theIota p` is the unique grounded individual with `p`, or a
marked reference (`m1`) when zero or several satisfy — Russell's uniqueness,
but failure lands on the mark, not on falsity. Cases are exhaustive over the
eight grounded satisfaction patterns (no wildcard). -/
def theIota (p : Indiv → Bool) : Indiv :=
  match p g0, p g1, p g2 with
  | true,  false, false => g0
  | false, true,  false => g1
  | false, false, true  => g2
  | false, false, false => m1
  | true,  true,  false => m1
  | true,  false, true  => m1
  | false, true,  true  => m1
  | true,  true,  true  => m1

/-- Exhaustive grounded predicates for the witnesses (no wildcard). -/
def pOnlyG0 : Indiv → Bool
  | g0 => true  | g1 => false | g2 => false | m1 => false | m2 => false
def pEmpty : Indiv → Bool
  | g0 => false | g1 => false | g2 => false | m1 => false | m2 => false
def pTwo : Indiv → Bool
  | g0 => true  | g1 => true  | g2 => false | m1 => false | m2 => false

/-- A unique description denotes its satisfier, which then exists. -/
theorem iota_unique_denotes :
    theIota pOnlyG0 = g0 ∧ Ebang (theIota pOnlyG0) = T := by decide

/-- "The F" with no F is a non-denoting reference: marked, and Z. -/
theorem iota_empty_marked :
    theIota pEmpty = m1 ∧ Ebang (theIota pEmpty) = Z := by decide

/-- "The F" with several F's is likewise non-denoting — uniqueness unearned. -/
theorem iota_multiple_marked : Ebang (theIota pTwo) = Z := by decide

/-- A generic grounded predicate, Z on a non-denoting reference. -/
def baldOf (x : Indiv) : V :=
  if marked x then Z else if x = g0 then T else F

/-- **Excluded middle fails on a non-denoting atom** — the sharp divergence
from supervaluational free logic (which makes it super-true). ZTL marks the
gap rather than completing it, so `P(τ) ∨ ¬P(τ) = F`. -/
theorem lem_fails_nondenoting :
    zor (baldOf (theIota pEmpty)) (znot (baldOf (theIota pEmpty))) = F := by
  decide

/-- **Greedy propagation**: the same non-denoting atom, once joined to a
guarded tautology, collapses to a verdict — the mark evaporates in a
compound. -/
theorem mark_evaporates_in_compound :
    baldOf (theIota pEmpty) = Z ∧
    zor (baldOf (theIota pEmpty)) T = T := by decide

#print axioms exists_is_self_identity
#print axioms grounded_exists
#print axioms nonexist_marked
#print axioms iota_unique_denotes
#print axioms iota_empty_marked
#print axioms iota_multiple_marked
#print axioms lem_fails_nondenoting
#print axioms mark_evaporates_in_compound

end ZDesc
