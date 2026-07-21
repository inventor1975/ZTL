/-
  ZEq.lean — E31: first-order IDENTITY under the zero-trust lift.

  Classical FO has a `=` predicate with reflexivity and Leibniz's law.
  ZTL's FO layer never had one. Here identity is an EARNED verdict: a
  *marked* individual is a reference that is not yet verified (the
  individual-level face of Z — a null pointer, an unresolved description,
  1/0), and equality inherits the mark:

      eqI a b = T   if a,b grounded and the same object
              = F   if a,b grounded and different
              = Z   if a or b is a marked (unverified) reference.

  Measured in full in zeq.py; this file promotes the first-order core to
  theorems on the EMPTY axiom list (imports only ZTL, no mathlib):

    * reflexivity holds on grounded, is Z on marked, and is NOT a free law;
    * an earned equality is genuine identity (eqI a b = T → a = b), so
      Leibniz substitution is congruence — salva veritate;
    * equality is never earned through a mark (no laundering);
    * symmetry and transitivity hold as rules; the symmetry *law*
      (biconditional) falls where the equality is Z, since ↔(Z,Z) = F.

  The second-order finding (identity of indiscernibles fails on marks)
  quantifies over all predicates and stays in zeq.py.
-/
import ZTL

namespace ZEq

open V

/-- Domain individuals: three grounded references, two unresolved (marked). -/
inductive Indiv where
  | g0 | g1 | g2 | m1 | m2
deriving DecidableEq, Repr

open Indiv

/-- Enumeration of the five individuals is decidable — every `decide` below
lives on this, exactly as ZTL.lean does for `V`. -/
instance (p : Indiv → Prop) [DecidablePred p] : Decidable (∀ x : Indiv, p x) :=
  decidable_of_iff (p g0 ∧ p g1 ∧ p g2 ∧ p m1 ∧ p m2)
    ⟨fun ⟨h0, h1, h2, hm1, hm2⟩ x => by cases x <;> assumption,
     fun h => ⟨h g0, h g1, h g2, h m1, h m2⟩⟩

/-- A marked individual is an unverified reference. Cases are EXHAUSTIVE
and NON-overlapping (no wildcard): an overlapping `_` compiles to a matcher
that drags `propext`, keeping the theorems off the empty axiom list. -/
def marked : Indiv → Bool
  | g0 => false
  | g1 => false
  | g2 => false
  | m1 => true
  | m2 => true

/-- Zero-trust identity: Z whenever a reference is unverified. `a = b` goes
through the derived `DecidableEq Indiv`, which is axiom-free. -/
def eqI (a b : Indiv) : V :=
  if marked a || marked b then Z
  else if a = b then T else F

/-! ### Reflexivity — earned, and not a free law -/

/-- Self-identity holds for grounded references. -/
theorem refl_ground : eqI g0 g0 = T ∧ eqI g1 g1 = T ∧ eqI g2 g2 = T := by decide

/-- Self-identity is Z on a marked reference — on credit. -/
theorem refl_marked : eqI m1 m1 = Z ∧ eqI m2 m2 = Z := by decide

/-- Reflexivity is NOT a free law: some individual is not certified equal to
itself (the marked ones). The identity analogue of `double_neg_fails`. -/
theorem refl_not_free : ¬ ∀ x : Indiv, eqI x x = T := by decide

/-! ### Leibniz substitutivity — an earned equality is genuine identity -/

/-- An EARNED equality means the two references are literally the same
object. This is the whole content of Leibniz substitution: once `eqI a b = T`
there is nothing to substitute — `a` and `b` are one. -/
theorem eq_forces_same : ∀ a b : Indiv, eqI a b = T → a = b := by decide

/-- **Leibniz's law / substitutivity of identicals**, for ANY predicate or
function `f : Indiv → V`: an earned equality licenses substitution salva
veritate. A pure term (`congrArg`), so the empty axiom list is immediate. -/
theorem leibniz_congr (f : Indiv → V) (a b : Indiv) (h : eqI a b = T) :
    f a = f b :=
  congrArg f (eq_forces_same a b h)

/-- No laundering: equality is never earned through a marked reference. -/
theorem no_laundering : ∀ a b : Indiv, eqI a b = T →
    marked a = false ∧ marked b = false := by decide

/-! ### Symmetry and transitivity — rules survive, the symmetry law falls -/

/-- Symmetry as a rule. -/
theorem symm_rule : ∀ a b : Indiv, eqI a b = T → eqI b a = T := by decide

/-- Transitivity as a rule. -/
theorem trans_rule : ∀ a b c : Indiv,
    eqI a b = T → eqI b c = T → eqI a c = T := by decide

/-- The symmetry *law* (biconditional) fails: where the equality is Z,
`↔(Z,Z) = F`, so `eqI a b ↔ eqI b a` is not T. The rule/law split of
entailment.py, now on identity. -/
theorem symm_law_falls : ¬ ∀ a b : Indiv, zxnor (eqI a b) (eqI b a) = T := by
  decide

#print axioms refl_ground
#print axioms refl_marked
#print axioms refl_not_free
#print axioms eq_forces_same
#print axioms leibniz_congr
#print axioms no_laundering
#print axioms symm_rule
#print axioms trans_rule
#print axioms symm_law_falls

end ZEq
