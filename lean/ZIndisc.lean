/-
  ZIndisc.lean — E31b: IDENTITY OF INDISCERNIBLES, promoted from measurement
  to a theorem on the EMPTY axiom list.

  WHY THIS FILE EXISTS. ZEq.lean says, in its own header:

      The second-order finding (identity of indiscernibles fails on marks)
      quantifies over all predicates and stays in zeq.py.

  That was the honest caveat printed in the paper: this one result was
  MEASURED by enumeration in Python while its neighbours were PROVED in Lean.
  The gap was never about the size of the domain — it was that the statement
  quantifies over PREDICATES, one order up.

  The gap closes because the quantifier is finite in the same way the domain
  is. A generic predicate reads a marked reference as Z and splits the
  grounded ones; over three grounded individuals there are exactly eight such
  predicates, and they can be named. Quantifying over a NAMED LIST keeps every
  step decidable and keeps the file off `propext` — quantifying over the
  function type `Indiv → V` would not.

  WHAT IS PROVED HERE, and it is exactly what zeq.py measured:

    * m1 and m2 are indiscernible: every generic predicate gives Z on both;
    * yet their identity is not earned — eqI m1 m2 = Z, not T;
    * therefore the law "indiscernibles are identical" FAILS;
    * and it fails ONLY on marks: among grounded individuals it holds.

  WHAT IS STILL NOT PROVED, stated so the caveat shrinks honestly rather than
  disappearing: this is the five-individual domain of ZEq. Nothing here says
  the failure persists in every domain — only that it is a theorem, not a
  measurement, in the domain where the rest of E31 lives.
-/
import ZEq

namespace ZIndisc

open V
open ZEq
open ZEq.Indiv

/-- A generic predicate over the domain: it reads a marked reference as Z —
the individual-level mark propagates into the atom — and splits the grounded
ones by membership in a named subset. This mirrors `generic` in zeq.py. -/
def gp (s0 s1 s2 : Bool) : Indiv → V
  | g0 => if s0 then T else F
  | g1 => if s1 then T else F
  | g2 => if s2 then T else F
  | m1 => Z
  | m2 => Z

/-- Every generic predicate over three grounded individuals. Eight of them,
named rather than generated: a `List` keeps `decide` on ground terms and off
the function type, which is what keeps the axiom list empty. -/
def preds : List (Indiv → V) :=
  [gp false false false, gp false false true,  gp false true  false,
   gp false true  true,  gp true  false false, gp true  false true,
   gp true  true  false, gp true  true  true]

/-- Two individuals are indiscernible when no generic predicate separates
them. This is the second-order clause, made decidable by ranging over the
named list instead of over all functions. -/
def indiscernible (a b : Indiv) : Bool :=
  preds.all (fun P => decide (P a = P b))

/-! ### The measurement, now a theorem -/

/-- Nothing tells the two marked references apart. -/
theorem marks_indiscernible : indiscernible m1 m2 = true := by decide

/-- Yet their identity is not earned: it is on credit, not true. -/
theorem marks_not_identical : eqI m1 m2 = Z := by decide

/-- Therefore the law falls: indiscernibility does not force identity. -/
theorem indiscernibles_not_identical :
    ¬ ∀ a b : Indiv, indiscernible a b = true → eqI a b = T := by decide

/-- The failure is not an accident of the pair — it is exactly the mark. On
grounded references indiscernibility DOES force earned identity. -/
theorem holds_on_grounded :
    ∀ a b : Indiv, marked a = false → marked b = false →
      indiscernible a b = true → eqI a b = T := by decide

/-- And the separation is sharp: a witness pair exists, and it is a marked
pair. Stated without `∃` over Prop so the check stays on ground terms. -/
theorem witness_is_marked :
    indiscernible m1 m2 = true ∧ eqI m1 m2 ≠ T ∧
    marked m1 = true ∧ marked m2 = true := by decide

/-- Grounded individuals are discernible from one another — the predicates
really do separate them, so the theorem above is not vacuous. -/
theorem grounded_are_discernible :
    indiscernible g0 g1 = false ∧ indiscernible g0 g2 = false ∧
    indiscernible g1 g2 = false := by decide

end ZIndisc
