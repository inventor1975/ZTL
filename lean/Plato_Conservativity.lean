/-
  Plato_Conservativity.lean  —  ZTL / dilemmas
  ---------------------------------------------------------------------------
  Absence has no formula: the operational theory cannot exclude a ground.

  Companion to Plato_Equality.lean (Part III там же).  The dispute's remainder
  after the Third Man is Aristotle's exit (a ground exists, immanent) versus
  the operational exit (no ground-object; the character is the record of test
  applications).  The claim to be checked, stated first in words:

  THE OPERATIONAL AXIOMS, fixed exactly (word list first, per the programme):

    O1 (doing-not-being)  Bearing the character IS the applicability record:
                          Bears x ↔ ∃ n, App x n.
    O2 (nonemptiness)     Something bears it: ∃ x, Bears x.

  Nothing else.  In particular NO axiom mentions grounds — that is the point:
  the operational theory refuses to postulate, and a refusal has no formula.

  THE THEOREM.  Every operational model extends to a model with a ground:
  a fresh element g (provably outside the old domain) which bears the
  character and grounds every bearer, while O1 and O2 keep holding and every
  old element keeps its old Bears- and App-facts.  By soundness this is the
  classical fact  Op-axioms ⊬ ¬∃g — no operational theorem denies the ground.
  The negative content of operationalism is therefore INEXPRESSIBLE at the
  object level; its only trace is procedural (which acts are performed), and
  the discriminator between the two exits must live a floor above the
  formulas (redeemability — see zredeem.py, E26).

  Scope, honestly: preservation is proved AXIOM BY AXIOM for O1 and O2 —
  conservativity is per-theory, not schematic; a different operational axiom
  list requires redoing exactly this file, and universally quantified axioms
  survive only because the fresh element is given the right facts.

  Self-contained: no imports, no mathlib.  Check with:

      lean Plato_Conservativity.lean

  All public objects must print "does not depend on any axioms".
-/

namespace PlatoConservativity

/-- An operational model: things, the application record, the character —
with the two operational axioms O1, O2 and nothing about grounds. -/
structure OpModel where
  D : Type
  App : D → Nat → Prop
  Bears : D → Prop
  O1 : ∀ x, Bears x ↔ ∃ n, App x n
  O2 : ∃ x, Bears x

/-- A grounded model: the same operational data PLUS a ground that bears the
character and grounds every bearer.  (Aristotle's ∃g, immanence left out of
the signature deliberately — separation is not needed for the point.) -/
structure GroundedModel where
  D : Type
  App : D → Nat → Prop
  Bears : D → Prop
  Grounds : D → D → Prop
  O1 : ∀ x, Bears x ↔ ∃ n, App x n
  O2 : ∃ x, Bears x
  g : D
  ground_bears : Bears g
  grounds_all : ∀ x, Bears x → Grounds g x

/-- The extended carrier: the old things, plus one fresh point for the ground. -/
inductive Ext (D : Type) where
  | old : D → Ext D
  | fresh : Ext D

open Ext

/-- THE CONSTRUCTION.  Extend any operational model by a fresh ground:
the fresh point bears the character (its record: every application succeeds),
and grounds every bearer.  Old elements keep their exact old facts. -/
def extend (M : OpModel) : GroundedModel where
  D := Ext M.D
  App := fun x n => match x with
    | old a => M.App a n
    | fresh => True
  Bears := fun x => match x with
    | old a => M.Bears a
    | fresh => True
  Grounds := fun gx x => gx = fresh ∧ (match x with
    | old a => M.Bears a
    | fresh => True)
  O1 := by
    intro x
    cases x with
    | old a =>
        constructor
        · intro h; exact (M.O1 a).mp h
        · intro h; exact (M.O1 a).mpr h
    | fresh =>
        constructor
        · intro _; exact ⟨0, trivial⟩
        · intro _; exact trivial
  O2 := by
    exact ⟨fresh, trivial⟩
  g := fresh
  ground_bears := trivial
  grounds_all := by
    intro x hx
    cases x with
    | old a => exact ⟨rfl, hx⟩
    | fresh => exact ⟨rfl, trivial⟩

/-! ### Preservation lemmas — the old world is untouched -/

/-- Old elements keep their Bears-facts exactly. -/
theorem bears_preserved (M : OpModel) (a : M.D) :
    (extend M).Bears (old a) ↔ M.Bears a := Iff.rfl

/-- Old elements keep their App-records exactly. -/
theorem app_preserved (M : OpModel) (a : M.D) (n : Nat) :
    (extend M).App (old a) n ↔ M.App a n := Iff.rfl

/-- The embedding of the old domain is injective — nothing is merged. -/
theorem old_injective (M : OpModel) (a b : M.D)
    (h : (old a : Ext M.D) = old b) : a = b := by
  cases h; rfl

/-- The ground is FRESH: it is provably not any old element. -/
theorem ground_is_fresh (M : OpModel) (a : M.D) :
    (extend M).g ≠ old a := by
  intro h
  cases h

/-- The extension really is grounded: the ground bears, and grounds every
bearer — packaged for citation. -/
theorem extension_grounded (M : OpModel) :
    (extend M).Bears (extend M).g
      ∧ ∀ x, (extend M).Bears x → (extend M).Grounds (extend M).g x :=
  ⟨(extend M).ground_bears, (extend M).grounds_all⟩

/-! ## Verdict

Every operational model sits inside a grounded one, old facts intact
(bears_preserved, app_preserved, old_injective), the ground genuinely new
(ground_is_fresh) and genuinely a ground (extension_grounded), with O1 and O2
still holding — they are fields of `extend M`, so their preservation is
checked by the kernel when the definition typechecks.  Hence no consequence
of O1∧O2 can say "there is no ground": to say it, a formula would have to be
false in `extend M` while true in M, and the theory cannot tell them apart
from inside.  The operational thesis is a refusal to postulate, and the
refusal leaves only a procedural trace — the floor above the formulas.
-/

end PlatoConservativity

#print axioms PlatoConservativity.extend
#print axioms PlatoConservativity.bears_preserved
#print axioms PlatoConservativity.app_preserved
#print axioms PlatoConservativity.old_injective
#print axioms PlatoConservativity.ground_is_fresh
#print axioms PlatoConservativity.extension_grounded
