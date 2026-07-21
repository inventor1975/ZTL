/-
  ZEps.lean — E34: Hilbert's ε-operator (indefinite descriptions), zero-trust.

  Companion to E32's definite description ι. εx.φ is the CHOICE term — "an
  x such that φ": it picks a canonical grounded witness of φ, and if φ has
  no grounded witness the choice is unearned and εx.φ is a marked (non-
  denoting) reference. To choose is an act; a choice from nothing is the
  mark. Measured in full in zeps.py; here the core on the EMPTY axiom list.

  As in ZEq/ZDesc, every match on `Indiv` is exhaustive and non-overlapping
  — a wildcard would drag propext through the matcher.
-/
import ZDesc

namespace ZEps

open V
open ZEq
open ZEq.Indiv
open ZDesc (Ebang theIota pOnlyG0 pEmpty pTwo)

/-- The choice over three grounded satisfaction bits: the first satisfied
individual, or `m1` when none. Exhaustive, no wildcard. -/
def epsB : Bool → Bool → Bool → Indiv
  | true,  true,  true  => g0
  | true,  true,  false => g0
  | true,  false, true  => g0
  | true,  false, false => g0
  | false, true,  true  => g1
  | false, true,  false => g1
  | false, false, true  => g2
  | false, false, false => m1

/-- εx.φ — the first grounded satisfier of `p` (canonical choice), or a
marked reference when nothing grounded satisfies. -/
def theEps (p : Indiv → Bool) : Indiv := epsB (p g0) (p g1) (p g2)

/-- The witness detector `∃x.φ` as a Boolean over the grounded domain. -/
def existsB (p : Indiv → Bool) : Bool := p g0 || p g1 || p g2

/-- Denotation as a Boolean (kept out of `Prop` so the bridge is a Bool
identity, not a `Prop = Prop` that would need propext). -/
def denotesB : Indiv → Bool
  | g0 => true | g1 => true | g2 => true | m1 => false | m2 => false

/-- **The ε–∃ bridge**: the choice term denotes exactly when a witness is
earned — existence of εx.φ IS the existential. A Bool identity, proved by
cases on the three grounded satisfaction bits (no wildcard, so `[]`). -/
theorem eps_denotes_iff_exists (p : Indiv → Bool) :
    denotesB (theEps p) = existsB p := by
  unfold theEps existsB
  cases p g0 <;> cases p g1 <;> cases p g2 <;> rfl

/-- The empty choice is the mark: εx.(false) is marked, and Z. -/
theorem eps_empty_marked :
    theEps pEmpty = m1 ∧ Ebang (theEps pEmpty) = Z := by decide

/-- A witnessed choice denotes and is self-identical. -/
theorem eps_witness_denotes :
    theEps pOnlyG0 = g0 ∧ Ebang (theEps pOnlyG0) = T := by decide

/-- **ι and ε split on multiplicity.** Where φ is satisfied by two grounded
individuals, "the F" (ι) is marked while "an F" (ε) denotes a choice. -/
theorem iota_eps_split : theIota pTwo = m1 ∧ theEps pTwo = g0 := by decide

/-- The ε-axiom `φ(t) → φ(εx.φ)`, an earned instance: a witness makes the
choice satisfy φ. -/
theorem eps_axiom_instance : pTwo g0 = true → pTwo (theEps pTwo) = true := by
  decide

#print axioms eps_denotes_iff_exists
#print axioms eps_empty_marked
#print axioms eps_witness_denotes
#print axioms iota_eps_split
#print axioms eps_axiom_instance

end ZEps
