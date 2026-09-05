/-
  ZNoAxiom.lean — E41: TRANSPORT, NOT CREATION.

  §23's first finding, measured on a 153-formula pool over three atoms:
  "From nothing, nothing — even on credit. The closure of the empty premise
  set is empty, with and without the loans: the battery has no axiom rule.
  And yet ZTL-tautologies EXIST — the guarded forms ¬q → ¬q and ¬(p ⊕ p) —
  because denial is classical (¬Z = F). The alive rules are transport, not
  creation: classical logic mints truth from form; ZTL's free truths must
  ENTER, as verified premises."

  Proved here in two halves that only together say anything.

    1. THE TAUTOLOGIES EXIST, for every assignment and not merely on a pool:
       `¬q → ¬q` and `¬(p ⊕ p)` are T under EVERY valuation, marks included.
       This is where the greedy denial earns its keep — ¬Z = F is classical,
       so a formula built on denials cannot be dragged to F by a mark.

    2. NOTHING IS DERIVABLE FROM NOTHING, for any rule system whose every
       rule has at least one premise. Not "the battery happens not to derive
       it": no such system can, whatever its rules are.

  Together: **there is a formula true under every assignment that no
  premise-requiring calculus derives from the empty set.** Truth of that
  shape has to be brought in, not minted.

  WHAT IS AND IS NOT PROVED HERE. That the twelve alive rules of §3.2 all
  have non-empty premise sets is a fact about the battery, recorded there and
  MEASURED — it is the hypothesis of the theorem below, not its conclusion.
  What is proved is that the hypothesis suffices, for every rule set at once,
  which is what the 153-formula closure could only sample.
-/
import ZTL

namespace ZNoAxiom

open V

/-! ### 1. The tautologies, over every valuation -/

/-- `¬q → ¬q`: the law of identity, guarded by a denial. -/
def guardedId (q : Nat) : Fm := Fm.imp (Fm.neg (Fm.atom q)) (Fm.neg (Fm.atom q))

/-- `¬(p ⊕ p)`: the denial of self-difference. -/
def deniedSelfXor (p : Nat) : Fm := Fm.neg (Fm.xor (Fm.atom p) (Fm.atom p))

theorem imp_self_of_not_Z : ∀ x : V, zimp (znot x) (znot x) = T := by decide

theorem not_xor_self : ∀ x : V, znot (zxor x x) = T := by decide

/-- **THE GUARDED IDENTITY IS TRUE UNDER EVERY VALUATION**, marks included.
The denial is classical, so no mark can drag it down. -/
theorem guardedId_valid (v : Nat → V) (q : Nat) : evalF v (guardedId q) = T :=
  imp_self_of_not_Z (v q)

theorem deniedSelfXor_valid (v : Nat → V) (p : Nat) :
    evalF v (deniedSelfXor p) = T :=
  not_xor_self (v p)

/-! ### 2. Nothing from nothing, for any premise-requiring calculus -/

/-- A rule: some premises, one conclusion. -/
structure Rule where
  premises : List Fm
  concl    : Fm

/-- The battery has no axiom rule: every rule demands something. -/
def NoAxiomRule (rs : List Rule) : Prop := ∀ r, r ∈ rs → r.premises ≠ []

/-- Derivability: a premise, or a rule all of whose premises are derivable. -/
inductive Derivable (rs : List Rule) (Γ : List Fm) : Fm → Prop where
  | prem {φ : Fm} : φ ∈ Γ → Derivable rs Γ φ
  | rule (r : Rule) : r ∈ rs →
      (∀ ψ, ψ ∈ r.premises → Derivable rs Γ ψ) → Derivable rs Γ r.concl

/-- **NOTHING IS DERIVABLE FROM NOTHING.** Not a fact about these twelve
rules: no calculus whose every rule demands a premise can produce anything
from the empty set. -/
theorem no_creation (rs : List Rule) (h : NoAxiomRule rs) :
    ∀ φ : Fm, ¬ Derivable rs [] φ := by
  intro φ d
  induction d with
  | prem hm => exact nomatch hm
  | rule r hr _ ih =>
      cases hp : r.premises with
      | nil => exact absurd hp (h r hr)
      | cons ψ rest =>
          exact ih ψ (by rw [hp]; exact List.Mem.head rest)

/-! ### The two halves together -/

/-- **TRANSPORT, NOT CREATION.** There is a formula true under every
valuation that no premise-requiring calculus derives from nothing. Classical
logic mints truth from form; here a free truth has to ENTER as a verified
premise. -/
theorem transport_not_creation (rs : List Rule) (h : NoAxiomRule rs) (q : Nat) :
    (∀ v : Nat → V, evalF v (guardedId q) = T)
  ∧ ¬ Derivable rs [] (guardedId q) :=
  ⟨fun v => guardedId_valid v q, no_creation rs h (guardedId q)⟩

end ZNoAxiom

#print axioms ZNoAxiom.guardedId_valid
#print axioms ZNoAxiom.deniedSelfXor_valid
#print axioms ZNoAxiom.no_creation
#print axioms ZNoAxiom.transport_not_creation
