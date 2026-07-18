/-
  QuantumWitness.lean — the quantum pole of the four-logic cycle, machine-checked.

  A self-contained, mathlib-FREE witness that quantum logic and ZTL make MIRROR
  sacrifices. ZTL (see ZTL.lean) keeps distributivity and drops LEM / DNE /
  identity at the mark. Quantum logic does the opposite: it DROPS distributivity
  and KEEPS excluded middle, double negation, and non-contradiction.

  The witness is MO2 (the six-element orthomodular "Chinese lantern"): the
  smallest ortholattice that is non-distributive. Everything below is proved by
  `decide` over the finite carrier — empty axiom list, verifiable from zero:

      lean QuantumWitness.lean

  This does NOT judge quantum logic; it exhibits a concrete lattice where the
  quantum profile holds, as the formalizable half of the cycle (the
  intuitionistic and classical corners are metatheorems, by design not here).
-/

namespace QuantumWitness

/-- MO2: ⊥, two complementary pairs (a,a') (b,b'), ⊤. -/
inductive Q where
  | bot | a | a' | b | b' | top
deriving DecidableEq, Repr

open Q

/-- Enumeration of the six elements is decidable — every `decide` lives on this. -/
instance (p : Q → Prop) [DecidablePred p] : Decidable (∀ x : Q, p x) :=
  decidable_of_iff (p bot ∧ p a ∧ p a' ∧ p b ∧ p b' ∧ p top)
    ⟨fun ⟨h0,h1,h2,h3,h4,h5⟩ x => by cases x <;> assumption,
     fun h => ⟨h bot, h a, h a', h b, h b', h top⟩⟩

/-- Orthocomplement: pairs swap, ⊥ ↔ ⊤. -/
def neg : Q → Q
  | bot => top | top => bot
  | a => a' | a' => a
  | b => b' | b' => b

/-- Meet: equal → itself; ⊥ absorbs; ⊤ is unit; two DISTINCT middle atoms → ⊥. -/
def meet (x y : Q) : Q :=
  if x = y then x
  else if x = bot ∨ y = bot then bot
  else if x = top then y
  else if y = top then x
  else bot

/-- Join, dual of meet: ⊤ absorbs; ⊥ is unit; two distinct middle atoms → ⊤. -/
def join (x y : Q) : Q :=
  if x = y then x
  else if x = top ∨ y = top then top
  else if x = bot then y
  else if y = bot then x
  else top

-- ============================================================
-- The quantum profile — all on the empty axiom list
-- ============================================================

/-- **Distributivity FAILS** — the quantum tax.  Witness: a ∧ (b ∨ b') = a,
but (a ∧ b) ∨ (a ∧ b') = ⊥. -/
theorem distributivity_fails :
    ¬ ∀ x y z : Q, meet x (join y z) = join (meet x y) (meet x z) := by decide

/-- **Excluded middle HOLDS**: x ∨ ¬x = ⊤ for every element. -/
theorem lem_holds : ∀ x : Q, join x (neg x) = top := by decide

/-- **Double negation HOLDS**: ¬¬x = x (the complement is involutive). -/
theorem dne_holds : ∀ x : Q, neg (neg x) = x := by decide

/-- **Non-contradiction HOLDS**: x ∧ ¬x = ⊥ — the shared floor of the cycle,
kept by quantum exactly as ZTL keeps it. -/
theorem no_contradiction_holds : ∀ x : Q, meet x (neg x) = bot := by decide

/-- The explicit mirror, in one statement: distributivity fails while the three
laws ZTL loses (LEM, DNE — and identity is trivial in a lattice, x ≤ x) all
hold; the invariant non-contradiction is kept by both. -/
theorem quantum_pole :
    (¬ ∀ x y z : Q, meet x (join y z) = join (meet x y) (meet x z))
    ∧ (∀ x : Q, join x (neg x) = top)
    ∧ (∀ x : Q, neg (neg x) = x)
    ∧ (∀ x : Q, meet x (neg x) = bot) :=
  ⟨distributivity_fails, lem_holds, dne_holds, no_contradiction_holds⟩

-- ============================================================
-- Axiom audit — every line prints "does not depend on any axioms"
-- ============================================================
#print axioms distributivity_fails
#print axioms lem_holds
#print axioms dne_holds
#print axioms no_contradiction_holds
#print axioms quantum_pole

end QuantumWitness
