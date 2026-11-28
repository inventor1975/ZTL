/-!
# QZ, theorem 2 — a strict verdict holds in EVERY lattice with a negation that reverses order. Written with AI, 2026-11-27.

Bare Lean 4, no imports.   lean research/qz/QZ2.lean

`QZ1.lean` proved it for the six-element lattice MO2 by enumeration. Here the lattice is ANY structure with

  * an order, a meet (greatest lower bound) and a join (least upper bound),
  * a negation that reverses the order and satisfies `x ≤ ¬¬x`.

Nothing else is used: no `x ∧ ¬x = ⊥`, no `¬¬x ≤ x`, no orthomodular law, no distributive law. So the theorem covers
the lattice of subspaces of any quantum system (an ortholattice has all of the above), every Boolean algebra, and
every Heyting algebra (intuitionistic negation reverses order and satisfies `x ≤ ¬¬x`).

THEOREM (`strict_sound`). Give each atom an element of the lattice and a strict mark T, F or U, so that an atom marked
T lies above the state `s` and an atom marked F has its negation above `s`. Then for every formula in ¬ ∧ ∨: if the
strict three-valued reading (strong Kleene) is T, the formula's element lies above `s`; if it is F, the negation of
the formula's element lies above `s`.

Boundary. That a given physical system's propositions form such a lattice is the standard account of quantum logic,
not proved here. That the strict reading is the ZTL judge's EARNED / REFUTED is measured (research/qz/rivals_probe.py and the
later probes: no disagreement), not imported. It is a fact about VALUES, not about mechanism: since the pure branch of
2026-11-22 the kernel defines EARNED / REFUTED by its own readings (ZTL lean/ZRead.lean, `earnedR`, `refutedR`), with
no Kleene register. A proof of this theorem directly for those readings is owed.
-/

namespace QZ2

/-- A lattice with an order-reversing negation satisfying `x ≤ ¬¬x`. -/
structure NLat (α : Type) where
  le : α → α → Prop
  meet : α → α → α
  join : α → α → α
  neg : α → α
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  meet_le_l : ∀ a b, le (meet a b) a
  meet_le_r : ∀ a b, le (meet a b) b
  le_meet : ∀ {s a b}, le s a → le s b → le s (meet a b)
  le_join_l : ∀ a b, le a (join a b)
  le_join_r : ∀ a b, le b (join a b)
  join_le : ∀ {a b c}, le a c → le b c → le (join a b) c
  anti : ∀ {a b}, le a b → le (neg b) (neg a)
  le_nn : ∀ a, le a (neg (neg a))

inductive K | T | F | U
  deriving DecidableEq

open K

instance (p : K → Prop) [DecidablePred p] : Decidable (∀ x : K, p x) :=
  decidable_of_iff (p T ∧ p F ∧ p U)
    ⟨fun ⟨h0,h1,h2⟩ x => by cases x <;> assumption, fun h => ⟨h T, h F, h U⟩⟩

def kneg : K → K
  | T => F | F => T | U => U
def kand (p q : K) : K := if p = F ∨ q = F then F else if p = T ∧ q = T then T else U
def kor (p q : K) : K := if p = T ∨ q = T then T else if p = F ∧ q = F then F else U

theorem kneg_T : ∀ p, kneg p = T → p = F := by decide
theorem kneg_F : ∀ p, kneg p = F → p = T := by decide
theorem kand_T : ∀ p q, kand p q = T → p = T ∧ q = T := by decide
theorem kand_F : ∀ p q, kand p q = F → p = F ∨ q = F := by decide
theorem kor_T : ∀ p q, kor p q = T → p = T ∨ q = T := by decide
theorem kor_F : ∀ p q, kor p q = F → p = F ∧ q = F := by decide

inductive Fm
  | atom (n : Nat)
  | not (f : Fm)
  | and (f g : Fm)
  | or (f g : Fm)

variable {α : Type} (L : NLat α)

/-- the lattice reading -/
def qe (v : Nat → α) : Fm → α
  | .atom n => v n
  | .not f => L.neg (qe v f)
  | .and f g => L.meet (qe v f) (qe v g)
  | .or f g => L.join (qe v f) (qe v g)

/-- the strict reading -/
def ke (k : Nat → K) : Fm → K
  | .atom n => k n
  | .not f => kneg (ke k f)
  | .and f g => kand (ke k f) (ke k g)
  | .or f g => kor (ke k f) (ke k g)

/-- what is established agrees with the state -/
def Agrees (s : α) (m : K) (x : α) : Prop :=
  (m = T → L.le s x) ∧ (m = F → L.le s (L.neg x))

/-- the one step that is not immediate: two refuted disjuncts refute the disjunction -/
theorem neg_join {s x y : α} (hx : L.le s (L.neg x)) (hy : L.le s (L.neg y)) : L.le s (L.neg (L.join x y)) := by
  have m := L.le_meet hx hy                                   -- s ≤ ¬x ∧ ¬y
  have ux : L.le x (L.neg (L.meet (L.neg x) (L.neg y))) := L.le_trans (L.le_nn x) (L.anti (L.meet_le_l _ _))
  have uy : L.le y (L.neg (L.meet (L.neg x) (L.neg y))) := L.le_trans (L.le_nn y) (L.anti (L.meet_le_r _ _))
  have j := L.anti (L.join_le ux uy)                          -- ¬¬(¬x ∧ ¬y) ≤ ¬(x ∨ y)
  exact L.le_trans m (L.le_trans (L.le_nn _) j)

/-- **QZ 2.** A strict verdict is the lattice's verdict: every formula, every such lattice, every state. -/
theorem strict_sound (s : α) (v : Nat → α) (k : Nat → K) (h : ∀ n, Agrees L s (k n) (v n)) :
    ∀ f : Fm, Agrees L s (ke k f) (qe L v f) := by
  intro f
  induction f with
  | atom n => exact h n
  | not f ih =>
    constructor
    · intro e; exact ih.2 (kneg_T _ e)
    · intro e; exact L.le_trans (ih.1 (kneg_F _ e)) (L.le_nn _)
  | and f g ihf ihg =>
    constructor
    · intro e
      have := kand_T _ _ e
      exact L.le_meet (ihf.1 this.1) (ihg.1 this.2)
    · intro e
      cases kand_F _ _ e with
      | inl h1 => exact L.le_trans (ihf.2 h1) (L.anti (L.meet_le_l _ _))
      | inr h2 => exact L.le_trans (ihg.2 h2) (L.anti (L.meet_le_r _ _))
  | or f g ihf ihg =>
    constructor
    · intro e
      cases kor_T _ _ e with
      | inl h1 => exact L.le_trans (ihf.1 h1) (L.le_join_l _ _)
      | inr h2 => exact L.le_trans (ihg.1 h2) (L.le_join_r _ _)
    · intro e
      have := kor_F _ _ e
      exact neg_join L (ihf.2 this.1) (ihg.2 this.2)

end QZ2

#print axioms QZ2.strict_sound
