import ZTL
import ZRead
/-!
# QZ, theorem 3 — the theorem for the KERNEL'S OWN readings (no Kleene). Written with AI, 2026-11-27.

    LEAN_PATH=<ZTL>/lean/.lake/build/lib/lean lean research/qz/QZ3.lean         (imports the public kernel, edits nothing in it)

`QZ2.lean` proved "a strict verdict holds in every lattice with an order-reversing negation" for the strong Kleene
reading, and the tie to the ZTL judge was a measurement. Since the pure branch (2026-11-22) the kernel does not use a
Kleene register at all: EARNED and REFUTED are DEFINED by the dirty reading `V.rd` (`ZRead.lean`: `earnedR`,
`refutedR` — no reading of the occurrences makes the formula false, resp. true). This file proves the theorem for
exactly those definitions, over the kernel's own formula type `V.Fm` with all its connectives.

THE LATTICE. An order with meet, join, top, bottom and a negation such that
    negation reverses the order,   x ≤ ¬¬x,   s ≤ ⊤,   s ≤ ¬⊥.
Nothing else: no x ∧ ¬x = ⊥, no ¬¬x ≤ x, no orthomodular law, no distributive law. Subspace lattices of quantum
systems, Boolean algebras and Heyting algebras all qualify.
The connectives the lattice has no symbol for are read by the kernel's own definitions (`V.imp_def`, `V.xor_def`,
`V.xnor_def`): p → q as ¬p ∨ q, p ⊕ q as (p ∧ ¬q) ∨ (¬p ∧ q), p ↔ q as (p ∧ q) ∨ (¬p ∧ ¬q).

THEOREM (`earned_sound`, `refuted_sound`). Let `s` be what is known (a state), let each atom have an element of the
lattice, and let the marking agree with the state: an atom marked T lies above `s`, an atom marked F has its negation
above `s`, an atom marked Z is free. Then every formula the kernel calls EARNED lies above `s`, and every formula it
calls REFUTED has its negation above `s`.

PRIOR WORK (read 2026-11-27; see the end of each item for how far it was read).
  * Holliday, "A fundamental non-classical logic", Logics 1(1):36-79, 2023 (arXiv 2207.06993), Sections 1-3 read in
    the paper's own text. Definition 3.2: an "ultraweak pseudocomplementation" on a bounded lattice is an antitone ¬
    with a ≤ ¬¬a and ¬1 = 0. Footnote 9: these "are equivalent to what Dunn and Zhou (2005) call quasi-minimal
    negations with the added assumption that ¬1 = 0". Definition 3.1: a "weak pseudocomplementation" adds
    a ∧ ¬a = 0; the paper offers the logic of those lattices as common ground of intuitionistic logic and orthologic,
    and notes Kleene's three-element chain as an ultraweak example. So "one layer valid in the quantum, the
    intuitionistic and the classical case at once" is his idea, not ours. Dunn and Zhou, "Negation in the context of
    gaggle theory", Studia Logica 2005: not read.
    (2026-11-27, later: the WHOLE text of Holliday's paper was searched for Kleene, three-valued, partial valuation,
    supervaluation, truth-value gap, undefined, partial information, forced - one hit, the Kleene chain as an example;
    a search by words, not a reading. Dunn and Zhou could not be reached: behind a login, no open copy found.)
    Every bounded lattice with a negation as in Definition 3.2 meets what this file asks (`neg_bot_above` derives
    s ≤ ¬⊥ from ⊥ being least). This file asks less. That the two classes coincide is NOT claimed.
  * NOT found in what was read: a statement that verdicts forced under partial information (ours: the kernel's
    EARNED / REFUTED, by the dirty reading) are valid in every such lattice. "Not found" is not "absent".
  * Quantum supervaluationism (Bolotin, arXiv 1709.01207 and 1904.01364; both read in full): no theorem of this kind,
    no three-valued soundness statement, nothing machine-checked. Abramsky and Barbosa, "The logic of contextuality"
    (arXiv 2011.03064; read in full): partial Boolean algebras; no three-valued reading, no such statement.

Boundary. That a physical system's propositions form such a lattice is the standard account of quantum logic, not
proved here. IF STABLE is NOT covered and cannot be: the lattice can refute it (`QZ1.stable_refuted_by_lattice`).
-/

namespace QZ3
open V

/-- A bounded lattice with an order-reversing negation satisfying `x ≤ ¬¬x`. -/
structure NLat (α : Type) where
  le : α → α → Prop
  meet : α → α → α
  join : α → α → α
  neg : α → α
  top : α
  bot : α
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  meet_le_l : ∀ a b, le (meet a b) a
  meet_le_r : ∀ a b, le (meet a b) b
  le_meet : ∀ {s a b}, le s a → le s b → le s (meet a b)
  le_join_l : ∀ a b, le a (join a b)
  le_join_r : ∀ a b, le b (join a b)
  join_le : ∀ {a b c}, le a c → le b c → le (join a b) c
  anti : ∀ {a b}, le a b → le (neg b) (neg a)
  le_nn : ∀ a, le a (neg (neg a))
  le_top : ∀ s, le s top
  le_neg_bot : ∀ s, le s (neg bot)

variable {α : Type} (L : NLat α)

/-- In a bounded lattice (⊥ least, ⊤ greatest) an antitone ¬ with a ≤ ¬¬a already gives the last requirement of `NLat`:
s ≤ ⊤ ≤ ¬¬⊤ ≤ ¬⊥, the last step because ⊥ ≤ ¬⊤. So every bounded lattice with such a negation is one of ours. -/
theorem neg_bot_above {β : Type} (le : β → β → Prop) (neg : β → β) (top bot : β)
    (tr : ∀ {a b c}, le a b → le b c → le a c) (anti : ∀ {a b}, le a b → le (neg b) (neg a))
    (nn : ∀ a, le a (neg (neg a))) (le_top : ∀ s, le s top) (bot_le : ∀ a, le bot a) :
    ∀ s, le s (neg bot) :=
  fun s => tr (le_top s) (tr (nn top) (anti (bot_le (neg top))))

/-- the lattice reading of a kernel formula -/
def qe (val : Nat → α) : Fm → α
  | .atom n    => val n
  | .top       => L.top
  | .bot       => L.bot
  | .neg φ     => L.neg (qe val φ)
  | .conj φ ψ  => L.meet (qe val φ) (qe val ψ)
  | .disj φ ψ  => L.join (qe val φ) (qe val ψ)
  | .imp φ ψ   => L.join (L.neg (qe val φ)) (qe val ψ)
  | .xor φ ψ   => L.join (L.meet (qe val φ) (L.neg (qe val ψ))) (L.meet (L.neg (qe val φ)) (qe val ψ))
  | .xnor φ ψ  => L.join (L.meet (qe val φ) (qe val ψ)) (L.meet (L.neg (qe val φ)) (L.neg (qe val ψ)))

/-! ### order facts -/

theorem neg_join {s x y : α} (hx : L.le s (L.neg x)) (hy : L.le s (L.neg y)) : L.le s (L.neg (L.join x y)) := by
  have m := L.le_meet hx hy
  have ux : L.le x (L.neg (L.meet (L.neg x) (L.neg y))) := L.le_trans (L.le_nn x) (L.anti (L.meet_le_l _ _))
  have uy : L.le y (L.neg (L.meet (L.neg x) (L.neg y))) := L.le_trans (L.le_nn y) (L.anti (L.meet_le_r _ _))
  exact L.le_trans m (L.le_trans (L.le_nn _) (L.anti (L.join_le ux uy)))
/-- refuting the left part refutes the meet -/
theorem neg_meet_l {s x y : α} (hx : L.le s (L.neg x)) : L.le s (L.neg (L.meet x y)) :=
  L.le_trans hx (L.anti (L.meet_le_l _ _))
theorem neg_meet_r {s x y : α} (hy : L.le s (L.neg y)) : L.le s (L.neg (L.meet x y)) :=
  L.le_trans hy (L.anti (L.meet_le_r _ _))
theorem nn {s x : α} (h : L.le s x) : L.le s (L.neg (L.neg x)) := L.le_trans h (L.le_nn _)

/-! ### what the kernel's `comb` says, in sixteen-case checks (a pair is (true reachable, false reachable)) -/

theorem and_E : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x && y) (a, b) (c, d)).2 = false → b = false ∧ d = false := by decide
theorem and_R : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x && y) (a, b) (c, d)).1 = false → a = false ∨ c = false := by decide
theorem or_E : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x || y) (a, b) (c, d)).2 = false → b = false ∨ d = false := by decide
theorem or_R : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x || y) (a, b) (c, d)).1 = false → a = false ∧ c = false := by decide
theorem imp_E : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => !x || y) (a, b) (c, d)).2 = false → a = false ∨ d = false := by decide
theorem imp_R : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => !x || y) (a, b) (c, d)).1 = false → b = false ∧ c = false := by decide
theorem xor_E : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x != y) (a, b) (c, d)).2 = false → (b = false ∧ c = false) ∨ (a = false ∧ d = false) := by decide
theorem xor_R : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x != y) (a, b) (c, d)).1 = false → (b = false ∧ d = false) ∨ (a = false ∧ c = false) := by decide
theorem xnor_E : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x == y) (a, b) (c, d)).2 = false → (b = false ∧ d = false) ∨ (a = false ∧ c = false) := by decide
theorem xnor_R : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    (comb (fun x y => x == y) (a, b) (c, d)).1 = false → (b = false ∧ c = false) ∨ (a = false ∧ d = false) := by decide
/-- some classical value is always reachable (one check per connective: no tactic that brings an axiom) -/
theorem and_ne : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    ((comb (fun x y => x && y) (a, b) (c, d)).1 || (comb (fun x y => x && y) (a, b) (c, d)).2) = true := by decide
theorem or_ne : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    ((comb (fun x y => x || y) (a, b) (c, d)).1 || (comb (fun x y => x || y) (a, b) (c, d)).2) = true := by decide
theorem imp_ne : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    ((comb (fun x y => !x || y) (a, b) (c, d)).1 || (comb (fun x y => !x || y) (a, b) (c, d)).2) = true := by decide
theorem xor_ne : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    ((comb (fun x y => x != y) (a, b) (c, d)).1 || (comb (fun x y => x != y) (a, b) (c, d)).2) = true := by decide
theorem xnor_ne : ∀ a b c d : Bool, (a || b) = true → (c || d) = true →
    ((comb (fun x y => x == y) (a, b) (c, d)).1 || (comb (fun x y => x == y) (a, b) (c, d)).2) = true := by decide
theorem or_swap : ∀ a b : Bool, (a || b) = true → (b || a) = true := by decide

theorem atom_ne : ∀ x : V, ((subs x).contains true || (subs x).contains false) = true := by decide
theorem atom_E : ∀ x : V, (subs x).contains false = false → x = T := by decide
theorem atom_R : ∀ x : V, (subs x).contains true = false → x = F := by decide

/-- what is established agrees with the state -/
def Agrees (s : α) (v : Nat → V) (val : Nat → α) : Prop :=
  ∀ n, (v n = T → L.le s (val n)) ∧ (v n = F → L.le s (L.neg (val n)))

/-- the invariant carried through the formula: a value is reachable; not-false-reachable puts the element above the
state; not-true-reachable puts its negation above the state -/
def Inv (s : α) (p : Bool × Bool) (x : α) : Prop :=
  (p.1 || p.2) = true ∧ (p.2 = false → L.le s x) ∧ (p.1 = false → L.le s (L.neg x))

/-- the marking agrees with the state ON THE ATOMS OF THE FORMULA (other atoms are not looked at) -/
def AgreesOn (s : α) (v : Nat → V) (val : Nat → α) : Fm → Prop
  | .atom n => (v n = T → L.le s (val n)) ∧ (v n = F → L.le s (L.neg (val n)))
  | .top => True
  | .bot => True
  | .neg φ => AgreesOn s v val φ
  | .conj φ ψ => AgreesOn s v val φ ∧ AgreesOn s v val ψ
  | .disj φ ψ => AgreesOn s v val φ ∧ AgreesOn s v val ψ
  | .imp φ ψ => AgreesOn s v val φ ∧ AgreesOn s v val ψ
  | .xor φ ψ => AgreesOn s v val φ ∧ AgreesOn s v val ψ
  | .xnor φ ψ => AgreesOn s v val φ ∧ AgreesOn s v val ψ

theorem agrees_on_of {s : α} {v : Nat → V} {val : Nat → α} (h : Agrees L s v val) : ∀ φ : Fm, AgreesOn L s v val φ
  | .atom n => h n
  | .top => True.intro
  | .bot => True.intro
  | .neg φ => agrees_on_of h φ
  | .conj φ ψ => ⟨agrees_on_of h φ, agrees_on_of h ψ⟩
  | .disj φ ψ => ⟨agrees_on_of h φ, agrees_on_of h ψ⟩
  | .imp φ ψ => ⟨agrees_on_of h φ, agrees_on_of h ψ⟩
  | .xor φ ψ => ⟨agrees_on_of h φ, agrees_on_of h ψ⟩
  | .xnor φ ψ => ⟨agrees_on_of h φ, agrees_on_of h ψ⟩

theorem inv_on (s : α) (v : Nat → V) (val : Nat → α) :
    ∀ φ : Fm, AgreesOn L s v val φ → Inv L s (rd v φ) (qe L val φ) := by
  intro φ
  induction φ with
  | atom n => intro h; exact ⟨atom_ne _, fun e => h.1 (atom_E _ e), fun e => h.2 (atom_R _ e)⟩
  | top => intro _; exact ⟨rfl, fun _ => L.le_top _, fun e => Bool.noConfusion e⟩
  | bot => intro _; exact ⟨rfl, fun e => Bool.noConfusion e, fun _ => L.le_neg_bot _⟩
  | neg φ ih =>
    intro h
    obtain ⟨n, e, r⟩ := ih h
    exact ⟨or_swap _ _ n, fun k => r k, fun k => nn L (e k)⟩
  | conj φ ψ ih1 ih2 =>
    intro h
    obtain ⟨n1, e1, r1⟩ := ih1 h.1; obtain ⟨n2, e2, r2⟩ := ih2 h.2
    refine ⟨and_ne _ _ _ _ n1 n2, fun k => ?_, fun k => ?_⟩
    · have := and_E _ _ _ _ n1 n2 k; exact L.le_meet (e1 this.1) (e2 this.2)
    · cases and_R _ _ _ _ n1 n2 k with
      | inl a => exact neg_meet_l L (r1 a)
      | inr a => exact neg_meet_r L (r2 a)
  | disj φ ψ ih1 ih2 =>
    intro h
    obtain ⟨n1, e1, r1⟩ := ih1 h.1; obtain ⟨n2, e2, r2⟩ := ih2 h.2
    refine ⟨or_ne _ _ _ _ n1 n2, fun k => ?_, fun k => ?_⟩
    · cases or_E _ _ _ _ n1 n2 k with
      | inl a => exact L.le_trans (e1 a) (L.le_join_l _ _)
      | inr a => exact L.le_trans (e2 a) (L.le_join_r _ _)
    · have := or_R _ _ _ _ n1 n2 k; exact neg_join L (r1 this.1) (r2 this.2)
  | imp φ ψ ih1 ih2 =>
    intro h
    obtain ⟨n1, e1, r1⟩ := ih1 h.1; obtain ⟨n2, e2, r2⟩ := ih2 h.2
    refine ⟨imp_ne _ _ _ _ n1 n2, fun k => ?_, fun k => ?_⟩
    · cases imp_E _ _ _ _ n1 n2 k with
      | inl a => exact L.le_trans (r1 a) (L.le_join_l _ _)
      | inr a => exact L.le_trans (e2 a) (L.le_join_r _ _)
    · have := imp_R _ _ _ _ n1 n2 k; exact neg_join L (nn L (e1 this.1)) (r2 this.2)
  | xor φ ψ ih1 ih2 =>
    intro h
    obtain ⟨n1, e1, r1⟩ := ih1 h.1; obtain ⟨n2, e2, r2⟩ := ih2 h.2
    refine ⟨xor_ne _ _ _ _ n1 n2, fun k => ?_, fun k => ?_⟩
    · cases xor_E _ _ _ _ n1 n2 k with
      | inl a => exact L.le_trans (L.le_meet (e1 a.1) (r2 a.2)) (L.le_join_l _ _)
      | inr a => exact L.le_trans (L.le_meet (r1 a.1) (e2 a.2)) (L.le_join_r _ _)
    · cases xor_R _ _ _ _ n1 n2 k with
      | inl a => exact neg_join L (neg_meet_r L (nn L (e2 a.2))) (neg_meet_l L (nn L (e1 a.1)))
      | inr a => exact neg_join L (neg_meet_l L (r1 a.1)) (neg_meet_r L (r2 a.2))
  | xnor φ ψ ih1 ih2 =>
    intro h
    obtain ⟨n1, e1, r1⟩ := ih1 h.1; obtain ⟨n2, e2, r2⟩ := ih2 h.2
    refine ⟨xnor_ne _ _ _ _ n1 n2, fun k => ?_, fun k => ?_⟩
    · cases xnor_E _ _ _ _ n1 n2 k with
      | inl a => exact L.le_trans (L.le_meet (e1 a.1) (e2 a.2)) (L.le_join_l _ _)
      | inr a => exact L.le_trans (L.le_meet (r1 a.1) (r2 a.2)) (L.le_join_r _ _)
    · cases xnor_R _ _ _ _ n1 n2 k with
      | inl a => exact neg_join L (neg_meet_r L (r2 a.2)) (neg_meet_l L (nn L (e1 a.1)))
      | inr a => exact neg_join L (neg_meet_l L (r1 a.1)) (neg_meet_r L (nn L (e2 a.2)))

theorem inv (s : α) (v : Nat → V) (val : Nat → α) (h : Agrees L s v val) :
    ∀ φ : Fm, Inv L s (rd v φ) (qe L val φ) := fun φ => inv_on L s v val φ (agrees_on_of L h φ)

/-- QZ 3a, looking only at the atoms of the formula. -/
theorem earned_sound_on (s : α) (v : Nat → V) (val : Nat → α) (φ : Fm) (h : AgreesOn L s v val φ)
    (e : earnedR v φ) : L.le s (qe L val φ) := (inv_on L s v val φ h).2.1 e

/-- QZ 3b, looking only at the atoms of the formula. -/
theorem refuted_sound_on (s : α) (v : Nat → V) (val : Nat → α) (φ : Fm) (h : AgreesOn L s v val φ)
    (r : refutedR v φ) : L.le s (L.neg (qe L val φ)) := (inv_on L s v val φ h).2.2 r

/-- **QZ 3a.** What the kernel calls EARNED lies above the state, in every such lattice. -/
theorem earned_sound (s : α) (v : Nat → V) (val : Nat → α) (h : Agrees L s v val) (φ : Fm)
    (e : earnedR v φ) : L.le s (qe L val φ) := (inv L s v val h φ).2.1 e

/-- **QZ 3b.** What the kernel calls REFUTED has its negation above the state, in every such lattice. -/
theorem refuted_sound (s : α) (v : Nat → V) (val : Nat → α) (h : Agrees L s v val) (φ : Fm)
    (r : refutedR v φ) : L.le s (L.neg (qe L val φ)) := (inv L s v val h φ).2.2 r

/-! ### the class is not empty: the smallest quantum lattice MO2 is such a lattice -/

inductive Q | bot | top | a | a' | b | b'
  deriving DecidableEq

instance (p : Q → Prop) [DecidablePred p] : Decidable (∀ x : Q, p x) :=
  decidable_of_iff (p .bot ∧ p .top ∧ p .a ∧ p .a' ∧ p .b ∧ p .b')
    ⟨fun ⟨h0,h1,h2,h3,h4,h5⟩ x => by cases x <;> assumption,
     fun h => ⟨h .bot, h .top, h .a, h .a', h .b, h .b'⟩⟩

def qneg : Q → Q
  | .bot => .top | .top => .bot | .a => .a' | .a' => .a | .b => .b' | .b' => .b
def qmeet (x y : Q) : Q :=
  if x = y then x else if x = .bot ∨ y = .bot then .bot else if x = .top then y else if y = .top then x else .bot
def qjoin (x y : Q) : Q := qneg (qmeet (qneg x) (qneg y))
def qle (x y : Q) : Prop := qmeet x y = x
instance (x y : Q) : Decidable (qle x y) := inferInstanceAs (Decidable (qmeet x y = x))

/-- MO2 (two contexts, non-distributive) satisfies every requirement of the theorem. -/
def mo2 : NLat Q where
  le := qle
  meet := qmeet
  join := qjoin
  neg := qneg
  top := .top
  bot := .bot
  le_trans := by intro x y z; revert x y z; decide
  meet_le_l := by decide
  meet_le_r := by decide
  le_meet := by intro s x y; revert s x y; decide
  le_join_l := by decide
  le_join_r := by decide
  join_le := by intro x y z; revert x y z; decide
  anti := by intro x y; revert x y; decide
  le_nn := by decide
  le_top := by decide
  le_neg_bot := by decide

end QZ3

#print axioms QZ3.earned_sound
#print axioms QZ3.refuted_sound
#print axioms QZ3.earned_sound_on
#print axioms QZ3.refuted_sound_on
#print axioms QZ3.mo2
#print axioms QZ3.neg_bot_above
