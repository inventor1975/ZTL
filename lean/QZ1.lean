/-!
# QZ, theorem 1 — a strict verdict is the lattice's verdict too (MO2). Written with AI, 2026-11-27.

Bare Lean 4, no imports.   lean research/qz/QZ1.lean

MO2 is the smallest quantum (orthomodular, non-distributive) lattice: ⊥, ⊤ and two contexts {a, a'}, {b, b'}.
A formula over the atoms a, b is read twice:

  * in the LATTICE: ¬ ∧ ∨ are orthocomplement, meet, join; in a state `s` the formula is true when `s ≤ x`
    and false when `s ≤ x'`;
  * by STRICT three-valued evaluation (strong Kleene): an atom is T, F or U (not established), and a compound is
    T or F only when that is forced whatever the U's turn out to be. MEASURED 2026-11-27 on the 1208 judgements of
    `research/qz/mo2_probe.py`: strict T is exactly the judge's EARNED (302 of 302) and strict F exactly its REFUTED
    (302 of 302); every other disposition reads U. The general identity is ZTL's own matter (`lean/ZDirty.lean`
    there), not imported and not re-proved here.

THEOREM (`strict_sound`). Let the established atoms agree with the state (an atom marked T lies above the state,
an atom marked F has its complement above the state). Then for EVERY formula: strict T gives lattice-true, strict
F gives lattice-false. No condition on which contexts the formula mixes.

The converse is false (`converse_fails`): the lattice decides `a ∧ b` (it is ⊥) while the strict reading leaves it
open — the lattice knows that the two contexts exclude each other, the three-valued reading does not.

Boundary: proved for MO2 only. The proof uses nothing but the seven order facts below, so the same argument is
expected for any ortholattice; that is argued, not proved here. The enumeration behind it: `research/qz/mo2_probe.py`.
-/

namespace QZ1

inductive Q | bot | top | a | a' | b | b'
  deriving DecidableEq

open Q

def neg : Q → Q
  | bot => top | top => bot | a => a' | a' => a | b => b' | b' => b

/-- Meet: equal → itself; ⊥ absorbs; ⊤ is unit; two distinct middle elements → ⊥. (If-chains on purpose: a `match`
with overlapping patterns drags `propext` into every `decide` that touches it.) -/
def meet (x y : Q) : Q :=
  if x = y then x
  else if x = bot ∨ y = bot then bot
  else if x = top then y
  else if y = top then x
  else bot

def join (x y : Q) : Q := neg (meet (neg x) (neg y))

def leq (x y : Q) : Bool := meet x y == x

/-- Enumeration of the six elements is decidable — every `decide` below lives on this. -/
instance (p : Q → Prop) [DecidablePred p] : Decidable (∀ x : Q, p x) :=
  decidable_of_iff (p bot ∧ p top ∧ p a ∧ p a' ∧ p b ∧ p b')
    ⟨fun ⟨h0,h1,h2,h3,h4,h5⟩ x => by cases x <;> assumption,
     fun h => ⟨h bot, h top, h a, h a', h b, h b'⟩⟩

/-! ### the seven order facts (each: 216 cases, checked by the kernel) -/

theorem meet_glb : ∀ s x y, leq s x = true → leq s y = true → leq s (meet x y) = true := by decide
theorem neg_meet_l : ∀ s x y, leq s (neg x) = true → leq s (neg (meet x y)) = true := by decide
theorem neg_meet_r : ∀ s x y, leq s (neg y) = true → leq s (neg (meet x y)) = true := by decide
theorem join_ub_l : ∀ s x y, leq s x = true → leq s (join x y) = true := by decide
theorem join_ub_r : ∀ s x y, leq s y = true → leq s (join x y) = true := by decide
theorem neg_join : ∀ s x y, leq s (neg x) = true → leq s (neg y) = true → leq s (neg (join x y)) = true := by decide
theorem neg_neg : ∀ s x, leq s x = true → leq s (neg (neg x)) = true := by decide

/-! ### the strict three-valued reading -/

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

/-! ### formulas -/

inductive Fm
  | A | B
  | not (f : Fm)
  | and (f g : Fm)
  | or (f g : Fm)

/-- the lattice reading -/
def qe : Fm → Q
  | .A => a | .B => b
  | .not f => neg (qe f)
  | .and f g => meet (qe f) (qe g)
  | .or f g => join (qe f) (qe g)

/-- the strict reading, from what is established about the two atoms -/
def ke (ka kb : K) : Fm → K
  | .A => ka | .B => kb
  | .not f => kneg (ke ka kb f)
  | .and f g => kand (ke ka kb f) (ke ka kb g)
  | .or f g => kor (ke ka kb f) (ke ka kb g)

/-- what is established agrees with the state -/
def Agrees (s : Q) (k : K) (x : Q) : Prop :=
  (k = T → leq s x = true) ∧ (k = F → leq s (neg x) = true)

/-- **QZ 1.** A strict verdict is the lattice's verdict, for every formula. -/
theorem strict_sound (s : Q) (ka kb : K) (ha : Agrees s ka a) (hb : Agrees s kb b) :
    ∀ f : Fm, Agrees s (ke ka kb f) (qe f) := by
  intro f
  induction f with
  | A => exact ha
  | B => exact hb
  | not f ih =>
    constructor
    · intro h; exact ih.2 (kneg_T _ h)
    · intro h; exact neg_neg _ _ (ih.1 (kneg_F _ h))
  | and f g ihf ihg =>
    constructor
    · intro h
      have := kand_T _ _ h
      exact meet_glb _ _ _ (ihf.1 this.1) (ihg.1 this.2)
    · intro h
      cases kand_F _ _ h with
      | inl h1 => exact neg_meet_l _ _ _ (ihf.2 h1)
      | inr h2 => exact neg_meet_r _ _ _ (ihg.2 h2)
  | or f g ihf ihg =>
    constructor
    · intro h
      cases kor_T _ _ h with
      | inl h1 => exact join_ub_l _ _ _ (ihf.1 h1)
      | inr h2 => exact join_ub_r _ _ _ (ihg.1 h2)
    · intro h
      have := kor_F _ _ h
      exact neg_join _ _ _ (ihf.2 this.1) (ihg.2 this.2)

/-- The run "a was asked and answered yes, b was not asked": the premise of the theorem holds. -/
theorem run_a_yes : Agrees a T a ∧ Agrees a U b :=
  ⟨⟨fun _ => by decide, fun h => K.noConfusion h⟩, ⟨fun h => K.noConfusion h, fun h => K.noConfusion h⟩⟩

/-- **The converse fails.** In that run the lattice refutes `a ∧ b` (its value is ⊥), the strict reading leaves it
open. -/
theorem converse_fails :
    leq a (neg (qe (.and .A .B))) = true ∧ ke T U (.and .A .B) = U := by decide

/-- **Where "true on every stable reading" is not the lattice's truth.** `¬b ∨ (a ∧ b)` with a answered yes is true
whether b is taken as T or as F, yet its lattice value is b', which the state a neither lies under nor excludes. -/
theorem stable_is_not_lattice :
    ke T T (.or (.not .B) (.and .A .B)) = T ∧ ke T F (.or (.not .B) (.and .A .B)) = T ∧
    qe (.or (.not .B) (.and .A .B)) = b' ∧ leq a b' = false ∧ leq a (neg b') = false := by decide

/-- **The lattice can REFUTE what every stable reading earns.** `((a ∧ b) ∨ ¬b) ∧ a` with a answered yes is true
whether b is taken as T or as F, and the strict reading leaves it open - yet its lattice value is ⊥: in the state a
it is false. The judge's "EARNED IF STABLE" names the condition under which it would hold; the lattice denies the
condition. (Found by `research/qz/depth3_probe.py`: 4576 such cases among 729640 at depth 3, none at depth 2.) -/
theorem stable_refuted_by_lattice :
    let f : Fm := .and (.or (.and .A .B) (.not .B)) .A
    ke T T f = T ∧ ke T F f = T ∧ ke T U f = U ∧ qe f = bot ∧ leq a (neg (qe f)) = true := by decide

end QZ1

#print axioms QZ1.strict_sound
#print axioms QZ1.converse_fails
#print axioms QZ1.stable_is_not_lattice
#print axioms QZ1.run_a_yes
#print axioms QZ1.stable_refuted_by_lattice
