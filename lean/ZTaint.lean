/-
  ZTaint.lean — E40: THE LAUNDERING BAN, AND WHEN CARDINALITY IS EARNED.

  Two claims that §§12 and 14 measured on worked cases, proved in general.

  1. NO FUNCTION LAUNDERS A MARK (§14). A function is a computation, not a
     verdict; applied to an unverified reference it returns an unverified
     reference with a longer pedigree, and no composition of any length
     changes that. In security terms this is no-declassification: the only
     sanitizer is external verification of the value, which is a
     SUBSTITUTION of the element and not an application of anything.

     §14 named this as one of five claims and measured it. The other four —
     image multiplicity, associativity of composition at representation
     level, the preimage split, and the merge of verified collisions — stay
     measured, and §14 still says so.

  2. CARDINALITY IS EARNED EXACTLY TWICE (§12). The count of a set with a
     verified core and a quarantine of marks is an interval; §12 exhibits
     four instances, including the striking |{Z}| = [1,1] — one mark is
     exactly one thing, so cardinality can be earned where identity cannot.
     Here the general law: the interval collapses to a point precisely when
     there are NO marks, or when there is exactly one mark and no verified
     core. Two marks are not two things.

  ФОРМА. `ZSets.cardLo` считается через `if`; здесь стоит его развёртка по
  образцам, и её совпадение с оригиналом ДОКАЗАНО, а не предположено —
  иначе теорема была бы о моей собственной записи, а не о том, что в корпусе.
-/
import ZExped

namespace ZTaint

open V

/-! ### 1. The laundering ban -/

def isMark : El → Bool
  | El.v _ => false
  | El.z _ => true

/-- Applying a chain of functions, outermost last. -/
def taints : List (Nat → Nat) → El → El
  | [],     x => x
  | f :: r, x => taint f (taints r x)

/-- **NO COMPOSITION LAUNDERS.** Whatever chain of verified functions is
applied to an unverified reference, the result is an unverified reference.
The pedigree grows; the mark never comes off. -/
theorem no_laundering : ∀ (fs : List (Nat → Nat)) (i : Nat),
    ∃ j, taints fs (El.z i) = El.z j
  | [],     i => ⟨i, rfl⟩
  | f :: r, i =>
      match no_laundering r i with
      | ⟨j, hj⟩ => ⟨j + 1, by
          show taint f (taints r (El.z i)) = El.z (j + 1)
          rw [hj]; rfl⟩

/-- The same, as the Bool the instruments read. -/
theorem no_laundering_mark (fs : List (Nat → Nat)) (i : Nat) :
    isMark (taints fs (El.z i)) = true :=
  match no_laundering fs i with
  | ⟨_, hj⟩ => by rw [hj]; rfl

/-- And the sanitizer is not an application at all: a verified value is a
different ELEMENT, put there by an act of checking. -/
theorem sanitizer_is_substitution (n : Nat) : isMark (El.v n) = false := rfl

/-! ### 2. When the count is earned -/

/-- `ZSets.cardLo` without the `if`. Agreement with the original is proved
below, so what follows is a theorem about the corpus and not about this
restatement. -/
def cardLo' : Nat → Nat → Nat
  | 0,     0     => 0
  | 0,     _ + 1 => 1
  | c + 1, _     => c + 1

def cardHi' (core quar : Nat) : Nat := core + quar

theorem cardLo_agrees : ∀ c q, V.cardLo c q = cardLo' c q
  | 0,     0     => rfl
  | 0,     1     => rfl
  | 0,     _ + 2 => rfl
  | _ + 1, _     => rfl

theorem cardHi_agrees : ∀ c q, V.cardHi c q = cardHi' c q :=
  fun _ _ => rfl

theorem self_add_eq : ∀ (n m : Nat), n = n + m → m = 0
  | 0,     m, h => by rw [Nat.zero_add] at h; exact h.symm
  | n + 1, m, h => self_add_eq n m (Nat.succ.inj (by
      rw [Nat.succ_add] at h; exact h))

/-- **CARDINALITY IS EARNED EXACTLY TWICE.** The interval collapses to a
point precisely when there are no marks at all, or exactly one mark over an
empty verified core. One mark is exactly one thing; two marks are not two
things. -/
theorem card_earned_iff : ∀ c q : Nat,
    cardLo' c q = cardHi' c q ↔ (q = 0 ∨ (c = 0 ∧ q = 1))
  | 0,     0     => ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | 0,     1     => ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => rfl⟩
  | 0,     q + 2 => by
      constructor
      · intro h
        -- lo = 1, hi = q + 2; equality would make 1 = q + 2
        have h1 : (1 : Nat) = 0 + (q + 2) := h
        rw [Nat.zero_add] at h1
        exact Nat.noConfusion (Nat.succ.inj h1)
      · intro h
        cases h with
        | inl hq => exact Nat.noConfusion hq
        | inr hc => exact Nat.noConfusion (Nat.succ.inj hc.2)
  | c + 1, 0     => ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | c + 1, q + 1 => by
      constructor
      · intro h
        have : q + 1 = 0 := self_add_eq (c + 1) (q + 1) h
        exact Nat.noConfusion this
      · intro h
        cases h with
        | inl hq => exact Nat.noConfusion hq
        | inr hc => exact Nat.noConfusion hc.1

/-- The four instances §12 exhibits, now consequences rather than samples. -/
theorem card_instances :
    (cardLo' 2 0 = 2 ∧ cardHi' 2 0 = 2)
  ∧ (cardLo' 2 1 = 2 ∧ cardHi' 2 1 = 3)
  ∧ (cardLo' 0 1 = 1 ∧ cardHi' 0 1 = 1)
  ∧ (cardLo' 0 2 = 1 ∧ cardHi' 0 2 = 2) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end ZTaint

#print axioms ZTaint.no_laundering
#print axioms ZTaint.no_laundering_mark
#print axioms ZTaint.cardLo_agrees
#print axioms ZTaint.self_add_eq
#print axioms ZTaint.card_earned_iff
#print axioms ZTaint.card_instances
