/-
  ZEpsilon.lean — Hilbert's ε read in ZTL: an ideal element is a stable unchecked pick, and what is earned of it is
  exactly what an ε-free statement says. Zero axioms.

  WHY (2026-11-06, the curator: "сопоставь"). Hilbert's ε-term (introduced in the early 1920s; Ackermann and von Neumann
  on its elimination in the 1920s) is a choice principle in the logic: εx.P(x), some x with P if there is one, governed
  by the critical axiom P(t) → P(εx.P(x)). The epsilon theorems (Hilbert and Bernays, Grundlagen der Mathematik II,
  1939) show, under conditions (an ε-free conclusion and ε-free non-logical axioms), that what is derivable with ε-terms
  is derivable without them: the ideal elements can be eliminated from proofs. Read in ZTL (ZChoiceRead), the ε-term is a pick no one exhibits,
  an unchecked value, used stably and constrained by the critical axiom. What can be earned of it?

  The finite face, proved here on a list X (a finite domain given in some order):
  * `Admissible X P e` — e is in X and obeys the critical axiom: if some element of X has P, so does e.
  * `eps_iff_exists` — "P(ε) holds for every admissible ε" exactly when some element of X has P: the classical
    definition ∃x P(x) ≡ P(εx.P(x)), read semantically; for a non-empty list and a COMPUTABLE P (Bool-valued) the
    witness is FOUND by a search, not posited — no excluded middle is used (for non-computable P the critical axiom
    is known to bring the excluded middle with it).
  * `eps_which_open` — what the ε-term is, beyond what P fixes, is not earned: for X = [0, 1] and P true of both, "ε is
    0" holds at one admissible pick and fails at the other.
  * `eps_needs_stable` — two uses of one ε-term denote the same element only if the pick is read stably (the judge's
    IF STABLE): read independently, two admissible picks can differ.
  NOT here: the epsilon theorems themselves (a proof-theoretic result about derivations); this file proves their
  semantic shadow on a finite domain — an ε-statement earned for every admissible pick says no more than an ε-free one.
-/
namespace ZEpsilon

/-- The critical axiom, read as a constraint on the pick. -/
def Admissible {α : Type} (X : List α) (P : α → Bool) (e : α) : Prop :=
  List.Mem e X ∧ ((∃ a, List.Mem a X ∧ P a = true) → P e = true)

/-- A search: the first element of the list with P, if any. -/
def search {α : Type} (P : α → Bool) : List α → Option α
  | [] => none
  | a :: t => match P a with
    | true => some a
    | false => search P t

theorem search_some {α : Type} (P : α → Bool) :
    ∀ (X : List α) (a : α), search P X = some a → List.Mem a X ∧ P a = true
  | [], _, h => by cases h
  | x :: t, a, h => by
      cases hx : P x with
      | true =>
          have h' : search P (x :: t) = some x := by
            show (match P x with | true => some x | false => search P t) = some x
            rw [hx]
          rw [h'] at h
          cases h
          exact ⟨List.Mem.head t, hx⟩
      | false =>
          have h' : search P (x :: t) = search P t := by
            show (match P x with | true => some x | false => search P t) = search P t
            rw [hx]
          rw [h'] at h
          obtain ⟨hm, hp⟩ := search_some P t a h
          exact ⟨List.Mem.tail x hm, hp⟩

theorem search_none {α : Type} (P : α → Bool) :
    ∀ (X : List α), search P X = none → ∀ a, List.Mem a X → P a = false
  | [], _, _, hm => nomatch hm
  | x :: t, h, a, hm => by
      cases hx : P x with
      | true =>
          have h' : search P (x :: t) = some x := by
            show (match P x with | true => some x | false => search P t) = some x
            rw [hx]
          rw [h'] at h
          cases h
      | false =>
          have h' : search P (x :: t) = search P t := by
            show (match P x with | true => some x | false => search P t) = search P t
            rw [hx]
          rw [h'] at h
          cases hm with
          | head => exact hx
          | tail _ hm' => exact search_none P t h a hm'

/-- P(ε) for every admissible ε exactly when a witness exists — found by search, on a non-empty list. -/
theorem eps_iff_exists {α : Type} (X : List α) (P : α → Bool) (x0 : α) (h0 : List.Mem x0 X) :
    (∀ e, Admissible X P e → P e = true) ↔ (∃ a, List.Mem a X ∧ P a = true) := by
  constructor
  · intro h
    cases hs : search P X with
    | some a => exact ⟨a, search_some P X a hs⟩
    | none =>
        have hall := search_none P X hs
        have hx0 : P x0 = true := h x0 ⟨h0, fun ⟨a, ha, hpa⟩ => absurd hpa (by rw [hall a ha]; decide)⟩
        exact absurd hx0 (by rw [hall x0 h0]; decide)
  · intro hex e he
    exact he.2 hex

/-- Two elements, 0 and 1, both with P. -/
def two : List Nat := [0, 1]

theorem mem0 : List.Mem 0 two := List.Mem.head _
theorem mem1 : List.Mem 1 two := List.Mem.tail _ (List.Mem.head _)

/-- Both 0 and 1 are admissible for P = "anything": the critical axiom does not fix which. -/
theorem eps_which_open :
    Admissible two (fun _ => true) 0 ∧ Admissible two (fun _ => true) 1 ∧
    decide ((0 : Nat) = 0) = true ∧ decide ((1 : Nat) = 0) = false :=
  ⟨⟨mem0, fun _ => rfl⟩, ⟨mem1, fun _ => rfl⟩, rfl, rfl⟩

/-- Two uses of one ε, read independently, can be two different admissible picks. -/
theorem eps_needs_stable :
    ∃ e₁ e₂, Admissible two (fun _ => true) e₁ ∧ Admissible two (fun _ => true) e₂ ∧ e₁ ≠ e₂ :=
  ⟨0, 1, ⟨mem0, fun _ => rfl⟩, ⟨mem1, fun _ => rfl⟩, by decide⟩

end ZEpsilon

#print axioms ZEpsilon.search_some
#print axioms ZEpsilon.search_none
#print axioms ZEpsilon.eps_iff_exists
#print axioms ZEpsilon.eps_which_open
#print axioms ZEpsilon.eps_needs_stable
