/-
  ZChoiceRead.lean — the axiom of choice read in ZTL: a pick is a dirty value used STABLY. Zero axioms.

  THE READING (2026-11-06, the curator: "AC делает выбор и возвращает грязный параметр… отдаёт решать логике, что оно
  на самом деле"; corrected in the conversation: the logic does not decide what the pick IS — it earns only what holds
  for every possible pick — and the pick of choice is not ZTL's default dirty value, read anew at each occurrence, but
  a STABLE one, the same at every use). A choice from a set X returns an element nobody can exhibit: to ZTL a value no
  one checked, Z. What can be earned about it is decided per claim, over the readings of its occurrences:

    EARNED                true whatever element each occurrence is read as (the dirty reading);
    EARNED IF STABLE      true whenever every occurrence is read as the SAME element (the stable reading);
    neither               true for some picks and false for others — OPEN.

  So the axiom of choice, read in ZTL, is the stipulation of stability on an unknown pick. Proved here, finite X:
  1. `earned_stable` — earned implies earned if stable;
  2. `invariant_earned` — a property true of every element of X is earned of the pick, under every reading;
  3. `same_pick` — "both uses denote the same element" is earned if stable and NOT earned, once X has two elements:
     what a construction like Banach–Tarski needs (the same representatives in every piece) is exactly this kind;
  4. `which_pick` — "the pick is this element" is not earned even if stable, and not refuted: OPEN;
  5. `finite_choice` — choosing from finitely many non-empty lists needs no axiom: take each list's first element.
  What is NOT here: infinite families (there the axiom is needed, and Banach–Tarski is its cost — `dilemmas/
  banach_tarski.py`). The link to the judge's IF STABLE is the definition (`ZDirty`'s stable completion: one value at
  every occurrence), mirrored, not imported.
-/
namespace ZChoiceRead

/-- A claim about two uses of the pick, as a test on the two elements they are read as. -/
def Earned {α : Type} (X : List α) (φ : α → α → Bool) : Prop :=
  ∀ a, List.Mem a X → ∀ b, List.Mem b X → φ a b = true

/-- The stable reading: both uses are the same element. -/
def EarnedIfStable {α : Type} (X : List α) (φ : α → α → Bool) : Prop :=
  ∀ a, List.Mem a X → φ a a = true

/-- Refuted if stable: false at every stable reading. -/
def RefutedIfStable {α : Type} (X : List α) (φ : α → α → Bool) : Prop :=
  ∀ a, List.Mem a X → φ a a = false

theorem earned_stable {α : Type} (X : List α) (φ : α → α → Bool) (h : Earned X φ) : EarnedIfStable X φ :=
  fun a ha => h a ha a ha

/-- A property of every element is earned of the pick, read anyhow. -/
theorem invariant_earned {α : Type} (X : List α) (P : α → Bool) (h : ∀ a, List.Mem a X → P a = true) :
    Earned X (fun a _ => P a) :=
  fun a ha _ _ => h a ha

/-- Two elements, 0 and 1. -/
def two : List Nat := [0, 1]

/-- "Both uses denote the same element". -/
def same (a b : Nat) : Bool := decide (a = b)

theorem mem0 : List.Mem 0 two := List.Mem.head _
theorem mem1 : List.Mem 1 two := List.Mem.tail _ (List.Mem.head _)

/-- Earned if stable — and not earned: read independently, the two uses can be 0 and 1. -/
theorem same_pick : EarnedIfStable two same ∧ ¬ Earned two same := by
  refine ⟨?_, ?_⟩
  · intro a _
    show decide (a = a) = true
    exact decide_eq_true rfl
  · intro h
    have h01 : same 0 1 = true := h 0 mem0 1 mem1
    exact absurd h01 (by decide)

/-- "The pick is 0": true at one stable reading, false at another — neither earned nor refuted, even if stable. -/
theorem which_pick :
    ¬ EarnedIfStable two (fun a _ => decide (a = 0)) ∧ ¬ RefutedIfStable two (fun a _ => decide (a = 0)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : decide (1 = 0) = true := h 1 mem1
    exact absurd h1 (by decide)
  · intro h
    have h0 : decide (0 = 0) = false := h 0 mem0
    exact absurd h0 (by decide)

/-- The first element of a list, or `d` for the empty list. -/
def firstOr {α : Type} (d : α) : List α → α
  | [] => d
  | a :: _ => a

theorem firstOr_mem {α : Type} (d : α) : ∀ L : List α, L ≠ [] → List.Mem (firstOr d L) L
  | [], h => absurd rfl h
  | _ :: t, _ => List.Mem.head t

/-- Finite choice is a theorem: from finitely many non-empty lists, a choice function exists, built, not posited. -/
theorem finite_choice {α : Type} (d : α) (Ls : List (List α)) (h : ∀ L, List.Mem L Ls → L ≠ []) :
    ∃ f : List α → α, ∀ L, List.Mem L Ls → List.Mem (f L) L :=
  ⟨firstOr d, fun L hL => firstOr_mem d L (h L hL)⟩

end ZChoiceRead

#print axioms ZChoiceRead.earned_stable
#print axioms ZChoiceRead.invariant_earned
#print axioms ZChoiceRead.same_pick
#print axioms ZChoiceRead.which_pick
#print axioms ZChoiceRead.finite_choice
