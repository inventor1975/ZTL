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

  READING, not proved: the axiom of choice — whose content is infinite families; one pick from a non-empty set needs no
  axiom — is then the stipulation of stability on unknown picks, infinitely many at once. Proved here, finite lists X:
  1. `earned_stable` — earned implies earned if stable;
  2. `invariant_earned` — a property true of every element of X is earned of the pick, under every reading (a sanity
     check of the encoding);
  3. `same_pick` — "both uses denote the same element" is earned if stable and NOT earned, once X has two elements:
     a construction like Banach–Tarski uses one set of representatives in every piece, which is this kind (a reading);
  4. `which_pick` — "the pick is this element" is not earned even if stable, and not refuted: OPEN;
  5. `finite_choice` — choosing from finitely many non-empty lists needs no axiom: take each list's first element (the
     list's order does the choosing; an unordered finite set needs an enumeration first).
  6. `choice_by_rule`, `choice_sequence` — choosing from ANY family of non-empty lists, infinite or uncountable index
     set included, needs no axiom either: the line is not finite/infinite but GIVEN/ONLY-ASSERTED. The axiom is needed
     where no rule picks from every member (Russell's socks); for arbitrary families it is unprovable — ZF: Cohen
     1963; Lean's `Classical.choice`: a separate result about type theory — cited. Close to trivial: a list's
     order does the choosing.
  What is NOT here: families with no rule picking from them (there the axiom is needed, and Banach–Tarski is its cost —
  `dilemmas/banach_tarski.py`). The link to the judge's IF STABLE is the definition (`ZDirty`'s stable completion: one value at
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

/-- The head of a non-empty list. -/
def pick {α : Type} : (l : List α) → l ≠ [] → α
  | [], h => absurd rfl h
  | a :: _, _ => a

theorem pick_mem {α : Type} : ∀ (l : List α) (h : l ≠ []), List.Mem (pick l h) l
  | [], h => absurd rfl h
  | _ :: t, _ => List.Mem.head t

/-- Choice from ANY family of lists given as a function — infinite, even uncountable, index sets included — needs no
axiom: a list carries an order, and the order does the choosing, so no choice principle is involved (close to
trivial). (2026-11-06, the curator: "на бесконечных мы только намекаем?") The point is Russell's shoes and socks:
what decides is whether a rule picks from every member, given with the family or definable from it, not finite
against infinite. Where no rule exists the axiom supplies the picks; that it cannot be proved there is, for ZF,
Cohen 1963 (with Gödel 1938 for consistency), and for Lean's `Classical.choice` a separate known result about type
theory — both cited, not proved here. -/
theorem choice_by_rule {ι α : Type} (L : ι → List α) (h : ∀ i, L i ≠ []) :
    ∃ f : ι → α, ∀ i, List.Mem (f i) (L i) :=
  ⟨fun i => pick (L i) (h i), fun i => pick_mem (L i) (h i)⟩

/-- The infinite case written out: a choice function for a sequence of non-empty lists, no axiom. -/
theorem choice_sequence {α : Type} (L : Nat → List α) (h : ∀ n, L n ≠ []) :
    ∃ f : Nat → α, ∀ n, List.Mem (f n) (L n) :=
  choice_by_rule L h

end ZChoiceRead

#print axioms ZChoiceRead.earned_stable
#print axioms ZChoiceRead.invariant_earned
#print axioms ZChoiceRead.same_pick
#print axioms ZChoiceRead.which_pick
#print axioms ZChoiceRead.finite_choice
#print axioms ZChoiceRead.pick_mem
#print axioms ZChoiceRead.choice_by_rule
#print axioms ZChoiceRead.choice_sequence
