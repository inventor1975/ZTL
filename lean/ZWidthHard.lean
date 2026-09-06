/-
  ZWidthHard.lean — E58: THE WIDTH OF AN INQUIRY IS NP-HARD TO KNOW.

  §19 defines the WIDTH of an unsettled claim: the smallest number of
  unverified grounds whose JOINT verification moves the verdict — width 1 is
  ordinary step-by-step inquiry, width ≥ 2 means no single check helps, and
  no width at all (nothing moves it) is the hereditary grade. The judge
  reports `joint` and deliberately does not compute the exact width: "that
  search is exponential in the number of marks". This file says the
  restraint is forced, not chosen.

  THE SAME WITNESS AS E57. `Φ_ψ = G_{n+1} → ψ`, with `G` the excluded-middle
  guard on the first n+1 atoms, at the all-marked start:

    * NOTHING SHORT OF THE WHOLE GUARD MOVES IT (`no_move_below`): a
      refinement that leaves any guarded atom marked keeps the guard F and
      the verdict T. So any moving set contains all n+1 guarded atoms, and
      has at least n+1 members.
    * THE WHOLE GUARD MOVES IT EXACTLY WHEN ψ CAN FAIL (`width_iff_refutable`):
      filling the n+1 atoms with a classical point c gives `T → ψ(c)`; it is
      F — a move — iff ψ(c) ≠ T.

  So the width of `Φ_ψ` is n+1 if ψ has a falsifying point and undefined if
  ψ is a tautology — never anything else. "Is the width ≤ k?" is therefore
  NP-HARD: the witness turns SAT(¬ψ) into "width ≤ n+1", and that reduction
  is the whole content of the two theorems above (the one prose step over
  them: the witness has the size of ψ plus n+1). The exact width cannot be
  had cheaply unless P = NP; width 1 can (`joint`: 2m evaluations), and
  that is the cut the judge already makes.

  CLAIM GRADE. NP-hard is the claim. Membership in NP — a moving set with
  its values would be a certificate, checked in one greedy pass — is an
  argument in prose that nothing in this file formalises; it is not
  claimed, so "NP-complete" is not said. (The first version of this header
  said it; the claim was one grade above the evidence.)

  FORM. A moving set is a `List Nat` of atoms allowed to change; "at least
  n+1 members" is the counting lemma `length_ge_of_all_below`, proved by
  removing one occurrence at a time — the one step E33 left as prose, done
  here because this time it carries the theorem.
-/
import ZHeredTaut

namespace ZWidthHard

open ZTime
open ZTime.V
open ZFenceDepth
open ZHeredTaut

/-! ### Moving a verdict: a refinement that changes only the atoms of `S` -/

/-- `m'` refines `m` and differs from it only on atoms listed in `S`. -/
def MovesWithin (φ : Fm) (m : Marking) (S : List Nat) : Prop :=
  ∃ m' : Marking, Refines m' m ∧ (∀ a, m' a ≠ m a → a ∈ S) ∧ evalF m' φ ≠ evalF m φ

/-- The width is at most `k`: some set of at most `k` atoms moves the verdict. -/
def WidthLE (φ : Fm) (m : Marking) (k : Nat) : Prop :=
  ∃ S : List Nat, S.length ≤ k ∧ MovesWithin φ m S

/-! ### Counting: a list holding every number below N has at least N members -/

def erase1 (n : Nat) : List Nat → List Nat
  | [] => []
  | x :: r => match Nat.beq x n with
              | true => r
              | false => x :: erase1 n r

theorem length_erase1_of_mem (n : Nat) : ∀ S : List Nat, n ∈ S → (erase1 n S).length + 1 = S.length
  | x :: r, h => by
      show (match Nat.beq x n with | true => r | false => x :: erase1 n r).length + 1 = r.length + 1
      cases hx : Nat.beq x n with
      | true => rfl
      | false =>
          show (erase1 n r).length + 1 + 1 = r.length + 1
          cases h with
          | head => rw [natBeq_refl n] at hx; cases hx
          | tail _ h' => rw [length_erase1_of_mem n r h']

theorem mem_erase1_of_ne (n : Nat) : ∀ (S : List Nat) (i : Nat), i ∈ S → ¬ i = n → i ∈ erase1 n S
  | x :: r, i, h, hne => by
      show i ∈ (match Nat.beq x n with | true => r | false => x :: erase1 n r)
      cases hx : Nat.beq x n with
      | true =>
          cases h with
          | head => exact absurd (Nat.eq_of_beq_eq_true hx) hne
          | tail _ h' => exact h'
      | false =>
          cases h with
          | head => exact List.Mem.head _
          | tail _ h' => exact List.Mem.tail _ (mem_erase1_of_ne n r i h' hne)

theorem lt_or_eq_of_lt_succ {i N : Nat} (h : i < N + 1) : i < N ∨ i = N :=
  Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ h)

/-- **A LIST HOLDING 0, 1, …, N−1 HAS AT LEAST N MEMBERS.** -/
theorem length_ge_of_all_below : ∀ (N : Nat) (S : List Nat), (∀ i, i < N → i ∈ S) → N ≤ S.length
  | 0, _, _ => Nat.zero_le _
  | N + 1, S, h => by
      have hN : N ∈ S := h N (Nat.lt_succ_self N)
      have hrest : ∀ i, i < N → i ∈ erase1 N S := fun i hi =>
        mem_erase1_of_ne N S i (h i (Nat.lt_succ_of_lt hi)) (Nat.ne_of_lt hi)
      have ih := length_ge_of_all_below N (erase1 N S) hrest
      rw [← length_erase1_of_mem N S hN]
      exact Nat.succ_le_succ ih

/-! ### Nothing short of the whole guard moves the witness -/

/-- A refinement of the all-marked start that leaves some guarded atom marked
keeps the verdict at T. -/
theorem stays_if_a_guard_is_marked (n : Nat) (ψ : Fm) (m' : Marking)
    (i : Nat) (hi : i < n + 1) (hz : m' i = V.Z) :
    evalF m' (witness (n + 1) ψ) = evalF allZ (witness (n + 1) ψ) := by
  rw [witness_allZ n ψ]
  show zimp (evalF m' (guard (n + 1))) (evalF m' ψ) = V.T
  rw [guard_F m' (n + 1) i hi hz]
  exact imp_F_left _

/-- **ANY MOVING SET CONTAINS EVERY GUARDED ATOM** — hence has at least n+1
members: no set of n atoms moves the witness. -/
theorem no_move_below (n : Nat) (ψ : Fm) : ¬ WidthLE (witness (n + 1) ψ) allZ n := by
  intro ⟨S, hlen, m', _, hS, hmove⟩
  have hall : ∀ i, i < n + 1 → i ∈ S := by
    intro i hi
    cases hz : m' i with
    | Z => exact absurd (stays_if_a_guard_is_marked n ψ m' i hi hz) hmove
    | T => exact hS i (by rw [hz]; intro h; cases h)
    | F => exact hS i (by rw [hz]; intro h; cases h)
  have := length_ge_of_all_below (n + 1) S hall
  exact absurd (Nat.le_trans this hlen) (Nat.lt_irrefl n)

/-! ### The whole guard moves it exactly when ψ can fail -/

/-- Fill the first N atoms from a classical point, leave the rest marked. -/
def fillBelow (N : Nat) (c : Marking) : Marking :=
  fun a => if a < N then c a else V.Z

def range : Nat → List Nat
  | 0 => []
  | n + 1 => n :: range n

theorem mem_range : ∀ (N i : Nat), i < N → i ∈ range N
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | N + 1, i, hi => by
      cases lt_or_eq_of_lt_succ hi with
      | inl hlt => exact List.Mem.tail _ (mem_range N i hlt)
      | inr heq => rw [heq]; exact List.Mem.head _

theorem length_range : ∀ N : Nat, (range N).length = N
  | 0 => rfl
  | N + 1 => by show (range N).length + 1 = N + 1; rw [length_range N]

/-- **WIDTH n+1 ⟺ ψ HAS A FALSIFYING CLASSICAL POINT.** -/
theorem width_iff_refutable (n : Nat) (ψ : Fm)
    (hψ : ∀ a, dependsOn ψ a = true → a < n + 1) :
    WidthLE (witness (n + 1) ψ) allZ (n + 1) ↔
      ∃ c : Marking, (∀ a, c a ≠ V.Z) ∧ evalF c ψ ≠ V.T := by
  constructor
  · intro ⟨S, _, m', hr, _, hmove⟩
    -- a move leaves no guarded atom marked, so m' agrees with its closure on the witness
    have hall : ∀ i, i < n + 1 → m' i ≠ V.Z := by
      intro i hi hz
      exact hmove (stays_if_a_guard_is_marked n ψ m' i hi hz)
    refine ⟨close m', close_grounded m', ?_⟩
    intro hT
    apply hmove
    rw [witness_allZ n ψ]
    have hagree : evalF (close m') (witness (n + 1) ψ) = evalF m' (witness (n + 1) ψ) := by
      apply evalF_congr_dep
      intro a ha
      have ha' : (dependsOn (guard (n + 1)) a || dependsOn ψ a) = true := ha
      have hlt : a < n + 1 := by
        cases dependsOn_guard.orT _ _ ha' with
        | inl h1 => exact dependsOn_guard (n + 1) a h1
        | inr h2 => exact hψ a h2
      exact close_fixes m' a (hall a hlt)
    rw [← hagree]
    show zimp (evalF (close m') (guard (n + 1))) (evalF (close m') ψ) = V.T
    rw [guard_T (close m') (n + 1) (fun i _ => close_grounded m' i),
        imp_T_left _ (evalF_ne_Z (close m') (close_grounded m') ψ)]
    exact hT
  · intro ⟨c, hc, hF⟩
    refine ⟨range (n + 1), Nat.le_of_eq (length_range (n + 1)), fillBelow (n + 1) c, ?_, ?_, ?_⟩
    · exact fun a ha => absurd rfl ha
    · intro a ha
      show a ∈ range (n + 1)
      cases Decidable.em (a < n + 1) with
      | inl hlt => exact mem_range (n + 1) a hlt
      | inr hge =>
          have : fillBelow (n + 1) c a = V.Z := by show (if a < n + 1 then c a else V.Z) = V.Z; rw [if_neg hge]
          exact absurd this ha
    · rw [witness_allZ n ψ]
      have hagree : evalF (fillBelow (n + 1) c) (witness (n + 1) ψ) = evalF c (witness (n + 1) ψ) := by
        apply evalF_congr_dep
        intro a ha
        have ha' : (dependsOn (guard (n + 1)) a || dependsOn ψ a) = true := ha
        have hlt : a < n + 1 := by
          cases dependsOn_guard.orT _ _ ha' with
          | inl h1 => exact dependsOn_guard (n + 1) a h1
          | inr h2 => exact hψ a h2
        show (if a < n + 1 then c a else V.Z) = c a
        rw [if_pos hlt]
      rw [hagree]
      show zimp (evalF c (guard (n + 1))) (evalF c ψ) ≠ V.T
      rw [guard_T c (n + 1) (fun i _ => hc i), imp_T_left _ (evalF_ne_Z c hc ψ)]
      exact hF

/-- The two together: the witness's width is n+1 or nothing. -/
theorem width_is_all_or_nothing (n : Nat) (ψ : Fm)
    (hψ : ∀ a, dependsOn ψ a = true → a < n + 1) :
    ¬ WidthLE (witness (n + 1) ψ) allZ n ∧
    (WidthLE (witness (n + 1) ψ) allZ (n + 1) ↔ ∃ c : Marking, (∀ a, c a ≠ V.Z) ∧ evalF c ψ ≠ V.T) :=
  ⟨no_move_below n ψ, width_iff_refutable n ψ hψ⟩

end ZWidthHard

#print axioms ZWidthHard.length_ge_of_all_below
#print axioms ZWidthHard.stays_if_a_guard_is_marked
#print axioms ZWidthHard.no_move_below
#print axioms ZWidthHard.width_iff_refutable
#print axioms ZWidthHard.width_is_all_or_nothing
