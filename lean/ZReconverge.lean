import RelianceBridge

/-!
# Reconvergence is the meet — no shared ancestor changes eligibility. Zero axioms. (E61)

A question asked from outside (T2 of the 2026-09-06 roadmap): is there a graph
witness where two branches individually remain eligible but their recombination
changes eligibility solely because they share one unresolved ancestor? Against
`RelianceBridge` the answer is no — a theorem about every marking and every
pair of bundles, not a failed search.

`bundle` is the conjunction of a list; `verdict m Γ = evalF m (bundle Γ)`;
`eligible m Γ` says the verdict is T. Recombining two branches is appending
their bundles, and

    verdict_append       :  Γ₁ ≠ [] → Γ₂ ≠ [] →
                            verdict m (Γ₁ ++ Γ₂) = zand (verdict m Γ₁) (verdict m Γ₂)
    eligible_append_iff  :  eligible m (Γ₁ ++ Γ₂) = true
                              ↔ eligible m Γ₁ = true ∧ eligible m Γ₂ = true

THE EDGE THE STAND FOUND, before the kernel did. The meet identity was
predicted for all bundles and is false for the empty one: `bundle [] = ⊤`
and `bundle [φ] = φ` bare, so a singleton keeps the Z of an unverified atom,
while `zand Z T = F` — the greedy register reads a mark as not-yet-true inside
any connective. 12 of 135,225 measured cells, all of that shape; eligibility
unaffected in every cell, because neither Z nor F is T. So the meet identity
carries the non-emptiness hypotheses, and `eligible_append_iff` — the
statement T2 is about — holds without them.

So eligibility of the recombination is exactly eligibility of both parts,
whatever grounds they share and however many times they share them
(`no_reconvergence_witness`). T1 — fan-out neutrality — holds by construction,
a consequence's verdict being a function of its own bundle; `verdict_append`
says what the bundle of a fan-in is: the meet.

WHERE THE SHARED ANCESTOR DOES BITE: below eligibility, in the verdict. The
same unverified ground read once refuses (Z) and read twice denies (F) —
`same_grounds_two_verdicts` — and neither is eligible, so no recombination of
eligible branches ever sees it (`reconvergence_moves_the_verdict_not_eligibility`).
An unresolved ground makes every branch that reads it ineligible before any
recombination; the one exception is the over-grant `¬¬p`, and there the
recombination is still neutral: `zand T T = T` (`overgrant_recombines_neutrally`).

MEASURED FIRST (`zreconverge.py`, the greedy evaluator of `ztl.py`): every
ordered pair of bundles of length ≤ 2 and ≤ 1 over all formulas of depth ≤ 1 on
two atoms, under all nine markings, plus random longer pairs — eligibility of
the appended bundle equals the conjunction on every cell; the verdict equals
the meet on every cell with both bundles non-empty, and fails exactly on the
empty-bundle edge above.
-/

namespace ZReconverge

open V
open RelianceBridge

theorem zand_assoc : ∀ x y z : V, zand (zand x y) z = zand x (zand y z) := by decide
theorem append_nil' : ∀ l : List Fm, l ++ [] = l := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => show a :: (l ++ []) = a :: l; rw [ih]

theorem eligible_nil (m : Nat → V) : eligible m [] = true := rfl
theorem zand_eq_T : ∀ x y : V, zand x y = T ↔ (x = T ∧ y = T) := by decide
theorem T_of_beq : ∀ x : V, (x == T) = true → x = T := by decide
theorem beq_of_T : ∀ x : V, x = T → (x == T) = true := by decide

/-- The bundle of a fan-in of two non-empty branches is the meet of the bundles. -/
theorem verdict_append (m : Nat → V) :
    ∀ Γ₁ Γ₂ : List Fm, Γ₁ ≠ [] → Γ₂ ≠ [] →
      verdict m (Γ₁ ++ Γ₂) = zand (verdict m Γ₁) (verdict m Γ₂) := by
  intro Γ₁
  induction Γ₁ with
  | nil => intro Γ₂ h _; exact absurd rfl h
  | cons φ r ih =>
      intro Γ₂ _ h2
      cases r with
      | nil =>
          cases Γ₂ with
          | nil => exact absurd rfl h2
          | cons ψ r' => rfl
      | cons ψ r' =>
          show zand (evalF m φ) (verdict m ((ψ :: r') ++ Γ₂))
             = zand (zand (evalF m φ) (verdict m (ψ :: r'))) (verdict m Γ₂)
          rw [ih Γ₂ (fun e => by cases e) h2, zand_assoc]

/-- Eligibility of a fan-in is eligibility of both branches — whatever they share. -/
theorem eligible_append_iff (m : Nat → V) (Γ₁ Γ₂ : List Fm) :
    eligible m (Γ₁ ++ Γ₂) = true ↔ (eligible m Γ₁ = true ∧ eligible m Γ₂ = true) := by
  cases Γ₁ with
  | nil =>
      show eligible m Γ₂ = true ↔ (eligible m [] = true ∧ eligible m Γ₂ = true)
      exact ⟨fun h => ⟨eligible_nil m, h⟩, fun h => h.2⟩
  | cons φ r =>
      cases Γ₂ with
      | nil =>
          rw [append_nil']
          exact ⟨fun h => ⟨h, eligible_nil m⟩, fun h => h.1⟩
      | cons ψ r' =>
          have hne1 : (φ :: r) ≠ [] := fun e => by cases e
          have hne2 : (ψ :: r') ≠ [] := fun e => by cases e
          constructor
          · intro h
            have h0 : (verdict m ((φ :: r) ++ (ψ :: r')) == T) = true := h
            have h1 : verdict m ((φ :: r) ++ (ψ :: r')) = T := T_of_beq _ h0
            rw [verdict_append m (φ :: r) (ψ :: r') hne1 hne2] at h1
            have h2 := (zand_eq_T _ _).1 h1
            exact ⟨beq_of_T _ h2.1, beq_of_T _ h2.2⟩
          · intro h
            have h1 : verdict m (φ :: r) = T := T_of_beq _ h.1
            have h2 : verdict m (ψ :: r') = T := T_of_beq _ h.2
            show (verdict m ((φ :: r) ++ (ψ :: r')) == T) = true
            apply beq_of_T
            rw [verdict_append m (φ :: r) (ψ :: r') hne1 hne2, h1, h2]
            decide

/-- T2's witness does not exist: eligible branches recombine eligibly, whatever they share. -/
theorem no_reconvergence_witness (m : Nat → V) (Γ₁ Γ₂ : List Fm)
    (h1 : eligible m Γ₁ = true) (h2 : eligible m Γ₂ = true) :
    eligible m (Γ₁ ++ Γ₂) = true :=
  (eligible_append_iff m Γ₁ Γ₂).2 ⟨h1, h2⟩

/-- Where the shared ancestor bites: below eligibility. One unresolved ground read
once refuses, read twice denies; neither is eligible, so recombination of eligible
branches never sees it. -/
theorem reconvergence_moves_the_verdict_not_eligibility :
    verdict (fun _ => Z) [proofValid] = Z
    ∧ verdict (fun _ => Z) [proofValid, proofValid] = F
    ∧ eligible (fun _ => Z) [proofValid] = false
    ∧ eligible (fun _ => Z) [proofValid, proofValid] = false := by decide

/-- The one way an unresolved ground enters an eligible branch is the over-grant
`¬¬p`; recombining two such branches is still neutral. -/
theorem overgrant_recombines_neutrally :
    eligible (fun _ => Z) [.neg (.neg proofValid)] = true
    ∧ eligible (fun _ => Z) [.neg (.neg proofValid), .neg (.neg proofValid)] = true := by
  decide

#print axioms append_nil'
#print axioms verdict_append
#print axioms eligible_append_iff
#print axioms no_reconvergence_witness
#print axioms reconvergence_moves_the_verdict_not_eligibility
#print axioms overgrant_recombines_neutrally

end ZReconverge
