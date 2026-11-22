import ClassicalAgreement
import ZDirty
import ZRead

/-!
# ZLens — what ZTL adds to classical logic, and why it cannot overtake it. Zero axioms.

One statement, assembled from pieces already proved elsewhere (`ClassicalAgreement`, `ZDirty`).
Nothing in it is new mathematics; the point is to say in one place what the lens is.

Classical logic has one axis: true or false. ZTL adds a second: checked or not (`Z` sits below `T`
and `F` in the information order). The judge's strict verdicts are EARNED / REFUTED — T / F under every
reading of every occurrence (`ZRead.earnedR` / `refutedR`; pure branch, no Kleene table). With that:

1. `lens_exact_on_checked` — AGREEMENT. On a valuation with no mark, the verdict IS the classical
   value: never OPEN, never different.
2. `lens_sound` / `lens_sound_F` — SOUNDNESS. What the judge earns (refutes) is classically true
   (false) under EVERY way of filling in the unchecked atoms consistently with what was checked.
3. `lens_mono` / `lens_mono_F` — MONOTONICITY. Checking more never withdraws a verdict: only OPEN
   can move, and only to T or F.
4. `lens_strict` — PRICE. The converse of 2 fails: `p → p` is classically true under every filling,
   and on an unchecked `p` the judge leaves it OPEN.
5. `lens_no_new_truth` — CEILING. A formula earned when NOTHING is checked is a classical tautology.

Hence, as theorems (scope: propositional formulas, independent atoms, checked values taken as given,
the STRICT verdict only — EARNED IF STABLE is not covered):
* "never ahead of classical": by 2 a strict verdict is a classical consequence of the checked atoms
  taken as premises, never more; by 5, with nothing checked, it is a classical tautology. By 4 it is
  sometimes LESS decisive (the stable reading grants `p → p`; the loss belongs to the strict verdict).
* "what it adds": by 1 and 3 the record of which claims the checks so far already settle, a record
  that only grows under refinement (a correction of an earlier check is not a refinement).

Prior art: three-valued logic read as an information order (Kleene 1938, 1952); close to Belnap,
"How a computer should think" (1977, four values) and to the abstract interpretation of Cousot & Cousot
(1977, see `ZAbsInt`). No novelty claimed. Wording fixed after an outside reading
(prose gate, 2026-11-06).
-/

namespace V

/-! ## 1. Agreement: on checked ground the readings are the classical value -/

theorem comb_emb (g : Bool → Bool → Bool) (x y : Bool) :
    comb g (x, !x) (y, !y) = (g x y, !(g x y)) := by
  dsimp only [comb, ok, List.any]
  cases x <;> cases y <;> cases g true true <;> cases g true false <;> cases g false true <;>
    cases g false false <;> rfl

/-- **Agreement.** With every atom checked, the one reading of φ is its classical value. -/
theorem lens_exact_on_checked (b : Nat → Bool) :
    ∀ φ : Fm, rd (fun n => emb (b n)) φ = (cval b φ, !cval b φ)
  | .atom n => by
      show ((subs (emb (b n))).contains true, (subs (emb (b n))).contains false) = (b n, !b n)
      cases b n <;> rfl
  | .top => rfl
  | .bot => rfl
  | .neg φ => by
      show ((rd _ φ).2, (rd _ φ).1) = (!cval b φ, !!cval b φ)
      rw [lens_exact_on_checked b φ]; cases cval b φ <;> rfl
  | .conj φ ψ => by
      show comb _ (rd _ φ) (rd _ ψ) = _; rw [lens_exact_on_checked b φ, lens_exact_on_checked b ψ]; exact comb_emb _ _ _
  | .disj φ ψ => by
      show comb _ (rd _ φ) (rd _ ψ) = _; rw [lens_exact_on_checked b φ, lens_exact_on_checked b ψ]; exact comb_emb _ _ _
  | .imp φ ψ => by
      show comb _ (rd _ φ) (rd _ ψ) = _; rw [lens_exact_on_checked b φ, lens_exact_on_checked b ψ]; exact comb_emb _ _ _
  | .xor φ ψ => by
      show comb _ (rd _ φ) (rd _ ψ) = _; rw [lens_exact_on_checked b φ, lens_exact_on_checked b ψ]; exact comb_emb _ _ _
  | .xnor φ ψ => by
      show comb _ (rd _ φ) (rd _ ψ) = _; rw [lens_exact_on_checked b φ, lens_exact_on_checked b ψ]; exact comb_emb _ _ _

/-! ## 2. Soundness: a verdict holds under every consistent filling of the unchecked atoms -/

/-- `b` fills in `v`: a classical valuation that agrees with `v` wherever `v` was checked. -/
def Fills (v : Nat → V) (b : Nat → Bool) : Prop := ∀ n, v n ≠ Z → v n = emb (b n)

theorem fills_refinesR (v : Nat → V) (b : Nat → Bool) (h : Fills v b) :
    refinesR v (fun n => emb (b n)) := fun n hn => (h n hn).symm

/-- **Soundness, T.** What the judge earns is classically true under every filling. -/
theorem lens_sound (v : Nat → V) (φ : Fm) (h : earnedR v φ) (b : Nat → Bool) (hb : Fills v b) :
    cval b φ = true := by
  have m : (rd (fun n => emb (b n)) φ).2 = false := earnedR_open (fills_refinesR v b hb) h
  rw [lens_exact_on_checked b φ] at m
  revert m; cases cval b φ <;> intro m
  · exact Bool.noConfusion m
  · rfl

/-- **Soundness, F.** What the judge refutes is classically false under every filling. -/
theorem lens_sound_F (v : Nat → V) (φ : Fm) (h : refutedR v φ) (b : Nat → Bool) (hb : Fills v b) :
    cval b φ = false := by
  have m : (rd (fun n => emb (b n)) φ).1 = false := refutedR_open (fills_refinesR v b hb) h
  rw [lens_exact_on_checked b φ] at m
  exact m

/-! ## 3. Monotonicity: checking more never withdraws a verdict -/

theorem lens_mono (v w : Nat → V) (hr : refinesR v w) (φ : Fm) (h : earnedR v φ) : earnedR w φ :=
  earnedR_open hr h

theorem lens_mono_F (v w : Nat → V) (hr : refinesR v w) (φ : Fm) (h : refutedR v φ) : refutedR w φ :=
  refutedR_open hr h

/-! ## 4. Price: the converse of soundness fails -/

/-- **Strictness.** `p → p` is true under every filling, and the judge does not earn it on an unchecked `p`
(a reading of its two occurrences makes it false: the judge says EARNED IF STABLE). -/
theorem lens_strict :
    (∀ b : Nat → Bool, Fills (fun _ => Z) b → cval b (.imp (.atom 0) (.atom 0)) = true) ∧
    ¬ earnedR (fun _ => Z) (.imp (.atom 0) (.atom 0)) := by
  refine ⟨fun b _ => ?_, by unfold earnedR; decide⟩
  show (!(b 0) || b 0) = true
  cases b 0 <;> rfl

/-! ## 5. Ceiling: earned from nothing ⇒ classical tautology -/

/-- **No new truth.** Earned with nothing checked, a formula is a classical tautology. -/
theorem lens_no_new_truth (φ : Fm) (h : earnedR (fun _ => Z) φ) : ∀ b : Nat → Bool, cval b φ = true :=
  fun b => lens_sound _ φ h b (fun _ hn => absurd rfl hn)

/-! ## The lens, in one statement -/

/-- **The lens theorem.** For any partial checking `v` and formula `φ`: an EARNED (REFUTED) verdict is
classical truth (falsehood) under every consistent filling, and survives every further check; with everything
checked the one reading is the classical value. -/
theorem lens (v : Nat → V) (φ : Fm) :
    (earnedR v φ → ∀ b, Fills v b → cval b φ = true) ∧
    (refutedR v φ → ∀ b, Fills v b → cval b φ = false) ∧
    (∀ w, refinesR v w → earnedR v φ → earnedR w φ) ∧
    (∀ w, refinesR v w → refutedR v φ → refutedR w φ) ∧
    (∀ b : Nat → Bool, rd (fun n => emb (b n)) φ = (cval b φ, !cval b φ)) :=
  ⟨lens_sound v φ, lens_sound_F v φ, fun w hr => lens_mono v w hr φ, fun w hr => lens_mono_F v w hr φ,
   fun b => lens_exact_on_checked b φ⟩

#print axioms lens_exact_on_checked
#print axioms lens_sound
#print axioms lens_sound_F
#print axioms lens_mono
#print axioms lens_mono_F
#print axioms lens_strict
#print axioms lens_no_new_truth
#print axioms lens

end V
