import ClassicalAgreement
import ZDirty

/-!
# ZLens — what ZTL adds to classical logic, and why it cannot overtake it. Zero axioms.

One statement, assembled from pieces already proved elsewhere (`ClassicalAgreement`, `ZDirty`).
Nothing in it is new mathematics; the point is to say in one place what the lens is.

Classical logic has one axis: true or false. ZTL adds a second: checked or not (`Z` sits below `T`
and `F` in the information order). The judge's verdict is the strong Kleene value `kev`
(`ZDirty.strict_earned_iff_kleene`). With that:

1. `lens_exact_on_checked` — AGREEMENT. On a valuation with no mark, the verdict IS the classical
   value: never OPEN, never different.
2. `lens_sound` / `lens_sound_F` — SOUNDNESS. What the judge earns (refutes) is classically true
   (false) under EVERY way of filling in the unchecked atoms consistently with what was checked.
3. `lens_mono` / `lens_mono_F` — MONOTONICITY. Checking more never withdraws a verdict: only OPEN
   can move, and only to T or F.
4. `lens_strict` — PRICE. The converse of 2 fails: `p → p` is classically true under every filling,
   and on an unchecked `p` the judge leaves it OPEN.
5. `lens_no_new_truth` — CEILING. A formula earned when NOTHING is checked is a classical tautology.

Hence the two halves of the slogan, as theorems:
* "level with classical": by 2 and 5 every verdict the judge gives is a classical fact; the judge
  cannot prove anything classical logic does not. This is a consequence of soundness, not a
  shortfall to be fixed.
* "beyond classical": by 1 and 3 the extra axis — which verdicts are already settled by what was
  checked — is tracked exactly and monotonically. Classical logic has no place to say it.

Prior art: Kleene (1938, 1952), strong three-valued logic; Belnap, "How a computer should think"
(1977); Cousot & Cousot (1977), abstract interpretation (see `ZAbsInt`). The lens is this
tradition applied; the novelty claimed is none.
-/

namespace V

/-! ## 1. Agreement: on checked ground the verdict is the classical value -/

theorem k1_not_emb : ∀ a : Bool, k1 (fun a => !a) (emb a) = emb (!a) := by decide
theorem k2_and_emb : ∀ a b : Bool, k2 (fun a b => a && b) (emb a) (emb b) = emb (a && b) := by decide
theorem k2_or_emb : ∀ a b : Bool, k2 (fun a b => a || b) (emb a) (emb b) = emb (a || b) := by decide
theorem k2_imp_emb : ∀ a b : Bool, k2 (fun a b => !a || b) (emb a) (emb b) = emb (!a || b) := by decide
theorem k2_xor_emb : ∀ a b : Bool, k2 (fun a b => a != b) (emb a) (emb b) = emb (a != b) := by decide
theorem k2_xnor_emb : ∀ a b : Bool, k2 (fun a b => a == b) (emb a) (emb b) = emb (a == b) := by decide

/-- **Agreement.** With every atom checked, the judge's value is the classical value, for every formula. -/
theorem lens_exact_on_checked (b : Nat → Bool) :
    ∀ φ : Fm, kev (fun n => emb (b n)) φ = emb (cval b φ) := by
  intro φ
  induction φ with
  | atom n => rfl
  | top => rfl
  | bot => rfl
  | neg φ ih => show k1 _ (kev _ φ) = _; rw [ih]; exact k1_not_emb _
  | conj φ ψ ihφ ihψ => show k2 _ (kev _ φ) (kev _ ψ) = _; rw [ihφ, ihψ]; exact k2_and_emb _ _
  | disj φ ψ ihφ ihψ => show k2 _ (kev _ φ) (kev _ ψ) = _; rw [ihφ, ihψ]; exact k2_or_emb _ _
  | imp φ ψ ihφ ihψ => show k2 _ (kev _ φ) (kev _ ψ) = _; rw [ihφ, ihψ]; exact k2_imp_emb _ _
  | xor φ ψ ihφ ihψ => show k2 _ (kev _ φ) (kev _ ψ) = _; rw [ihφ, ihψ]; exact k2_xor_emb _ _
  | xnor φ ψ ihφ ihψ => show k2 _ (kev _ φ) (kev _ ψ) = _; rw [ihφ, ihψ]; exact k2_xnor_emb _ _

/-! ## 2. Soundness: a verdict holds under every consistent filling of the unchecked atoms -/

/-- `b` fills in `v`: a classical valuation that agrees with `v` wherever `v` was checked. -/
def Fills (v : Nat → V) (b : Nat → Bool) : Prop := ∀ n, v n ≠ Z → v n = emb (b n)

theorem fills_refines (v : Nat → V) (b : Nat → Bool) (h : Fills v b) :
    refines v (fun n => emb (b n)) := fun n hn => (h n hn).symm

theorem emb_T (c : Bool) (h : emb c = T) : c = true := by
  cases c
  · exact absurd h (by decide)
  · rfl

theorem emb_F (c : Bool) (h : emb c = F) : c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

/-- **Soundness, T.** What the judge earns is classically true under every filling. -/
theorem lens_sound (v : Nat → V) (φ : Fm) (h : kev v φ = T) (b : Nat → Bool) (hb : Fills v b) :
    cval b φ = true := by
  have m := kev_mono v _ (fills_refines v b hb) φ
  rw [h, lens_exact_on_checked b φ] at m
  exact emb_T _ (kle_T _ m)

/-- **Soundness, F.** What the judge refutes is classically false under every filling. -/
theorem lens_sound_F (v : Nat → V) (φ : Fm) (h : kev v φ = F) (b : Nat → Bool) (hb : Fills v b) :
    cval b φ = false := by
  have m := kev_mono v _ (fills_refines v b hb) φ
  rw [h, lens_exact_on_checked b φ] at m
  exact emb_F _ (kle_F _ m)

/-! ## 3. Monotonicity: checking more never withdraws a verdict -/

theorem lens_mono (v w : Nat → V) (hr : refines v w) (φ : Fm) (h : kev v φ = T) : kev w φ = T := by
  have m := kev_mono v w hr φ
  rw [h] at m
  exact kle_T _ m

theorem lens_mono_F (v w : Nat → V) (hr : refines v w) (φ : Fm) (h : kev v φ = F) : kev w φ = F := by
  have m := kev_mono v w hr φ
  rw [h] at m
  exact kle_F _ m

/-! ## 4. Price: the converse of soundness fails -/

/-- **Strictness.** `p → p` is true under every filling, and the judge leaves it OPEN on an unchecked `p`. -/
theorem lens_strict :
    (∀ b : Nat → Bool, Fills (fun _ => Z) b → cval b (.imp (.atom 0) (.atom 0)) = true) ∧
    kev (fun _ => Z) (.imp (.atom 0) (.atom 0)) = Z := by
  refine ⟨fun b _ => ?_, by decide⟩
  show (!(b 0) || b 0) = true
  cases b 0 <;> rfl

/-! ## 5. Ceiling: earned from nothing ⇒ classical tautology -/

/-- **No new truth.** Earned with nothing checked, a formula is a classical tautology. -/
theorem lens_no_new_truth (φ : Fm) (h : kev (fun _ => Z) φ = T) : ∀ b : Nat → Bool, cval b φ = true :=
  fun b => lens_sound _ φ h b (fun _ hn => absurd rfl hn)

/-! ## The lens, in one statement -/

/-- **The lens theorem.** For any partial checking `v` and formula `φ`: a T (F) verdict is classical truth
(falsehood) under every consistent filling, and survives every further check; with everything checked the
verdict is the classical value. -/
theorem lens (v : Nat → V) (φ : Fm) :
    (kev v φ = T → ∀ b, Fills v b → cval b φ = true) ∧
    (kev v φ = F → ∀ b, Fills v b → cval b φ = false) ∧
    (∀ w, refines v w → kev v φ = T → kev w φ = T) ∧
    (∀ w, refines v w → kev v φ = F → kev w φ = F) ∧
    (∀ b : Nat → Bool, kev (fun n => emb (b n)) φ = emb (cval b φ)) :=
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
