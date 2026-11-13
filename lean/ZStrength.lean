import ClassicalAgreement

/-!
# Strength over classical logic: a proper conservative extension, in the MARKED language. Zero axioms.

The question (the curator, 2026-11-13): "which of two logics is stronger?" has no answer until the relation is
named, and for two months the relation here was named wrongly: "ZTL keeps only 12 of the 26 classical laws, so it
is weaker". The same inclusion read the right way says the opposite, and this file states it once.

`x == x` and `x === x` are two laws, not one. Likewise "φ holds when every atom is VERIFIED" and "φ holds when
some atoms are NOT verified" are two statements about one formula. Classical logic has only the first. So a law
is a formula TOGETHER WITH A MARKING — which atoms are verified — and it holds when the formula is T under every
valuation that puts T or F on the verified atoms (an unverified atom may carry anything, the mark Z included).

What is proved, for the whole formula language:

1. `law_all_iff_classical` — the layer "every atom verified" IS classical logic: the same laws, both ways.
   Nothing classical is lost, and nothing is added about classical logic's own domain. (It cannot be: classical
   propositional logic is complete for two-valued truth; a further law there would be false.)
2. `law_weaken` — verifying MORE atoms never loses a law. So a law under a marking implies the same law under
   every stronger marking, and in particular
3. `law_implies_classical` — every ZTL law implies its classical counterpart. A law that holds with unverified
   atoms is a STRONGER THEOREM than the classical one, not a rival of it.
4. `lnc_none` — the new layer is not empty: non-contradiction holds with NO atom verified.
5. `identity_splits` — and the new layer is not a copy of the old: `p → p` is a law when `p` is verified and is
   not one when it is not. The marking is part of the statement.

`proper_conservative_extension` puts the five together; `strictly_more_laws` says it as an inclusion: the
classical laws sit inside the marked laws as one layer, and there is a marked law outside that layer.

WHAT THIS IS NOT. It is not a new theorem about verified data — there is none to be had. "Stronger" here means
exactly: strictly more laws in the language with the marking, each implying the classical one, and the same laws
on the classical layer. Whoever reserves the word for an extension that proves more about the OLD domain will
call this "more expressive and conservative", and the theorems are the same under either name.
-/

namespace V

/-- A valuation RESPECTS a marking (`true` = verified) when every verified atom carries T or F. -/
def Respects (m : Nat → Bool) (v : Nat → V) : Prop := ∀ n, m n = true → v n ≠ Z

/-- A LAW UNDER A MARKING: the formula is T on every valuation that respects the marking. -/
def Law (m : Nat → Bool) (φ : Fm) : Prop := ∀ v : Nat → V, Respects m v → evalF v φ = T

/-- A classical law: true under every two-valued valuation. -/
def CLaw (φ : Fm) : Prop := ∀ b : Nat → Bool, cval b φ = true

/-- Every atom verified: classical logic's own domain. -/
def allVerified : Nat → Bool := fun _ => true

/-- No atom verified. -/
def noneVerified : Nat → Bool := fun _ => false

/-- Evaluation depends on the valuation pointwise (no function extensionality: that would be an axiom). -/
theorem evalF_pointwise (v w : Nat → V) (h : ∀ n, v n = w n) :
    ∀ φ : Fm, evalF v φ = evalF w φ := by
  intro φ
  induction φ with
  | atom n   => exact h n
  | top      => rfl
  | bot      => rfl
  | neg φ ih =>
      show znot (evalF v φ) = znot (evalF w φ)
      rw [ih]
  | conj φ ψ ihφ ihψ =>
      show zand (evalF v φ) (evalF v ψ) = zand (evalF w φ) (evalF w ψ)
      rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      show zor (evalF v φ) (evalF v ψ) = zor (evalF w φ) (evalF w ψ)
      rw [ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      show zimp (evalF v φ) (evalF v ψ) = zimp (evalF w φ) (evalF w ψ)
      rw [ihφ, ihψ]
  | xor φ ψ ihφ ihψ =>
      show zxor (evalF v φ) (evalF v ψ) = zxor (evalF w φ) (evalF w ψ)
      rw [ihφ, ihψ]
  | xnor φ ψ ihφ ihψ =>
      show zxnor (evalF v φ) (evalF v ψ) = zxnor (evalF w φ) (evalF w ψ)
      rw [ihφ, ihψ]

/-- The classical bit of a value that carries no mark. -/
def bitOf : V → Bool
  | T => true
  | F => false
  | Z => false

/-- A value is the mark, or the embedding of its bit. (Stated with no hypothesis about the value: a case split
under a hypothesis that mentions the value brings `propext` in.) -/
theorem emb_bitOf_or (x : V) : x = Z ∨ x = emb (bitOf x) := by
  cases x with
  | T => exact Or.inr rfl
  | F => exact Or.inr rfl
  | Z => exact Or.inl rfl

/-- A value without the mark is the embedding of its bit. -/
theorem emb_bitOf (x : V) (h : x ≠ Z) : x = emb (bitOf x) :=
  (emb_bitOf_or x).elim (fun hz => absurd hz h) id

/-- An embedded classical value never carries the mark. -/
theorem emb_ne_Z (a : Bool) : emb a ≠ Z := by
  cases a <;> decide

/-- **1. The verified layer is classical logic.** A formula is a law with every atom verified exactly when it is a
classical law. Nothing lost, nothing added, for every formula. -/
theorem law_all_iff_classical (φ : Fm) : Law allVerified φ ↔ CLaw φ := by
  constructor
  · intro h b
    have hv := h (fun n => emb (b n)) (fun n _ => emb_ne_Z (b n))
    rw [evalF_agrees b φ] at hv
    cases hb : cval b φ with
    | true  => rfl
    | false => rw [hb] at hv; exact absurd hv (by decide)
  · intro h v hr
    have hc : ∀ n, v n = emb (bitOf (v n)) := fun n => emb_bitOf (v n) (hr n rfl)
    rw [evalF_pointwise v (fun n => emb (bitOf (v n))) hc φ, evalF_agrees (fun n => bitOf (v n)) φ,
        h (fun n => bitOf (v n))]
    rfl

/-- **2. Verification never loses a law.** A law under a marking is a law under every marking that verifies at
least the same atoms. -/
theorem law_weaken (m m' : Nat → Bool) (hm : ∀ n, m n = true → m' n = true) (φ : Fm) :
    Law m φ → Law m' φ := by
  intro h v hr
  exact h v (fun n hn => hr n (hm n hn))

/-- **3. Every ZTL law implies its classical counterpart.** Whatever the marking, a law of ZTL is a classical law:
a law that holds with unverified atoms is the stronger statement. -/
theorem law_implies_classical (m : Nat → Bool) (φ : Fm) : Law m φ → CLaw φ := by
  intro h
  exact (law_all_iff_classical φ).mp (law_weaken m allVerified (fun _ _ => rfl) φ h)

/-- **4. The new layer is not empty.** Non-contradiction, `¬(p ∧ ¬p)`, is a law with NO atom verified. -/
theorem lnc_none : Law noneVerified (.neg (.conj (.atom 0) (.neg (.atom 0)))) := by
  intro v _
  show znot (zand (v 0) (znot (v 0))) = T
  generalize v 0 = x
  cases x <;> decide

/-- **5. The new layer is not a copy of the old.** `p → p` is a law when `p` is verified and is not a law when it
is not: the marking is part of the statement, as `==` and `===` are two laws. -/
theorem identity_splits :
    Law allVerified (.imp (.atom 0) (.atom 0)) ∧ ¬ Law noneVerified (.imp (.atom 0) (.atom 0)) := by
  constructor
  · exact (law_all_iff_classical _).mpr not_conversely.1
  · intro h
    exact absurd (h (fun _ => Z) (fun _ hn => Bool.noConfusion hn)) (by decide)

/-- The layer of unverified atoms and the layer of verified atoms are different sets of laws. -/
theorem layers_differ : ¬ (∀ φ : Fm, Law noneVerified φ ↔ Law allVerified φ) := by
  intro h
  exact identity_splits.2 ((h _).mpr identity_splits.1)

/-- **ZTL is a proper conservative extension of classical logic, in the marked language.**
(i) on the verified layer the laws are exactly the classical laws; (ii) every law, under any marking, implies the
classical law; (iii) there is a law with no atom verified; (iv) the two layers differ. -/
theorem proper_conservative_extension :
    (∀ φ : Fm, Law allVerified φ ↔ CLaw φ) ∧
    (∀ (m : Nat → Bool) (φ : Fm), Law m φ → CLaw φ) ∧
    Law noneVerified (.neg (.conj (.atom 0) (.neg (.atom 0)))) ∧
    ¬ (∀ φ : Fm, Law noneVerified φ ↔ Law allVerified φ) :=
  ⟨law_all_iff_classical, law_implies_classical, lnc_none, layers_differ⟩

/-- **Strictly more laws.** Every classical law is a marked law (on the verified layer), and there is a marked law
outside that layer — a formula with an atom, under a marking that verifies nothing. -/
theorem strictly_more_laws :
    (∀ φ : Fm, CLaw φ → Law allVerified φ) ∧
    (∃ (m : Nat → Bool) (φ : Fm), Law m φ ∧ m 0 = false ∧ φ = .neg (.conj (.atom 0) (.neg (.atom 0)))) :=
  ⟨fun φ => (law_all_iff_classical φ).mpr, ⟨noneVerified, _, lnc_none, rfl, rfl⟩⟩

#print axioms evalF_pointwise
#print axioms emb_bitOf_or
#print axioms emb_bitOf
#print axioms emb_ne_Z
#print axioms law_all_iff_classical
#print axioms law_weaken
#print axioms law_implies_classical
#print axioms lnc_none
#print axioms identity_splits
#print axioms layers_differ
#print axioms proper_conservative_extension
#print axioms strictly_more_laws

end V
