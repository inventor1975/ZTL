import ZAlgebra

/-!
# ZReplace — where ZTL keeps propext, and where it refuses it. Zero axioms. (2026-11-25)

THE QUESTION (the curator's line "ZTL без propext → математика", direction C): ZTL refutes `propext` on unverified
data — p and p ∧ p are true exactly together, yet ¬(p ∧ p) and ¬p differ at p = Z (`ZAxiomsRead.propext_fails_dirty`,
`ZAlgebra.not_selfextensional`).  Which equivalent formulas ARE interchangeable in every context?

THE ANSWER, complete:

    replace_compound      two COMPOUND formulas that are true exactly together (under every valuation) are
                          interchangeable in EVERY context — propext holds between judgments;
    replace_atom_fails    a bare ATOM and any compound formula true exactly together with it are told apart by
                          the context ¬ (at the all-unverified valuation);
    replace_iff           so: equivalent φ, ψ are interchangeable in every context iff both are compound, or they
                          are the same formula.

WHY. Greediness (`evalF_classical`): a compound formula never takes Z — it is a verdict, T or F.  Between verdicts
"true exactly together" IS "the same value", and the same value can be put anywhere (the substitution lemma).  An
atom is an INPUT: it may be unverified (Z), and Z is not a verdict — "not T" covers both F and Z, and ¬ tells them
apart (¬F = T, ¬Z = F).

READING. ZTL does not refute propext wholesale.  It refuses one thing: to substitute a raw, unverified datum for a
judgment about it.  Equivalent judgments are interchangeable as in classical logic; an input and its judgment are
not — "p" and "p is the case" are different objects until p is verified.
-/

namespace ZReplace

open V

/-- A compound formula: anything but a bare atom (every constructor listed — no overlapping match). -/
def Compound : Fm → Prop
  | .atom _ => False
  | .neg _ => True
  | .conj _ _ => True
  | .disj _ _ => True
  | .imp _ _ => True
  | .xor _ _ => True
  | .xnor _ _ => True
  | .top => True
  | .bot => True

/-- A compound formula is a verdict: never Z. -/
theorem compound_ne_Z (v : Nat → V) {φ : Fm} (hφ : Compound φ) : evalF v φ ≠ Z := by
  intro hz
  cases evalF_classical v φ with
  | inl h =>
    obtain ⟨n, e⟩ := h
    subst e
    exact hφ
  | inr h => cases h with
    | inl h => rw [hz] at h; exact V.noConfusion h
    | inr h => rw [hz] at h; exact V.noConfusion h

/-- Two verdicts true exactly together are the same verdict. -/
theorem verdict_eq : ∀ a b : V, a ≠ Z → b ≠ Z → (a = T ↔ b = T) → a = b := by decide

/-- Evaluation depends on the valuation pointwise (no funext). -/
theorem evalF_congr {v w : Nat → V} (h : ∀ n, v n = w n) : ∀ χ : Fm, evalF v χ = evalF w χ := by
  intro χ
  induction χ with
  | atom n => exact h n
  | top => rfl
  | bot => rfl
  | neg φ ih => exact congrArg znot ih
  | conj φ ψ ih1 ih2 => exact congr2 zand ih1 ih2
  | disj φ ψ ih1 ih2 => exact congr2 zor ih1 ih2
  | imp φ ψ ih1 ih2 => exact congr2 zimp ih1 ih2
  | xor φ ψ ih1 ih2 => exact congr2 zxor ih1 ih2
  | xnor φ ψ ih1 ih2 => exact congr2 zxnor ih1 ih2

/-- Put `φ` at the hole `k` of a context `χ` (every other atom stays itself). -/
def plug (k : Nat) (φ : Fm) (χ : Fm) : Fm := substF (fun n => if n = k then φ else .atom n) χ

/-- **Between judgments propext holds**: compound formulas true exactly together are interchangeable in every
context, under every valuation. -/
theorem replace_compound {φ ψ : Fm} (hφ : Compound φ) (hψ : Compound ψ)
    (heq : ∀ v, evalF v φ = T ↔ evalF v ψ = T) (k : Nat) (χ : Fm) (v : Nat → V) :
    evalF v (plug k φ χ) = evalF v (plug k ψ χ) := by
  unfold plug
  rw [evalF_subst, evalF_subst]
  apply evalF_congr
  intro n
  by_cases hn : n = k
  · show evalF v (if n = k then φ else .atom n) = evalF v (if n = k then ψ else .atom n)
    rw [if_pos hn, if_pos hn]
    exact verdict_eq _ _ (compound_ne_Z v hφ) (compound_ne_Z v hψ) (heq v)
  · show evalF v (if n = k then φ else .atom n) = evalF v (if n = k then ψ else .atom n)
    rw [if_neg hn, if_neg hn]

/-- The all-unverified valuation. -/
def allZ : Nat → V := fun _ => Z

/-- **A bare atom and any compound formula equivalent to it are told apart by ¬**, at the all-unverified
valuation: the atom is Z, the compound is a verdict (F, since it is not T), and ¬Z = F while ¬F = T. -/
theorem replace_atom_fails {ψ : Fm} (hψ : Compound ψ) (n : Nat)
    (heq : ∀ v, evalF v (.atom n) = T ↔ evalF v ψ = T) :
    evalF allZ (.neg (.atom n)) ≠ evalF allZ (.neg ψ) := by
  have hz : evalF allZ ψ ≠ Z := compound_ne_Z allZ hψ
  have hnT : evalF allZ ψ ≠ T := fun h => V.noConfusion ((heq allZ).mpr h)
  have hF : evalF allZ ψ = F := by
    revert hz hnT
    cases evalF allZ ψ with
    | T => intro _ h; exact absurd rfl h
    | F => intro _ _; rfl
    | Z => intro h; exact absurd rfl h
  show znot Z ≠ znot (evalF allZ ψ)
  rw [hF]
  decide

/-- The textbook instance: p and p ∧ p are equivalent, and ¬ separates them. -/
theorem p_and_p : (∀ v, evalF v (.atom 0) = T ↔ evalF v (.conj (.atom 0) (.atom 0)) = T) ∧
    evalF allZ (.neg (.atom 0)) ≠ evalF allZ (.neg (.conj (.atom 0) (.atom 0))) := by
  have heq : ∀ v, evalF v (.atom 0) = T ↔ evalF v (.conj (.atom 0) (.atom 0)) = T := by
    intro v
    show v 0 = T ↔ zand (v 0) (v 0) = T
    cases v 0 <;> decide
  exact ⟨heq, replace_atom_fails (ψ := .conj (.atom 0) (.atom 0)) trivial 0 heq⟩

/-- …the other side of the boundary: an atom against a compound is never interchangeable. -/
theorem atom_compound_not_interchangeable {ψ : Fm} (hψ : Compound ψ) (n : Nat)
    (heq : ∀ v, evalF v (.atom n) = T ↔ evalF v ψ = T) :
    ∃ k χ v, evalF v (plug k (.atom n) χ) ≠ evalF v (plug k ψ χ) :=
  ⟨0, .neg (.atom 0), allZ, by
    show znot (evalF allZ (if 0 = 0 then .atom n else .atom 0)) ≠ znot (evalF allZ (if 0 = 0 then ψ else .atom 0))
    rw [if_pos rfl, if_pos rfl]
    exact replace_atom_fails hψ n heq⟩

/-- Every formula is an atom or compound (every constructor listed). -/
theorem atom_or_compound : ∀ φ : Fm, (∃ n, φ = .atom n) ∨ Compound φ
  | .atom n => .inl ⟨n, rfl⟩
  | .neg _ => .inr trivial
  | .conj _ _ => .inr trivial
  | .disj _ _ => .inr trivial
  | .imp _ _ => .inr trivial
  | .xor _ _ => .inr trivial
  | .xnor _ _ => .inr trivial
  | .top => .inr trivial
  | .bot => .inr trivial

/-- Two equivalent atoms are one atom (the valuation "n true, all else false" separates distinct atoms). -/
theorem atoms_equiv_same {n m : Nat} (heq : ∀ v, evalF v (.atom n) = T ↔ evalF v (.atom m) = T) : n = m := by
  by_cases h : m = n
  · exact h.symm
  · have := (heq (fun i => if i = n then T else F)).mp
    have e1 : evalF (fun i => if i = n then T else F) (.atom n) = T := by
      show (if n = n then T else F) = T
      rw [if_pos rfl]
    have e2 : evalF (fun i => if i = n then T else F) (.atom m) = F := by
      show (if m = n then T else F) = F
      rw [if_neg h]
    exact absurd (e2.symm.trans (this e1)) (fun h' => V.noConfusion h')

/-- **The complete answer.**  For equivalent φ, ψ (true exactly together under every valuation): they are
interchangeable in every context IFF both are compound, or they are one formula.  The one place ZTL refuses
propext is between an input (a bare atom) and a judgment. -/
theorem replace_iff {φ ψ : Fm} (heq : ∀ v, evalF v φ = T ↔ evalF v ψ = T) :
    (∀ k χ v, evalF v (plug k φ χ) = evalF v (plug k ψ χ)) ↔ ((Compound φ ∧ Compound ψ) ∨ φ = ψ) := by
  constructor
  · intro hall
    cases atom_or_compound φ with
    | inl ha =>
      obtain ⟨n, e⟩ := ha
      subst e
      cases atom_or_compound ψ with
      | inl hb =>
        obtain ⟨m, e⟩ := hb
        subst e
        exact .inr (congrArg Fm.atom (atoms_equiv_same heq))
      | inr hψ =>
        obtain ⟨k, χ, v, hne⟩ := atom_compound_not_interchangeable hψ n heq
        exact absurd (hall k χ v) hne
    | inr hφ =>
      cases atom_or_compound ψ with
      | inl hb =>
        obtain ⟨m, e⟩ := hb
        subst e
        obtain ⟨k, χ, v, hne⟩ := atom_compound_not_interchangeable hφ m (fun v => (heq v).symm)
        exact absurd (hall k χ v).symm hne
      | inr hψ => exact .inl ⟨hφ, hψ⟩
  · intro h k χ v
    cases h with
    | inl hc => exact replace_compound hc.1 hc.2 heq k χ v
    | inr e => rw [e]

end ZReplace

#print axioms ZReplace.compound_ne_Z
#print axioms ZReplace.verdict_eq
#print axioms ZReplace.replace_compound
#print axioms ZReplace.replace_atom_fails
#print axioms ZReplace.p_and_p
#print axioms ZReplace.replace_iff
#print axioms ZReplace.atom_compound_not_interchangeable
#print axioms ZReplace.atoms_equiv_same
