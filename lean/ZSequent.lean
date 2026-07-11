import TableauCert

/-!
# The sequent reading: cut, weakening, identity — admissible. Zero axioms.

The tableau engine read bottom-up is a cut-free sequent calculus for
the refutability judgment ⊢ S ("S is jointly unsatisfiable"). The
cut-free system is complete (closes_iff); cut on a covering sign pair
is sound; hence cut is admissible — semantic cut elimination, here as
kernel-checked theorems over the certified engine.
-/

namespace V

/-- The signs T and N cover all values: every value lies in {T} ∪ {F,Z}. -/
theorem signTN_total : ∀ x : V, SignT x = true ∨ SignN x = true := by decide

/-- ...and they are disjoint. -/
theorem signTN_disjoint : ∀ x : V,
    ¬(SignT x = true ∧ SignN x = true) := by decide

/-- The dual covering pair F/P. -/
theorem signFP_total : ∀ x : V, SignF x = true ∨ SignP x = true := by decide

/-- A satisfying valuation satisfies one of the two cut premises. -/
theorem SAT_cut_split {e : Env} {ws : List Node} (φ : Fm) :
    SAT e ws → SAT e ((SignT, φ) :: ws) ∨ SAT e ((SignN, φ) :: ws) := by
  rintro ⟨v, hOK, hs⟩
  rcases signTN_total (evalF v φ) with h | h
  · exact Or.inl ⟨v, hOK, h, hs⟩
  · exact Or.inr ⟨v, hOK, h, hs⟩

/-- CUT ADMISSIBILITY (semantic cut elimination): if both premises of
the cut close, the conclusion closes. -/
theorem cut_admissible (e : Env) (ws : List Node) (φ : Fm)
    (he : ∀ n, sIsEmpty (e n) = false)
    (h1 : closes (wsize ((SignT, φ) :: ws) + 1) e ((SignT, φ) :: ws) = true)
    (h2 : closes (wsize ((SignN, φ) :: ws) + 1) e ((SignN, φ) :: ws) = true) :
    closes (wsize ws + 1) e ws = true := by
  have k1 := (closes_iff _ e _ (Nat.lt_succ_self _) he).mp h1
  have k2 := (closes_iff _ e _ (Nat.lt_succ_self _) he).mp h2
  refine (closes_iff _ e ws (Nat.lt_succ_self _) he).mpr ?_
  intro hS
  rcases SAT_cut_split φ hS with h | h
  · exact k1 h
  · exact k2 h

/-- WEAKENING is admissible: a closed sequent stays closed under any
extra signed formula. -/
theorem weakening_admissible (e : Env) (ws : List Node) (nd : Node)
    (he : ∀ n, sIsEmpty (e n) = false)
    (h : closes (wsize ws + 1) e ws = true) :
    closes (wsize (nd :: ws) + 1) e (nd :: ws) = true := by
  have k := (closes_iff _ e _ (Nat.lt_succ_self _) he).mp h
  refine (closes_iff _ e _ (Nat.lt_succ_self _) he).mpr ?_
  rintro ⟨v, hOK, _, hs⟩
  exact k ⟨v, hOK, hs⟩

/-- IDENTITY: the sequent {T:φ, N:φ} is always derivable. -/
theorem identity_refutable (e : Env) (φ : Fm)
    (he : ∀ n, sIsEmpty (e n) = false) :
    closes (wsize [((SignT : Sign), φ), ((SignN : Sign), φ)] + 1) e
      [(SignT, φ), (SignN, φ)] = true := by
  refine (closes_iff _ e _ (Nat.lt_succ_self _) he).mpr ?_
  rintro ⟨v, hOK, h1, h2, _⟩
  exact signTN_disjoint (evalF v φ) ⟨h1, h2⟩

#print axioms cut_admissible
#print axioms weakening_admissible
#print axioms identity_refutable

end V
