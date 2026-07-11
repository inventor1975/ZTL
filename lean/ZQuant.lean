import TableauCert

/-!
# Quantifier tableaux over finite domains, kernel-checked. Zero axioms.

Over a finite domain the ZTL quantifiers are strict folds: ∀ = "all
instances strictly T, else F", ∃ = "some instance strictly T, else F".
Both are expressible in the certified language Fm — ∀ as a conj-fold,
∃ as a disj-fold, with the singleton case collapsing to the J_T guard
(φ∧φ): on a one-element domain both quantifiers ARE the truth detector.

Consequently the n-ary signed quantifier rules are THEOREMS about the
folds (the T/F preimage coverages below), and the finite-domain
quantifier tableau procedure is the certified engine run on unfolded
sequents — soundness and completeness inherited from closes_iff.
Smoke theorems replicate the Python battery (tableau_fo.py) by kernel
evaluation of the certified engine.
-/

namespace V

/-- ∀ over a nonempty finite domain (head instance + the rest):
the strict conj-fold; a singleton collapses to the J_T guard φ∧φ. -/
def allF : Fm → List Fm → Fm
  | φ, [] => .conj φ φ
  | φ, ψ :: l => .conj φ (allF ψ l)

/-- ∃ over a nonempty finite domain: the strict disj-fold; a singleton
also collapses to the J_T guard — a witness must be strict. -/
def exF : Fm → List Fm → Fm
  | φ, [] => .conj φ φ
  | φ, ψ :: l => .disj φ (exF ψ l)

/-- "All instances are strictly T" (recursive, no list membership). -/
def allInstT (v : Nat → V) : Fm → List Fm → Prop
  | φ, [] => evalF v φ = T
  | φ, ψ :: l => evalF v φ = T ∧ allInstT v ψ l

/-- "Some instance is non-T" (the weak sign N, recursively). -/
def anyInstN (v : Nat → V) : Fm → List Fm → Prop
  | φ, [] => evalF v φ = F ∨ evalF v φ = Z
  | φ, ψ :: l => (evalF v φ = F ∨ evalF v φ = Z) ∨ anyInstN v ψ l

/-- "Some instance is strictly T" (a strict witness). -/
def anyInstT (v : Nat → V) : Fm → List Fm → Prop
  | φ, [] => evalF v φ = T
  | φ, ψ :: l => evalF v φ = T ∨ anyInstT v ψ l

/-- "All instances are non-T". -/
def allInstN (v : Nat → V) : Fm → List Fm → Prop
  | φ, [] => evalF v φ = F ∨ evalF v φ = Z
  | φ, ψ :: l => (evalF v φ = F ∨ evalF v φ = Z) ∧ allInstN v ψ l

/-! ## The singleton collapse: both quantifiers are the J_T guard -/

theorem jTT : ∀ a : V, zand a a = T ↔ a = T := by decide
theorem jTF : ∀ a : V, zand a a = F ↔ (a = F ∨ a = Z) := by decide

/-! ## Preimage coverage of the n-ary quantifier rules
(the finite-domain tableau rules of §6, as theorems) -/

/-- T:∀ — all instances strictly T (one branch, strict signs). -/
theorem cover_allF_T (v : Nat → V) : ∀ (l : List Fm) (φ : Fm),
    evalF v (allF φ l) = T ↔ allInstT v φ l := by
  intro l
  induction l with
  | nil => intro φ; exact jTT _
  | cons ψ l ih =>
    intro φ
    exact (cover_and_T _ _).trans (andCongr Iff.rfl (ih ψ))

/-- Greediness extends: quantified formulas are classical. -/
theorem allF_classical (v : Nat → V) (φ : Fm) (l : List Fm) :
    evalF v (allF φ l) = T ∨ evalF v (allF φ l) = F := by
  cases l <;> exact lift2_classical _ _ _

theorem exF_classical (v : Nat → V) (φ : Fm) (l : List Fm) :
    evalF v (exF φ l) = T ∨ evalF v (exF φ l) = F := by
  cases l <;> exact lift2_classical _ _ _

/-- For a classical value the weak sign N collapses to strict F. -/
theorem nz_of_classical {b : V} (hc : b = T ∨ b = F) :
    (b = F ∨ b = Z) ↔ b = F := by
  constructor
  · rintro (h | h)
    · exact h
    · rcases hc with rfl | rfl <;> exact nomatch h
  · exact Or.inl

/-- F:∀ — some instance is non-T (branches, weak sign N). -/
theorem cover_allF_F (v : Nat → V) : ∀ (l : List Fm) (φ : Fm),
    evalF v (allF φ l) = F ↔ anyInstN v φ l := by
  intro l
  induction l with
  | nil => intro φ; exact jTF _
  | cons ψ l ih =>
    intro φ
    exact (cover_and_F _ _).trans (orCongr Iff.rfl
      ((nz_of_classical (allF_classical v ψ l)).trans (ih ψ)))

/-- T:∃ — some instance strictly T (branches, strict sign). -/
theorem cover_exF_T (v : Nat → V) : ∀ (l : List Fm) (φ : Fm),
    evalF v (exF φ l) = T ↔ anyInstT v φ l := by
  intro l
  induction l with
  | nil => intro φ; exact jTT _
  | cons ψ l ih =>
    intro φ
    exact (cover_or_T _ _).trans (orCongr Iff.rfl (ih ψ))

/-- F:∃ — all instances non-T (one branch, weak signs). -/
theorem cover_exF_F (v : Nat → V) : ∀ (l : List Fm) (φ : Fm),
    evalF v (exF φ l) = F ↔ allInstN v φ l := by
  intro l
  induction l with
  | nil => intro φ; exact jTF _
  | cons ψ l ih =>
    intro φ
    exact (cover_or_F _ _).trans (andCongr Iff.rfl
      ((nz_of_classical (exF_classical v ψ l)).trans (ih ψ)))

/-! ## UI/EG over the whole language (membership versions) -/

/-- UI: an earned universal spends freely on every instance. -/
theorem ui_mem (v : Nat → V) : ∀ (l : List Fm) (φ ψ : Fm),
    evalF v (allF φ l) = T → (ψ = φ ∨ ψ ∈ l) → evalF v ψ = T := by
  intro l
  induction l with
  | nil =>
    intro φ ψ h hm
    rcases hm with rfl | hm
    · exact (jTT _).mp h
    · exact nomatch hm
  | cons χ l ih =>
    intro φ ψ h hm
    have hp := (cover_and_T _ _).mp h
    rcases hm with rfl | hm
    · exact hp.1
    · cases hm with
      | head => exact ih χ χ hp.2 (Or.inl rfl)
      | tail _ hm' => exact ih χ ψ hp.2 (Or.inr hm')

/-- EG as a rule: a strict witness earns the existential. -/
theorem eg_mem (v : Nat → V) : ∀ (l : List Fm) (φ ψ : Fm),
    (ψ = φ ∨ ψ ∈ l) → evalF v ψ = T → evalF v (exF φ l) = T := by
  intro l
  induction l with
  | nil =>
    intro φ ψ hm h
    rcases hm with rfl | hm
    · exact (jTT _).mpr h
    · exact nomatch hm
  | cons χ l ih =>
    intro φ ψ hm h
    refine (cover_or_T _ _).mpr ?_
    rcases hm with rfl | hm
    · exact Or.inl h
    · cases hm with
      | head => exact Or.inr (ih χ χ (Or.inl rfl) h)
      | tail _ hm' => exact Or.inr (ih χ ψ (Or.inr hm') h)

/-! ## The battery, run through the certified engine (domain 2)

P = atoms 0/1, Q = atoms 2/3; ∀P = allF, ∃P = exF over the instances.
Each verdict is a kernel-evaluation theorem of the certified `tproves`
(soundness+completeness inherited from tproves_iff) and matches the
measured Python battery (tableau_fo.py). -/

private def allP : Fm := allF (.atom 0) [.atom 1]
private def exP : Fm := exF (.atom 0) [.atom 1]
private def allNotP : Fm := allF (.neg (.atom 0)) [.neg (.atom 1)]
private def allPQ : Fm :=
  allF (.conj (.atom 0) (.atom 2)) [.conj (.atom 1) (.atom 3)]

/-- UI rule: ∀P ⊢ P(a₁). -/
theorem tab_ui : tproves [allP] (.atom 0) = true := by rfl
/-- EG rule: P(a₁) ⊢ ∃P. -/
theorem tab_eg : tproves [.atom 0] exP = true := by rfl
/-- EG law fails: ⊬ P(a₁) → ∃P. -/
theorem tab_eg_law_fails : tproves [] (.imp (.atom 0) exP) = false := by rfl
/-- ∀¬ ⊢ ¬∃. -/
theorem tab_allnot_notex : tproves [allNotP] (.neg exP) = true := by rfl
/-- ¬∃ ⊬ ∀¬ (Z hides under negation). -/
theorem tab_notex_allnot_fails :
    tproves [.neg exP] allNotP = false := by rfl
/-- Quantified LEM fails: ⊬ ∀y(P ∨ ¬P). -/
theorem tab_qlem_fails :
    tproves [] (allF (.disj (.atom 0) (.neg (.atom 0)))
                     [.disj (.atom 1) (.neg (.atom 1))]) = false := by rfl
/-- The drinker fails: ⊬ ∃y(P(y) → ∀zP(z)). -/
theorem tab_drinker_fails :
    tproves [] (exF (.imp (.atom 0) allP) [.imp (.atom 1) allP]) = false :=
  by rfl
/-- ∀-distribution: ∀(P∧Q) ⊢ ∀P. -/
theorem tab_distrib : tproves [allPQ] allP = true := by rfl

#print axioms cover_allF_T
#print axioms cover_allF_F
#print axioms cover_exF_F
#print axioms ui_mem
#print axioms eg_mem
#print axioms tab_ui
#print axioms tab_drinker_fails

end V
