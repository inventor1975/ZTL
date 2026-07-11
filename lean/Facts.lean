import ZTL

/-!
# Facts: quantifiers on finite domains and paradox dynamics. Zero axioms.

Quantifiers over a finite domain are folds: ∀ = zand (all strictly T),
∃ = zor (a strict witness). Domains 1–2 are represented by value tuples.
Dynamics: oscillation periods, Curry, cycle parity, the Yablo truncation.
-/

namespace V

/-! ## Quantifiers, domain 2: ∀ = zand, ∃ = zor -/

/-- The UI law is alive on domain 2: ⊨ ∀P → P(a). -/
theorem ui_law_dom2 : ∀ p₁ p₂ : V, zimp (zand p₁ p₂) p₁ = T := by decide

/-- The EG law fell: ⊭ P(a) → ∃P (a Z-witness does not count). -/
theorem eg_law_dom2_fails : ¬ ∀ p₁ p₂ : V, zimp p₁ (zor p₁ p₂) = T := by
  decide

/-- An alive rule: ∀¬ ⊨ ¬∃. -/
theorem allnot_notex_dom2 : ∀ p₁ p₂ : V,
    zand (znot p₁) (znot p₂) = T → znot (zor p₁ p₂) = T := by decide

/-- A fallen rule: ¬∃ ⊭ ∀¬ (Z hides under negation). -/
theorem notex_allnot_dom2_fails : ¬ ∀ p₁ p₂ : V,
    (znot (zor p₁ p₂) = T → zand (znot p₁) (znot p₂) = T) := by decide

/-- The mirror fallen rule: ¬∀ ⊭ ∃¬. -/
theorem notall_exnot_dom2_fails : ¬ ∀ p₁ p₂ : V,
    (znot (zand p₁ p₂) = T → zor (znot p₁) (znot p₂) = T) := by decide

/-- Quantified LEM fell: ⊭ ∀x (P(x) ∨ ¬P(x)). -/
theorem qlem_dom2_fails : ¬ ∀ p₁ p₂ : V,
    zand (zor p₁ (znot p₁)) (zor p₂ (znot p₂)) = T := by decide

/-- The "drinker" fell: ⊭ ∃x (P(x) → ∀y P(y)). -/
theorem drinker_dom2_fails : ¬ ∀ p₁ p₂ : V,
    zor (zimp p₁ (zand p₁ p₂)) (zimp p₂ (zand p₁ p₂)) = T := by decide

/-! ## Dynamics: oscillations and fixed points -/

/-- The liar: period 2 on classical values (¬¬v = v, ¬v ≠ v). -/
theorem liar_period2 : ∀ v : V, (v = T ∨ v = F) →
    znot (znot v) = v ∧ znot v ≠ v := by decide

/-- Jourdain's carousel: the jump J(a,b) = (b, ¬a) has no fixed points. -/
theorem carousel_no_fp : ∀ a b : V, ¬(b = a ∧ znot a = b) := by decide

/-- The carousel: period 4 on classical values. -/
theorem carousel_period4 : ∀ a b : V, (a = T ∨ a = F) → (b = T ∨ b = F) →
    (znot (znot a), znot (znot b)) = (a, b) := by decide

/-- Curry c = (Tr c → ⊥): greedily homeless — without any negation. -/
theorem curry_homeless : ∀ v : V, zimp v F ≠ v := by decide

/-- Curry finds a home in the lazy register: kimp Z ⊥ = Z. -/
theorem curry_kleene_home : kor (knot Z) F = Z := rfl

/-- Parity, cycle 3 with one inversion: no models. -/
theorem odd3_no_model : ∀ a b c : V, ¬(a = b ∧ b = c ∧ c = znot a) := by
  decide

/-- Parity, cycle 2 with two inversions: models EXIST (underdetermination). -/
theorem even2_has_model : ∃ a b : V, a = znot b ∧ b = znot a :=
  ⟨T, F, rfl, rfl⟩

/-- The Yablo truncation (n=3): the unique model F,F,T — grounded, no
paradox; Yablo's paradox lives only at actual infinity. -/
theorem yablo3_unique : ∀ a b c : V,
    (a = zand (znot b) (znot c) ∧ b = znot c ∧ c = T) ↔
    (a = F ∧ b = F ∧ c = T) := by decide

/-- The crocodile: the deal R↔M at the grounded point (Z,Z) does not
earn truth — the contract is void. -/
theorem crocodile_deal_void : zxnor Z Z = F := rfl

/-- Passport discriminator (E18): the even two-cycle has EXACTLY two
classical models — underdetermined, liftable by stipulation; the odd
loop has none (liar_period2, carousel_no_fp) — paradox, permanent. -/
theorem passport_even2 : ∀ a b : V, (a = T ∨ a = F) → (b = T ∨ b = F) →
    ((a = znot b ∧ b = znot a) ↔
     ((a = T ∧ b = F) ∨ (a = F ∧ b = T))) := by decide

#print axioms ui_law_dom2
#print axioms notex_allnot_dom2_fails
#print axioms liar_period2
#print axioms carousel_period4
#print axioms curry_homeless
#print axioms yablo3_unique
#print axioms passport_even2

end V
