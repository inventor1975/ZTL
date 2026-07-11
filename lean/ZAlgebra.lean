import ZTL

/-!
# The algebraic passport: J-operators, the external implication E,
# the Blok–Pigozzi witnesses, structurality. Zero axioms.

The chain (E14): fallen idempotence gives the truth detector
J_T(p) = p∧p; with J_F and isZ every external function is a J-DNF;
the definable E(p,q) = ¬(p∧p) ∨ (q∧q) satisfies a TWO-WAY deduction
theorem (the primitive → stays one-way); the same-value detector Δ and
the truth equation p∧p ≈ ¬(p∧¬p) witness the Blok–Pigozzi conditions —
ZTL is algebraizable. Self-extensionality fails. The substitution lemma
makes ⊨ structural.
-/

namespace V

/-! ## J-operators from fallen laws -/

def jT (x : V) : V := zand x x
def jF (x : V) : V := zand (znot x) (znot x)

/-- Exact indicators: J_T detects T, J_F detects F, isZ detects Z. -/
theorem jT_spec : ∀ x : V, jT x = T ↔ x = T := by decide
theorem jF_spec : ∀ x : V, jF x = T ↔ x = F := by decide
theorem jZ_spec : ∀ x : V, isZ x = T ↔ x = Z := by decide

/-- The indicators are classical and disjointly cover V. -/
theorem indicators_partition : ∀ x : V,
    (jT x = T ∧ jF x = F ∧ isZ x = F) ∨
    (jT x = F ∧ jF x = T ∧ isZ x = F) ∨
    (jT x = F ∧ jF x = F ∧ isZ x = T) := by decide

/-! ## Expressive completeness, unary case (n = 2 measured in Python) -/

/-- J-DNF builder for an arbitrary unary external function given by its
value bits at T, F, Z. -/
def mkU (bT bF bZ : Bool) (x : V) : V :=
  zor (zor (cond bT (jT x) F) (cond bF (jF x) F)) (cond bZ (isZ x) F)

/-- Every unary external function is expressed by its J-DNF: all 8
target tables, all 3 inputs. -/
theorem unary_complete : ∀ (bT bF bZ : Bool) (x : V),
    mkU bT bF bZ x = (match x with
                      | T => cond bT T F
                      | F => cond bF T F
                      | Z => cond bZ T F) := by decide

/-! ## The external implication E and its two-way deduction theorem -/

def eimp (a b : V) : V := zor (znot (zand a a)) (zand b b)

/-- E internalizes the meta-implication "if a is true then b is true". -/
theorem eimp_spec : ∀ a b : V, eimp a b = T ↔ (a = T → b = T) := by decide

/-- The primitive arrow does not (one-way DDT, the keel): here is the
cell where they differ. -/
theorem eimp_vs_zimp : eimp Z Z = T ∧ zimp Z Z = F := ⟨rfl, rfl⟩

/-- E on formulas. -/
def EimpF (φ ψ : Fm) : Fm := .disj (.neg (.conj φ φ)) (.conj ψ ψ)

/-- Recursive "all premises are T" (no list membership). -/
def allT (v : Nat → V) : List Fm → Prop
  | [] => True
  | φ :: Γ => evalF v φ = T ∧ allT v Γ

/-- THE FULL DEDUCTION THEOREM for E, with premises:
Γ, φ ⊨ ψ  ⟺  Γ ⊨ E(φ,ψ) — both directions, over the whole language. -/
theorem ddt_E (Γ : List Fm) (φ ψ : Fm) :
    (∀ v, allT v Γ → evalF v φ = T → evalF v ψ = T) ↔
    (∀ v, allT v Γ → evalF v (EimpF φ ψ) = T) := by
  constructor
  · intro h v hΓ
    exact (eimp_spec (evalF v φ) (evalF v ψ)).mpr (h v hΓ)
  · intro h v hΓ hφ
    exact (eimp_spec (evalF v φ) (evalF v ψ)).mp (h v hΓ) hφ

/-! ## The Blok–Pigozzi witnesses on the matrix -/

/-- Δ(p,q): the same-value detector, a J-DNF over pairs. -/
def dEq (a b : V) : V :=
  zor (zor (zand (jT a) (jT b)) (zand (jF a) (jF b)))
      (zand (isZ a) (isZ b))

theorem dEq_spec : ∀ a b : V, dEq a b = T ↔ a = b := by decide

/-- (i) reflexivity: ⊨ Δ(p,p). -/
theorem bp_refl : ∀ a : V, dEq a a = T := by decide

/-- (ii) detachment: p, Δ(p,q) ⊨ q. -/
theorem bp_mp : ∀ a b : V, a = T → dEq a b = T → b = T := by decide

/-- (iii) congruence for all six connectives. -/
theorem bp_cong_not : ∀ a b : V,
    dEq a b = T → dEq (znot a) (znot b) = T := by decide
theorem bp_cong_and : ∀ a b c d : V, dEq a c = T → dEq b d = T →
    dEq (zand a b) (zand c d) = T := by decide
theorem bp_cong_or : ∀ a b c d : V, dEq a c = T → dEq b d = T →
    dEq (zor a b) (zor c d) = T := by decide
theorem bp_cong_imp : ∀ a b c d : V, dEq a c = T → dEq b d = T →
    dEq (zimp a b) (zimp c d) = T := by decide
theorem bp_cong_xor : ∀ a b c d : V, dEq a c = T → dEq b d = T →
    dEq (zxor a b) (zxor c d) = T := by decide
theorem bp_cong_xnor : ∀ a b c d : V, dEq a c = T → dEq b d = T →
    dEq (zxnor a b) (zxnor c d) = T := by decide

/-- The truth equation: p∧p ≈ ¬(p∧¬p) holds exactly at p = T. -/
theorem truth_equation : ∀ x : V,
    (zand x x = znot (zand x (znot x))) ↔ x = T := by decide

/-- (iv) p ⊣⊨ Δ(δ(p), ε(p)) for δ(p) = p∧p, ε(p) = ¬(p∧¬p). -/
theorem bp_iv : ∀ x : V,
    x = T ↔ dEq (zand x x) (znot (zand x (znot x))) = T := by decide

/-! Conditions (i)–(iv) are the Blok–Pigozzi characterization
(1989, Thm 4.7): ZTL is algebraizable. The general theorem is cited,
not formalized; every finite witness above is kernel-checked. -/

/-! ## Self-extensionality fails -/

/-- p ⊣⊨ p∧p: idempotence is dead as a law, alive as interderivability. -/
theorem idem_interderivable :
    (∀ a : V, a = T → zand a a = T) ∧ (∀ a : V, zand a a = T → a = T) :=
  ⟨by decide, by decide⟩

/-- ...yet interderivability is not a congruence: ¬(p∧p) ⊭ ¬p. -/
theorem not_selfextensional :
    ¬ ∀ a : V, znot (zand a a) = T → znot a = T := by decide

/-! ## Structurality: the substitution lemma -/

/-- Uniform substitution on formulas. -/
def substF (σ : Nat → Fm) : Fm → Fm
  | .atom n   => σ n
  | .neg φ    => .neg (substF σ φ)
  | .conj φ ψ => .conj (substF σ φ) (substF σ ψ)
  | .disj φ ψ => .disj (substF σ φ) (substF σ ψ)
  | .imp φ ψ  => .imp (substF σ φ) (substF σ ψ)
  | .xor φ ψ  => .xor (substF σ φ) (substF σ ψ)
  | .xnor φ ψ => .xnor (substF σ φ) (substF σ ψ)

/-- Binary congruence, in-house and axiom-free (Eq.rec only). -/
theorem congr2 (f : V → V → V) {a a' b b' : V}
    (h1 : a = a') (h2 : b = b') : f a b = f a' b' := h1 ▸ h2 ▸ rfl

/-- The substitution lemma: evaluating σφ = evaluating φ under the
pushed-forward valuation. -/
theorem evalF_subst (σ : Nat → Fm) (v : Nat → V) :
    ∀ φ : Fm, evalF v (substF σ φ) = evalF (fun n => evalF v (σ n)) φ := by
  intro φ
  induction φ with
  | atom n => rfl
  | neg φ ih => exact congrArg znot ih
  | conj φ ψ ih1 ih2 => exact congr2 zand ih1 ih2
  | disj φ ψ ih1 ih2 => exact congr2 zor ih1 ih2
  | imp φ ψ ih1 ih2 => exact congr2 zimp ih1 ih2
  | xor φ ψ ih1 ih2 => exact congr2 zxor ih1 ih2
  | xnor φ ψ ih1 ih2 => exact congr2 zxnor ih1 ih2

/-- σ applied to a premise list, recursively. -/
def substL (σ : Nat → Fm) : List Fm → List Fm
  | [] => []
  | φ :: Γ => substF σ φ :: substL σ Γ

theorem allT_subst (σ : Nat → Fm) (v : Nat → V) : ∀ Γ : List Fm,
    allT v (substL σ Γ) ↔ allT (fun n => evalF v (σ n)) Γ := by
  intro Γ
  induction Γ with
  | nil => exact Iff.rfl
  | cons φ Γ ih =>
    exact andCongrLocal (iffOfEqLocal (congrArg (· = T) (evalF_subst σ v φ))) ih
where
  iffOfEqLocal {a b : Prop} (h : a = b) : a ↔ b := h ▸ Iff.rfl
  andCongrLocal {a b c d : Prop} (h1 : a ↔ c) (h2 : b ↔ d) :
      (a ∧ b) ↔ (c ∧ d) :=
    ⟨fun ⟨x, y⟩ => ⟨h1.mp x, h2.mp y⟩, fun ⟨x, y⟩ => ⟨h1.mpr x, h2.mpr y⟩⟩

/-- STRUCTURALITY: Γ ⊨ φ implies σΓ ⊨ σφ — ⊨ is a structural
(Tarskian) consequence relation. -/
theorem entails_structural (σ : Nat → Fm) (Γ : List Fm) (φ : Fm)
    (h : ∀ v, allT v Γ → evalF v φ = T) :
    ∀ v, allT v (substL σ Γ) → evalF v (substF σ φ) = T := by
  intro v hΓ
  have hv := h (fun n => evalF v (σ n)) ((allT_subst σ v Γ).mp hΓ)
  exact (evalF_subst σ v φ).trans hv

#print axioms unary_complete
#print axioms ddt_E
#print axioms dEq_spec
#print axioms bp_cong_xnor
#print axioms truth_equation
#print axioms bp_iv
#print axioms not_selfextensional
#print axioms evalF_subst
#print axioms entails_structural

end V
