import ZTL

/-!
# Emergence — when can strong emergence be established? Zero axioms.

Written 2026-11-27 at the curator's word, after Mary's room and «sensus est, ergo est». His questions: «Сможет ли ZTL
отделить эмерджентное, или установить его существование» … «Запиши это или теорема получается?». Twin of VR-ZTL's
`ZTL/Emergence.agda`. The judge's runs on the same situations are in VR-ZTL `research/mary/judge_emergence.py`.

SETTING. A base is a valuation `b : Nat → V` of the base atoms, the physical facts of one case. A quantity `q`, the
sensing of that case, is fixed by the base through a formula `φ` when `evalF b φ = q`. "q supervenes on the base"
means that one φ fixes q in every case. "q is strongly emergent over the base" means that no φ does.

PROVED HERE:
1. `one_case_fits_T`, `one_case_fits_F` — one case NEVER refutes supervenience. Any act-grounded value (T or F) is
   fixed by some formula (`top` or `bot`).
2. `twin_refutes_all` — a WITNESSED TWIN refutes supervenience for EVERY formula at once. Two cases whose bases agree
   atom by atom and whose q differ admit no φ that fixes q in both. This follows from pointwise congruence of
   evaluation.
3. `zombie_on_credit` — a CONCEIVED twin refutes nothing. With q₂ = Z (no act witnesses the absence), Z refines to T,
   and `top` then fixes both cases.
4. `emergence_relative` — emergence is relative to the declared base. Cases that agree everywhere but at one atom k,
   left out of the base, are separated by `atom k`, so over the larger base they are no twins.

NOT CLAIMED: that sensing is or is not emergent. The theorem says what kind of ground would settle it.
-/

namespace Emergence

open V

/-- Evaluation depends on the valuation pointwise. -/
theorem evalF_congr' (v w : Nat → V) (h : ∀ n, v n = w n) : ∀ φ : Fm, evalF v φ = evalF w φ
  | .atom n => h n
  | .top => rfl
  | .bot => rfl
  | .neg φ => by show znot (evalF v φ) = znot (evalF w φ); rw [evalF_congr' v w h φ]
  | .conj φ ψ => by
      show zand (evalF v φ) (evalF v ψ) = zand (evalF w φ) (evalF w ψ)
      rw [evalF_congr' v w h φ, evalF_congr' v w h ψ]
  | .disj φ ψ => by
      show zor (evalF v φ) (evalF v ψ) = zor (evalF w φ) (evalF w ψ)
      rw [evalF_congr' v w h φ, evalF_congr' v w h ψ]
  | .imp φ ψ => by
      show zimp (evalF v φ) (evalF v ψ) = zimp (evalF w φ) (evalF w ψ)
      rw [evalF_congr' v w h φ, evalF_congr' v w h ψ]
  | .xor φ ψ => by
      show zxor (evalF v φ) (evalF v ψ) = zxor (evalF w φ) (evalF w ψ)
      rw [evalF_congr' v w h φ, evalF_congr' v w h ψ]
  | .xnor φ ψ => by
      show zxnor (evalF v φ) (evalF v ψ) = zxnor (evalF w φ) (evalF w ψ)
      rw [evalF_congr' v w h φ, evalF_congr' v w h ψ]

/-- φ fixes q in the case with base b. -/
def fixes (φ : Fm) (b : Nat → V) (q : V) : Prop := evalF b φ = q

/-- (1) One case never refutes supervenience. -/
theorem one_case_fits_T (b : Nat → V) : ∃ φ, fixes φ b T := ⟨.top, rfl⟩
theorem one_case_fits_F (b : Nat → V) : ∃ φ, fixes φ b F := ⟨.bot, rfl⟩

/-- (2) A witnessed twin refutes supervenience for every formula. -/
theorem twin_refutes_all (b₁ b₂ : Nat → V) (q₁ q₂ : V) (same : ∀ n, b₁ n = b₂ n) (differ : q₁ ≠ q₂) :
    ∀ φ : Fm, ¬ (fixes φ b₁ q₁ ∧ fixes φ b₂ q₂) :=
  fun φ ⟨f₁, f₂⟩ => differ (f₁.symm.trans ((evalF_congr' b₁ b₂ same φ).trans f₂))

/-- (3) A conceived twin (q₂ = Z) refutes nothing: Z refines to T, and `top` then fixes both cases. -/
theorem zombie_on_credit (b₁ b₂ : Nat → V) : leqb Z T = true ∧ fixes .top b₁ T ∧ fixes .top b₂ T :=
  ⟨rfl, rfl, rfl⟩

/-- (4) Emergence is relative to the declared base: cases that agree everywhere but at one atom k are separated by
`atom k`. -/
theorem emergence_relative (e₁ e₂ : Nat → V) (k : Nat) (_agree : ∀ n, n ≠ k → e₁ n = e₂ n)
    (q₁ q₂ : V) (h₁ : q₁ = e₁ k) (h₂ : q₂ = e₂ k) : fixes (.atom k) e₁ q₁ ∧ fixes (.atom k) e₂ q₂ :=
  ⟨h₁.symm, h₂.symm⟩

/-- **THE THEOREM.** One case never establishes strong emergence. A witnessed twin establishes it over the declared base,
for every formula at once. A conceived twin does not. And over a larger base it may vanish, so "this base is all of
physics" stays a premise. -/
theorem emergence_verdict :
    (∀ b : Nat → V, ∃ φ, fixes φ b T) ∧
    (∀ (b₁ b₂ : Nat → V) (q₁ q₂ : V), (∀ n, b₁ n = b₂ n) → q₁ ≠ q₂ → ∀ φ, ¬ (fixes φ b₁ q₁ ∧ fixes φ b₂ q₂)) ∧
    leqb Z T = true ∧
    (∀ (e₁ e₂ : Nat → V) (k : Nat), (∀ n, n ≠ k → e₁ n = e₂ n) →
      ∀ q₁ q₂ : V, q₁ = e₁ k → q₂ = e₂ k → fixes (.atom k) e₁ q₁ ∧ fixes (.atom k) e₂ q₂) :=
  ⟨one_case_fits_T, twin_refutes_all, rfl, emergence_relative⟩

end Emergence

#print axioms Emergence.evalF_congr'
#print axioms Emergence.one_case_fits_T
#print axioms Emergence.one_case_fits_F
#print axioms Emergence.twin_refutes_all
#print axioms Emergence.zombie_on_credit
#print axioms Emergence.emergence_relative
#print axioms Emergence.emergence_verdict
