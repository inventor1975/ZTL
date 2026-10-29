import ZTL
import ZComplete
/-! # ZBochvar — ZTL and Bochvar's external logic B^e, both directions. Zero axioms.

Paper v8 §4.2, Proposition 5 (2026-10-29, asked for by the cloud referee of v8: "the only unformalised proposition
in a paper whose selling point is formalisation").

B^e is the logic of the matrix ⟨WK^e, {1}⟩ [Bonzio & Pra Baldi 2025]: weak Kleene ¬, ∧, ∨ (the middle value ½
contaminates), the external operators J₀ ("is 0"), J₁ ("is ½"), J₂ ("is 1"), and the constants 0, 1. Here ½ is Z.
(1) `zeta_exact`: the translation ζ sends every ZTL formula to a B^e formula with the same value at every valuation;
    so φ is T in ZTL exactly where ζφ is designated in B^e, and Γ ⊨ φ iff ζΓ ⊢ ζφ.
(2) `external_is_ztl`: every B^e formula that never takes ½ — in particular every external formula — has the value
    of some ZTL formula at every valuation (by `Cpl.ztl_expressively_complete`). So ζ is onto the two-valued
    fragment of B^e up to equivalence: by the functions they compute, ZTL is that fragment in another basis.
-/

namespace V
namespace Boch
open Cpl

inductive BFm where
  | atom : Nat → BFm
  | zero : BFm
  | one  : BFm
  | wneg : BFm → BFm
  | wand : BFm → BFm → BFm
  | wor  : BFm → BFm → BFm
  | j0   : BFm → BFm
  | j1   : BFm → BFm
  | j2   : BFm → BFm

/-- weak Kleene: ½ (Z) contaminates -/
def wnot : V → V | T => F | F => T | Z => Z
def wa : V → V → V
  | T, T => T | T, F => F | T, Z => Z
  | F, T => F | F, F => F | F, Z => Z
  | Z, T => Z | Z, F => Z | Z, Z => Z
def wo : V → V → V
  | T, T => T | T, F => T | T, Z => Z
  | F, T => T | F, F => F | F, Z => Z
  | Z, T => Z | Z, F => Z | Z, Z => Z
def jj0 : V → V | T => F | F => T | Z => F
def jj1 : V → V | T => F | F => F | Z => T
def jj2 : V → V | T => T | F => F | Z => F

def beval (v : Nat → V) : BFm → V
  | .atom n => v n
  | .zero => F
  | .one => T
  | .wneg χ => wnot (beval v χ)
  | .wand χ ω => wa (beval v χ) (beval v ω)
  | .wor χ ω => wo (beval v χ) (beval v ω)
  | .j0 χ => jj0 (beval v χ)
  | .j1 χ => jj1 (beval v χ)
  | .j2 χ => jj2 (beval v χ)

/-- the translation ζ of Proposition 5 -/
def zeta : Fm → BFm
  | .atom n => .atom n
  | .top => .one
  | .bot => .zero
  | .neg φ => .j0 (zeta φ)
  | .conj φ ψ => .wand (.j2 (zeta φ)) (.j2 (zeta ψ))
  | .disj φ ψ => .wor (.j2 (zeta φ)) (.j2 (zeta ψ))
  | .imp φ ψ => .wor (.j0 (zeta φ)) (.j2 (zeta ψ))
  | .xor φ ψ => .wor (.wand (.j2 (zeta φ)) (.j0 (zeta ψ))) (.wand (.j0 (zeta φ)) (.j2 (zeta ψ)))
  | .xnor φ ψ => .wor (.wand (.j2 (zeta φ)) (.j2 (zeta ψ))) (.wand (.j0 (zeta φ)) (.j0 (zeta ψ)))

theorem c_neg : ∀ a : V, jj0 a = znot a := by decide
theorem c_and : ∀ a b : V, wa (jj2 a) (jj2 b) = zand a b := by decide
theorem c_or : ∀ a b : V, wo (jj2 a) (jj2 b) = zor a b := by decide
theorem c_imp : ∀ a b : V, wo (jj0 a) (jj2 b) = zimp a b := by decide
theorem c_xor : ∀ a b : V, wo (wa (jj2 a) (jj0 b)) (wa (jj0 a) (jj2 b)) = zxor a b := by decide
theorem c_xnor : ∀ a b : V, wo (wa (jj2 a) (jj2 b)) (wa (jj0 a) (jj0 b)) = zxnor a b := by decide

/-- **Proposition 5, (1).** ζφ has, at every valuation, the value φ has in ZTL. -/
theorem zeta_exact (v : Nat → V) : ∀ φ : Fm, beval v (zeta φ) = evalF v φ
  | .atom _ => rfl
  | .top => rfl
  | .bot => rfl
  | .neg φ => by
      show jj0 (beval v (zeta φ)) = znot (evalF v φ)
      rw [zeta_exact v φ]; exact c_neg _
  | .conj φ ψ => by
      show wa (jj2 (beval v (zeta φ))) (jj2 (beval v (zeta ψ))) = zand (evalF v φ) (evalF v ψ)
      rw [zeta_exact v φ, zeta_exact v ψ]; exact c_and _ _
  | .disj φ ψ => by
      show wo (jj2 (beval v (zeta φ))) (jj2 (beval v (zeta ψ))) = zor (evalF v φ) (evalF v ψ)
      rw [zeta_exact v φ, zeta_exact v ψ]; exact c_or _ _
  | .imp φ ψ => by
      show wo (jj0 (beval v (zeta φ))) (jj2 (beval v (zeta ψ))) = zimp (evalF v φ) (evalF v ψ)
      rw [zeta_exact v φ, zeta_exact v ψ]; exact c_imp _ _
  | .xor φ ψ => by
      show wo (wa (jj2 (beval v (zeta φ))) (jj0 (beval v (zeta ψ))))
             (wa (jj0 (beval v (zeta φ))) (jj2 (beval v (zeta ψ)))) = zxor (evalF v φ) (evalF v ψ)
      rw [zeta_exact v φ, zeta_exact v ψ]; exact c_xor _ _
  | .xnor φ ψ => by
      show wo (wa (jj2 (beval v (zeta φ))) (jj2 (beval v (zeta ψ))))
             (wa (jj0 (beval v (zeta φ))) (jj0 (beval v (zeta ψ)))) = zxnor (evalF v φ) (evalF v ψ)
      rw [zeta_exact v φ, zeta_exact v ψ]; exact c_xnor _ _

/-- Consequence: Γ ⊨ φ in ZTL iff ζΓ ⊢ ζφ in B^e (designated value T, i.e. 1, in both). -/
theorem zeta_consequence (Γ : List Fm) (φ : Fm) :
    (∀ v, (∀ γ ∈ Γ, evalF v γ = T) → evalF v φ = T) ↔
    (∀ v, (∀ γ ∈ Γ, beval v (zeta γ) = T) → beval v (zeta φ) = T) :=
  ⟨fun h v hg => by rw [zeta_exact]; exact h v (fun γ hγ => by rw [← zeta_exact]; exact hg γ hγ),
   fun h v hg => by rw [← zeta_exact]; exact h v (fun γ hγ => by rw [zeta_exact]; exact hg γ hγ)⟩

/-! ## (2) The converse: a two-valued B^e formula is a ZTL formula -/

def batoms : BFm → List Nat
  | .atom n => [n]
  | .zero => []
  | .one => []
  | .wneg χ => batoms χ
  | .wand χ ω => batoms χ ++ batoms ω
  | .wor χ ω => batoms χ ++ batoms ω
  | .j0 χ => batoms χ
  | .j1 χ => batoms χ
  | .j2 χ => batoms χ

theorem memB_app_l (n : Nat) (l m : List Nat) (h : memB n l = true) : memB n (l ++ m) = true :=
  memB_append n l m (Or.inl h)
theorem memB_app_r (n : Nat) (l m : List Nat) (h : memB n m = true) : memB n (l ++ m) = true :=
  memB_append n l m (Or.inr h)

theorem beval_congr (v w : Nat → V) : ∀ χ : BFm, (∀ n, memB n (batoms χ) = true → v n = w n) →
    beval v χ = beval w χ
  | .atom n, h => h n (by show (decide (n = n) || memB n []) = true; rw [decide_eq_true rfl]; rfl)
  | .zero, _ => rfl
  | .one, _ => rfl
  | .wneg χ, h => by show wnot _ = wnot _; rw [beval_congr v w χ h]
  | .j0 χ, h => by show jj0 _ = jj0 _; rw [beval_congr v w χ h]
  | .j1 χ, h => by show jj1 _ = jj1 _; rw [beval_congr v w χ h]
  | .j2 χ, h => by show jj2 _ = jj2 _; rw [beval_congr v w χ h]
  | .wand χ ω, h => by
      show wa _ _ = wa _ _
      rw [beval_congr v w χ (fun n hn => h n (memB_app_l n _ _ hn)),
          beval_congr v w ω (fun n hn => h n (memB_app_r n _ _ hn))]
  | .wor χ ω, h => by
      show wo _ _ = wo _ _
      rw [beval_congr v w χ (fun n hn => h n (memB_app_l n _ _ hn)),
          beval_congr v w ω (fun n hn => h n (memB_app_r n _ _ hn))]

theorem toV_isT : ∀ x : V, x ≠ Z → toV (isTB x) = x := by decide

/-- **Proposition 5, (2).** Every B^e formula that never takes the middle value — every external formula among
them — has, at every valuation, the value of some ZTL formula. -/
theorem external_is_ztl (χ : BFm) (h2 : ∀ v, beval v χ ≠ Z) : ∃ φ : Fm, ∀ v, evalF v φ = beval v χ := by
  let g : (Nat → V) → Bool := fun v => isTB (beval v χ)
  have hD : Dep (batoms χ) g := fun v w ha => by
    show isTB (beval v χ) = isTB (beval w χ)
    rw [beval_congr v w χ (fun n hn => agree_mem n _ v w ha hn)]
  obtain ⟨φ, hφ⟩ := ztl_expressively_complete (batoms χ) g hD
  exact ⟨φ, fun v => by rw [hφ v]; exact toV_isT _ (h2 v)⟩

/-- The same-value detector Δ(p, q) = (p ↔ q) ∨ (¬(p ↔ p) ∧ ¬(q ↔ q)) of paper v8 §3.8, as a formula, is `dEq`. -/
theorem delta_formula : ∀ a b : V,
    evalF (fun n => if n = 0 then a else b)
      (.disj (.xnor (.atom 0) (.atom 1)) (.conj (.neg (.xnor (.atom 0) (.atom 0))) (.neg (.xnor (.atom 1) (.atom 1)))))
      = (if a = b then T else F) := by decide

end Boch
end V

#print axioms V.Boch.zeta_exact
#print axioms V.Boch.zeta_consequence
#print axioms V.Boch.beval_congr
#print axioms V.Boch.external_is_ztl
#print axioms V.Boch.delta_formula
