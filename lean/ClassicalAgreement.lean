import ZTL

/-!
# Conservativity over classical logic, for the WHOLE language. Zero axioms.

The card `CLASSIC-VS-ZTL.md` claims two things about our relation to
classical logic, and until now both were *measurements* — 2906 formulas
against four verified markings, zero divergences. A measurement over a
sample is exactly what this project refuses to accept from others, so
here they are as theorems over the whole formula language:

1. `evalF_agrees` — on a Z-FREE valuation, ZTL evaluation and classical
   evaluation give the same answer, for every formula. Structural
   induction, not enumeration: the formula language is infinite.
2. `ztl_taut_is_classical` — every ZTL tautology is a classical
   tautology. The gain column of LAWS is therefore closed by proof, not
   by failure to find a counterexample.
3. `not_conversely` — and the inclusion is STRICT: `p → p` is a
   classical tautology that fails here at a mark. One exhibited witness,
   so the two theorems above cannot be read as "the logics coincide".

Nothing here uses the third value in a clever way; that is the point.
The whole content is that Z is a discipline about UNVERIFIED ground and
takes nothing away from verified ground.
-/

namespace V

/-- A classical truth value seen as a ZTL value: the mark never appears. -/
def emb : Bool → V
  | true  => T
  | false => F

/-- Classical evaluation of the same formula language. -/
def cval (b : Nat → Bool) : Fm → Bool
  | .atom n   => b n
  | .top      => true
  | .bot      => false
  | .neg φ    => !(cval b φ)
  | .conj φ ψ => (cval b φ) && (cval b ψ)
  | .disj φ ψ => (cval b φ) || (cval b ψ)
  | .imp φ ψ  => !(cval b φ) || (cval b ψ)
  | .xor φ ψ  => (cval b φ) != (cval b ψ)
  | .xnor φ ψ => (cval b φ) == (cval b ψ)

/-! ## The two lift lemmas: on embedded values the lift IS the classical
connective. Both are finite checks over `Bool`, done by case split so the
reader can see there is no enumeration of the formula language. -/

theorem lift1_emb (f : Bool → Bool) (a : Bool) :
    lift1 f (emb a) = emb (f a) := by
  cases a
  · show (if (f false && true) = true then T else F) = emb (f false)
    cases hf : f false <;> decide
  · show (if (f true && true) = true then T else F) = emb (f true)
    cases hf : f true <;> decide

theorem lift2_emb (f : Bool → Bool → Bool) (a c : Bool) :
    lift2 f (emb a) (emb c) = emb (f a c) := by
  cases a
  · cases c
    · show (if ((f false false && true) && true) = true then T else F)
             = emb (f false false)
      cases hf : f false false <;> decide
    · show (if ((f false true && true) && true) = true then T else F)
             = emb (f false true)
      cases hf : f false true <;> decide
  · cases c
    · show (if ((f true false && true) && true) = true then T else F)
             = emb (f true false)
      cases hf : f true false <;> decide
    · show (if ((f true true && true) && true) = true then T else F)
             = emb (f true true)
      cases hf : f true true <;> decide

/-- **Conservativity.** On a valuation that carries no mark, ZTL agrees
with classical logic — for every formula of the language. -/
theorem evalF_agrees (b : Nat → Bool) :
    ∀ φ : Fm, evalF (fun n => emb (b n)) φ = emb (cval b φ) := by
  intro φ
  induction φ with
  | atom n   => rfl
  | top      => rfl
  | bot      => rfl
  | neg φ ih =>
      show znot (evalF (fun n => emb (b n)) φ) = _
      rw [ih]; exact lift1_emb _ _
  | conj φ ψ ihφ ihψ =>
      show zand _ _ = _
      rw [ihφ, ihψ]; exact lift2_emb _ _ _
  | disj φ ψ ihφ ihψ =>
      show zor _ _ = _
      rw [ihφ, ihψ]; exact lift2_emb _ _ _
  | imp φ ψ ihφ ihψ =>
      show zimp _ _ = _
      rw [ihφ, ihψ]; exact lift2_emb _ _ _
  | xor φ ψ ihφ ihψ =>
      show zxor _ _ = _
      rw [ihφ, ihψ]; exact lift2_emb _ _ _
  | xnor φ ψ ihφ ihψ =>
      show zxnor _ _ = _
      rw [ihφ, ihψ]; exact lift2_emb _ _ _

/-- **No new laws.** A formula valid in ZTL under every valuation is
valid classically. The gain column of laws is closed by proof. -/
theorem ztl_taut_is_classical (φ : Fm)
    (h : ∀ v : Nat → V, evalF v φ = T) :
    ∀ b : Nat → Bool, cval b φ = true := by
  intro b
  have hv := h (fun n => emb (b n))
  rw [evalF_agrees b φ] at hv
  cases hb : cval b φ with
  | true  => rfl
  | false => rw [hb] at hv; exact absurd hv (by decide)

/-- **And strictly so.** `p → p` is classically valid and fails here on a
marked atom: the inclusion of validities is proper, so the theorems above
say "conservative", never "the same logic". -/
theorem not_conversely :
    (∀ b : Nat → Bool, cval b (.imp (.atom 0) (.atom 0)) = true) ∧
    ¬ (∀ v : Nat → V, evalF v (.imp (.atom 0) (.atom 0)) = T) := by
  constructor
  · intro b
    show (!(b 0) || b 0) = true
    cases h : b 0 <;> decide
  · intro h; exact absurd (h (fun _ => Z)) (by decide)

#print axioms lift1_emb
#print axioms lift2_emb
#print axioms evalF_agrees
#print axioms ztl_taut_is_classical
#print axioms not_conversely

end V
