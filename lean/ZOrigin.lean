import ZTL

/-!
# Where F and T come from: the order of birth under pure doubt. Zero axioms. (2026-09-28)

Classical negation is an involution: ¬T = F and ¬F = T, and neither value is prior to the
other. ZTL breaks that symmetry in one cell, ¬Z = F, and the tables then carry an ORDER OF
BIRTH. Start from pure doubt — every atom unverified (Z), no constant handed in — and ask what
the connectives can make of it:

    doubt_gives_F      one connective over doubt alone gives F, every time (all six)
    T_through_F        a formula over pure doubt is T only if some PROPER subformula is F:
                       truth is never made from doubt directly, only through a falsehood
    T_second           and it is made that way: ¬¬p is T when p is Z (depth 2, via ¬Z = F)
    no_T_at_depth_one  hence no single connective over atoms ever yields T

and, already proved in ZTL.lean, `evalF_classical`: no compound formula is Z — doubt is not
made by anything; it lives on the atom and nowhere else.

So the birth order the paper names (§4: nothing, doubt, free denial, earned affirmation —
N, Z, F, T) is not a gloss laid over the tables: Z is only given, F is the first thing doubt
yields, T comes only after an F. In classical logic, with no Z, this
statement has nothing to be about.

Why the constants are excluded: `.top` hands T in without deriving it, so over a language
with constants "truth only through a falsehood" is false for the trivial reason that T was
supplied. `Pure` is exactly the language of doubt: atoms and connectives.

What the theorem is NOT: a claim that T under pure doubt says anything about the atoms.
¬¬p is T while p stays Z — which is precisely why ¬¬p ⊨ p fails in ZTL.
-/

namespace ZOrigin

open V

/-- Built from atoms and connectives only: no constant hands a value in. -/
def Pure : Fm → Prop
  | .atom _   => True
  | .top      => False
  | .bot      => False
  | .neg φ    => Pure φ
  | .conj φ ψ => Pure φ ∧ Pure ψ
  | .disj φ ψ => Pure φ ∧ Pure ψ
  | .imp φ ψ  => Pure φ ∧ Pure ψ
  | .xor φ ψ  => Pure φ ∧ Pure ψ
  | .xnor φ ψ => Pure φ ∧ Pure ψ

/-- φ has a PROPER subformula whose value is F. -/
def ThroughF (v : Nat → V) : Fm → Prop
  | .atom _   => False
  | .top      => False
  | .bot      => False
  | .neg φ    => evalF v φ = F ∨ ThroughF v φ
  | .conj φ ψ => (evalF v φ = F ∨ ThroughF v φ) ∨ (evalF v ψ = F ∨ ThroughF v ψ)
  | .disj φ ψ => (evalF v φ = F ∨ ThroughF v φ) ∨ (evalF v ψ = F ∨ ThroughF v ψ)
  | .imp φ ψ  => (evalF v φ = F ∨ ThroughF v φ) ∨ (evalF v ψ = F ∨ ThroughF v ψ)
  | .xor φ ψ  => (evalF v φ = F ∨ ThroughF v φ) ∨ (evalF v ψ = F ∨ ThroughF v ψ)
  | .xnor φ ψ => (evalF v φ = F ∨ ThroughF v φ) ∨ (evalF v ψ = F ∨ ThroughF v ψ)

/-- Pure doubt: every atom is unverified. -/
def AllZ (v : Nat → V) : Prop := ∀ n, v n = Z

/-! ### Doubt yields F first -/

/-- One connective over doubt alone: F, for every connective. -/
theorem doubt_gives_F :
    znot Z = F ∧ zand Z Z = F ∧ zor Z Z = F ∧ zimp Z Z = F ∧ zxor Z Z = F ∧ zxnor Z Z = F := by
  decide

/-- A binary connective that makes F of doubt makes T only from a classical input. -/
theorem bin_origin (op : V → V → V) (hzz : op Z Z ≠ T) (a b : V) (h : op a b = T) :
    a = F ∨ b = F ∨ a = T ∨ b = T := by
  cases a with
  | T => exact Or.inr (Or.inr (Or.inl rfl))
  | F => exact Or.inl rfl
  | Z =>
    cases b with
    | T => exact Or.inr (Or.inr (Or.inr rfl))
    | F => exact Or.inr (Or.inl rfl)
    | Z => exact absurd h hzz

/-- The binary step of `T_through_F`, stated once for all five connectives. -/
theorem bin_step (v : Nat → V) (op : V → V → V) (hzz : op Z Z ≠ T) (φ ψ : Fm)
    (ihφ : Pure φ → evalF v φ = T → ThroughF v φ)
    (ihψ : Pure ψ → evalF v ψ = T → ThroughF v ψ)
    (hp : Pure φ ∧ Pure ψ) (h : op (evalF v φ) (evalF v ψ) = T) :
    (evalF v φ = F ∨ ThroughF v φ) ∨ (evalF v ψ = F ∨ ThroughF v ψ) := by
  cases bin_origin op hzz _ _ h with
  | inl h1 => exact Or.inl (Or.inl h1)
  | inr h =>
    cases h with
    | inl h2 => exact Or.inr (Or.inl h2)
    | inr h =>
      cases h with
      | inl h3 => exact Or.inl (Or.inr (ihφ hp.1 h3))
      | inr h4 => exact Or.inr (Or.inr (ihψ hp.2 h4))

/-! ### Truth is born only through a falsehood -/

theorem T_through_F (v : Nat → V) (hz : AllZ v) :
    ∀ φ : Fm, Pure φ → evalF v φ = T → ThroughF v φ := by
  intro φ
  induction φ with
  | atom n =>
    intro _ h
    have h' : v n = T := h
    rw [hz n] at h'
    exact absurd h' (by decide)
  | top => intro hp; exact False.elim hp
  | bot => intro hp; exact False.elim hp
  | neg φ ih =>
    intro _ h
    have h' : znot (evalF v φ) = T := h
    show evalF v φ = F ∨ ThroughF v φ
    cases hφ : evalF v φ with
    | T => rw [hφ] at h'; exact absurd h' (by decide)
    | F => exact Or.inl rfl
    | Z => rw [hφ] at h'; exact absurd h' (by decide)
  | conj φ ψ ihφ ihψ =>
    intro hp h; exact bin_step v zand (by decide) φ ψ ihφ ihψ hp h
  | disj φ ψ ihφ ihψ =>
    intro hp h; exact bin_step v zor (by decide) φ ψ ihφ ihψ hp h
  | imp φ ψ ihφ ihψ =>
    intro hp h; exact bin_step v zimp (by decide) φ ψ ihφ ihψ hp h
  | xor φ ψ ihφ ihψ =>
    intro hp h; exact bin_step v zxor (by decide) φ ψ ihφ ihψ hp h
  | xnor φ ψ ihφ ihψ =>
    intro hp h; exact bin_step v zxnor (by decide) φ ψ ihφ ihψ hp h

/-- No single connective over atoms yields T under doubt: an atom has no proper subformula,
so a depth-one formula has nothing to be "through". -/
theorem no_T_at_depth_one (v : Nat → V) (hz : AllZ v) (m n : Nat) :
    evalF v (.neg (.atom n)) ≠ T ∧
    evalF v (.conj (.atom m) (.atom n)) ≠ T ∧ evalF v (.disj (.atom m) (.atom n)) ≠ T ∧
    evalF v (.imp (.atom m) (.atom n)) ≠ T ∧ evalF v (.xor (.atom m) (.atom n)) ≠ T ∧
    evalF v (.xnor (.atom m) (.atom n)) ≠ T := by
  have e : ∀ k, evalF v (.atom k) = Z := fun k => hz k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show znot (evalF v (.atom n)) ≠ T; rw [e n]; decide
  · show zand (evalF v (.atom m)) (evalF v (.atom n)) ≠ T; rw [e m, e n]; decide
  · show zor (evalF v (.atom m)) (evalF v (.atom n)) ≠ T; rw [e m, e n]; decide
  · show zimp (evalF v (.atom m)) (evalF v (.atom n)) ≠ T; rw [e m, e n]; decide
  · show zxor (evalF v (.atom m)) (evalF v (.atom n)) ≠ T; rw [e m, e n]; decide
  · show zxnor (evalF v (.atom m)) (evalF v (.atom n)) ≠ T; rw [e m, e n]; decide

/-- And the first truth is indeed made that way: ¬¬p is T when p is Z. -/
theorem T_second (v : Nat → V) (hz : AllZ v) :
    evalF v (.neg (.atom 0)) = F ∧ evalF v (.neg (.neg (.atom 0))) = T := by
  have e : evalF v (.atom 0) = Z := hz 0
  constructor
  · show znot (evalF v (.atom 0)) = F; rw [e]; decide
  · show znot (znot (evalF v (.atom 0))) = T; rw [e]; decide

/-- The whole order in one statement: Z is never made (it lives on atoms), F is made from doubt
alone, T is made only through an F. -/
theorem birth_order (v : Nat → V) (hz : AllZ v) :
    (∀ φ : Fm, (∃ n, φ = .atom n) ∨ evalF v φ = T ∨ evalF v φ = F) ∧
    evalF v (.neg (.atom 0)) = F ∧
    (∀ φ : Fm, Pure φ → evalF v φ = T → ThroughF v φ) :=
  ⟨evalF_classical v, (T_second v hz).1, T_through_F v hz⟩

end ZOrigin

#print axioms ZOrigin.doubt_gives_F
#print axioms ZOrigin.T_through_F
#print axioms ZOrigin.no_T_at_depth_one
#print axioms ZOrigin.T_second
#print axioms ZOrigin.birth_order
