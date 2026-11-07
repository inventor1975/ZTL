import ZField
/-!
# ZExpLaw — what `check_none` needs of `exp`, in TAYLOR form, and what follows. Zero axioms.

A tail of the Lean-checked `check_none` (curator, 2026-11-08: exp and ln). The exponential is a function `ex` on a
constructive ordered field `CF` with laws chosen so that VR's operational exponential (`ZExp.rexpR`, a limit of
partial sums, the reciprocal for negative arguments) can satisfy them from what ZTL already proves, with no addition
law (`e^(a+b) = eᵃ·eᵇ` is NOT among them — measured 2026-11-08: not proved for `rexpR`, and the hardest to prove):

  * `congr`, `mono`, `pos` — congruence, monotonicity, positivity;
  * `strict` — `a < b` gives `eᵃ < eᵇ`;
  * `recip` — `eᵈ · e^(−d) = 1`, at DYADIC points `d` (the only ones the readings evaluate);
  * `lo`, `hi` — at dyadic `d ≥ 0`, the partial sums: `n!·Tₙ(a) ≤ n!·eᵃ`, and, when `2a ≤ n + 1`,
    `n!·eᵃ ≤ n!·Tₙ(a) + 2aⁿ` (`Tₙ(a) = Σ_{k<n} aᵏ/k!`; `n!·Tₙ` is `W n a`, integer coefficients, no division).

From them: REFLECTION `eᵃ ≤ eᵇ → a ≤ b` (the logarithm's reading needs it).
-/

namespace ZExpLaw
open VR.CSR ZNumBin ZField

variable {α : Type} (S : CF α)

/-- `n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `aⁿ`. -/
def pw (a : α) : Nat → α
  | 0 => S.one
  | n + 1 => S.mul a (pw a n)

/-- `n! · Σ_{k<n} aᵏ/k!`, by `W (n+1) = (n+1)·(W n + aⁿ)`. -/
def W (a : α) : Nat → α
  | 0 => S.zero
  | n + 1 => S.mul (CR.numeral S.toCR (n + 1)) (S.add (W a n) (pw S a n))

structure ExpLaws (ex : α → α) : Prop where
  congr : ∀ {a b}, S.r a b → S.r (ex a) (ex b)
  mono : ∀ {a b}, S.le a b → S.le (ex a) (ex b)
  pos : ∀ a, S.pos (ex a)
  strict : ∀ {a b}, S.pos (S.add b (S.neg a)) → S.pos (S.add (ex b) (S.neg (ex a)))
  recip : ∀ d : D, S.r (S.mul (ex (dv S.toOH d)) (ex (S.neg (dv S.toOH d)))) S.one
  lo : ∀ (n : Nat) (d : D), S.le S.zero (dv S.toOH d) →
    S.le (W S (dv S.toOH d) n) (S.mul (CR.numeral S.toCR (fact n)) (ex (dv S.toOH d)))
  hi : ∀ (n : Nat) (d : D), S.le S.zero (dv S.toOH d) →
    S.le (S.add (dv S.toOH d) (dv S.toOH d)) (CR.numeral S.toCR (n + 1)) →
    S.le (S.mul (CR.numeral S.toCR (fact n)) (ex (dv S.toOH d)))
      (S.add (W S (dv S.toOH d) n) (S.mul (CR.numeral S.toCR 2) (pw S (dv S.toOH d) n)))

variable {S} {ex : α → α} (H : ExpLaws S ex)
include H

/-- REFLECTION: `eᵃ ≤ eᵇ` gives `a ≤ b`. -/
theorem ex_reflect {a b : α} (h : S.le (ex a) (ex b)) : S.le a b := by
  apply S.le_of_not_pos
  intro hp
  have q := H.strict hp
  exact S.pos_not_le q (by cr_linarith S.toOCR [h])

end ZExpLaw
