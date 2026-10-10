/-!
# ZLP — the rule `zlp.py` proves a lower bound on a linear optimum by. Zero axioms.

Weak duality (blind test 3, 2026-10-10: a feed formula, a concrete mix — "no cheaper mix exists" must be
checkable, not taken from an LP solver). For a mix `x` that meets every requirement — each written `h_i(x) ≥ 0`
for EVERY value of the uncertain data — and ANY multipliers `y_i ≥ 0`:

    cost(x) ≥ cost(x) − Σ y_i · h_i(x) ≥ L

where `L` is the kernel's reading of the minimum of the right side over the box of `x` (and of the data).
`lower_bound_sound` proves the chain: the sum of non-negative products is non-negative, subtracting it never
raises the cost, so the kernel's `L` bounds the cost of every feasible mix — whatever the multipliers (a bad
`y` gives a weak bound, never a false one).

PREMISE, said rather than hidden: `min_sound` — that the kernel's box-minimum of the affine right side lies
below its value at every point of the box (interval arithmetic on the affine form; the kernel computes it
with exact fractions). The order laws are parameters (`ORing`), nothing borrowed, as in ZCertify — and for the
same reason: an `ORing Int` built from core's lemmas carries `propext` (probed 2026-10-10: `Int.add_comm`,
`Int.le_trans` …), so the theorems stay axiom-free by taking the laws as given, not by importing them.
-/

namespace ZLP

/-- An ordered commutative ring, given by the laws this proof uses (no typeclass). -/
structure ORing (α : Type) where
  zero : α
  add  : α → α → α
  neg  : α → α
  mul  : α → α → α
  le   : α → α → Prop
  le_refl  : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_zero : ∀ a, add a zero = a
  add_neg  : ∀ a, add a (neg a) = zero
  add_le_add_left : ∀ {a b} (c : α), le a b → le (add c a) (add c b)
  mul_nonneg : ∀ {a b}, le zero a → le zero b → le zero (mul a b)
  zero_add_zero : add zero zero = zero

variable {α : Type}

/-- Σ y_i · h_i over the constraints (multiplier, remainder). -/
def wsum (R : ORing α) : List (α × α) → α
  | [] => R.zero
  | (y, h) :: rest => R.add (R.mul y h) (wsum R rest)

/-- Non-negative multipliers on non-negative remainders: the sum is non-negative. -/
theorem wsum_nonneg (R : ORing α) :
    ∀ (l : List (α × α)), (∀ yh, List.Mem yh l → R.le R.zero yh.1 ∧ R.le R.zero yh.2) →
      R.le R.zero (wsum R l) := by
  intro l
  induction l with
  | nil => intro _; exact R.le_refl _
  | cons yh rest ih =>
      intro h
      have h0 := h yh (List.Mem.head rest)
      have hp : R.le R.zero (R.mul yh.1 yh.2) := R.mul_nonneg h0.1 h0.2
      have hr : R.le R.zero (wsum R rest) := ih (fun z hz => h z (List.Mem.tail yh hz))
      -- 0 = 0 + 0 ≤ p + 0 ≤ p + r
      have s1 : R.le (R.add R.zero R.zero) (R.add (R.mul yh.1 yh.2) R.zero) := by
        rw [R.add_comm R.zero R.zero, R.add_comm (R.mul yh.1 yh.2) R.zero]
        exact R.add_le_add_left R.zero hp
      have s2 : R.le (R.add (R.mul yh.1 yh.2) R.zero) (R.add (R.mul yh.1 yh.2) (wsum R rest)) :=
        R.add_le_add_left _ hr
      rw [R.zero_add_zero] at s1
      exact R.le_trans s1 s2

/-- Subtracting a non-negative amount never raises a value: c − s ≤ c. -/
theorem sub_le (R : ORing α) (c s : α) (hs : R.le R.zero s) : R.le (R.add c (R.neg s)) c := by
  -- (c − s) + 0 ≤ (c − s) + s = c + (−s + s) = c + (s + −s) = c + 0 = c
  have h := R.add_le_add_left (R.add c (R.neg s)) hs
  rw [R.add_zero, R.add_assoc, R.add_comm (R.neg s) s, R.add_neg, R.add_zero] at h
  exact h

/-- THE LOWER BOUND IS SOUND. A mix meeting every requirement (each remainder non-negative), any non-negative
multipliers, and the kernel's box-minimum `L` of `cost − Σ y·h` (`min_sound`, the premise): `L ≤ cost`. -/
theorem lower_bound_sound (R : ORing α) (cost L : α) (l : List (α × α))
    (feasible : ∀ yh, List.Mem yh l → R.le R.zero yh.1 ∧ R.le R.zero yh.2)
    (min_sound : R.le L (R.add cost (R.neg (wsum R l)))) :
    R.le L cost :=
  R.le_trans min_sound (sub_le R cost (wsum R l) (wsum_nonneg R l feasible))

/-- NO MIX EXISTS (Farkas, 2026-10-10). Multipliers `y ≥ 0`, and the kernel's box-MAXIMUM `M` of `Σ y·h`
(`max_sound`, the premise, at the mix in question) strictly below zero: then that mix does not meet every
requirement — a feasible one would make the sum non-negative. Constructive: the conclusion is a negation. -/
theorem infeasible_sound (R : ORing α) (M : α) (l : List (α × α))
    (max_sound : R.le (wsum R l) M) (neg : ¬ R.le R.zero M) :
    ¬ (∀ yh, List.Mem yh l → R.le R.zero yh.1 ∧ R.le R.zero yh.2) :=
  fun feasible => neg (R.le_trans (wsum_nonneg R l feasible) max_sound)

end ZLP

#print axioms ZLP.wsum_nonneg
#print axioms ZLP.sub_le
#print axioms ZLP.lower_bound_sound
#print axioms ZLP.infeasible_sound
