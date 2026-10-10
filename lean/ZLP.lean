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
below its value at every point of the box. Since 2026-10-10 it is PROVED for the kernel's reading
(`corner_below`, `affine_min_sound`; `lower_bound_sound_box` is the chain without it): what stays a premise is
that the expression equals its affine form with coefficients in the read intervals (`zlp.affine`). "No mix
exists" (Farkas) is `infeasible_sound`. The order laws are parameters (`ORing`), nothing borrowed, as in ZCertify — and for the
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

/-! ## The box-minimum, proved (2026-10-10): `min_sound` is no longer a premise

The kernel reads the minimum of an affine form `e0 + Σ c_i·x_i` over a box — each coefficient `c_i` in an
interval (from the data), each choice `x_i` in its range — as `e0_lo + Σ m_i`, where `m_i` is the least of the
four corner products of `c_i`'s and `x_i`'s ends (`zlp._mul_iv`). Proved here for any ordered ring given by its
laws: the corners bound every product (`corner_below`), so the reading bounds every value of the form
(`affine_min_sound`). What stays a premise is that the expression EQUALS its affine form with coefficients in
the read intervals — the kernel's affinity check (`zlp.affine`, derivatives by `zcertify.derivative`). -/

/-- The multiplication laws the corner argument uses, beside the ring's (no typeclass, nothing borrowed). -/
structure OMul (α : Type) extends ORing α where
  mul_comm : ∀ a b, mul a b = mul b a
  le_total : ∀ a b, le a b ∨ le b a
  mul_le_mul_nonneg : ∀ {c a b}, le zero c → le a b → le (mul c a) (mul c b)
  mul_le_mul_nonpos : ∀ {c a b}, le c zero → le a b → le (mul c b) (mul c a)
  add_le_add_right : ∀ {a b} (c : α), le a b → le (add a c) (add b c)

/-- THE CORNERS BOUND THE PRODUCT. `C` below all four corner products of `[a1, a2] × [x1, x2]`: then `C ≤ a·x`
for every `a` and `x` in their intervals. Constructive: `le_total` is a law, cases on it are on a given `Or`. -/
theorem corner_below (R : OMul α) {a1 a2 x1 x2 a x C : α}
    (ha1 : R.le a1 a) (ha2 : R.le a a2) (hx1 : R.le x1 x) (hx2 : R.le x x2)
    (c11 : R.le C (R.mul a1 x1)) (c12 : R.le C (R.mul a1 x2))
    (c21 : R.le C (R.mul a2 x1)) (c22 : R.le C (R.mul a2 x2)) :
    R.le C (R.mul a x) := by
  cases R.le_total R.zero x with
  | inl hx =>
      -- 0 ≤ x: a1·x ≤ a·x
      have h1 : R.le (R.mul a1 x) (R.mul a x) := by
        have := R.mul_le_mul_nonneg hx ha1
        rw [R.mul_comm x a1, R.mul_comm x a] at this
        exact this
      cases R.le_total R.zero a1 with
      | inl hp => exact R.le_trans c11 (R.le_trans (R.mul_le_mul_nonneg hp hx1) h1)
      | inr hn => exact R.le_trans c12 (R.le_trans (R.mul_le_mul_nonpos hn hx2) h1)
  | inr hx =>
      -- x ≤ 0: a2·x ≤ a·x
      have h2 : R.le (R.mul a2 x) (R.mul a x) := by
        have := R.mul_le_mul_nonpos hx ha2
        rw [R.mul_comm x a2, R.mul_comm x a] at this
        exact this
      cases R.le_total R.zero a2 with
      | inl hp => exact R.le_trans c21 (R.le_trans (R.mul_le_mul_nonneg hp hx1) h2)
      | inr hn => exact R.le_trans c22 (R.le_trans (R.mul_le_mul_nonpos hn hx2) h2)

/-- Sums keep the order: `a ≤ b`, `c ≤ d` give `a + c ≤ b + d`. -/
theorem add_le_add (R : OMul α) {a b c d : α} (h1 : R.le a b) (h2 : R.le c d) :
    R.le (R.add a c) (R.add b d) :=
  R.le_trans (R.add_le_add_right c h1) (R.add_le_add_left b h2)

/-- One term of the affine form: the coefficient `c` in `[c1, c2]`, the choice `x` in `[x1, x2]`, and the
kernel's `m` — below all four corners. -/
structure Term (α : Type) where
  (c1 c2 c x1 x2 x m : α)

/-- What the kernel checks of a term (the ends hold the value; `m` below every corner). -/
def TermOK (R : OMul α) (t : Term α) : Prop :=
  R.le t.c1 t.c ∧ R.le t.c t.c2 ∧ R.le t.x1 t.x ∧ R.le t.x t.x2 ∧
  R.le t.m (R.mul t.c1 t.x1) ∧ R.le t.m (R.mul t.c1 t.x2) ∧
  R.le t.m (R.mul t.c2 t.x1) ∧ R.le t.m (R.mul t.c2 t.x2)

/-- The kernel's reading `Σ m` and the value `Σ c·x`. -/
def sumM (R : OMul α) : List (Term α) → α
  | [] => R.zero
  | t :: rest => R.add t.m (sumM R rest)

def sumV (R : OMul α) : List (Term α) → α
  | [] => R.zero
  | t :: rest => R.add (R.mul t.c t.x) (sumV R rest)

/-- THE BOX-MINIMUM IS SOUND. Every term checked: the kernel's `e0_lo + Σ m` is at most `e0 + Σ c·x` — for every
value of the coefficients and every choice in the box. -/
theorem affine_min_sound (R : OMul α) (e0lo e0 : α) (h0 : R.le e0lo e0) :
    ∀ (l : List (Term α)), (∀ t, List.Mem t l → TermOK R t) →
      R.le (R.add e0lo (sumM R l)) (R.add e0 (sumV R l)) := by
  intro l hl
  apply add_le_add R h0
  induction l with
  | nil => exact R.le_refl _
  | cons t rest ih =>
      have ht := hl t (List.Mem.head rest)
      have hm : R.le t.m (R.mul t.c t.x) :=
        corner_below R ht.1 ht.2.1 ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2.1 ht.2.2.2.2.2.1 ht.2.2.2.2.2.2.1
          ht.2.2.2.2.2.2.2
      exact add_le_add R hm (ih (fun z hz => hl z (List.Mem.tail t hz)))

/-- WEAK DUALITY WITH THE BOX-MINIMUM PROVED. Feasible mix, multipliers `y ≥ 0`; the expression `cost − Σ y·h`
equal to its affine form `e0 + Σ c·x` (`affine`, the kernel's affinity check — the one premise left); every term
checked. Then the kernel's `L = e0_lo + Σ m` bounds the cost. -/
theorem lower_bound_sound_box (R : OMul α) (cost e0lo e0 : α) (l : List (α × α)) (ts : List (Term α))
    (feasible : ∀ yh, List.Mem yh l → R.le R.zero yh.1 ∧ R.le R.zero yh.2)
    (affine : R.add cost (R.neg (wsum R.toORing l)) = R.add e0 (sumV R ts))
    (h0 : R.le e0lo e0) (hts : ∀ t, List.Mem t ts → TermOK R t) :
    R.le (R.add e0lo (sumM R ts)) cost := by
  apply lower_bound_sound R.toORing cost _ l feasible
  rw [affine]
  exact affine_min_sound R e0lo e0 h0 ts hts

/-- NONVACUITY: the integers satisfy every law (built from core's `Int` lemmas, which carry `propext` — so this
instance is NOT among the zero-axiom theorems; it only shows the laws describe a real ordered ring). -/
def intOMul : OMul Int where
  zero := 0
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  le := (· ≤ ·)
  le_refl := Int.le_refl
  le_trans := Int.le_trans
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  add_neg := Int.add_right_neg
  add_le_add_left := fun c h => Int.add_le_add_left h c
  mul_nonneg := Int.mul_nonneg
  zero_add_zero := rfl
  mul_comm := Int.mul_comm
  le_total := Int.le_total
  mul_le_mul_nonneg := fun hc h => Int.mul_le_mul_of_nonneg_left h hc
  mul_le_mul_nonpos := fun hc h => Int.mul_le_mul_of_nonpos_left hc h
  add_le_add_right := fun c h => Int.add_le_add_right h c

/-- The corners at work on ℤ: `a ∈ [-2, 3]`, `x ∈ [-1, 4]`, corner minimum −8 ≤ a·x at a = −2, x = 4. -/
example : intOMul.le (-8) (intOMul.mul (-2) 4) :=
  corner_below intOMul (a1 := -2) (a2 := 3) (x1 := -1) (x2 := 4)
    (show (-2 : Int) ≤ -2 by decide) (show (-2 : Int) ≤ 3 by decide)
    (show (-1 : Int) ≤ 4 by decide) (show (4 : Int) ≤ 4 by decide)
    (show (-8 : Int) ≤ (-2) * (-1) by decide) (show (-8 : Int) ≤ (-2) * 4 by decide)
    (show (-8 : Int) ≤ 3 * (-1) by decide) (show (-8 : Int) ≤ 3 * 4 by decide)

end ZLP

#print axioms ZLP.wsum_nonneg
#print axioms ZLP.sub_le
#print axioms ZLP.lower_bound_sound
#print axioms ZLP.infeasible_sound
#print axioms ZLP.corner_below
#print axioms ZLP.add_le_add
#print axioms ZLP.affine_min_sound
#print axioms ZLP.lower_bound_sound_box
