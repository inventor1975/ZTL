import ZLP

/-!
# ZSuperpose — the rule `znumsolve._superpose` reads a linear system by. Zero axioms.

2026-10-20 (the bridge girder; the curator's "Да и да"). A linear system whose matrix holds no uncertain quantity and
whose right-hand side is AFFINE in the uncertain ones — a truss under toleranced loads, a circuit with toleranced
sources, a balance with toleranced inflows: `A x = b0 + Σ p_k b_k`. The kernel solves ONE elimination with
`1 + #p` right-hand sides (`A x0 = b0`, `A x_k = b_k`) and reads every unknown as `x0 + Σ p_k x_k`; its range over
the box is read term by term, each term at the end its coefficient's sign picks. Proved here:

  `superpose`         if `A x0 = b0` and `A x_k = b_k` for every k, then `A (x0 + Σ p_k x_k) = b0 + Σ p_k b_k` —
                      for any linear map `A` (the laws as parameters: additive, homogeneous), any scalars `p_k`;
  `superpose_unique`  and, `A` one-to-one, that point is THE solution: any `x` with `A x = b0 + Σ p_k b_k` equals it;
  `affine_low_le`     the sign-picked lower end `c0 + Σ c_k·(c_k ≥ 0 ? lo_k : hi_k)` is below `c0 + Σ c_k p_k` for
                      every `p` in the box;
  `affine_high_ge`    the upper end likewise above;
  `affine_attained`   and both are VALUES: at the corner the signs pick, the affine form equals the end — the range
                      is exact, not an enclosure.

The order laws are `ZLP.OMul`'s (nothing borrowed; `ZLP` says why: core's `Int` lemmas carry `propext`). What stays a
premise, said: that the kernel's exact elimination over `Fraction` computed `x0`, `x_k` with `A x0 = b0`, `A x_k = b_k`
and found `A` invertible (a nonzero determinant) — exact rational arithmetic, run, not proved here.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace ZSuperpose

open ZLP

variable {α β : Type}

/-! ## Superposition: a linear map, the laws as parameters -/

/-- A vector space's operations and a linear map on it, given by the laws `superpose` uses. -/
structure Lin (α β : Type) where
  vzero : β
  vadd  : β → β → β
  smul  : α → β → β
  A     : β → β
  A_add  : ∀ u v, A (vadd u v) = vadd (A u) (A v)
  A_smul : ∀ c u, A (smul c u) = smul c (A u)

/-- `x0 + Σ p_k x_k` — the list holds the pairs `(p_k, x_k)`. -/
def comb (L : Lin α β) (x0 : β) : List (α × β) → β
  | [] => x0
  | (p, x) :: rest => L.vadd (comb L x0 rest) (L.smul p x)

/-- THE SUPERPOSITION. `A x0 = b0` and `A x_k = b_k` for every k (each pair of the list `(p_k, x_k, b_k)`): then
`A (x0 + Σ p_k x_k) = b0 + Σ p_k b_k`. -/
theorem superpose (L : Lin α β) (x0 b0 : β) (h0 : L.A x0 = b0) :
    ∀ (ts : List (α × β × β)), (∀ t, List.Mem t ts → L.A t.2.1 = t.2.2) →
      L.A (comb L x0 (ts.map (fun t => (t.1, t.2.1)))) = comb L b0 (ts.map (fun t => (t.1, t.2.2))) := by
  intro ts
  induction ts with
  | nil => intro _; exact h0
  | cons t rest ih =>
      intro h
      show L.A (L.vadd (comb L x0 (rest.map (fun t => (t.1, t.2.1)))) (L.smul t.1 t.2.1)) =
        L.vadd (comb L b0 (rest.map (fun t => (t.1, t.2.2)))) (L.smul t.1 t.2.2)
      rw [L.A_add, L.A_smul, ih (fun z hz => h z (List.Mem.tail t hz)), h t (List.Mem.head rest)]

/-- AND IT IS THE SOLUTION: `A` one-to-one, any `x` with `A x = b0 + Σ p_k b_k` is `x0 + Σ p_k x_k`. -/
theorem superpose_unique (L : Lin α β) (inj : ∀ u v, L.A u = L.A v → u = v) (x0 b0 x : β) (h0 : L.A x0 = b0)
    (ts : List (α × β × β)) (hts : ∀ t, List.Mem t ts → L.A t.2.1 = t.2.2)
    (hx : L.A x = comb L b0 (ts.map (fun t => (t.1, t.2.2)))) :
    x = comb L x0 (ts.map (fun t => (t.1, t.2.1))) := by
  apply inj
  rw [hx, superpose L x0 b0 h0 ts hts]

/-! ## The range of an affine form over a box, exact -/

/-- One term `c·p` with `p ∈ [lo, hi]` and the side its coefficient's sign picks (`pos`: `c ≥ 0`). -/
structure STerm (α : Type) where
  (c lo hi p : α)
  (pos : Bool)

/-- What the kernel checks of a term: `p` in the box, and the sign it read. -/
def STermOK (R : OMul α) (t : STerm α) : Prop :=
  R.le t.lo t.p ∧ R.le t.p t.hi ∧ (t.pos = true → R.le R.zero t.c) ∧ (t.pos = false → R.le t.c R.zero)

/-- The end each term contributes to the lower bound, and to the upper. -/
def lowEnd (t : STerm α) : α := if t.pos then t.lo else t.hi
def highEnd (t : STerm α) : α := if t.pos then t.hi else t.lo

def sumWith (R : OMul α) (e : STerm α → α) : List (STerm α) → α
  | [] => R.zero
  | t :: rest => R.add (R.mul t.c (e t)) (sumWith R e rest)

/-- `c·(lowEnd) ≤ c·p` for one term. -/
theorem term_low (R : OMul α) (t : STerm α) (h : STermOK R t) : R.le (R.mul t.c (lowEnd t)) (R.mul t.c t.p) := by
  unfold lowEnd
  cases hp : t.pos with
  | true =>
      rw [if_pos rfl]
      exact R.mul_le_mul_nonneg (h.2.2.1 hp) h.1
  | false =>
      rw [if_neg Bool.false_ne_true]
      exact R.mul_le_mul_nonpos (h.2.2.2 hp) h.2.1

/-- `c·p ≤ c·(highEnd)` for one term. -/
theorem term_high (R : OMul α) (t : STerm α) (h : STermOK R t) : R.le (R.mul t.c t.p) (R.mul t.c (highEnd t)) := by
  unfold highEnd
  cases hp : t.pos with
  | true =>
      rw [if_pos rfl]
      exact R.mul_le_mul_nonneg (h.2.2.1 hp) h.2.1
  | false =>
      rw [if_neg Bool.false_ne_true]
      exact R.mul_le_mul_nonpos (h.2.2.2 hp) h.1

/-- THE LOWER END IS BELOW: `c0 + Σ c·lowEnd ≤ c0 + Σ c·p` for every `p` in the box. -/
theorem affine_low_le (R : OMul α) (c0 : α) :
    ∀ (l : List (STerm α)), (∀ t, List.Mem t l → STermOK R t) →
      R.le (R.add c0 (sumWith R lowEnd l)) (R.add c0 (sumWith R (fun t => t.p) l)) := by
  intro l hl
  apply R.add_le_add_left
  induction l with
  | nil => exact R.le_refl _
  | cons t rest ih =>
      exact add_le_add R (term_low R t (hl t (List.Mem.head rest))) (ih (fun z hz => hl z (List.Mem.tail t hz)))

/-- THE UPPER END IS ABOVE: `c0 + Σ c·p ≤ c0 + Σ c·highEnd`. -/
theorem affine_high_ge (R : OMul α) (c0 : α) :
    ∀ (l : List (STerm α)), (∀ t, List.Mem t l → STermOK R t) →
      R.le (R.add c0 (sumWith R (fun t => t.p) l)) (R.add c0 (sumWith R highEnd l)) := by
  intro l hl
  apply R.add_le_add_left
  induction l with
  | nil => exact R.le_refl _
  | cons t rest ih =>
      exact add_le_add R (term_high R t (hl t (List.Mem.head rest))) (ih (fun z hz => hl z (List.Mem.tail t hz)))

/-- The corner the signs pick, as terms: each `p` moved to its lower (or upper) end. -/
def atLow (t : STerm α) : STerm α := { t with p := lowEnd t }
def atHigh (t : STerm α) : STerm α := { t with p := highEnd t }

theorem sum_atLow (R : OMul α) : ∀ (l : List (STerm α)),
    sumWith R (fun t => t.p) (l.map atLow) = sumWith R lowEnd l
  | [] => rfl
  | t :: rest => by
      show R.add (R.mul t.c (lowEnd t)) (sumWith R (fun t => t.p) (rest.map atLow)) =
        R.add (R.mul t.c (lowEnd t)) (sumWith R lowEnd rest)
      rw [sum_atLow R rest]

theorem sum_atHigh (R : OMul α) : ∀ (l : List (STerm α)),
    sumWith R (fun t => t.p) (l.map atHigh) = sumWith R highEnd l
  | [] => rfl
  | t :: rest => by
      show R.add (R.mul t.c (highEnd t)) (sumWith R (fun t => t.p) (rest.map atHigh)) =
        R.add (R.mul t.c (highEnd t)) (sumWith R highEnd rest)
      rw [sum_atHigh R rest]

/-- BOTH ENDS ARE VALUES: at the corner the signs pick, the form equals the end — the range is exact. -/
theorem affine_attained (R : OMul α) (c0 : α) (l : List (STerm α)) :
    R.add c0 (sumWith R (fun t => t.p) (l.map atLow)) = R.add c0 (sumWith R lowEnd l) ∧
    R.add c0 (sumWith R (fun t => t.p) (l.map atHigh)) = R.add c0 (sumWith R highEnd l) :=
  ⟨by rw [sum_atLow R l], by rw [sum_atHigh R l]⟩

/-- The picked corner is in the box: `lo ≤ lowEnd ≤ hi` and the same for `highEnd` (given `lo ≤ hi`). -/
theorem ends_in_box (R : OMul α) (t : STerm α) (h : R.le t.lo t.hi) :
    (R.le t.lo (lowEnd t) ∧ R.le (lowEnd t) t.hi) ∧ (R.le t.lo (highEnd t) ∧ R.le (highEnd t) t.hi) := by
  unfold lowEnd highEnd
  cases t.pos with
  | true =>
      rw [if_pos rfl, if_pos rfl]
      exact ⟨⟨R.le_refl _, h⟩, ⟨h, R.le_refl _⟩⟩
  | false =>
      rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      exact ⟨⟨h, R.le_refl _⟩, ⟨R.le_refl _, h⟩⟩

end ZSuperpose

#print axioms ZSuperpose.superpose
#print axioms ZSuperpose.superpose_unique
#print axioms ZSuperpose.term_low
#print axioms ZSuperpose.term_high
#print axioms ZSuperpose.affine_low_le
#print axioms ZSuperpose.affine_high_ge
#print axioms ZSuperpose.sum_atLow
#print axioms ZSuperpose.sum_atHigh
#print axioms ZSuperpose.affine_attained
#print axioms ZSuperpose.ends_in_box
