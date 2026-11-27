import ZExpAdd

/-!
# ZExpAdd2 — STAGE 2 of exp's addition law: the product of partial sums is squeezed. Zero axioms.

For a, b ≥ 0 (pre-rationals):    S(a+b, n)  ≤  S(a, n)·S(b, n)  ≤  S(a+b, 2n).
Read as index sets: the triangle i + j < n lies inside the square i, j < n, which lies inside the triangle i + j < 2n;
every term t_i(a)·t_j(b) is ≥ 0. Written WITHOUT sets: the triangle is Σ_{i<n} R_i(n − i), the square Σ_{i<n} R_i(n),
the rows R_i(m) = Σ_{j<m} f i j are monotone in m, and n − i ≤ n ≤ 2n − i for i < n — termwise inequalities only.
`diag_eq_sum` links the triangle to `ZExpAdd.diag` (the Cauchy product), so the left end is S(a+b, n) by
`ZExpAdd.conv_tm`.
-/

namespace ZExpAdd2
open VR VR.Numbers ZExp ZExpAdd

/-! ## Finite sums -/

def sumTo (g : Nat → QExpr) : Nat → QExpr
  | 0 => qzero
  | m + 1 => qadd (sumTo g m) (g m)

theorem qadd_le_add {a b c d : QExpr} (h1 : qle a b) (h2 : qle c d) : qle (qadd a c) (qadd b d) :=
  qle_trans (qle_add_right c h1)
    (qle_respects (qadd_comm _ _) (qadd_comm _ _) (qle_add_right b h2))

theorem sumTo_le (g h : Nat → QExpr) : ∀ m, (∀ i, i < m → qle (g i) (h i)) → qle (sumTo g m) (sumTo h m)
  | 0, _ => qle_refl _
  | m + 1, hh => qadd_le_add (sumTo_le g h m (fun i hi => hh i (Nat.lt_succ_of_lt hi))) (hh m (Nat.lt_succ_self m))

theorem sumTo_nonneg (g : Nat → QExpr) : ∀ m, (∀ i, i < m → qle qzero (g i)) → qle qzero (sumTo g m)
  | 0, _ => qle_refl _
  | m + 1, hh =>
      qle_respects (qadd_zero _) (qEq_refl _)
        (qadd_le_add (sumTo_nonneg g m (fun i hi => hh i (Nat.lt_succ_of_lt hi))) (hh m (Nat.lt_succ_self m)))

theorem sumTo_respects (g h : Nat → QExpr) : ∀ m, (∀ i, i < m → qEq (g i) (h i)) → qEq (sumTo g m) (sumTo h m)
  | 0, _ => qEq_refl _
  | m + 1, hh => qadd_respects (sumTo_respects g h m (fun i hi => hh i (Nat.lt_succ_of_lt hi))) (hh m (Nat.lt_succ_self m))

/-- Longer is larger, for non-negative terms. -/
theorem sumTo_extend (g : Nat → QExpr) (hg : ∀ i, qle qzero (g i)) (m : Nat) : ∀ d, qle (sumTo g m) (sumTo g (m + d))
  | 0 => qle_refl _
  | d + 1 => qle_trans (sumTo_extend g hg m d)
      (qle_respects (qadd_zero _) (qEq_refl _) (qadd_le_add (qle_refl _) (hg (m + d))))

theorem sumTo_mono_len (g : Nat → QExpr) (hg : ∀ i, qle qzero (g i)) {m m' : Nat} (h : m ≤ m') :
    qle (sumTo g m) (sumTo g m') := by
  obtain ⟨d, rfl⟩ := le_ex h
  exact sumTo_extend g hg m d

/-- The first term split off. -/
theorem sumTo_first (g : Nat → QExpr) : ∀ m, qEq (sumTo g (m + 1)) (qadd (g 0) (sumTo (fun i => g (i + 1)) m))
  | 0 => by show qEq (qadd qzero (g 0)) (qadd (g 0) qzero); q_ring
  | m + 1 => by
      have ih := sumTo_first g m
      show qEq (qadd (sumTo g (m + 1)) (g (m + 1))) (qadd (g 0) (qadd (sumTo (fun i => g (i + 1)) m) (g (m + 1))))
      refine qEq_trans (qadd_respects ih (qEq_refl _)) ?_
      q_ring

theorem sumTo_add (g h : Nat → QExpr) : ∀ m, qEq (sumTo (fun i => qadd (g i) (h i)) m) (qadd (sumTo g m) (sumTo h m))
  | 0 => by show qEq qzero (qadd qzero qzero); q_ring
  | m + 1 => by
      have ih := sumTo_add g h m
      show qEq (qadd (sumTo (fun i => qadd (g i) (h i)) m) (qadd (g m) (h m)))
        (qadd (qadd (sumTo g m) (g m)) (qadd (sumTo h m) (h m)))
      refine qEq_trans (qadd_respects ih (qEq_refl _)) ?_
      q_ring

theorem sumTo_smul (c : QExpr) (g : Nat → QExpr) : ∀ m, qEq (sumTo (fun i => qmul c (g i)) m) (qmul c (sumTo g m))
  | 0 => by show qEq qzero (qmul c qzero); q_ring
  | m + 1 => by
      have ih := sumTo_smul c g m
      show qEq (qadd (sumTo (fun i => qmul c (g i)) m) (qmul c (g m))) (qmul c (qadd (sumTo g m) (g m)))
      refine qEq_trans (qadd_respects ih (qEq_refl _)) ?_
      q_ring

/-! ## Nat subtraction, the few facts needed (core's carry `propext`) -/

theorem succ_sub_of_le : ∀ (i n : Nat), i ≤ n → n + 1 - i = (n - i) + 1
  | 0, n, _ => by rw [Nat.sub_zero, Nat.sub_zero]
  | i + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | i + 1, n + 1, h => by
      rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
      exact succ_sub_of_le i n (Nat.le_of_succ_le_succ h)

/-- n ≤ (n + n) − i for i ≤ n. -/
theorem le_double_sub : ∀ (i n : Nat), i ≤ n → n ≤ (n + n) - i
  | 0, n, _ => by rw [Nat.sub_zero]; exact Nat.le_add_right n n
  | i + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | i + 1, n + 1, h => by
      have e : (n + 1 + (n + 1)) - (i + 1) = (n + 1 + n) - i := by
        rw [Nat.add_succ, Nat.succ_sub_succ]
      rw [e]
      have ih := le_double_sub i n (Nat.le_of_succ_le_succ h)
      -- (n+1+n) − i = (n + n − i) + 1  (i ≤ n + n)
      have e2 : n + 1 + n - i = (n + n - i) + 1 := by
        rw [Nat.add_right_comm]
        exact succ_sub_of_le i (n + n) (Nat.le_trans (Nat.le_of_succ_le_succ h) (Nat.le_add_right n n))
      rw [e2]; exact Nat.succ_le_succ ih

/-! ## The triangle as rows -/

/-- `diag f n = Σ_{i ≤ n} f i (n − i)`. -/
theorem diag_eq_sum : ∀ (n : Nat) (f : Nat → Nat → QExpr), qEq (diag f n) (sumTo (fun i => f i (n - i)) (n + 1))
  | 0, f => by show qEq (f 0 0) (qadd qzero (f 0 (0 - 0))); q_ring
  | n + 1, f => by
      have ih := diag_eq_sum n (fun i j => f (i + 1) j)
      refine qEq_trans ?_ (qEq_symm (sumTo_first _ (n + 1)))
      show qEq (qadd (f 0 (n + 1)) (diag (fun i j => f (i + 1) j) n))
        (qadd (f 0 (n + 1 - 0)) (sumTo (fun i => f (i + 1) (n + 1 - (i + 1))) (n + 1)))
      rw [Nat.sub_zero]
      refine qadd_respects (qEq_refl _) (qEq_trans ih ?_)
      apply sumTo_respects
      intro i _
      rw [Nat.succ_sub_succ]
      exact qEq_refl _

/-- The row sums. -/
def row (f : Nat → Nat → QExpr) (i m : Nat) : QExpr := sumTo (f i) m

/-- THE TRIANGLE, by rows: Σ_{k<n} diag f k = Σ_{i<n} row i (n − i). -/
theorem tri_rows (f : Nat → Nat → QExpr) : ∀ n, qEq (sumTo (diag f) n) (sumTo (fun i => row f i (n - i)) n)
  | 0 => qEq_refl _
  | n + 1 => by
      have ih := tri_rows f n
      -- right side at n+1: rows i < n gain one term f i (n − i); row n is f n 0
      have hrow : ∀ i, i < n + 1 → qEq (row f i (n + 1 - i)) (qadd (row f i (n - i)) (f i (n - i))) := by
        intro i hi
        rw [succ_sub_of_le i n (Nat.le_of_lt_succ hi)]
        exact qEq_refl _
      have h1 := sumTo_respects _ _ (n + 1) hrow
      have h2 := sumTo_add (fun i => row f i (n - i)) (fun i => f i (n - i)) (n + 1)
      have hlast : qEq (sumTo (fun i => row f i (n - i)) (n + 1)) (sumTo (fun i => row f i (n - i)) n) := by
        show qEq (qadd (sumTo (fun i => row f i (n - i)) n) (row f n (n - n))) (sumTo (fun i => row f i (n - i)) n)
        rw [Nat.sub_self]
        show qEq (qadd (sumTo (fun i => row f i (n - i)) n) qzero) _
        exact qadd_zero _
      show qEq (qadd (sumTo (diag f) n) (diag f n)) (sumTo (fun i => row f i (n + 1 - i)) (n + 1))
      refine qEq_trans ?_ (qEq_symm (qEq_trans h1 h2))
      exact qadd_respects (qEq_trans ih (qEq_symm hlast)) (diag_eq_sum n f)

/-! ## The squeeze, for non-negative terms -/

theorem row_mono (f : Nat → Nat → QExpr) (hf : ∀ i j, qle qzero (f i j)) {i m m' : Nat} (h : m ≤ m') : qle (row f i m) (row f i m') :=
  sumTo_mono_len (f i) (hf i) h

/-- triangle(n) ≤ square(n). -/
theorem tri_le_sq (f : Nat → Nat → QExpr) (hf : ∀ i j, qle qzero (f i j)) (n : Nat) : qle (sumTo (diag f) n) (sumTo (fun i => row f i n) n) :=
  qle_respects (qEq_symm (tri_rows f n)) (qEq_refl _)
    (sumTo_le _ _ n (fun i _ => row_mono f hf (Nat.sub_le n i)))

/-- square(n) ≤ triangle(2n). -/
theorem sq_le_tri (f : Nat → Nat → QExpr) (hf : ∀ i j, qle qzero (f i j)) (n : Nat) : qle (sumTo (fun i => row f i n) n) (sumTo (diag f) (n + n)) := by
  refine qle_respects (qEq_refl _) (qEq_symm (tri_rows f (n + n))) ?_
  have h1 : qle (sumTo (fun i => row f i n) n) (sumTo (fun i => row f i (n + n - i)) n) :=
    sumTo_le _ _ n (fun i hi => row_mono f hf (le_double_sub i n (Nat.le_of_lt hi)))
  exact qle_trans h1 (sumTo_mono_len _ (fun i => sumTo_nonneg _ _ (fun j _ => hf i j)) (Nat.le_add_right n n))

end ZExpAdd2

#print axioms ZExpAdd2.qadd_le_add
#print axioms ZExpAdd2.sumTo_le
#print axioms ZExpAdd2.sumTo_nonneg
#print axioms ZExpAdd2.sumTo_respects
#print axioms ZExpAdd2.sumTo_extend
#print axioms ZExpAdd2.sumTo_mono_len
#print axioms ZExpAdd2.sumTo_first
#print axioms ZExpAdd2.sumTo_add
#print axioms ZExpAdd2.sumTo_smul
#print axioms ZExpAdd2.succ_sub_of_le
#print axioms ZExpAdd2.le_double_sub
#print axioms ZExpAdd2.diag_eq_sum
#print axioms ZExpAdd2.tri_rows
#print axioms ZExpAdd2.row_mono
#print axioms ZExpAdd2.tri_le_sq
#print axioms ZExpAdd2.sq_le_tri
