import ZExp

/-!
# ZExpAdd — exp's addition law on VR's continuum, from the partial sums. Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема»: `zlogexact` reads ln 6 = ln 2 + ln 3, i.e.
ln(xy) = ln x + ln y, i.e. exp(a + b) = exp a · exp b — which `ZExpLaw` lists as NOT proved for VR's `rexpR`
("the hardest"). This file builds it from the partial sums `S x n = Σ_{k<n} x^k/k!` (`ZExp`).

STAGE 1 (here): THE CAUCHY PRODUCT OF THE TERMS. `conv a b k = Σ_{i+j=k} t_i(a)·t_j(b)` equals `t_k(a + b)` — the
binomial theorem divided by k!, proved without binomial coefficients: `(k+1)·conv(k+1) = (a+b)·conv k`, which is
`t_{k+1}`'s own recursion, and `k + 1 ≠ 0` cancels. The diagonal sum `diag` is written with no subtraction (Nat's
`-` lemmas carry `propext`): `diag f (k+1) = f 0 (k+1) + diag (f shifted in i) k`, and `diag_right` proves the other
split, `diag (f shifted in j) k + f (k+1) 0`.
-/

namespace ZExpAdd
open VR VR.Numbers ZExp

/-- Σ_{i+j=k} f i j, by the first index. -/
def diag (f : Nat → Nat → QExpr) : Nat → QExpr
  | 0 => f 0 0
  | k + 1 => qadd (f 0 (k + 1)) (diag (fun i j => f (i + 1) j) k)

theorem diag_congr : ∀ (k : Nat) (f g : Nat → Nat → QExpr), (∀ i j, qEq (f i j) (g i j)) → qEq (diag f k) (diag g k)
  | 0, f, g, h => h 0 0
  | k + 1, f, g, h => qadd_respects (h 0 (k + 1)) (diag_congr k _ _ (fun i j => h (i + 1) j))

theorem diag_add : ∀ (k : Nat) (f g : Nat → Nat → QExpr),
    qEq (diag (fun i j => qadd (f i j) (g i j)) k) (qadd (diag f k) (diag g k))
  | 0, f, g => qEq_refl _
  | k + 1, f, g => by
      have ih := diag_add k (fun i j => f (i + 1) j) (fun i j => g (i + 1) j)
      show qEq (qadd (qadd (f 0 (k + 1)) (g 0 (k + 1))) (diag (fun i j => qadd (f (i + 1) j) (g (i + 1) j)) k))
        (qadd (qadd (f 0 (k + 1)) (diag (fun i j => f (i + 1) j) k)) (qadd (g 0 (k + 1)) (diag (fun i j => g (i + 1) j) k)))
      refine qEq_trans (qadd_respects (qEq_refl _) ih) ?_
      q_ring

theorem diag_smul : ∀ (k : Nat) (c : QExpr) (f : Nat → Nat → QExpr),
    qEq (diag (fun i j => qmul c (f i j)) k) (qmul c (diag f k))
  | 0, c, f => qEq_refl _
  | k + 1, c, f => by
      have ih := diag_smul k c (fun i j => f (i + 1) j)
      show qEq (qadd (qmul c (f 0 (k + 1))) (diag (fun i j => qmul c (f (i + 1) j)) k))
        (qmul c (qadd (f 0 (k + 1)) (diag (fun i j => f (i + 1) j) k)))
      refine qEq_trans (qadd_respects (qEq_refl _) ih) ?_
      q_ring

/-- The other split: by the last index. -/
theorem diag_right : ∀ (k : Nat) (f : Nat → Nat → QExpr),
    qEq (diag f (k + 1)) (qadd (diag (fun i j => f i (j + 1)) k) (f (k + 1) 0))
  | 0, f => by
      show qEq (qadd (f 0 1) (f 1 0)) (qadd (f 0 1) (f 1 0))
      exact qEq_refl _
  | k + 1, f => by
      have ih := diag_right k (fun i j => f (i + 1) j)
      show qEq (qadd (f 0 (k + 2)) (diag (fun i j => f (i + 1) j) (k + 1)))
        (qadd (qadd (f 0 (k + 1 + 1)) (diag (fun i j => f (i + 1) (j + 1)) k)) (f (k + 2) 0))
      refine qEq_trans (qadd_respects (qEq_refl _) ih) ?_
      q_ring

/-- The weights: Σ_{i+j=k} (i + j)·f i j = k · Σ f. -/
theorem diag_weight : ∀ (k : Nat) (f : Nat → Nat → QExpr),
    qEq (diag (fun i j => qmul (qnat (i + j)) (f i j)) k) (qmul (qnat k) (diag f k))
  | 0, f => by
      show qEq (qmul (qnat (0 + 0)) (f 0 0)) (qmul (qnat 0) (f 0 0))
      exact qEq_refl _
  | k + 1, f => by
      -- shift: weight (i+1)+j = (i+j) + 1
      have hshift : ∀ i j, qEq (qmul (qnat (i + 1 + j)) (f (i + 1) j))
          (qadd (qmul (qnat (i + j)) (f (i + 1) j)) (f (i + 1) j)) := by
        intro i j
        have e : i + 1 + j = (i + j) + 1 := by rw [Nat.add_right_comm]
        rw [e]
        refine qEq_trans (qmul_respects (qnat_succ (i + j)) (qEq_refl _)) ?_
        q_ring
      have h1 := diag_congr k _ _ hshift
      have h2 := diag_add k (fun i j => qmul (qnat (i + j)) (f (i + 1) j)) (fun i j => f (i + 1) j)
      have ih := diag_weight k (fun i j => f (i + 1) j)
      show qEq (qadd (qmul (qnat (0 + (k + 1))) (f 0 (k + 1))) (diag (fun i j => qmul (qnat (i + 1 + j)) (f (i + 1) j)) k))
        (qmul (qnat (k + 1)) (qadd (f 0 (k + 1)) (diag (fun i j => f (i + 1) j) k)))
      rw [Nat.zero_add]
      refine qEq_trans (qadd_respects (qmul_respects (qnat_succ k) (qEq_refl _))
        (qEq_trans h1 (qEq_trans h2 (qadd_respects ih (qEq_refl _))))) ?_
      refine qEq_trans ?_ (qmul_respects (qEq_symm (qnat_succ k)) (qEq_refl _))
      q_ring

/-- THE CAUCHY PRODUCT of the terms. -/
def conv (a b : QExpr) (k : Nat) : QExpr := diag (fun i j => qmul (tm a i) (tm b j)) k

/-- `(k+1)·conv(k+1) = (a + b)·conv k`. -/
theorem conv_step (a b : QExpr) (k : Nat) :
    qEq (qmul (qnat (k + 1)) (conv a b (k + 1))) (qmul (qadd a b) (conv a b k)) := by
  unfold conv
  -- weights split as i + j
  have hw := diag_weight (k + 1) (fun i j => qmul (tm a i) (tm b j))
  have hsplit : ∀ i j, qEq (qmul (qnat (i + j)) (qmul (tm a i) (tm b j)))
      (qadd (qmul (qmul (qnat i) (tm a i)) (tm b j)) (qmul (tm a i) (qmul (qnat j) (tm b j)))) := by
    intro i j
    refine qEq_trans (qmul_respects (qnat_add i j) (qEq_refl _)) ?_
    q_ring
  have hs := diag_add (k + 1) (fun i j => qmul (qmul (qnat i) (tm a i)) (tm b j))
    (fun i j => qmul (tm a i) (qmul (qnat j) (tm b j)))
  -- the i-part: the first term has weight 0; the rest is a·conv k
  have hA : qEq (diag (fun i j => qmul (qmul (qnat i) (tm a i)) (tm b j)) (k + 1)) (qmul a (diag (fun i j => qmul (tm a i) (tm b j)) k)) := by
    show qEq (qadd (qmul (qmul (qnat 0) (tm a 0)) (tm b (k + 1)))
      (diag (fun i j => qmul (qmul (qnat (i + 1)) (tm a (i + 1))) (tm b j)) k)) (qmul a (diag (fun i j => qmul (tm a i) (tm b j)) k))
    have h0 : qEq (qmul (qmul (qnat 0) (tm a 0)) (tm b (k + 1))) qzero := by
      refine qEq_trans (qmul_respects (qmul_respects qnat_zero (qEq_refl _)) (qEq_refl _)) ?_
      q_ring
    have hr : ∀ i j, qEq (qmul (qmul (qnat (i + 1)) (tm a (i + 1))) (tm b j)) (qmul a (qmul (tm a i) (tm b j))) := by
      intro i j
      refine qEq_trans (qmul_respects (tm_succ a i) (qEq_refl _)) ?_
      q_ring
    refine qEq_trans (qadd_respects h0 (qEq_trans (diag_congr k _ _ hr) (diag_smul k a _))) ?_
    q_ring
  -- the j-part: the last term has weight 0; the rest is b·conv k
  have hB : qEq (diag (fun i j => qmul (tm a i) (qmul (qnat j) (tm b j))) (k + 1)) (qmul b (diag (fun i j => qmul (tm a i) (tm b j)) k)) := by
    refine qEq_trans (diag_right k _) ?_
    have h0 : qEq (qmul (tm a (k + 1)) (qmul (qnat 0) (tm b 0))) qzero := by
      refine qEq_trans (qmul_respects (qEq_refl _) (qmul_respects qnat_zero (qEq_refl _))) ?_
      q_ring
    have hr : ∀ i j, qEq (qmul (tm a i) (qmul (qnat (j + 1)) (tm b (j + 1)))) (qmul b (qmul (tm a i) (tm b j))) := by
      intro i j
      refine qEq_trans (qmul_respects (qEq_refl _) (tm_succ b j)) ?_
      q_ring
    refine qEq_trans (qadd_respects (qEq_trans (diag_congr k _ _ hr) (diag_smul k b _)) h0) ?_
    q_ring
  refine qEq_trans (qEq_symm hw) ?_
  refine qEq_trans (diag_congr (k + 1) _ _ hsplit) ?_
  refine qEq_trans hs ?_
  refine qEq_trans (qadd_respects hA hB) ?_
  q_ring

/-- Cancel a nonzero factor. -/
theorem cancel {c x y : QExpr} (hc : ¬ qEq c qzero) (h : qEq (qmul c x) (qmul c y)) : qEq x y := by
  have hi := qmul_inv'_cancel hc
  have e1 : qEq x (qmul (qmul (qinv' c) c) x) := by
    refine qEq_trans ?_ (qmul_respects (qEq_trans (qmul_comm _ _) hi |> qEq_symm) (qEq_refl x))
    q_ring
  have e2 : qEq (qmul (qmul (qinv' c) c) y) y := by
    refine qEq_trans (qmul_respects (qEq_trans (qmul_comm _ _) hi) (qEq_refl y)) ?_
    q_ring
  refine qEq_trans e1 (qEq_trans ?_ e2)
  refine qEq_trans (qmul_assoc _ _ _) (qEq_trans (qmul_respects (qEq_refl _) h) (qEq_symm (qmul_assoc _ _ _)))

/-- **STAGE 1: conv a b k = t_k(a + b)** — the binomial theorem over k!, for every pre-rational a, b. -/
theorem conv_tm (a b : QExpr) : ∀ k, qEq (conv a b k) (tm (qadd a b) k)
  | 0 => by
      show qEq (qmul (tm a 0) (tm b 0)) (tm (qadd a b) 0)
      show qEq (qmul qone qone) qone
      q_ring
  | k + 1 => by
      have ih := conv_tm a b k
      apply cancel (qnat_ne_zero k)
      refine qEq_trans (conv_step a b k) ?_
      refine qEq_trans (qmul_respects (qEq_refl _) ih) ?_
      refine qEq_trans ?_ (qEq_symm (tm_succ (qadd a b) k))
      exact qmul_comm _ _

end ZExpAdd

#print axioms ZExpAdd.diag_congr
#print axioms ZExpAdd.diag_add
#print axioms ZExpAdd.diag_smul
#print axioms ZExpAdd.diag_right
#print axioms ZExpAdd.diag_weight
#print axioms ZExpAdd.conv_step
#print axioms ZExpAdd.cancel
#print axioms ZExpAdd.conv_tm
