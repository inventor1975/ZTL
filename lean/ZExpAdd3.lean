import ZExpAdd2

/-!
# ZExpAdd3 — STAGE 3: exp(a + b) = exp a · exp b at non-negative pre-rationals, on VR's continuum. Zero axioms.

`ZExpAdd2` squeezes S(a, n)·S(b, n) between S(a+b, n) and S(a+b, 2n); the series S(a+b, ·) is Cauchy (`ZExp`), so the
two ends meet, and the product of the exponentials (`rmul`, pointwise) is the exponential of the sum.
-/

namespace ZExpAdd3
open VR VR.Numbers ZExp ZExpAdd ZExpAdd2

theorem S_sumTo (x : QExpr) : ∀ n, S x n = sumTo (tm x) n
  | 0 => rfl
  | n + 1 => by show qadd (S x n) (tm x n) = qadd (sumTo (tm x) n) (tm x n); rw [S_sumTo x n]

/-- The square is the product of the partial sums. -/
theorem square_is_product (a b : QExpr) (n : Nat) :
    qEq (sumTo (fun i => row (fun i j => qmul (tm a i) (tm b j)) i n) n) (qmul (S a n) (S b n)) := by
  have hrow : ∀ i, i < n → qEq (row (fun i j => qmul (tm a i) (tm b j)) i n) (qmul (S b n) (tm a i)) := by
    intro i _
    show qEq (sumTo (fun j => qmul (tm a i) (tm b j)) n) _
    refine qEq_trans (sumTo_smul (tm a i) (tm b) n) ?_
    rw [S_sumTo]; exact qmul_comm _ _
  refine qEq_trans (sumTo_respects _ _ n hrow) ?_
  refine qEq_trans (sumTo_smul (S b n) (tm a) n) ?_
  rw [S_sumTo a n]; exact qmul_comm _ _

/-- The triangle is the partial sum of the sum. -/
theorem triangle_is_S (a b : QExpr) (n : Nat) :
    qEq (sumTo (diag (fun i j => qmul (tm a i) (tm b j))) n) (S (qadd a b) n) := by
  rw [S_sumTo]
  exact sumTo_respects _ _ n (fun k _ => conv_tm a b k)

/-- **THE SQUEEZE**, a, b ≥ 0: S(a+b, n) ≤ S(a, n)·S(b, n) ≤ S(a+b, n + n). -/
theorem squeeze {a b : QExpr} (ha : qle qzero a) (hb : qle qzero b) (n : Nat) :
    qle (S (qadd a b) n) (qmul (S a n) (S b n)) ∧ qle (qmul (S a n) (S b n)) (S (qadd a b) (n + n)) := by
  have hf : ∀ i j, qle qzero (qmul (tm a i) (tm b j)) := fun i j => qmul_nonneg (tm_nonneg ha i) (tm_nonneg hb j)
  refine ⟨?_, ?_⟩
  · exact qle_respects (triangle_is_S a b n) (square_is_product a b n) (tri_le_sq _ hf n)
  · exact qle_respects (square_is_product a b n) (triangle_is_S a b (n + n)) (sq_le_tri _ hf n)

/-- Squeezed between two close ends ⇒ close to the lower end. -/
theorem close_of_squeeze {L P U e : QExpr} (h1 : qle L P) (h2 : qle P U) (hU : qclose U L e) (he : qle qzero e) :
    qclose P L e := by
  refine ⟨qle_trans (qle_add_right (qneg L) h2) hU.1, ?_⟩
  have h0 : qle qzero (qsub P L) :=
    qle_respects (qadd_neg L) (qEq_refl _) (qle_add_right (qneg L) h1)
  have hne : qle (qneg e) qzero := by
    have := qle_add_right (qneg e) he
    exact qle_respects (by q_ring) (qadd_neg e) this
  exact qle_trans hne h0

/-- **STAGE 3: exp(a + b) = exp a · exp b**, a, b ≥ 0 pre-rationals. -/
theorem rexp_add_nonneg {a b : QExpr} (ha : qle qzero a) (hb : qle qzero b) :
    rEq (rmul (rexp a) (rexp b)) (rexp (qadd a b)) := by
  have hab : qle qzero (qadd a b) := qle_respects (qadd_zero qzero) (qEq_refl _) (qadd_le_add ha hb)
  intro k
  obtain ⟨N, hN⟩ := (rexp (qadd a b)).cauchy k
  refine ⟨N, fun n hn => ?_⟩
  show qclose (qmul (eseq a n) (eseq b n)) (eseq (qadd a b) n) (qeps k)
  rw [eseq_pos ha, eseq_pos hb, eseq_pos hab]
  obtain ⟨h1, h2⟩ := squeeze ha hb n
  have hU : qclose (S (qadd a b) (n + n)) (S (qadd a b) n) (qeps k) := by
    have := hN (n + n) n (Nat.le_trans hn (Nat.le_add_right n n)) hn
    show qclose (S (qadd a b) (n + n)) (S (qadd a b) n) (qeps k)
    have e1 := eseq_pos hab (n + n)
    have e2 := eseq_pos hab n
    rw [← e1, ← e2]; exact this
  exact close_of_squeeze h1 h2 hU (qeps_nonneg k)

end ZExpAdd3

#print axioms ZExpAdd3.S_sumTo
#print axioms ZExpAdd3.square_is_product
#print axioms ZExpAdd3.triangle_is_S
#print axioms ZExpAdd3.squeeze
#print axioms ZExpAdd3.close_of_squeeze
#print axioms ZExpAdd3.rexp_add_nonneg
