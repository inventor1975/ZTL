import ZExpAdd3
import ZRealExp

/-!
# ZExpAdd4 — STAGE 4: exp(a + b) = exp a · exp b at EVERY pre-rational, by signs. Zero axioms.

Stage 3 has the law for a, b ≥ 0. The other signs follow from it and the reciprocal law at the partial sums
(`ZRealExp.eseq_recip`: E_m(x)·E_m(−x) = 1, m ≥ 1), by three ring arguments on VR's reals:
  a, b < 0:          exp(−a)·exp(−b) = exp(−(a+b)), and every exp has its reciprocal;
  a ≥ 0 > b, a+b ≥ 0: exp(a+b)·exp(−b) = exp a;
  a ≥ 0 > b, a+b < 0: exp a·exp(−(a+b)) = exp(−b);
  a < 0 ≤ b:         the previous two with a, b exchanged.
-/

namespace ZExpAdd4
open VR VR.Numbers VR.CSR ZExp ZExpAdd2 ZExpAdd3

abbrev R := RExpr.cr

theorem rexp_respects {x y : QExpr} (h : qEq x y) : rEq (rexp x) (rexp y) :=
  rEq_of_seq (fun n => ZRealExp.eseq_respects h n)

theorem rexp_recip (x : QExpr) : rEq (rmul (rexp x) (rexp (qneg x))) rone := by
  intro k
  refine ⟨1, fun n hn => ?_⟩
  show qclose (qmul (eseq x n) (eseq (qneg x) n)) qone (qeps k)
  exact qclose_respects (qEq_symm (ZRealExp.eseq_recip x n hn)) (qEq_refl _) (qEq_refl _)
    (qclose_refl _ _ (qeps_nonneg k))

/-- u·u' = 1, v·v' = 1, w·w' = 1, u'·v' = w'  ⇒  u·v = w. -/
theorem law_L1 {u u' v v' w w' : RExpr} (hu : rEq (rmul u u') rone) (hv : rEq (rmul v v') rone)
    (hw : rEq (rmul w w') rone) (h : rEq (rmul u' v') w') : rEq (rmul u v) w := by
  have e1 : R.r (rmul u v) (rmul (rmul u v) (rmul w w')) :=
    R.trans (R.symm (CSR.mul_one R.toCSR _)) (R.mul_congr (R.refl _) (R.symm hw))
  have e2 : R.r (rmul (rmul u v) (rmul w w')) (rmul w (rmul (rmul u v) w')) := by cr_ring R
  have e3 : R.r (rmul w (rmul (rmul u v) w')) (rmul w (rmul (rmul u v) (rmul u' v'))) :=
    R.mul_congr (R.refl _) (R.mul_congr (R.refl _) (R.symm h))
  have e4 : R.r (rmul w (rmul (rmul u v) (rmul u' v'))) (rmul w (rmul (rmul u u') (rmul v v'))) := by cr_ring R
  have e5 : R.r (rmul w (rmul (rmul u u') (rmul v v'))) (rmul w (rmul rone rone)) :=
    R.mul_congr (R.refl _) (R.mul_congr hu hv)
  have e6 : R.r (rmul w (rmul rone rone)) w := by cr_ring R
  exact R.trans e1 (R.trans e2 (R.trans e3 (R.trans e4 (R.trans e5 e6))))

/-- w·v' = u, v·v' = 1  ⇒  u·v = w. -/
theorem law_L2 {u v v' w : RExpr} (hv : rEq (rmul v v') rone) (h : rEq (rmul w v') u) : rEq (rmul u v) w := by
  have e1 : R.r (rmul u v) (rmul (rmul w v') v) := R.mul_congr (R.symm h) (R.refl _)
  have e2 : R.r (rmul (rmul w v') v) (rmul w (rmul v v')) := by cr_ring R
  have e3 : R.r (rmul w (rmul v v')) (rmul w rone) := R.mul_congr (R.refl _) hv
  exact R.trans e1 (R.trans e2 (R.trans e3 (CSR.mul_one R.toCSR w)))

/-- u·w' = v', v·v' = 1, w·w' = 1  ⇒  u·v = w. -/
theorem law_L3 {u v v' w w' : RExpr} (hv : rEq (rmul v v') rone) (hw : rEq (rmul w w') rone)
    (h : rEq (rmul u w') v') : rEq (rmul u v) w := by
  have e1 : R.r (rmul u v) (rmul (rmul u v) (rmul w w')) :=
    R.trans (R.symm (CSR.mul_one R.toCSR _)) (R.mul_congr (R.refl _) (R.symm hw))
  have e2 : R.r (rmul (rmul u v) (rmul w w')) (rmul w (rmul (rmul u w') v)) := by cr_ring R
  have e3 : R.r (rmul w (rmul (rmul u w') v)) (rmul w (rmul v' v)) :=
    R.mul_congr (R.refl _) (R.mul_congr h (R.refl _))
  have e4 : R.r (rmul w (rmul v' v)) (rmul w (rmul v v')) := by cr_ring R
  have e5 : R.r (rmul w (rmul v v')) (rmul w rone) := R.mul_congr (R.refl _) hv
  exact R.trans e1 (R.trans e2 (R.trans e3 (R.trans e4 (R.trans e5 (CSR.mul_one R.toCSR w)))))

theorem neg_nonneg_of_not_le {x : QExpr} (h : ¬ qle qzero x) : qle qzero (qneg x) := neg_nonneg_of_not h

/-- One positive, one negative (a ≥ 0 > b). -/
theorem mixed {a b : QExpr} (ha : qle qzero a) (hb : ¬ qle qzero b) : rEq (rmul (rexp a) (rexp b)) (rexp (qadd a b)) := by
  have hnb := neg_nonneg_of_not hb
  cases qle_total qzero (qadd a b) with
  | inl hs =>
      -- exp(a+b)·exp(−b) = exp a
      have h := rEq_trans (rexp_add_nonneg hs hnb) (rexp_respects (by q_ring : qEq (qadd (qadd a b) (qneg b)) a))
      exact law_L2 (rexp_recip b) h
  | inr hs =>
      have hns : qle qzero (qneg (qadd a b)) := by
        have := qle_add_right (qneg (qadd a b)) hs
        exact qle_respects (qadd_neg _) (by q_ring) this
      -- exp a·exp(−(a+b)) = exp(−b)
      have h := rEq_trans (rexp_add_nonneg ha hns) (rexp_respects (by q_ring : qEq (qadd a (qneg (qadd a b))) (qneg b)))
      exact law_L3 (rexp_recip b) (rexp_recip (qadd a b)) h

/-- **STAGE 4: exp(a + b) = exp a · exp b for all pre-rationals a, b.** -/
theorem rexp_add (a b : QExpr) : rEq (rmul (rexp a) (rexp b)) (rexp (qadd a b)) := by
  cases qle.decidable qzero a with
  | isTrue ha =>
      cases qle.decidable qzero b with
      | isTrue hb => exact rexp_add_nonneg ha hb
      | isFalse hb => exact mixed ha hb
  | isFalse ha =>
      cases qle.decidable qzero b with
      | isTrue hb =>
          exact rEq_trans (rmul_comm _ _) (rEq_trans (mixed hb ha) (rexp_respects (qadd_comm b a)))
      | isFalse hb =>
          have hna := neg_nonneg_of_not ha
          have hnb := neg_nonneg_of_not hb
          have h := rEq_trans (rexp_add_nonneg hna hnb)
            (rexp_respects (by q_ring : qEq (qadd (qneg a) (qneg b)) (qneg (qadd a b))))
          exact law_L1 (rexp_recip a) (rexp_recip b) (rexp_recip (qadd a b)) h

end ZExpAdd4

#print axioms ZExpAdd4.rexp_respects
#print axioms ZExpAdd4.rexp_recip
#print axioms ZExpAdd4.law_L1
#print axioms ZExpAdd4.law_L2
#print axioms ZExpAdd4.law_L3
#print axioms ZExpAdd4.mixed
#print axioms ZExpAdd4.rexp_add
