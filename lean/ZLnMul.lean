import ZExpAdd5

/-!
# ZLnMul — ln(x·y) = ln x + ln y on VR's continuum (STAGE 6 of exp's addition law). Zero axioms.

From `ZExpAdd5.rexpR_add` (exp(u + v) = exp u · exp v on VR's reals), `ZRealExp.rexp_rln` (exp(ln y) = y) and the
reflection `ZExpLaw.ex_reflect` (exp a ≤ exp b ⇒ a ≤ b, for the lawful exponential `rExpLaws`): both sides have the
same exponential, so they are equal. This is the law `zlogexact` uses when it reads ln 6 as ln 2 + ln 3, and every
factorisation c + Σ r_p ln p rests on it (with `rln_pow`, the power case, by induction).
-/

namespace ZLnMul
open VR VR.Numbers ZRealCF ZRealExp ZExpAdd5 ZExp

/-- exp a = exp b ⇒ a = b. -/
theorem rexpR_inj {a b : RExpr} (h : rEq (rexpR a) (rexpR b)) : rEq a b :=
  rle_antisymm (ZExpLaw.ex_reflect rExpLaws (rle_of_rEq h)) (ZExpLaw.ex_reflect rExpLaws (rle_of_rEq (rEq_symm h)))

/-- **ln(x·y) = ln x + ln y**, x, y > 0. -/
theorem rln_mul (x y : RExpr) (hx : rlt rzero x) (hy : rlt rzero y) :
    rEq (rln (rmul x y) (rpos_mul hx hy)) (radd (rln x hx) (rln y hy)) := by
  apply rexpR_inj
  refine rEq_trans (rexp_rln (rmul x y) (rpos_mul hx hy)) ?_
  refine rEq_trans ?_ (rexpR_add (rln x hx) (rln y hy))
  exact rEq_symm (rmul_respects (rexp_rln x hx) (rexp_rln y hy))

/-- ln respects equality of its argument. -/
theorem rln_respects {a b : RExpr} (ha : rlt rzero a) (hb : rlt rzero b) (h : rEq a b) : rEq (rln a ha) (rln b hb) :=
  rexpR_inj (rEq_trans (rexp_rln a ha) (rEq_trans h (rEq_symm (rexp_rln b hb))))

/-- ln 1 = 0. -/
theorem rln_one (h : rlt rzero rone) : rEq (rln rone h) rzero := by
  apply rexpR_inj
  refine rEq_trans (rexp_rln rone h) ?_
  -- exp 0 = 1: the partial sums at 0 are 1 from the first term on
  intro k
  refine ⟨1, fun n hn => ?_⟩
  show qclose qone (ZExp.eseq qzero n) (qeps k)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n => rfl⟩
  rw [ZExp.eseq_pos (qle_refl qzero)]
  exact qclose_respects (qEq_refl _) (qEq_symm (ZExp.S_zero m)) (qEq_refl _) (qclose_refl _ _ (qeps_nonneg k))

end ZLnMul

#print axioms ZLnMul.rexpR_inj
#print axioms ZLnMul.rln_mul
#print axioms ZLnMul.rln_one
#print axioms ZLnMul.rln_respects
