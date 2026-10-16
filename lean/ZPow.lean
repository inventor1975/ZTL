import ZSqrt

/-!
# ZPow — integer powers on VR's operational reals: value, exact slope, Cauchy. Zero axioms.

The kernel reads `pow(u, n)`, `n` a natural number, as the EXACT interval power (`zfunc.iv_pow`) and its derivative
as `n·u^(n−1)·u'` (`zcertify._graph_grad`, the exponent a constant). For a base read `≥ 0` both are algebra:

  * `Ev_powN` — `u ∈ [lo, hi]`, `0 ≤ lo ≤ hi`: `u^k ∈ [lo^k, hi^k]`;
  * `pow_diff` — `b^(k+1) − a^(k+1) = (b − a)·Σ_{i≤k} a^i b^(k−i)` exactly, and `Ev_gsum` — that sum lies in
    `[(k+1)·lo^k, (k+1)·hi^k]`: the slope with no intermediate point;
  * `powN_cauchy` — a power of an operational real is one.

NOT covered: a base whose reading straddles `0` (the slope's terms then change sign), negative and non-integer
exponents (`exp(c·ln u)` needs `exp`'s functional equation for its derivative reading).
-/

namespace ZPow

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-- `x^k`. -/
def qpowN (x : QExpr) : Nat → QExpr
  | 0 => qone
  | k + 1 => qmul (qpowN x k) x

/-- `Σ_{i≤k} a^i b^(k−i)`. -/
def gsum (a b : QExpr) : Nat → QExpr
  | 0 => qone
  | k + 1 => qadd (qmul b (gsum a b k)) (qpowN a (k + 1))

theorem pow_diff (a b : QExpr) : ∀ k, qEq (qsub (qpowN b (k + 1)) (qpowN a (k + 1))) (qmul (qsub b a) (gsum a b k))
  | 0 => by show qEq (qsub (qmul qone b) (qmul qone a)) (qmul (qsub b a) qone); unfold qsub; rat_ring
  | k + 1 => by
      have ih := pow_diff a b k
      show qEq (qsub (qmul (qpowN b (k + 1)) b) (qmul (qpowN a (k + 1)) a))
        (qmul (qsub b a) (qadd (qmul b (gsum a b k)) (qpowN a (k + 1))))
      have e := qmul_respects ih (qEq_refl b)
      generalize qpowN b (k + 1) = B at *; generalize qpowN a (k + 1) = A at *; generalize gsum a b k = S at *
      unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem powN_nonneg {x : QExpr} (hx : qle qzero x) : ∀ k, qle qzero (qpowN x k)
  | 0 => qle_of_qlt qone_pos
  | k + 1 => qmul_nonneg (powN_nonneg hx k) hx

theorem powN_mono {x y : QExpr} (hx : qle qzero x) (hxy : qle x y) : ∀ k, qle (qpowN x k) (qpowN y k)
  | 0 => qle_refl _
  | k + 1 => by
      have ih := powN_mono hx hxy k
      have a := ZExp.scale ih hx
      have b := scale_l hxy (powN_nonneg (qle_trans hx hxy) k)
      exact qle_trans a b

/-- The corners of two non-negative intervals: the product's least is `a1·b1`, its greatest `a2·b2`. -/
theorem corners_nonneg {a1 a2 b1 b2 : QExpr} (ha : qle qzero a1) (ha' : qle a1 a2) (hb : qle qzero b1) (hb' : qle b1 b2) :
    Corners (qmul a1 b1) (qmul a2 b2) a1 a2 b1 b2 := by
  have a0 : qle qzero a2 := qle_trans ha ha'
  have b0 : qle qzero b2 := qle_trans hb hb'
  have f1 := scale_l hb' ha
  have f2 := ZExp.scale ha' hb
  have f3 := ZExp.scale ha' b0
  have f4 := scale_l hb' a0
  exact ⟨⟨qle_refl _, f1, f2, qle_trans f2 f4⟩, ⟨qle_trans f1 f3, f3, f4, qle_refl _⟩⟩

/-- THE VALUE: `y ∈ [lo, hi]`, `0 ≤ lo ≤ hi` — `y^k ∈ [lo^k, hi^k]`. -/
theorem Ev_powN {y : Nat → QExpr} {lo hi : QExpr} (hy : Ev y lo hi) (h0 : qle qzero lo) (hlh : qle lo hi) :
    ∀ k, Ev (fun n => qpowN (y n) k) (qpowN lo k) (qpowN hi k)
  | 0 => Ev_of_exact 0 (fun _ _ => ⟨qle_refl _, qle_refl _⟩)
  | k + 1 => Ev_mul (Ev_powN hy h0 hlh k) hy
      (corners_nonneg (powN_nonneg h0 k) (powN_mono h0 hlh k) h0 hlh)

/-- THE SLOPE'S SUM: `a, b ∈ [lo, hi]`, `0 ≤ lo ≤ hi` — `Σ_{i≤k} a^i b^(k−i) ∈ [(k+1)·lo^k, (k+1)·hi^k]`. -/
theorem Ev_gsum {a b : Nat → QExpr} {lo hi : QExpr} (ha : Ev a lo hi) (hb : Ev b lo hi) (h0 : qle qzero lo)
    (hlh : qle lo hi) : ∀ k, Ev (fun n => gsum (a n) (b n) k) (qmul (qnat (k + 1)) (qpowN lo k)) (qmul (qnat (k + 1)) (qpowN hi k))
  | 0 => by
      have e1 := qnat_succ 0; have e2 := qnat_zero
      have e3 : qEq (qmul (qnat 1) qone) qone := by
        have := qmul_respects e1 (qEq_refl qone); have := qmul_one (qadd (qnat 0) qone)
        exact qle_antisymm (by rat_linarith) (by rat_linarith)
      exact Ev_of_exact 0 (fun _ _ => ⟨by show qle (qmul (qnat 1) qone) qone; rat_linarith,
                                       by show qle qone (qmul (qnat 1) qone); rat_linarith⟩)
  | k + 1 => by
      have ih := Ev_gsum ha hb h0 hlh k
      have n0 : qle qzero (qmul (qnat (k + 1)) (qpowN lo k)) := qmul_nonneg (qnat_nonneg _) (powN_nonneg h0 k)
      have nm : qle (qmul (qnat (k + 1)) (qpowN lo k)) (qmul (qnat (k + 1)) (qpowN hi k)) :=
        scale_l (powN_mono h0 hlh k) (qnat_nonneg _)
      have T := Ev_add (Ev_mul hb ih (corners_nonneg h0 hlh n0 nm)) (Ev_powN ha h0 hlh (k + 1))
      have s := qnat_succ (k + 1)
      have r1 : qEq (qmul (qnat (k + 1 + 1)) (qpowN lo (k + 1))) (qmul (qadd (qnat (k + 1)) qone) (qmul (qpowN lo k) lo)) :=
        qmul_respects s (qEq_refl _)
      have r2 : qEq (qmul (qnat (k + 1 + 1)) (qpowN hi (k + 1))) (qmul (qadd (qnat (k + 1)) qone) (qmul (qpowN hi k) hi)) :=
        qmul_respects s (qEq_refl _)
      refine Ev_widen (Ev_congr (fun n => qEq_refl _) T) ?_ ?_
      · show qle _ (qadd (qmul lo (qmul (qnat (k + 1)) (qpowN lo k))) (qmul (qpowN lo k) lo))
        generalize qpowN lo k = P at *; generalize qnat (k + 1) = c at *; generalize qnat (k + 1 + 1) = c' at *
        exact qle_of_qEq (qEq_trans r1 (by rat_ring))
      · show qle (qadd (qmul hi (qmul (qnat (k + 1)) (qpowN hi k))) (qmul (qpowN hi k) hi)) _
        generalize qpowN hi k = P at *; generalize qnat (k + 1) = c at *; generalize qnat (k + 1 + 1) = c' at *
        exact qle_of_qEq (qEq_symm (qEq_trans r2 (by rat_ring)))

/-- A power of an operational real is one. -/
theorem powN_cauchy {y : Nat → QExpr} (hc : ZRecip.Cauchy y) : ∀ k, ZRecip.Cauchy (fun n => qpowN (y n) k)
  | 0 => fun k => ⟨0, fun _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩
  | k + 1 => (rmul ⟨_, powN_cauchy hc k⟩ ⟨_, hc⟩).cauchy

end ZPow

#print axioms ZPow.pow_diff
#print axioms ZPow.powN_mono
#print axioms ZPow.corners_nonneg
#print axioms ZPow.Ev_powN
#print axioms ZPow.Ev_gsum
#print axioms ZPow.powN_cauchy
