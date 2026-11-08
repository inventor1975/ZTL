import ZTrig13
import ZRealCF
/-!
# ZRSin — VR's operational `sin`, `cos`: `n ↦ S_n(xₙ)`, `C_n(xₙ)` (`ZTrig`'s partial sums at the argument's own
index), Cauchy by `ZTrig.CS_cauchy`. Zero axioms. Their laws (`ZSinIv.TrigLaws`) are proved in `ZRootSin`.
-/

namespace ZRSin
open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

theorem ab_of_close {x : QExpr} {C : Nat} (h : qclose x qzero (qofInt (pow2 C))) : ZTrig.Ab x (qnat (2 ^ C)) := by
  obtain ⟨h1, h2⟩ := h
  have e := ZLn.qnat_pow2 C
  unfold qsub at h1 h2
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- An operational real is eventually within some `2^B`. -/
theorem ab_real (x : RExpr) : ∃ K N, ∀ n, N ≤ n → ZTrig.Ab (x.seq n) (qnat K) := by
  obtain ⟨B, N, h⟩ := rbounded x
  exact ⟨2 ^ B, N, fun n hn => ab_of_close (h n hn)⟩

theorem cs_cauchy (x : RExpr) :
    ZRecip.Cauchy (fun n => ZTrig.Cn (x.seq n) n) ∧ ZRecip.Cauchy (fun n => ZTrig.Sn (x.seq n) n) := by
  obtain ⟨K, N, h⟩ := ab_real x
  exact ZTrig.CS_cauchy (qnat_nonneg K) x.cauchy h

/-- `sin x` on VR's continuum. -/
def rsin (x : RExpr) : RExpr := ⟨fun n => ZTrig.Sn (x.seq n) n, (cs_cauchy x).2⟩
/-- `cos x` on VR's continuum. -/
def rcos (x : RExpr) : RExpr := ⟨fun n => ZTrig.Cn (x.seq n) n, (cs_cauchy x).1⟩

end ZRSin

#print axioms ZRSin.ab_real
#print axioms ZRSin.rsin
#print axioms ZRSin.rcos
