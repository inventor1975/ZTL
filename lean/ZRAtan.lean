import ZAtan
import ZRealCF
/-!
# ZRAtan — VR's operational `atan`: `n ↦ atseq (xₙ) n` (the grid sums of `ZAtan`), Cauchy by `ZAtan.atan_cauchy`.
Zero axioms. Its laws (`ZXE.AtanLaws`) are proved in `ZRootAtan`.
-/

namespace ZRAtan
open VR.Numbers

/-- `atan x` on VR's continuum. -/
def ratan (x : RExpr) : RExpr := ⟨fun n => ZAtan.atseq (x.seq n) n, ZAtan.atan_cauchy x.cauchy⟩

end ZRAtan

#print axioms ZRAtan.ratan
