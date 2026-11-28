import QZ19
import QZ16
import Sqrt3

/-!
# QZ19Q3 — the instance Q(√3) of QZ19: the rationals with a square root of three are an ordered field of the kernel,
with an inverse, a test for zero, min and max. Zero axioms. (2026-11-28, queue item F; written with AI, Logik2.)

The two premises of `QZ19.extOF` for d = 3 over the canonical rationals `QOF.QC`: 0 ≤ 3 (`nn3`, from the field's
laws) and no rational squares to three times a nonzero square (`Sqrt3.no_sqrt3`). One computed line: √3·√3 = 3.

Not here: the tower Q(√2)(√3) (it needs that 3 has no root in Q(√2), not proved).
-/

namespace QZ19Q3
open ZNet QOF QZ19

/-- three among the canonical rationals, as 1 + 1 + 1 -/
def three : QC := qOF.add (qOF.add qOF.one qOF.one) qOF.one

/-- three is not negative: 0 ≤ 1 + 1 and 0 ≤ 1 (the laws of an ordered field, QZ19) -/
instance nn3 : NonNeg qOF three := ⟨nn_add qOF (two_nonneg qOF) (zero_le_one qOF)⟩

/-- three has no root among the rationals (Sqrt3) -/
theorem nr3 : NoRoot qOF three := Sqrt3.no_sqrt3

/-- Q(√3) -/
def r3 : OF (Ed three) := extOF qOF QZ16.dleQ nr3
def r3Inv : QZ12.Inv r3 := extInv qOF QZ16.dleQ QZ13.qInv nr3
def r3mm : QZ8.MinMax r3 := extMinMax qOF QZ16.dleQ nr3

/-- √3 -/
def root3 : Ed three := ⟨qOF.zero, qOF.one⟩
/-- 3, as a number of Q(√3) -/
def three3 : Ed three := ⟨three, qOF.zero⟩

/-- √3 · √3 = 3, computed by the kernel -/
theorem sq3 : r3.mul root3 root3 = three3 := by
  show Ed.mk _ _ = Ed.mk _ _
  exact ext2 (by decide +kernel) (by decide +kernel)

end QZ19Q3

#print axioms QZ19Q3.nn3
#print axioms QZ19Q3.nr3
#print axioms QZ19Q3.r3
#print axioms QZ19Q3.r3Inv
#print axioms QZ19Q3.r3mm
#print axioms QZ19Q3.sq3
