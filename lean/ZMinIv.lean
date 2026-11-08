import ZSinIv
/-!
# ZMinIv — what `min` MEANS over any ordered field, and its interval reading. Zero axioms.

`MinLaws`: congruent, below both arguments, and the GREATEST such (`c ≤ a`, `c ≤ b` give `c ≤ min a b`). No case
split on which argument is smaller (that would decide `a ≤ b ∨ b ≤ a`, not available on VR's continuum); VR's `rmin`
(the termwise minimum) satisfies it (`ZRootMin.r_minLaws`). `max u v` is read as `−min(−u, −v)` by the translators.

The reading: `min` of the lower ends, `min` of the upper ends — sound from the laws alone.
-/

namespace ZMinIv

open VR.CSR ZNumBin ZField ZPoly ZIv ZAff ZDivIv ZSinIv

variable {α : Type} (S : CF α)

structure MinLaws (mn : α → α → α) : Prop where
  congr : ∀ {a a' b b'}, S.r a a' → S.r b b' → S.r (mn a b) (mn a' b')
  le_l : ∀ a b, S.le (mn a b) a
  le_r : ∀ a b, S.le (mn a b) b
  glb : ∀ {a b c}, S.le c a → S.le c b → S.le c (mn a b)

/-- **THE READING OF `min`**. -/
def ivMin (I J : Iv) : Iv := (dmin I.1 J.1, dmin I.2 J.2)

variable {S}

/-- **THE READING OF `min` IS SOUND.** -/
theorem mem_min {mn : α → α → α} (H : MinLaws S mn) {x y : α} {I J : Iv} (hx : Mem S x I) (hy : Mem S y J) :
    Mem S (mn x y) (ivMin I J) :=
  ⟨H.glb (S.le_trans (dmin_l S I.1 J.1) hx.1) (S.le_trans (dmin_r S I.1 J.1) hy.1),
   le_dmin (S.le_trans (H.le_l x y) hx.2) (S.le_trans (H.le_r x y) hy.2)⟩

end ZMinIv

#print axioms ZMinIv.ivMin
#print axioms ZMinIv.mem_min
