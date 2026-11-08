import ZRootExp
import ZMinIv
/-!
# ZRootMin — VR's `rmin` (the termwise minimum) satisfies `ZMinIv.MinLaws`, and the oracle `qmin` converges
uniformly. Zero axioms.
-/

namespace ZRootMin
open VR VR.Numbers VR.CSR ZNumBin ZField ZIv ZXE ZRealCF ZExp ZRealExp ZRootExp ZMinIv

theorem qmin_congr {a a' b b' : QExpr} (ha : qEq a a') (hb : qEq b b') : qEq (qmin a b) (qmin a' b') := by
  rcases qmin_cases a b with ⟨e1, h1⟩ | ⟨e1, h1⟩ <;> rcases qmin_cases a' b' with ⟨e2, h2⟩ | ⟨e2, h2⟩ <;>
    rw [e1, e2] <;> exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem rmin_congr {a a' b b' : RExpr} (ha : rEq a a') (hb : rEq b b') : rEq (rmin a b) (rmin a' b') := fun k => by
  obtain ⟨N1, h1⟩ := ha k
  obtain ⟨N2, h2⟩ := hb k
  exact ⟨N1 + N2, fun n hn => qmin_close (h1 n (lA hn)) (h2 n (lB hn))⟩

theorem rmin_glb {a b c : RExpr} (ha : rle c a) (hb : rle c b) : rle c (rmin a b) := fun k => by
  obtain ⟨N1, h1⟩ := ha k
  obtain ⟨N2, h2⟩ := hb k
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have x := h1 n (lA hn)
  have y := h2 n (lB hn)
  change qle (qsub (c.seq n) (qmin (a.seq n) (b.seq n))) (qeps k)
  rcases qmin_cases (a.seq n) (b.seq n) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> assumption

/-- **VR's `min` IS LAWFUL.** -/
theorem r_minLaws : MinLaws rCF rmin where
  congr := fun ha hb => rmin_congr ha hb
  le_l := fun _ _ => rle_of_eventually 0 (fun _ _ => qmin_le_l _ _)
  le_r := fun _ _ => rle_of_eventually 0 (fun _ _ => qmin_le_r _ _)
  glb := fun ha hb => rmin_glb ha hb

/-- **THE ORACLE `qmin` CONVERGES UNIFORMLY** when both arguments do. -/
theorem uc_min {f g : Nat → (Nat → QExpr) → QExpr} (hf : UCo f) (hg : UCo g) :
    UCo (fun n q => qmin (f n q) (g n q)) := by
  intro R R0
  obtain ⟨C1, B1, b1, c1⟩ := hf R R0
  obtain ⟨C2, B2, b2, c2⟩ := hg R R0
  obtain ⟨C, hC⟩ := qexpr_bound (qadd (qofInt (pow2 C1)) (qofInt (pow2 C2)))
  refine ⟨C, B1 + B2, fun n q hn hq => ?_, fun k => ?_⟩
  · obtain ⟨x1, x2⟩ := b1 n q (lA hn) hq
    obtain ⟨y1, y2⟩ := b2 n q (lB hn) hq
    refine ZRootExp.close_up (B := qadd (qofInt (pow2 C1)) (qofInt (pow2 C2))) ?_ hC
    show qclose (qmin (f n q) (g n q)) qzero _
    unfold qsub at x1 x2 y1 y2
    rcases qmin_cases (f n q) (g n q) with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;>
      (constructor <;> (unfold qsub; rat_linarith))
  · obtain ⟨N1, hb1, h1⟩ := c1 k
    obtain ⟨N2, hb2, h2⟩ := c2 k
    refine ⟨N1 + N2 + (B1 + B2), lB (Nat.le_refl _), fun m n q hm hn hq => ?_⟩
    exact qmin_close (h1 m n q (lA (lA hm)) (lA (lA hn)) hq)
      (h2 m n q (lB (lA hm)) (lB (lA hn)) hq)

end ZRootMin

#print axioms ZRootMin.qmin_congr
#print axioms ZRootMin.rmin_congr
#print axioms ZRootMin.rmin_glb
#print axioms ZRootMin.r_minLaws
#print axioms ZRootMin.uc_min
