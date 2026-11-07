import ZAff
/-!
# ZDivIv — the reciprocal interval, computed then checked. Zero axioms.

`1/x` on `[l, h]` with `l > 0`: `q₁ ≈ 1/h`, `q₂ ≈ 1/l` by `Nat` division, then CHECKED `0 ≤ q₁`, `q₁·h ≤ 1`,
`0 ≤ q₂`, `q₂·l ≥ 1` (a negative interval through the sign). `mem_inv`: with `x·t = 1`, `t` is in the result —
proved through `le_of_not_pos` (`q₁ > t` would make `(q₁ − t)·x > 0`, against `q₁·x ≤ q₁·h ≤ 1`).
Split out of `ZXE` so that `ZExpIv` can use it.
-/

namespace ZDivIv
open VR.CSR ZNumBin ZField ZIv ZAff

variable {α : Type} (S : CF α)

/-! ## The reciprocal interval -/

def posX (d : D) : Bool := Nat.blt d.m.n d.m.p
def negX (d : D) : Bool := Nat.blt d.m.p d.m.n

theorem pos_of_posX {d : D} (h : posX d = true) : S.pos (dv S.toOH d) := by
  have l := nI_le_of_ble S.toOH (a := d.m.n + 1) (b := d.m.p) h
  have a := nI_add S.toOH d.m.n 1
  have one : S.r (nI S.toOH 1) S.one := by show S.r (S.add S.one S.zero) S.one; cr_ring S.toCR
  have l' := S.le_respects (S.trans a (S.add_congr (S.refl _) one)) (S.refl _) l
  have pz : S.pos (zv S.toOH d.m) := S.pos_mono (pos_one S) (by unfold zv; cr_linarith S.toOCR [l'])
  have ph : ∀ e, S.pos (hp S.toOH e) := by
    intro e; induction e with
    | zero => exact pos_one S
    | succ e ih => exact S.pos_mul S.pos_half ih
  exact S.pos_mul pz (ph d.e)

/-- `2^(e+K)/m · ½^K` rounded down (`up = false`) or up — for a dyadic with positive normalised numerator. -/
def recipD (d : D) (K : Nat) (up : Bool) : D :=
  let m := (znorm d.m).p
  cond up ⟨⟨(2 ^ (d.e + K) + m - 1) / m, 0⟩, K⟩ ⟨⟨2 ^ (d.e + K) / m, 0⟩, K⟩

/-- `1/x` on `[l, h]`, `l > 0`: `[q₁, q₂]` with `0 ≤ q₁`, `q₁·h ≤ 1`, `0 ≤ q₂`, `q₂·l ≥ 1` CHECKED. -/
def ivInvPos (I : Iv) : Option Iv :=
  let q1 := recipD I.2 64 false
  let q2 := recipD I.1 64 true
  cond (posX I.1 && dle zeroD q1 && dle (dmul q1 I.2) oneD && dle zeroD q2 && dle oneD (dmul q2 I.1))
    (some (q1, q2)) none

def ivInv (I : Iv) : Option Iv :=
  cond (posX I.1) (ivInvPos I)
    (cond (negX I.2) ((ivInvPos (dneg I.2, dneg I.1)).map (fun J => (dneg J.2, dneg J.1))) none)

theorem mem_congr {x y : α} {K : Iv} (e : S.r x y) (h : Mem S y K) : Mem S x K :=
  ⟨S.le_respects (S.refl _) (S.symm e) h.1, S.le_respects (S.symm e) (S.refl _) h.2⟩

theorem and5 {a b c d e : Bool} (H : (a && b && c && d && e) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true := by
  have s1 := and_true_split H
  have s2 := and_true_split s1.1
  have s3 := and_true_split s2.1
  have s4 := and_true_split s3.1
  exact ⟨s4.1, s4.2, s3.2, s2.2, s1.2⟩

theorem mem_inv_pos {x t : α} {I J : Iv} (hx : Mem S x I) (h : ivInvPos I = some J) (ht : S.r (S.mul x t) S.one) :
    Mem S t J := by
  unfold ivInvPos at h
  obtain ⟨hb, hJ⟩ := cond_some h
  cases hJ
  obtain ⟨c1, c2, c3, c4, c5⟩ := and5 hb
  have pl := pos_of_posX S c1
  have px := S.pos_mono pl hx.1
  have z1 := S.le_respects (dv_zeroD S) (S.refl _) (dle_sound S.toOH c2)
  have z2 := S.le_respects (dv_zeroD S) (S.refl _) (dle_sound S.toOH c4)
  have b1 := S.le_respects (dv_mul S.toOH _ _) (dv_oneD S) (dle_sound S.toOH c3)
  have b2 := S.le_respects (dv_oneD S) (dv_mul S.toOH _ _) (dle_sound S.toOH c5)
  have t1 := S.le_respects (S.refl _) ht (S.le_refl (S.mul x t))
  have t2 := S.le_respects ht (S.refl _) (S.le_refl (S.mul x t))
  constructor
  · apply S.le_of_not_pos
    intro H
    have pp := S.pos_mul H px
    have m1 := le_mul_left' S hx.2 z1
    exact S.pos_not_le pp (by cr_linarith S.toOCR [m1, b1, t1, t2])
  · apply S.le_of_not_pos
    intro H
    have pp := S.pos_mul H px
    have m2 := le_mul_left' S hx.1 z2
    exact S.pos_not_le pp (by cr_linarith S.toOCR [m2, b2, t1, t2])

theorem mem_inv {x t : α} {I J : Iv} (hx : Mem S x I) (h : ivInv I = some J) (ht : S.r (S.mul x t) S.one) :
    Mem S t J := by
  unfold ivInv at h
  cases hp : posX I.1 with
  | true => rw [hp] at h; exact mem_inv_pos S hx h ht
  | false =>
      rw [hp] at h
      cases hn : negX I.2 with
      | false => rw [hn] at h; cases h
      | true =>
          rw [hn] at h
          cases hJ' : ivInvPos (dneg I.2, dneg I.1) with
          | none => rw [hJ'] at h; cases h
          | some J' =>
              rw [hJ'] at h
              cases h
              have hx' : Mem S (S.neg x) (dneg I.2, dneg I.1) :=
                ⟨S.le_respects (S.symm (dv_neg S.toOH I.2)) (S.refl _) (by cr_linarith S.toOCR [hx.2]),
                 S.le_respects (S.refl _) (S.symm (dv_neg S.toOH I.1)) (by cr_linarith S.toOCR [hx.1])⟩
              have ht' : S.r (S.mul (S.neg x) (S.neg t)) S.one := S.trans (by cr_ring S.toCR) ht
              have m := mem_inv_pos S hx' hJ' ht'
              exact ⟨S.le_respects (S.symm (dv_neg S.toOH J'.2)) (S.refl _) (by cr_linarith S.toOCR [m.2]),
                S.le_respects (S.refl _) (S.symm (dv_neg S.toOH J'.1)) (by cr_linarith S.toOCR [m.1])⟩

/-- The quotient's value: with `vb·v = va` and `vb·t = 1`, `v = va·t`. -/
theorem quot_val {va vb v t : α} (hb : ap S vb) (hv : S.r (S.mul vb v) va) (ht : S.r (S.mul vb t) S.one) :
    S.r v (S.mul va t) := by
  have e1 : S.r v (S.mul (S.mul vb t) v) := S.symm (S.trans (S.mul_congr ht (S.refl _)) (S.one_mul _))
  have e2 : S.r (S.mul (S.mul vb t) v) (S.mul (S.mul vb v) t) := by cr_ring S.toCR
  exact S.trans e1 (S.trans e2 (S.mul_congr hv (S.refl _)))


end ZDivIv
