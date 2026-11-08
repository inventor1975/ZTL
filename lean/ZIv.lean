import ZField
import ZPoly
/-!
# ZIv — the interval reading of a polynomial expression over a box, computed by the kernel. Zero axioms.

Module 4a of the Lean-checked `check_none` (curator, 2026-11-07: "Б"). A box gives each variable a dyadic
interval (a function `Nat → Option`, no list lemmas); `ivE` reads `+ − × ^` with outward rounding
(`ZNumBin.rdn`/`rup`); a product's bounds are the four corner products, rounded, and CHECKED against each corner
by `dle` (computed, then checked: a failed check returns `none`, never a wrong interval).

`ivE_sound`: the value at any point of the box lies in the reading — in every constructive ordered field `CF`.
The corner bound `mul_lower` needs signs that `≤` does not decide; it is proved inside a proof of `False`
(`ZField.sign_case`), where a case split on any proposition is constructive.

Not in this version (curator, 2026-11-07, "не забудь"): the affine reading, and functions beyond `+ − ×`.
-/

namespace ZIv
open VR.CSR ZNumBin ZField ZPoly

abbrev Iv := D × D
/-- A box: an interval per variable, or none. -/
abbrev Box := Nat → Option Iv

variable {α : Type} (S : CF α)

/-! ## Corner bounds of a product, constructively -/

theorem le_mul_left' {a b c : α} (hab : S.le a b) (hc : S.le S.zero c) : S.le (S.mul c a) (S.mul c b) := by
  have h := le_mul_right S.toOH hab hc
  exact S.le_respects (S.mul_comm _ _) (S.mul_comm _ _) h

theorem le_mul_nonpos {a b c : α} (hab : S.le a b) (hc : S.le c S.zero) : S.le (S.mul b c) (S.mul a c) := by
  have h1 := OCR.sub_nonneg_of_le S.toOCR hab
  have h2 : S.le S.zero (S.neg c) := by cr_linarith S.toOCR [hc]
  have h3 := S.mul_nonneg h1 h2
  cr_linarith S.toOCR [h3]

/-- `m` below the four corner products bounds `x·y` below, for `x ∈ [a, b]`, `y ∈ [c, d]`. -/
theorem mul_lower {x y a b c d m : α} (ha : S.le a x) (hb : S.le x b) (hc : S.le c y) (hd : S.le y d)
    (h1 : S.le m (S.mul a c)) (h2 : S.le m (S.mul a d)) (h3 : S.le m (S.mul b c)) (h4 : S.le m (S.mul b d)) :
    S.le m (S.mul x y) := by
  apply S.le_of_not_pos
  intro H
  have fin : S.le m (S.mul x y) → False := fun hm =>
    S.pos_not_le H (by cr_linarith S.toOCR [hm])
  refine sign_case S y (fun y0 => ?_) (fun y0 => ?_)
  · -- y ≥ 0: x·y ≥ a·y
    have e1 := le_mul_right S.toOH ha y0
    refine sign_case S a (fun a0 => ?_) (fun a0 => ?_)
    · exact fin (S.le_trans h1 (S.le_trans (le_mul_left' S hc a0) e1))
    · exact fin (S.le_trans h2 (S.le_trans (S.le_respects (S.mul_comm _ _) (S.mul_comm _ _) (le_mul_nonpos S hd a0)) e1))
  · -- y ≤ 0: x·y ≥ b·y
    have e1 := le_mul_nonpos S hb y0
    refine sign_case S b (fun b0 => ?_) (fun b0 => ?_)
    · exact fin (S.le_trans h3 (S.le_trans (le_mul_left' S hc b0) e1))
    · exact fin (S.le_trans h4 (S.le_trans (S.le_respects (S.mul_comm _ _) (S.mul_comm _ _) (le_mul_nonpos S hd b0)) e1))

/-- `M` above the four corner products bounds `x·y` above. -/
theorem mul_upper {x y a b c d M : α} (ha : S.le a x) (hb : S.le x b) (hc : S.le c y) (hd : S.le y d)
    (h1 : S.le (S.mul a c) M) (h2 : S.le (S.mul a d) M) (h3 : S.le (S.mul b c) M) (h4 : S.le (S.mul b d) M) :
    S.le (S.mul x y) M := by
  -- the lower bound for −x ∈ [−b, −a]
  have l := mul_lower S (x := S.neg x) (a := S.neg b) (b := S.neg a)
    (by cr_linarith S.toOCR [hb]) (by cr_linarith S.toOCR [ha]) hc hd
    (m := S.neg M) (by cr_linarith S.toOCR [h3]) (by cr_linarith S.toOCR [h4])
    (by cr_linarith S.toOCR [h1]) (by cr_linarith S.toOCR [h2])
  cr_linarith S.toOCR [l]

/-! ## The reading -/

def dmin (a b : D) : D := cond (dle a b) a b
def dmax (a b : D) : D := cond (dle a b) b a

/-- An interval `[lo, hi]` around four corners, CHECKED against each corner. -/
def hullW (p1 p2 p3 p4 lo hi : D) : Option Iv :=
  cond (dle lo p1 && dle lo p2 && dle lo p3 && dle lo p4 && dle p1 hi && dle p2 hi && dle p3 hi && dle p4 hi)
    (some (lo, hi)) none

/-- The hull of four corners, rounded outward. No check is needed: `dmin`/`dmax` are below/above each corner by
`dle_swap` (MEASURED 2026-11-08: the eight checks of `hullW` were 22% of a product in the kernel). -/
def hull4 (p1 p2 p3 p4 : D) : Option Iv :=
  some (rdn (dmin (dmin p1 p2) (dmin p3 p4)), rup (dmax (dmax p1 p2) (dmax p3 p4)))

/-- The product of two intervals: the hull of the four corner products. -/
def ivMul (I J : Iv) : Option Iv := hull4 (dmul I.1 J.1) (dmul I.1 J.2) (dmul I.2 J.1) (dmul I.2 J.2)

def ivAdd (I J : Iv) : Option Iv := some (rdn (dadd I.1 J.1), rup (dadd I.2 J.2))
def ivSub (I J : Iv) : Option Iv := some (rdn (dadd I.1 (dneg J.2)), rup (dadd I.2 (dneg J.1)))

def lift2 (f : Iv → Iv → Option Iv) : Option Iv → Option Iv → Option Iv
  | none, _ => none
  | some _, none => none
  | some a, some b => f a b

def one : Iv := (⟨⟨1, 0⟩, 0⟩, ⟨⟨1, 0⟩, 0⟩)

def ivPow (I : Iv) : Nat → Option Iv
  | 0 => some one
  | n + 1 => lift2 ivMul (some I) (ivPow I n)

/-- The kernel's interval reading of an expression over a box. -/
def ivE (B : Box) : PE → Option Iv
  | .var i => B i
  | .cst c => some (c, c)
  | .add p q => lift2 ivAdd (ivE B p) (ivE B q)
  | .sub p q => lift2 ivSub (ivE B p) (ivE B q)
  | .mul p q => lift2 ivMul (ivE B p) (ivE B q)
  | .pow p n => match ivE B p with
      | none => none
      | some I => ivPow I n

/-! ## Soundness -/

/-- A point in a box. -/
def InBox (B : Box) (p : Nat → α) : Prop :=
  ∀ i I, B i = some I → S.le (dv S.toOH I.1) (p i) ∧ S.le (p i) (dv S.toOH I.2)

/-- `x ∈ I`. -/
def Mem (x : α) (I : Iv) : Prop := S.le (dv S.toOH I.1) x ∧ S.le x (dv S.toOH I.2)

theorem and4 {a b c d e f g h : Bool} (H : (a && b && c && d && e && f && g && h) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true ∧ g = true ∧ h = true := by
  have s1 := and_true_split H
  have s2 := and_true_split s1.1
  have s3 := and_true_split s2.1
  have s4 := and_true_split s3.1
  have s5 := and_true_split s4.1
  have s6 := and_true_split s5.1
  have s7 := and_true_split s6.1
  exact ⟨s7.1, s7.2, s6.2, s5.2, s4.2, s3.2, s2.2, s1.2⟩

theorem none_ne_some {x : Iv} (h : (none : Option Iv) = some x) : False := by cases h

theorem lift2_some {f : Iv → Iv → Option Iv} {a b : Option Iv} {I : Iv} (h : lift2 f a b = some I) :
    ∃ x y, a = some x ∧ b = some y ∧ f x y = some I := by
  cases a with
  | none => exact (none_ne_some h).elim
  | some x =>
      cases b with
      | none => exact (none_ne_some h).elim
      | some y => exact ⟨x, y, rfl, rfl, h⟩

theorem cond_some {b : Bool} {x K : Iv} (h : cond b (some x) none = some K) : b = true ∧ x = K := by
  cases b with
  | false => exact (none_ne_some h).elim
  | true => exact ⟨rfl, Option.some.inj h⟩

theorem hullW_sound {p1 p2 p3 p4 lo hi : D} {K : Iv} (h : hullW p1 p2 p3 p4 lo hi = some K) :
    (dle K.1 p1 = true ∧ dle K.1 p2 = true ∧ dle K.1 p3 = true ∧ dle K.1 p4 = true) ∧
    (dle p1 K.2 = true ∧ dle p2 K.2 = true ∧ dle p3 K.2 = true ∧ dle p4 K.2 = true) := by
  obtain ⟨hb, hK⟩ := cond_some h
  cases hK
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := and4 hb
  exact ⟨⟨c1, c2, c3, c4⟩, ⟨c5, c6, c7, c8⟩⟩

theorem mem_add {x y : α} {I J K : Iv} (hx : Mem S x I) (hy : Mem S y J) (h : ivAdd I J = some K) :
    Mem S (S.add x y) K := by
  cases h
  have l := rdn_le S.toOH (dadd I.1 J.1)
  have u := le_rup S.toOH (dadd I.2 J.2)
  have a1 := dv_add S.toOH I.1 J.1
  have a2 := dv_add S.toOH I.2 J.2
  have l' := S.le_respects (S.refl _) a1 l
  have u' := S.le_respects a2 (S.refl _) u
  exact ⟨by cr_linarith S.toOCR [l', hx.1, hy.1], by cr_linarith S.toOCR [u', hx.2, hy.2]⟩

theorem mem_sub {x y : α} {I J K : Iv} (hx : Mem S x I) (hy : Mem S y J) (h : ivSub I J = some K) :
    Mem S (S.add x (S.neg y)) K := by
  cases h
  have l := rdn_le S.toOH (dadd I.1 (dneg J.2))
  have u := le_rup S.toOH (dadd I.2 (dneg J.1))
  have a1 := S.trans (dv_add S.toOH I.1 (dneg J.2)) (S.add_congr (S.refl _) (dv_neg S.toOH J.2))
  have a2 := S.trans (dv_add S.toOH I.2 (dneg J.1)) (S.add_congr (S.refl _) (dv_neg S.toOH J.1))
  have l' := S.le_respects (S.refl _) a1 l
  have u' := S.le_respects a2 (S.refl _) u
  exact ⟨by cr_linarith S.toOCR [l', hx.1, hy.2], by cr_linarith S.toOCR [u', hx.2, hy.1]⟩

theorem ble_swap {x y : Nat} (h : Nat.ble x y = false) : Nat.ble y x = true := by
  cases Nat.le_total x y with
  | inl hxy => rw [Nat.ble_eq_true_of_le hxy] at h; cases h
  | inr hyx => exact Nat.ble_eq_true_of_le hyx

/-- `a ≤ b` refused means `b ≤ a`: the same comparison, sides swapped. -/
theorem dle_swap {a b : D} (h : dle a b = false) : dle b a = true := by
  unfold dle zle at h ⊢; exact ble_swap h

theorem dmin_l (a b : D) : S.le (dv S.toOH (dmin a b)) (dv S.toOH a) := by
  unfold dmin
  cases h : dle a b with
  | true => exact S.le_refl _
  | false => exact dle_sound S.toOH (dle_swap h)
theorem dmin_r (a b : D) : S.le (dv S.toOH (dmin a b)) (dv S.toOH b) := by
  unfold dmin
  cases h : dle a b with
  | true => exact dle_sound S.toOH h
  | false => exact S.le_refl _
theorem dmax_l (a b : D) : S.le (dv S.toOH a) (dv S.toOH (dmax a b)) := by
  unfold dmax
  cases h : dle a b with
  | true => exact dle_sound S.toOH h
  | false => exact S.le_refl _
theorem dmax_r (a b : D) : S.le (dv S.toOH b) (dv S.toOH (dmax a b)) := by
  unfold dmax
  cases h : dle a b with
  | true => exact S.le_refl _
  | false => exact dle_sound S.toOH (dle_swap h)

theorem mem_mul_aux {x y : α} {I J : Iv} {L U : D} (hx : Mem S x I) (hy : Mem S y J)
    (lo : S.le (dv S.toOH L) (dv S.toOH (dmin (dmin (dmul I.1 J.1) (dmul I.1 J.2)) (dmin (dmul I.2 J.1) (dmul I.2 J.2)))))
    (hi : S.le (dv S.toOH (dmax (dmax (dmul I.1 J.1) (dmul I.1 J.2)) (dmax (dmul I.2 J.1) (dmul I.2 J.2)))) (dv S.toOH U)) : Mem S (S.mul x y) (L, U) := by
  have m := fun a b => dv_mul S.toOH a b
  have c1 := S.le_trans lo (S.le_trans (dmin_l S _ _) (dmin_l S _ _))
  have c2 := S.le_trans lo (S.le_trans (dmin_l S _ _) (dmin_r S _ _))
  have c3 := S.le_trans lo (S.le_trans (dmin_r S _ _) (dmin_l S _ _))
  have c4 := S.le_trans lo (S.le_trans (dmin_r S _ _) (dmin_r S _ _))
  have c5 := S.le_trans (S.le_trans (dmax_l S _ _) (dmax_l S _ _)) hi
  have c6 := S.le_trans (S.le_trans (dmax_r S _ _) (dmax_l S _ _)) hi
  have c7 := S.le_trans (S.le_trans (dmax_l S _ _) (dmax_r S _ _)) hi
  have c8 := S.le_trans (S.le_trans (dmax_r S _ _) (dmax_r S _ _)) hi
  exact ⟨mul_lower S hx.1 hx.2 hy.1 hy.2
      (S.le_respects (S.refl _) (m _ _) c1) (S.le_respects (S.refl _) (m _ _) c2)
      (S.le_respects (S.refl _) (m _ _) c3) (S.le_respects (S.refl _) (m _ _) c4),
    mul_upper S hx.1 hx.2 hy.1 hy.2
      (S.le_respects (m _ _) (S.refl _) c5) (S.le_respects (m _ _) (S.refl _) c6)
      (S.le_respects (m _ _) (S.refl _) c7) (S.le_respects (m _ _) (S.refl _) c8)⟩

theorem mem_mul {x y : α} {I J K : Iv} (hx : Mem S x I) (hy : Mem S y J) (h : ivMul I J = some K) :
    Mem S (S.mul x y) K := by
  have hK : (rdn (dmin (dmin (dmul I.1 J.1) (dmul I.1 J.2)) (dmin (dmul I.2 J.1) (dmul I.2 J.2))), rup (dmax (dmax (dmul I.1 J.1) (dmul I.1 J.2)) (dmax (dmul I.2 J.1) (dmul I.2 J.2)))) = K := Option.some.inj h
  rw [← hK]
  exact mem_mul_aux S hx hy (rdn_le S.toOH _) (le_rup S.toOH _)

theorem mem_one : Mem S S.one one := by
  have e : S.r (dv S.toOH (⟨⟨1, 0⟩, 0⟩ : D)) S.one := by
    show S.r (S.mul (S.add (S.add S.one S.zero) (S.neg S.zero)) S.one) S.one
    cr_ring S.toCR
  exact ⟨S.le_respects (S.symm e) (S.refl _) (S.le_refl _), S.le_respects (S.refl _) (S.symm e) (S.le_refl _)⟩

theorem mem_pow {x : α} {I : Iv} (hx : Mem S x I) : ∀ n K, ivPow I n = some K → Mem S (powS S.toOH x n) K
  | 0, K, h => by cases h; exact mem_one S
  | n + 1, K, h => by
      obtain ⟨a, b, ea, eb, hk⟩ := lift2_some h
      cases ea
      exact mem_mul S hx (mem_pow hx n b eb) hk

theorem mem_cst (c : D) : Mem S (dv S.toOH c) (c, c) :=
  ⟨S.le_refl _, S.le_refl _⟩

/-- **THE READING ENCLOSES THE VALUE**, at every point of the box, in every `CF`. -/
theorem ivE_sound {B : Box} {p : Nat → α} (hp : InBox S B p) :
    ∀ (e : PE) (K : Iv), ivE B e = some K → Mem S (eval S.toOH p e) K
  | .var i, K, h => hp i K h
  | .cst c, K, h => by cases h; exact mem_cst S c
  | .add a b, K, h => by
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      exact mem_add S (ivE_sound hp a x ex) (ivE_sound hp b y ey) hk
  | .sub a b, K, h => by
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      exact mem_sub S (ivE_sound hp a x ex) (ivE_sound hp b y ey) hk
  | .mul a b, K, h => by
      obtain ⟨x, y, ex, ey, hk⟩ := lift2_some h
      exact mem_mul S (ivE_sound hp a x ex) (ivE_sound hp b y ey) hk
  | .pow a n, K, h => by
      unfold ivE at h
      cases ha : ivE B a with
      | none => rw [ha] at h; exact (none_ne_some h).elim
      | some I => rw [ha] at h; exact mem_pow S (ivE_sound hp a I ha) n K h

end ZIv

namespace ZIv
open ZNumBin
/-! The kernel reads `x·x − 2` on `x ∈ [1, 3/2]`: an interval inside `[−1, 1/4]`, so it does not exclude 0
(√2 is in the box) — and on `x ∈ [3/2, 2]` it reads inside `[1/4, 2]`, which does. -/
private def B1 : Box := fun i => if i == 0 then some (⟨⟨1, 0⟩, 0⟩, ⟨⟨3, 0⟩, 1⟩) else none
private def B2 : Box := fun i => if i == 0 then some (⟨⟨3, 0⟩, 1⟩, ⟨⟨2, 0⟩, 0⟩) else none
private def f : ZPoly.PE := .sub (.mul (.var 0) (.var 0)) (.cst ⟨⟨2, 0⟩, 0⟩)
example : (match ivE B1 f with | some K => dle K.1 ⟨⟨0, 0⟩, 0⟩ && dle ⟨⟨0, 0⟩, 0⟩ K.2 | none => false) = true := by decide +kernel
example : (match ivE B2 f with | some K => dle ⟨⟨1, 0⟩, 2⟩ K.1 | none => false) = true := by decide +kernel
end ZIv

#print axioms ZIv.mul_lower
#print axioms ZIv.mul_upper
#print axioms ZIv.mem_mul
#print axioms ZIv.mem_pow
#print axioms ZIv.ivE_sound
