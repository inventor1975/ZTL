import ZNet
import ZRound
import VR.Meta.CSRNorm
import QZ7
import QZ8
import QZ12
import QZ15

/-!
# QZ19 — an ordered field of the kernel with a square root of d added is one again, for every d. Zero axioms.

(2026-11-28, queue item F, "field tower". Written with AI.)

QZ15 adds the square root of two. This file is the same construction with the number under the root a PARAMETER:
the numbers are pairs (a, b), read a + b·√d, over any `ZNet.OF` F with a d that is not negative (`NonNeg`) and has
no square root in F (`NoRoot`: x·x = d·(y·y) → y = 0), and whose order is decidable. The order goes through the norm
N = a² − d·b²:
    a + b√d ≥ 0   :⇔   (a ≥ 0 and N ≥ 0)  or  (b ≥ 0 and N ≤ 0).

  `extOF`                F[√d] is an ordered field of the kernel (`ZNet.OF`): every law, the absolute value included
  `extInv`, `extMinMax`  with the inverse, the test for zero, min and max - so Gram–Schmidt (QZ12), the Born weight
                         (QZ8) and the certificates (QZ18) run over it
  the result is again a `ZNet.OF` with a decidable order (`posDec`), so the step can be repeated: Q(√2)(√3) is two steps,
  given that 3 has no root in Q(√2) (not proved here)

What changed against QZ15, beyond the parameter: d is carried IN THE TYPE (`Ed d`), so the proofs name it nowhere;
0 ≤ d is an instance (`NonNeg`); and the one step of QZ15 that halved an inequality (`le_of_double`, true of 2 only)
is replaced by cancelling d (`le_of_d_mul`: d·x ≤ d·y gives x ≤ y, because d ≥ 0 and d = 0 would have a root).
Where QZ15 wrote 2 for "twice" (N(p + q) = N p + N q + 2(...)), it is still 1 + 1.

Not here: that a given d has no root in a given field. For d = 2 over the rationals: Logik2's `Sqrt2.no_sqrt2`.
-/

namespace QZ19
open ZNet
open QZ15 (ofCR)

variable {α : Type} {dd : α}

/-- a + b·√d -/
structure Ed {α : Type} (dd : α) where
  a : α
  b : α

theorem ext2 {p q : Ed dd} (h1 : p.a = q.a) (h2 : p.b = q.b) : p = q := by
  cases p; cases q; cases h1; cases h2; rfl

/-! ### the operations, over a ring of the normaliser -/

section Ring
variable (R : VR.CSR.CR α)

def eadd (p q : Ed dd) : Ed dd := ⟨R.add p.a q.a, R.add p.b q.b⟩
def eneg (p : Ed dd) : Ed dd := ⟨R.neg p.a, R.neg p.b⟩
def emul (p q : Ed dd) : Ed dd :=
  ⟨R.add (R.mul p.a q.a) (R.mul dd (R.mul p.b q.b)), R.add (R.mul p.a q.b) (R.mul p.b q.a)⟩
def ezero : Ed dd := ⟨R.zero, R.zero⟩
def eone : Ed dd := ⟨R.one, R.zero⟩
/-- the norm: a² − d·b² -/
def nrm (p : Ed dd) : α := R.add (R.mul p.a p.a) (R.neg (R.mul dd (R.mul p.b p.b)))

theorem add_comm_a (p q : Ed dd) : R.r (eadd R p q).a (eadd R q p).a := by dsimp only [eadd]; cr_ring R
theorem add_comm_b (p q : Ed dd) : R.r (eadd R p q).b (eadd R q p).b := by dsimp only [eadd]; cr_ring R
theorem add_assoc_a (p q s : Ed dd) : R.r (eadd R (eadd R p q) s).a (eadd R p (eadd R q s)).a := by dsimp only [eadd]; cr_ring R
theorem add_assoc_b (p q s : Ed dd) : R.r (eadd R (eadd R p q) s).b (eadd R p (eadd R q s)).b := by dsimp only [eadd]; cr_ring R
theorem add_zero_a (p : Ed dd) : R.r (eadd R p (ezero (dd := dd) R)).a p.a := by dsimp only [eadd, ezero]; cr_ring R
theorem add_zero_b (p : Ed dd) : R.r (eadd R p (ezero (dd := dd) R)).b p.b := by dsimp only [eadd, ezero]; cr_ring R
theorem add_neg_a (p : Ed dd) : R.r (eadd R p (eneg R p)).a (ezero (dd := dd) R).a := by dsimp only [eadd, eneg, ezero]; cr_ring R
theorem add_neg_b (p : Ed dd) : R.r (eadd R p (eneg R p)).b (ezero (dd := dd) R).b := by dsimp only [eadd, eneg, ezero]; cr_ring R
theorem mul_comm_a (p q : Ed dd) : R.r (emul R p q).a (emul R q p).a := by dsimp only [emul]; cr_ring R
theorem mul_comm_b (p q : Ed dd) : R.r (emul R p q).b (emul R q p).b := by dsimp only [emul]; cr_ring R
theorem mul_assoc_a (p q s : Ed dd) : R.r (emul R (emul R p q) s).a (emul R p (emul R q s)).a := by dsimp only [emul]; cr_ring R
theorem mul_assoc_b (p q s : Ed dd) : R.r (emul R (emul R p q) s).b (emul R p (emul R q s)).b := by dsimp only [emul]; cr_ring R
theorem mul_one_a (p : Ed dd) : R.r (emul R p (eone (dd := dd) R)).a p.a := by dsimp only [emul, eone]; cr_ring R
theorem mul_one_b (p : Ed dd) : R.r (emul R p (eone (dd := dd) R)).b p.b := by dsimp only [emul, eone]; cr_ring R
theorem mul_zero_a (p : Ed dd) : R.r (emul R p (ezero (dd := dd) R)).a (ezero (dd := dd) R).a := by dsimp only [emul, ezero]; cr_ring R
theorem mul_zero_b (p : Ed dd) : R.r (emul R p (ezero (dd := dd) R)).b (ezero (dd := dd) R).b := by dsimp only [emul, ezero]; cr_ring R
theorem mul_add_a (p q s : Ed dd) : R.r (emul R p (eadd R q s)).a (eadd R (emul R p q) (emul R p s)).a := by
  dsimp only [emul, eadd]; cr_ring R
theorem mul_add_b (p q s : Ed dd) : R.r (emul R p (eadd R q s)).b (eadd R (emul R p q) (emul R p s)).b := by
  dsimp only [emul, eadd]; cr_ring R
theorem neg_mul_a (p q : Ed dd) : R.r (emul R (eneg R p) q).a (eneg R (emul R p q)).a := by dsimp only [emul, eneg]; cr_ring R
theorem neg_mul_b (p q : Ed dd) : R.r (emul R (eneg R p) q).b (eneg R (emul R p q)).b := by dsimp only [emul, eneg]; cr_ring R
theorem neg_neg_a (p : Ed dd) : R.r (eneg R (eneg R p)).a p.a := by dsimp only [eneg]; cr_ring R
theorem neg_neg_b (p : Ed dd) : R.r (eneg R (eneg R p)).b p.b := by dsimp only [eneg]; cr_ring R

/-- THE NORM IS MULTIPLICATIVE -/
theorem nrm_mul (p q : Ed dd) : R.r (nrm R (emul R p q)) (R.mul (nrm R p) (nrm R q)) := by
  dsimp only [nrm, emul]; cr_ring R
theorem nrm_neg (p : Ed dd) : R.r (nrm R (eneg R p)) (nrm R p) := by dsimp only [nrm, eneg]; cr_ring R
/-- N(p + q) = N p + N q + 2(aa' − d·bb') -/
theorem nrm_add (p q : Ed dd) :
    R.r (nrm R (eadd R p q))
      (R.add (R.add (nrm R p) (nrm R q))
        (R.mul (R.add R.one R.one) (R.add (R.mul p.a q.a) (R.neg (R.mul dd (R.mul p.b q.b)))))) := by
  dsimp only [nrm, eadd]; cr_ring R
/-- −N(p + q) = (−N p) + (−N q) + 2(d·bb' − aa') -/
theorem nrm_add_neg (p q : Ed dd) :
    R.r (R.neg (nrm R (eadd R p q)))
      (R.add (R.add (R.neg (nrm R p)) (R.neg (nrm R q)))
        (R.mul (R.add R.one R.one) (R.add (R.mul dd (R.mul p.b q.b)) (R.neg (R.mul p.a q.a))))) := by
  dsimp only [nrm, eadd]; cr_ring R
theorem nrm_double (p : Ed dd) : R.r (nrm R (eadd R p p)) (R.add (R.add (nrm R p) (nrm R p)) (R.add (nrm R p) (nrm R p))) := by
  dsimp only [nrm, eadd]; cr_ring R

theorem dsq (z x : α) : R.r (R.mul (R.add z (R.neg x)) (R.add z x)) (R.add (R.mul z z) (R.neg (R.mul x x))) := by cr_ring R
theorem negsq (y : α) : R.r (R.mul (R.neg y) (R.neg y)) (R.mul y y) := by cr_ring R
theorem idA (a a' : α) : R.r (R.mul (R.mul a a') (R.mul a a')) (R.mul (R.mul a a) (R.mul a' a')) := by cr_ring R
theorem idB (b b' : α) : R.r (R.mul (R.mul dd (R.mul b b')) (R.mul dd (R.mul b b')))
    (R.mul (R.mul dd (R.mul b b)) (R.mul dd (R.mul b' b'))) := by cr_ring R

theorem cancel_a (p q : Ed dd) : R.r (eadd R p (eneg R (eadd R p q))).a (eneg R q).a := by dsimp only [eadd, eneg]; cr_ring R
theorem cancel_b (p q : Ed dd) : R.r (eadd R p (eneg R (eadd R p q))).b (eneg R q).b := by dsimp only [eadd, eneg]; cr_ring R
theorem cancel2_a (p q : Ed dd) : R.r (eadd R q (eneg R (eadd R p q))).a (eneg R p).a := by dsimp only [eadd, eneg]; cr_ring R
theorem cancel2_b (p q : Ed dd) : R.r (eadd R q (eneg R (eadd R p q))).b (eneg R p).b := by dsimp only [eadd, eneg]; cr_ring R
theorem idE (x y : α) : R.r (R.mul x (R.mul dd y)) (R.mul dd (R.mul x y)) := by cr_ring R
theorem negneg (x y : α) : R.r (R.mul (R.neg x) (R.neg y)) (R.mul x y) := by cr_ring R

theorem nrm_zero : R.r (nrm R (ezero (dd := dd) R)) R.zero := by dsimp only [nrm, ezero]; cr_ring R
theorem i_sub0 (p : Ed dd) : R.r (eadd R p (eneg R (ezero (dd := dd) R))).a p.a ∧ R.r (eadd R p (eneg R (ezero (dd := dd) R))).b p.b := by
  constructor <;> (dsimp only [eadd, eneg, ezero]; cr_ring R)
theorem i_0sub (p : Ed dd) : R.r (eadd R (ezero (dd := dd) R) (eneg R p)).a (eneg R p).a ∧ R.r (eadd R (ezero (dd := dd) R) (eneg R p)).b (eneg R p).b := by
  constructor <;> (dsimp only [eadd, eneg, ezero]; cr_ring R)
theorem i_trans (p q s : Ed dd) :
    R.r (eadd R (eadd R s (eneg R q)) (eadd R q (eneg R p))).a (eadd R s (eneg R p)).a ∧
    R.r (eadd R (eadd R s (eneg R q)) (eadd R q (eneg R p))).b (eadd R s (eneg R p)).b := by
  constructor <;> (dsimp only [eadd, eneg]; cr_ring R)
theorem i_addle (a b c d : Ed dd) :
    R.r (eadd R (eadd R b (eneg R a)) (eadd R d (eneg R c))).a (eadd R (eadd R b d) (eneg R (eadd R a c))).a ∧
    R.r (eadd R (eadd R b (eneg R a)) (eadd R d (eneg R c))).b (eadd R (eadd R b d) (eneg R (eadd R a c))).b := by
  constructor <;> (dsimp only [eadd, eneg]; cr_ring R)
theorem i_mulle (c a b : Ed dd) :
    R.r (emul R c (eadd R b (eneg R a))).a (eadd R (emul R c b) (eneg R (emul R c a))).a ∧
    R.r (emul R c (eadd R b (eneg R a))).b (eadd R (emul R c b) (eneg R (emul R c a))).b := by
  constructor <;> (dsimp only [emul, eadd, eneg]; cr_ring R)
theorem i_flip (p q : Ed dd) :
    R.r (eneg R (eadd R q (eneg R p))).a (eadd R p (eneg R q)).a ∧ R.r (eneg R (eadd R q (eneg R p))).b (eadd R p (eneg R q)).b := by
  constructor <;> (dsimp only [eadd, eneg]; cr_ring R)
theorem i_mulneg (a b : Ed dd) :
    R.r (emul R a (eneg R b)).a (eneg R (emul R a b)).a ∧ R.r (emul R a (eneg R b)).b (eneg R (emul R a b)).b := by
  constructor <;> (dsimp only [emul, eneg]; cr_ring R)
theorem i_negnegmul (a b : Ed dd) :
    R.r (emul R (eneg R a) (eneg R b)).a (emul R a b).a ∧ R.r (emul R (eneg R a) (eneg R b)).b (emul R a b).b := by
  constructor <;> (dsimp only [emul, eneg]; cr_ring R)
theorem i_abs2 (x y a b : Ed dd) :
    R.r (eadd R (eadd R x (eneg R (eneg R a))) (eadd R y (eneg R (eneg R b)))).a (eadd R (eadd R x y) (eneg R (eneg R (eadd R a b)))).a ∧
    R.r (eadd R (eadd R x (eneg R (eneg R a))) (eadd R y (eneg R (eneg R b)))).b (eadd R (eadd R x y) (eneg R (eneg R (eadd R a b)))).b := by
  constructor <;> (dsimp only [eadd, eneg]; cr_ring R)
theorem i_aa (a : Ed dd) : R.r (eadd R a (eneg R (eneg R a))).a (eadd R a a).a ∧ R.r (eadd R a (eneg R (eneg R a))).b (eadd R a a).b := by
  constructor <;> (dsimp only [eadd, eneg]; cr_ring R)
theorem i_nn0 (a : Ed dd) : R.r (eadd R (eneg R a) (eneg R (eneg R a))).a (ezero (dd := dd) R).a ∧ R.r (eadd R (eneg R a) (eneg R (eneg R a))).b (ezero (dd := dd) R).b := by
  constructor <;> (dsimp only [eadd, eneg, ezero]; cr_ring R)
/-- N·c = a·(ac + d·be) − d·b·(ae + bc) (the fourth letter of the statement is e here) -/
theorem idK (a b c d : α) :
    R.r (R.mul (R.add (R.mul a a) (R.neg (R.mul dd (R.mul b b)))) c)
      (R.add (R.mul a (R.add (R.mul a c) (R.mul dd (R.mul b d)))) (R.neg (R.mul (R.mul dd b) (R.add (R.mul a d) (R.mul b c))))) := by
  cr_ring R
/-- N·e = a·(ae + bc) − b·(ac + d·be) -/
theorem idL (a b c d : α) :
    R.r (R.mul (R.add (R.mul a a) (R.neg (R.mul dd (R.mul b b)))) d)
      (R.add (R.mul a (R.add (R.mul a d) (R.mul b c))) (R.neg (R.mul b (R.add (R.mul a c) (R.mul dd (R.mul b d)))))) := by
  cr_ring R

theorem invA (a b c : α) :
    R.r (R.add (R.mul a (R.mul a c)) (R.mul dd (R.mul b (R.mul (R.neg b) c))))
      (R.mul (R.add (R.mul a a) (R.neg (R.mul dd (R.mul b b)))) c) := by cr_ring R
theorem invB (a b c : α) : R.r (R.add (R.mul a (R.mul (R.neg b) c)) (R.mul b (R.mul a c))) R.zero := by cr_ring R

end Ring

/-! ### the order of the base field: what is used -/

variable (F : OF α)

theorem le_of_eq' {x y : α} (h : x = y) : F.le x y := h ▸ F.le_refl x

theorem zero_le_one : F.le F.zero F.one := by
  have h := F.sq_nonneg F.one
  rw [F.mul_one] at h
  exact h

theorem nn_add {x y : α} (hx : F.le F.zero x) (hy : F.le F.zero y) : F.le F.zero (F.add x y) := by
  have h := F.add_le_add hx hy
  rw [F.add_zero] at h
  exact h

/-- d is not negative (carried as an instance, so that it need not be passed by hand) -/
class NonNeg (F : OF α) (dd : α) : Prop where
  h : F.le F.zero dd

theorem d_nonneg [n : NonNeg F dd] : F.le F.zero dd := n.h
theorem two_nonneg : F.le F.zero (F.add F.one F.one) := nn_add F (zero_le_one F) (zero_le_one F)

-- the instance is carried by every statement of the section, used or not (it is always at hand where d is)
set_option linter.unusedSectionVars false
variable [NonNeg F dd]

theorem neg_nn {x : α} (h : F.le x F.zero) : F.le F.zero (F.neg x) := by
  have h1 := QZ8.neg_le_neg F h
  rw [ZNet.neg_zero] at h1
  exact h1

theorem neg_np {x : α} (h : F.le F.zero x) : F.le (F.neg x) F.zero := by
  have h1 := QZ8.neg_le_neg F h
  rw [ZNet.neg_zero] at h1
  exact h1

theorem np_of_neg_nn {x : α} (h : F.le F.zero (F.neg x)) : F.le x F.zero := by
  have h1 := neg_np F h
  rw [F.neg_neg] at h1
  exact h1

theorem nn_of_neg_np {x : α} (h : F.le (F.neg x) F.zero) : F.le F.zero x := by
  have h1 := neg_nn F h
  rw [F.neg_neg] at h1
  exact h1

theorem zero_of_sum {a b : α} (ha : F.le F.zero a) (hb : F.le F.zero b) (h : F.add a b = F.zero) : a = F.zero := by
  have h1 := F.add_le_add (F.le_refl a) hb
  rw [F.add_zero, h] at h1
  exact F.le_antisymm h1 ha

/-- 0 ≤ u ≤ v and 0 ≤ v', u' ≤ v': u·u' ≤ v·v' -/
theorem mul_mono {u v u' v' : α} (hu : F.le F.zero u) (huv : F.le u v) (hv' : F.le F.zero v') (hu'v' : F.le u' v') :
    F.le (F.mul u u') (F.mul v v') := by
  have h1 : F.le (F.mul u u') (F.mul u v') := F.mul_le_mul_left hu hu'v'
  have h2 : F.le (F.mul v' u) (F.mul v' v) := F.mul_le_mul_left hv' huv
  rw [F.mul_comm v' u, F.mul_comm v' v] at h2
  exact F.le_trans h1 h2

/-- for numbers that are not negative, the squares compare as the numbers do -/
theorem le_of_sq_le {x z : α} (hx : F.le F.zero x) (hz : F.le F.zero z) (h : F.le (F.mul z z) (F.mul x x)) : F.le z x := by
  cases F.le_total z x with
  | inl h1 => exact h1
  | inr h1 =>
    have h2 : F.le (F.mul x x) (F.mul z z) := mul_mono F hx h1 hz h1
    have e : F.mul z z = F.mul x x := F.le_antisymm h h2
    have id : F.mul (F.add z (F.neg x)) (F.add z x) = F.add (F.mul z z) (F.neg (F.mul x x)) := dsq (ofCR F) z x
    have e2 : F.mul (F.add z (F.neg x)) (F.add z x) = F.zero := by
      rw [id, e]
      exact F.add_neg _
    cases F.mul_eq_zero e2 with
    | inl e3 =>
      have e4 := ZNet.eq_neg_of_add F e3
      rw [F.neg_neg] at e4
      rw [e4]
      exact F.le_refl x
    | inr e3 =>
      have ez : z = F.zero := zero_of_sum F hz hx e3
      have ex : x = F.zero := by
        rw [ez, ZNet.zero_add] at e3
        exact e3
      rw [ez, ex]
      exact F.le_refl _

/-- 0 ≤ x and y² ≤ x²: 0 ≤ x + y -/
theorem nn_add_of_sq {x y : α} (hx : F.le F.zero x) (h : F.le (F.mul y y) (F.mul x x)) : F.le F.zero (F.add x y) := by
  cases F.le_total F.zero y with
  | inl hy => exact nn_add F hx hy
  | inr hy =>
    have hz : F.le F.zero (F.neg y) := neg_nn F hy
    have hsq : F.mul (F.neg y) (F.neg y) = F.mul y y := negsq (ofCR F) y
    have h1 : F.le (F.neg y) x := le_of_sq_le F hx hz (by rw [hsq]; exact h)
    have h2 := ZNet.sub_nonneg_of_le F h1
    have h3 : F.le F.zero (F.add x (F.neg (F.neg y))) := h2
    rw [F.neg_neg] at h3
    exact h3

/-- …and 0 ≤ x − y -/
theorem nn_sub_of_sq {x y : α} (hx : F.le F.zero x) (h : F.le (F.mul y y) (F.mul x x)) : F.le F.zero (F.add x (F.neg y)) := by
  have hsq : F.mul (F.neg y) (F.neg y) = F.mul y y := negsq (ofCR F) y
  exact nn_add_of_sq F hx (by rw [hsq]; exact h)

/-! ### the order of the extension -/

/-- d has no square root in the base field (said without division) -/
def NoRoot (dd : α) : Prop := ∀ x y : α, F.mul x x = F.mul dd (F.mul y y) → y = F.zero

/-- not negative, the first way: a ≥ 0 and the norm is not negative -/
def PosA (p : Ed dd) : Prop := F.le F.zero p.a ∧ F.le F.zero (nrm (ofCR F) p)
/-- the second way: b ≥ 0 and the norm is not positive -/
def PosB (p : Ed dd) : Prop := F.le F.zero p.b ∧ F.le (nrm (ofCR F) p) F.zero
/-- a + b√d is not negative -/
def Pos (p : Ed dd) : Prop := PosA F p ∨ PosB F p

theorem sqA {p : Ed dd} (h : PosA F p) : F.le (F.mul dd (F.mul p.b p.b)) (F.mul p.a p.a) :=
  ZNet.le_of_sub_nonneg F (show F.le F.zero (ZNet.sub F (F.mul p.a p.a) (F.mul dd (F.mul p.b p.b))) from h.2)

theorem sqB {p : Ed dd} (h : PosB F p) : F.le (F.mul p.a p.a) (F.mul dd (F.mul p.b p.b)) :=
  ZNet.le_of_sub_nonpos F (show F.le (ZNet.sub F (F.mul p.a p.a) (F.mul dd (F.mul p.b p.b))) F.zero from h.2)

theorem d_sq_nonneg (b : α) : F.le F.zero (F.mul dd (F.mul b b)) :=
  F.mul_nonneg (d_nonneg F) (F.sq_nonneg b)

/-- A + A is A -/
theorem posA_add {p q : Ed dd} (hp : PosA F p) (hq : PosA F q) : PosA F (eadd (ofCR F) p q) := by
  have hsq : F.le (F.mul (F.mul dd (F.mul p.b q.b)) (F.mul dd (F.mul p.b q.b)))
      (F.mul (F.mul p.a q.a) (F.mul p.a q.a)) :=
    F.le_trans (le_of_eq' F (idB (ofCR F) p.b q.b))
      (F.le_trans (mul_mono F (d_sq_nonneg F p.b) (sqA F hp) (F.sq_nonneg q.a) (sqA F hq))
        (le_of_eq' F (idA (ofCR F) p.a q.a).symm))
  have hd : F.le F.zero (F.add (F.mul p.a q.a) (F.neg (F.mul dd (F.mul p.b q.b)))) :=
    nn_sub_of_sq F (F.mul_nonneg hp.1 hq.1) hsq
  have hN := nn_add F (nn_add F hp.2 hq.2) (F.mul_nonneg (two_nonneg F) hd)
  exact ⟨nn_add F hp.1 hq.1, F.le_trans hN (le_of_eq' F (nrm_add (ofCR F) p q).symm)⟩

/-- B + B is B -/
theorem posB_add {p q : Ed dd} (hp : PosB F p) (hq : PosB F q) : PosB F (eadd (ofCR F) p q) := by
  have hsq : F.le (F.mul (F.mul p.a q.a) (F.mul p.a q.a))
      (F.mul (F.mul dd (F.mul p.b q.b)) (F.mul dd (F.mul p.b q.b))) :=
    F.le_trans (le_of_eq' F (idA (ofCR F) p.a q.a))
      (F.le_trans (mul_mono F (F.sq_nonneg p.a) (sqB F hp) (d_sq_nonneg F q.b) (sqB F hq))
        (le_of_eq' F (idB (ofCR F) p.b q.b).symm))
  have hx : F.le F.zero (F.mul dd (F.mul p.b q.b)) := F.mul_nonneg (d_nonneg F) (F.mul_nonneg hp.1 hq.1)
  have hd : F.le F.zero (F.add (F.mul dd (F.mul p.b q.b)) (F.neg (F.mul p.a q.a))) :=
    nn_sub_of_sq F hx hsq
  have hN := nn_add F (nn_add F (neg_nn F hp.2) (neg_nn F hq.2)) (F.mul_nonneg (two_nonneg F) hd)
  have hN' : F.le F.zero (F.neg (nrm (ofCR F) (eadd (ofCR F) p q))) :=
    F.le_trans hN (le_of_eq' F (nrm_add_neg (ofCR F) p q).symm)
  exact ⟨nn_add F hp.1 hq.1, np_of_neg_nn F hN'⟩

/-! ### a number and its negative both not negative: zero (here d having no root is used) -/

theorem sq_zero {a : α} (h : F.le (F.mul a a) F.zero) : a = F.zero := by
  have e := F.le_antisymm h (F.sq_nonneg a)
  cases F.mul_eq_zero e with
  | inl e3 => exact e3
  | inr e3 => exact e3

theorem sq_zero_of_two [NonNeg F dd] (nr : NoRoot F dd) {b : α} (h : F.le (F.mul dd (F.mul b b)) F.zero) : b = F.zero := by
  have e : F.mul dd (F.mul b b) = F.zero := F.le_antisymm h (d_sq_nonneg F b)
  exact nr F.zero b (by rw [F.mul_zero]; exact e.symm)

theorem pos_antisymm (nr : NoRoot F dd) {p : Ed dd} (h1 : Pos F p) (h2 : Pos F (eneg (ofCR F) p)) :
    p.a = F.zero ∧ p.b = F.zero := by
  have eN : nrm (ofCR F) (eneg (ofCR F) p) = nrm (ofCR F) p := nrm_neg (ofCR F) p
  have fromN0 : nrm (ofCR F) p = F.zero → p.a = F.zero ∧ p.b = F.zero := by
    intro e
    have e' : F.add (F.mul p.a p.a) (F.neg (F.mul dd (F.mul p.b p.b))) = F.zero := e
    have e2 := ZNet.eq_neg_of_add F e'
    rw [F.neg_neg] at e2
    have hb : p.b = F.zero := nr p.a p.b e2
    have ha : F.mul p.a p.a = F.zero := by rw [e2, hb, F.mul_zero, F.mul_zero]
    cases F.mul_eq_zero ha with
    | inl e3 => exact ⟨e3, hb⟩
    | inr e3 => exact ⟨e3, hb⟩
  cases h1 with
  | inl hA =>
    cases h2 with
    | inl hA' =>
      have hna : F.le F.zero (F.neg p.a) := hA'.1
      have ha : p.a = F.zero := F.le_antisymm (np_of_neg_nn F hna) hA.1
      have s := sqA F hA
      rw [ha, F.mul_zero] at s
      exact ⟨ha, sq_zero_of_two F nr s⟩
    | inr hB' =>
      have hle : F.le (nrm (ofCR F) p) F.zero := eN ▸ hB'.2
      exact fromN0 (F.le_antisymm hle hA.2)
  | inr hB =>
    cases h2 with
    | inl hA' =>
      have hge : F.le F.zero (nrm (ofCR F) p) := eN ▸ hA'.2
      exact fromN0 (F.le_antisymm hB.2 hge)
    | inr hB' =>
      have hnb : F.le F.zero (F.neg p.b) := hB'.1
      have hb : p.b = F.zero := F.le_antisymm (np_of_neg_nn F hnb) hB.1
      have s := sqB F hB
      rw [hb, F.mul_zero, F.mul_zero] at s
      exact ⟨sq_zero F s, hb⟩

/-! ### the not-negative numbers are closed under addition and multiplication -/

theorem posAB_add (nr : NoRoot F dd) {p q : Ed dd} (hp : PosA F p) (hq : PosB F q) : Pos F (eadd (ofCR F) p q) := by
  cases F.le_total F.zero (nrm (ofCR F) (eadd (ofCR F) p q)) with
  | inl hN =>
    cases F.le_total F.zero (F.add p.a q.a) with
    | inl ha => exact Or.inl ⟨ha, hN⟩
    | inr ha =>
      have hns : PosA F (eneg (ofCR F) (eadd (ofCR F) p q)) :=
        ⟨neg_nn F ha, F.le_trans hN (le_of_eq' F (nrm_neg (ofCR F) (eadd (ofCR F) p q)).symm)⟩
      have h3 := posA_add F hp hns
      have e : eadd (ofCR F) p (eneg (ofCR F) (eadd (ofCR F) p q)) = eneg (ofCR F) q :=
        ext2 (cancel_a (ofCR F) p q) (cancel_b (ofCR F) p q)
      have z := pos_antisymm F nr (Or.inr hq) (Or.inl (e ▸ h3))
      have ha' : F.le F.zero (F.add p.a q.a) := by
        rw [z.1, F.add_zero]
        exact hp.1
      exact Or.inl ⟨ha', hN⟩
  | inr hN =>
    cases F.le_total F.zero (F.add p.b q.b) with
    | inl hb => exact Or.inr ⟨hb, hN⟩
    | inr hb =>
      have hns : PosB F (eneg (ofCR F) (eadd (ofCR F) p q)) :=
        ⟨neg_nn F hb, F.le_trans (le_of_eq' F (nrm_neg (ofCR F) (eadd (ofCR F) p q))) hN⟩
      have h3 := posB_add F hq hns
      have e : eadd (ofCR F) q (eneg (ofCR F) (eadd (ofCR F) p q)) = eneg (ofCR F) p :=
        ext2 (cancel2_a (ofCR F) p q) (cancel2_b (ofCR F) p q)
      have z := pos_antisymm F nr (Or.inl hp) (Or.inr (e ▸ h3))
      have hb' : F.le F.zero (F.add p.b q.b) := by
        rw [z.2, ZNet.zero_add]
        exact hq.1
      exact Or.inr ⟨hb', hN⟩

/-- THE SUM OF TWO NOT-NEGATIVE NUMBERS IS NOT NEGATIVE -/
theorem pos_add (nr : NoRoot F dd) {p q : Ed dd} (hp : Pos F p) (hq : Pos F q) : Pos F (eadd (ofCR F) p q) := by
  cases hp with
  | inl hA =>
    cases hq with
    | inl hA' => exact Or.inl (posA_add F hA hA')
    | inr hB' => exact posAB_add F nr hA hB'
  | inr hB =>
    cases hq with
    | inl hA' =>
      have e : eadd (ofCR F) q p = eadd (ofCR F) p q := ext2 (add_comm_a (ofCR F) q p) (add_comm_b (ofCR F) q p)
      exact e ▸ posAB_add F nr hA' hB
    | inr hB' => exact Or.inr (posB_add F hB hB')

theorem posAA_mul {p q : Ed dd} (hp : PosA F p) (hq : PosA F q) : PosA F (emul (ofCR F) p q) := by
  have hsq : F.le (F.mul (F.mul dd (F.mul p.b q.b)) (F.mul dd (F.mul p.b q.b)))
      (F.mul (F.mul p.a q.a) (F.mul p.a q.a)) :=
    F.le_trans (le_of_eq' F (idB (ofCR F) p.b q.b))
      (F.le_trans (mul_mono F (d_sq_nonneg F p.b) (sqA F hp) (F.sq_nonneg q.a) (sqA F hq))
        (le_of_eq' F (idA (ofCR F) p.a q.a).symm))
  exact ⟨nn_add_of_sq F (F.mul_nonneg hp.1 hq.1) hsq,
    F.le_trans (F.mul_nonneg hp.2 hq.2) (le_of_eq' F (nrm_mul (ofCR F) p q).symm)⟩

/-- d·x ≤ d·y gives x ≤ y: d is not negative and not zero (zero has a root) -/
theorem le_of_d_mul (nr : NoRoot F dd) {x y : α} (h : F.le (F.mul dd x) (F.mul dd y)) : F.le x y := by
  cases F.le_total x y with
  | inl h' => exact h'
  | inr h' =>
    have e : F.mul dd x = F.mul dd y := F.le_antisymm h (F.mul_le_mul_left (d_nonneg F) h')
    have e0 : F.mul dd (F.add x (F.neg y)) = F.zero := by rw [F.mul_add, ZNet.mul_neg, e, F.add_neg]
    cases F.mul_eq_zero e0 with
    | inl hd =>
      have all : ∀ z : α, z = F.zero := fun z => nr F.zero z (by rw [F.mul_zero, hd, ZNet.zero_mul])
      rw [all x, all y]
      exact F.le_refl _
    | inr hxy =>
      exact ZNet.le_of_sub_nonpos F (show F.le (ZNet.sub F x y) F.zero from by
        show F.le (F.add x (F.neg y)) F.zero
        rw [hxy]
        exact F.le_refl _)

theorem posAB_mul (nr : NoRoot F dd) {p q : Ed dd} (hp : PosA F p) (hq : PosB F q) : PosB F (emul (ofCR F) p q) := by
  -- (bc)² ≤ (ad)²: from d·b² ≤ a² and c² ≤ d·d'², with d cancelled
  have h1 : F.le (F.mul (F.mul dd (F.mul p.b p.b)) (F.mul q.a q.a))
      (F.mul (F.mul p.a p.a) (F.mul dd (F.mul q.b q.b))) :=
    mul_mono F (d_sq_nonneg F p.b) (sqA F hp) (d_sq_nonneg F q.b) (sqB F hq)
  have h2 : F.le (F.mul dd (F.mul (F.mul p.b p.b) (F.mul q.a q.a))) (F.mul dd (F.mul (F.mul p.a p.a) (F.mul q.b q.b))) :=
    F.le_trans (le_of_eq' F (F.mul_assoc dd (F.mul p.b p.b) (F.mul q.a q.a)).symm)
      (F.le_trans h1 (le_of_eq' F (idE (ofCR F) (F.mul p.a p.a) (F.mul q.b q.b))))
  have hsq : F.le (F.mul (F.mul p.b q.a) (F.mul p.b q.a)) (F.mul (F.mul p.a q.b) (F.mul p.a q.b)) :=
    F.le_trans (le_of_eq' F (idA (ofCR F) p.b q.a))
      (F.le_trans (le_of_d_mul F nr h2) (le_of_eq' F (idA (ofCR F) p.a q.b).symm))
  exact ⟨nn_add_of_sq F (F.mul_nonneg hp.1 hq.1) hsq,
    F.le_trans (le_of_eq' F (nrm_mul (ofCR F) p q))
      (F.le_trans (le_of_eq' F (F.mul_comm _ _)) (F.nonpos_mul hq.2 hp.2))⟩

theorem posBB_mul {p q : Ed dd} (hp : PosB F p) (hq : PosB F q) : PosA F (emul (ofCR F) p q) := by
  have hsq : F.le (F.mul (F.mul p.a q.a) (F.mul p.a q.a))
      (F.mul (F.mul dd (F.mul p.b q.b)) (F.mul dd (F.mul p.b q.b))) :=
    F.le_trans (le_of_eq' F (idA (ofCR F) p.a q.a))
      (F.le_trans (mul_mono F (F.sq_nonneg p.a) (sqB F hp) (d_sq_nonneg F q.b) (sqB F hq))
        (le_of_eq' F (idB (ofCR F) p.b q.b).symm))
  have hx : F.le F.zero (F.mul dd (F.mul p.b q.b)) := F.mul_nonneg (d_nonneg F) (F.mul_nonneg hp.1 hq.1)
  have h1 := nn_add_of_sq F hx hsq
  rw [F.add_comm] at h1
  exact ⟨h1, F.le_trans (F.le_trans (F.mul_nonneg (neg_nn F hp.2) (neg_nn F hq.2))
      (le_of_eq' F (negneg (ofCR F) (nrm (ofCR F) p) (nrm (ofCR F) q)))) (le_of_eq' F (nrm_mul (ofCR F) p q).symm)⟩

/-- THE PRODUCT OF TWO NOT-NEGATIVE NUMBERS IS NOT NEGATIVE -/
theorem pos_mul (nr : NoRoot F dd) {p q : Ed dd} (hp : Pos F p) (hq : Pos F q) : Pos F (emul (ofCR F) p q) := by
  cases hp with
  | inl hA =>
    cases hq with
    | inl hA' => exact Or.inl (posAA_mul F hA hA')
    | inr hB' => exact Or.inr (posAB_mul F nr hA hB')
  | inr hB =>
    cases hq with
    | inl hA' =>
      have e : emul (ofCR F) q p = emul (ofCR F) p q := ext2 (mul_comm_a (ofCR F) q p) (mul_comm_b (ofCR F) q p)
      exact Or.inr (e ▸ posAB_mul F nr hA' hB)
    | inr hB' => exact Or.inl (posBB_mul F hB hB')

/-! ### the ordered field -/

theorem eqE {p q : Ed dd} (h : p.a = q.a ∧ p.b = q.b) : p = q := ext2 h.1 h.2

theorem pos_zero : Pos F (ezero (dd := dd) (ofCR F)) := Or.inl ⟨F.le_refl _, le_of_eq' F (nrm_zero (ofCR F)).symm⟩

/-- p ≤ q: q − p is not negative -/
def ele (p q : Ed dd) : Prop := Pos F (eadd (ofCR F) q (eneg (ofCR F) p))

theorem pos_congr {x y : Ed dd} (e : x = y) (h : Pos F x) : Pos F y := e ▸ h

theorem pos_of_zero_le {p : Ed dd} (h : ele F (ezero (dd := dd) (ofCR F)) p) : Pos F p := pos_congr F (eqE (i_sub0 (ofCR F) p)) h
theorem zero_le_of_pos {p : Ed dd} (h : Pos F p) : ele F (ezero (dd := dd) (ofCR F)) p := pos_congr F (eqE (i_sub0 (ofCR F) p)).symm h
theorem negpos_of_le_zero {p : Ed dd} (h : ele F p (ezero (dd := dd) (ofCR F))) : Pos F (eneg (ofCR F) p) :=
  pos_congr F (eqE (i_0sub (ofCR F) p)) h

/-- a number is not negative or its negative is not -/
theorem pos_total (p : Ed dd) : Pos F p ∨ Pos F (eneg (ofCR F) p) := by
  have eN : nrm (ofCR F) (eneg (ofCR F) p) = nrm (ofCR F) p := nrm_neg (ofCR F) p
  cases F.le_total F.zero (nrm (ofCR F) p) with
  | inl hN =>
    cases F.le_total F.zero p.a with
    | inl ha => exact Or.inl (Or.inl ⟨ha, hN⟩)
    | inr ha => exact Or.inr (Or.inl ⟨neg_nn F ha, eN.symm ▸ hN⟩)
  | inr hN =>
    cases F.le_total F.zero p.b with
    | inl hb => exact Or.inl (Or.inr ⟨hb, hN⟩)
    | inr hb => exact Or.inr (Or.inr ⟨neg_nn F hb, eN.symm ▸ hN⟩)

theorem half_nn {x : α} (h : F.le F.zero (F.add x x)) : F.le F.zero x :=
  F.le_of_double (by rw [F.add_zero]; exact h)
theorem half_np {x : α} (h : F.le (F.add x x) F.zero) : F.le x F.zero :=
  F.le_of_double (by rw [F.add_zero]; exact h)

theorem pos_half {d : Ed dd} (h : Pos F (eadd (ofCR F) d d)) : Pos F d := by
  have eN : nrm (ofCR F) (eadd (ofCR F) d d) =
      F.add (F.add (nrm (ofCR F) d) (nrm (ofCR F) d)) (F.add (nrm (ofCR F) d) (nrm (ofCR F) d)) := nrm_double (ofCR F) d
  cases h with
  | inl hA =>
    have ha : F.le F.zero (F.add d.a d.a) := hA.1
    exact Or.inl ⟨half_nn F ha, half_nn F (half_nn F (eN ▸ hA.2))⟩
  | inr hB =>
    have hb : F.le F.zero (F.add d.b d.b) := hB.1
    exact Or.inr ⟨half_nn F hb, half_np F (half_np F (eN ▸ hB.2))⟩

theorem zero_of_nrm_zero (nr : NoRoot F dd) {p : Ed dd} (e : nrm (ofCR F) p = F.zero) : p = ezero (dd := dd) (ofCR F) := by
  have e' : F.add (F.mul p.a p.a) (F.neg (F.mul dd (F.mul p.b p.b))) = F.zero := e
  have e2 := ZNet.eq_neg_of_add F e'
  rw [F.neg_neg] at e2
  have hb : p.b = F.zero := nr p.a p.b e2
  have ha : F.mul p.a p.a = F.zero := by rw [e2, hb, F.mul_zero, F.mul_zero]
  cases F.mul_eq_zero ha with
  | inl e3 => exact ext2 e3 hb
  | inr e3 => exact ext2 e3 hb

theorem emul_eq_zero (nr : NoRoot F dd) {p q : Ed dd} (h : emul (ofCR F) p q = ezero (dd := dd) (ofCR F)) :
    p = ezero (dd := dd) (ofCR F) ∨ q = ezero (dd := dd) (ofCR F) := by
  have h1 : F.add (F.mul p.a q.a) (F.mul dd (F.mul p.b q.b)) = F.zero := congrArg Ed.a h
  have h2 : F.add (F.mul p.a q.b) (F.mul p.b q.a) = F.zero := congrArg Ed.b h
  have k1 : F.mul (nrm (ofCR F) p) q.a =
      F.add (F.mul p.a (F.add (F.mul p.a q.a) (F.mul dd (F.mul p.b q.b))))
        (F.neg (F.mul (F.mul dd p.b) (F.add (F.mul p.a q.b) (F.mul p.b q.a)))) := idK (ofCR F) p.a p.b q.a q.b
  have k2 : F.mul (nrm (ofCR F) p) q.b =
      F.add (F.mul p.a (F.add (F.mul p.a q.b) (F.mul p.b q.a)))
        (F.neg (F.mul p.b (F.add (F.mul p.a q.a) (F.mul dd (F.mul p.b q.b))))) := idL (ofCR F) p.a p.b q.a q.b
  rw [h1, h2, F.mul_zero, F.mul_zero, ZNet.neg_zero, F.add_zero] at k1
  rw [h1, h2, F.mul_zero, F.mul_zero, ZNet.neg_zero, F.add_zero] at k2
  cases F.mul_eq_zero k1 with
  | inl e => exact Or.inl (zero_of_nrm_zero F nr e)
  | inr ea =>
    cases F.mul_eq_zero k2 with
    | inl e => exact Or.inl (zero_of_nrm_zero F nr e)
    | inr eb => exact Or.inr (ext2 ea eb)

/-! ### the absolute value (the order of the base field must be decidable) -/

variable (dle : ∀ x y : α, Decidable (F.le x y))

def posDec (p : Ed dd) : Decidable (Pos F p) :=
  @instDecidableOr _ _ (@instDecidableAnd _ _ (dle _ _) (dle _ _)) (@instDecidableAnd _ _ (dle _ _) (dle _ _))

def eabs (p : Ed dd) : Ed dd := @ite _ (Pos F p) (posDec F dle p) p (eneg (ofCR F) p)

theorem eabs_pos {p : Ed dd} (h : Pos F p) : eabs F dle p = p := @if_pos _ (posDec F dle p) h _ _ _
theorem eabs_npos {p : Ed dd} (h : ¬ Pos F p) : eabs F dle p = eneg (ofCR F) p := @if_neg _ (posDec F dle p) h _ _ _

theorem eneg_zero_of {p : Ed dd} (h : p.a = F.zero ∧ p.b = F.zero) : p = eneg (ofCR F) p :=
  ext2 (show p.a = F.neg p.a by rw [h.1, ZNet.neg_zero]) (show p.b = F.neg p.b by rw [h.2, ZNet.neg_zero])

/-- where the negative is not negative, the absolute value is the negative -/
theorem eabs_negpos (nr : NoRoot F dd) {p : Ed dd} (h : Pos F (eneg (ofCR F) p)) : eabs F dle p = eneg (ofCR F) p :=
  @Decidable.byCases _ _ (posDec F dle p)
    (fun hp => (eabs_pos F dle hp).trans (eneg_zero_of F (pos_antisymm F nr hp h)))
    (fun hp => eabs_npos F dle hp)

theorem pos_eabs (p : Ed dd) : Pos F (eabs F dle p) :=
  @Decidable.byCases _ _ (posDec F dle p)
    (fun hp => (eabs_pos F dle hp).symm ▸ hp)
    (fun hp => (eabs_npos F dle hp).symm ▸ (match pos_total F p with
      | Or.inl h => absurd h hp
      | Or.inr h => h))

theorem pos_negneg {p : Ed dd} (h : Pos F p) : Pos F (eneg (ofCR F) (eneg (ofCR F) p)) :=
  (ext2 (neg_neg_a (ofCR F) p) (neg_neg_b (ofCR F) p) : eneg (ofCR F) (eneg (ofCR F) p) = p).symm ▸ h

/-- a ≤ |a| -/
theorem le_eabs (nr : NoRoot F dd) (p : Ed dd) : Pos F (eadd (ofCR F) (eabs F dle p) (eneg (ofCR F) p)) :=
  match pos_total F p with
  | Or.inl h => (eabs_pos F dle h).symm ▸
      ((ext2 (add_neg_a (ofCR F) p) (add_neg_b (ofCR F) p) : eadd (ofCR F) p (eneg (ofCR F) p) = ezero (dd := dd) (ofCR F)).symm ▸ pos_zero F)
  | Or.inr h => (eabs_negpos F dle nr h).symm ▸ pos_add F nr h h

/-- −a ≤ |a| -/
theorem neg_le_eabs (nr : NoRoot F dd) (p : Ed dd) :
    Pos F (eadd (ofCR F) (eabs F dle p) (eneg (ofCR F) (eneg (ofCR F) p))) :=
  match pos_total F p with
  | Or.inl h => (eabs_pos F dle h).symm ▸ ((eqE (i_aa (ofCR F) p)).symm ▸ pos_add F nr h h)
  | Or.inr h => (eabs_negpos F dle nr h).symm ▸ ((eqE (i_nn0 (ofCR F) p)).symm ▸ pos_zero F)

/-- THE ORDERED FIELD F[√d]: a field of the kernel again -/
def extOF (nr : NoRoot F dd) : OF (Ed dd) where
  zero := ezero (dd := dd) (ofCR F)
  one := eone (dd := dd) (ofCR F)
  add := eadd (ofCR F)
  mul := emul (ofCR F)
  neg := eneg (ofCR F)
  le := ele F
  add_comm := fun p q => ext2 (add_comm_a (ofCR F) p q) (add_comm_b (ofCR F) p q)
  add_assoc := fun p q s => ext2 (add_assoc_a (ofCR F) p q s) (add_assoc_b (ofCR F) p q s)
  add_zero := fun p => ext2 (add_zero_a (ofCR F) p) (add_zero_b (ofCR F) p)
  add_neg := fun p => ext2 (add_neg_a (ofCR F) p) (add_neg_b (ofCR F) p)
  mul_comm := fun p q => ext2 (mul_comm_a (ofCR F) p q) (mul_comm_b (ofCR F) p q)
  mul_assoc := fun p q s => ext2 (mul_assoc_a (ofCR F) p q s) (mul_assoc_b (ofCR F) p q s)
  mul_one := fun p => ext2 (mul_one_a (ofCR F) p) (mul_one_b (ofCR F) p)
  mul_zero := fun p => ext2 (mul_zero_a (ofCR F) p) (mul_zero_b (ofCR F) p)
  mul_add := fun p q s => ext2 (mul_add_a (ofCR F) p q s) (mul_add_b (ofCR F) p q s)
  neg_mul := fun p q => ext2 (neg_mul_a (ofCR F) p q) (neg_mul_b (ofCR F) p q)
  neg_neg := fun p => ext2 (neg_neg_a (ofCR F) p) (neg_neg_b (ofCR F) p)
  le_refl := fun p =>
    pos_congr F (ext2 (add_neg_a (ofCR F) p) (add_neg_b (ofCR F) p) : eadd (ofCR F) p (eneg (ofCR F) p) = ezero (dd := dd) (ofCR F)).symm
      (pos_zero F)
  le_trans := fun {p q s} h1 h2 => pos_congr F (eqE (i_trans (ofCR F) p q s)) (pos_add F nr h2 h1)
  add_le_add := fun {a b c d} h1 h2 => pos_congr F (eqE (i_addle (ofCR F) a b c d)) (pos_add F nr h1 h2)
  mul_le_mul_left := fun {a b c} hc h => pos_congr F (eqE (i_mulle (ofCR F) c a b)) (pos_mul F nr (pos_of_zero_le F hc) h)
  mul_nonneg := fun {a b} ha hb => zero_le_of_pos F (pos_mul F nr (pos_of_zero_le F ha) (pos_of_zero_le F hb))
  sq_nonneg := fun p => zero_le_of_pos F (Or.inl
    ⟨nn_add F (F.sq_nonneg p.a) (d_sq_nonneg F p.b),
     F.le_trans (F.sq_nonneg (nrm (ofCR F) p)) (le_of_eq' F (nrm_mul (ofCR F) p p).symm)⟩)
  nonpos_mul := fun {a b} ha hb => by
    have h1 := pos_mul F nr (negpos_of_le_zero F ha) (pos_of_zero_le F hb)
    have e : emul (ofCR F) (eneg (ofCR F) a) b = eneg (ofCR F) (emul (ofCR F) a b) :=
      ext2 (neg_mul_a (ofCR F) a b) (neg_mul_b (ofCR F) a b)
    exact pos_congr F (eqE (i_0sub (ofCR F) (emul (ofCR F) a b))).symm (pos_congr F e h1)
  le_of_double := fun {a b} h => pos_half F (pos_congr F (eqE (i_addle (ofCR F) a b a b)).symm h)
  le_total := fun p q =>
    match pos_total F (eadd (ofCR F) q (eneg (ofCR F) p)) with
    | Or.inl h => Or.inl h
    | Or.inr h => Or.inr (pos_congr F (eqE (i_flip (ofCR F) p q)) h)
  le_antisymm := fun {p q} h1 h2 => by
    have h2' : Pos F (eneg (ofCR F) (eadd (ofCR F) q (eneg (ofCR F) p))) := pos_congr F (eqE (i_flip (ofCR F) p q)).symm h2
    have z := pos_antisymm F nr h1 h2'
    have za : F.add q.a (F.neg p.a) = F.zero := z.1
    have zb : F.add q.b (F.neg p.b) = F.zero := z.2
    have ea := ZNet.eq_neg_of_add F za
    have eb := ZNet.eq_neg_of_add F zb
    rw [F.neg_neg] at ea eb
    exact ext2 ea.symm eb.symm
  mul_eq_zero := fun h => emul_eq_zero F nr h
  abs := eabs F dle
  abs_mul := fun a b =>
    match pos_total F a, pos_total F b with
    | Or.inl ha, Or.inl hb => by
        rw [eabs_pos F dle ha, eabs_pos F dle hb, eabs_pos F dle (pos_mul F nr ha hb)]
    | Or.inl ha, Or.inr hb => by
        have e : emul (ofCR F) a (eneg (ofCR F) b) = eneg (ofCR F) (emul (ofCR F) a b) := eqE (i_mulneg (ofCR F) a b)
        rw [eabs_pos F dle ha, eabs_negpos F dle nr hb, eabs_negpos F dle nr (e ▸ pos_mul F nr ha hb), e]
    | Or.inr ha, Or.inl hb => by
        have e : emul (ofCR F) (eneg (ofCR F) a) b = eneg (ofCR F) (emul (ofCR F) a b) :=
          ext2 (neg_mul_a (ofCR F) a b) (neg_mul_b (ofCR F) a b)
        rw [eabs_negpos F dle nr ha, eabs_pos F dle hb, eabs_negpos F dle nr (e ▸ pos_mul F nr ha hb), e]
    | Or.inr ha, Or.inr hb => by
        have e : emul (ofCR F) (eneg (ofCR F) a) (eneg (ofCR F) b) = emul (ofCR F) a b := eqE (i_negnegmul (ofCR F) a b)
        rw [eabs_negpos F dle nr ha, eabs_negpos F dle nr hb, eabs_pos F dle (e ▸ pos_mul F nr ha hb), e]
  abs_add := fun a b =>
    match pos_total F (eadd (ofCR F) a b) with
    | Or.inl h => by
        show Pos F (eadd (ofCR F) (eadd (ofCR F) (eabs F dle a) (eabs F dle b)) (eneg (ofCR F) (eabs F dle (eadd (ofCR F) a b))))
        rw [eabs_pos F dle h]
        exact eqE (i_addle (ofCR F) a (eabs F dle a) b (eabs F dle b)) ▸ pos_add F nr (le_eabs F dle nr a) (le_eabs F dle nr b)
    | Or.inr h => by
        show Pos F (eadd (ofCR F) (eadd (ofCR F) (eabs F dle a) (eabs F dle b)) (eneg (ofCR F) (eabs F dle (eadd (ofCR F) a b))))
        rw [eabs_negpos F dle nr h]
        exact eqE (i_abs2 (ofCR F) (eabs F dle a) (eabs F dle b) a b) ▸ pos_add F nr (neg_le_eabs F dle nr a) (neg_le_eabs F dle nr b)
  abs_zero := eabs_pos F dle (pos_zero F)
  abs_nonneg := fun p => zero_le_of_pos F (pos_eabs F dle p)
  abs_of_nonneg := fun {p} h => eabs_pos F dle (pos_of_zero_le F h)
  abs_neg := fun p =>
    match pos_total F p with
    | Or.inl h => by
        rw [eabs_pos F dle h, eabs_negpos F dle nr (pos_negneg F h)]
        exact ext2 (neg_neg_a (ofCR F) p) (neg_neg_b (ofCR F) p)
    | Or.inr h => by
        rw [eabs_pos F dle h, eabs_negpos F dle nr h]

/-! ### the inverse, the test for zero, the minimum and the maximum -/

variable (I : QZ12.Inv F)

/-- (a + b√d)⁻¹ = (a − b√d)/N -/
def einv (p : Ed dd) : Ed dd := ⟨F.mul p.a (I.inv (nrm (ofCR F) p)), F.mul (F.neg p.b) (I.inv (nrm (ofCR F) p))⟩

theorem emul_inv (nr : NoRoot F dd) {p : Ed dd} (h : p ≠ ezero (dd := dd) (ofCR F)) : emul (ofCR F) p (einv F I p) = eone (dd := dd) (ofCR F) := by
  have hn : nrm (ofCR F) p ≠ F.zero := fun e => h (zero_of_nrm_zero F nr e)
  have hu : F.mul (nrm (ofCR F) p) (I.inv (nrm (ofCR F) p)) = F.one := I.mul_inv hn
  exact ext2 ((ofCR F).trans (invA (ofCR F) p.a p.b (I.inv (nrm (ofCR F) p))) hu)
    (invB (ofCR F) p.a p.b (I.inv (nrm (ofCR F) p)))

def edec (p : Ed dd) : Decidable (p = ezero (dd := dd) (ofCR F)) :=
  match I.dec p.a with
  | isFalse ha => isFalse (fun e => ha (congrArg Ed.a e))
  | isTrue ha =>
    match I.dec p.b with
    | isFalse hb => isFalse (fun e => hb (congrArg Ed.b e))
    | isTrue hb => isTrue (ext2 ha hb)

/-- the extension has the inverse and the test for zero that Gram–Schmidt (QZ12) asks for -/
def extInv (nr : NoRoot F dd) : QZ12.Inv (extOF F dle nr) :=
  ⟨einv F I, fun {_} h => emul_inv F I nr h, edec F I⟩

def emn (p q : Ed dd) : Ed dd := @ite _ (ele F p q) (posDec F dle _) p q
def emx (p q : Ed dd) : Ed dd := @ite _ (ele F p q) (posDec F dle _) q p

/-- …and the minimum and the maximum that QZ8's scale asks for -/
def extMinMax (nr : NoRoot F dd) : QZ8.MinMax (extOF F dle nr) where
  mn := emn F dle
  mx := emx F dle
  le_mn := fun {_ x y} h1 h2 =>
    @Decidable.byCases _ _ (posDec F dle (eadd (ofCR F) y (eneg (ofCR F) x)))
      (fun h => (show emn F dle x y = x from @if_pos _ (posDec F dle _) h _ _ _).symm ▸ h1)
      (fun h => (show emn F dle x y = y from @if_neg _ (posDec F dle _) h _ _ _).symm ▸ h2)
  mx_le := fun {_ x y} h1 h2 =>
    @Decidable.byCases _ _ (posDec F dle (eadd (ofCR F) y (eneg (ofCR F) x)))
      (fun h => (show emx F dle x y = y from @if_pos _ (posDec F dle _) h _ _ _).symm ▸ h2)
      (fun h => (show emx F dle x y = x from @if_neg _ (posDec F dle _) h _ _ _).symm ▸ h1)

end QZ19

#print axioms QZ19.mul_assoc_a
#print axioms QZ19.nrm_mul
#print axioms QZ19.nrm_add
#print axioms QZ19.le_of_sq_le
#print axioms QZ19.nn_add_of_sq
#print axioms QZ19.posA_add
#print axioms QZ19.posB_add
#print axioms QZ19.pos_antisymm
#print axioms QZ19.pos_add
#print axioms QZ19.pos_mul
#print axioms QZ19.emul_eq_zero
#print axioms QZ19.extOF
#print axioms QZ19.extInv
#print axioms QZ19.extMinMax
