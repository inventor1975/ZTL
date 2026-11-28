import ZNet
import ZRound
import QZ3
import QZ5
import QZ7
import QZ8
import QZ9
import QZ10
import QZ11
import QZ12
import QZ13
import QZ15
import QOF
import Sqrt2

/-!
# QZ16 — Q(√2): the numbers a + b·√2 with a, b rational, as an ordered field of the kernel; CHSH computed. Zero axioms.

(2026-11-28. Written with AI. The rationals `QOF.qOF` and the irrationality of √2 `Sqrt2.no_sqrt2` are Logik2's.)

  `r2`              Q(√2) = QZ15's extension of the rationals: an ordered field of the kernel, not trivial (`r2_nontrivial`)
  `r2Inv`, `r2mm`   with inverse, test for zero, min and max; equality is decidable (`decE2`)
  `r2Lat`, `r2Born` hence QZ12 over it: the lattice of ALL symmetric projections with entries in Q(√2), every dimension,
                    and the Born weight a probability of layer 3 on it
  `sq2`             √2·√2 = 2, computed
  `chsh_*`          CHSH at its optimal directions (tan(π/8) = −1 + √2), state (1, 0, 0, 1), ψᵀψ = 2: the weight of
                    "the outcomes agree" is 1 + ½√2 for three pairs of directions and 1 − ½√2 for the fourth; each
                    such event is a projection (`chsh_proj`: the sum of the rays of two orthogonal vectors, QZ10)
  `chsh_S`          so S·ψᵀψ = 4√2, i.e. S = 2√2 - above the classical 2 (`chsh_above`: 2·2 ≤ 4√2 and not the other way)

The judge (qz_judge.py, class R2) computed the same numbers in Python; here the kernel does, on the kernel's field.
-/

namespace QZ16
open ZNet ZRound QZ3 QZ7 QZ8 QZ9 QZ10 QZ12 QZ15 QOF

/-- the order of the rationals is decidable -/
def dleQ : ∀ x y : QC, Decidable (qOF.le x y) := fun x y => VR.Numbers.qle.decidable x.1 y.1

/-- two has no root among the rationals (Logik2) -/
theorem nrQ : NoRoot2 qOF := Sqrt2.no_sqrt2

/-- Q(√2) -/
def r2 : OF (E2 QC) := ext2OF qOF dleQ nrQ

instance decE2 : DecidableEq (E2 QC) := fun p q =>
  match decEqC p.a q.a with
  | isFalse h => isFalse (fun e => h (congrArg E2.a e))
  | isTrue ha =>
    match decEqC p.b q.b with
    | isFalse h => isFalse (fun e => h (congrArg E2.b e))
    | isTrue hb => isTrue (ext2 ha hb)

theorem r2_nontrivial : r2.zero ≠ r2.one := fun e => qOF_nontrivial (congrArg E2.a e)

def r2Inv : Inv r2 := ext2Inv qOF dleQ QZ13.qInv nrQ
def r2mm : MinMax r2 := ext2MinMax qOF dleQ nrQ

/-- the lattice of all symmetric projections over Q(√2) -/
def r2Lat (l : List Nat) (hn : NoDup l) : NLat (Proj r2 l hn) := projLat r2 r2Inv l hn

/-- THE BORN WEIGHT OVER Q(√2) IS A PROBABILITY OF LAYER 3, in every dimension -/
def r2Born (l : List Nat) (hn : NoDup l) (ψ : Vec (E2 QC)) :
    QZ5.Prob (r2Lat l hn) (scale r2 r2mm (qf r2 l (matOne r2) ψ)) :=
  born_prob_all r2 r2Inv l hn r2mm ψ

/-! ### numbers -/

def q (k : Nat) (neg : Bool) (d : Nat) : QC := frac k neg d
/-- a rational as a number of Q(√2) -/
def rat (x : QC) : E2 QC := ⟨x, qOF.zero⟩
/-- √2 -/
def root2 : E2 QC := ⟨qOF.zero, qOF.one⟩
/-- 2 -/
def two2 : E2 QC := rat (q 2 false 0)

/-- √2·√2 = 2 -/
theorem sq2 : r2.mul root2 root2 = two2 := by decide +kernel

/-! ### CHSH -/

def l4 : List Nat := [0, 1, 2, 3]
def v4 (a b c d : E2 QC) : Vec (E2 QC) := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d
def z : E2 QC := r2.zero
def u : E2 QC := r2.one
/-- tan(π/8) = −1 + √2 -/
def t8 : E2 QC := ⟨q 1 true 0, qOF.one⟩
def nt8 : E2 QC := r2.neg t8
/-- the state (|00⟩ + |11⟩), not normalised -/
def phi : Vec (E2 QC) := v4 u z z u

/-- "the outcomes agree", as the sum of the rays of two orthogonal vectors with the inverses of their squared lengths -/
def agree (c1 : E2 QC) (w1 : Vec (E2 QC)) (c2 : E2 QC) (w2 : Vec (E2 QC)) : Mat (E2 QC) :=
  matAdd r2 (ray r2 c1 w1) (ray r2 c2 w2)

/-- 1/(1 + t²) = ½ + ¼√2 -/
def c8 : E2 QC := ⟨q 1 false 1, q 1 false 3⟩
def chalf : E2 QC := rat (q 1 false 1)
def cquarter : E2 QC := rat (q 1 false 3)

/-- the four events: Alice at 0 or π/2, Bob at π/4 or −π/4 (half-angle vectors, as in the judge's test) -/
def Pab : Mat (E2 QC) := agree c8 (v4 u t8 z z) c8 (v4 z z nt8 u)
def Pab' : Mat (E2 QC) := agree c8 (v4 u nt8 z z) c8 (v4 z z t8 u)
def Pa'b : Mat (E2 QC) := agree (r2.mul chalf c8) (v4 u t8 u t8) (r2.mul chalf c8) (v4 t8 (r2.neg u) nt8 u)
def Pa'b' : Mat (E2 QC) := agree (r2.mul chalf c8) (v4 u nt8 u nt8) (r2.mul chalf c8) (v4 nt8 (r2.neg u) t8 u)

/-- 1 + ½√2 and 1 − ½√2 -/
def wHi : E2 QC := ⟨qOF.one, q 1 false 1⟩
def wLo : E2 QC := ⟨qOF.one, q 1 true 1⟩

theorem chsh_norm : qf r2 l4 (matOne r2) phi = two2 := by decide +kernel
theorem chsh_ab : qf r2 l4 Pab phi = wHi := by decide +kernel
theorem chsh_ab' : qf r2 l4 Pab' phi = wHi := by decide +kernel
theorem chsh_a'b : qf r2 l4 Pa'b phi = wHi := by decide +kernel
theorem chsh_a'b' : qf r2 l4 Pa'b' phi = wLo := by decide +kernel

theorem mem_cons_inv {a b : Nat} {l : List Nat} (h : List.Mem a (b :: l)) : a = b ∨ List.Mem a l := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h' => exact Or.inr h'

theorem not_mem_nil {a : Nat} (h : List.Mem a []) : False := nomatch h

theorem not_mem_cons {a b : Nat} {l : List Nat} (hne : a ≠ b) (hl : ¬ List.Mem a l) : ¬ List.Mem a (b :: l) := fun h =>
  match mem_cons_inv h with
  | Or.inl e => hne e
  | Or.inr h' => hl h'

theorem nd4 : NoDup l4 :=
  ⟨not_mem_cons (by decide) (not_mem_cons (by decide) (not_mem_cons (by decide) not_mem_nil)),
   not_mem_cons (by decide) (not_mem_cons (by decide) not_mem_nil),
   not_mem_cons (by decide) not_mem_nil,
   not_mem_nil, True.intro⟩

/-- the constants are the inverses of the squared lengths… -/
theorem chsh_units :
    r2.mul c8 (ip r2 l4 (v4 u t8 z z) (v4 u t8 z z)) = r2.one ∧ r2.mul c8 (ip r2 l4 (v4 z z nt8 u) (v4 z z nt8 u)) = r2.one ∧
    r2.mul c8 (ip r2 l4 (v4 u nt8 z z) (v4 u nt8 z z)) = r2.one ∧ r2.mul c8 (ip r2 l4 (v4 z z t8 u) (v4 z z t8 u)) = r2.one ∧
    r2.mul (r2.mul chalf c8) (ip r2 l4 (v4 u t8 u t8) (v4 u t8 u t8)) = r2.one ∧
    r2.mul (r2.mul chalf c8) (ip r2 l4 (v4 t8 (r2.neg u) nt8 u) (v4 t8 (r2.neg u) nt8 u)) = r2.one ∧
    r2.mul (r2.mul chalf c8) (ip r2 l4 (v4 u nt8 u nt8) (v4 u nt8 u nt8)) = r2.one ∧
    r2.mul (r2.mul chalf c8) (ip r2 l4 (v4 nt8 (r2.neg u) t8 u) (v4 nt8 (r2.neg u) t8 u)) = r2.one := by decide +kernel

/-- …and the two vectors of each event are orthogonal -/
theorem chsh_orth :
    ip r2 l4 (v4 u t8 z z) (v4 z z nt8 u) = r2.zero ∧ ip r2 l4 (v4 u nt8 z z) (v4 z z t8 u) = r2.zero ∧
    ip r2 l4 (v4 u t8 u t8) (v4 t8 (r2.neg u) nt8 u) = r2.zero ∧
    ip r2 l4 (v4 u nt8 u nt8) (v4 nt8 (r2.neg u) t8 u) = r2.zero := by decide +kernel

/-- SO THE FOUR EVENTS ARE PROJECTIONS (QZ10: the sum of the rays of two orthogonal vectors) -/
theorem chsh_proj : IsP (matAlg r2 l4 nd4) Pab ∧ IsP (matAlg r2 l4 nd4) Pab' ∧ IsP (matAlg r2 l4 nd4) Pa'b ∧
    IsP (matAlg r2 l4 nd4) Pa'b' :=
  ⟨frame2_isP r2 l4 nd4 _ _ _ _ chsh_units.1 chsh_units.2.1 chsh_orth.1,
   frame2_isP r2 l4 nd4 _ _ _ _ chsh_units.2.2.1 chsh_units.2.2.2.1 chsh_orth.2.1,
   frame2_isP r2 l4 nd4 _ _ _ _ chsh_units.2.2.2.2.1 chsh_units.2.2.2.2.2.1 chsh_orth.2.2.1,
   frame2_isP r2 l4 nd4 _ _ _ _ chsh_units.2.2.2.2.2.2.1 chsh_units.2.2.2.2.2.2.2 chsh_orth.2.2.2⟩

/-- the correlation times ψᵀψ: (agree) − (differ) = 2w − ψᵀψ -/
def corr (w : E2 QC) : E2 QC := r2.add (r2.add w w) (r2.neg two2)

/-- S·ψᵀψ = 4√2: S = 2√2 -/
theorem chsh_S : r2.add (r2.add (corr wHi) (corr wHi)) (r2.add (corr wHi) (r2.neg (corr wLo))) = ⟨qOF.zero, q 4 false 0⟩ := by
  decide +kernel

/-- above the classical bound: 2·ψᵀψ = 4 ≤ 4√2, and not 4√2 ≤ 4 -/
theorem chsh_above : r2.le (rat (q 4 false 0)) ⟨qOF.zero, q 4 false 0⟩ ∧ ¬ r2.le ⟨qOF.zero, q 4 false 0⟩ (rat (q 4 false 0)) := by
  refine ⟨?_, ?_⟩
  · exact @of_decide_eq_true _ (posDec qOF dleQ _) (by decide +kernel)
  · exact @of_decide_eq_false _ (posDec qOF dleQ _) (by decide +kernel)

end QZ16

#print axioms QZ16.r2
#print axioms QZ16.r2_nontrivial
#print axioms QZ16.r2Born
#print axioms QZ16.sq2
#print axioms QZ16.chsh_norm
#print axioms QZ16.chsh_ab
#print axioms QZ16.chsh_a'b
#print axioms QZ16.chsh_a'b'
#print axioms QZ16.chsh_S
#print axioms QZ16.chsh_above
#print axioms QZ16.chsh_proj
#print axioms QZ16.nd4
#print axioms QZ16.chsh_units
#print axioms QZ16.chsh_orth
