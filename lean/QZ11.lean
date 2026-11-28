import ZNet
import ZRound
import QZ3
import QZ4
import QZ5
import QZ7
import QZ8
import QZ9
import QZ10
import QOF

/-!
# QZ11 — the qubit over REAL NUMBERS: the theorems of QZ7–QZ10 with nothing left conditional. Zero axioms.

(2026-11-28, the curator: "работай далее". Written with AI. The numbers are Logik2's `QOF.qOF` - the kernel's ordered
field built on the empty axiom list, computing: the rationals in canonical form.)

Until now `born_prob` (QZ8) was proved for ANY ordered field and ANY lattice of symmetric projections, and no field
and no such lattice of real matrices had been exhibited. Here both are:

  the field       `qOF` (rational numbers, exact)
  the lattice     the qubit's six questions (QZ3.mo2) as real symmetric 2×2 matrices:
                  a = diag(1, 0), ¬a = diag(0, 1), b = ½[[1, 1], [1, 1]], ¬b = ½[[1, −1], [−1, 1]], 0, 1
  `realQubit`     they ARE a lattice of projections of the matrices (QZ7 `Rep`): order, negation, sums - every law
                  checked by the kernel's own evaluation of the matrix products
  `realProb`      so the Born weight of ANY state vector ψ is a probability of layer 3 on it (QZ8 `born_prob`)
  `born_values`   and for ψ = (1, 0) it is QZ5's own table: a sure, ¬a impossible, b and ¬b one half
  `tilted_*`      for ψ = (1, 2) (not normalised: ψᵀψ = 5): a 1, ¬a 4, b 9/2, ¬b 1/2 - each pair sums to 5
  `real_closed`, `real_splits`, `real_no_split`   QZ9 on it: a and b do not commute, b does not split along a
  `b_is_ray`      b is the ray of (1, 1) with c = ½ (QZ10)

What is still NOT proved in general: that every subspace of any dimension has such a projection and that they form
such a lattice (Gram–Schmidt). This file is one lattice, of one qubit, with everything computed.
-/

namespace QZ11
open ZNet ZRound QZ3 QZ7 QZ8 QOF

/-- the two indices -/
def l2 : List Nat := [0, 1]

theorem nd2 : NoDup l2 := by
  refine ⟨?_, ?_, True.intro⟩
  · intro h
    cases h with
    | tail _ h' => nomatch h'
  · intro h
    nomatch h

theorem mem0 : List.Mem 0 l2 := List.Mem.head _
theorem mem1 : List.Mem 1 l2 := List.Mem.tail _ (List.Mem.head _)

/-- a 2×2 matrix from its four entries (other indices read as the last row / column: they are never looked at) -/
def m2 (a b c d : QC) : Mat QC := fun i j => if i = 0 then (if j = 0 then a else b) else (if j = 0 then c else d)

/-- equal in the four entries -/
def Eq4 (M N : Mat QC) : Prop := M 0 0 = N 0 0 ∧ M 0 1 = N 0 1 ∧ M 1 0 = N 1 0 ∧ M 1 1 = N 1 1
instance (M N : Mat QC) : Decidable (Eq4 M N) :=
  inferInstanceAs (Decidable (M 0 0 = N 0 0 ∧ M 0 1 = N 0 1 ∧ M 1 0 = N 1 0 ∧ M 1 1 = N 1 1))

theorem of4 {M N : Mat QC} (h : Eq4 M N) : meq l2 M N := by
  intro i j hi hj
  cases hi with
  | head =>
    cases hj with
    | head => exact h.1
    | tail _ hj' =>
      cases hj' with
      | head => exact h.2.1
      | tail _ k => nomatch k
  | tail _ hi' =>
    cases hi' with
    | head =>
      cases hj with
      | head => exact h.2.2.1
      | tail _ hj' =>
        cases hj' with
        | head => exact h.2.2.2
        | tail _ k => nomatch k
    | tail _ k => nomatch k

theorem to4 {M N : Mat QC} (h : meq l2 M N) : Eq4 M N :=
  ⟨h 0 0 mem0 mem0, h 0 1 mem0 mem1, h 1 0 mem1 mem0, h 1 1 mem1 mem1⟩

def half : QC := frac 1 false 1
def mhalf : QC := frac 1 true 1

/-- the qubit's six questions as real symmetric matrices -/
def emb : Q → Mat QC
  | .bot => m2 qOF.zero qOF.zero qOF.zero qOF.zero
  | .top => m2 qOF.one qOF.zero qOF.zero qOF.one
  | .a => m2 qOF.one qOF.zero qOF.zero qOF.zero
  | .a' => m2 qOF.zero qOF.zero qOF.zero qOF.one
  | .b => m2 half half half half
  | .b' => m2 half mhalf mhalf half

theorem emb_isP : ∀ x : Q, Eq4 (matMul qOF l2 (emb x) (emb x)) (emb x) := by decide +kernel
theorem emb_le_to : ∀ x y : Q, qle x y →
    Eq4 (matMul qOF l2 (emb x) (emb y)) (emb x) ∧ Eq4 (matMul qOF l2 (emb y) (emb x)) (emb x) := by decide +kernel
theorem emb_le_of : ∀ x y : Q,
    Eq4 (matMul qOF l2 (emb x) (emb y)) (emb x) ∧ Eq4 (matMul qOF l2 (emb y) (emb x)) (emb x) → qle x y := by decide +kernel
theorem emb_neg : ∀ x : Q, Eq4 (emb (qneg x)) (matSub qOF (matOne qOF) (emb x)) := by decide +kernel
theorem emb_top : Eq4 (emb .top) (matOne qOF) := by decide +kernel
theorem emb_bot : Eq4 (emb .bot) (matZero qOF) := by decide +kernel
theorem emb_sum : ∀ x y : Q,
    Eq4 (matMul qOF l2 (emb x) (emb y)) (matZero qOF) ∧ Eq4 (matMul qOF l2 (emb y) (emb x)) (matZero qOF) →
    Eq4 (emb (qjoin x y)) (matAdd qOF (emb x) (emb y)) := by decide +kernel
theorem emb_sym01 : ∀ x : Q, emb x 0 1 = emb x 1 0 := by decide +kernel

/-- THE QUBIT'S LATTICE IS A LATTICE OF PROJECTIONS OF THE REAL 2×2 MATRICES -/
def realQubit : Rep (matAlg qOF l2 nd2) mo2 where
  e := emb
  isP := fun x => of4 (emb_isP x)
  le_to := fun {x y} h => ⟨of4 (emb_le_to x y h).1, of4 (emb_le_to x y h).2⟩
  le_of := fun {x y} h => emb_le_of x y ⟨to4 h.1, to4 h.2⟩
  neg := fun x => of4 (emb_neg x)
  top := of4 emb_top
  bot := of4 emb_bot
  sum := fun x y h => ⟨qjoin x y, of4 (emb_sum x y ⟨to4 h.1, to4 h.2⟩)⟩

theorem emb_sym (x : Q) : sym l2 (emb x) := by
  intro i j hi hj
  cases hi with
  | head =>
    cases hj with
    | head => rfl
    | tail _ hj' =>
      cases hj' with
      | head => exact emb_sym01 x
      | tail _ k => nomatch k
  | tail _ hi' =>
    cases hi' with
    | head =>
      cases hj with
      | head => exact (emb_sym01 x).symm
      | tail _ hj' =>
        cases hj' with
        | head => rfl
        | tail _ k => nomatch k
    | tail _ k => nomatch k

/-- the minimum and the maximum of the rationals (QOF) -/
def mmQ : MinMax qOF := ⟨cmn, cmx, QOF.le_mn, QOF.mx_le⟩

/-- THE BORN WEIGHT OF ANY STATE VECTOR IS A PROBABILITY OF LAYER 3 ON THE QUBIT - nothing conditional left -/
def realProb (ψ : Nat → QC) : QZ5.Prob mo2 (scale qOF mmQ (qf qOF l2 (matOne qOF) ψ)) :=
  born_prob qOF l2 nd2 mmQ ψ realQubit emb_sym

/-- the state in which a is sure: ψ = (1, 0) -/
def psiA : Nat → QC := fun i => if i = 0 then qOF.one else qOF.zero

/-- 0, 1/2, 1 of QZ5 as numbers -/
def num : QZ5.H → QC
  | .o => qOF.zero | .h => half | .i => qOF.one

/-- FOR ψ = (1, 0) THE BORN WEIGHT IS QZ5'S TABLE, computed from the matrices: ψᵀPψ, question by question -/
theorem born_values : ∀ x : Q, qf qOF l2 (emb x) psiA = num (QZ5.born x) := by decide +kernel

/-- a tilted, not normalised state: ψ = (1, 2), ψᵀψ = 5 -/
def psiT : Nat → QC := fun i => if i = 0 then qOF.one else frac 2 false 0

theorem tilted_one : qf qOF l2 (matOne qOF) psiT = frac 5 false 0 := by decide +kernel
theorem tilted_a : qf qOF l2 (emb .a) psiT = frac 1 false 0 ∧ qf qOF l2 (emb .a') psiT = frac 4 false 0 := by decide +kernel
theorem tilted_b : qf qOF l2 (emb .b) psiT = frac 9 false 1 ∧ qf qOF l2 (emb .b') psiT = frac 1 false 1 := by decide +kernel

/-! ### QZ9 and QZ10 on it -/

theorem emb_prod : ∀ x y : Q, Eq4 (matMul qOF l2 (emb x) (emb y)) (matMul qOF l2 (emb y) (emb x)) →
    Eq4 (emb (qmeet x y)) (matMul qOF l2 (emb x) (emb y)) := by decide +kernel

theorem real_closed : QZ9.Closed realQubit := fun x y h => ⟨qmeet x y, of4 (emb_prod x y (to4 h))⟩

theorem ab_do_not_commute : ¬ Eq4 (matMul qOF l2 (emb .b) (emb .a)) (matMul qOF l2 (emb .a) (emb .b)) := by decide +kernel

/-- the top splits along a… -/
theorem real_splits : mo2.le Q.top (mo2.join (mo2.meet Q.top Q.a) (mo2.meet Q.top (mo2.neg Q.a))) :=
  QZ9.comm_split (QZ9.mat_assoc qOF l2 nd2) realQubit real_closed Q.top Q.a
    (of4 (by decide +kernel : Eq4 (matMul qOF l2 (emb .top) (emb .a)) (matMul qOF l2 (emb .a) (emb .top))))

/-- …and b does not split along a, because over the real numbers their projections do not commute -/
theorem real_no_split : ¬ mo2.le Q.b (mo2.join (mo2.meet Q.b Q.a) (mo2.meet Q.b (mo2.neg Q.a))) :=
  fun h => ab_do_not_commute (to4 (QZ9.split_comm realQubit Q.b Q.a h))

/-- b is the ray of the vector (1, 1), with c = 1/2 (QZ10) -/
theorem b_is_ray : Eq4 (emb .b) (QZ10.ray qOF half (fun _ => qOF.one)) := by decide +kernel

end QZ11

#print axioms QZ11.realQubit
#print axioms QZ11.realProb
#print axioms QZ11.born_values
#print axioms QZ11.tilted_one
#print axioms QZ11.tilted_a
#print axioms QZ11.tilted_b
#print axioms QZ11.real_closed
#print axioms QZ11.real_splits
#print axioms QZ11.real_no_split
#print axioms QZ11.b_is_ray
