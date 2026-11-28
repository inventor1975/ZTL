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
import QOF

/-!
# QZ13 — QZ12 over real numbers: the lattice of projections of Q^n, computed. Zero axioms.

(2026-11-28. Written with AI. The numbers are Logik2's `QOF.qOF`.)

  `qInv`            the rationals have the inverse and the test for zero QZ12 asks for
  `qProj`, `qLat`   the lattice of all symmetric projections of the rational n×n matrices, for any index list
  `qBorn`           the Born weight of any rational state vector is a probability of layer 3 on it - UNCONDITIONAL
  `qSplits`         a state splits along a question there exactly when the projections commute
  `join_ab`, `join_3`   the Gram–Schmidt join COMPUTES in the kernel: in the qubit a ∨ b = 1 (as QZ3's table says);
                    in dimension 3 the rays of (1,0,0) and (1,1,0) join to diag(1,1,0)
-/

namespace QZ13
open ZNet ZRound QZ3 QZ7 QZ8 QZ9 QZ10 QZ12 QOF

/-- the rationals: the inverse and the test for zero -/
def qInv : Inv qOF := ⟨cinv, cmul_inv, fun a => decEqC a qOF.zero⟩

/-- the symmetric projections of the rational matrices over an index list -/
abbrev qProj (l : List Nat) (hn : NoDup l) : Type := Proj qOF l hn

/-- their lattice -/
def qLat (l : List Nat) (hn : NoDup l) : NLat (qProj l hn) := projLat qOF qInv l hn

/-- THE BORN WEIGHT OF ANY RATIONAL STATE VECTOR IS A PROBABILITY OF LAYER 3 ON THE LATTICE OF ALL PROJECTIONS -/
def qBorn (l : List Nat) (hn : NoDup l) (ψ : Vec QC) :
    QZ5.Prob (qLat l hn) (scale qOF QZ11.mmQ (qf qOF l (matOne qOF) ψ)) :=
  born_prob_all qOF qInv l hn QZ11.mmQ ψ

/-- A STATE SPLITS ALONG A QUESTION EXACTLY WHEN THE PROJECTIONS COMMUTE -/
theorem qSplits (l : List Nat) (hn : NoDup l) (s a : qProj l hn) :
    (qLat l hn).le s ((qLat l hn).join ((qLat l hn).meet s a) ((qLat l hn).meet s ((qLat l hn).neg a)))
      ↔ Comm (matAlg qOF l hn) s.1 a.1 :=
  splits_iff_comm qOF qInv l hn s a

/-- THE JOIN COMPUTES: in the qubit, a ∨ b is the whole space -/
theorem join_ab : QZ11.Eq4 (QZ12.join qOF qInv QZ11.l2 (QZ11.emb .a) (QZ11.emb .b)) (matOne qOF) := by decide +kernel

/-- …and a ∨ ¬a too, while a ∨ a is a -/
theorem join_aa : QZ11.Eq4 (QZ12.join qOF qInv QZ11.l2 (QZ11.emb .a) (QZ11.emb .a')) (matOne qOF) ∧
    QZ11.Eq4 (QZ12.join qOF qInv QZ11.l2 (QZ11.emb .a) (QZ11.emb .a)) (QZ11.emb .a) := by decide +kernel

/-- dimension 3 -/
def l3 : List Nat := [0, 1, 2]
def e1 : Vec QC := fun i => if i = 0 then qOF.one else qOF.zero
def v110 : Vec QC := fun i => if i = 2 then qOF.zero else qOF.one
def d110 : Mat QC := fun i j => if i = j then (if i = 2 then qOF.zero else qOF.one) else qOF.zero

/-- the rays of (1,0,0) and (1,1,0) join to diag(1,1,0): the nine entries, computed -/
theorem join_3 :
    let J := QZ12.join qOF qInv l3 (ray qOF qOF.one e1) (ray qOF QZ11.half v110)
    J 0 0 = d110 0 0 ∧ J 0 1 = d110 0 1 ∧ J 0 2 = d110 0 2 ∧ J 1 0 = d110 1 0 ∧ J 1 1 = d110 1 1 ∧ J 1 2 = d110 1 2 ∧
    J 2 0 = d110 2 0 ∧ J 2 1 = d110 2 1 ∧ J 2 2 = d110 2 2 := by decide +kernel

end QZ13

#print axioms QZ13.qInv
#print axioms QZ13.qLat
#print axioms QZ13.qBorn
#print axioms QZ13.qSplits
#print axioms QZ13.join_ab
#print axioms QZ13.join_aa
#print axioms QZ13.join_3
