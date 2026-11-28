import QZ8
import QZ10
import QZ12
import QZ13
import QOF
import QZCtxS

/-!
# QZCtxKS18C — two rays of the 18-vector set do not commute, so the judge must withdraw. Zero axioms.

(2026-11-28, Logik2; twin of Q/CtxKS18Comm.agda. Written with AI.) Rays (0,0,0,1) and (1,1,1,1) — rays 0 and 17 of
calib/ks18_set.py — as projections over the canonical rationals: entry (3,0) of P₀P₁₇ is 1/4, of P₁₇P₀ it is 0. By
QZCtxS.no_split_of', the full space does not split along them (`ks18_no_split`): T2's last tail, for this set.
-/

namespace QZCtxKS18C
open QZ3 QZ4 QZ7 QZ8 QZ9 QZ10 QZ12 QZ13 QOF QZCtxS

def l4 : List Nat := [0, 1, 2, 3]

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

def v0 : Nat → QC := fun i => if i = 3 then qOF.one else qOF.zero
def v17 : Nat → QC := fun _ => qOF.one
/-- 1/4 = 1/⟨v17, v17⟩ -/
def c17 : QC := frac 1 false 3

theorem u0 : qOF.mul qOF.one (ip qOF l4 v0 v0) = qOF.one := by decide +kernel
theorem u17 : qOF.mul c17 (ip qOF l4 v17 v17) = qOF.one := by decide +kernel

def r0 : Proj qOF l4 nd4 := ⟨ray qOF qOF.one v0, ⟨ray_sym qOF l4 _ _, ray_isP qOF l4 nd4 _ _ u0⟩⟩
def r17 : Proj qOF l4 nd4 := ⟨ray qOF c17 v17, ⟨ray_sym qOF l4 _ _, ray_isP qOF l4 nd4 _ _ u17⟩⟩

theorem e30 : matMul qOF l4 (ray qOF qOF.one v0) (ray qOF c17 v17) 3 0 ≠ matMul qOF l4 (ray qOF c17 v17) (ray qOF qOF.one v0) 3 0 := by
  decide +kernel

/-- THE TWO PROJECTIONS DO NOT COMMUTE (entry (3,0): 1/4 against 0) -/
theorem no_comm : ¬ Comm (matAlg qOF l4 nd4) (ray qOF qOF.one v0) (ray qOF c17 v17) := fun h =>
  e30 (h 3 0 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _))

/-- THE FULL SPACE DOES NOT SPLIT ALONG THE TWO RAYS: the stable verdict on the KS formula must be withdrawn -/
theorem ks18_no_split : ¬ Splits (projLat qOF qInv l4 nd4) (projLat qOF qInv l4 nd4).top [r0, r17] :=
  no_split_of' (projRep qOF qInv l4 nd4) r0 r17 _ _ rfl rfl no_comm

end QZCtxKS18C

#print axioms QZCtxKS18C.no_comm
#print axioms QZCtxKS18C.ks18_no_split
