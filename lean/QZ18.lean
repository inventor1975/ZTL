import ZNet
import ZRound
import QZ7
import QZ8
import QZ9
import QZ10
import QZ12
import QZ13
import QZ14
import QZ15
import QZ17
import VR.Meta.CSRNorm

/-!
# QZ18 — certificates: the QZ judge's lattice verdict, re-checked by the kernel from cheap integer checks. Zero axioms.

(2026-11-28, the curator on the judge's implementation: "все на нем держится, он должен быть точным". Written with AI.)

The lattice of QZ12 is computed by Gram–Schmidt, which the kernel cannot run on real documents (each entry of the
result unfolds the whole computation again). A program can: the judge (qz_judge.py) computes the projections, and
qz_cert.py writes them down with witnesses. This file says what the kernel has to CHECK about matrices handed to it,
by matrix products alone, to know they are the lattice's own values - and then what the verdict is.

1. What makes a matrix the lattice's value (any ordered field of the kernel with an inverse):
  `join_cert`    J symmetric projection, A ≤ J, B ≤ J, and J = A·U + B·V for some U, V   →   J is the join of A and B
  `meet_cert`    the same for the complements                                             →   M is the meet of A and B
  `projOf_cert`  P symmetric projection, P holds every vector of the list, and P = Σ_t v_t·w_tᵀ for some w_t
                                                                                          →   P is the projection of the list
  `pauli_cert`   P symmetric projection and P + P = 1 + M   →   (1 + M)·P = P + P: P is the projection on the +1
                 eigenvectors of M
U, V and the w_t are WITNESSES: the program finds them (a linear system), the kernel only multiplies.

2. The claim as a formula: `Fm` (¬, ∧, ∨, →, xor, ↔, nand, nor over atoms that carry their projections), `val` its
value in the lattice `QZ12.projLat`, `Is M X` (the literal M is the value X), and one lemma per connective
(`is_neg`, `is_join`, `is_meet`), so that a certificate ends in ONE statement about the formula:
`verdict_le` / `verdict_not_le`:  val Know ≤ val Claim, or not.

3. Integer data. A certificate's numbers are rationals over one common denominator d; a matrix N of integers stands
for `lit d N` = (1/d)·N. Every check is an identity of integer matrices, decided by the kernel's arithmetic on
naturals (`goodB`, `leB`, `joinB`, `meetB`, `negB`, `topB`, `pauliB`, `spanB`), and carried to the field:
`is_zatom`, `is_ztop`, `is_zneg`, `is_zjoin`, `is_zmeet`, `verdict_z`, `verdict_not_z`, `pauli_z`, `span_z`.
Needed of the field: 1 ≠ 0 (then no natural number but 0 is zero - `nat_succ_ne` - and different integers are
different numbers, `zi_inj`: the "not ≤" of an undetermined verdict rests on it).

Not here: the probability (Born weight of a certificate), the stable reading, amplitudes outside the rationals.
-/

namespace QZ18
open ZNet ZRound QZ7 QZ8 QZ9 QZ10 QZ12 QZ14

variable {α : Type} (F : OF α) (I : Inv F) (l : List Nat) (hn : NoDup l)

include hn in
/-- THE JOIN, CERTIFIED: an upper bound of A and B whose columns are combinations of theirs is the least one -/
theorem join_cert {A B J U V : Mat α} (GA : Good F l hn A) (GB : Good F l hn B) (GJ : Good F l hn J)
    (hA : Le (matAlg F l hn) A J) (hB : Le (matAlg F l hn) B J)
    (hc : meq l J (matAdd F (matMul F l A U) (matMul F l B V))) : meq l J (join F I l A B) := by
  have R := matAlg F l hn
  have hAs := mat_assoc F l hn
  have h1 : Le (matAlg F l hn) (join F I l A B) J := join_le F I l hn GJ hA hB
  have la := le_join_l F I l hn (Q := B) GA
  have lb := le_join_r F I l hn GA GB
  -- Jn·J = Jn·(A·U + B·V) = (Jn·A)·U + (Jn·B)·V = A·U + B·V = J
  have e : meq l (matMul F l (join F I l A B) J) J :=
    (matAlg F l hn).trans ((matAlg F l hn).mul_congr ((matAlg F l hn).refl _) hc)
      ((matAlg F l hn).trans ((matAlg F l hn).mul_add _ _ _)
        ((matAlg F l hn).trans
          ((matAlg F l hn).add_congr
            ((matAlg F l hn).trans ((matAlg F l hn).symm (hAs _ A U)) ((matAlg F l hn).mul_congr la.2 ((matAlg F l hn).refl U)))
            ((matAlg F l hn).trans ((matAlg F l hn).symm (hAs _ B V)) ((matAlg F l hn).mul_congr lb.2 ((matAlg F l hn).refl V))))
          ((matAlg F l hn).symm hc)))
  -- and Jn·J = Jn because Jn ≤ J
  exact (matAlg F l hn).symm ((matAlg F l hn).trans ((matAlg F l hn).symm h1.1) e)

include hn in
/-- THE MEET, CERTIFIED: through the complements -/
theorem meet_cert {A B M U V : Mat α} (GA : Good F l hn A) (GB : Good F l hn B) (GM : Good F l hn M)
    (hA : Le (matAlg F l hn) (matSub F (matOne F) A) (matSub F (matOne F) M))
    (hB : Le (matAlg F l hn) (matSub F (matOne F) B) (matSub F (matOne F) M))
    (hc : meq l (matSub F (matOne F) M)
      (matAdd F (matMul F l (matSub F (matOne F) A) U) (matMul F l (matSub F (matOne F) B) V))) :
    meq l M (matSub F (matOne F) (join F I l (matSub F (matOne F) A) (matSub F (matOne F) B))) := by
  have j := join_cert F I l hn (good_ng F l hn GA) (good_ng F l hn GB) (good_ng F l hn GM) hA hB hc
  exact (matAlg F l hn).trans ((matAlg F l hn).symm (mat_ng_ng F l M))
    ((matAlg F l hn).sub_congr ((matAlg F l hn).refl _) j)

/-- Σ_t v_t(i)·w_t(j): the matrix whose columns are combinations of the vectors v_t -/
def comb : List (Vec α × Vec α) → Mat α
  | [] => matZero F
  | vw :: ps => fun i j => F.add (F.mul (vw.1 i) (vw.2 j)) (comb ps i j)

/-- the matrix holds the first vector of every pair -/
def FixedFst (M : Mat α) : List (Vec α × Vec α) → Prop
  | [] => True
  | vw :: ps => veq l (mv F l M vw.1) vw.1 ∧ FixedFst M ps

/-- a matrix that holds the vectors holds their combinations: M·comb = comb -/
theorem mul_comb {M : Mat α} : ∀ ps, FixedFst F l M ps → meq l (matMul F l M (comb F ps)) (comb F ps)
  | [], _ => fun i j _ _ => S_all_zero F l (fun k _ => F.mul_zero (M i k))
  | vw :: ps, h => fun i j hi hj => by
      show S F l (fun k => F.mul (M i k) (F.add (F.mul (vw.1 k) (vw.2 j)) (comb F ps k j))) =
        F.add (F.mul (vw.1 i) (vw.2 j)) (comb F ps i j)
      have e1 : S F l (fun k => F.mul (M i k) (F.add (F.mul (vw.1 k) (vw.2 j)) (comb F ps k j))) =
          F.add (S F l (fun k => F.mul (F.mul (M i k) (vw.1 k)) (vw.2 j))) (S F l (fun k => F.mul (M i k) (comb F ps k j))) := by
        rw [← S_add F _ _ l]
        exact S_congr F l (fun k _ => by
          show F.mul (M i k) (F.add (F.mul (vw.1 k) (vw.2 j)) (comb F ps k j)) =
            F.add (F.mul (F.mul (M i k) (vw.1 k)) (vw.2 j)) (F.mul (M i k) (comb F ps k j))
          rw [F.mul_add, F.mul_assoc])
      have e2 : S F l (fun k => F.mul (F.mul (M i k) (vw.1 k)) (vw.2 j)) = F.mul (vw.1 i) (vw.2 j) := by
        rw [S_mul_right F (vw.2 j) (fun k => F.mul (M i k) (vw.1 k)) l]
        have hv : S F l (fun k => F.mul (M i k) (vw.1 k)) = vw.1 i := h.1 i hi
        rw [hv]
      have e3 : S F l (fun k => F.mul (M i k) (comb F ps k j)) = comb F ps i j := mul_comb ps h.2 i j hi hj
      rw [e1, e2, e3]

def fsts : List (Vec α × Vec α) → List (Vec α)
  | [] => []
  | vw :: ps => vw.1 :: fsts ps

theorem allFixed_fsts {M : Mat α} : ∀ ps, FixedFst F l M ps → AllFixed F l M (fsts ps)
  | [], _ => True.intro
  | _ :: ps, h => ⟨h.1, allFixed_fsts ps h.2⟩

theorem fixedFst_of {M : Mat α} : ∀ ps, AllFixed F l M (fsts ps) → FixedFst F l M ps
  | [], _ => True.intro
  | _ :: ps, h => ⟨h.1, fixedFst_of ps h.2⟩

include hn in
/-- THE PROJECTION OF A SPANNING LIST, CERTIFIED -/
theorem projOf_cert {P : Mat α} (ps : List (Vec α × Vec α)) (GP : Good F l hn P) (hf : FixedFst F l P ps)
    (hc : meq l P (comb F ps)) : meq l P (projOf F I l (fsts ps)) := by
  have h1 : Le (matAlg F l hn) (projOf F I l (fsts ps)) P :=
    projOf_least F I l hn GP (fsts ps) (allFixed_fsts F l ps hf)
  have hfix : FixedFst F l (projOf F I l (fsts ps)) ps := fixedFst_of F l ps (projOf_fixes F I l hn (fsts ps))
  have e : meq l (matMul F l (projOf F I l (fsts ps)) P) P :=
    (matAlg F l hn).trans ((matAlg F l hn).mul_congr ((matAlg F l hn).refl _) hc)
      ((matAlg F l hn).trans (mul_comb F l ps hfix) ((matAlg F l hn).symm hc))
  exact (matAlg F l hn).symm ((matAlg F l hn).trans ((matAlg F l hn).symm h1.1) e)

include hn in
/-- A PAULI QUESTION, CERTIFIED: P a projection with P + P = 1 + M is the projection on the +1 eigenvectors of M:
M·P = P (and so M·(1 − P) = −(1 − P)) -/
theorem pauli_cert {P M : Mat α} (GP : Good F l hn P) (h : meq l (matAdd F P P) (matAdd F (matOne F) M)) :
    meq l (matMul F l (matAdd F (matOne F) M) P) (matAdd F P P) :=
  -- (1 + M)·P = (P + P)·P = P·P + P·P = P + P
  (matAlg F l hn).trans ((matAlg F l hn).mul_congr ((matAlg F l hn).symm h) ((matAlg F l hn).refl P))
    ((matAlg F l hn).trans ((matAlg F l hn).add_mul P P P) ((matAlg F l hn).add_congr GP.pr GP.pr))

/-! ### the claim as a FORMULA, and its value in the lattice of QZ12

The judge reads a claim through ¬, ∧, ∨ and what is written through them. `val` is that reading in the lattice of all
symmetric projections (`QZ12.projLat`: 1 − P, the join by Gram–Schmidt, the meet through it). `Is M X` says the
literal matrix M handed to the kernel is the value X, both symmetric projections. The lemmas below let a certificate
climb the formula one connective at a time, so that the last theorem is about the formula itself. -/

/-- the claims the judge reads; an atom carries the projection of its question -/
inductive Fm (α : Type) where
  | top : Fm α
  | atom : Mat α → Fm α
  | neg : Fm α → Fm α
  | and : Fm α → Fm α → Fm α
  | or : Fm α → Fm α → Fm α
  | imp : Fm α → Fm α → Fm α
  | xor : Fm α → Fm α → Fm α
  | xnor : Fm α → Fm α → Fm α
  | nand : Fm α → Fm α → Fm α
  | nor : Fm α → Fm α → Fm α

/-- 1 − P -/
def mng (P : Mat α) : Mat α := matSub F (matOne F) P
/-- the lattice's meet (QZ12.projLat) -/
def mmeet (P Q : Mat α) : Mat α := mng F (join F I l (mng F P) (mng F Q))

/-- THE VALUE of a formula in the lattice of projections: the judge's reading (qz_judge.Lattice.value) -/
def val : Fm α → Mat α
  | .top => matOne F
  | .atom M => M
  | .neg f => mng F (val f)
  | .and f g => mmeet F I l (val f) (val g)
  | .or f g => join F I l (val f) (val g)
  | .imp f g => join F I l (mng F (val f)) (val g)
  | .xor f g => join F I l (mmeet F I l (val f) (mng F (val g))) (mmeet F I l (mng F (val f)) (val g))
  | .xnor f g => join F I l (mmeet F I l (val f) (val g)) (mmeet F I l (mng F (val f)) (mng F (val g)))
  | .nand f g => mng F (mmeet F I l (val f) (val g))
  | .nor f g => mng F (join F I l (val f) (val g))

/-- the literal matrix M is the value X; both are symmetric projections -/
structure Is (M X : Mat α) : Prop where
  eq : meq l M X
  gM : Good F l hn M
  gX : Good F l hn X

theorem is_atom {M : Mat α} (G : Good F l hn M) : Is F l hn M M := ⟨(matAlg F l hn).refl M, G, G⟩

theorem is_top {M : Mat α} (G : Good F l hn M) (e : meq l M (matOne F)) : Is F l hn M (matOne F) :=
  ⟨e, G, good_one F l hn⟩

theorem is_neg {M N X : Mat α} (a : Is F l hn M X) (G : Good F l hn N) (e : meq l N (mng F M)) :
    Is F l hn N (mng F X) :=
  ⟨(matAlg F l hn).trans e ((matAlg F l hn).sub_congr ((matAlg F l hn).refl _) a.eq), G, good_ng F l hn a.gX⟩

theorem is_join {A B J U V X Y : Mat α} (a : Is F l hn A X) (b : Is F l hn B Y) (GJ : Good F l hn J)
    (hA : Le (matAlg F l hn) A J) (hB : Le (matAlg F l hn) B J)
    (hc : meq l J (matAdd F (matMul F l A U) (matMul F l B V))) : Is F l hn J (join F I l X Y) :=
  ⟨join_cert F I l hn a.gX b.gX GJ
      (le_congr (matAlg F l hn) a.eq ((matAlg F l hn).refl J) hA)
      (le_congr (matAlg F l hn) b.eq ((matAlg F l hn).refl J) hB)
      ((matAlg F l hn).trans hc ((matAlg F l hn).add_congr
        ((matAlg F l hn).mul_congr a.eq ((matAlg F l hn).refl U))
        ((matAlg F l hn).mul_congr b.eq ((matAlg F l hn).refl V)))),
   GJ, join_good F I l hn a.gX⟩

theorem is_meet {A B M U V X Y : Mat α} (a : Is F l hn A X) (b : Is F l hn B Y) (GM : Good F l hn M)
    (hA : Le (matAlg F l hn) (mng F A) (mng F M)) (hB : Le (matAlg F l hn) (mng F B) (mng F M))
    (hc : meq l (mng F M) (matAdd F (matMul F l (mng F A) U) (matMul F l (mng F B) V))) :
    Is F l hn M (mmeet F I l X Y) := by
  have an := is_neg F l hn a (good_ng F l hn a.gM) ((matAlg F l hn).refl _)
  have bn := is_neg F l hn b (good_ng F l hn b.gM) ((matAlg F l hn).refl _)
  have j := is_join F I l hn an bn (good_ng F l hn GM) hA hB hc
  exact ⟨(matAlg F l hn).trans ((matAlg F l hn).symm (mat_ng_ng F l M))
      ((matAlg F l hn).sub_congr ((matAlg F l hn).refl _) j.eq), GM, good_ng F l hn j.gX⟩

/-- THE VERDICT, from the literals to the values -/
theorem verdict_le {K M KX X : Mat α} (k : Is F l hn K KX) (x : Is F l hn M X) (h : Le (matAlg F l hn) K M) :
    Le (matAlg F l hn) KX X := le_congr (matAlg F l hn) k.eq x.eq h

theorem verdict_not_le {K M KX X : Mat α} (k : Is F l hn K KX) (x : Is F l hn M X) (h : ¬ Le (matAlg F l hn) K M) :
    ¬ Le (matAlg F l hn) KX X := fun hl =>
  h (le_congr (matAlg F l hn) ((matAlg F l hn).symm k.eq) ((matAlg F l hn).symm x.eq) hl)

/-! ### INTEGER DATA: the checks are made on integers, the statement is about the field

A certificate's numbers are rationals with one common denominator d. The matrix handed to the kernel is a matrix N of
integers (a pair (p, n) of naturals stands for p − n), and it stands for `lit d N` = (1/d)·N over ANY ordered field of
the kernel with an inverse in which 1 ≠ 0. A product of such matrices is checked as an identity of integer matrices -
the kernel's own fast arithmetic on naturals - and the lemmas below carry it to the field. (The kernel's rationals,
QOF, normalise by search: fractions like 9/25 do not come back. MEASURED 2026-11-28: one such certificate, 62 s and
14 GB before it was stopped.) -/

section Ring
variable (R : VR.CSR.CR α)
theorem r1 (a b c e : α) : R.r (R.add (R.add a (R.neg b)) (R.add c (R.neg e))) (R.add (R.add a c) (R.neg (R.add b e))) := by cr_ring R
theorem r2 (a b c e : α) : R.r (R.mul (R.add a (R.neg b)) (R.add c (R.neg e)))
    (R.add (R.add (R.mul a c) (R.mul b e)) (R.neg (R.add (R.mul a e) (R.mul b c)))) := by cr_ring R
theorem r3a (a b e : α) : R.r (R.add a (R.neg b)) (R.add (R.add a e) (R.add (R.neg b) (R.neg e))) := by cr_ring R
theorem r3b (c b e : α) : R.r (R.add (R.add c b) (R.add (R.neg b) (R.neg e))) (R.add c (R.neg e)) := by cr_ring R
theorem r3c (a b e : α) : R.r (R.add a e) (R.add (R.add a (R.neg b)) (R.add b e)) := by cr_ring R
theorem r3d (c b e : α) : R.r (R.add (R.add c (R.neg e)) (R.add b e)) (R.add c b) := by cr_ring R
theorem r4 (s a b : α) : R.r (R.mul (R.mul s a) (R.mul s b)) (R.mul (R.mul s s) (R.mul a b)) := by cr_ring R
theorem r5 (s c k : α) : R.r (R.mul (R.mul s s) (R.mul c k)) (R.mul (R.mul s c) (R.mul s k)) := by cr_ring R
theorem r6 (a b c e : α) : R.r (R.add (R.add a e) (R.neg (R.add b c))) (R.add (R.add a (R.neg b)) (R.neg (R.add c (R.neg e)))) := by cr_ring R
theorem r7 (s a b : α) : R.r (R.add (R.mul s a) (R.neg (R.mul s b))) (R.mul s (R.add a (R.neg b))) := by cr_ring R
theorem r8a (s c z : α) : R.r (R.mul c (R.mul c (R.mul (R.mul s s) z))) (R.mul (R.mul s c) (R.mul (R.mul s c) z)) := by cr_ring R
theorem r8b (s c k : α) : R.r (R.mul c (R.mul c (R.mul s k))) (R.mul (R.mul s c) (R.mul c k)) := by cr_ring R
theorem r10 (s v w x : α) : R.r (R.add (R.mul v (R.mul s w)) (R.mul s x)) (R.mul s (R.add (R.mul v w) x)) := by cr_ring R
end Ring

theorem i1 (a b c e : α) : F.add (F.add a (F.neg b)) (F.add c (F.neg e)) = F.add (F.add a c) (F.neg (F.add b e)) := r1 (QZ15.ofCR F) a b c e
theorem i2 (a b c e : α) : F.mul (F.add a (F.neg b)) (F.add c (F.neg e)) =
    F.add (F.add (F.mul a c) (F.mul b e)) (F.neg (F.add (F.mul a e) (F.mul b c))) := r2 (QZ15.ofCR F) a b c e
theorem i3a (a b e : α) : F.add a (F.neg b) = F.add (F.add a e) (F.add (F.neg b) (F.neg e)) := r3a (QZ15.ofCR F) a b e
theorem i3b (c b e : α) : F.add (F.add c b) (F.add (F.neg b) (F.neg e)) = F.add c (F.neg e) := r3b (QZ15.ofCR F) c b e
theorem i3c (a b e : α) : F.add a e = F.add (F.add a (F.neg b)) (F.add b e) := r3c (QZ15.ofCR F) a b e
theorem i3d (c b e : α) : F.add (F.add c (F.neg e)) (F.add b e) = F.add c b := r3d (QZ15.ofCR F) c b e
theorem i4 (s a b : α) : F.mul (F.mul s a) (F.mul s b) = F.mul (F.mul s s) (F.mul a b) := r4 (QZ15.ofCR F) s a b
theorem i5 (s c k : α) : F.mul (F.mul s s) (F.mul c k) = F.mul (F.mul s c) (F.mul s k) := r5 (QZ15.ofCR F) s c k
theorem i6 (a b c e : α) : F.add (F.add a e) (F.neg (F.add b c)) = F.add (F.add a (F.neg b)) (F.neg (F.add c (F.neg e))) := r6 (QZ15.ofCR F) a b c e
theorem i7 (s a b : α) : F.add (F.mul s a) (F.neg (F.mul s b)) = F.mul s (F.add a (F.neg b)) := r7 (QZ15.ofCR F) s a b
theorem i8a (s c z : α) : F.mul c (F.mul c (F.mul (F.mul s s) z)) = F.mul (F.mul s c) (F.mul (F.mul s c) z) := r8a (QZ15.ofCR F) s c z
theorem i8b (s c k : α) : F.mul c (F.mul c (F.mul s k)) = F.mul (F.mul s c) (F.mul c k) := r8b (QZ15.ofCR F) s c k
theorem i10 (s v w x : α) : F.add (F.mul v (F.mul s w)) (F.mul s x) = F.mul s (F.add (F.mul v w) x) := r10 (QZ15.ofCR F) s v w x

/-- an integer: the pair (p, n) stands for p − n -/
abbrev Z2 := Nat × Nat
abbrev ZM := Nat → Nat → Z2
abbrev ZV := Nat → Z2

/-- the n-th member of a list, or the default -/
def nthD {β : Type} (dflt : β) : List β → Nat → β
  | [], _ => dflt
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nthD dflt xs n
/-- an integer matrix written by its rows -/
def rows (r : List (List Z2)) : ZM := fun i j => nthD (0, 0) (nthD [] r i) j
/-- an integer vector written by its entries -/
def ents (r : List Z2) : ZV := fun i => nthD (0, 0) r i

/-- a natural number in the field: 1 + … + 1 -/
def nat : Nat → α
  | 0 => F.zero
  | n + 1 => F.add (nat n) F.one

theorem nat_add (a : Nat) : ∀ b, nat F (a + b) = F.add (nat F a) (nat F b)
  | 0 => (F.add_zero _).symm
  | b + 1 => by
      show F.add (nat F (a + b)) F.one = F.add (nat F a) (F.add (nat F b) F.one)
      rw [nat_add a b, F.add_assoc]

theorem nat_mul (a : Nat) : ∀ b, nat F (a * b) = F.mul (nat F a) (nat F b)
  | 0 => (F.mul_zero _).symm
  | b + 1 => by
      show nat F (a * b + a) = F.mul (nat F a) (F.add (nat F b) F.one)
      rw [nat_add, nat_mul a b, F.mul_add, F.mul_one]

theorem zero_le_one : F.le F.zero F.one := by
  have h := F.sq_nonneg F.one
  rw [F.mul_one] at h
  exact h

theorem nat_nonneg : ∀ n, F.le F.zero (nat F n)
  | 0 => F.le_refl _
  | n + 1 => by
      have h := F.add_le_add (nat_nonneg n) (zero_le_one F)
      rw [F.add_zero] at h
      exact h

/-- where 1 ≠ 0, no successor is zero (the field has characteristic 0: it is ordered) -/
theorem nat_succ_ne (h1 : F.one ≠ F.zero) (n : Nat) : nat F (n + 1) ≠ F.zero := fun h => by
  have h2 := F.add_le_add (nat_nonneg F n) (F.le_refl F.one)
  rw [ZNet.zero_add] at h2
  have h3 : F.le F.one F.zero := by
    have h' : F.add (nat F n) F.one = F.zero := h
    rw [h'] at h2
    exact h2
  exact h1 (F.le_antisymm h3 (zero_le_one F))

theorem nat_ne_zero (h1 : F.one ≠ F.zero) : ∀ d, d ≠ 0 → nat F d ≠ F.zero
  | 0, h => absurd rfl h
  | n + 1, _ => nat_succ_ne F h1 n

theorem add_one_cancel {x y : α} (h : F.add x F.one = F.add y F.one) : x = y := by
  have ex : F.add (F.add x F.one) (F.neg F.one) = x := by rw [F.add_assoc, F.add_neg, F.add_zero]
  have ey : F.add (F.add y F.one) (F.neg F.one) = y := by rw [F.add_assoc, F.add_neg, F.add_zero]
  rw [← ex, h, ey]

theorem nat_inj (h1 : F.one ≠ F.zero) : ∀ a b, nat F a = nat F b → a = b
  | 0, 0, _ => rfl
  | 0, b + 1, h => absurd h.symm (nat_succ_ne F h1 b)
  | a + 1, 0, h => absurd h (nat_succ_ne F h1 a)
  | a + 1, b + 1, h => congrArg Nat.succ (nat_inj h1 a b (add_one_cancel F h))

/-- the integer in the field -/
def zi (x : Z2) : α := F.add (nat F x.1) (F.neg (nat F x.2))
def zadd (x y : Z2) : Z2 := (x.1 + y.1, x.2 + y.2)
def zsub (x y : Z2) : Z2 := (x.1 + y.2, x.2 + y.1)
def zmul (x y : Z2) : Z2 := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def zsc (d : Nat) (x : Z2) : Z2 := (d * x.1, d * x.2)
/-- the same integer -/
def zeq (x y : Z2) : Prop := x.1 + y.2 = y.1 + x.2

theorem zi_zero : zi F (0, 0) = F.zero := F.add_neg F.zero

theorem zi_add (x y : Z2) : zi F (zadd x y) = F.add (zi F x) (zi F y) := by
  show F.add (nat F (x.1 + y.1)) (F.neg (nat F (x.2 + y.2))) = _
  rw [nat_add, nat_add]
  exact (i1 F _ _ _ _).symm

theorem zi_sub (x y : Z2) : zi F (zsub x y) = F.add (zi F x) (F.neg (zi F y)) := by
  show F.add (nat F (x.1 + y.2)) (F.neg (nat F (x.2 + y.1))) = _
  rw [nat_add, nat_add]
  exact i6 F _ _ _ _

theorem zi_mul (x y : Z2) : zi F (zmul x y) = F.mul (zi F x) (zi F y) := by
  show F.add (nat F (x.1 * y.1 + x.2 * y.2)) (F.neg (nat F (x.1 * y.2 + x.2 * y.1))) = _
  rw [nat_add, nat_add, nat_mul, nat_mul, nat_mul, nat_mul]
  exact (i2 F _ _ _ _).symm

theorem zi_sc (d : Nat) (x : Z2) : zi F (zsc d x) = F.mul (nat F d) (zi F x) := by
  show F.add (nat F (d * x.1)) (F.neg (nat F (d * x.2))) = _
  rw [nat_mul, nat_mul]
  exact i7 F _ _ _

theorem zi_congr {x y : Z2} (h : zeq x y) : zi F x = zi F y := by
  have h' : F.add (nat F x.1) (nat F y.2) = F.add (nat F y.1) (nat F x.2) := by
    rw [← nat_add, ← nat_add]
    exact congrArg (nat F) h
  show F.add (nat F x.1) (F.neg (nat F x.2)) = F.add (nat F y.1) (F.neg (nat F y.2))
  rw [i3a F (nat F x.1) (nat F x.2) (nat F y.2), h', i3b]

/-- in a field where 1 ≠ 0, different integers are different numbers -/
theorem zi_inj (h1 : F.one ≠ F.zero) {x y : Z2} (h : zi F x = zi F y) : zeq x y := by
  have h' : F.add (nat F x.1) (F.neg (nat F x.2)) = F.add (nat F y.1) (F.neg (nat F y.2)) := h
  have e : F.add (nat F x.1) (nat F y.2) = F.add (nat F y.1) (nat F x.2) := by
    rw [i3c F (nat F x.1) (nat F x.2) (nat F y.2), h', i3d]
  rw [← nat_add, ← nat_add] at e
  exact nat_inj F h1 _ _ e

/-! #### integer matrices and what they stand for -/

def zS : List Nat → (Nat → Z2) → Z2
  | [], _ => (0, 0)
  | k :: l, f => zadd (f k) (zS l f)

theorem zi_S (f : Nat → Z2) : ∀ l, zi F (zS l f) = S F l (fun k => zi F (f k))
  | [] => zi_zero F
  | k :: l => by
      show zi F (zadd (f k) (zS l f)) = F.add (zi F (f k)) (S F l (fun k => zi F (f k)))
      rw [zi_add, zi_S f l]

def zmm (l : List Nat) (A B : ZM) : ZM := fun i j => zS l (fun k => zmul (A i k) (B k j))
def zmv (l : List Nat) (A : ZM) (v : ZV) : ZV := fun i => zS l (fun k => zmul (A i k) (v k))
def zaddM (A B : ZM) : ZM := fun i j => zadd (A i j) (B i j)
def zscM (d : Nat) (A : ZM) : ZM := fun i j => zsc d (A i j)
/-- d times the identity -/
def zone (d : Nat) : ZM := fun i j => if i = j then (d, 0) else (0, 0)
/-- d·1 − A: the complement of (1/d)·A, times d -/
def zcomp (d : Nat) (A : ZM) : ZM := fun i j => zsub (zone d i j) (A i j)
def ztr (A : ZM) : ZM := fun i j => A j i
def ZEq (l : List Nat) (A B : ZM) : Prop := ∀ i j, List.Mem i l → List.Mem j l → zeq (A i j) (B i j)

/-- 1/d -/
def sc (d : Nat) : α := I.inv (nat F d)
/-- THE MATRIX A CERTIFICATE NAMES: (1/d)·N -/
def lit (d : Nat) (N : ZM) : Mat α := fun i j => F.mul (sc F I d) (zi F (N i j))
def lit2 (d : Nat) (N : ZM) : Mat α := fun i j => F.mul (F.mul (sc F I d) (sc F I d)) (zi F (N i j))
/-- an integer matrix as it is (an observable) -/
def zmat (N : ZM) : Mat α := fun i j => zi F (N i j)
/-- an integer vector as it is (a vector of the document, cleared of denominators) -/
def zvec (v : ZV) : Vec α := fun i => zi F (v i)
def svec (d : Nat) (v : ZV) : Vec α := fun i => F.mul (sc F I d) (zi F (v i))

variable (d : Nat) (hd : nat F d ≠ F.zero)

include hd in
theorem sc_mul : F.mul (sc F I d) (nat F d) = F.one := by
  rw [F.mul_comm]
  exact I.mul_inv hd

theorem mul_lit (A B : ZM) : meq l (matMul F l (lit F I d A) (lit F I d B)) (lit2 F I d (zmm l A B)) := fun i j _ _ => by
  show S F l (fun k => F.mul (F.mul (sc F I d) (zi F (A i k))) (F.mul (sc F I d) (zi F (B k j)))) =
    F.mul (F.mul (sc F I d) (sc F I d)) (zi F (zS l (fun k => zmul (A i k) (B k j))))
  rw [zi_S, ← S_mul F (F.mul (sc F I d) (sc F I d)) (fun k => zi F (zmul (A i k) (B k j))) l]
  exact S_congr F l (fun k _ => by
    show F.mul (F.mul (sc F I d) (zi F (A i k))) (F.mul (sc F I d) (zi F (B k j))) =
      F.mul (F.mul (sc F I d) (sc F I d)) (zi F (zmul (A i k) (B k j)))
    rw [zi_mul]
    exact i4 F _ _ _)

include hd in
theorem lit2_eq {X C : ZM} (h : ZEq l X (zscM d C)) : meq l (lit2 F I d X) (lit F I d C) := fun i j hi hj => by
  have h' : zeq (X i j) (zsc d (C i j)) := h i j hi hj
  show F.mul (F.mul (sc F I d) (sc F I d)) (zi F (X i j)) = F.mul (sc F I d) (zi F (C i j))
  rw [zi_congr F h', zi_sc, i5, sc_mul F I d hd, ZRound.one_mul]

include hd in
/-- A PRODUCT, CHECKED ON INTEGERS: N_A·N_B = d·N_C gives A·B = C -/
theorem lit_mul_eq {A B C : ZM} (h : ZEq l (zmm l A B) (zscM d C)) :
    meq l (matMul F l (lit F I d A) (lit F I d B)) (lit F I d C) := fun i j hi hj =>
  (mul_lit F I l d A B i j hi hj).trans (lit2_eq F I l d hd h i j hi hj)

include hd in
/-- THE WITNESS EQUATION, CHECKED ON INTEGERS: d·N_J = N_A·N_U + N_B·N_V gives J = A·U + B·V -/
theorem lit_wit {A B J U V : ZM} (h : ZEq l (zscM d J) (zaddM (zmm l A U) (zmm l B V))) :
    meq l (lit F I d J) (matAdd F (matMul F l (lit F I d A) (lit F I d U)) (matMul F l (lit F I d B) (lit F I d V))) :=
  fun i j hi hj => by
    have h' : zeq (zsc d (J i j)) (zadd (zmm l A U i j) (zmm l B V i j)) := h i j hi hj
    have e1 : matMul F l (lit F I d A) (lit F I d U) i j = F.mul (F.mul (sc F I d) (sc F I d)) (zi F (zmm l A U i j)) :=
      mul_lit F I l d A U i j hi hj
    have e2 : matMul F l (lit F I d B) (lit F I d V) i j = F.mul (F.mul (sc F I d) (sc F I d)) (zi F (zmm l B V i j)) :=
      mul_lit F I l d B V i j hi hj
    show F.mul (sc F I d) (zi F (J i j)) =
      F.add (matMul F l (lit F I d A) (lit F I d U) i j) (matMul F l (lit F I d B) (lit F I d V) i j)
    rw [e1, e2, ← F.mul_add, ← zi_add, ← zi_congr F h', zi_sc, i5, sc_mul F I d hd, ZRound.one_mul]

theorem lit_congr {N N' : ZM} (h : ZEq l N N') : meq l (lit F I d N) (lit F I d N') := fun i j hi hj =>
  congrArg (F.mul (sc F I d)) (zi_congr F (h i j hi hj))

theorem zi_d0 (k : Nat) : zi F (k, 0) = nat F k := by
  show F.add (nat F k) (F.neg F.zero) = nat F k
  rw [ZNet.neg_zero, F.add_zero]

include hd in
theorem sc_zone (i j : Nat) : F.mul (sc F I d) (zi F (zone d i j)) = matOne F i j := by
  show F.mul (sc F I d) (zi F (if i = j then (d, 0) else (0, 0))) = (if i = j then F.one else F.zero)
  match Nat.decEq i j with
  | isTrue h => rw [if_pos h, if_pos h, zi_d0, sc_mul F I d hd]
  | isFalse h => rw [if_neg h, if_neg h, zi_zero, F.mul_zero]

theorem zi_zone1 (i j : Nat) : zi F (zone 1 i j) = matOne F i j := by
  show zi F (if i = j then (1, 0) else (0, 0)) = (if i = j then F.one else F.zero)
  match Nat.decEq i j with
  | isTrue h =>
      rw [if_pos h, if_pos h, zi_d0]
      exact ZNet.zero_add F F.one
  | isFalse h => rw [if_neg h, if_neg h, zi_zero]

include hd in
/-- THE COMPLEMENT: (1/d)·(d·1 − N) = 1 − (1/d)·N -/
theorem lit_ng (N : ZM) : meq l (lit F I d (zcomp d N)) (mng F (lit F I d N)) := fun i j _ _ => by
  show F.mul (sc F I d) (zi F (zsub (zone d i j) (N i j))) = F.add (matOne F i j) (F.neg (F.mul (sc F I d) (zi F (N i j))))
  rw [zi_sub, ← i7, sc_zone F I d hd]

include hd in
theorem lit_one {N : ZM} (h : ZEq l N (zone d)) : meq l (lit F I d N) (matOne F) := fun i j hi hj => by
  show F.mul (sc F I d) (zi F (N i j)) = matOne F i j
  rw [zi_congr F (h i j hi hj), sc_zone F I d hd]

/-! #### the checks, as computations on naturals (for `decide +kernel`) -/

theorem allB_complete : ∀ (l : List Nat) (f : Nat → Bool), (∀ i, List.Mem i l → f i = true) → QZ17.C2.allB l f = true
  | [], _, _ => rfl
  | i0 :: l, f, h => by
      show (f i0 && QZ17.C2.allB l f) = true
      rw [h i0 (List.Mem.head _), allB_complete l f (fun i hi => h i (List.Mem.tail _ hi))]
      rfl

def zeqB (x y : Z2) : Bool := decide (x.1 + y.2 = y.1 + x.2)
theorem zeqB_sound {x y : Z2} (h : zeqB x y = true) : zeq x y := (of_decide_eq_true h : x.1 + y.2 = y.1 + x.2)
theorem zeqB_complete {x y : Z2} (h : zeq x y) : zeqB x y = true := decide_eq_true (h : x.1 + y.2 = y.1 + x.2)
/-- two integer matrices are the same on the index list -/
def zchk (l : List Nat) (A B : ZM) : Bool := QZ17.C2.allB l (fun i => QZ17.C2.allB l (fun j => zeqB (A i j) (B i j)))
def zvchk (l : List Nat) (u v : ZV) : Bool := QZ17.C2.allB l (fun i => zeqB (u i) (v i))

theorem zchk_sound {l : List Nat} {A B : ZM} (h : zchk l A B = true) : ZEq l A B := fun i j hi hj =>
  zeqB_sound (QZ17.C2.allB_sound l _ (QZ17.C2.allB_sound l _ h i hi) j hj)

theorem zchk_complete {l : List Nat} {A B : ZM} (h : ZEq l A B) : zchk l A B = true :=
  allB_complete l _ (fun i hi => allB_complete l _ (fun j hj => zeqB_complete (h i j hi hj)))

theorem band3 : ∀ a b c : Bool, (a && b && c) = true → a = true ∧ b = true ∧ c = true := by decide
theorem band4 : ∀ a b c e : Bool, (a && b && c && e) = true → a = true ∧ b = true ∧ c = true ∧ e = true := by decide

/-- a symmetric projection: Nᵀ = N and N·N = d·N -/
def goodB (l : List Nat) (d : Nat) (N : ZM) : Bool := zchk l (ztr N) N && zchk l (zmm l N N) (zscM d N)
/-- A ≤ B: N_A·N_B = d·N_A and N_B·N_A = d·N_A -/
def leB (l : List Nat) (d : Nat) (A B : ZM) : Bool := zchk l (zmm l A B) (zscM d A) && zchk l (zmm l B A) (zscM d A)

include hd in
theorem good_z {N : ZM} (h : goodB l d N = true) : Good F l hn (lit F I d N) :=
  have h' := QZ17.C2.band _ _ h
  ⟨fun i j hi hj => congrArg (F.mul (sc F I d)) (zi_congr F (zchk_sound h'.1 j i hj hi)),
   lit_mul_eq F I l d hd (zchk_sound h'.2)⟩

include hd in
theorem le_z {A B : ZM} (h : leB l d A B = true) : Le (matAlg F l hn) (lit F I d A) (lit F I d B) :=
  have h' := QZ17.C2.band _ _ h
  ⟨lit_mul_eq F I l d hd (zchk_sound h'.1), lit_mul_eq F I l d hd (zchk_sound h'.2)⟩

include hd in
/-- NOT A ≤ B, from one failed integer check (here 1 ≠ 0 is used: different integers are different numbers) -/
theorem not_le_z (h1 : F.one ≠ F.zero) {A B : ZM} (h : zchk l (zmm l A B) (zscM d A) = false) :
    ¬ Le (matAlg F l hn) (lit F I d A) (lit F I d B) := fun hl => by
  have hz : ZEq l (zmm l A B) (zscM d A) := fun i j hi hj => by
    have e : F.mul (F.mul (sc F I d) (sc F I d)) (zi F (zmm l A B i j)) = F.mul (sc F I d) (zi F (A i j)) :=
      (mul_lit F I l d A B i j hi hj).symm.trans (hl.1 i j hi hj)
    have e2 : zi F (zmm l A B i j) = zi F (zsc d (A i j)) := by
      have a := congrArg (fun t => F.mul (nat F d) (F.mul (nat F d) t)) e
      have a' : F.mul (nat F d) (F.mul (nat F d) (F.mul (F.mul (sc F I d) (sc F I d)) (zi F (zmm l A B i j)))) =
          F.mul (nat F d) (F.mul (nat F d) (F.mul (sc F I d) (zi F (A i j)))) := a
      rw [i8a, i8b, sc_mul F I d hd, ZRound.one_mul, ZRound.one_mul, ZRound.one_mul] at a'
      rw [zi_sc]
      exact a'
    exact zi_inj F h1 e2
  have c := zchk_complete hz
  rw [h] at c
  exact Bool.noConfusion c

/-! #### the steps of a certificate, each from ONE computed check -/

include hd in
theorem is_zatom {N : ZM} (h : goodB l d N = true) : Is F l hn (lit F I d N) (lit F I d N) :=
  is_atom F l hn (good_z F I l hn d hd h)

def topB (l : List Nat) (d : Nat) (N : ZM) : Bool := goodB l d N && zchk l N (zone d)

include hd in
theorem is_ztop {N : ZM} (h : topB l d N = true) : Is F l hn (lit F I d N) (matOne F) :=
  have h' := QZ17.C2.band _ _ h
  is_top F l hn (good_z F I l hn d hd h'.1) (lit_one F I l d hd (zchk_sound h'.2))

def negB (l : List Nat) (d : Nat) (M N : ZM) : Bool := goodB l d N && zchk l N (zcomp d M)

include hd in
theorem is_zneg {M N : ZM} {X : Mat α} (a : Is F l hn (lit F I d M) X) (h : negB l d M N = true) :
    Is F l hn (lit F I d N) (mng F X) :=
  have h' := QZ17.C2.band _ _ h
  is_neg F l hn a (good_z F I l hn d hd h'.1)
    ((matAlg F l hn).trans (lit_congr F I l d (zchk_sound h'.2)) (lit_ng F I l d hd M))

def joinB (l : List Nat) (d : Nat) (A B J U V : ZM) : Bool :=
  goodB l d J && leB l d A J && leB l d B J && zchk l (zscM d J) (zaddM (zmm l A U) (zmm l B V))

include hd in
theorem is_zjoin {A B J U V : ZM} {X Y : Mat α} (a : Is F l hn (lit F I d A) X) (b : Is F l hn (lit F I d B) Y)
    (h : joinB l d A B J U V = true) : Is F l hn (lit F I d J) (join F I l X Y) :=
  have h' := band4 _ _ _ _ h
  is_join F I l hn a b (good_z F I l hn d hd h'.1) (le_z F I l hn d hd h'.2.1) (le_z F I l hn d hd h'.2.2.1)
    (lit_wit F I l d hd (zchk_sound h'.2.2.2))

def meetB (l : List Nat) (d : Nat) (A B M U V : ZM) : Bool :=
  goodB l d M && leB l d (zcomp d A) (zcomp d M) && leB l d (zcomp d B) (zcomp d M) &&
    zchk l (zscM d (zcomp d M)) (zaddM (zmm l (zcomp d A) U) (zmm l (zcomp d B) V))

include hd in
theorem is_zmeet {A B M U V : ZM} {X Y : Mat α} (a : Is F l hn (lit F I d A) X) (b : Is F l hn (lit F I d B) Y)
    (h : meetB l d A B M U V = true) : Is F l hn (lit F I d M) (mmeet F I l X Y) :=
  have h' := band4 _ _ _ _ h
  have nA := lit_ng F I l d hd A
  have nB := lit_ng F I l d hd B
  have nM := lit_ng F I l d hd M
  is_meet F I l hn (U := lit F I d U) (V := lit F I d V) a b (good_z F I l hn d hd h'.1)
    (le_congr (matAlg F l hn) nA nM (le_z F I l hn d hd h'.2.1))
    (le_congr (matAlg F l hn) nB nM (le_z F I l hn d hd h'.2.2.1))
    ((matAlg F l hn).trans ((matAlg F l hn).symm nM)
      ((matAlg F l hn).trans (lit_wit F I l d hd (zchk_sound h'.2.2.2))
        ((matAlg F l hn).add_congr
          ((matAlg F l hn).mul_congr nA ((matAlg F l hn).refl _))
          ((matAlg F l hn).mul_congr nB ((matAlg F l hn).refl _)))))

include hd in
theorem verdict_z {K M : ZM} {KX X : Mat α} (k : Is F l hn (lit F I d K) KX) (x : Is F l hn (lit F I d M) X)
    (h : leB l d K M = true) : Le (matAlg F l hn) KX X := verdict_le F l hn k x (le_z F I l hn d hd h)

include hd in
theorem verdict_not_z (h1 : F.one ≠ F.zero) {K M : ZM} {KX X : Mat α} (k : Is F l hn (lit F I d K) KX)
    (x : Is F l hn (lit F I d M) X) (h : zchk l (zmm l K M) (zscM d K) = false) : ¬ Le (matAlg F l hn) KX X :=
  verdict_not_le F l hn k x (not_le_z F I l hn d hd h1 h)

/-! #### the questions -/

/-- a Pauli question: 2·N = d·(1 + O) -/
def pauliB (l : List Nat) (d : Nat) (N O : ZM) : Bool := goodB l d N && zchk l (zaddM N N) (zscM d (zaddM (zone 1) O))

include hn hd in
/-- A PAULI QUESTION, CHECKED: P + P = 1 + O, so P is the projection on the +1 eigenvectors of O ((1 + O)·P = P + P) -/
theorem pauli_z {N O : ZM} (h : pauliB l d N O = true) :
    meq l (matAdd F (lit F I d N) (lit F I d N)) (matAdd F (matOne F) (zmat F O)) ∧
    meq l (matMul F l (matAdd F (matOne F) (zmat F O)) (lit F I d N)) (matAdd F (lit F I d N) (lit F I d N)) := by
  have h' := QZ17.C2.band _ _ h
  have e : meq l (matAdd F (lit F I d N) (lit F I d N)) (matAdd F (matOne F) (zmat F O)) := fun i j hi hj => by
    have hz : zeq (zadd (N i j) (N i j)) (zsc d (zadd (zone 1 i j) (O i j))) := zchk_sound h'.2 i j hi hj
    show F.add (F.mul (sc F I d) (zi F (N i j))) (F.mul (sc F I d) (zi F (N i j))) = F.add (matOne F i j) (zi F (O i j))
    rw [← F.mul_add, ← zi_add, zi_congr F hz, zi_sc, ← F.mul_assoc, sc_mul F I d hd, ZRound.one_mul, zi_add, zi_zone1]
  exact ⟨e, pauli_cert F l hn (good_z F I l hn d hd h'.1) e⟩

def zcomb : List (ZV × ZV) → ZM
  | [] => fun _ _ => (0, 0)
  | vw :: ps => fun i j => zadd (zmul (vw.1 i) (vw.2 j)) (zcomb ps i j)

def zpairs : List (ZV × ZV) → List (Vec α × Vec α)
  | [] => []
  | vw :: ps => (zvec F vw.1, svec F I d vw.2) :: zpairs ps

/-- the document's vectors (integers) -/
def zvecs : List (ZV × ZV) → List (Vec α)
  | [] => []
  | vw :: ps => zvec F vw.1 :: zvecs ps

theorem fsts_zpairs : ∀ ps : List (ZV × ZV), fsts (zpairs F I d ps) = zvecs F ps
  | [] => rfl
  | vw :: ps => congrArg (fun t => zvec F vw.1 :: t) (fsts_zpairs ps)

theorem comb_z : ∀ (ps : List (ZV × ZV)) (i j : Nat), comb F (zpairs F I d ps) i j = F.mul (sc F I d) (zi F (zcomb ps i j))
  | [], _, _ => by
      show F.zero = F.mul (sc F I d) (zi F (0, 0))
      rw [zi_zero, F.mul_zero]
  | vw :: ps, i, j => by
      show F.add (F.mul (zi F (vw.1 i)) (F.mul (sc F I d) (zi F (vw.2 j)))) (comb F (zpairs F I d ps) i j) =
        F.mul (sc F I d) (zi F (zadd (zmul (vw.1 i) (vw.2 j)) (zcomb ps i j)))
      rw [comb_z ps i j, zi_add, zi_mul]
      exact i10 F _ _ _ _

def zfixB (l : List Nat) (d : Nat) (N : ZM) : List (ZV × ZV) → Bool
  | [] => true
  | vw :: ps => zvchk l (zmv l N vw.1) (fun i => zsc d (vw.1 i)) && zfixB l d N ps

include hd in
theorem lit_mv {N : ZM} {v : ZV} (h : zvchk l (zmv l N v) (fun i => zsc d (v i)) = true) :
    veq l (mv F l (lit F I d N) (zvec F v)) (zvec F v) := fun i hi => by
  have hz : zeq (zmv l N v i) (zsc d (v i)) := zeqB_sound (QZ17.C2.allB_sound l _ h i hi)
  show S F l (fun k => F.mul (F.mul (sc F I d) (zi F (N i k))) (zi F (v k))) = zi F (v i)
  have e : S F l (fun k => F.mul (F.mul (sc F I d) (zi F (N i k))) (zi F (v k))) =
      S F l (fun k => F.mul (sc F I d) (zi F (zmul (N i k) (v k)))) :=
    S_congr F l (fun k _ => by
      show F.mul (F.mul (sc F I d) (zi F (N i k))) (zi F (v k)) = F.mul (sc F I d) (zi F (zmul (N i k) (v k)))
      rw [zi_mul, F.mul_assoc])
  have e3 : zi F (zS l (fun k => zmul (N i k) (v k))) = zi F (zsc d (v i)) := zi_congr F hz
  rw [e, S_mul F (sc F I d) (fun k => zi F (zmul (N i k) (v k))) l, ← zi_S, e3, zi_sc, ← F.mul_assoc,
    sc_mul F I d hd, ZRound.one_mul]

include hd in
theorem fixed_z {N : ZM} : ∀ ps : List (ZV × ZV), zfixB l d N ps = true → FixedFst F l (lit F I d N) (zpairs F I d ps)
  | [], _ => True.intro
  | _ :: ps, h =>
      have h' := QZ17.C2.band _ _ h
      ⟨lit_mv F I l d hd h'.1, fixed_z ps h'.2⟩

/-- a subspace question: N symmetric projection (times d), holds every vector, and N = Σ_t v_t·w_tᵀ on integers -/
def spanB (l : List Nat) (d : Nat) (N : ZM) (ps : List (ZV × ZV)) : Bool := goodB l d N && zfixB l d N ps && zchk l N (zcomb ps)

include hn hd in
/-- A SUBSPACE QUESTION, CHECKED: the matrix is the kernel's projection of the document's vectors -/
theorem span_z {N : ZM} {ps : List (ZV × ZV)} (h : spanB l d N ps = true) :
    meq l (lit F I d N) (projOf F I l (zvecs F ps)) := by
  have h' := band3 _ _ _ h
  have hc : meq l (lit F I d N) (comb F (zpairs F I d ps)) := fun i j hi hj => by
    show F.mul (sc F I d) (zi F (N i j)) = comb F (zpairs F I d ps) i j
    rw [comb_z, zi_congr F (zchk_sound h'.2.2 i j hi hj)]
  have r := projOf_cert F I l hn (zpairs F I d ps) (good_z F I l hn d hd h'.1) (fixed_z F I l d hd ps h'.2.1) hc
  rw [fsts_zpairs] at r
  exact r

/-! #### the index list -/

theorem bnot_and : ∀ a b : Bool, (!a && b) = true → a = false ∧ b = true := by decide
theorem bor_false : ∀ a b : Bool, (a || b) = false → a = false ∧ b = false := by decide

def memB (a : Nat) : List Nat → Bool
  | [] => false
  | b :: l => decide (a = b) || memB a l

theorem memB_false {a : Nat} : ∀ l : List Nat, memB a l = false → ¬ List.Mem a l
  | [], _ => fun h => nomatch h
  | b :: l, h => fun hm => by
      have h' := bor_false (decide (a = b)) (memB a l) h
      cases hm with
      | head => exact absurd (decide_eq_true rfl) (by rw [h'.1]; decide)
      | tail _ hm' => exact memB_false l h'.2 hm'

/-- no index twice, as a computation -/
def ndB : List Nat → Bool
  | [] => true
  | a :: l => !memB a l && ndB l

theorem ndB_sound : ∀ l : List Nat, ndB l = true → NoDup l
  | [], _ => True.intro
  | a :: l, h => by
      have h' := bnot_and (memB a l) (ndB l) h
      exact ⟨memB_false l h'.1, ndB_sound l h'.2⟩

end QZ18

#print axioms QZ18.join_cert
#print axioms QZ18.meet_cert
#print axioms QZ18.mul_comb
#print axioms QZ18.projOf_cert
#print axioms QZ18.pauli_cert
#print axioms QZ18.is_join
#print axioms QZ18.is_meet
#print axioms QZ18.is_neg
#print axioms QZ18.verdict_le
#print axioms QZ18.verdict_not_le
#print axioms QZ18.zi_inj
#print axioms QZ18.lit_mul_eq
#print axioms QZ18.lit_wit
#print axioms QZ18.lit_ng
#print axioms QZ18.good_z
#print axioms QZ18.le_z
#print axioms QZ18.not_le_z
#print axioms QZ18.is_zatom
#print axioms QZ18.is_ztop
#print axioms QZ18.is_zneg
#print axioms QZ18.is_zjoin
#print axioms QZ18.is_zmeet
#print axioms QZ18.verdict_z
#print axioms QZ18.verdict_not_z
#print axioms QZ18.pauli_z
#print axioms QZ18.span_z
#print axioms QZ18.ndB_sound
