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
import QOF

/-!
# QZ17 — the complex structure: the projections that commute with "times i" are a lattice of their own. Zero axioms.

(2026-11-28, the curator on "the complex structure": "делай". Written with AI.)

The judge carries C^n as R^2n: a complex vector a + ib is the real vector (a, b), and "times i" is a real matrix
u with an inverse v (u·v = 1 = v·u) that is its transpose (uᵀ = v). A COMPLEX subspace is a real one that "times i"
keeps, and its projection is a real symmetric projection that COMMUTES with u. This file proves that such
projections are closed under everything the lattice of QZ12 does:

  `cj`, `cj_isP`, `cj_le`, `cj_fix`, `comm_of_fix`   conjugation p ↦ v·p·u in any associative algebra of QZ7: it
                 keeps projections and their order, fixes exactly what commutes with u
  `good_cj`      for matrices it keeps symmetry (transposes: `tr_mul`)
  `cx_join`      THE JOIN of two symmetric projections that commute with u commutes with u
                 (the conjugates of the join, both ways, are again above the two; the join is the least)
  `cxLat`        so they are a lattice (`NLat`): order, 1 − P, join, meet of QZ12, restricted
  `cxRep`, `cx_closed`, `cx_born`   a lattice of projections in the sense of QZ7 and QZ9; the Born weight is a
                 probability of layer 3 on it
  `C2.cstr`, `C2.PY_complex`, `C2.PY_born`, `C2.real_ray_not_complex`
                 C² as R⁴ over the rationals: "times i" is checked; the complex ray of (1, i) - the question Y of a
                 qubit - is a projection that commutes with it, with Born weight ½ in the state |0⟩; the real ray of
                 (1, 0) is a projection that does not commute: not a complex subspace

So everything proved for real projections holds for the complex subspaces the judge uses for Y and for complex
amplitudes. Not here: a general construction of "times i" for every n (it is given by its four laws; for n = 2 it is
written out and checked); Hermitian forms as such (the weight is the real ψᵀPψ, which for a projection commuting
with "times i" is the complex ⟨ψ, Pψ⟩).
-/

namespace QZ17
open ZNet ZRound QZ3 QZ7 QZ8 QZ9 QZ10 QZ12

/-! ### conjugation in an associative algebra -/

section Conj
variable {A : Type} {R : Alg A} (hA : Assoc R) {u v : A}

/-- p ↦ v·p·u -/
def cj (R : Alg A) (u v p : A) : A := R.mul v (R.mul p u)

theorem cj_congr {p q : A} (h : R.eqv p q) : R.eqv (cj R u v p) (cj R u v q) :=
  R.mul_congr (R.refl v) (R.mul_congr h (R.refl u))

include hA

/-- u·(v·x) = x -/
theorem cancel_l (huv : R.eqv (R.mul u v) R.one) (x : A) : R.eqv (R.mul u (R.mul v x)) x :=
  R.trans (R.symm (hA u v x)) (R.trans (R.mul_congr huv (R.refl x)) (R.one_mul x))

theorem cj_isP (huv : R.eqv (R.mul u v) R.one) {p : A} (hp : IsP R p) : IsP R (cj R u v p) :=
  R.trans (hA v (R.mul p u) (R.mul v (R.mul p u)))
    (R.mul_congr (R.refl v)
      (R.trans (hA p u (R.mul v (R.mul p u)))
        (R.trans (R.mul_congr (R.refl p) (cancel_l hA huv (R.mul p u)))
          (R.trans (R.symm (hA p p u)) (R.mul_congr hp (R.refl u))))))

/-- (x·u)·(v·(y·u)) = (x·y)·u -/
theorem mid (huv : R.eqv (R.mul u v) R.one) (x y : A) :
    R.eqv (R.mul (R.mul x u) (R.mul v (R.mul y u))) (R.mul (R.mul x y) u) :=
  R.trans (hA x u (R.mul v (R.mul y u)))
    (R.trans (R.mul_congr (R.refl x) (cancel_l hA huv (R.mul y u))) (R.symm (hA x y u)))

theorem cj_le (huv : R.eqv (R.mul u v) R.one) {p q : A} (h : Le R p q) : Le R (cj R u v p) (cj R u v q) :=
  ⟨R.trans (hA v (R.mul p u) (R.mul v (R.mul q u)))
      (R.mul_congr (R.refl v) (R.trans (mid hA huv p q) (R.mul_congr h.1 (R.refl u)))),
   R.trans (hA v (R.mul q u) (R.mul v (R.mul p u)))
      (R.mul_congr (R.refl v) (R.trans (mid hA huv q p) (R.mul_congr h.2 (R.refl u))))⟩

/-- what commutes with u is fixed -/
theorem cj_fix (hvu : R.eqv (R.mul v u) R.one) {p : A} (hc : Comm R p u) : R.eqv (cj R u v p) p :=
  R.trans (R.mul_congr (R.refl v) hc) (cancel_l hA hvu p)

/-- …and only that -/
theorem comm_of_fix (huv : R.eqv (R.mul u v) R.one) {p : A} (h : R.eqv (cj R u v p) p) : Comm R p u :=
  R.trans (R.symm (cancel_l hA huv (R.mul p u))) (R.mul_congr (R.refl u) h)

/-- conjugating one way and back -/
theorem cj_back (hvu : R.eqv (R.mul v u) R.one) (p : A) : R.eqv (cj R u v (cj R v u p)) p :=
  R.trans (R.mul_congr (R.refl v) (hA u (R.mul p v) u))
    (R.trans (cancel_l hA hvu (R.mul (R.mul p v) u))
      (R.trans (hA p v u) (R.trans (R.mul_congr (R.refl p) hvu) (R.mul_one p))))

end Conj

/-! ### matrices: transposes, and the conjugate of a symmetric projection -/

variable {α : Type} (F : OF α) (l : List Nat) (hn : NoDup l)

/-- the transpose -/
def tr (M : Mat α) : Mat α := fun i j => M j i

theorem tr_mul (A B : Mat α) : meq l (tr (matMul F l A B)) (matMul F l (tr B) (tr A)) := fun i j _ _ =>
  S_congr F l (fun k _ => F.mul_comm (A j k) (B k i))

theorem tr_of_sym {P : Mat α} (h : sym l P) : meq l (tr P) P := fun i j hi hj => h j i hj hi
theorem sym_of_tr {P : Mat α} (h : meq l (tr P) P) : sym l P := fun i j hi hj => (h j i hj hi)

variable {u v : Mat α}

/-- the conjugate of a symmetric projection is one (u·v = 1, uᵀ = v, vᵀ = u) -/
theorem good_cj (huv : meq l (matMul F l u v) (matOne F)) (htu : meq l (tr u) v) (htv : meq l (tr v) u)
    {P : Mat α} (G : Good F l hn P) : Good F l hn (cj (matAlg F l hn) u v P) :=
  ⟨sym_of_tr l
      ((matAlg F l hn).trans (tr_mul F l v (matMul F l P u))
        ((matAlg F l hn).trans ((matAlg F l hn).mul_congr (tr_mul F l P u) htv)
          ((matAlg F l hn).trans ((matAlg F l hn).mul_congr ((matAlg F l hn).mul_congr htu (tr_of_sym l G.sy)) ((matAlg F l hn).refl u))
            (mat_assoc F l hn v P u)))),
   cj_isP (mat_assoc F l hn) huv G.pr⟩

/-! ### the join of two that commute with u commutes with u -/

variable (I : Inv F)

/-- THE JOIN KEEPS THE COMPLEX STRUCTURE -/
theorem cx_join (huv : meq l (matMul F l u v) (matOne F)) (hvu : meq l (matMul F l v u) (matOne F))
    (htu : meq l (tr u) v) (htv : meq l (tr v) u)
    {P Q : Mat α} (GP : Good F l hn P) (GQ : Good F l hn Q)
    (cP : Comm (matAlg F l hn) P u) (cQ : Comm (matAlg F l hn) Q u) :
    Comm (matAlg F l hn) (join F I l P Q) u := by
  have hA := mat_assoc F l hn
  have GJ := join_good F I l hn (Q := Q) GP
  -- P and Q commute with v too
  have cv : ∀ {X : Mat α}, Comm (matAlg F l hn) X u → Comm (matAlg F l hn) X v := fun {X} c =>
    comm_of_fix (u := v) (v := u) hA hvu
      ((matAlg F l hn).trans ((matAlg F l hn).symm (cj_congr (u := v) (v := u) (cj_fix hA hvu c)))
        (cj_back (u := v) (v := u) hA huv X))
  -- one conjugate is above P and Q, so above the join
  have G1 := good_cj F l hn huv htu htv GJ
  have h1 : Le (matAlg F l hn) (join F I l P Q) (cj (matAlg F l hn) u v (join F I l P Q)) :=
    join_le F I l hn G1
      (le_congr (matAlg F l hn) (cj_fix hA hvu cP) ((matAlg F l hn).refl _) (cj_le hA huv (le_join_l F I l hn GP)))
      (le_congr (matAlg F l hn) (cj_fix hA hvu cQ) ((matAlg F l hn).refl _) (cj_le hA huv (le_join_r F I l hn GP GQ)))
  -- the other conjugate too
  have G2 := good_cj F l hn hvu htv htu GJ
  have h2 : Le (matAlg F l hn) (join F I l P Q) (cj (matAlg F l hn) v u (join F I l P Q)) :=
    join_le F I l hn G2
      (le_congr (matAlg F l hn) (cj_fix hA huv (cv cP)) ((matAlg F l hn).refl _) (cj_le hA hvu (le_join_l F I l hn GP)))
      (le_congr (matAlg F l hn) (cj_fix hA huv (cv cQ)) ((matAlg F l hn).refl _) (cj_le hA hvu (le_join_r F I l hn GP GQ)))
  -- conjugate the second back: the first conjugate is below the join
  have h3 : Le (matAlg F l hn) (cj (matAlg F l hn) u v (join F I l P Q)) (join F I l P Q) :=
    le_congr (matAlg F l hn) ((matAlg F l hn).refl _) (cj_back hA hvu (join F I l P Q)) (cj_le hA huv h2)
  exact comm_of_fix hA huv (le_antisymm (matAlg F l hn) h3 h1)

/-! ### the lattice of the projections that commute with "times i" -/

/-- "times i" on R^2n: a matrix with an inverse that is its transpose -/
structure CStr where
  u : Mat α
  v : Mat α
  uv : meq l (matMul F l u v) (matOne F)
  vu : meq l (matMul F l v u) (matOne F)
  tu : meq l (tr u) v
  tv : meq l (tr v) u

variable (C : CStr F l)

theorem cx_ng {P : Mat α} (c : Comm (matAlg F l hn) P C.u) : Comm (matAlg F l hn) (matSub F (matOne F) P) C.u :=
  comm_symm (matAlg F l hn) (comm_ng (matAlg F l hn) (comm_symm (matAlg F l hn) c))

theorem cx_one : Comm (matAlg F l hn) (matOne F) C.u :=
  (matAlg F l hn).trans ((matAlg F l hn).one_mul C.u) ((matAlg F l hn).symm ((matAlg F l hn).mul_one C.u))

theorem cx_zero : Comm (matAlg F l hn) (matZero F) C.u := fun i j _ _ =>
  (S_all_zero F l (fun k _ => ZNet.zero_mul F (C.u k j))).trans (S_all_zero F l (fun k _ => F.mul_zero (C.u i k))).symm

theorem cx_add {P Q : Mat α} (cP : Comm (matAlg F l hn) P C.u) (cQ : Comm (matAlg F l hn) Q C.u) :
    Comm (matAlg F l hn) (matAdd F P Q) C.u :=
  (matAlg F l hn).trans ((matAlg F l hn).add_mul P Q C.u)
    ((matAlg F l hn).trans ((matAlg F l hn).add_congr cP cQ) ((matAlg F l hn).symm ((matAlg F l hn).mul_add C.u P Q)))

/-- a symmetric projection that commutes with "times i": the projection of a complex subspace -/
def CProj : Type := {J : Mat α // Good F l hn J ∧ Comm (matAlg F l hn) J C.u}

/-- forget the complex structure -/
def fg (x : CProj F l hn C) : Proj F l hn := ⟨x.1, x.2.1⟩

/-- THE LATTICE OF COMPLEX SUBSPACES: QZ12's order, negation, join and meet, on the projections that commute with
"times i" - they are closed under all four -/
def cxLat : NLat (CProj F l hn C) where
  le := fun x y => (projLat F I l hn).le (fg F l hn C x) (fg F l hn C y)
  join := fun x y =>
    ⟨join F I l x.1 y.1, join_good F I l hn x.2.1, cx_join F l hn I C.uv C.vu C.tu C.tv x.2.1 y.2.1 x.2.2 y.2.2⟩
  neg := fun x => ⟨matSub F (matOne F) x.1, good_ng F l hn x.2.1, cx_ng F l hn C x.2.2⟩
  meet := fun x y =>
    ⟨matSub F (matOne F) (join F I l (matSub F (matOne F) x.1) (matSub F (matOne F) y.1)),
     good_ng F l hn (join_good F I l hn (good_ng F l hn x.2.1)),
     cx_ng F l hn C (cx_join F l hn I C.uv C.vu C.tu C.tv (good_ng F l hn x.2.1) (good_ng F l hn y.2.1)
       (cx_ng F l hn C x.2.2) (cx_ng F l hn C y.2.2))⟩
  top := ⟨matOne F, good_one F l hn, cx_one F l hn C⟩
  bot := ⟨matZero F, good_zero F l hn, cx_zero F l hn C⟩
  le_trans := fun h1 h2 => (projLat F I l hn).le_trans h1 h2
  meet_le_l := fun x y => (projLat F I l hn).meet_le_l (fg F l hn C x) (fg F l hn C y)
  meet_le_r := fun x y => (projLat F I l hn).meet_le_r (fg F l hn C x) (fg F l hn C y)
  le_meet := fun {s a b} h1 h2 =>
    (projLat F I l hn).le_meet (s := fg F l hn C s) (a := fg F l hn C a) (b := fg F l hn C b) h1 h2
  le_join_l := fun x y => (projLat F I l hn).le_join_l (fg F l hn C x) (fg F l hn C y)
  le_join_r := fun x y => (projLat F I l hn).le_join_r (fg F l hn C x) (fg F l hn C y)
  join_le := fun {a b c} h1 h2 =>
    (projLat F I l hn).join_le (a := fg F l hn C a) (b := fg F l hn C b) (c := fg F l hn C c) h1 h2
  anti := fun {a b} h => (projLat F I l hn).anti (a := fg F l hn C a) (b := fg F l hn C b) h
  le_nn := fun x => (projLat F I l hn).le_nn (fg F l hn C x)
  le_top := fun x => (projLat F I l hn).le_top (fg F l hn C x)
  le_neg_bot := fun x => (projLat F I l hn).le_neg_bot (fg F l hn C x)

/-- it is a lattice of projections in the sense of QZ7… -/
def cxRep : Rep (matAlg F l hn) (cxLat F l hn I C) where
  e := fun x => x.1
  isP := fun x => x.2.1.pr
  le_to := fun h => h
  le_of := fun h => h
  neg := fun _ _ _ _ _ => rfl
  top := fun _ _ _ _ => rfl
  bot := fun _ _ _ _ => rfl
  sum := fun x y h =>
    ⟨⟨matAdd F x.1 y.1, good_add F l hn x.2.1 y.2.1 h, cx_add F l hn C x.2.2 y.2.2⟩, fun _ _ _ _ => rfl⟩

/-- …and of QZ9 -/
theorem cx_closed : Closed (cxRep F l hn I C) := fun x y h =>
  ⟨⟨matMul F l x.1 y.1, good_mul F l hn x.2.1 y.2.1 h, comm_mul (mat_assoc F l hn) x.2.2 y.2.2⟩, fun _ _ _ _ => rfl⟩

/-- THE BORN WEIGHT IS A PROBABILITY OF LAYER 3 ON THE LATTICE OF COMPLEX SUBSPACES -/
def cx_born (mm : MinMax F) (ψ : Vec α) :
    QZ5.Prob (cxLat F l hn I C) (scale F mm (qf F l (matOne F) ψ)) :=
  born_prob F l hn mm ψ (cxRep F l hn I C) (fun x => x.2.1.sy)

/-- …and a state splits along a question there exactly when the projections commute -/
theorem cx_splits_iff_comm (s a : CProj F l hn C) :
    (cxLat F l hn I C).le s ((cxLat F l hn I C).join ((cxLat F l hn I C).meet s a) ((cxLat F l hn I C).meet s ((cxLat F l hn I C).neg a)))
      ↔ Comm (matAlg F l hn) s.1 a.1 :=
  ⟨fun h => split_comm (cxRep F l hn I C) s a h,
   fun h => comm_split (mat_assoc F l hn) (cxRep F l hn I C) (cx_closed F l hn I C) s a h⟩

/-! ### C² as R⁴ over the rationals -/

namespace C2
open QOF

def allB : List Nat → (Nat → Bool) → Bool
  | [], _ => true
  | i :: l, f => f i && allB l f

theorem band : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by decide

theorem allB_sound : ∀ (l : List Nat) (f : Nat → Bool), allB l f = true → ∀ i, List.Mem i l → f i = true
  | [], _, _, _, hi => nomatch hi
  | i0 :: l, f, h, i, hi => by
      have h' := band (f i0) (allB l f) h
      cases hi with
      | head => exact h'.1
      | tail _ hi' => exact allB_sound l f h'.2 i hi'

/-- two matrices equal entry by entry on the index list, checked by computation -/
def chk (l : List Nat) (M N : Mat QC) : Bool := allB l (fun i => allB l (fun j => decide (M i j = N i j)))

theorem chk_sound {l : List Nat} {M N : Mat QC} (h : chk l M N = true) : meq l M N := fun i j hi hj =>
  of_decide_eq_true (allB_sound l _ (allB_sound l _ h i hi) j hj)

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

/-- "times i" on (re₀, re₁, im₀, im₁): (a, b) ↦ (−b, a) -/
def uC : Mat QC := fun i j =>
  if (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) then qOF.one
  else if (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) then qOF.neg qOF.one else qOF.zero

/-- its inverse, the transpose -/
def vC : Mat QC := tr uC

/-- IT IS A COMPLEX STRUCTURE: u·v = 1 = v·u, the inverse is the transpose -/
def cstr : CStr qOF l4 :=
  ⟨uC, vC, chk_sound (by decide +kernel), chk_sound (by decide +kernel), fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def v4 (a b c d : QC) : Vec QC := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else d
def h2 : QC := frac 1 false 1

/-- the complex vector (1, i): real part (1, 0), imaginary part (0, 1); and i times it, (i, −1) -/
def w1 : Vec QC := v4 qOF.one qOF.zero qOF.zero qOF.one
def w2 : Vec QC := v4 qOF.zero (qOF.neg qOF.one) qOF.one qOF.zero

/-- the question Y of a qubit: the projection on the complex ray of (1, i) -/
def PY : Mat QC := matAdd qOF (ray qOF h2 w1) (ray qOF h2 w2)

theorem PY_good : Good qOF l4 nd4 PY :=
  ⟨sym_of_tr l4 (chk_sound (by decide +kernel)), chk_sound (by decide +kernel)⟩

/-- it commutes with "times i": a complex subspace -/
theorem PY_complex : Comm (matAlg qOF l4 nd4) PY uC := chk_sound (by decide +kernel)

/-- so it is a member of the lattice of complex subspaces -/
def Yq : CProj qOF l4 nd4 cstr := ⟨PY, PY_good, PY_complex⟩

/-- in the state |0⟩ = (1, 0) its Born weight is one half (of ψᵀψ = 1) -/
theorem PY_born : qf qOF l4 PY (v4 qOF.one qOF.zero qOF.zero qOF.zero) = h2 ∧
    qf qOF l4 (matOne qOF) (v4 qOF.one qOF.zero qOF.zero qOF.zero) = qOF.one := by decide +kernel

/-- the real ray of (1, 0) alone is a symmetric projection that does NOT commute with "times i": not a complex
subspace (its complex ray is two-dimensional over the reals) -/
theorem real_ray_not_complex :
    ¬ Comm (matAlg qOF l4 nd4) (ray qOF qOF.one (v4 qOF.one qOF.zero qOF.zero qOF.zero)) uC := fun h =>
  (by decide +kernel :
      ¬ matMul qOF l4 (ray qOF qOF.one (v4 qOF.one qOF.zero qOF.zero qOF.zero)) uC 0 2 =
        matMul qOF l4 uC (ray qOF qOF.one (v4 qOF.one qOF.zero qOF.zero qOF.zero)) 0 2)
    (h 0 2 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

/-- the Born weight of any rational state is a probability of layer 3 on the complex subspaces of C² -/
def c2_born (ψ : Vec QC) :=
  cx_born qOF l4 nd4 QZ13.qInv cstr QZ11.mmQ ψ

end C2

end QZ17

#print axioms QZ17.cj_isP
#print axioms QZ17.cj_le
#print axioms QZ17.cj_back
#print axioms QZ17.good_cj
#print axioms QZ17.cx_join
#print axioms QZ17.cxLat
#print axioms QZ17.cxRep
#print axioms QZ17.cx_closed
#print axioms QZ17.cx_born
#print axioms QZ17.cx_splits_iff_comm
#print axioms QZ17.C2.cstr
#print axioms QZ17.C2.PY_good
#print axioms QZ17.C2.PY_complex
#print axioms QZ17.C2.PY_born
#print axioms QZ17.C2.real_ray_not_complex
#print axioms QZ17.C2.c2_born
