import ZNet
import ZRound
import QZ3
import QZ5
import QZ7
import QZ8
import QZ9
import QZ10
import QZ12

/-!
# QZ14 — a subspace given by a SPANNING LIST is its projection: order, join and complement agree. Zero axioms.

(2026-11-28, the curator: "работай далее". Written with AI.)

QZ12 built the lattice of symmetric projections. A program (the judge's subspace.py) keeps a subspace differently -
as a list of vectors that span it. This file ties the two presentations, for any spanning list (no row reduction
is assumed of it):

  `projOf A`         the projection of the list A: start from 0 and add the vectors one after another (QZ12's `gs`)
  `projOf_fixes`     it holds every vector of A;  `projOf_least`: it is the least symmetric projection that does
  `le_iff_fixed`     ORDER:  projOf A ≤ projOf B  ↔  projOf B holds every vector of A   ("A lies in the span of B")
  `projOf_append`    JOIN:   the projection of A ++ B is the join of the two projections  (span of the union)
  `projOf_cols`      a symmetric projection is the projection of its own columns
  `projOf_compl`     COMPLEMENT: the columns of 1 − projOf A span the complement: their projection is 1 − projOf A
  `kills_iff_orth`   and that complement is the orthogonal one: projOf A sends u to 0  ↔  u is orthogonal to every
                     vector of A

So the lattice of subspaces presented by spanning lists - "lies in the span", concatenation, the vectors orthogonal
to all - IS the lattice of projections of QZ12, and what QZ8-QZ13 prove holds for it.

WHAT THIS DOES NOT REACH: the Python program itself. That subspace.py computes these operations (its row reduction
keeps the span, its `comp` returns a spanning list of the orthogonal vectors) is a statement about code, not about
this mathematics; it stays measured (rep_probe.py).
-/

namespace QZ14
open ZNet ZRound QZ7 QZ8 QZ9 QZ10 QZ12

variable {α : Type} (F : OF α) (I : Inv F) (l : List Nat) (hn : NoDup l)

/-- the projection of a spanning list -/
def projOf (A : List (Vec α)) : Mat α := gs F I l (matZero F) A

theorem projOf_good (A : List (Vec α)) : Good F l hn (projOf F I l A) := gs_good F I l hn A (good_zero F l hn)

include hn in
/-- it holds every vector of the list -/
theorem projOf_fixes (A : List (Vec α)) : AllFixed F l (projOf F I l A) A := gs_fixes F I l hn A (good_zero F l hn)

/-- 0 is a part of everything -/
theorem zero_le (R : Mat α) : Le (matAlg F l hn) (matZero F) R :=
  ⟨fun _ j _ _ => S_all_zero F l (fun k _ => ZNet.zero_mul F (R k j)),
   fun i _ _ _ => S_all_zero F l (fun k _ => F.mul_zero (R i k))⟩

/-- …and it is the least symmetric projection that does -/
theorem projOf_least {R : Mat α} (GR : Good F l hn R) (A : List (Vec α)) (h : AllFixed F l R A) :
    Le (matAlg F l hn) (projOf F I l A) R := gs_least F I l hn GR A (zero_le F l hn R) h

/-- what a part holds, the whole holds -/
theorem fixed_of_le {P R : Mat α} (h : Le (matAlg F l hn) P R) {u : Vec α} (hu : veq l (mv F l P u) u) :
    veq l (mv F l R u) u := by
  intro i hi
  have e1 : mv F l R u i = mv F l R (mv F l P u) i :=
    mv_congr F l (fun _ _ _ _ => rfl) (fun k hk => (hu k hk).symm) i hi
  have e2 : mv F l R (mv F l P u) i = mv F l P u i := by
    rw [← mv_mul]
    exact mv_congr F l h.2 (fun _ _ => rfl) i hi
  rw [e1, e2]
  exact hu i hi

theorem allFixed_of_le {P R : Mat α} (h : Le (matAlg F l hn) P R) : ∀ A, AllFixed F l P A → AllFixed F l R A
  | [], _ => True.intro
  | _ :: A, hf => ⟨fixed_of_le F l hn h hf.1, allFixed_of_le h A hf.2⟩

/-- ORDER: one projection is a part of another exactly when the other holds the first list -/
theorem le_iff_fixed (A B : List (Vec α)) :
    Le (matAlg F l hn) (projOf F I l A) (projOf F I l B) ↔ AllFixed F l (projOf F I l B) A :=
  ⟨fun h => allFixed_of_le F l hn h A (projOf_fixes F I l hn A),
   fun h => projOf_least F I l hn (projOf_good F I l hn B) A h⟩

theorem allFixed_append {M : Mat α} : ∀ A B, AllFixed F l M A → AllFixed F l M B → AllFixed F l M (A ++ B)
  | [], _, _, hB => hB
  | _ :: A, B, hA, hB => ⟨hA.1, allFixed_append A B hA.2 hB⟩

theorem allFixed_left {M : Mat α} : ∀ A B, AllFixed F l M (A ++ B) → AllFixed F l M A
  | [], _, _ => True.intro
  | _ :: A, B, h => ⟨h.1, allFixed_left A B h.2⟩

theorem allFixed_right {M : Mat α} : ∀ A B, AllFixed F l M (A ++ B) → AllFixed F l M B
  | [], _, h => h
  | _ :: A, B, h => allFixed_right A B h.2

include hn in
/-- JOIN: the projection of the two lists together is the join of the two projections -/
theorem projOf_append (A B : List (Vec α)) :
    meq l (projOf F I l (A ++ B)) (join F I l (projOf F I l A) (projOf F I l B)) := by
  have GA := projOf_good F I l hn A
  have GB := projOf_good F I l hn B
  have GAB := projOf_good F I l hn (A ++ B)
  have GJ := join_good F I l hn (Q := projOf F I l B) GA
  have fAB := projOf_fixes F I l hn (A ++ B)
  -- the join is below: each of the two projections is the least one holding its list, and the union's holds both
  have h1 : Le (matAlg F l hn) (join F I l (projOf F I l A) (projOf F I l B)) (projOf F I l (A ++ B)) :=
    join_le F I l hn GAB (projOf_least F I l hn GAB A (allFixed_left F l A B fAB))
      (projOf_least F I l hn GAB B (allFixed_right F l A B fAB))
  -- the union's is below: the join holds both lists
  have h2 : Le (matAlg F l hn) (projOf F I l (A ++ B)) (join F I l (projOf F I l A) (projOf F I l B)) :=
    projOf_least F I l hn GJ (A ++ B)
      (allFixed_append F l A B
        (allFixed_of_le F l hn (le_join_l F I l hn GA) A (projOf_fixes F I l hn A))
        (allFixed_of_le F l hn (le_join_r F I l hn GA GB) B (projOf_fixes F I l hn B)))
  exact le_antisymm (matAlg F l hn) h2 h1

/-- a symmetric projection holds its own columns -/
theorem own_cols {R : Mat α} (GR : Good F l hn R) : ∀ j, List.Mem j l → veq l (mv F l R (col R j)) (col R j) :=
  cols_of_le F l hn (le_refl_good F l hn GR)

include hn in
/-- a symmetric projection is the projection of its own columns -/
theorem projOf_cols {R : Mat α} (GR : Good F l hn R) : meq l (projOf F I l (cols R l)) R :=
  le_antisymm (matAlg F l hn)
    (projOf_least F I l hn GR (cols R l) (cols_allFixed F l l (own_cols F l hn GR)))
    (le_of_cols F l hn (projOf_good F I l hn (cols R l)).sy GR.sy
      (allFixed_cols F l l (projOf_fixes F I l hn (cols R l))))

include hn in
/-- COMPLEMENT: the columns of 1 − projOf A span the complement -/
theorem projOf_compl (A : List (Vec α)) :
    meq l (projOf F I l (cols (matSub F (matOne F) (projOf F I l A)) l)) (matSub F (matOne F) (projOf F I l A)) :=
  projOf_cols F I l hn (good_ng F l hn (projOf_good F I l hn A))

/-! ### the complement is the orthogonal one -/

/-- u is orthogonal to every vector of the list -/
def AllOrth (u : Vec α) : List (Vec α) → Prop
  | [] => True
  | a :: A => ip F l a u = F.zero ∧ AllOrth u A

theorem ip_zero_r {u : Vec α} (h : veq l u (vzero F)) (v : Vec α) : ip F l v u = F.zero := by
  rw [ip_comm]
  exact ip_zero_l F l h v

theorem ip_vsub_l (a b u : Vec α) : ip F l (vsub F a b) u = F.add (ip F l a u) (F.neg (ip F l b u)) := by
  show S F l (fun i => F.mul (F.add (a i) (F.neg (b i))) (u i)) =
    F.add (S F l (fun i => F.mul (a i) (u i))) (F.neg (S F l (fun i => F.mul (b i) (u i))))
  rw [← S_neg F _ l, ← S_add F _ _ l]
  exact S_congr F l (fun i _ => by
    show F.mul (F.add (a i) (F.neg (b i))) (u i) = F.add (F.mul (a i) (u i)) (F.neg (F.mul (b i) (u i)))
    rw [ZNet.add_mul, F.neg_mul])

/-- one step keeps "sends u to 0" when the new vector is orthogonal to u -/
theorem step_kills {J : Mat α} (G : Good F l hn J) (q u : Vec α) (hu : veq l (mv F l J u) (vzero F))
    (hq : ip F l q u = F.zero) : veq l (mv F l (step F I l J q) u) (vzero F) :=
  @Decidable.byCases _ _ (I.dec (ip F l (resid F l J q) (resid F l J q)))
    (fun h => by rw [step_zero F I l J q h]; exact hu)
    (fun h => by
      rw [step_pos F I l J q h]
      intro i hi
      have e0 : ip F l (resid F l J q) u = F.zero := by
        show ip F l (vsub F q (mv F l J q)) u = F.zero
        rw [ip_vsub_l, hq, ip_mv_sym F l G.sy, ip_zero_r F l hu q, ZNet.neg_zero, F.add_zero]
      rw [mv_add_mat, mv_ray, e0, F.mul_zero, ZNet.zero_mul, F.add_zero]
      exact hu i hi)

theorem gs_kills (u : Vec α) : ∀ (qs : List (Vec α)) {J : Mat α}, Good F l hn J → veq l (mv F l J u) (vzero F) →
    AllOrth F l u qs → veq l (mv F l (gs F I l J qs) u) (vzero F)
  | [], _, _, hu, _ => hu
  | q :: qs, _, G, hu, ho => gs_kills u qs (good_step F I l hn G q) (step_kills F I l hn G q u hu ho.1) ho.2

theorem orth_of_kills {P : Mat α} (sP : sym l P) (u : Vec α) (hu : veq l (mv F l P u) (vzero F)) :
    ∀ A, AllFixed F l P A → AllOrth F l u A
  | [], _ => True.intro
  | a :: A, hf => ⟨by
      rw [ip_congr F l (fun k hk => (hf.1 k hk).symm) (fun _ _ => rfl), ip_mv_sym F l sP]
      exact ip_zero_r F l hu a, orth_of_kills sP u hu A hf.2⟩

include hn in
/-- THE COMPLEMENT IS THE ORTHOGONAL ONE: the projection of A sends u to 0 exactly when u is orthogonal to every
vector of A -/
theorem kills_iff_orth (A : List (Vec α)) (u : Vec α) :
    veq l (mv F l (projOf F I l A) u) (vzero F) ↔ AllOrth F l u A :=
  ⟨fun h => orth_of_kills F l (projOf_good F I l hn A).sy u h A (projOf_fixes F I l hn A),
   fun h => gs_kills F I l hn u A (good_zero F l hn)
     (fun _ _ => S_all_zero F l (fun k _ => ZNet.zero_mul F (u k))) h⟩

end QZ14

#print axioms QZ14.projOf_fixes
#print axioms QZ14.projOf_least
#print axioms QZ14.le_iff_fixed
#print axioms QZ14.projOf_append
#print axioms QZ14.projOf_cols
#print axioms QZ14.projOf_compl
#print axioms QZ14.kills_iff_orth
