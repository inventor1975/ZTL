import ZNet
import ZRound
import QZ7
import QZ8
import QZ10
import QZ12
import QZ17
import QZ18

/-!
# QZ20 — an inequality between averages, re-checked by the kernel: the classical bound and the quantum value. Zero axioms.

(2026-11-28, the curator on the limits of the judge's layer for linear functionals: "Но делать это надо". Written with AI.)

The QZ judge's layer `functional.py` takes a combination of the questions' ±1 outcomes - "a + b − ½·a·b" - and says
two exact things: its greatest value over all assignments of definite values, and its value in the quantum states
the document allows. This file is what the kernel checks about both, for ONE list of terms read both ways:

  the functional   `terms : List (Z2 × List Nat)`: an integer coefficient and the questions multiplied
  classical        `fval s terms`: its value under the assignment s (true = the question shows −1);
                   `classical_bound`: a computed sweep over EVERY assignment of the named questions (`allS`) gives
                   `∀ s, fval s terms ≤ c` - no assignment is sampled, and none is left out (`allS_sound`)
  quantum          `opE env terms`: the same terms as an operator, a question read as its observable 2P − 1 (`obs`);
                   `scalar_on`: if P·O·P = (b/a)·P for the projection P of what is known, then in every state ψ of the
                   knowledge  a·⟨ψ|O|ψ⟩ = b·⟨ψ|ψ⟩ - the functional has ONE value there, b/a
  on integers      as in QZ18: the matrices are integer matrices over one denominator, every check a computation on
                   naturals (`prod_z`, `op_z`, `scalar_z`); the statement is about any ordered field with 1 ≠ 0

So a certificate ends in: every definite assignment gives at most c; every state of the knowledge gives b/a; and
c·a < b is a comparison of two naturals. Yu and Oh's 13 rays: 16 against 50/3 (twice the functional: 8 against 25/3).

Not here: a functional that is NOT one number on the knowledge (the judge's "in some states" and its enclosures);
amplitudes outside the rationals (CHSH's 2·√2 needs certificates over Q(√2)).
-/

namespace QZ20
open ZNet ZRound QZ7 QZ8 QZ10 QZ12 QZ18

variable {α : Type} (F : OF α) (I : Inv F) (l : List Nat) (hn : NoDup l)

/-! ### the classical side: every assignment of definite values -/

/-- an integer is at most another ((p, n) stands for p − n) -/
def zle (x y : Z2) : Prop := x.1 + y.2 ≤ y.1 + x.2
def zleB (x y : Z2) : Bool := Nat.ble (x.1 + y.2) (y.1 + x.2)
theorem zleB_sound {x y : Z2} (h : zleB x y = true) : zle x y := Nat.le_of_ble_eq_true h

def bxor : Bool → Bool → Bool
  | true, b => !b
  | false, b => b
/-- the sign of a product of ±1 values: true = −1 (an odd number of the factors show −1) -/
def odd (s : Nat → Bool) : List Nat → Bool
  | [] => false
  | i :: is => bxor (s i) (odd s is)
def zneg (x : Z2) : Z2 := (x.2, x.1)
def tsgn : Bool → Z2 → Z2
  | true, c => zneg c
  | false, c => c
/-- THE VALUE of the functional under an assignment of definite values -/
def fval (s : Nat → Bool) : List (Z2 × List Nat) → Z2
  | [] => (0, 0)
  | t :: ts => zadd (tsgn (odd s t.2) t.1) (fval s ts)

theorem odd_congr {s s' : Nat → Bool} : ∀ is : List Nat, (∀ i, List.Mem i is → s i = s' i) → odd s is = odd s' is
  | [], _ => rfl
  | i :: is, h => by
      show bxor (s i) (odd s is) = bxor (s' i) (odd s' is)
      rw [h i (List.Mem.head _), odd_congr is (fun j hj => h j (List.Mem.tail _ hj))]

theorem bor_true : ∀ a b : Bool, (a || b) = true → a = true ∨ b = true := by decide
theorem bool_cases : ∀ b : Bool, b = true ∨ b = false
  | true => Or.inl rfl
  | false => Or.inr rfl

theorem memB_true {a : Nat} : ∀ l : List Nat, memB a l = true → List.Mem a l
  | [], h => Bool.noConfusion h
  | b :: l, h => by
      cases bor_true (decide (a = b)) (memB a l) h with
      | inl e => exact (of_decide_eq_true e : a = b) ▸ List.Mem.head _
      | inr e => exact List.Mem.tail _ (memB_true l e)

/-- every question of every term is in the list vs -/
def covB (vs : List Nat) : List (Z2 × List Nat) → Bool
  | [] => true
  | t :: ts => QZ17.C2.allB t.2 (fun i => memB i vs) && covB vs ts

theorem fval_congr {s s' : Nat → Bool} {vs : List Nat} (h : ∀ i, List.Mem i vs → s i = s' i) :
    ∀ ts : List (Z2 × List Nat), covB vs ts = true → fval s ts = fval s' ts
  | [], _ => rfl
  | t :: ts, hc => by
      have hc' := QZ17.C2.band _ _ hc
      have e : odd s t.2 = odd s' t.2 :=
        odd_congr t.2 (fun i hi => h i (memB_true vs (QZ17.C2.allB_sound t.2 _ hc'.1 i hi)))
      show zadd (tsgn (odd s t.2) t.1) (fval s ts) = zadd (tsgn (odd s' t.2) t.1) (fval s' ts)
      rw [e, fval_congr h ts hc'.2]

/-- the assignment s with the question v set to b -/
def setv (s : Nat → Bool) (v : Nat) (b : Bool) : Nat → Bool := fun i => if i = v then b else s i

theorem setv_same (s : Nat → Bool) (v : Nat) (b : Bool) : setv s v b v = b := by
  show (if v = v then b else s v) = b
  rw [if_pos rfl]

theorem setv_other (s : Nat → Bool) (v : Nat) (b : Bool) {i : Nat} (h : ¬ i = v) : setv s v b i = s i := by
  show (if i = v then b else s i) = s i
  rw [if_neg h]

/-- THE SWEEP: p on every assignment of the questions vs (the others as in s) -/
def allS : List Nat → (Nat → Bool) → ((Nat → Bool) → Bool) → Bool
  | [], s, p => p s
  | v :: vs, s, p => allS vs (setv s v false) p && allS vs (setv s v true) p

/-- the sweep leaves no assignment out: for every s it visited one that agrees with s on vs -/
theorem allS_sound (p : (Nat → Bool) → Bool) : ∀ (vs : List Nat) (s0 : Nat → Bool), allS vs s0 p = true →
    ∀ s : Nat → Bool, ∃ t : Nat → Bool, p t = true ∧ (∀ i, List.Mem i vs → t i = s i) ∧ (∀ i, ¬ List.Mem i vs → t i = s0 i)
  | [], s0, h, _ => ⟨s0, h, (fun _ hi => nomatch hi), fun _ _ => rfl⟩
  | v :: vs, s0, h, s => by
      have h' := QZ17.C2.band _ _ h
      have pick : ∃ b : Bool, b = s v ∧ allS vs (setv s0 v b) p = true := by
        cases bool_cases (s v) with
        | inl e => exact ⟨true, e.symm, h'.2⟩
        | inr e => exact ⟨false, e.symm, h'.1⟩
      cases pick with
      | intro b hb =>
        cases allS_sound p vs (setv s0 v b) hb.2 s with
        | intro t ht =>
          refine ⟨t, ht.1, ?_, ?_⟩
          · intro i hi
            cases hi with
            | head =>
              cases bool_cases (memB v vs) with
              | inl e => exact ht.2.1 v (memB_true vs e)
              | inr e => exact (ht.2.2 v (memB_false vs e)).trans ((setv_same s0 v b).trans hb.1)
            | tail _ hi' => exact ht.2.1 i hi'
          · intro i hi
            have hiv : ¬ i = v := fun e => hi (e ▸ List.Mem.head _)
            exact (ht.2.2 i (fun hm => hi (List.Mem.tail _ hm))).trans (setv_other s0 v b hiv)

/-- THE SWEEP IS SOUND for any property of the value: checked on every assignment of vs, it holds of every assignment -/
theorem sweep (q : Z2 → Bool) {ts : List (Z2 × List Nat)} {vs : List Nat} (hc : covB vs ts = true)
    (h : allS vs (fun _ => false) (fun s => q (fval s ts)) = true) : ∀ s : Nat → Bool, q (fval s ts) = true := fun s => by
  cases allS_sound _ vs _ h s with
  | intro t ht =>
    have e : fval s ts = fval t ts := fval_congr (fun i hi => (ht.2.1 i hi).symm) ts hc
    rw [e]
    exact ht.1

/-- THE CLASSICAL BOUND: the functional is at most c under EVERY assignment of definite values -/
theorem classical_bound {ts : List (Z2 × List Nat)} {vs : List Nat} {c : Z2} (hc : covB vs ts = true)
    (h : allS vs (fun _ => false) (fun s => zleB (fval s ts) c) = true) : ∀ s : Nat → Bool, zle (fval s ts) c := fun s =>
  zleB_sound (sweep (fun x => zleB x c) hc h s)

/-- ... and at least c -/
theorem classical_floor {ts : List (Z2 × List Nat)} {vs : List Nat} {c : Z2} (hc : covB vs ts = true)
    (h : allS vs (fun _ => false) (fun s => zleB c (fval s ts)) = true) : ∀ s : Nat → Bool, zle c (fval s ts) := fun s =>
  zleB_sound (sweep (fun x => zleB c x) hc h s)

/-! ### the quantum side: the same terms as an operator -/

/-- the ±1 observable of a question with projection P: 2P − 1 -/
def obs (P : Mat α) : Mat α := matSub F (matAdd F P P) (matOne F)
def prodM (env : Nat → Mat α) : List Nat → Mat α
  | [] => matOne F
  | i :: is => matMul F l (env i) (prodM env is)
def smul (c : α) (M : Mat α) : Mat α := fun i j => F.mul c (M i j)
/-- THE OPERATOR of the functional: Σ c · Π (observables) -/
def opE (env : Nat → Mat α) : List (Z2 × List Nat) → Mat α
  | [] => matZero F
  | t :: ts => matAdd F (smul F (zi F t.1) (prodM F l env t.2)) (opE env ts)

theorem mul_left_comm (a b c : α) : F.mul a (F.mul b c) = F.mul b (F.mul a c) := by
  rw [← F.mul_assoc, F.mul_comm a b, F.mul_assoc]

theorem qf_ip (M : Mat α) (ψ : Vec α) : qf F l M ψ = ip F l ψ (mv F l M ψ) :=
  S_congr F l (fun i _ => S_mul F (ψ i) (fun j => F.mul (M i j) (ψ j)) l)

theorem qf_congr {M N : Mat α} (h : meq l M N) (ψ : Vec α) : qf F l M ψ = qf F l N ψ :=
  S_congr F l (fun i hi => S_congr F l (fun j hj => by
    show F.mul (ψ i) (F.mul (M i j) (ψ j)) = F.mul (ψ i) (F.mul (N i j) (ψ j))
    rw [h i j hi hj]))

theorem ip_smul_r (c : α) (u v : Vec α) : ip F l u (fun i => F.mul c (v i)) = F.mul c (ip F l u v) := by
  show S F l (fun i => F.mul (u i) (F.mul c (v i))) = F.mul c (S F l (fun i => F.mul (u i) (v i)))
  rw [← S_mul F c (fun i => F.mul (u i) (v i)) l]
  exact S_congr F l (fun i _ => mul_left_comm F (u i) c (v i))

theorem mv_smul (c : α) (M : Mat α) (v : Vec α) (i : Nat) : mv F l (smul F c M) v i = F.mul c (mv F l M v i) := by
  show S F l (fun k => F.mul (F.mul c (M i k)) (v k)) = F.mul c (S F l (fun k => F.mul (M i k) (v k)))
  rw [← S_mul F c (fun k => F.mul (M i k) (v k)) l]
  exact S_congr F l (fun k _ => F.mul_assoc c (M i k) (v k))

include hn in
/-- ONE VALUE ON THE KNOWLEDGE: if P·O·P = W and a·W = b·P, then a·⟨ψ|O|ψ⟩ = b·⟨ψ|ψ⟩ for every ψ that P holds -/
theorem scalar_on {P O W : Mat α} {a b : α} (GP : Good F l hn P) (hW : meq l (matMul F l P (matMul F l O P)) W)
    (hab : ∀ i j, List.Mem i l → List.Mem j l → F.mul a (W i j) = F.mul b (P i j)) {ψ : Vec α}
    (hψ : veq l (mv F l P ψ) ψ) : F.mul a (qf F l O ψ) = F.mul b (ip F l ψ ψ) := by
  have hψ' : veq l ψ (mv F l P ψ) := fun i hi => (hψ i hi).symm
  have refl_O : meq l O O := fun _ _ _ _ => rfl
  -- ⟨ψ|O|ψ⟩ = ⟨Pψ|O|Pψ⟩ = ⟨ψ|P O P|ψ⟩ = ⟨ψ|W|ψ⟩
  have e1 : ip F l ψ (mv F l O ψ) = ip F l (mv F l P ψ) (mv F l O (mv F l P ψ)) :=
    ip_congr F l hψ' (mv_congr F l refl_O hψ')
  have e2 : ip F l (mv F l P ψ) (mv F l O (mv F l P ψ)) = ip F l ψ (mv F l P (mv F l O (mv F l P ψ))) :=
    ip_mv_sym F l GP.sy ψ (mv F l O (mv F l P ψ))
  have e3 : veq l (mv F l P (mv F l O (mv F l P ψ))) (mv F l W ψ) := fun i hi => by
    have a1 : mv F l (matMul F l P (matMul F l O P)) ψ i = mv F l P (mv F l (matMul F l O P) ψ) i := mv_mul F l P _ ψ i
    have a2 : veq l (mv F l (matMul F l O P) ψ) (mv F l O (mv F l P ψ)) := fun k _ => mv_mul F l O P ψ k
    have a3 : mv F l P (mv F l (matMul F l O P) ψ) i = mv F l P (mv F l O (mv F l P ψ)) i :=
      mv_congr F l (fun _ _ _ _ => rfl) a2 i hi
    have a4 : mv F l (matMul F l P (matMul F l O P)) ψ i = mv F l W ψ i :=
      mv_congr F l hW (fun _ _ => rfl) i hi
    exact (a3.symm.trans a1.symm).trans a4
  have e4 : ip F l ψ (mv F l P (mv F l O (mv F l P ψ))) = ip F l ψ (mv F l W ψ) :=
    ip_congr F l (fun _ _ => rfl) e3
  -- a·⟨ψ|W|ψ⟩ = ⟨ψ|aW|ψ⟩ = ⟨ψ|bP|ψ⟩ = b·⟨ψ|Pψ⟩ = b·⟨ψ|ψ⟩
  have e5 : F.mul a (ip F l ψ (mv F l W ψ)) = ip F l ψ (mv F l (smul F a W) ψ) :=
    ((ip_smul_r F l a ψ (mv F l W ψ)).symm).trans (ip_congr F l (fun _ _ => rfl) (fun i _ => (mv_smul F l a W ψ i).symm))
  have e6 : ip F l ψ (mv F l (smul F a W) ψ) = ip F l ψ (mv F l (smul F b P) ψ) :=
    ip_congr F l (fun _ _ => rfl) (mv_congr F l (fun i j hi hj => hab i j hi hj) (fun _ _ => rfl))
  have e7 : ip F l ψ (mv F l (smul F b P) ψ) = F.mul b (ip F l ψ ψ) :=
    ((ip_congr F l (fun _ _ => rfl) (fun i _ => mv_smul F l b P ψ i)).trans (ip_smul_r F l b ψ (mv F l P ψ))).trans
      (congrArg (F.mul b) (ip_congr F l (fun _ _ => rfl) hψ))
  rw [qf_ip, e1, e2, e4, e5, e6, e7]

/-! ### on integer data (QZ18: a matrix N of integers stands for `lit d N` = (1/d)·N) -/

variable (d : Nat) (hd : nat F d ≠ F.zero)

/-- 2N − d·1: the observable of the projection (1/d)·N, times d -/
def zobs (d : Nat) (N : ZM) : ZM := fun i j => zsub (zadd (N i j) (N i j)) (zone d i j)
/-- an integer times an integer matrix -/
def zcM (c : Z2) (N : ZM) : ZM := fun i j => zmul c (N i j)

include hd in
theorem lit_obs (N : ZM) : meq l (lit F I d (zobs d N)) (obs F (lit F I d N)) := fun i j _ _ => by
  show F.mul (sc F I d) (zi F (zsub (zadd (N i j) (N i j)) (zone d i j))) =
    F.add (F.add (F.mul (sc F I d) (zi F (N i j))) (F.mul (sc F I d) (zi F (N i j)))) (F.neg (matOne F i j))
  rw [zi_sub, ← i7, zi_add, F.mul_add, sc_zone F I d hd]

theorem lit_add (A B : ZM) : meq l (matAdd F (lit F I d A) (lit F I d B)) (lit F I d (zaddM A B)) := fun i j _ _ => by
  show F.add (F.mul (sc F I d) (zi F (A i j))) (F.mul (sc F I d) (zi F (B i j))) = F.mul (sc F I d) (zi F (zadd (A i j) (B i j)))
  rw [zi_add, F.mul_add]

theorem lit_smul (c : Z2) (N : ZM) : meq l (smul F (zi F c) (lit F I d N)) (lit F I d (zcM c N)) := fun i j _ _ => by
  show F.mul (zi F c) (F.mul (sc F I d) (zi F (N i j))) = F.mul (sc F I d) (zi F (zmul c (N i j)))
  rw [zi_mul, mul_left_comm]

include hd in
/-- the empty product is 1 -/
theorem prod_nil (env : Nat → Mat α) : meq l (prodM F l env []) (lit F I d (zone d)) := fun i j hi hj =>
  (lit_one F I l d hd (fun _ _ _ _ => rfl) i j hi hj).symm

include hn hd in
/-- one more factor: N_A·N_R = d·N_R' gives A·R = R' -/
theorem prod_z {env : Nat → Mat α} {i : Nat} {is : List Nat} {A R R' : ZM} (hA : meq l (env i) (lit F I d A))
    (hR : meq l (prodM F l env is) (lit F I d R)) (h : zchk l (zmm l A R) (zscM d R') = true) :
    meq l (prodM F l env (i :: is)) (lit F I d R') :=
  (matAlg F l hn).trans ((matAlg F l hn).mul_congr hA hR) (lit_mul_eq F I l d hd (zchk_sound h))

theorem op_nil (env : Nat → Mat α) : meq l (opE F l env []) (lit F I d (fun _ _ => (0, 0))) := fun i j _ _ => by
  show F.zero = F.mul (sc F I d) (zi F (0, 0))
  rw [zi_zero, F.mul_zero]

include hn in
/-- one more term: N_S' = c·N_T + N_S -/
theorem op_z {env : Nat → Mat α} {t : Z2 × List Nat} {ts : List (Z2 × List Nat)} {T S S' : ZM}
    (hT : meq l (prodM F l env t.2) (lit F I d T)) (hS : meq l (opE F l env ts) (lit F I d S))
    (h : zchk l S' (zaddM (zcM t.1 T) S) = true) : meq l (opE F l env (t :: ts)) (lit F I d S') := by
  have e1 : meq l (smul F (zi F t.1) (prodM F l env t.2)) (lit F I d (zcM t.1 T)) := fun i j hi hj => by
    show F.mul (zi F t.1) (prodM F l env t.2 i j) = lit F I d (zcM t.1 T) i j
    rw [hT i j hi hj]
    exact lit_smul F I l d t.1 T i j hi hj
  exact (matAlg F l hn).trans ((matAlg F l hn).add_congr e1 hS)
    ((matAlg F l hn).trans (lit_add F I l d _ _) ((matAlg F l hn).symm (lit_congr F I l d (zchk_sound h))))

/-- N_O·N_K = d·N_T, N_K·N_T = d·N_W, and q·N_W = p·N_K: P·O·P = (p/q)·P on integers -/
def scalarB (l : List Nat) (d : Nat) (NK NO NT NW : ZM) (p : Z2) (q : Nat) : Bool :=
  zchk l (zmm l NO NK) (zscM d NT) && zchk l (zmm l NK NT) (zscM d NW) && zchk l (zscM q NW) (zcM p NK)

include hn hd in
/-- THE QUANTUM VALUE, CHECKED ON INTEGERS: q·⟨ψ|O|ψ⟩ = p·⟨ψ|ψ⟩ in every state ψ of the knowledge -/
theorem scalar_z {NK NO NT NW : ZM} {p : Z2} {q : Nat} {O : Mat α} (GK : goodB l d NK = true)
    (hO : meq l O (lit F I d NO)) (h : scalarB l d NK NO NT NW p q = true) {ψ : Vec α}
    (hψ : veq l (mv F l (lit F I d NK) ψ) ψ) : F.mul (nat F q) (qf F l O ψ) = F.mul (zi F p) (ip F l ψ ψ) := by
  have h' := band3 _ _ _ h
  have R := matAlg F l hn
  have e1 : meq l (matMul F l (lit F I d NO) (lit F I d NK)) (lit F I d NT) := lit_mul_eq F I l d hd (zchk_sound h'.1)
  have e2 : meq l (matMul F l (lit F I d NK) (lit F I d NT)) (lit F I d NW) := lit_mul_eq F I l d hd (zchk_sound h'.2.1)
  have hW : meq l (matMul F l (lit F I d NK) (matMul F l (lit F I d NO) (lit F I d NK))) (lit F I d NW) :=
    (matAlg F l hn).trans ((matAlg F l hn).mul_congr ((matAlg F l hn).refl _) e1) e2
  have hab : ∀ i j, List.Mem i l → List.Mem j l →
      F.mul (nat F q) (lit F I d NW i j) = F.mul (zi F p) (lit F I d NK i j) := fun i j hi hj => by
    have z : zeq (zsc q (NW i j)) (zmul p (NK i j)) := zchk_sound h'.2.2 i j hi hj
    show F.mul (nat F q) (F.mul (sc F I d) (zi F (NW i j))) = F.mul (zi F p) (F.mul (sc F I d) (zi F (NK i j)))
    rw [mul_left_comm, ← zi_sc, zi_congr F z, zi_mul, mul_left_comm]
  rw [qf_congr F l hO ψ]
  exact scalar_on F l hn (good_z F I l hn d hd GK) hW hab hψ

include hn in
/-- 1·ψ = ψ -/
theorem mv_one (ψ : Vec α) : veq l (mv F l (matOne F) ψ) ψ := fun i hi => S_delta_l F ψ i l hn hi

include hn hd in
/-- when nothing is settled the knowledge is everything: every ψ is held -/
theorem held_all {NK : ZM} (h : zchk l NK (zone d) = true) (ψ : Vec α) : veq l (mv F l (lit F I d NK) ψ) ψ := fun i hi =>
  (mv_congr F l (lit_one F I l d hd (zchk_sound h)) (fun _ _ => rfl) i hi).trans (mv_one F l hn ψ i hi)

end QZ20

#print axioms QZ20.zleB_sound
#print axioms QZ20.allS_sound
#print axioms QZ20.sweep
#print axioms QZ20.classical_bound
#print axioms QZ20.classical_floor
#print axioms QZ20.scalar_on
#print axioms QZ20.lit_obs
#print axioms QZ20.prod_z
#print axioms QZ20.op_z
#print axioms QZ20.scalar_z
#print axioms QZ20.held_all
