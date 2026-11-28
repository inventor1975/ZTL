import ZNet
import ZRound
import QZ3
import QZ5
import QZ7
import QZ8
import QZ9
import QZ10

/-!
# QZ12 — Gram–Schmidt as projections: the symmetric projections of every dimension ARE a lattice, and the Born
weight is a probability of layer 3 on it with nothing handed in. Zero axioms.

(2026-11-28, the curator: "будешь делать?" - yes. Written with AI.)

QZ8 proved the Born weight a probability of layer 3 on ANY lattice of symmetric projections GIVEN (QZ7's `Rep`);
QZ11 gave one such lattice, of one qubit. Here the lattice is built, for every index list (every dimension):

  (1) vectors and what a matrix does to them  (`mv`, `ip_mv_sym`, `mv_mul`, `mat_ray`, `ray_mat`)
  (2) ONE STEP  `step J q`: a symmetric projection J and a vector q give the least symmetric projection above J that
      holds q - J itself when q is already held, else J plus the ray of the residual q − Jq
      (`good_step`, `step_fixes`, `step_keeps`, `step_least`)
  (3) THE JOIN of two projections: P, then the columns of Q one after another (`join`); it is above both
      (`le_join_l`, `le_join_r`) and below every symmetric projection that is (`join_le`)
  (4) THE LATTICE `projLat`: order p·q = p = q·p, negation 1 − P, that join, the meet through it (¬(¬P ∨ ¬Q)).
      `projRep`, `proj_closed`: it is a lattice of projections in the sense of QZ7 and QZ9, so
      `born_prob_all`    the Born weight ψᵀPψ is a probability of layer 3 on it - for every state ψ, every dimension
      `splits_iff_comm`  and a state splits along a question exactly when their projections commute.

No spans, no bases, no dimension count: every statement is about a matrix and what it does to a vector. This is
Gram–Schmidt, read as "add what is missing as a ray".

The field is any `ZNet.OF` with an inverse and a test for zero (`Inv`) - Logik2's `QOF.qOF` has both (QZ13).

WHAT IS NOT IN THIS FILE: (a) the tie to the judge's own representation - subspace.py keeps a subspace as a reduced
basis, this lattice keeps it as its projection; that the two agree is measured (rep_probe.py), not proved;
(b) amplitudes with a square root of two (no such field built), and complex amplitudes (the judge carries C^n as
R^2n; nothing here singles out the projections that respect the complex structure); (c) an Agda twin.

PRIOR WORK: the projection lattice of a finite-dimensional space is textbook (Birkhoff-von Neumann 1936); nothing
here is new mathematics. Ours: it is built on the kernel's own field, with no axiom, and feeds the kernel's layers.
-/

namespace QZ12
open ZNet ZRound QZ7 QZ8 QZ9 QZ10

variable {α : Type}

/-- a vector: entries by an index; only those of the index list matter -/
abbrev Vec (α : Type) := Nat → α

/-- equal entry by entry on the index list -/
def veq (l : List Nat) (u v : Vec α) : Prop := ∀ i, List.Mem i l → u i = v i
/-- the matrix applied to the vector -/
def mv (F : OF α) (l : List Nat) (M : Mat α) (v : Vec α) : Vec α := fun i => S F l (fun k => F.mul (M i k) (v k))
def vsub (F : OF α) (u v : Vec α) : Vec α := fun i => F.add (u i) (F.neg (v i))
def vzero (F : OF α) : Vec α := fun _ => F.zero
/-- a column of a matrix -/
def col (M : Mat α) (j : Nat) : Vec α := fun i => M i j

/-! ### vectors and matrices -/

theorem mv_congr (F : OF α) (l : List Nat) {M N : Mat α} {u v : Vec α} (hM : meq l M N) (hv : veq l u v) :
    veq l (mv F l M u) (mv F l N v) := fun i hi =>
  S_congr F l (fun k hk => by
    show F.mul (M i k) (u k) = F.mul (N i k) (v k)
    rw [hM i k hi hk, hv k hk])

theorem ip_congr (F : OF α) (l : List Nat) {u u' v v' : Vec α} (hu : veq l u u') (hv : veq l v v') :
    ip F l u v = ip F l u' v' :=
  S_congr F l (fun i hi => by
    show F.mul (u i) (v i) = F.mul (u' i) (v' i)
    rw [hu i hi, hv i hi])

theorem ip_zero_l (F : OF α) (l : List Nat) {u : Vec α} (h : veq l u (vzero F)) (v : Vec α) : ip F l u v = F.zero :=
  S_all_zero F l (fun i hi => by
    show F.mul (u i) (v i) = F.zero
    rw [h i hi]
    exact ZNet.zero_mul F (v i))

theorem ip_add_r (F : OF α) (l : List Nat) (u v w : Vec α) :
    ip F l u (fun i => F.add (v i) (w i)) = F.add (ip F l u v) (ip F l u w) := by
  show S F l (fun i => F.mul (u i) (F.add (v i) (w i))) = F.add (S F l (fun i => F.mul (u i) (v i))) (S F l (fun i => F.mul (u i) (w i)))
  rw [← S_add F _ _ l]
  exact S_congr F l (fun i _ => F.mul_add _ _ _)

/-- a symmetric matrix moves across the inner product: ⟨Mu, v⟩ = ⟨u, Mv⟩ -/
theorem ip_mv_sym (F : OF α) (l : List Nat) {M : Mat α} (hs : sym l M) (u v : Vec α) :
    ip F l (mv F l M u) v = ip F l u (mv F l M v) := by
  show S F l (fun i => F.mul (S F l (fun k => F.mul (M i k) (u k))) (v i)) =
    S F l (fun k => F.mul (u k) (S F l (fun i => F.mul (M k i) (v i))))
  rw [S_congr F l (fun i _ => (S_mul_right F (v i) (fun k => F.mul (M i k) (u k)) l).symm)]
  rw [S_swap F (fun i k => F.mul (F.mul (M i k) (u k)) (v i)) l l]
  exact S_congr F l (fun k hk => by
    show S F l (fun i => F.mul (F.mul (M i k) (u k)) (v i)) = F.mul (u k) (S F l (fun i => F.mul (M k i) (v i)))
    rw [← S_mul F (u k) (fun i => F.mul (M k i) (v i)) l]
    exact S_congr F l (fun i hi => by
      show F.mul (F.mul (M i k) (u k)) (v i) = F.mul (u k) (F.mul (M k i) (v i))
      rw [hs i k hi hk, F.mul_comm (M k i) (u k), F.mul_assoc]))

/-- the product of two matrices acts as one after the other -/
theorem mv_mul (F : OF α) (l : List Nat) (M N : Mat α) (v : Vec α) (i : Nat) :
    mv F l (matMul F l M N) v i = mv F l M (mv F l N v) i := by
  show S F l (fun k => F.mul (S F l (fun m => F.mul (M i m) (N m k))) (v k)) =
    S F l (fun m => F.mul (M i m) (S F l (fun k => F.mul (N m k) (v k))))
  rw [S_congr F l (fun k _ => (S_mul_right F (v k) (fun m => F.mul (M i m) (N m k)) l).symm)]
  rw [S_swap F (fun k m => F.mul (F.mul (M i m) (N m k)) (v k)) l l]
  exact S_congr F l (fun m _ => by
    rw [← S_mul F (M i m) (fun k => F.mul (N m k) (v k)) l]
    exact S_congr F l (fun k _ => F.mul_assoc _ _ _))

theorem mv_add_mat (F : OF α) (l : List Nat) (M N : Mat α) (v : Vec α) (i : Nat) :
    mv F l (matAdd F M N) v i = F.add (mv F l M v i) (mv F l N v i) := by
  show S F l (fun k => F.mul (F.add (M i k) (N i k)) (v k)) =
    F.add (S F l (fun k => F.mul (M i k) (v k))) (S F l (fun k => F.mul (N i k) (v k)))
  rw [← S_add F _ _ l]
  exact S_congr F l (fun k _ => ZNet.add_mul F _ _ _)

theorem mv_vsub (F : OF α) (l : List Nat) (M : Mat α) (u v : Vec α) (i : Nat) :
    mv F l M (vsub F u v) i = F.add (mv F l M u i) (F.neg (mv F l M v i)) := by
  show S F l (fun k => F.mul (M i k) (F.add (u k) (F.neg (v k)))) =
    F.add (S F l (fun k => F.mul (M i k) (u k))) (F.neg (S F l (fun k => F.mul (M i k) (v k))))
  rw [← S_neg F _ l, ← S_add F _ _ l]
  exact S_congr F l (fun k _ => by
    show F.mul (M i k) (F.add (u k) (F.neg (v k))) = F.add (F.mul (M i k) (u k)) (F.neg (F.mul (M i k) (v k)))
    rw [F.mul_add, ZNet.mul_neg])

/-- the ray applied to a vector: (c·⟨r, v⟩)·r -/
theorem mv_ray (F : OF α) (l : List Nat) (c : α) (r v : Vec α) (i : Nat) :
    mv F l (ray F c r) v i = F.mul (F.mul c (ip F l r v)) (r i) := by
  show S F l (fun k => F.mul (F.mul c (F.mul (r i) (r k))) (v k)) = F.mul (F.mul c (ip F l r v)) (r i)
  have h : ∀ k, F.mul (F.mul c (F.mul (r i) (r k))) (v k) = F.mul (F.mul c (r i)) (F.mul (r k) (v k)) := fun k => by
    rw [← F.mul_assoc c (r i) (r k), F.mul_assoc (F.mul c (r i)) (r k) (v k)]
  rw [S_congr F l (fun k _ => h k), S_mul F (F.mul c (r i)) (fun k => F.mul (r k) (v k)) l]
  show F.mul (F.mul c (r i)) (ip F l r v) = F.mul (F.mul c (ip F l r v)) (r i)
  rw [F.mul_assoc c (r i), F.mul_comm (r i), ← F.mul_assoc]

/-- a matrix times a ray: (M·ray)_ij = (c·(Mr)_i)·r_j -/
theorem mat_ray (F : OF α) (l : List Nat) (M : Mat α) (c : α) (r : Vec α) (i j : Nat) :
    matMul F l M (ray F c r) i j = F.mul (F.mul c (mv F l M r i)) (r j) := by
  show S F l (fun k => F.mul (M i k) (F.mul c (F.mul (r k) (r j)))) =
    F.mul (F.mul c (S F l (fun k => F.mul (M i k) (r k)))) (r j)
  have h : ∀ k, F.mul (M i k) (F.mul c (F.mul (r k) (r j))) = F.mul (F.mul c (r j)) (F.mul (M i k) (r k)) := fun k => by
    rw [F.mul_comm (r k) (r j), ← F.mul_assoc c (r j) (r k), ← F.mul_assoc (M i k) (F.mul c (r j)) (r k),
      F.mul_comm (M i k) (F.mul c (r j)), F.mul_assoc]
  rw [S_congr F l (fun k _ => h k), S_mul F (F.mul c (r j)) (fun k => F.mul (M i k) (r k)) l]
  rw [F.mul_assoc c (r j), F.mul_comm (r j), ← F.mul_assoc]

/-- a ray times a symmetric matrix: (ray·M)_ij = (c·r_i)·(Mr)_j -/
theorem ray_mat (F : OF α) (l : List Nat) {M : Mat α} (hs : sym l M) (c : α) (r : Vec α) (i j : Nat) (hj : List.Mem j l) :
    matMul F l (ray F c r) M i j = F.mul (F.mul c (r i)) (mv F l M r j) := by
  show S F l (fun k => F.mul (F.mul c (F.mul (r i) (r k))) (M k j)) =
    F.mul (F.mul c (r i)) (S F l (fun k => F.mul (M j k) (r k)))
  rw [← S_mul F (F.mul c (r i)) (fun k => F.mul (M j k) (r k)) l]
  exact S_congr F l (fun k hk => by
    show F.mul (F.mul c (F.mul (r i) (r k))) (M k j) = F.mul (F.mul c (r i)) (F.mul (M j k) (r k))
    rw [hs k j hk hj, ← F.mul_assoc c (r i) (r k), F.mul_assoc (F.mul c (r i)) (r k) (M j k), F.mul_comm (r k) (M j k)])

/-! ### a sum of squares that is zero -/

theorem zero_of_sum (F : OF α) {a b : α} (ha : F.le F.zero a) (hb : F.le F.zero b) (h : F.add a b = F.zero) : a = F.zero := by
  have h1 := F.add_le_add (F.le_refl a) hb
  rw [F.add_zero, h] at h1
  exact F.le_antisymm h1 ha

/-- ⟨r, r⟩ = 0 → r is zero on the index list -/
theorem zero_of_ip_self (F : OF α) (r : Vec α) : ∀ l, ip F l r r = F.zero → veq l r (vzero F)
  | [], _ => fun _ hi => nomatch hi
  | i :: l, h => by
      have h' : F.add (F.mul (r i) (r i)) (S F l (fun k => F.mul (r k) (r k))) = F.zero := h
      have hs : F.le F.zero (S F l (fun k => F.mul (r k) (r k))) := S_nonneg F l (fun k _ => F.sq_nonneg (r k))
      have h1 : F.mul (r i) (r i) = F.zero := zero_of_sum F (F.sq_nonneg (r i)) hs h'
      have h2 : S F l (fun k => F.mul (r k) (r k)) = F.zero := by
        rw [h1, ZNet.zero_add] at h'
        exact h'
      have hi0 : r i = F.zero := by
        cases F.mul_eq_zero h1 with
        | inl e => exact e
        | inr e => exact e
      intro k hk
      cases hk with
      | head => exact hi0
      | tail _ hk' => exact zero_of_ip_self F r l h2 k hk'

/-! ### one step: a projection and a vector -/

/-- an inverse and a test for zero (the kernel's ordered field has neither as a law) -/
structure Inv (F : OF α) where
  inv : α → α
  mul_inv : ∀ {a}, a ≠ F.zero → F.mul a (inv a) = F.one
  dec : ∀ a, Decidable (a = F.zero)

/-- a symmetric projection -/
structure Good (F : OF α) (l : List Nat) (hn : NoDup l) (J : Mat α) : Prop where
  sy : sym l J
  pr : IsP (matAlg F l hn) J

/-- what J does not hold of q: q − Jq -/
def resid (F : OF α) (l : List Nat) (J : Mat α) (q : Vec α) : Vec α := vsub F q (mv F l J q)

/-- THE STEP: J when q is already held, else J plus the ray of the residual -/
def step (F : OF α) (I : Inv F) (l : List Nat) (J : Mat α) (q : Vec α) : Mat α :=
  @ite _ (ip F l (resid F l J q) (resid F l J q) = F.zero) (I.dec _) J
    (matAdd F J (ray F (I.inv (ip F l (resid F l J q) (resid F l J q))) (resid F l J q)))

theorem step_zero (F : OF α) (I : Inv F) (l : List Nat) (J : Mat α) (q : Vec α)
    (h : ip F l (resid F l J q) (resid F l J q) = F.zero) : step F I l J q = J := @if_pos _ (I.dec _) h _ _ _

theorem step_pos (F : OF α) (I : Inv F) (l : List Nat) (J : Mat α) (q : Vec α)
    (h : ¬ ip F l (resid F l J q) (resid F l J q) = F.zero) :
    step F I l J q = matAdd F J (ray F (I.inv (ip F l (resid F l J q) (resid F l J q))) (resid F l J q)) :=
  @if_neg _ (I.dec _) h _ _ _

variable (F : OF α) (I : Inv F) (l : List Nat) (hn : NoDup l)

/-- J kills the residual: J(q − Jq) = Jq − JJq = 0 -/
theorem J_resid {J : Mat α} (G : Good F l hn J) (q : Vec α) : veq l (mv F l J (resid F l J q)) (vzero F) := by
  intro i hi
  show mv F l J (vsub F q (mv F l J q)) i = F.zero
  have e : mv F l J (mv F l J q) i = mv F l J q i := by
    rw [← mv_mul]
    exact mv_congr F l G.pr (fun _ _ => rfl) i hi
  rw [mv_vsub, e]
  exact F.add_neg _

/-- so the ray of the residual is orthogonal to J -/
theorem resid_orth {J : Mat α} (G : Good F l hn J) (q : Vec α) (c : α) :
    Orth (matAlg F l hn) J (ray F c (resid F l J q)) := by
  constructor
  · intro i j hi _
    show matMul F l J (ray F c (resid F l J q)) i j = F.zero
    rw [mat_ray, J_resid F l hn G q i hi]
    show F.mul (F.mul c F.zero) (resid F l J q j) = F.zero
    rw [F.mul_zero, ZNet.zero_mul]
  · intro i j _ hj
    show matMul F l (ray F c (resid F l J q)) J i j = F.zero
    rw [ray_mat F l G.sy c _ i j hj, J_resid F l hn G q j hj]
    exact F.mul_zero _

theorem inv_unit {x : α} (h : ¬ x = F.zero) : F.mul (I.inv x) x = F.one := by
  rw [F.mul_comm]
  exact I.mul_inv h

/-- the step keeps a symmetric projection -/
theorem good_step {J : Mat α} (G : Good F l hn J) (q : Vec α) : Good F l hn (step F I l J q) :=
  @Decidable.byCases _ _ (I.dec (ip F l (resid F l J q) (resid F l J q)))
    (fun h => by rw [step_zero F I l J q h]; exact G)
    (fun h => by
      rw [step_pos F I l J q h]
      exact ⟨fun i j hi hj => by
          show F.add (J i j) (ray F _ (resid F l J q) i j) = F.add (J j i) (ray F _ (resid F l J q) j i)
          rw [G.sy i j hi hj, ray_sym F l _ (resid F l J q) i j hi hj],
        isP_add (matAlg F l hn) G.pr (ray_isP F l hn _ _ (inv_unit F I h)) (resid_orth F l hn G q _)⟩)

/-- the step is above J -/
theorem le_step {J : Mat α} (G : Good F l hn J) (q : Vec α) : Le (matAlg F l hn) J (step F I l J q) :=
  @Decidable.byCases _ _ (I.dec (ip F l (resid F l J q) (resid F l J q)))
    (fun h => by rw [step_zero F I l J q h]; exact ⟨G.pr, G.pr⟩)
    (fun h => by rw [step_pos F I l J q h]; exact le_add_l (matAlg F l hn) G.pr (resid_orth F l hn G q _))

/-- THE STEP HOLDS q -/
theorem step_fixes {J : Mat α} (G : Good F l hn J) (q : Vec α) : veq l (mv F l (step F I l J q) q) q :=
  @Decidable.byCases _ _ (I.dec (ip F l (resid F l J q) (resid F l J q)))
    (fun h => by
      rw [step_zero F I l J q h]
      intro i hi
      have hz : F.add (q i) (F.neg (mv F l J q i)) = F.zero := zero_of_ip_self F _ l h i hi
      have e := eq_neg_of_add F hz
      rw [F.neg_neg] at e
      exact e.symm)
    (fun h => by
      rw [step_pos F I l J q h]
      intro i hi
      have hq : veq l q (fun k => F.add (resid F l J q k) (mv F l J q k)) := fun k _ => by
        show q k = F.add (F.add (q k) (F.neg (mv F l J q k))) (mv F l J q k)
        rw [F.add_assoc, F.add_comm (F.neg (mv F l J q k)), F.add_neg, F.add_zero]
      have e0 : ip F l (resid F l J q) (mv F l J q) = F.zero := by
        rw [← ip_mv_sym F l G.sy]
        exact ip_zero_l F l (J_resid F l hn G q) q
      have e1 : ip F l (resid F l J q) q = ip F l (resid F l J q) (resid F l J q) := by
        rw [ip_congr F l (fun _ _ => rfl) hq, ip_add_r, e0, F.add_zero]
      rw [mv_add_mat, mv_ray, e1, inv_unit F I h, ZRound.one_mul]
      show F.add (mv F l J q i) (F.add (q i) (F.neg (mv F l J q i))) = q i
      rw [F.add_comm (q i), ← F.add_assoc, F.add_neg, ZNet.zero_add])

/-- …and keeps what J held -/
theorem step_keeps {J : Mat α} (G : Good F l hn J) (q : Vec α) {u : Vec α} (hu : veq l (mv F l J u) u) :
    veq l (mv F l (step F I l J q) u) u :=
  @Decidable.byCases _ _ (I.dec (ip F l (resid F l J q) (resid F l J q)))
    (fun h => by rw [step_zero F I l J q h]; exact hu)
    (fun h => by
      rw [step_pos F I l J q h]
      intro i hi
      have e0 : ip F l (resid F l J q) u = F.zero := by
        rw [ip_congr F l (fun _ _ => rfl) (fun k hk => (hu k hk).symm), ← ip_mv_sym F l G.sy]
        exact ip_zero_l F l (J_resid F l hn G q) u
      rw [mv_add_mat, mv_ray, e0, F.mul_zero, ZNet.zero_mul, F.add_zero]
      exact hu i hi)

/-- THE STEP IS THE LEAST: a symmetric projection above J that holds q is above the step -/
theorem step_least {J R : Mat α} (GR : Good F l hn R) (q : Vec α) (hJR : Le (matAlg F l hn) J R)
    (hq : veq l (mv F l R q) q) : Le (matAlg F l hn) (step F I l J q) R :=
  @Decidable.byCases _ _ (I.dec (ip F l (resid F l J q) (resid F l J q)))
    (fun h => by rw [step_zero F I l J q h]; exact hJR)
    (fun h => by
      rw [step_pos F I l J q h]
      have hRr : veq l (mv F l R (resid F l J q)) (resid F l J q) := by
        intro i hi
        show mv F l R (vsub F q (mv F l J q)) i = F.add (q i) (F.neg (mv F l J q i))
        have e : mv F l R (mv F l J q) i = mv F l J q i := by
          rw [← mv_mul]
          exact mv_congr F l hJR.2 (fun _ _ => rfl) i hi
        rw [mv_vsub, e, hq i hi]
      refine add_le (matAlg F l hn) hJR ⟨?_, ?_⟩
      · intro i j _ hj
        show matMul F l (ray F _ (resid F l J q)) R i j = ray F _ (resid F l J q) i j
        rw [ray_mat F l GR.sy _ _ i j hj, hRr j hj]
        exact F.mul_assoc _ _ _
      · intro i j hi _
        show matMul F l R (ray F _ (resid F l J q)) i j = ray F _ (resid F l J q) i j
        rw [mat_ray, hRr i hi]
        exact F.mul_assoc _ _ _)

/-! ### many vectors, one after another -/

/-- J, then the vectors of the list one after another -/
def gs : Mat α → List (Vec α) → Mat α
  | J, [] => J
  | J, q :: qs => gs (step F I l J q) qs

/-- the matrix holds every vector of the list -/
def AllFixed (M : Mat α) : List (Vec α) → Prop
  | [] => True
  | q :: qs => veq l (mv F l M q) q ∧ AllFixed M qs

theorem le_refl_good {J : Mat α} (G : Good F l hn J) : Le (matAlg F l hn) J J := ⟨G.pr, G.pr⟩

/-- the order of projections is transitive (the matrices are associative) -/
theorem le_trans_alg {A : Type} {R : Alg A} (hA : Assoc R) {p q r : A} (h1 : Le R p q) (h2 : Le R q r) : Le R p r :=
  ⟨R.trans (R.mul_congr (R.symm h1.1) (R.refl r)) (R.trans (hA p q r) (R.trans (R.mul_congr (R.refl p) h2.1) h1.1)),
   R.trans (R.mul_congr (R.refl r) (R.symm h1.2)) (R.trans (R.symm (hA r q p)) (R.trans (R.mul_congr h2.2 (R.refl p)) h1.2))⟩

theorem gs_good : ∀ (qs : List (Vec α)) {J : Mat α}, Good F l hn J → Good F l hn (gs F I l J qs)
  | [], _, G => G
  | q :: qs, _, G => gs_good qs (good_step F I l hn G q)

theorem gs_le : ∀ (qs : List (Vec α)) {J : Mat α}, Good F l hn J → Le (matAlg F l hn) J (gs F I l J qs)
  | [], _, G => le_refl_good F l hn G
  | q :: qs, _, G =>
      le_trans_alg (mat_assoc F l hn) (le_step F I l hn G q) (gs_le qs (good_step F I l hn G q))

theorem gs_keeps : ∀ (qs : List (Vec α)) {J : Mat α}, Good F l hn J → ∀ {u : Vec α}, veq l (mv F l J u) u →
    veq l (mv F l (gs F I l J qs) u) u
  | [], _, _, _, hu => hu
  | q :: qs, _, G, _, hu => gs_keeps qs (good_step F I l hn G q) (step_keeps F I l hn G q hu)

theorem gs_fixes : ∀ (qs : List (Vec α)) {J : Mat α}, Good F l hn J → AllFixed F l (gs F I l J qs) qs
  | [], _, _ => True.intro
  | q :: qs, _, G =>
      ⟨gs_keeps F I l hn qs (good_step F I l hn G q) (step_fixes F I l hn G q), gs_fixes qs (good_step F I l hn G q)⟩

theorem gs_least {R : Mat α} (GR : Good F l hn R) : ∀ (qs : List (Vec α)) {J : Mat α}, Le (matAlg F l hn) J R →
    AllFixed F l R qs → Le (matAlg F l hn) (gs F I l J qs) R
  | [], _, h, _ => h
  | q :: qs, _, h, hf => gs_least GR qs (step_least F I l hn GR q h hf.1) hf.2

/-! ### the join of two projections -/

/-- the columns of a matrix, for the indices of a list -/
def cols (Q : Mat α) : List Nat → List (Vec α)
  | [] => []
  | j :: js => col Q j :: cols Q js

/-- THE JOIN: P, then the columns of Q -/
def join (P Q : Mat α) : Mat α := gs F I l P (cols Q l)

theorem allFixed_cols {M Q : Mat α} : ∀ js, AllFixed F l M (cols Q js) → ∀ j, List.Mem j js → veq l (mv F l M (col Q j)) (col Q j)
  | [], _, _, hj => nomatch hj
  | j0 :: js, h, j, hj => by
      cases hj with
      | head => exact h.1
      | tail _ hj' => exact allFixed_cols js h.2 j hj'

theorem cols_allFixed {M Q : Mat α} : ∀ js, (∀ j, List.Mem j js → veq l (mv F l M (col Q j)) (col Q j)) → AllFixed F l M (cols Q js)
  | [], _ => True.intro
  | j0 :: js, h => ⟨h j0 (List.Mem.head _), cols_allFixed js (fun j hj => h j (List.Mem.tail _ hj))⟩

/-- a matrix that holds the columns of Q, both symmetric: Q is a part of it -/
theorem le_of_cols {M Q : Mat α} (sM : sym l M) (sQ : sym l Q)
    (h : ∀ j, List.Mem j l → veq l (mv F l M (col Q j)) (col Q j)) : Le (matAlg F l hn) Q M := by
  have hMQ : meq l (matMul F l M Q) Q := fun i j hi hj => h j hj i hi
  refine ⟨?_, hMQ⟩
  intro i j hi hj
  show S F l (fun k => F.mul (Q i k) (M k j)) = Q i j
  have e : S F l (fun k => F.mul (Q i k) (M k j)) = matMul F l M Q j i :=
    S_congr F l (fun k hk => by
      show F.mul (Q i k) (M k j) = F.mul (M j k) (Q k i)
      rw [sQ i k hi hk, sM k j hk hj, F.mul_comm])
  rw [e, hMQ j i hj hi, sQ j i hj hi]

/-- …and the other way: a part of M has its columns held by M -/
theorem cols_of_le {M Q : Mat α} (h : Le (matAlg F l hn) Q M) : ∀ j, List.Mem j l → veq l (mv F l M (col Q j)) (col Q j) :=
  fun j hj i hi => h.2 i j hi hj

theorem join_good {P Q : Mat α} (GP : Good F l hn P) : Good F l hn (join F I l P Q) := gs_good F I l hn _ GP

/-- P ≤ P ∨ Q -/
theorem le_join_l {P Q : Mat α} (GP : Good F l hn P) : Le (matAlg F l hn) P (join F I l P Q) := gs_le F I l hn _ GP

/-- Q ≤ P ∨ Q -/
theorem le_join_r {P Q : Mat α} (GP : Good F l hn P) (GQ : Good F l hn Q) : Le (matAlg F l hn) Q (join F I l P Q) :=
  le_of_cols F l hn (join_good F I l hn GP).sy GQ.sy (allFixed_cols F l l (gs_fixes F I l hn (cols Q l) GP))

/-- THE JOIN IS THE LEAST UPPER BOUND among the symmetric projections -/
theorem join_le {P Q R : Mat α} (GR : Good F l hn R) (hP : Le (matAlg F l hn) P R) (hQ : Le (matAlg F l hn) Q R) :
    Le (matAlg F l hn) (join F I l P Q) R :=
  gs_least F I l hn GR (cols Q l) hP (cols_allFixed F l l (cols_of_le F l hn hQ))

/-! ### the lattice of ALL symmetric projections -/

/-- ¬ is antitone, in any algebra of QZ7: p ≤ q → 1 − q ≤ 1 − p -/
theorem ng_anti {A : Type} (R : Alg A) {p q : A} (h : Le R p q) : Le R (ng R q) (ng R p) :=
  ⟨R.trans (R.mul_sub (R.sub R.one q) R.one p)
     (R.trans (R.sub_congr (R.mul_one _) (R.trans (R.sub_mul R.one q p) (R.trans (R.sub_congr (R.one_mul p) h.2) (R.sub_self p))))
       (R.sub_zero _)),
   R.trans (R.sub_mul R.one p (R.sub R.one q))
     (R.trans (R.sub_congr (R.one_mul _) (R.trans (R.mul_sub p R.one q) (R.trans (R.sub_congr (R.mul_one p) h.1) (R.sub_self p))))
       (R.sub_zero _))⟩

/-- every operator's projection is a part of 1 -/
theorem le_one_alg {A : Type} (R : Alg A) (p : A) : Le R p R.one := ⟨R.mul_one p, R.one_mul p⟩

/-- 1 − (1 − P) = P, entry by entry -/
theorem mat_ng_ng (P : Mat α) : meq l (matSub F (matOne F) (matSub F (matOne F) P)) P := fun i j _ _ => by
  show F.add (matOne F i j) (F.neg (F.add (matOne F i j) (F.neg (P i j)))) = P i j
  rw [ZNet.neg_add, F.neg_neg, ← F.add_assoc, F.add_neg, ZNet.zero_add]

theorem one_sym : sym l (matOne F) := fun i j _ _ => by
  show (if i = j then F.one else F.zero) = (if j = i then F.one else F.zero)
  match Nat.decEq i j with
  | isTrue h => rw [if_pos h, if_pos h.symm]
  | isFalse h => rw [if_neg h, if_neg (fun e => h e.symm)]

theorem good_one : Good F l hn (matOne F) := ⟨one_sym F l, (matAlg F l hn).mul_one (matOne F)⟩
theorem good_zero : Good F l hn (matZero F) := ⟨fun _ _ _ _ => rfl, zero_isP F l hn⟩

theorem good_ng {P : Mat α} (G : Good F l hn P) : Good F l hn (matSub F (matOne F) P) :=
  ⟨fun i j hi hj => by
      show F.add (matOne F i j) (F.neg (P i j)) = F.add (matOne F j i) (F.neg (P j i))
      rw [one_sym F l i j hi hj, G.sy i j hi hj],
   isP_ng (matAlg F l hn) G.pr⟩

theorem good_add {P Q : Mat α} (GP : Good F l hn P) (GQ : Good F l hn Q) (h : Orth (matAlg F l hn) P Q) :
    Good F l hn (matAdd F P Q) :=
  ⟨fun i j hi hj => by
      show F.add (P i j) (Q i j) = F.add (P j i) (Q j i)
      rw [GP.sy i j hi hj, GQ.sy i j hi hj],
   isP_add (matAlg F l hn) GP.pr GQ.pr h⟩

/-- the product of two commuting symmetric projections is one -/
theorem good_mul {P Q : Mat α} (GP : Good F l hn P) (GQ : Good F l hn Q) (h : Comm (matAlg F l hn) P Q) :
    Good F l hn (matMul F l P Q) :=
  ⟨fun i j hi hj => by
      show S F l (fun k => F.mul (P i k) (Q k j)) = S F l (fun k => F.mul (P j k) (Q k i))
      have e : S F l (fun k => F.mul (P i k) (Q k j)) = matMul F l Q P i j := h i j hi hj
      rw [e]
      exact S_congr F l (fun k hk => by
        show F.mul (Q i k) (P k j) = F.mul (P j k) (Q k i)
        rw [GQ.sy i k hi hk, GP.sy k j hk hj, F.mul_comm]),
   (le_mul (mat_assoc F l hn) (mul_le_l (mat_assoc F l hn) GP.pr h) (mul_le_r (mat_assoc F l hn) GQ.pr h)).1⟩

/-- a symmetric projection of the matrices over the index list -/
def Proj : Type := {J : Mat α // Good F l hn J}

/-- THE LATTICE OF ALL SYMMETRIC PROJECTIONS: the order of QZ7, 1 − P, the join by Gram–Schmidt, the meet through it -/
def projLat : QZ3.NLat (Proj F l hn) where
  le := fun x y => Le (matAlg F l hn) x.1 y.1
  join := fun x y => ⟨join F I l x.1 y.1, join_good F I l hn x.2⟩
  neg := fun x => ⟨matSub F (matOne F) x.1, good_ng F l hn x.2⟩
  meet := fun x y =>
    ⟨matSub F (matOne F) (join F I l (matSub F (matOne F) x.1) (matSub F (matOne F) y.1)),
     good_ng F l hn (join_good F I l hn (good_ng F l hn x.2))⟩
  top := ⟨matOne F, good_one F l hn⟩
  bot := ⟨matZero F, good_zero F l hn⟩
  le_trans := fun h1 h2 => le_trans_alg (mat_assoc F l hn) h1 h2
  meet_le_l := fun x _ =>
    le_congr (matAlg F l hn) (fun _ _ _ _ => rfl) (mat_ng_ng F l x.1)
      (ng_anti (matAlg F l hn) (le_join_l F I l hn (good_ng F l hn x.2)))
  meet_le_r := fun x y =>
    le_congr (matAlg F l hn) (fun _ _ _ _ => rfl) (mat_ng_ng F l y.1)
      (ng_anti (matAlg F l hn) (le_join_r F I l hn (good_ng F l hn x.2) (good_ng F l hn y.2)))
  le_meet := fun {s _ _} h1 h2 =>
    le_congr (matAlg F l hn) (mat_ng_ng F l s.1) (fun _ _ _ _ => rfl)
      (ng_anti (matAlg F l hn)
        (join_le F I l hn (good_ng F l hn s.2) (ng_anti (matAlg F l hn) h1) (ng_anti (matAlg F l hn) h2)))
  le_join_l := fun x _ => le_join_l F I l hn x.2
  le_join_r := fun x y => le_join_r F I l hn x.2 y.2
  join_le := fun {_ _ c} h1 h2 => join_le F I l hn c.2 h1 h2
  anti := fun h => ng_anti (matAlg F l hn) h
  le_nn := fun x =>
    le_congr (matAlg F l hn) (fun _ _ _ _ => rfl) (fun i j hi hj => (mat_ng_ng F l x.1 i j hi hj).symm)
      (le_refl_good F l hn x.2)
  le_top := fun x => le_one_alg (matAlg F l hn) x.1
  le_neg_bot := fun x =>
    le_congr (matAlg F l hn) (fun _ _ _ _ => rfl)
      (fun i j hi hj => ((matAlg F l hn).sub_zero (matOne F) i j hi hj).symm) (le_one_alg (matAlg F l hn) x.1)

/-- it is a lattice of projections in the sense of QZ7 (it holds every sum of orthogonal members)… -/
def projRep : Rep (matAlg F l hn) (projLat F I l hn) where
  e := fun x => x.1
  isP := fun x => x.2.pr
  le_to := fun h => h
  le_of := fun h => h
  neg := fun _ _ _ _ _ => rfl
  top := fun _ _ _ _ => rfl
  bot := fun _ _ _ _ => rfl
  sum := fun x y h => ⟨⟨matAdd F x.1 y.1, good_add F l hn x.2 y.2 h⟩, fun _ _ _ _ => rfl⟩

/-- …and of QZ9 (it holds every product of commuting members) -/
theorem proj_closed : Closed (projRep F I l hn) :=
  fun x y h => ⟨⟨matMul F l x.1 y.1, good_mul F l hn x.2 y.2 h⟩, fun _ _ _ _ => rfl⟩

/-- THE BORN WEIGHT IS A PROBABILITY OF LAYER 3 ON THE LATTICE OF ALL SYMMETRIC PROJECTIONS, in every dimension:
no lattice is handed in any more -/
def born_prob_all (mm : MinMax F) (ψ : Vec α) :
    QZ5.Prob (projLat F I l hn) (scale F mm (qf F l (matOne F) ψ)) :=
  born_prob F l hn mm ψ (projRep F I l hn) (fun x => x.2.sy)

/-- A STATE SPLITS ALONG A QUESTION EXACTLY WHEN THE PROJECTIONS COMMUTE, in that lattice -/
theorem splits_iff_comm (s a : Proj F l hn) :
    (projLat F I l hn).le s ((projLat F I l hn).join ((projLat F I l hn).meet s a) ((projLat F I l hn).meet s ((projLat F I l hn).neg a)))
      ↔ Comm (matAlg F l hn) s.1 a.1 :=
  ⟨fun h => split_comm (projRep F I l hn) s a h,
   fun h => comm_split (mat_assoc F l hn) (projRep F I l hn) (proj_closed F I l hn) s a h⟩

end QZ12

#print axioms QZ12.ip_mv_sym
#print axioms QZ12.mv_mul
#print axioms QZ12.mv_ray
#print axioms QZ12.mat_ray
#print axioms QZ12.ray_mat
#print axioms QZ12.zero_of_ip_self
#print axioms QZ12.good_step
#print axioms QZ12.step_fixes
#print axioms QZ12.step_keeps
#print axioms QZ12.step_least
#print axioms QZ12.gs_fixes
#print axioms QZ12.gs_least
#print axioms QZ12.join_good
#print axioms QZ12.le_join_l
#print axioms QZ12.le_join_r
#print axioms QZ12.join_le
#print axioms QZ12.ng_anti
#print axioms QZ12.good_mul
#print axioms QZ12.projLat
#print axioms QZ12.projRep
#print axioms QZ12.proj_closed
#print axioms QZ12.born_prob_all
#print axioms QZ12.splits_iff_comm
