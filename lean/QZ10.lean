import ZNet
import ZRound
import QZ3
import QZ5
import QZ7
import QZ8

/-!
# QZ10 — the projection on a ray, and the Born rule in its textbook form: ψᵀPψ = ⟨v,ψ⟩² / ⟨v,v⟩. Zero axioms.

(2026-11-28, the curator: "работай далее". Written with AI.)

QZ8 proves that the Born weight ψᵀPψ meets layer 3 on any lattice of symmetric projections. This file exhibits
the simplest such projections and computes the weight on them, over any ordered field of the kernel (`ZNet.OF`):

  `ray c v`        the matrix c·v_i·v_j, where c is the inverse of ⟨v,v⟩ (given as a number with c·⟨v,v⟩ = 1 - the
                   field of the kernel has no division of its own)
  `ray_isP`, `ray_sym`   it is a symmetric projection
  `ray_orth`       the rays of two orthogonal vectors are orthogonal projections
  `born_ray`       ψᵀ(ray c v)ψ = c·⟨v,ψ⟩²                — the Born rule for one outcome, as a theorem
  `frame2_isP`, `born_frame2`   two orthogonal rays: their sum is a projection and its weight is the sum
  `frame_isP`, `frame_sym`, `born_frame`   a whole ORTHOGONAL FAMILY (a list): the sum of its rays is a symmetric
                   projection and its weight is Σ c_k·⟨v_k,ψ⟩² - the Born rule for an event with several outcomes;
                   `born_frame_nonneg`: so that sum of squares is the weight QZ8 speaks of

WHAT IS STILL NOT PROVED: that every subspace HAS an orthogonal basis (Gram–Schmidt needs the division, and an
induction on the spanning list), and that the subspaces so obtained form the lattice of QZ7's `Rep`.
-/

namespace QZ10
open ZNet ZRound QZ7 QZ8

variable {α : Type}

/-- the inner product over the index list -/
def ip (F : OF α) (l : List Nat) (u v : Nat → α) : α := S F l (fun i => F.mul (u i) (v i))

theorem ip_comm (F : OF α) (l : List Nat) (u v : Nat → α) : ip F l u v = ip F l v u :=
  S_congr F l (fun i _ => F.mul_comm (u i) (v i))

/-- the projection on the ray of v: c·v_i·v_j, with c the inverse of ⟨v,v⟩ -/
def ray (F : OF α) (c : α) (v : Nat → α) : Mat α := fun i j => F.mul c (F.mul (v i) (v j))

theorem ray_sym (F : OF α) (l : List Nat) (c : α) (v : Nat → α) : sym l (ray F c v) := fun i j _ _ => by
  show F.mul c (F.mul (v i) (v j)) = F.mul c (F.mul (v j) (v i))
  rw [F.mul_comm (v i) (v j)]

/-- the product of two rays: (c·u_i u_k)(d·v_k v_j) summed over k is (c·d·⟨u,v⟩)·u_i v_j -/
theorem ray_mul (F : OF α) (l : List Nat) (c d : α) (u v : Nat → α) (i j : Nat) :
    matMul F l (ray F c u) (ray F d v) i j = F.mul (F.mul (F.mul c d) (ip F l u v)) (F.mul (u i) (v j)) := by
  show S F l (fun k => F.mul (F.mul c (F.mul (u i) (u k))) (F.mul d (F.mul (v k) (v j)))) =
    F.mul (F.mul (F.mul c d) (ip F l u v)) (F.mul (u i) (v j))
  have h : ∀ k, F.mul (F.mul c (F.mul (u i) (u k))) (F.mul d (F.mul (v k) (v j))) =
      F.mul (F.mul (F.mul c d) (F.mul (u i) (v j))) (F.mul (u k) (v k)) := by
    intro k
    rw [mul4 F c (F.mul (u i) (u k)) d (F.mul (v k) (v j)), F.mul_comm (v k) (v j),
      mul4 F (u i) (u k) (v j) (v k), ← F.mul_assoc]
  rw [S_congr F l (fun k _ => h k), S_mul F _ (fun k => F.mul (u k) (v k)) l]
  show F.mul (F.mul (F.mul c d) (F.mul (u i) (v j))) (ip F l u v) =
    F.mul (F.mul (F.mul c d) (ip F l u v)) (F.mul (u i) (v j))
  rw [F.mul_assoc (F.mul c d), F.mul_comm (F.mul (u i) (v j)), ← F.mul_assoc]

/-- THE RAY IS A PROJECTION (c·⟨v,v⟩ = 1) -/
theorem ray_isP (F : OF α) (l : List Nat) (hn : NoDup l) (c : α) (v : Nat → α) (h : F.mul c (ip F l v v) = F.one) :
    IsP (matAlg F l hn) (ray F c v) := by
  intro i j _ _
  show matMul F l (ray F c v) (ray F c v) i j = ray F c v i j
  rw [ray_mul, F.mul_assoc c c, h, F.mul_one]
  rfl

/-- THE RAYS OF TWO ORTHOGONAL VECTORS ARE ORTHOGONAL PROJECTIONS -/
theorem ray_orth (F : OF α) (l : List Nat) (hn : NoDup l) (c d : α) (u v : Nat → α) (h : ip F l u v = F.zero) :
    Orth (matAlg F l hn) (ray F c u) (ray F d v) := by
  constructor
  · intro i j _ _
    show matMul F l (ray F c u) (ray F d v) i j = F.zero
    rw [ray_mul, h, F.mul_zero, ZNet.zero_mul]
  · intro i j _ _
    show matMul F l (ray F d v) (ray F c u) i j = F.zero
    rw [ray_mul, ip_comm, h, F.mul_zero, ZNet.zero_mul]

/-- THE BORN RULE FOR ONE OUTCOME: ψᵀ(ray c v)ψ = c·⟨v,ψ⟩² -/
theorem born_ray (F : OF α) (l : List Nat) (c : α) (v ψ : Nat → α) :
    qf F l (ray F c v) ψ = F.mul c (F.mul (ip F l v ψ) (ip F l v ψ)) := by
  unfold qf
  have h : ∀ i j, F.mul (ψ i) (F.mul (ray F c v i j) (ψ j)) =
      F.mul c (F.mul (F.mul (v i) (ψ i)) (F.mul (v j) (ψ j))) := by
    intro i j
    show F.mul (ψ i) (F.mul (F.mul c (F.mul (v i) (v j))) (ψ j)) = F.mul c (F.mul (F.mul (v i) (ψ i)) (F.mul (v j) (ψ j)))
    rw [F.mul_assoc c (F.mul (v i) (v j)) (ψ j), ← F.mul_assoc (ψ i) c, F.mul_comm (ψ i) c, F.mul_assoc c (ψ i),
      F.mul_assoc (v i) (v j) (ψ j), ← F.mul_assoc (ψ i) (v i), F.mul_comm (ψ i) (v i)]
  rw [S_congr F l (fun i _ => S_congr F l (fun j _ => h i j))]
  rw [S_congr F l (fun i _ => S_mul F c (fun j => F.mul (F.mul (v i) (ψ i)) (F.mul (v j) (ψ j))) l)]
  rw [S_mul F c (fun i => S F l (fun j => F.mul (F.mul (v i) (ψ i)) (F.mul (v j) (ψ j)))) l]
  rw [S_prod F (fun i => F.mul (v i) (ψ i)) (fun j => F.mul (v j) (ψ j)) l]
  rfl

/-- the weight of a ray is not negative (the general fact of QZ8, here for the ray) -/
theorem born_ray_nonneg (F : OF α) (l : List Nat) (hn : NoDup l) (c : α) (v ψ : Nat → α)
    (h : F.mul c (ip F l v v) = F.one) : F.le F.zero (qf F l (ray F c v) ψ) :=
  born_nonneg F l ψ (ray_isP F l hn c v h) (ray_sym F l c v)

/-- TWO ORTHOGONAL RAYS: their sum is a symmetric projection… -/
theorem frame2_isP (F : OF α) (l : List Nat) (hn : NoDup l) (c d : α) (u v : Nat → α)
    (hu : F.mul c (ip F l u u) = F.one) (hv : F.mul d (ip F l v v) = F.one) (h : ip F l u v = F.zero) :
    IsP (matAlg F l hn) (matAdd F (ray F c u) (ray F d v)) :=
  isP_add (matAlg F l hn) (ray_isP F l hn c u hu) (ray_isP F l hn d v hv) (ray_orth F l hn c d u v h)

/-- …and its Born weight is the sum of the two outcomes' weights: c·⟨u,ψ⟩² + d·⟨v,ψ⟩² -/
theorem born_frame2 (F : OF α) (l : List Nat) (c d : α) (u v ψ : Nat → α) :
    qf F l (matAdd F (ray F c u) (ray F d v)) ψ =
      F.add (F.mul c (F.mul (ip F l u ψ) (ip F l u ψ))) (F.mul d (F.mul (ip F l v ψ) (ip F l v ψ))) := by
  rw [← born_ray F l c u ψ, ← born_ray F l d v ψ]
  exact qf_add F l (ray F c u) (ray F d v) ψ

/-! ### a whole orthogonal family: an event with several outcomes -/

/-- the sum of the rays of a family (c_k, v_k) -/
def frame (F : OF α) : List (α × (Nat → α)) → Mat α
  | [] => matZero F
  | cv :: fs => matAdd F (ray F cv.1 cv.2) (frame F fs)

/-- every c_k is the inverse of ⟨v_k, v_k⟩ -/
def Normed (F : OF α) (l : List Nat) : List (α × (Nat → α)) → Prop
  | [] => True
  | cv :: fs => F.mul cv.1 (ip F l cv.2 cv.2) = F.one ∧ Normed F l fs

/-- u is orthogonal to every vector of the family -/
def OrthTo (F : OF α) (l : List Nat) (u : Nat → α) : List (α × (Nat → α)) → Prop
  | [] => True
  | cv :: fs => ip F l u cv.2 = F.zero ∧ OrthTo F l u fs

/-- the vectors of the family are orthogonal to one another -/
def OrthFam (F : OF α) (l : List Nat) : List (α × (Nat → α)) → Prop
  | [] => True
  | cv :: fs => OrthTo F l cv.2 fs ∧ OrthFam F l fs

/-- the sum of the outcomes' weights: Σ c_k·⟨v_k, ψ⟩² -/
def wsum (F : OF α) (l : List Nat) (ψ : Nat → α) : List (α × (Nat → α)) → α
  | [] => F.zero
  | cv :: fs => F.add (F.mul cv.1 (F.mul (ip F l cv.2 ψ) (ip F l cv.2 ψ))) (wsum F l ψ fs)

theorem zero_isP (F : OF α) (l : List Nat) (hn : NoDup l) : IsP (matAlg F l hn) (matZero F) := fun i j _ _ => by
  show S F l (fun _ => F.mul F.zero F.zero) = F.zero
  exact S_all_zero F l (fun _ _ => F.mul_zero F.zero)

theorem orth_zero (F : OF α) (l : List Nat) (hn : NoDup l) (p : Mat α) : Orth (matAlg F l hn) p (matZero F) :=
  ⟨fun i _ _ _ => S_all_zero F l (fun k _ => F.mul_zero (p i k)),
   fun _ j _ _ => S_all_zero F l (fun k _ => ZNet.zero_mul F (p k j))⟩

/-- orthogonal to two → orthogonal to their sum (in any algebra of QZ7) -/
theorem orth_add_r {A : Type} (R : Alg A) {p q r : A} (h1 : Orth R p q) (h2 : Orth R p r) : Orth R p (R.add q r) :=
  ⟨R.trans (R.mul_add p q r) (R.trans (R.add_congr h1.1 h2.1) (R.add_zero R.zero)),
   R.trans (R.add_mul q r p) (R.trans (R.add_congr h1.2 h2.2) (R.add_zero R.zero))⟩

theorem ray_orth_frame (F : OF α) (l : List Nat) (hn : NoDup l) (c : α) (u : Nat → α) :
    ∀ fs, OrthTo F l u fs → Orth (matAlg F l hn) (ray F c u) (frame F fs)
  | [], _ => orth_zero F l hn _
  | cv :: fs, h => orth_add_r (matAlg F l hn) (ray_orth F l hn c cv.1 u cv.2 h.1) (ray_orth_frame F l hn c u fs h.2)

/-- THE SUM OF THE RAYS OF AN ORTHOGONAL FAMILY IS A PROJECTION -/
theorem frame_isP (F : OF α) (l : List Nat) (hn : NoDup l) :
    ∀ fs, Normed F l fs → OrthFam F l fs → IsP (matAlg F l hn) (frame F fs)
  | [], _, _ => zero_isP F l hn
  | cv :: fs, hN, hO =>
      isP_add (matAlg F l hn) (ray_isP F l hn cv.1 cv.2 hN.1) (frame_isP F l hn fs hN.2 hO.2)
        (ray_orth_frame F l hn cv.1 cv.2 fs hO.1)

/-- …a symmetric one -/
theorem frame_sym (F : OF α) (l : List Nat) : ∀ fs, sym l (frame F fs)
  | [] => fun _ _ _ _ => rfl
  | cv :: fs => fun i j hi hj => by
      show F.add (ray F cv.1 cv.2 i j) (frame F fs i j) = F.add (ray F cv.1 cv.2 j i) (frame F fs j i)
      rw [ray_sym F l cv.1 cv.2 i j hi hj, frame_sym F l fs i j hi hj]

/-- THE BORN RULE FOR AN EVENT WITH SEVERAL OUTCOMES: the weight of the family's projection is Σ c_k·⟨v_k, ψ⟩² -/
theorem born_frame (F : OF α) (l : List Nat) (ψ : Nat → α) : ∀ fs, qf F l (frame F fs) ψ = wsum F l ψ fs
  | [] => born_zero F l ψ
  | cv :: fs => by
      show qf F l (matAdd F (ray F cv.1 cv.2) (frame F fs)) ψ =
        F.add (F.mul cv.1 (F.mul (ip F l cv.2 ψ) (ip F l cv.2 ψ))) (wsum F l ψ fs)
      rw [← born_ray F l cv.1 cv.2 ψ, ← born_frame F l ψ fs]
      exact qf_add F l (ray F cv.1 cv.2) (frame F fs) ψ

/-- …and it is not negative (QZ8) -/
theorem born_frame_nonneg (F : OF α) (l : List Nat) (hn : NoDup l) (ψ : Nat → α) (fs : List (α × (Nat → α)))
    (hN : Normed F l fs) (hO : OrthFam F l fs) : F.le F.zero (wsum F l ψ fs) := by
  rw [← born_frame F l ψ fs]
  exact born_nonneg F l ψ (frame_isP F l hn fs hN hO) (frame_sym F l fs)

end QZ10

#print axioms QZ10.ray_mul
#print axioms QZ10.ray_isP
#print axioms QZ10.ray_orth
#print axioms QZ10.born_ray
#print axioms QZ10.born_ray_nonneg
#print axioms QZ10.frame2_isP
#print axioms QZ10.born_frame2
#print axioms QZ10.ray_orth_frame
#print axioms QZ10.frame_isP
#print axioms QZ10.frame_sym
#print axioms QZ10.born_frame
#print axioms QZ10.born_frame_nonneg
