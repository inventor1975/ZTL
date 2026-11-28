import ZNet
import ZRound
import QZ3
import QZ5
import QZ7

/-!
# QZ8 — the Born weight ⟨ψ, Pψ⟩ on matrices is such a weight: additive, and not negative on a symmetric projection. Zero axioms.

(2026-11-28, the curator: "Да, строй". Written with AI.)

QZ7 proves the requirements of layer 3 for any weight that is additive on orthogonal projections of an algebra and
not negative on them. Here the algebra is the n×n MATRICES over an ordered field and the weight is the BORN weight
of a vector ψ:   w(M) = ψᵀ M ψ   (one = ψᵀψ: the weight is not divided by the norm, the scale's "one" is ψᵀψ).

Nothing new is computed: the kernel already had the sums over a list of indices (ZNet: `S`, `S_add`, `S_swap`) and
the quadratic form with its two facts (ZRound: `qf_add` - the form is additive in the matrix; `qf_rtr_nonneg` -
xᵀ(RᵀR)x is a sum of squares). They were built for a floating Cholesky; the same two facts are the Born rule's:
  `matAlg`       the matrices are an algebra in the sense of QZ7 (equal = equal entry by entry on the index list)
  `sym_proj_rtr` a symmetric projection is PᵀP                       (P = P·P and Pᵀ = P)
  `born_nonneg`  so ψᵀPψ = |Pψ|² ≥ 0
  `bornWt`       the Born weight is a weight of QZ7, `ok` = symmetric
  `born_prob`    hence a probability of layer 3 (QZ5.Prob) on every lattice of symmetric projections
  `born_split`   and additive over the two cells of a splitting (what QZ6 asks of a count)

The field is the kernel's `ZNet.OF` (an ordered field given by its laws); a minimum and a maximum are asked of it
separately (`MinMax`) because QZ5's scale has them and an ordered field given by laws does not compute them.

WHAT IS STILL NOT PROVED, said plainly: that every SUBSPACE has a symmetric projection, and that the subspaces with
intersection and span are a lattice in the order p·q = p (Gram–Schmidt and what follows). Until then `born_prob` is
conditional on being handed such a lattice of projections (`Rep`); the judge's own lattice (subspace.py) is tied to
it by measurement only (born_requirements_probe.py).
-/

namespace QZ8
open ZNet ZRound QZ3 QZ7

variable {α : Type}

/-- a matrix: entries by two indices; only those of the index list matter -/
abbrev Mat (α : Type) := Nat → Nat → α

/-- equal entry by entry on the index list -/
def meq (l : List Nat) (M N : Mat α) : Prop := ∀ i j, List.Mem i l → List.Mem j l → M i j = N i j
def matAdd (F : OF α) (M N : Mat α) : Mat α := fun i j => F.add (M i j) (N i j)
def matSub (F : OF α) (M N : Mat α) : Mat α := fun i j => F.add (M i j) (F.neg (N i j))
def matMul (F : OF α) (l : List Nat) (M N : Mat α) : Mat α := fun i j => S F l (fun k => F.mul (M i k) (N k j))
def matZero (F : OF α) : Mat α := fun _ _ => F.zero
def matOne (F : OF α) : Mat α := fun i j => if i = j then F.one else F.zero

/-- no index twice -/
def NoDup : List Nat → Prop
  | [] => True
  | i :: l => ¬ List.Mem i l ∧ NoDup l

theorem S_all_zero (F : OF α) {f : Nat → α} (l : List Nat) (h : ∀ k, List.Mem k l → f k = F.zero) : S F l f = F.zero := by
  rw [S_congr F l h]
  exact S_zero F l

/-- Σ_k f(k)·δ(k, j) = f(j) -/
theorem S_delta (F : OF α) (f : Nat → α) (j : Nat) :
    ∀ l, NoDup l → List.Mem j l → S F l (fun k => F.mul (f k) (if k = j then F.one else F.zero)) = f j
  | [], _, hj => nomatch hj
  | i :: l, hn, hj => by
      show F.add (F.mul (f i) (if i = j then F.one else F.zero))
        (S F l (fun k => F.mul (f k) (if k = j then F.one else F.zero))) = f j
      match Nat.decEq i j with
      | isTrue hij =>
          have hz : S F l (fun k => F.mul (f k) (if k = j then F.one else F.zero)) = F.zero :=
            S_all_zero F l (fun k hk => by
              have hkj : ¬ k = j := fun e => hn.1 ((e.trans hij.symm) ▸ hk)
              rw [if_neg hkj, F.mul_zero])
          rw [hz, if_pos hij, F.mul_one, F.add_zero, hij]
      | isFalse hij =>
          have hj' : List.Mem j l := by
            cases hj with
            | head => exact absurd rfl hij
            | tail _ h => exact h
          rw [if_neg hij, F.mul_zero, ZNet.zero_add, S_delta F f j l hn.2 hj']

/-- Σ_k δ(i, k)·g(k) = g(i) -/
theorem S_delta_l (F : OF α) (g : Nat → α) (i : Nat) :
    ∀ l, NoDup l → List.Mem i l → S F l (fun k => F.mul (if i = k then F.one else F.zero) (g k)) = g i
  | [], _, hi => nomatch hi
  | m :: l, hn, hi => by
      show F.add (F.mul (if i = m then F.one else F.zero) (g m))
        (S F l (fun k => F.mul (if i = k then F.one else F.zero) (g k))) = g i
      match Nat.decEq i m with
      | isTrue him =>
          have hz : S F l (fun k => F.mul (if i = k then F.one else F.zero) (g k)) = F.zero :=
            S_all_zero F l (fun k hk => by
              have hik : ¬ i = k := fun e => hn.1 ((e.symm.trans him) ▸ hk)
              rw [if_neg hik, ZNet.zero_mul])
          rw [hz, if_pos him, ZRound.one_mul, F.add_zero, him]
      | isFalse him =>
          have hi' : List.Mem i l := by
            cases hi with
            | head => exact absurd rfl him
            | tail _ h => exact h
          rw [if_neg him, ZNet.zero_mul, ZNet.zero_add, S_delta_l F g i l hn.2 hi']

/-- a + c = a → c = 0 -/
theorem add_eq_self (F : OF α) {a c : α} (h : F.add a c = a) : c = F.zero := by
  have h1 : F.add (F.neg a) (F.add a c) = F.add (F.neg a) a := by rw [h]
  rw [← F.add_assoc, F.add_comm (F.neg a) a, F.add_neg, ZNet.zero_add] at h1
  exact h1

/-- THE MATRICES ARE AN ALGEBRA OF QZ7 (on an index list with no index twice) -/
def matAlg (F : OF α) (l : List Nat) (hn : NoDup l) : Alg (Mat α) where
  eqv := meq l
  add := matAdd F
  sub := matSub F
  mul := matMul F l
  zero := matZero F
  one := matOne F
  refl := fun _ _ _ _ _ => rfl
  symm := fun h i j hi hj => (h i j hi hj).symm
  trans := fun h k i j hi hj => (h i j hi hj).trans (k i j hi hj)
  add_congr := fun {a a' b b'} h k i j hi hj => by
    show F.add (a i j) (b i j) = F.add (a' i j) (b' i j)
    rw [h i j hi hj, k i j hi hj]
  sub_congr := fun {a a' b b'} h k i j hi hj => by
    show F.add (a i j) (F.neg (b i j)) = F.add (a' i j) (F.neg (b' i j))
    rw [h i j hi hj, k i j hi hj]
  mul_congr := fun {a a' b b'} h k i j hi hj =>
    S_congr F l (fun m hm => by
      show F.mul (a i m) (b m j) = F.mul (a' i m) (b' m j)
      rw [h i m hi hm, k m j hm hj])
  mul_add := fun a b c i j _ _ => by
    show S F l (fun k => F.mul (a i k) (F.add (b k j) (c k j))) =
      F.add (S F l (fun k => F.mul (a i k) (b k j))) (S F l (fun k => F.mul (a i k) (c k j)))
    rw [← S_add F _ _ l]
    exact S_congr F l (fun k _ => F.mul_add _ _ _)
  add_mul := fun a b c i j _ _ => by
    show S F l (fun k => F.mul (F.add (a i k) (b i k)) (c k j)) =
      F.add (S F l (fun k => F.mul (a i k) (c k j))) (S F l (fun k => F.mul (b i k) (c k j)))
    rw [← S_add F _ _ l]
    exact S_congr F l (fun k _ => ZNet.add_mul F _ _ _)
  mul_sub := fun a b c i j _ _ => by
    show S F l (fun k => F.mul (a i k) (F.add (b k j) (F.neg (c k j)))) =
      F.add (S F l (fun k => F.mul (a i k) (b k j))) (F.neg (S F l (fun k => F.mul (a i k) (c k j))))
    rw [← S_neg F _ l, ← S_add F _ _ l]
    exact S_congr F l (fun k _ => by
      show F.mul (a i k) (F.add (b k j) (F.neg (c k j))) = F.add (F.mul (a i k) (b k j)) (F.neg (F.mul (a i k) (c k j)))
      rw [F.mul_add, ZNet.mul_neg])
  sub_mul := fun a b c i j _ _ => by
    show S F l (fun k => F.mul (F.add (a i k) (F.neg (b i k))) (c k j)) =
      F.add (S F l (fun k => F.mul (a i k) (c k j))) (F.neg (S F l (fun k => F.mul (b i k) (c k j))))
    rw [← S_neg F _ l, ← S_add F _ _ l]
    exact S_congr F l (fun k _ => by
      show F.mul (F.add (a i k) (F.neg (b i k))) (c k j) = F.add (F.mul (a i k) (c k j)) (F.neg (F.mul (b i k) (c k j)))
      rw [ZNet.add_mul, F.neg_mul])
  mul_one := fun a i j _ hj => S_delta F (fun k => a i k) j l hn hj
  one_mul := fun a i j hi _ => S_delta_l F (fun k => a k j) i l hn hi
  add_zero := fun a i j _ _ => F.add_zero (a i j)
  zero_add := fun a i j _ _ => ZNet.zero_add F (a i j)
  sub_self := fun a i j _ _ => F.add_neg (a i j)
  sub_zero := fun a i j _ _ => by
    show F.add (a i j) (F.neg F.zero) = a i j
    rw [ZNet.neg_zero, F.add_zero]
  add_sub := fun a b i j _ _ => by
    show F.add (a i j) (F.add (b i j) (F.neg (a i j))) = b i j
    rw [F.add_comm (b i j), ← F.add_assoc, F.add_neg, ZNet.zero_add]
  sub_eq_self := fun a b h i j hi hj => by
    have h1 : F.add (a i j) (F.neg (b i j)) = a i j := h i j hi hj
    have h2 : F.neg (b i j) = F.zero := add_eq_self F h1
    show b i j = F.zero
    rw [← F.neg_neg (b i j), h2, ZNet.neg_zero]

/-! ### the Born weight -/

/-- symmetric on the index list -/
def sym (l : List Nat) (P : Mat α) : Prop := ∀ i j, List.Mem i l → List.Mem j l → P i j = P j i

/-- A SYMMETRIC PROJECTION IS PᵀP: (PᵀP)_ij = Σ_m P_mi P_mj = Σ_m P_im P_mj = (P·P)_ij = P_ij -/
theorem sym_proj_rtr (F : OF α) (l : List Nat) {P : Mat α} (hp : meq l (matMul F l P P) P) (hs : sym l P) :
    meq l P (rtr F l P) := by
  intro i j hi hj
  show P i j = S F l (fun m => F.mul (P m i) (P m j))
  rw [S_congr F l (fun m hm => by rw [hs m i hm hi] : ∀ m, List.Mem m l → F.mul (P m i) (P m j) = F.mul (P i m) (P m j))]
  exact (hp i j hi hj).symm

/-- THE BORN WEIGHT OF A SYMMETRIC PROJECTION IS NOT NEGATIVE: ψᵀPψ = ψᵀ(PᵀP)ψ, a sum of squares -/
theorem born_nonneg (F : OF α) (l : List Nat) (ψ : Nat → α) {P : Mat α} (hp : meq l (matMul F l P P) P) (hs : sym l P) :
    F.le F.zero (qf F l P ψ) := by
  rw [qf_congr F l ψ (sym_proj_rtr F l hp hs)]
  exact qf_rtr_nonneg F l P ψ

theorem born_zero (F : OF α) (l : List Nat) (ψ : Nat → α) : qf F l (matZero F) ψ = F.zero := by
  unfold qf
  exact S_all_zero F l (fun i _ => S_all_zero F l (fun j _ => by
    show F.mul (ψ i) (F.mul F.zero (ψ j)) = F.zero
    rw [ZNet.zero_mul, F.mul_zero]))

/-! ### the scale: the field itself, with ψᵀψ for "one" -/

/-- a minimum and a maximum (QZ5's scale has them; an ordered field given by its laws does not compute them) -/
structure MinMax (F : OF α) where
  mn : α → α → α
  mx : α → α → α
  le_mn : ∀ {a x y}, F.le a x → F.le a y → F.le a (mn x y)
  mx_le : ∀ {a x y}, F.le x a → F.le y a → F.le (mx x y) a

theorem neg_le_neg (F : OF α) {a b : α} (h : F.le a b) : F.le (F.neg b) (F.neg a) := by
  have h1 := F.add_le_add h (F.le_refl (F.add (F.neg a) (F.neg b)))
  have e1 : F.add a (F.add (F.neg a) (F.neg b)) = F.neg b := by rw [← F.add_assoc, F.add_neg, ZNet.zero_add]
  have e2 : F.add b (F.add (F.neg a) (F.neg b)) = F.neg a := by
    rw [F.add_comm (F.neg a), ← F.add_assoc, F.add_neg, ZNet.zero_add]
  rw [e1, e2] at h1
  exact h1

/-- the scale of QZ5 on the field: one = N, the complement of x is N − x -/
def scale (F : OF α) (mm : MinMax F) (N : α) : QZ5.Scale α where
  le := F.le
  zero := F.zero
  one := N
  co := fun x => F.add N (F.neg x)
  mn := mm.mn
  mx := mm.mx
  le_trans := F.le_trans
  co_anti := fun h => F.add_le_add (F.le_refl N) (neg_le_neg F h)
  le_mn := mm.le_mn
  mx_le := mm.mx_le
  le_zero_of := fun p h => by
    have h0 : F.le N (F.add N (F.neg p)) := h
    have h1 := F.add_le_add (F.le_refl (F.neg N)) h0
    have e1 : F.add (F.neg N) N = F.zero := by rw [F.add_comm, F.add_neg]
    have e2 : F.add (F.neg N) (F.add N (F.neg p)) = F.neg p := by rw [← F.add_assoc, e1, ZNet.zero_add]
    rw [e1, e2] at h1
    have h2 := neg_le_neg F h1
    rw [F.neg_neg, ZNet.neg_zero] at h2
    exact h2

theorem co_of_sum (F : OF α) {a b N : α} (h : F.add a b = N) : F.add N (F.neg a) = b := by
  rw [← h, F.add_comm a b, F.add_assoc, F.add_neg, F.add_zero]

def scaleAdd (F : OF α) (mm : MinMax F) (N : α) : SAdd (scale F mm N) where
  add := F.add
  le_refl := F.le_refl
  co_le := fun {a b} h => by
    have h' : F.add a b = N := h
    show F.le b (F.add N (F.neg a))
    rw [co_of_sum F h']
    exact F.le_refl b
  le_co := fun {a b} h => by
    have h' : F.add a b = N := h
    show F.le (F.add N (F.neg a)) b
    rw [co_of_sum F h']
    exact F.le_refl b

/-- THE BORN WEIGHT IS A WEIGHT OF QZ7: additive in the matrix, ψᵀψ at 1, zero at 0, not negative on a symmetric
projection -/
def bornWt (F : OF α) (l : List Nat) (hn : NoDup l) (mm : MinMax F) (ψ : Nat → α) :
    Wt (matAlg F l hn) (scale F mm (qf F l (matOne F) ψ)) (scaleAdd F mm (qf F l (matOne F) ψ)) where
  w := fun M => qf F l M ψ
  ok := sym l
  ok_sub := fun {p q} hp hq i j hi hj => by
    show F.add (q i j) (F.neg (p i j)) = F.add (q j i) (F.neg (p j i))
    rw [hq i j hi hj, hp i j hi hj]
  congr := fun h => qf_congr F l ψ h
  additive := fun {p q} _ _ _ => qf_add F l p q ψ
  one := rfl
  zero := born_zero F l ψ
  le_add := fun {p q} hq oq => by
    have h1 := F.add_le_add (F.le_refl (qf F l p ψ)) (born_nonneg F l ψ hq oq)
    rw [F.add_zero] at h1
    exact h1
  zero_le := fun {p} hp op => born_nonneg F l ψ hp op

variable {β : Type} {L : NLat β}

/-- THE BORN WEIGHT IS A PROBABILITY OF LAYER 3, on every lattice of symmetric projections of the matrices -/
def born_prob (F : OF α) (l : List Nat) (hn : NoDup l) (mm : MinMax F) (ψ : Nat → α)
    (E : Rep (matAlg F l hn) L) (hs : ∀ x, sym l (E.e x)) : QZ5.Prob L (scale F mm (qf F l (matOne F) ψ)) :=
  state_prob E (bornWt F l hn mm ψ) hs

/-- …and along a splitting it is the sum over the two cells: inside a context the Born weights add up -/
theorem born_split (F : OF α) (l : List Nat) (hn : NoDup l) (mm : MinMax F) (ψ : Nat → α)
    (E : Rep (matAlg F l hn) L) (s a : β) (h : L.le s (L.join (L.meet s a) (L.meet s (L.neg a)))) :
    qf F l (E.e s) ψ = F.add (qf F l (E.e (L.meet s a)) ψ) (qf F l (E.e (L.meet s (L.neg a))) ψ) :=
  wt_split E (bornWt F l hn mm ψ) s a h

end QZ8

#print axioms QZ8.S_delta
#print axioms QZ8.S_delta_l
#print axioms QZ8.matAlg
#print axioms QZ8.sym_proj_rtr
#print axioms QZ8.born_nonneg
#print axioms QZ8.scale
#print axioms QZ8.bornWt
#print axioms QZ8.born_prob
#print axioms QZ8.born_split
