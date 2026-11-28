import ZNet
import ZRound
import QZ3
import QZ4
import QZ5
import QZ7
import QZ8

/-!
# QZ9 — a state SPLITS along a question exactly when their projections COMMUTE. Zero axioms.

(2026-11-28, the curator: "работай далее". Written with AI.)

Layer 2 (QZ4) keeps a stable verdict where what is known SPLITS along the dirty questions of the claim:
s ≤ (s ∧ a) ∨ (s ∧ ¬a). That condition was stated in the lattice and measured on qubits. Here it is read in the
algebra of projections of QZ7, with one more law - multiplication is associative:

  `comm_split`   the projections of s and a commute  →  s splits along a
  `split_comm`   s splits along a  →  the projections commute
  `comm_Splits`  a list of questions that commute with s and with one another: s splits along the whole list
                 (QZ4.Splits - the premise of QZ4's `stable_sound_under`)
  `meet_of_comm` for commuting projections the lattice's meet IS the product
  `stable_sound_commuting`, `stableF_sound_commuting`   hence the kernel's IF STABLE verdicts are sound where the
                 dirty questions of the claim commute with what is known and with one another

So "the questions can be asked together" (they commute - one context, one measurement) and "the stable verdict is
kept" are the same condition. `mat_assoc`: the matrices of QZ8 are associative, so this holds for them; `f2_assoc`,
`qubit_closed`: and for the 2×2 example, where a and b do not commute and b does not split along a.

The lattice must hold the product of two commuting members (`Closed`), as it must hold the sum of two orthogonal
ones (QZ7's `Rep`): both are members of any lattice of ALL projections; that the judge's subspaces are such a
lattice is still not proved here (QZ8's header).

PRIOR WORK, as far as checked: compatibility = commutativity in projection lattices is classical (the Foulis-Holland
theorem lives in every orthomodular lattice; not read in the original). Not new mathematics; ours is the tie to the
kernel's own splitting condition, by machine.
-/

namespace QZ9
open ZNet ZRound QZ3 QZ7 QZ8

variable {A : Type} (R : Alg A)

/-- multiplication is associative -/
def Assoc : Prop := ∀ a b c, R.eqv (R.mul (R.mul a b) c) (R.mul a (R.mul b c))
/-- the two commute -/
def Comm (p q : A) : Prop := R.eqv (R.mul p q) (R.mul q p)

theorem comm_symm {p q : A} (h : Comm R p q) : Comm R q p := R.symm h

theorem comm_congr {p p' q q' : A} (hp : R.eqv p p') (hq : R.eqv q q') (h : Comm R p q) : Comm R p' q' :=
  R.trans (R.mul_congr (R.symm hp) (R.symm hq)) (R.trans h (R.mul_congr hq hp))

/-- p commutes with q → p commutes with 1 − q -/
theorem comm_ng {p q : A} (h : Comm R p q) : Comm R p (ng R q) :=
  R.trans (R.trans (R.mul_sub p R.one q) (R.sub_congr (R.mul_one p) (R.refl _)))
    (R.symm (R.trans (R.sub_mul R.one q p) (R.sub_congr (R.one_mul p) (R.symm h))))

variable {R}

/-- p and q commute with r → p·q commutes with r -/
theorem comm_mul (hA : Assoc R) {p q r : A} (h1 : Comm R p r) (h2 : Comm R q r) : Comm R (R.mul p q) r :=
  R.trans (hA p q r) (R.trans (R.mul_congr (R.refl p) h2) (R.trans (R.symm (hA p r q))
    (R.trans (R.mul_congr h1 (R.refl q)) (hA r p q))))

/-- (p·q)·q = p·q for a projection q -/
theorem mul_absorb_r (hA : Assoc R) (p : A) {q : A} (hq : IsP R q) : R.eqv (R.mul (R.mul p q) q) (R.mul p q) :=
  R.trans (hA p q q) (R.mul_congr (R.refl p) hq)

/-- p·(p·q) = p·q for a projection p -/
theorem mul_absorb_l (hA : Assoc R) {p : A} (hp : IsP R p) (q : A) : R.eqv (R.mul p (R.mul p q)) (R.mul p q) :=
  R.trans (R.symm (hA p p q)) (R.mul_congr hp (R.refl q))

/-- the product of two commuting projections is a part of the first -/
theorem mul_le_l (hA : Assoc R) {p q : A} (hp : IsP R p) (hc : Comm R p q) : Le R (R.mul p q) p :=
  ⟨R.trans (hA p q p) (R.trans (R.mul_congr (R.refl p) (R.symm hc)) (mul_absorb_l hA hp q)), mul_absorb_l hA hp q⟩

/-- …and of the second -/
theorem mul_le_r (hA : Assoc R) {p q : A} (hq : IsP R q) (hc : Comm R p q) : Le R (R.mul p q) q :=
  ⟨mul_absorb_r hA p hq,
   R.trans (R.symm (hA q p q)) (R.trans (R.mul_congr (R.symm hc) (R.refl q)) (mul_absorb_r hA p hq))⟩

/-- …and the greatest such: a part of both is a part of the product -/
theorem le_mul (hA : Assoc R) {r p q : A} (h1 : Le R r p) (h2 : Le R r q) : Le R r (R.mul p q) :=
  ⟨R.trans (R.symm (hA r p q)) (R.trans (R.mul_congr h1.1 (R.refl q)) h2.1),
   R.trans (hA p q r) (R.trans (R.mul_congr (R.refl p) h2.2) h1.2)⟩

/-- p = p·q + p·(1 − q) -/
theorem split_id (R : Alg A) (p q : A) : R.eqv (R.add (R.mul p q) (R.mul p (ng R q))) p :=
  R.trans (R.add_congr (R.refl _) (R.trans (R.mul_sub p R.one q) (R.sub_congr (R.mul_one p) (R.refl _))))
    (R.add_sub (R.mul p q) p)

/-! ### in a lattice of projections -/

variable {α : Type} {L : NLat α}

/-- the lattice holds the product of two commuting members -/
def Closed (E : Rep R L) : Prop := ∀ x y, Comm R (E.e x) (E.e y) → ∃ t, R.eqv (E.e t) (R.mul (E.e x) (E.e y))

/-- FOR COMMUTING PROJECTIONS THE MEET IS THE PRODUCT -/
theorem meet_of_comm (hA : Assoc R) (E : Rep R L) (hcl : Closed E) (x y : α) (hc : Comm R (E.e x) (E.e y)) :
    R.eqv (E.e (L.meet x y)) (R.mul (E.e x) (E.e y)) := by
  have ⟨t, ht⟩ := hcl x y hc
  have htx : L.le t x := E.le_of (le_congr R (R.symm ht) (R.refl _) (mul_le_l hA (E.isP x) hc))
  have hty : L.le t y := E.le_of (le_congr R (R.symm ht) (R.refl _) (mul_le_r hA (E.isP y) hc))
  have h1 : Le R (E.e t) (E.e (L.meet x y)) := E.le_to (L.le_meet htx hty)
  have h2 : Le R (E.e (L.meet x y)) (E.e t) :=
    le_congr R (R.refl _) (R.symm ht) (le_mul hA (E.le_to (L.meet_le_l x y)) (E.le_to (L.meet_le_r x y)))
  exact R.trans (le_antisymm R h2 h1) ht

/-- COMMUTING → SPLITTING: s = s·a + s·(1 − a), and the two parts are the two cells -/
theorem comm_split (hA : Assoc R) (E : Rep R L) (hcl : Closed E) (s a : α) (hc : Comm R (E.e s) (E.e a)) :
    L.le s (L.join (L.meet s a) (L.meet s (L.neg a))) := by
  have m1 := meet_of_comm hA E hcl s a hc
  have hc' : Comm R (E.e s) (E.e (L.neg a)) := comm_congr R (R.refl _) (R.symm (E.neg a)) (comm_ng R hc)
  have m2 : R.eqv (E.e (L.meet s (L.neg a))) (R.mul (E.e s) (ng R (E.e a))) :=
    R.trans (meet_of_comm hA E hcl s (L.neg a) hc') (R.mul_congr (R.refl _) (E.neg a))
  have ho := cells_orth E s a
  have ⟨t, ht⟩ := E.sum _ _ ho
  have hts : R.eqv (E.e t) (E.e s) := R.trans ht (R.trans (R.add_congr m1 m2) (split_id R (E.e s) (E.e a)))
  have hst : L.le s t := E.le_of (le_congr R (R.refl _) (R.symm hts) ⟨E.isP s, E.isP s⟩)
  have htj : L.le t (L.join (L.meet s a) (L.meet s (L.neg a))) :=
    E.le_of (le_congr R (R.symm ht) (R.refl _) (add_le R (E.le_to (L.le_join_l _ _)) (E.le_to (L.le_join_r _ _))))
  exact L.le_trans hst htj

/-- SPLITTING → COMMUTING (no associativity needed): with s = u + u', u a part of a and u' orthogonal to a,
s·a = u = a·s -/
theorem split_comm (E : Rep R L) (s a : α) (h : L.le s (L.join (L.meet s a) (L.meet s (L.neg a)))) :
    Comm R (E.e s) (E.e a) := by
  have hs := split_sum E s a h
  have hu : Le R (E.e (L.meet s a)) (E.e a) := E.le_to (L.meet_le_r s a)
  have hu' : Orth R (E.e (L.meet s (L.neg a))) (E.e a) :=
    orth_of_le_ng R (le_congr R (R.refl _) (E.neg a) (E.le_to (L.meet_le_r s (L.neg a))))
  have l1 : R.eqv (R.mul (E.e s) (E.e a)) (E.e (L.meet s a)) :=
    R.trans (R.mul_congr hs (R.refl _)) (R.trans (R.add_mul _ _ _) (R.trans (R.add_congr hu.1 hu'.1) (R.add_zero _)))
  have l2 : R.eqv (R.mul (E.e a) (E.e s)) (E.e (L.meet s a)) :=
    R.trans (R.mul_congr (R.refl _) hs) (R.trans (R.mul_add _ _ _) (R.trans (R.add_congr hu.2 hu'.2) (R.add_zero _)))
  exact R.trans l1 (R.symm l2)

/-! ### a whole list: one context -/

/-- p commutes with every question of the list -/
def CommAll (E : Rep R L) (p : A) : List α → Prop
  | [] => True
  | x :: xs => Comm R p (E.e x) ∧ CommAll E p xs

/-- the questions of the list commute with one another -/
def Pairwise (E : Rep R L) : List α → Prop
  | [] => True
  | x :: xs => CommAll E (E.e x) xs ∧ Pairwise E xs

theorem commAll_congr (E : Rep R L) {p p' : A} (hp : R.eqv p p') : ∀ xs, CommAll E p xs → CommAll E p' xs
  | [], _ => True.intro
  | _ :: xs, h => ⟨comm_congr R hp (R.refl _) h.1, commAll_congr E hp xs h.2⟩

theorem commAll_mul (hA : Assoc R) (E : Rep R L) {p q : A} : ∀ xs, CommAll E p xs → CommAll E q xs → CommAll E (R.mul p q) xs
  | [], _, _ => True.intro
  | _ :: xs, h1, h2 => ⟨comm_mul hA h1.1 h2.1, commAll_mul hA E xs h1.2 h2.2⟩

theorem commAll_ng (E : Rep R L) {q : A} : ∀ xs, CommAll E q xs → CommAll E (ng R q) xs
  | [], _ => True.intro
  | _ :: xs, h => ⟨comm_symm R (comm_ng R (comm_symm R h.1)), commAll_ng E xs h.2⟩

/-- ONE CONTEXT SPLITS: questions that commute with what is known and with one another - the state splits along the
whole list, which is the premise QZ4 asks for a stable verdict to be kept -/
theorem comm_Splits (hA : Assoc R) (E : Rep R L) (hcl : Closed E) :
    ∀ (xs : List α) (s : α), CommAll E (E.e s) xs → Pairwise E xs → QZ4.Splits L s xs
  | [], _, _, _ => True.intro
  | x :: xs, s, h1, h2 => by
      have hx : Comm R (E.e s) (E.e x) := h1.1
      have hnx : Comm R (E.e s) (E.e (L.neg x)) := comm_congr R (R.refl _) (R.symm (E.neg x)) (comm_ng R hx)
      have c1 : CommAll E (E.e (L.meet s x)) xs :=
        commAll_congr E (R.symm (meet_of_comm hA E hcl s x hx)) xs (commAll_mul hA E xs h1.2 h2.1)
      have cn : CommAll E (E.e (L.neg x)) xs := commAll_congr E (R.symm (E.neg x)) xs (commAll_ng E xs h2.1)
      have c2 : CommAll E (E.e (L.meet s (L.neg x))) xs :=
        commAll_congr E (R.symm (meet_of_comm hA E hcl s (L.neg x) hnx)) xs (commAll_mul hA E xs h1.2 cn)
      exact ⟨comm_split hA E hcl s x hx, comm_Splits hA E hcl xs (L.meet s x) c1 h2.2,
             comm_Splits hA E hcl xs (L.meet s (L.neg x)) c2 h2.2⟩

/-! ### the stable layer, from commutation -/

open V in
/-- LAYER 2 FROM COMMUTATION: where the dirty questions of the claim commute with what is known and with one
another, a verdict "EARNED IF STABLE" of the kernel is true in the lattice (QZ4.stable_sound_on with its splitting
premise discharged) -/
theorem stable_sound_commuting (hA : Assoc R) (E : Rep R L) (hcl : Closed E) (s : α) (v : Nat → V) (val : Nat → α)
    (zs : List Nat) (φ : Fm) (ag : AgreesOn L s v val φ) (hz : QZ4.DirtyIn v zs φ)
    (hc : CommAll E (E.e s) (zs.map val)) (hp : Pairwise E (zs.map val)) (st : stableT v φ) :
    L.le s (qe L val φ) :=
  QZ4.stable_sound_on L s v val zs φ ag hz (comm_Splits hA E hcl (zs.map val) s hc hp) st

open V in
/-- …and "REFUTED IF STABLE" is false in the lattice there -/
theorem stableF_sound_commuting (hA : Assoc R) (E : Rep R L) (hcl : Closed E) (s : α) (v : Nat → V) (val : Nat → α)
    (zs : List Nat) (φ : Fm) (ag : AgreesOn L s v val φ) (hz : QZ4.DirtyIn v zs φ)
    (hc : CommAll E (E.e s) (zs.map val)) (hp : Pairwise E (zs.map val)) (st : stableF v φ) :
    L.le s (L.neg (qe L val φ)) :=
  QZ4.stableF_sound_on L s v val zs φ ag hz (comm_Splits hA E hcl (zs.map val) s hc hp) st

/-! ### the matrices are associative -/

variable {β : Type}

theorem mat_assoc (F : OF β) (l : List Nat) (hn : NoDup l) : Assoc (matAlg F l hn) := by
  intro a b c i j _ _
  show S F l (fun k => F.mul (S F l (fun m => F.mul (a i m) (b m k))) (c k j)) =
    S F l (fun m => F.mul (a i m) (S F l (fun k => F.mul (b m k) (c k j))))
  rw [S_congr F l (fun k _ => (S_mul_right F (c k j) (fun m => F.mul (a i m) (b m k)) l).symm)]
  rw [S_swap F (fun k m => F.mul (F.mul (a i m) (b m k)) (c k j)) l l]
  exact S_congr F l (fun m _ => by
    rw [← S_mul F (a i m) (fun k => F.mul (b m k) (c k j)) l]
    exact S_congr F l (fun k _ => F.mul_assoc _ _ _))

/-! ### the 2×2 example: a and b do not commute, and b does not split along a -/

theorem m_assoc : ∀ a b c d a' b' c' d' a'' b'' c'' d'' : Bool,
    mmul (mmul ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩) ⟨a'', b'', c'', d''⟩ =
    mmul ⟨a, b, c, d⟩ (mmul ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩) := by decide

theorem f2_assoc : Assoc f2 := fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩ => m_assoc a b c d a' b' c' d' a'' b'' c'' d''

theorem emb_prod : ∀ x y : Q, mmul (emb x) (emb y) = mmul (emb y) (emb x) → emb (qmeet x y) = mmul (emb x) (emb y) := by
  decide

theorem qubit_closed : Closed qubitRep := fun x y h => ⟨qmeet x y, emb_prod x y h⟩

/-- a commutes with its own negation: the top splits along a (one context) -/
theorem qubit_splits : mo2.le Q.top (mo2.join (mo2.meet Q.top Q.a) (mo2.meet Q.top (mo2.neg Q.a))) :=
  comm_split f2_assoc qubitRep qubit_closed Q.top Q.a (by decide : mmul (emb Q.top) (emb Q.a) = mmul (emb Q.a) (emb Q.top))

/-- b does not split along a - because they do not commute (QZ4's `mo2_no_split`, now with its reason) -/
theorem qubit_no_split : ¬ mo2.le Q.b (mo2.join (mo2.meet Q.b Q.a) (mo2.meet Q.b (mo2.neg Q.a))) :=
  fun h => (by decide : ¬ mmul (emb Q.b) (emb Q.a) = mmul (emb Q.a) (emb Q.b)) (split_comm qubitRep Q.b Q.a h)

end QZ9

#print axioms QZ9.comm_mul
#print axioms QZ9.meet_of_comm
#print axioms QZ9.comm_split
#print axioms QZ9.split_comm
#print axioms QZ9.comm_Splits
#print axioms QZ9.mat_assoc
#print axioms QZ9.f2_assoc
#print axioms QZ9.qubit_closed
#print axioms QZ9.qubit_splits
#print axioms QZ9.qubit_no_split
#print axioms QZ9.stable_sound_commuting
#print axioms QZ9.stableF_sound_commuting
