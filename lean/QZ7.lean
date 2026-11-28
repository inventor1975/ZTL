import ZTL
import ZRead
import QZ3
import QZ5
import QZ6

/-!
# QZ7 — a weight that is additive on orthogonal projections meets everything layer 3 asks of a probability. Zero axioms.

(2026-11-28, the curator: "Да, строй" — the projection, so that Born becomes a theorem. Written with AI.)

QZ5 (`Prob`) and QZ6 (`Count`) prove their conclusions for ANY weight that is monotone, complements on negation, is
additive along a splitting. That the BORN weight μ(x) = ⟨ψ, P_x ψ⟩ / ⟨ψ, ψ⟩ is such a weight was, until this file,
measured only (born_requirements_probe.py). Here is the reason, with no numbers in it:

  the questions are the PROJECTIONS of an algebra of operators (p·p = p), ordered by p ≤ q :⇔ p·q = p = q·p, with
  ¬p = 1 − p;  the weight is ADDITIVE ON ORTHOGONAL PROJECTIONS: w(p + q) = w(p) + w(q) whenever p·q = 0 = q·p.

From these alone:
  `wt_mono`      p ≤ q → w p ≤ w q                 (q = p + (q − p), and q − p is a projection orthogonal to p)
  `state_prob`   the weight is a `QZ5.Prob`         (monotone; w(¬p) is the complement of w(p); bounds; top; bottom)
  `state_count`  a count is a `QZ6.Count`           (monotone; superadditive on orthogonal parts; additive on a split)
on EVERY lattice structure carried by those projections with that order (`Rep`): the meet and the join are whatever
the lattice says, only their being the greatest lower and the least upper bound is used.

The algebra is given by the laws used (`Alg`: both distributive laws, the unit, zero, a − a = 0, a + (b − a) = b,
a − b = a → b = 0) — every ring has them; multiplication need not commute, and nothing here uses associativity.
Equality in the algebra is its own relation (`eqv`), so that matrices "equal entry by entry" are an instance (QZ8).

WHAT THIS LEAVES TO LINEAR ALGEBRA, said plainly. For the Born weight on matrices two facts remain: (1) M ↦ ⟨ψ, Mψ⟩
is additive in M and is ≥ 0 on a symmetric projection (it is |Pψ|²) - PROVED in QZ8.lean from the kernel's own
quadratic forms; (2) every subspace has such a projection, and the subspaces with intersection and span are a
lattice in the order above - NOT proved.
(2) is Gram–Schmidt and what follows from it. The instance at the end (`f2`, `qubitRep`, `qubitRank`)
is a NON-COMMUTATIVE algebra — the 2×2 matrices over the two-element field, its laws checked over every matrix — in
which the six-element lattice of the qubit (QZ3.mo2) sits as four projections with 0 and 1; QZ6's count is additive
on its orthogonal projections, so the general theorem returns it (`cnt_is_twice`); the same for QZ5's probability in
a scale that can add (`qubitProb`, `wgt_is_born`). They show the theorems are not empty where questions do not
commute; they are NOT a derivation of the Born weight from a state vector (no inner product over two elements): in
dimension two additivity ties only a question to its negation, so the weights of a and b are put in by hand.

PRIOR WORK, as far as checked: additivity on orthogonal projections is the definition of a state on a projection
lattice (Gleason 1957 is the converse direction in dimension ≥ 3; not used). Nothing here is new mathematics; what is
ours is that the requirements of QZ5 and QZ6 are derived from it by machine, for the kernel's layers.
-/

namespace QZ7
open QZ3

/-- an algebra of operators: the operations and exactly the laws used below (every ring has them). Equality is the
algebra's own (`eqv`): for matrices it is "equal entry by entry", which is not `=` of functions without an axiom. -/
structure Alg (A : Type) where
  eqv : A → A → Prop
  add : A → A → A
  sub : A → A → A
  mul : A → A → A
  zero : A
  one : A
  refl : ∀ a, eqv a a
  symm : ∀ {a b}, eqv a b → eqv b a
  trans : ∀ {a b c}, eqv a b → eqv b c → eqv a c
  add_congr : ∀ {a a' b b'}, eqv a a' → eqv b b' → eqv (add a b) (add a' b')
  sub_congr : ∀ {a a' b b'}, eqv a a' → eqv b b' → eqv (sub a b) (sub a' b')
  mul_congr : ∀ {a a' b b'}, eqv a a' → eqv b b' → eqv (mul a b) (mul a' b')
  mul_add : ∀ a b c, eqv (mul a (add b c)) (add (mul a b) (mul a c))
  add_mul : ∀ a b c, eqv (mul (add a b) c) (add (mul a c) (mul b c))
  mul_sub : ∀ a b c, eqv (mul a (sub b c)) (sub (mul a b) (mul a c))
  sub_mul : ∀ a b c, eqv (mul (sub a b) c) (sub (mul a c) (mul b c))
  mul_one : ∀ a, eqv (mul a one) a
  one_mul : ∀ a, eqv (mul one a) a
  add_zero : ∀ a, eqv (add a zero) a
  zero_add : ∀ a, eqv (add zero a) a
  sub_self : ∀ a, eqv (sub a a) zero
  sub_zero : ∀ a, eqv (sub a zero) a
  add_sub : ∀ a b, eqv (add a (sub b a)) b
  sub_eq_self : ∀ a b, eqv (sub a b) a → eqv b zero

variable {A : Type} (R : Alg A)

/-- a projection -/
def IsP (p : A) : Prop := R.eqv (R.mul p p) p
/-- p ≤ q: p is a part of q -/
def Le (p q : A) : Prop := R.eqv (R.mul p q) p ∧ R.eqv (R.mul q p) p
/-- orthogonal -/
def Orth (p q : A) : Prop := R.eqv (R.mul p q) R.zero ∧ R.eqv (R.mul q p) R.zero
/-- the negation: 1 − p -/
def ng (p : A) : A := R.sub R.one p

/-! ### the algebra of projections -/

/-- (1 − p)·p = 0 for a projection p -/
theorem ng_mul {p : A} (hp : IsP R p) : R.eqv (R.mul (R.sub R.one p) p) R.zero :=
  R.trans (R.sub_mul R.one p p) (R.trans (R.sub_congr (R.one_mul p) hp) (R.sub_self p))

theorem isP_ng {p : A} (hp : IsP R p) : IsP R (ng R p) :=
  R.trans (R.mul_sub (R.sub R.one p) R.one p)
    (R.trans (R.sub_congr (R.mul_one _) (ng_mul R hp)) (R.sub_zero _))

theorem orth_ng {p : A} (hp : IsP R p) : Orth R p (ng R p) :=
  ⟨R.trans (R.mul_sub p R.one p) (R.trans (R.sub_congr (R.mul_one p) hp) (R.sub_self p)), ng_mul R hp⟩

theorem add_ng (p : A) : R.eqv (R.add p (ng R p)) R.one := R.add_sub p R.one

theorem isP_add {p q : A} (hp : IsP R p) (hq : IsP R q) (h : Orth R p q) : IsP R (R.add p q) :=
  R.trans (R.mul_add (R.add p q) p q)
    (R.add_congr
      (R.trans (R.add_mul p q p) (R.trans (R.add_congr hp h.2) (R.add_zero p)))
      (R.trans (R.add_mul p q q) (R.trans (R.add_congr h.1 hq) (R.zero_add q))))

/-- (q − p)·p = 0 where p is a part of q -/
theorem sub_mul_part {p q : A} (hp : IsP R p) (h : Le R p q) : R.eqv (R.mul (R.sub q p) p) R.zero :=
  R.trans (R.sub_mul q p p) (R.trans (R.sub_congr h.2 hp) (R.sub_self p))

theorem isP_sub {p q : A} (hp : IsP R p) (hq : IsP R q) (h : Le R p q) : IsP R (R.sub q p) :=
  R.trans (R.mul_sub (R.sub q p) q p)
    (R.trans (R.sub_congr (R.trans (R.sub_mul q p q) (R.sub_congr hq h.1)) (sub_mul_part R hp h)) (R.sub_zero _))

theorem orth_sub {p q : A} (hp : IsP R p) (h : Le R p q) : Orth R p (R.sub q p) :=
  ⟨R.trans (R.mul_sub p q p) (R.trans (R.sub_congr h.1 hp) (R.sub_self p)), sub_mul_part R hp h⟩

/-- p ≤ ¬q says p and q are orthogonal -/
theorem orth_of_le_ng {p q : A} (h : Le R p (ng R q)) : Orth R p q :=
  ⟨R.sub_eq_self _ _ (R.trans (R.sub_congr (R.symm (R.mul_one p)) (R.refl _)) (R.trans (R.symm (R.mul_sub p R.one q)) h.1)),
   R.sub_eq_self _ _ (R.trans (R.sub_congr (R.symm (R.one_mul p)) (R.refl _)) (R.trans (R.symm (R.sub_mul R.one q p)) h.2))⟩

/-- the sum of two parts of r is a part of r -/
theorem add_le {p q r : A} (hp : Le R p r) (hq : Le R q r) : Le R (R.add p q) r :=
  ⟨R.trans (R.add_mul p q r) (R.add_congr hp.1 hq.1), R.trans (R.mul_add r p q) (R.add_congr hp.2 hq.2)⟩

theorem le_add_l {p q : A} (hp : IsP R p) (h : Orth R p q) : Le R p (R.add p q) :=
  ⟨R.trans (R.mul_add p p q) (R.trans (R.add_congr hp h.1) (R.add_zero p)),
   R.trans (R.add_mul p q p) (R.trans (R.add_congr hp h.2) (R.add_zero p))⟩

theorem le_add_r {p q : A} (hq : IsP R q) (h : Orth R p q) : Le R q (R.add p q) :=
  ⟨R.trans (R.mul_add q p q) (R.trans (R.add_congr h.2 hq) (R.zero_add q)),
   R.trans (R.add_mul p q q) (R.trans (R.add_congr h.1 hq) (R.zero_add q))⟩

theorem le_antisymm {p q : A} (h1 : Le R p q) (h2 : Le R q p) : R.eqv p q := R.trans (R.symm h1.2) h2.1

/-- the order does not see which of two equal operators is written -/
theorem le_congr {p p' q q' : A} (hp : R.eqv p p') (hq : R.eqv q q') (h : Le R p q) : Le R p' q' :=
  ⟨R.trans (R.mul_congr (R.symm hp) (R.symm hq)) (R.trans h.1 hp), R.trans (R.mul_congr (R.symm hq) (R.symm hp)) (R.trans h.2 hp)⟩

/-! ### a lattice carried by the projections -/

variable {α : Type} (L : NLat α)

/-- the lattice IS a lattice of projections of the algebra, in their own order and with 1 − p for the negation;
the sum of two orthogonal members is a member. Nothing is asked of the meet and the join beyond `NLat`. -/
structure Rep where
  e : α → A
  isP : ∀ x, IsP R (e x)
  le_to : ∀ {x y}, L.le x y → Le R (e x) (e y)
  le_of : ∀ {x y}, Le R (e x) (e y) → L.le x y
  neg : ∀ x, R.eqv (e (L.neg x)) (ng R (e x))
  top : R.eqv (e L.top) R.one
  bot : R.eqv (e L.bot) R.zero
  sum : ∀ x y, Orth R (e x) (e y) → ∃ t, R.eqv (e t) (R.add (e x) (e y))

variable {R L}

/-- the two cells of a cut are orthogonal: s ∧ a ≤ a ≤ ¬¬a ≤ ¬(s ∧ ¬a) -/
theorem cells_orth (E : Rep R L) (s a : α) : Orth R (E.e (L.meet s a)) (E.e (L.meet s (L.neg a))) := by
  have h : L.le (L.meet s a) (L.neg (L.meet s (L.neg a))) :=
    L.le_trans (L.le_trans (L.meet_le_r s a) (L.le_nn a)) (L.anti (L.meet_le_r s (L.neg a)))
  exact orth_of_le_ng R (le_congr R (R.refl _) (E.neg _) (E.le_to h))

/-- where s splits along a, its projection is the sum of the projections of the two cells -/
theorem split_sum (E : Rep R L) (s a : α) (h : L.le s (L.join (L.meet s a) (L.meet s (L.neg a)))) :
    R.eqv (E.e s) (R.add (E.e (L.meet s a)) (E.e (L.meet s (L.neg a)))) := by
  have ho := cells_orth E s a
  have ⟨t, ht⟩ := E.sum _ _ ho
  have hu : L.le (L.meet s a) t := E.le_of (le_congr R (R.refl _) (R.symm ht) (le_add_l R (E.isP _) ho))
  have hu' : L.le (L.meet s (L.neg a)) t := E.le_of (le_congr R (R.refl _) (R.symm ht) (le_add_r R (E.isP _) ho))
  have hst : Le R (E.e s) (E.e t) := E.le_to (L.le_trans h (L.join_le hu hu'))
  have hts : Le R (E.e t) (E.e s) :=
    le_congr R (R.symm ht) (R.refl _) (add_le R (E.le_to (L.meet_le_l s a)) (E.le_to (L.meet_le_l s (L.neg a))))
  exact R.trans (le_antisymm R hst hts) ht

/-! ### a count: additive on orthogonal projections, in whole numbers -/

/-- a weight in whole numbers ("how many of N"); it does not see which of two equal operators is written -/
structure NWt (R : Alg A) where
  c : A → Nat
  congr : ∀ {p q}, R.eqv p q → c p = c q
  additive : ∀ {p q}, IsP R p → IsP R q → Orth R p q → c (R.add p q) = c p + c q

theorem nwt_mono (W : NWt R) {p q : A} (hp : IsP R p) (hq : IsP R q) (h : Le R p q) : W.c p ≤ W.c q := by
  have e1 : W.c q = W.c (R.add p (R.sub q p)) := W.congr (R.symm (R.add_sub p q))
  have e2 := W.additive hp (isP_sub R hp hq h) (orth_sub R hp h)
  rw [e1, e2]
  exact Nat.le_add_right _ _

/-- THE COUNT OF LAYER 3 (QZ6.Count), from additivity on orthogonal projections alone -/
def state_count (E : Rep R L) (W : NWt R) : QZ6.Count L where
  c := fun x => W.c (E.e x)
  mono := fun h => nwt_mono W (E.isP _) (E.isP _) (E.le_to h)
  super := by
    intro u u' y hu hu' ho
    have orth := orth_of_le_ng R (le_congr R (R.refl _) (E.neg _) (E.le_to ho))
    have e := W.additive (E.isP u) (E.isP u') orth
    show W.c (E.e u) + W.c (E.e u') ≤ W.c (E.e y)
    rw [← e]
    exact nwt_mono W (isP_add R (E.isP u) (E.isP u') orth) (E.isP y) (add_le R (E.le_to hu) (E.le_to hu'))
  split := by
    intro s a h
    show W.c (E.e s) = W.c (E.e (L.meet s a)) + W.c (E.e (L.meet s (L.neg a)))
    rw [W.congr (split_sum E s a h)]
    exact W.additive (E.isP _) (E.isP _) (cells_orth E s a)

/-! ### a probability: additive on orthogonal projections, in any scale that can add -/

variable {D : Type}

/-- what the scale of QZ5 needs beside its order: an addition, and the complement as "what is missing to one" -/
structure SAdd (S : QZ5.Scale D) where
  add : D → D → D
  le_refl : ∀ a, S.le a a
  co_le : ∀ {a b}, add a b = S.one → S.le b (S.co a)
  le_co : ∀ {a b}, add a b = S.one → S.le (S.co a) b

/-- a weight: additive on orthogonal projections, one at 1, zero at 0, and NOT NEGATIVE on a projection of the kind
`ok` (for matrices: the symmetric ones - an oblique idempotent can have a negative form). Not negative is said the
two ways it is used: adding such a projection's weight never lowers, and zero is below it. -/
structure Wt (R : Alg A) (S : QZ5.Scale D) (G : SAdd S) where
  w : A → D
  ok : A → Prop
  ok_sub : ∀ {p q}, ok p → ok q → ok (R.sub q p)
  congr : ∀ {p q}, R.eqv p q → w p = w q
  additive : ∀ {p q}, IsP R p → IsP R q → Orth R p q → w (R.add p q) = G.add (w p) (w q)
  one : w R.one = S.one
  zero : w R.zero = S.zero
  le_add : ∀ {p q}, IsP R q → ok q → S.le (w p) (G.add (w p) (w q))
  zero_le : ∀ {p}, IsP R p → ok p → S.le S.zero (w p)

theorem wt_mono {S : QZ5.Scale D} {G : SAdd S} (W : Wt R S G) {p q : A} (hp : IsP R p) (hq : IsP R q) (h : Le R p q)
    (op : W.ok p) (oq : W.ok q) : S.le (W.w p) (W.w q) := by
  have e1 : W.w q = W.w (R.add p (R.sub q p)) := W.congr (R.symm (R.add_sub p q))
  have e2 := W.additive hp (isP_sub R hp hq h) (orth_sub R hp h)
  rw [e1, e2]
  exact W.le_add (isP_sub R hp hq h) (W.ok_sub op oq)

theorem wt_ng {S : QZ5.Scale D} {G : SAdd S} (W : Wt R S G) {p : A} (hp : IsP R p) :
    G.add (W.w p) (W.w (ng R p)) = S.one := by
  have e := W.additive hp (isP_ng R hp) (orth_ng R hp)
  rw [← e, W.congr (add_ng R p), W.one]

/-- along a splitting the weight is the sum of the weights of the two cells (what QZ6 asks of a count, for a weight
in any scale) -/
theorem wt_split {S : QZ5.Scale D} {G : SAdd S} (E : Rep R L) (W : Wt R S G) (s a : α)
    (h : L.le s (L.join (L.meet s a) (L.meet s (L.neg a)))) :
    W.w (E.e s) = G.add (W.w (E.e (L.meet s a))) (W.w (E.e (L.meet s (L.neg a)))) := by
  rw [W.congr (split_sum E s a h)]
  exact W.additive (E.isP _) (E.isP _) (cells_orth E s a)

/-- THE PROBABILITY OF LAYER 3 (QZ5.Prob), from additivity on orthogonal projections alone (`hok`: the lattice's
projections are of the kind on which the weight is not negative) -/
def state_prob {S : QZ5.Scale D} {G : SAdd S} (E : Rep R L) (W : Wt R S G) (hok : ∀ x, W.ok (E.e x)) : QZ5.Prob L S where
  μ := fun x => W.w (E.e x)
  mono := fun {x y} h => wt_mono W (E.isP _) (E.isP _) (E.le_to h) (hok x) (hok y)
  neg_le := by
    intro x
    show S.le (W.w (E.e (L.neg x))) (S.co (W.w (E.e x)))
    rw [W.congr (E.neg x)]
    exact G.co_le (wt_ng W (E.isP x))
  neg_ge := by
    intro x
    show S.le (S.co (W.w (E.e x))) (W.w (E.e (L.neg x)))
    rw [W.congr (E.neg x)]
    exact G.le_co (wt_ng W (E.isP x))
  zero_le := fun x => W.zero_le (E.isP x) (hok x)
  le_one := by
    intro x
    have h := wt_mono W (E.isP x) (E.isP L.top) (E.le_to (L.le_top x)) (hok x) (hok L.top)
    rw [W.congr E.top, W.one] at h
    exact h
  top_ge := by
    show S.le S.one (W.w (E.e L.top))
    rw [W.congr E.top, W.one]
    exact G.le_refl _
  bot_le := by
    show S.le (W.w (E.e L.bot)) S.zero
    rw [W.congr E.bot, W.zero]
    exact G.le_refl _

/-! ### an instance that does not commute: the 2×2 matrices over the two-element field, and the qubit's lattice in them -/

/-- a 2×2 matrix over {0, 1} (false = 0, true = 1; addition is xor, and subtraction is the same) -/
structure M2 where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  deriving DecidableEq

def madd (x y : M2) : M2 := ⟨xor x.a y.a, xor x.b y.b, xor x.c y.c, xor x.d y.d⟩
def mmul (x y : M2) : M2 :=
  ⟨xor (x.a && y.a) (x.b && y.c), xor (x.a && y.b) (x.b && y.d), xor (x.c && y.a) (x.d && y.c), xor (x.c && y.b) (x.d && y.d)⟩
def m0 : M2 := ⟨false, false, false, false⟩
def m1 : M2 := ⟨true, false, false, true⟩

theorem m_mul_add : ∀ a b c d a' b' c' d' a'' b'' c'' d'' : Bool,
    mmul ⟨a, b, c, d⟩ (madd ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩) =
    madd (mmul ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩) (mmul ⟨a, b, c, d⟩ ⟨a'', b'', c'', d''⟩) := by decide
theorem m_add_mul : ∀ a b c d a' b' c' d' a'' b'' c'' d'' : Bool,
    mmul (madd ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩) ⟨a'', b'', c'', d''⟩ =
    madd (mmul ⟨a, b, c, d⟩ ⟨a'', b'', c'', d''⟩) (mmul ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩) := by decide
theorem m_mul_one : ∀ a b c d : Bool, mmul ⟨a, b, c, d⟩ m1 = ⟨a, b, c, d⟩ := by decide
theorem m_one_mul : ∀ a b c d : Bool, mmul m1 ⟨a, b, c, d⟩ = ⟨a, b, c, d⟩ := by decide
theorem m_add_zero : ∀ a b c d : Bool, madd ⟨a, b, c, d⟩ m0 = ⟨a, b, c, d⟩ := by decide
theorem m_zero_add : ∀ a b c d : Bool, madd m0 ⟨a, b, c, d⟩ = ⟨a, b, c, d⟩ := by decide
theorem m_sub_self : ∀ a b c d : Bool, madd ⟨a, b, c, d⟩ ⟨a, b, c, d⟩ = m0 := by decide
theorem m_add_sub : ∀ a b c d a' b' c' d' : Bool,
    madd ⟨a, b, c, d⟩ (madd ⟨a', b', c', d'⟩ ⟨a, b, c, d⟩) = ⟨a', b', c', d'⟩ := by decide
theorem m_sub_eq_self : ∀ a b c d a' b' c' d' : Bool,
    madd ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ = ⟨a, b, c, d⟩ → (⟨a', b', c', d'⟩ : M2) = m0 := by decide

/-- the algebra: its laws are checked over every matrix (the kernel's `decide`) -/
def f2 : Alg M2 where
  eqv := Eq
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h k => h.trans k
  add_congr := fun h k => by rw [h, k]
  sub_congr := fun h k => by rw [h, k]
  mul_congr := fun h k => by rw [h, k]
  add := madd
  sub := madd
  mul := mmul
  zero := m0
  one := m1
  mul_add := fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩ => m_mul_add a b c d a' b' c' d' a'' b'' c'' d''
  add_mul := fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩ => m_add_mul a b c d a' b' c' d' a'' b'' c'' d''
  mul_sub := fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩ => m_mul_add a b c d a' b' c' d' a'' b'' c'' d''
  sub_mul := fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ ⟨a'', b'', c'', d''⟩ => m_add_mul a b c d a' b' c' d' a'' b'' c'' d''
  mul_one := fun ⟨a, b, c, d⟩ => m_mul_one a b c d
  one_mul := fun ⟨a, b, c, d⟩ => m_one_mul a b c d
  add_zero := fun ⟨a, b, c, d⟩ => m_add_zero a b c d
  zero_add := fun ⟨a, b, c, d⟩ => m_zero_add a b c d
  sub_self := fun ⟨a, b, c, d⟩ => m_sub_self a b c d
  sub_zero := fun ⟨a, b, c, d⟩ => m_add_zero a b c d
  add_sub := fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ => m_add_sub a b c d a' b' c' d'
  sub_eq_self := fun ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ => m_sub_eq_self a b c d a' b' c' d'

/-- the qubit's six questions as matrices: a and its negation on the diagonal, b and its negation askew -/
def emb : Q → M2
  | .bot => m0 | .top => m1
  | .a => ⟨true, false, false, false⟩ | .a' => ⟨false, false, false, true⟩
  | .b => ⟨true, true, false, false⟩ | .b' => ⟨false, true, false, true⟩

/-- a and b do not commute: this is not a Boolean algebra of projections -/
theorem emb_not_commuting : mmul (emb .a) (emb .b) ≠ mmul (emb .b) (emb .a) := by decide

theorem emb_isP : ∀ x : Q, mmul (emb x) (emb x) = emb x := by decide
theorem emb_le_to : ∀ x y : Q, qle x y → mmul (emb x) (emb y) = emb x ∧ mmul (emb y) (emb x) = emb x := by decide
theorem emb_le_of : ∀ x y : Q, mmul (emb x) (emb y) = emb x ∧ mmul (emb y) (emb x) = emb x → qle x y := by decide
theorem emb_neg : ∀ x : Q, emb (qneg x) = madd m1 (emb x) := by decide
theorem emb_sum : ∀ x y : Q, mmul (emb x) (emb y) = m0 ∧ mmul (emb y) (emb x) = m0 → emb (qjoin x y) = madd (emb x) (emb y) := by
  decide

/-- the qubit's lattice (QZ3.mo2) is a lattice of projections of this algebra -/
def qubitRep : Rep f2 mo2 where
  e := emb
  isP := emb_isP
  le_to := fun {x y} h => emb_le_to x y h
  le_of := fun {x y} h => emb_le_of x y h
  neg := emb_neg
  top := rfl
  bot := rfl
  sum := fun x y h => ⟨qjoin x y, emb_sum x y h⟩

/-- a count on the matrices: QZ6's own on the six embedded questions (a certain: 2 of 2; b: 1 of 2), and the same
on the two projections the lattice does not use -/
def cnt (x : M2) : Nat :=
  if x = m1 then 2 else if x = emb .a then 2 else if x = emb .a' then 0 else if x = m0 then 0
  else if mmul x x = x then 1 else 0

theorem cnt_additive : ∀ a b c d a' b' c' d' : Bool,
    mmul ⟨a, b, c, d⟩ ⟨a, b, c, d⟩ = ⟨a, b, c, d⟩ → mmul ⟨a', b', c', d'⟩ ⟨a', b', c', d'⟩ = ⟨a', b', c', d'⟩ →
    mmul ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ = m0 ∧ mmul ⟨a', b', c', d'⟩ ⟨a, b, c, d⟩ = m0 →
    cnt (madd ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩) = cnt ⟨a, b, c, d⟩ + cnt ⟨a', b', c', d'⟩ := by decide

def qubitWt : NWt f2 where
  c := cnt
  congr := fun h => congrArg cnt h
  additive := fun {p q} hp hq h => by
    cases p; cases q
    exact cnt_additive _ _ _ _ _ _ _ _ hp hq h

/-- QZ6's count on the qubit, obtained from the general theorem: additivity on orthogonal projections is all it is -/
def qubitRank : QZ6.Count mo2 := state_count qubitRep qubitWt

/-- and it IS the count of QZ6 (`twice`), question by question -/
theorem cnt_is_twice : ∀ x : Q, cnt (emb x) = QZ6.twice x := by decide

/-! ### the same for the probability: a scale that can add -/

/-- the degrees 0, 1/2, 1 of QZ5 and "more than one" (so that the addition is total and never lowers) -/
inductive H4 | o | h | i | x
  deriving DecidableEq

instance (p : H4 → Prop) [DecidablePred p] : Decidable (∀ y : H4, p y) :=
  decidable_of_iff (p .o ∧ p .h ∧ p .i ∧ p .x)
    ⟨fun ⟨h0, h1, h2, h3⟩ y => by cases y <;> assumption, fun k => ⟨k .o, k .h, k .i, k .x⟩⟩

def rk4 : H4 → Nat
  | .o => 0 | .h => 1 | .i => 2 | .x => 3
def le4 (a b : H4) : Prop := rk4 a ≤ rk4 b
instance (a b : H4) : Decidable (le4 a b) := inferInstanceAs (Decidable (rk4 a ≤ rk4 b))
def co4 : H4 → H4
  | .o => .i | .h => .h | .i => .o | .x => .o
def mn4 (a b : H4) : H4 := if rk4 a ≤ rk4 b then a else b
def mx4 (a b : H4) : H4 := if rk4 a ≤ rk4 b then b else a
/-- (every pair written out: overlapping patterns would bring `propext` into the kernel's `decide`) -/
def add4 : H4 → H4 → H4
  | .o, .o => .o | .o, .h => .h | .o, .i => .i | .o, .x => .x
  | .h, .o => .h | .h, .h => .i | .h, .i => .x | .h, .x => .x
  | .i, .o => .i | .i, .h => .x | .i, .i => .x | .i, .x => .x
  | .x, .o => .x | .x, .h => .x | .x, .i => .x | .x, .x => .x

def half4 : QZ5.Scale H4 where
  le := le4
  zero := .o
  one := .i
  co := co4
  mn := mn4
  mx := mx4
  le_trans := by intro a b c; revert a b c; decide
  co_anti := by intro a b; revert a b; decide
  le_mn := by intro a u v; revert a u v; decide
  mx_le := by intro a u v; revert a u v; decide
  le_zero_of := by decide

theorem co_le4 : ∀ a b : H4, add4 a b = .i → le4 b (co4 a) := by decide
theorem le_co4 : ∀ a b : H4, add4 a b = .i → le4 (co4 a) b := by decide

def half4Add : SAdd half4 where
  add := add4
  le_refl := (by decide : ∀ a : H4, le4 a a)
  co_le := fun {a b} h => co_le4 a b h
  le_co := fun {a b} h => le_co4 a b h

/-- the Born weight of the qubit in the state where a is sure, on the matrices: QZ5's `born` on the six embedded
questions, one half on the two projections the lattice does not use -/
def wgt (m : M2) : H4 :=
  if m = m1 then .i else if m = emb .a then .i else if m = emb .a' then .o else if m = m0 then .o
  else if mmul m m = m then .h else .o

theorem wgt_additive : ∀ a b c d a' b' c' d' : Bool,
    mmul ⟨a, b, c, d⟩ ⟨a, b, c, d⟩ = ⟨a, b, c, d⟩ → mmul ⟨a', b', c', d'⟩ ⟨a', b', c', d'⟩ = ⟨a', b', c', d'⟩ →
    mmul ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ = m0 ∧ mmul ⟨a', b', c', d'⟩ ⟨a, b, c, d⟩ = m0 →
    wgt (madd ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩) = add4 (wgt ⟨a, b, c, d⟩) (wgt ⟨a', b', c', d'⟩) := by decide

def qubitBorn : Wt f2 half4 half4Add where
  w := wgt
  ok := fun _ => True
  ok_sub := fun _ _ => True.intro
  congr := fun h => congrArg wgt h
  le_add := fun {p q} _ _ => (by decide : ∀ a b : H4, le4 a (add4 a b)) (wgt p) (wgt q)
  zero_le := fun {p} _ _ => (by decide : ∀ a : H4, le4 .o a) (wgt p)
  additive := fun {p q} hp hq h => by
    cases p; cases q
    exact wgt_additive _ _ _ _ _ _ _ _ hp hq h
  one := rfl
  zero := rfl

/-- QZ5's probability on the qubit, obtained from the general theorem -/
def qubitProb : QZ5.Prob mo2 half4 := state_prob qubitRep qubitBorn (fun _ => True.intro)

/-- and it IS QZ5's `born`, question by question (0, 1/2, 1 read in the larger scale) -/
def up : QZ5.H → H4
  | .o => .o | .h => .h | .i => .i
theorem wgt_is_born : ∀ q : Q, wgt (emb q) = up (QZ5.born q) := by decide

end QZ7

#print axioms QZ7.isP_ng
#print axioms QZ7.orth_of_le_ng
#print axioms QZ7.cells_orth
#print axioms QZ7.split_sum
#print axioms QZ7.nwt_mono
#print axioms QZ7.state_count
#print axioms QZ7.wt_mono
#print axioms QZ7.state_prob
#print axioms QZ7.f2
#print axioms QZ7.emb_not_commuting
#print axioms QZ7.qubitRep
#print axioms QZ7.qubitRank
#print axioms QZ7.cnt_is_twice
#print axioms QZ7.half4Add
#print axioms QZ7.qubitProb
#print axioms QZ7.wgt_is_born
#print axioms QZ7.wt_split
