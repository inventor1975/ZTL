import ZTL
import ZRead
import QZ3
/-!
# QZ, theorem 5 — layer 3: the range that order alone gives holds for every probability. With AI, 2026-11-27.

    sh research/qz/build.sh

A PROBABILITY on the lattice is asked for two things only:
    it is monotone                       x ≤ y  ⇒  μ x ≤ μ y
    it turns negation into complement    μ (¬x) = 1 − μ x          (written as two inequalities with `co`)
together with 0 ≤ μ ≤ 1, μ ⊤ = 1, μ ⊥ = 0. The Born probability of a state on the subspaces of a quantum system is
one (standard, not proved here); so is any classical probability; so is a two-valued truth assignment.
Additivity, a joint distribution of the questions, the distributive law: NOT asked. The numbers themselves live in
any ordered scale with a complement, a least and a greatest element, minimum and maximum (`Scale`) — no real numbers
are needed, and none are used.

THE RANGE (`rng`), from the ranges of the atoms, by order alone:
    ¬φ      [1 − hi, 1 − lo]
    φ ∧ ψ   [0, min(hi φ, hi ψ)]
    φ ∨ ψ   [max(lo φ, lo ψ), 1]
    φ → ψ   [max(1 − hi φ, lo ψ), 1]        (the kernel's own reading ¬φ ∨ ψ)
    φ ⊕ ψ, φ ↔ ψ   [0, 1]                    (order says nothing)
This is the range `qz_guard.order_range` computes, the one that never missed in 71368 exact two-qubit cases while the
Boole–Fréchet range of the kernel's degree calculus missed 8296 times across contexts (research/qz/degree_probe.py).

THEOREM (`range_sound`). If every atom's probability lies in its range, the probability of every formula lies in
the range computed for it — in every lattice of QZ3, for every such probability.

COROLLARY (`earned_prob_one`, `refuted_prob_zero`). What the kernel calls EARNED has probability 1, and what it
calls REFUTED has probability 0, in every state that the knowledge `s` is sure of (μ s = 1). So the three layers meet:
a strict verdict is probability 1 or 0 everywhere; a stable verdict is that inside a context (QZ4); the rest is a
number, and its order-only range is always right.

PRIOR WORK (2026-11-27). That quantum probabilities violate the classical bounds across contexts is known: Pitowsky,
"George Boole's 'Conditions of Possible Experience' and the Quantum Puzzle", BJPS 1994 — Bell inequalities are a
special case of Boole's conditions, and a violation needs frequencies that are not measured on one sample (abstract
and secondary sources only; the paper itself not read). A state on a partial Boolean algebra is defined in
Abramsky–Barbosa (arXiv 2011.03064, Definition 6, read) with ν(¬x) = 1 − ν(x) and additivity on commeasurable pairs.
The order-only range itself is elementary; no source for it as a named result was looked for.

Boundary. The range is wide: its mean width in the census was 0.46 against 0.12–0.17 for the kernel's range. Inside
one context the kernel's own range is the right, sharper tool; that it is sound there is measured (0 of 23320), not
proved here.
-/

namespace QZ5
open V QZ3

/-- an ordered scale of degrees: least, greatest, complement, minimum, maximum -/
structure Scale (D : Type) where
  le : D → D → Prop
  zero : D
  one : D
  co : D → D
  mn : D → D → D
  mx : D → D → D
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  co_anti : ∀ {a b}, le a b → le (co b) (co a)
  le_mn : ∀ {a x y}, le a x → le a y → le a (mn x y)
  mx_le : ∀ {a x y}, le x a → le y a → le (mx x y) a
  le_zero_of : ∀ p, le one (co p) → le p zero

variable {α D : Type} (L : NLat α) (S : Scale D)

/-- a probability on the lattice: monotone, complement on negation, bounded, 1 at the top, 0 at the bottom -/
structure Prob where
  μ : α → D
  mono : ∀ {x y}, L.le x y → S.le (μ x) (μ y)
  neg_le : ∀ x, S.le (μ (L.neg x)) (S.co (μ x))
  neg_ge : ∀ x, S.le (S.co (μ x)) (μ (L.neg x))
  zero_le : ∀ x, S.le S.zero (μ x)
  le_one : ∀ x, S.le (μ x) S.one
  top_ge : S.le S.one (μ L.top)
  bot_le : S.le (μ L.bot) S.zero

/-- the range that order alone gives -/
def rng (lo hi : Nat → D) : Fm → D × D
  | .atom n    => (lo n, hi n)
  | .top       => (S.one, S.one)
  | .bot       => (S.zero, S.zero)
  | .neg φ     => (S.co (rng lo hi φ).2, S.co (rng lo hi φ).1)
  | .conj φ ψ  => (S.zero, S.mn (rng lo hi φ).2 (rng lo hi ψ).2)
  | .disj φ ψ  => (S.mx (rng lo hi φ).1 (rng lo hi ψ).1, S.one)
  | .imp φ ψ   => (S.mx (S.co (rng lo hi φ).2) (rng lo hi ψ).1, S.one)
  | .xor _ _   => (S.zero, S.one)
  | .xnor _ _  => (S.zero, S.one)

/-- **QZ 5.** The probability of every formula lies in its order-only range. -/
theorem range_sound (P : Prob L S) (val : Nat → α) (lo hi : Nat → D)
    (h : ∀ n, S.le (lo n) (P.μ (val n)) ∧ S.le (P.μ (val n)) (hi n)) :
    ∀ φ : Fm, S.le (rng S lo hi φ).1 (P.μ (qe L val φ)) ∧ S.le (P.μ (qe L val φ)) (rng S lo hi φ).2
  | .atom n => h n
  | .top => ⟨P.top_ge, P.le_one _⟩
  | .bot => ⟨P.zero_le _, P.bot_le⟩
  | .neg φ =>
    have ih := range_sound P val lo hi h φ
    ⟨S.le_trans (S.co_anti ih.2) (P.neg_ge _), S.le_trans (P.neg_le _) (S.co_anti ih.1)⟩
  | .conj φ ψ =>
    have i1 := range_sound P val lo hi h φ
    have i2 := range_sound P val lo hi h ψ
    ⟨P.zero_le _, S.le_mn (S.le_trans (P.mono (L.meet_le_l _ _)) i1.2) (S.le_trans (P.mono (L.meet_le_r _ _)) i2.2)⟩
  | .disj φ ψ =>
    have i1 := range_sound P val lo hi h φ
    have i2 := range_sound P val lo hi h ψ
    ⟨S.mx_le (S.le_trans i1.1 (P.mono (L.le_join_l _ _))) (S.le_trans i2.1 (P.mono (L.le_join_r _ _))), P.le_one _⟩
  | .imp φ ψ =>
    have i1 := range_sound P val lo hi h φ
    have i2 := range_sound P val lo hi h ψ
    ⟨S.mx_le (S.le_trans (S.le_trans (S.co_anti i1.2) (P.neg_ge _)) (P.mono (L.le_join_l _ _)))
             (S.le_trans i2.1 (P.mono (L.le_join_r _ _))), P.le_one _⟩
  | .xor _ _ => ⟨P.zero_le _, P.le_one _⟩
  | .xnor _ _ => ⟨P.zero_le _, P.le_one _⟩

/-- **The layers meet (1).** EARNED by the kernel: probability 1 in every state the knowledge is sure of. -/
theorem earned_prob_one (P : Prob L S) (s : α) (v : Nat → V) (val : Nat → α) (ag : Agrees L s v val) (φ : Fm)
    (e : earnedR v φ) (sure : S.le S.one (P.μ s)) : S.le S.one (P.μ (qe L val φ)) :=
  S.le_trans sure (P.mono (earned_sound L s v val ag φ e))

/-- **The layers meet (2).** REFUTED by the kernel: probability 0 there. -/
theorem refuted_prob_zero (P : Prob L S) (s : α) (v : Nat → V) (val : Nat → α) (ag : Agrees L s v val) (φ : Fm)
    (r : refutedR v φ) (sure : S.le S.one (P.μ s)) : S.le (P.μ (qe L val φ)) S.zero :=
  S.le_zero_of _ (S.le_trans (S.le_trans sure (P.mono (refuted_sound L s v val ag φ r))) (P.neg_le _))

/-! ### the classes are not empty: one qubit prepared "up along Z", asked along Z (a) and along X (b) -/

/-- the three degrees that occur: 0, 1/2, 1 -/
inductive H | o | h | i
  deriving DecidableEq

instance (p : H → Prop) [DecidablePred p] : Decidable (∀ x : H, p x) :=
  decidable_of_iff (p .o ∧ p .h ∧ p .i)
    ⟨fun ⟨h0,h1,h2⟩ x => by cases x <;> assumption, fun k => ⟨k .o, k .h, k .i⟩⟩

def hrank : H → Nat
  | .o => 0 | .h => 1 | .i => 2
def hle (x y : H) : Prop := hrank x ≤ hrank y
instance (x y : H) : Decidable (hle x y) := inferInstanceAs (Decidable (hrank x ≤ hrank y))
def hco : H → H
  | .o => .i | .h => .h | .i => .o
def hmn (x y : H) : H := if hrank x ≤ hrank y then x else y
def hmx (x y : H) : H := if hrank x ≤ hrank y then y else x

def half : Scale H where
  le := hle
  zero := .o
  one := .i
  co := hco
  mn := hmn
  mx := hmx
  le_trans := by intro a b c; revert a b c; decide
  co_anti := by intro a b; revert a b; decide
  le_mn := by intro a x y; revert a x y; decide
  mx_le := by intro a x y; revert a x y; decide
  le_zero_of := by decide

/-- the Born probabilities of that qubit on MO2: a sure, a' impossible, b and b' one half each -/
def born : Q → H
  | .bot => .o | .top => .i | .a => .i | .a' => .o | .b => .h | .b' => .h

theorem born_mono : ∀ x y : Q, qle x y → hle (born x) (born y) := by decide

def qubit : Prob mo2 half where
  μ := born
  mono := fun {x y} h => born_mono x y h
  neg_le := (by decide : ∀ x : Q, hle (born (qneg x)) (hco (born x)))
  neg_ge := (by decide : ∀ x : Q, hle (hco (born x)) (born (qneg x)))
  zero_le := (by decide : ∀ x : Q, hle .o (born x))
  le_one := (by decide : ∀ x : Q, hle (born x) .i)
  top_ge := (by decide : hle .i (born .top))
  bot_le := (by decide : hle (born .bot) .o)

/-- On that qubit the two classical bounds that order does NOT give are both false: P(a ∧ b) = 0 although
P(a) + P(b) − 1 = 1/2, and P(a' ∨ b) = 1 although P(a') + P(b) = 1/2. (Boole–Fréchet fails across contexts.) -/
theorem frechet_fails_across :
    born (qmeet .a .b) = .o ∧ born .a = .i ∧ born .b = .h ∧ born (qjoin .a' .b) = .i ∧ born .a' = .o := by decide

end QZ5

#print axioms QZ5.range_sound
#print axioms QZ5.earned_prob_one
#print axioms QZ5.refuted_prob_zero
#print axioms QZ5.qubit
#print axioms QZ5.frechet_fails_across
