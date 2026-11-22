/-
  ZProv.lean — E34: PROVENANCE SEMIRINGS EMBED, AND INTO WHICH REGISTER.

  PURE BRANCH (curator 2026-11-22: only ZTL, burn everything else, totally). The embedding of the semiring
  into the LAZY (strong Kleene) register, its semiring laws there, and every theorem stated through that
  register are REMOVED below (`ev`, `kand_*`, `kor_*`, `ev_*`, `requirement_dies`, `alternative_survives`,
  `registers_agree`). What stays is ZTL's own fact: the greedy operations carry NO semiring structure
  (`greedy_no_additive_unit`, `greedy_no_multiplicative_unit`, `greedy_obstruction`). The text that follows
  is the original header and describes the removed half too.

  WHAT §27 ASKED. "A fragment-embedding theorem for one of the six traditions
  of §1 — the open problem this paper most wants closed. §§13–17 exhibit six
  worked correspondences, but a reproduced case is not an embedding: no
  tradition's own semantics is formalised here and mapped into ZTL.
  Provenance semirings look the most tractable." This file does that for
  semiring provenance (Green–Karvounarakis–Tannen, PODS 2007).

  WHAT IS PROVED, AND THE ANSWER IS SHARPER THAN "IT EMBEDS".

    * The free provenance semiring — sources as variables, `+` for an
      alternative derivation, `·` for a joint requirement — evaluates into
      ZTL's LAZY register as a homomorphism, and the register satisfies every
      semiring law: both operations commutative and associative, `F` neutral
      for `+`, `T` neutral for `·`, `F` annihilating for `·`, and `·`
      distributing over `+`. All by kernel evaluation.

    * The GREEDY OPERATIONS carry no semiring structure — and the failure is
      not "we picked the wrong units": NO constant whatever is neutral for
      `zor`, and none for `zand`. (The claim is about `zor`/`zand`, not about
      the set V, which of course carries the lazy structure above.) The
      obstruction is the mark: `zor F Z = F` and `zand T Z = F`. A verdict
      register refuses, and refusal is not a neutral element.

    * On mark-free trust the two registers coincide, so classical provenance
      — the Boolean-semiring case the 2007 paper starts from — is recovered
      exactly, in either register.

  SO THE HONEST SHAPE OF THE RESULT IS A SPLIT, NOT A CONQUEST. The algebra
  of trust in derivations lives in the lazy register; the greedy register is
  where such an algebra is CASHED, and cashing is provably not a
  homomorphism. That is a boundary of this logic, stated as a theorem rather
  than as a caveat — and it says why the two registers had to be two.

  AND THE SCOPE, STATED BEFORE ANYONE HAS TO ASK. What is formalised here is
  their ALGEBRA — the free commutative semiring on sources, with `+` for an
  alternative and `·` for a joint requirement — and its evaluation. Their
  DATABASE semantics (K-relations, the annotated relational operators) is NOT
  formalised. So this closes §27's ask for the algebraic core of one
  tradition, not for the whole of that tradition. Six worked correspondences
  became one structure-preserving map with a proved obstruction beside it;
  that is the size of the step, and it is not larger.

  WHAT THIS IS NOT. It is not a claim of priority over ProvSQL. Our own probe
  (`db/probe_provenance.py`, measured on PostgreSQL 16.14 / ProvSQL 1.13.0-dev)
  already found that semirings do the cascade, the alternatives and the
  exposed set, and that the shipped package also carries magnitudes through
  aggregation — which this corpus had previously denied in print and has
  withdrawn. This file adds one thing only: where their algebra sits inside
  our two registers, and where it provably cannot sit.

  ФОРМА ПОД ПУСТОЙ СПИСОК. Все развилки — по неперекрывающимся образцам
  (ZTL.lean предупреждает об этом прямо над `kand`: перекрывающийся `_`
  тянет propext через матчер). Равенство натуральных — `Nat.beq` со своей
  рефлексивностью, а не `==`: применение `beq_self_eq_true` к `Nat` тащит
  все три аксиомы через инстанс `LawfulBEq`. Оба промерены сегодня.
-/
import ZTL

namespace ZProv

open V

/-- A provenance expression: source variables, the alternative `+`, the joint
requirement `·`. This is the free commutative semiring on the sources — the
object of the 2007 paper, written as syntax. -/
inductive Prov where
  | var  : Nat → Prov
  | zero : Prov
  | one  : Prov
  | add  : Prov → Prov → Prov
  | mul  : Prov → Prov → Prov

/-- What each source is worth: earned, dirty, or refuted. -/
def Trust := Nat → V

/-! ### The lazy register IS a commutative semiring -/

/-- No constant is neutral for the greedy `∨`. -/
theorem greedy_no_additive_unit : ∀ e : V, ¬ (∀ a : V, zor e a = a) := by decide

/-- No constant is neutral for the greedy `∧`. -/
theorem greedy_no_multiplicative_unit :
    ∀ e : V, ¬ (∀ a : V, zand e a = a) := by decide

/-- And the obstruction has a name: it is the mark, in both operations. -/
theorem greedy_obstruction : zor F Z = F ∧ zand T Z = F := ⟨rfl, rfl⟩

/-! ### Evaluation, and it is a homomorphism by construction -/

/-- Retract one source: its variable goes to refuted, everything else stands.
`Nat.beq` with its own reflexivity, not `==` — see the header. -/
def retract (τ : Trust) (x : Nat) : Trust :=
  fun n => match Nat.beq n x with
           | true  => F
           | false => τ n

theorem natBeq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0     => rfl
  | n + 1 => natBeq_refl n

/-- The trust order: refuted below dirty below earned. -/
def trustLe : V → V → Bool
  | T, T => true  | T, F => false | T, Z => false
  | F, T => true  | F, F => true  | F, Z => true
  | Z, T => true  | Z, F => false | Z, Z => true

theorem trustLe_refl : ∀ a : V, trustLe a a = true := by decide
theorem trustLe_F    : ∀ a : V, trustLe F a = true := by decide
theorem retract_le (τ : Trust) (x n : Nat) :
    trustLe (retract τ x n) (τ n) = true := by
  show trustLe (match Nat.beq n x with | true => F | false => τ n) (τ n) = true
  cases Nat.beq n x with
  | true  => exact trustLe_F _
  | false => exact trustLe_refl _

/-- The same evaluation read GREEDILY — the verdict register. -/
def evG (τ : Trust) : Prov → V
  | Prov.var n   => τ n
  | Prov.zero    => F
  | Prov.one     => T
  | Prov.add p q => zor  (evG τ p) (evG τ q)
  | Prov.mul p q => zand (evG τ p) (evG τ q)

#print axioms ZProv.greedy_no_additive_unit
#print axioms ZProv.greedy_no_multiplicative_unit
#print axioms ZProv.greedy_obstruction
