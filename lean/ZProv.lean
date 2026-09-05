/-
  ZProv.lean — E34: PROVENANCE SEMIRINGS EMBED, AND INTO WHICH REGISTER.

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

/-- What each source is worth: earned, unverified, or refuted. -/
def Trust := Nat → V

/-! ### The lazy register IS a commutative semiring -/

theorem kor_comm    : ∀ a b : V, kor a b = kor b a := by decide
theorem kor_assoc   : ∀ a b c : V, kor (kor a b) c = kor a (kor b c) := by decide
theorem kor_zero    : ∀ a : V, kor F a = a := by decide
theorem kand_comm   : ∀ a b : V, kand a b = kand b a := by decide
theorem kand_assoc  : ∀ a b c : V, kand (kand a b) c = kand a (kand b c) := by decide
theorem kand_one    : ∀ a : V, kand T a = a := by decide
theorem kand_zero   : ∀ a : V, kand F a = F := by decide
theorem kand_distrib : ∀ a b c : V,
    kand a (kor b c) = kor (kand a b) (kand a c) := by decide

/-! ### The greedy register is NOT one — and not for want of the right units -/

/-- No constant is neutral for the greedy `∨`. -/
theorem greedy_no_additive_unit : ∀ e : V, ¬ (∀ a : V, zor e a = a) := by decide

/-- No constant is neutral for the greedy `∧`. -/
theorem greedy_no_multiplicative_unit :
    ∀ e : V, ¬ (∀ a : V, zand e a = a) := by decide

/-- And the obstruction has a name: it is the mark, in both operations. -/
theorem greedy_obstruction : zor F Z = F ∧ zand T Z = F := ⟨rfl, rfl⟩

/-! ### Evaluation, and it is a homomorphism by construction -/

/-- Evaluate a provenance expression against a trust assignment, in the LAZY
register. -/
def ev (τ : Trust) : Prov → V
  | Prov.var n   => τ n
  | Prov.zero    => F
  | Prov.one     => T
  | Prov.add p q => kor  (ev τ p) (ev τ q)
  | Prov.mul p q => kand (ev τ p) (ev τ q)

theorem ev_add (τ : Trust) (p q : Prov) :
    ev τ (Prov.add p q) = kor (ev τ p) (ev τ q) := rfl
theorem ev_mul (τ : Trust) (p q : Prov) :
    ev τ (Prov.mul p q) = kand (ev τ p) (ev τ q) := rfl
theorem ev_zero (τ : Trust) : ev τ Prov.zero = F := rfl
theorem ev_one  (τ : Trust) : ev τ Prov.one  = T := rfl

/-! ### The semiring laws survive evaluation — so the map is well defined on
     provenance polynomials, not merely on their syntax -/

theorem ev_add_comm (τ : Trust) (p q : Prov) :
    ev τ (Prov.add p q) = ev τ (Prov.add q p) := kor_comm _ _

theorem ev_add_assoc (τ : Trust) (p q r : Prov) :
    ev τ (Prov.add (Prov.add p q) r) = ev τ (Prov.add p (Prov.add q r)) :=
  kor_assoc _ _ _

theorem ev_add_zero (τ : Trust) (p : Prov) :
    ev τ (Prov.add Prov.zero p) = ev τ p := kor_zero _

theorem ev_mul_comm (τ : Trust) (p q : Prov) :
    ev τ (Prov.mul p q) = ev τ (Prov.mul q p) := kand_comm _ _

theorem ev_mul_assoc (τ : Trust) (p q r : Prov) :
    ev τ (Prov.mul (Prov.mul p q) r) = ev τ (Prov.mul p (Prov.mul q r)) :=
  kand_assoc _ _ _

theorem ev_mul_one (τ : Trust) (p : Prov) :
    ev τ (Prov.mul Prov.one p) = ev τ p := kand_one _

theorem ev_mul_zero (τ : Trust) (p : Prov) :
    ev τ (Prov.mul Prov.zero p) = ev τ Prov.zero := kand_zero _

theorem ev_distrib (τ : Trust) (p q r : Prov) :
    ev τ (Prov.mul p (Prov.add q r))
      = ev τ (Prov.add (Prov.mul p q) (Prov.mul p r)) :=
  kand_distrib _ _ _

/-! ### Withdrawal: what retracting a source costs

    The operational half. "Retracting a source zeroes a variable" (§20); here
    that is a definition, and what follows from it is a theorem. -/

/-- Retract one source: its variable goes to refuted, everything else stands.
`Nat.beq` with its own reflexivity, not `==` — see the header. -/
def retract (τ : Trust) (x : Nat) : Trust :=
  fun n => match Nat.beq n x with
           | true  => F
           | false => τ n

theorem natBeq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0     => rfl
  | n + 1 => natBeq_refl n

/-- The trust order: refuted below unverified below earned. -/
def trustLe : V → V → Bool
  | T, T => true  | T, F => false | T, Z => false
  | F, T => true  | F, F => true  | F, Z => true
  | Z, T => true  | Z, F => false | Z, Z => true

theorem trustLe_refl : ∀ a : V, trustLe a a = true := by decide
theorem trustLe_F    : ∀ a : V, trustLe F a = true := by decide
theorem kor_mono  : ∀ a b c d : V, trustLe a c = true → trustLe b d = true →
    trustLe (kor a b) (kor c d) = true := by decide
theorem kand_mono : ∀ a b c d : V, trustLe a c = true → trustLe b d = true →
    trustLe (kand a b) (kand c d) = true := by decide

theorem retract_le (τ : Trust) (x n : Nat) :
    trustLe (retract τ x n) (τ n) = true := by
  show trustLe (match Nat.beq n x with | true => F | false => τ n) (τ n) = true
  cases Nat.beq n x with
  | true  => exact trustLe_F _
  | false => exact trustLe_refl _

/-- **WITHDRAWAL NEVER RAISES TRUST.** Whatever the derivation, retracting a
source can only move its verdict down the order — never up. -/
theorem ev_retract_le (τ : Trust) (x : Nat) :
    ∀ p : Prov, trustLe (ev (retract τ x) p) (ev τ p) = true
  | Prov.var n   => retract_le τ x n
  | Prov.zero    => trustLe_refl _
  | Prov.one     => trustLe_refl _
  | Prov.add p q => kor_mono  _ _ _ _ (ev_retract_le τ x p) (ev_retract_le τ x q)
  | Prov.mul p q => kand_mono _ _ _ _ (ev_retract_le τ x p) (ev_retract_le τ x q)

/-- A joint requirement dies with any one of its sources. -/
theorem requirement_dies (τ : Trust) (x y : Nat) :
    ev (retract τ x) (Prov.mul (Prov.var x) (Prov.var y)) = F := by
  show kand (retract τ x x) (retract τ x y) = F
  have hx : retract τ x x = F := by
    show (match Nat.beq x x with | true => F | false => τ x) = F
    rw [natBeq_refl x]
  rw [hx]
  exact kand_zero _

/-- An alternative survives losing one of its sources — the other monomial
carries the fact. This is the 2007 paper's `A·B + C` behaviour, here as a
theorem about our register. -/
theorem alternative_survives (τ : Trust) (x y : Nat)
    (hxy : Nat.beq y x = false) (h : τ y = T) :
    ev (retract τ x) (Prov.add (Prov.var x) (Prov.var y)) = T := by
  show kor (retract τ x x) (retract τ x y) = T
  have hx : retract τ x x = F := by
    show (match Nat.beq x x with | true => F | false => τ x) = F
    rw [natBeq_refl x]
  have hy : retract τ x y = T := by
    show (match Nat.beq y x with | true => F | false => τ y) = T
    rw [hxy]; exact h
  rw [hx, hy]
  rfl

/-! ### Classical provenance is the mark-free case, in either register -/

/-- The same evaluation read GREEDILY — the verdict register. -/
def evG (τ : Trust) : Prov → V
  | Prov.var n   => τ n
  | Prov.zero    => F
  | Prov.one     => T
  | Prov.add p q => zor  (evG τ p) (evG τ q)
  | Prov.mul p q => zand (evG τ p) (evG τ q)

theorem classical_or : ∀ a b : V, a ≠ Z → b ≠ Z →
    (kor a b = zor a b ∧ kor a b ≠ Z) := by decide
theorem classical_and : ∀ a b : V, a ≠ Z → b ≠ Z →
    (kand a b = zand a b ∧ kand a b ≠ Z) := by decide

/-- **ON MARK-FREE TRUST THE TWO REGISTERS COINCIDE.** So the Boolean-semiring
case the 2007 paper starts from is recovered exactly, and the split between
the registers is a fact about marks alone. -/
theorem registers_agree (τ : Trust) (hτ : ∀ n, τ n ≠ Z) :
    ∀ p : Prov, ev τ p = evG τ p ∧ ev τ p ≠ Z
  | Prov.var n   => ⟨rfl, hτ n⟩
  | Prov.zero    => ⟨rfl, fun h => nomatch h⟩
  | Prov.one     => ⟨rfl, fun h => nomatch h⟩
  | Prov.add p q => by
      have hp := registers_agree τ hτ p
      have hq := registers_agree τ hτ q
      have hc := classical_or (ev τ p) (ev τ q) hp.2 hq.2
      show (kor (ev τ p) (ev τ q) = zor (evG τ p) (evG τ q))
         ∧ kor (ev τ p) (ev τ q) ≠ Z
      rw [← hp.1, ← hq.1]
      exact ⟨hc.1, hc.2⟩
  | Prov.mul p q => by
      have hp := registers_agree τ hτ p
      have hq := registers_agree τ hτ q
      have hc := classical_and (ev τ p) (ev τ q) hp.2 hq.2
      show (kand (ev τ p) (ev τ q) = zand (evG τ p) (evG τ q))
         ∧ kand (ev τ p) (ev τ q) ≠ Z
      rw [← hp.1, ← hq.1]
      exact ⟨hc.1, hc.2⟩

end ZProv

#print axioms ZProv.kor_zero
#print axioms ZProv.kand_one
#print axioms ZProv.kand_distrib
#print axioms ZProv.greedy_no_additive_unit
#print axioms ZProv.greedy_no_multiplicative_unit
#print axioms ZProv.greedy_obstruction
#print axioms ZProv.ev_add
#print axioms ZProv.ev_distrib
#print axioms ZProv.ev_retract_le
#print axioms ZProv.requirement_dies
#print axioms ZProv.alternative_survives
#print axioms ZProv.registers_agree
