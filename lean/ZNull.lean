/-
  ZNull.lean — E50: SQL's NULL — THE LAZY REGISTER INSIDE, THE FOUR SIGNS AT
  THE BOUNDARY.

  THE TRADITION. SQL (1986; here as ISO/IEC 9075-2, SQL/Foundation): a
  comparison with a NULL operand yields the truth value UNKNOWN; the
  connectives AND / OR / NOT are three-valued inside a search condition; a
  WHERE clause retains exactly the rows whose condition is TRUE; a CHECK
  constraint is satisfied iff its condition is NOT FALSE; and the <boolean
  test> IS [NOT] TRUE / FALSE / UNKNOWN reads a two-valued answer off the
  three-valued expression. §1 of the paper lists it as the second tradition:
  "three-valued logic inside expressions, forced falsehood at the WHERE
  boundary". §4 places it on the collapse scale at "never (it flows)". This
  file is the embedding, and — as with NaN — the theorems are sharper than
  the slogan.

  WHAT IS PROVED (empty axiom list).

    1. THE EXPRESSION LAYER IS THE LAZY REGISTER. `toV` sends TRUE/FALSE/
       UNKNOWN to T/F/Z and is a homomorphism from SQL's three tables onto
       `knot`, `kand`, `kor` — cell for cell, by `decide`. And it is NOT the
       greedy register: `NOT NOT UNKNOWN` is UNKNOWN, `¬¬Z` is T.

    2. THE COMPARISON WITH NULL IS THE MARK ATOM — the SAME atom IEEE's
       `==` landed on in `ZNaN`: `toV (sqlEq x y) = zeq (embD x) (embD y)`.
       Two traditions, one ZTL atom.

    3. THE BOUNDARIES ARE THE FOUR SIGNS. WHERE keeps a row iff `SignT`;
       CHECK passes iff `SignP` ("not F"); IS TRUE / IS FALSE / IS NOT TRUE /
       IS NOT FALSE are `SignT / SignF / SignN / SignP`; IS UNKNOWN is the
       mark test `SignT (isZ …)`. SQL's <boolean test> is the sign alphabet
       of the tableaux, under other names.

    4. SQL HAS TWO BOUNDARIES WITH OPPOSITE DEFAULTS, ZTL ONE. `x < NULL`
       and `x >= NULL` are both dropped by WHERE (Libkin–Peterfreund's "false
       in both polarities", §4) — and both PASS a CHECK. ZTL's collapse is
       WHERE's: the mark falls to F, never to T.

    5. WHERE AGREES WITH ZTL'S GREEDY VERDICT ON EVERY NEGATION-NORMAL
       SEARCH CONDITION — `SignT (greedy c) = SignT (lazy c)` when negation
       stands only on atoms — AND PARTS EXACTLY WHERE A NEGATION STANDS OVER
       A COMPOUND: `¬¬Z`, the signature cell (T greedily, Z lazily). At the
       CHECK boundary they part already on `TRUE AND NULL`.

    6. SQL'S TWO EQUALITIES. `NULL = NULL` is UNKNOWN, yet `NULL IS NOT
       DISTINCT FROM NULL` is TRUE ("two null values are not distinct" —
       the rule DISTINCT and GROUP BY run on). ZTL has one equality and it
       withholds: `zeq mark mark = Z`. §17's "SQL's inconsistency is not
       inherited", as a theorem.

  WHAT IS NOT DONE. Tables, joins, aggregates, the relational algebra: not
  modelled. The truth-value layer and its four boundaries are mapped — the
  algebraic core of the tradition, not the language. Fifth core.

  FORM. The comparison atoms are read off `ZNaN.cmp3`, so no `Int` order
  lemma is used (they carry propext, measured). All match cells explicit;
  `∀` over the new finite types gets its own Decidable instance.
-/
import ZNaN

namespace ZNull

open V
open ZNaN

/-! ### SQL's truth values and tables (ISO/IEC 9075-2, §8: <search condition>) -/

inductive Tv where
  | tt | ff | un
  deriving DecidableEq, Repr

instance (p : Tv → Prop) [DecidablePred p] : Decidable (∀ x : Tv, p x) :=
  decidable_of_iff (p Tv.tt ∧ p Tv.ff ∧ p Tv.un)
    ⟨fun ⟨a, b, c⟩ x => match x with | Tv.tt => a | Tv.ff => b | Tv.un => c,
     fun h => ⟨h Tv.tt, h Tv.ff, h Tv.un⟩⟩

def sqlNot : Tv → Tv
  | Tv.tt => Tv.ff | Tv.ff => Tv.tt | Tv.un => Tv.un

def sqlAnd : Tv → Tv → Tv
  | Tv.tt, Tv.tt => Tv.tt | Tv.tt, Tv.ff => Tv.ff | Tv.tt, Tv.un => Tv.un
  | Tv.ff, Tv.tt => Tv.ff | Tv.ff, Tv.ff => Tv.ff | Tv.ff, Tv.un => Tv.ff
  | Tv.un, Tv.tt => Tv.un | Tv.un, Tv.ff => Tv.ff | Tv.un, Tv.un => Tv.un

def sqlOr : Tv → Tv → Tv
  | Tv.tt, Tv.tt => Tv.tt | Tv.tt, Tv.ff => Tv.tt | Tv.tt, Tv.un => Tv.tt
  | Tv.ff, Tv.tt => Tv.tt | Tv.ff, Tv.ff => Tv.ff | Tv.ff, Tv.un => Tv.un
  | Tv.un, Tv.tt => Tv.tt | Tv.un, Tv.ff => Tv.un | Tv.un, Tv.un => Tv.un

def toV : Tv → V
  | Tv.tt => T | Tv.ff => F | Tv.un => Z

/-! ### 1. The expression layer is the lazy register -/

theorem toV_not : ∀ p, toV (sqlNot p) = knot (toV p) := by decide
theorem toV_and : ∀ p q, toV (sqlAnd p q) = kand (toV p) (toV q) := by decide
theorem toV_or  : ∀ p q, toV (sqlOr p q) = kor (toV p) (toV q) := by decide

/-- …and not the greedy one: the signature cell. -/
theorem not_the_greedy_register :
    toV (sqlNot (sqlNot Tv.un)) = Z ∧ znot (znot Z) = T := by decide

/-! ### 2. The comparison with NULL is the mark atom — the same one as IEEE's -/

inductive Dv where
  | v    : Int → Dv
  | null : Dv
  deriving DecidableEq, Repr

def embD : Dv → ZQ
  | Dv.v a  => ZQ.val a
  | Dv.null => ZQ.mark

/-- §8.2 <comparison predicate>: UNKNOWN if either operand is the null value. -/
def sqlEq : Dv → Dv → Tv
  | Dv.v a, Dv.v b =>
      match cmp3 a b with
      | Ord3.lt => Tv.ff | Ord3.eq => Tv.tt | Ord3.gt => Tv.ff
  | Dv.v _, Dv.null => Tv.un
  | Dv.null, Dv.v _ => Tv.un
  | Dv.null, Dv.null => Tv.un

def sqlLt : Dv → Dv → Tv
  | Dv.v a, Dv.v b =>
      match cmp3 a b with
      | Ord3.lt => Tv.tt | Ord3.eq => Tv.ff | Ord3.gt => Tv.ff
  | Dv.v _, Dv.null => Tv.un
  | Dv.null, Dv.v _ => Tv.un
  | Dv.null, Dv.null => Tv.un

def sqlGe : Dv → Dv → Tv
  | Dv.v a, Dv.v b =>
      match cmp3 a b with
      | Ord3.lt => Tv.ff | Ord3.eq => Tv.tt | Ord3.gt => Tv.tt
  | Dv.v _, Dv.null => Tv.un
  | Dv.null, Dv.v _ => Tv.un
  | Dv.null, Dv.null => Tv.un

/-- **SQL's `=` and IEEE's `==` land on ONE ZTL atom.** -/
theorem eq_atom : ∀ x y : Dv, toV (sqlEq x y) = zeq (embD x) (embD y)
  | Dv.v a, Dv.v b => by
      show toV (match cmp3 a b with | Ord3.lt => Tv.ff | Ord3.eq => Tv.tt | Ord3.gt => Tv.ff)
         = (match cmp3 a b with | Ord3.lt => F | Ord3.eq => T | Ord3.gt => F)
      cases cmp3 a b <;> rfl
  | Dv.v _, Dv.null => rfl
  | Dv.null, Dv.v _ => rfl
  | Dv.null, Dv.null => rfl

theorem lt_atom : ∀ x y : Dv, toV (sqlLt x y) = zlt (embD x) (embD y)
  | Dv.v a, Dv.v b => by
      show toV (match cmp3 a b with | Ord3.lt => Tv.tt | Ord3.eq => Tv.ff | Ord3.gt => Tv.ff)
         = (match cmp3 a b with | Ord3.lt => T | Ord3.eq => F | Ord3.gt => F)
      cases cmp3 a b <;> rfl
  | Dv.v _, Dv.null => rfl
  | Dv.null, Dv.v _ => rfl
  | Dv.null, Dv.null => rfl

/-- "NULL = NULL is not true" (§17). -/
theorem null_eq_null : sqlEq Dv.null Dv.null = Tv.un := rfl

/-! ### 3. The boundaries are the four signs -/

/-- §7 <where clause>: the rows for which the search condition is True. -/
def whereKeeps : Tv → Bool
  | Tv.tt => true | Tv.ff => false | Tv.un => false

/-- §4 / §11 <check constraint definition>: satisfied iff the condition is
not False — UNKNOWN passes. -/
def checkPasses : Tv → Bool
  | Tv.tt => true | Tv.ff => false | Tv.un => true

/-- SQL:1999 §8.x <boolean test>. -/
def isTrue       : Tv → Bool | Tv.tt => true  | Tv.ff => false | Tv.un => false
def isFalse      : Tv → Bool | Tv.tt => false | Tv.ff => true  | Tv.un => false
def isUnknown    : Tv → Bool | Tv.tt => false | Tv.ff => false | Tv.un => true
def isNotTrue    : Tv → Bool | Tv.tt => false | Tv.ff => true  | Tv.un => true
def isNotFalse   : Tv → Bool | Tv.tt => true  | Tv.ff => false | Tv.un => true
def isNotUnknown : Tv → Bool | Tv.tt => true  | Tv.ff => true  | Tv.un => false

theorem where_signT  : ∀ p, whereKeeps p  = SignT (toV p) := by decide
theorem check_signP  : ∀ p, checkPasses p = SignP (toV p) := by decide
theorem isTrue_signT     : ∀ p, isTrue p     = SignT (toV p) := by decide
theorem isFalse_signF    : ∀ p, isFalse p    = SignF (toV p) := by decide
theorem isNotTrue_signN  : ∀ p, isNotTrue p  = SignN (toV p) := by decide
theorem isNotFalse_signP : ∀ p, isNotFalse p = SignP (toV p) := by decide
/-- IS UNKNOWN is the mark test — quarantine detectable from inside (§1). -/
theorem isUnknown_isZ    : ∀ p, isUnknown p  = SignT (isZ (toV p)) := by decide
theorem isNotUnknown_isZ : ∀ p, isNotUnknown p = !SignT (isZ (toV p)) := by decide

/-! ### 4. Two boundaries, opposite defaults -/

/-- Libkin–Peterfreund's "false in both polarities" (§4), for the standard
itself: WHERE drops `x < NULL` and `x >= NULL` alike… -/
theorem where_both_polarities : ∀ x : Dv,
    whereKeeps (sqlLt x Dv.null) = false ∧ whereKeeps (sqlGe x Dv.null) = false
  | Dv.v _  => ⟨rfl, rfl⟩
  | Dv.null => ⟨rfl, rfl⟩

/-- …and a CHECK constraint PASSES both. -/
theorem check_both_polarities : ∀ x : Dv,
    checkPasses (sqlLt x Dv.null) = true ∧ checkPasses (sqlGe x Dv.null) = true
  | Dv.v _  => ⟨rfl, rfl⟩
  | Dv.null => ⟨rfl, rfl⟩

/-- **ZTL'S COLLAPSE IS WHERE'S, NEVER CHECK'S.** Made to answer, the mark
falls to F in every greedy connective; there is no default-allow. -/
theorem collapse_is_where :
    SignT (znot Z) = false ∧ SignT (zand T Z) = false ∧ SignT (zor F Z) = false
  ∧ SignP (zand T Z) = false := by decide

/-! ### 5. WHERE agrees with the greedy verdict on negation-normal conditions -/

/-- A search condition in negation normal form over atom values: negation
stands on atoms only. -/
inductive Cond where
  | lit  : V → Cond
  | nlit : V → Cond
  | and  : Cond → Cond → Cond
  | or   : Cond → Cond → Cond

/-- SQL's reading: the lazy register. -/
def evalK : Cond → V
  | Cond.lit a  => a
  | Cond.nlit a => knot a
  | Cond.and c d => kand (evalK c) (evalK d)
  | Cond.or c d  => kor (evalK c) (evalK d)

/-- ZTL's reading: the greedy register. -/
def evalG : Cond → V
  | Cond.lit a  => a
  | Cond.nlit a => znot a
  | Cond.and c d => zand (evalG c) (evalG d)
  | Cond.or c d  => zor (evalG c) (evalG d)

theorem signT_znot_knot : ∀ a, SignT (znot a) = SignT (knot a) := by decide
theorem signT_zand : ∀ a b, SignT (zand a b) = (SignT a && SignT b) := by decide
theorem signT_kand : ∀ a b, SignT (kand a b) = (SignT a && SignT b) := by decide
theorem signT_zor  : ∀ a b, SignT (zor a b)  = (SignT a || SignT b) := by decide
theorem signT_kor  : ∀ a b, SignT (kor a b)  = (SignT a || SignT b) := by decide

/-- **AT THE WHERE BOUNDARY, SQL AND ZTL AGREE ON EVERY NEGATION-NORMAL
SEARCH CONDITION.** The two registers have the same T-cells at every
connective; they differ only in what the non-T cells are (F against Z), and
a negation over a compound is the only thing that can see that. -/
theorem where_agrees_nnf : ∀ c : Cond, SignT (evalG c) = SignT (evalK c)
  | Cond.lit _ => rfl
  | Cond.nlit a => signT_znot_knot a
  | Cond.and c d => by
      show SignT (zand (evalG c) (evalG d)) = SignT (kand (evalK c) (evalK d))
      rw [signT_zand, signT_kand, where_agrees_nnf c, where_agrees_nnf d]
  | Cond.or c d => by
      show SignT (zor (evalG c) (evalG d)) = SignT (kor (evalK c) (evalK d))
      rw [signT_zor, signT_kor, where_agrees_nnf c, where_agrees_nnf d]

/-- **AND PART EXACTLY WHERE A NEGATION STANDS OVER A COMPOUND**: `¬¬Z`, the
signature cell — kept by ZTL's verdict, dropped by SQL's WHERE. -/
theorem where_departs_double_negation :
    SignT (znot (znot Z)) = true ∧ SignT (knot (knot Z)) = false := by decide

/-- At the CHECK boundary they part already on `TRUE AND NULL`: ZTL's F fails
the constraint, SQL's UNKNOWN passes it. -/
theorem check_departs_on_conjunction :
    SignP (zand T Z) = false ∧ SignP (kand T Z) = true := by decide

/-! ### 6. SQL's two equalities, ZTL's one -/

/-- `IS NOT DISTINCT FROM`: "two null values are not distinct" — the rule
DISTINCT and GROUP BY run on. -/
def sqlNotDistinct : Dv → Dv → Tv
  | Dv.v a, Dv.v b =>
      match cmp3 a b with
      | Ord3.lt => Tv.ff | Ord3.eq => Tv.tt | Ord3.gt => Tv.ff
  | Dv.v _, Dv.null => Tv.ff
  | Dv.null, Dv.v _ => Tv.ff
  | Dv.null, Dv.null => Tv.tt

/-- **SQL AFFIRMS THE IDENTITY OF MARKS IN ONE PREDICATE AND WITHHOLDS IT IN
THE OTHER; ZTL WITHHOLDS.** §17: the inconsistency is not inherited. -/
theorem two_equalities :
    sqlEq Dv.null Dv.null = Tv.un ∧ sqlNotDistinct Dv.null Dv.null = Tv.tt
  ∧ zeq ZQ.mark ZQ.mark = Z := ⟨rfl, rfl, rfl⟩

/-- Off the null the two SQL equalities coincide with each other and with the
ZTL atom. -/
theorem equalities_agree_off_null (a b : Int) :
    sqlNotDistinct (Dv.v a) (Dv.v b) = sqlEq (Dv.v a) (Dv.v b) := by
  show (match cmp3 a b with | Ord3.lt => Tv.ff | Ord3.eq => Tv.tt | Ord3.gt => Tv.ff)
     = (match cmp3 a b with | Ord3.lt => Tv.ff | Ord3.eq => Tv.tt | Ord3.gt => Tv.ff)
  rfl

end ZNull

#print axioms ZNull.toV_not
#print axioms ZNull.toV_and
#print axioms ZNull.toV_or
#print axioms ZNull.not_the_greedy_register
#print axioms ZNull.eq_atom
#print axioms ZNull.lt_atom
#print axioms ZNull.where_signT
#print axioms ZNull.check_signP
#print axioms ZNull.isNotTrue_signN
#print axioms ZNull.isUnknown_isZ
#print axioms ZNull.where_both_polarities
#print axioms ZNull.check_both_polarities
#print axioms ZNull.collapse_is_where
#print axioms ZNull.where_agrees_nnf
#print axioms ZNull.where_departs_double_negation
#print axioms ZNull.check_departs_on_conjunction
#print axioms ZNull.two_equalities
#print axioms ZNull.equalities_agree_off_null
