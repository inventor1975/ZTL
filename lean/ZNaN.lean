/-
  ZNaN.lean — E49: IEEE 754's NaN, AND WHICH SIGN EACH OF ITS PREDICATES IS.

  THE TRADITION. IEEE 754 (1985; here as 754-2019 §5.11 and §6.2.3): a
  floating-point datum may be a NaN; arithmetic on a quiet NaN delivers a
  quiet NaN ("arithmetic is infected"); and comparison places every pair of
  data in exactly one of FOUR relations — less than, equal, greater than,
  UNORDERED — where "every NaN shall compare unordered with everything,
  including itself". The comparison predicates are Booleans read off the
  relation: `<` is true only on LT, `==` only on EQ, and `!=` is true on LT,
  GT and UN. §1 of the paper lists this as the first of six traditions that
  reinvented the logic: "arithmetic is infected, comparisons refuse". Until
  now that was a worked case (`zarith.py`), which §1's own ceiling says is
  not an embedding. This file is the embedding, and it is sharper than the
  slogan.

  WHAT IS PROVED (empty axiom list).

    1. THEIR CONSTRUCTION, AS THEY STATE IT: data `Fl`, the four-way relation
       `rel`, the seven predicates of Table 5.1 as Booleans on it, the
       propagation rule of §6.2.3 for `+ − ×`. Their Boolean layer is
       classical: `pNE r = !pEQ r` for every relation, by `decide`.

    2. INFECTION IS THE LAZY REGISTER. On the mark-carrying integers `ZQ`
       (§15's arithmetic with marks in its bare mode: a mark with no bounds)
       the embedding `emb` is a HOMOMORPHISM for `+` and `−`: a mark flows
       exactly as a NaN does.

    3. EVERY ORDERED PREDICATE IS THE T-SIGN OF A ZTL ATOM. `<` is `SignT` of
       the atom `x < y`; `==` of `x = y`; `>` of `y < x`; `<=` and `>=` of
       the GREEDY disjunction of the two. That is: IEEE's Boolean is ZTL's
       "earned T" test, and IEEE's false conflates ZTL's F with its Z.

    4. THE UNORDERED PREDICATE IS THE MARK TEST: `x ? y` is `SignT (isZ …)`
       of the atom — quarantine detectable from inside, §1, and IEEE has the
       same instrument under another name.

    5. AND `!=` IS THE ONE PREDICATE THAT IS AN N-SIGN. `pNE` is `SignN` of
       the equality atom — "not earned T" — and NOT the T-sign of the
       greedily negated atom: on a mark, IEEE's `x != y` is TRUE while ZTL's
       `¬(x = y)` is `¬Z = F`. So the NaN signature "not equal to itself"
       splits exactly here: both refuse `x == x`; IEEE affirms `x != x`,
       ZTL refuses that too (§18: "neither membership nor non-membership is
       earned"). The two agree off the mark and part on it, by theorem.

  THE BOUNDARY OF THE ARITHMETIC HALF, in the same file: `0 × NaN = NaN`
  in IEEE, while ZTL earns `0 · mark = 0` (§15, forcedness on ℤ). The
  homomorphism holds for `×` off that cell and fails on it — two `rfl`s.

  WHAT IS NOT DONE. Rounding, signed zero, infinities, the signaling NaN, the
  exception flags: not modelled — the finite numbers are integers here, and
  nothing in §5.11 or §6.2.3's NaN clauses depends on them. One tradition's
  algebraic core is mapped, not the standard. Fourth core, not fourth
  tradition — the same honest count as `ZProv`, `ZDempster`, `ZAbsInt`.

  FORM. Every order lemma on `Int` measured today carries propext
  (`Int.lt_irrefl`, `Int.ne_of_lt`, `Int.lt_iff_le_and_ne`). So BOTH sides
  read the order off one three-way comparison `cmp3`, defined from the two
  clean decisions `decide (a = b)` and `decide (a < b)`, and every theorem is
  a case split on its three outcomes. No `_` in any `def` (a wildcard matcher
  carries propext — measured 2026-09-05).
-/
import TableauCert

namespace ZNaN

open V

/-! ### One comparison, three outcomes -/

inductive Ord3 where
  | lt | eq | gt
  deriving DecidableEq, Repr

/-- Trichotomy on ℤ, read off the two clean decisions. `a = b` wins; then
`a < b`; otherwise `a > b`. -/
def cmp3 (a b : Int) : Ord3 :=
  match decide (a = b), decide (a < b) with
  | true,  true  => Ord3.eq
  | true,  false => Ord3.eq
  | false, true  => Ord3.lt
  | false, false => Ord3.gt

/-! ### IEEE 754 — the fragment, as the standard states it -/

/-- A floating-point datum: a finite number or a quiet NaN. -/
inductive Fl where
  | num : Int → Fl
  | nan : Fl
  deriving DecidableEq, Repr

/-- §5.11: "four mutually exclusive relations are possible". -/
inductive Rel where
  | lt | eq | gt | un
  deriving DecidableEq, Repr

/-- Enumeration of the four relations is decidable — the `decide`s below live on it. -/
instance (p : Rel → Prop) [DecidablePred p] : Decidable (∀ r : Rel, p r) :=
  decidable_of_iff (p Rel.lt ∧ p Rel.eq ∧ p Rel.gt ∧ p Rel.un)
    ⟨fun ⟨a, b, c, d⟩ r => match r with
        | Rel.lt => a | Rel.eq => b | Rel.gt => c | Rel.un => d,
     fun h => ⟨h Rel.lt, h Rel.eq, h Rel.gt, h Rel.un⟩⟩

def ofOrd3 : Ord3 → Rel
  | Ord3.lt => Rel.lt
  | Ord3.eq => Rel.eq
  | Ord3.gt => Rel.gt

/-- The relation between two data. "Every NaN shall compare unordered with
everything, including itself." -/
def rel : Fl → Fl → Rel
  | Fl.num a, Fl.num b => ofOrd3 (cmp3 a b)
  | Fl.num _, Fl.nan   => Rel.un
  | Fl.nan,   Fl.num _ => Rel.un
  | Fl.nan,   Fl.nan   => Rel.un

/-- Table 5.1: the predicates, each a Boolean read off the relation. -/
def pLT : Rel → Bool | Rel.lt => true  | Rel.eq => false | Rel.gt => false | Rel.un => false
def pLE : Rel → Bool | Rel.lt => true  | Rel.eq => true  | Rel.gt => false | Rel.un => false
def pEQ : Rel → Bool | Rel.lt => false | Rel.eq => true  | Rel.gt => false | Rel.un => false
def pGE : Rel → Bool | Rel.lt => false | Rel.eq => true  | Rel.gt => true  | Rel.un => false
def pGT : Rel → Bool | Rel.lt => false | Rel.eq => false | Rel.gt => true  | Rel.un => false
/-- "The relation `!=` is TRUE when the operands are unordered." -/
def pNE : Rel → Bool | Rel.lt => true  | Rel.eq => false | Rel.gt => true  | Rel.un => true
def pUN : Rel → Bool | Rel.lt => false | Rel.eq => false | Rel.gt => false | Rel.un => true

/-- §6.2.3: an operation with a quiet NaN input delivers a quiet NaN. -/
def fadd : Fl → Fl → Fl
  | Fl.num a, Fl.num b => Fl.num (a + b)
  | Fl.num _, Fl.nan   => Fl.nan
  | Fl.nan,   Fl.num _ => Fl.nan
  | Fl.nan,   Fl.nan   => Fl.nan

def fsub : Fl → Fl → Fl
  | Fl.num a, Fl.num b => Fl.num (a - b)
  | Fl.num _, Fl.nan   => Fl.nan
  | Fl.nan,   Fl.num _ => Fl.nan
  | Fl.nan,   Fl.nan   => Fl.nan

def fmul : Fl → Fl → Fl
  | Fl.num a, Fl.num b => Fl.num (a * b)
  | Fl.num _, Fl.nan   => Fl.nan
  | Fl.nan,   Fl.num _ => Fl.nan
  | Fl.nan,   Fl.nan   => Fl.nan

/-- Every NaN compares unordered with everything — including itself. -/
theorem rel_nan_left : ∀ y, rel Fl.nan y = Rel.un
  | Fl.num _ => rfl
  | Fl.nan   => rfl
theorem rel_nan_right : ∀ x, rel x Fl.nan = Rel.un
  | Fl.num _ => rfl
  | Fl.nan   => rfl
theorem nan_not_self_equal : pEQ (rel Fl.nan Fl.nan) = false := rfl
theorem nan_self_unequal   : pNE (rel Fl.nan Fl.nan) = true := rfl

/-- **THEIR BOOLEAN LAYER IS CLASSICAL.** `!=` is the complement of `==` on
every relation, the unordered one included — the collapse has already
happened inside the predicate. -/
theorem pNE_compl : ∀ r : Rel, pNE r = !pEQ r := by decide
theorem pGE_compl : ∀ r : Rel, pGE r = true → pLT r = false := by decide
/-- And a NaN falsifies BOTH `<` and `>=` — Libkin–Peterfreund's "false in
both polarities", §4, here for IEEE itself. -/
theorem both_polarities_false : pLT Rel.un = false ∧ pGE Rel.un = false := ⟨rfl, rfl⟩

/-! ### ZTL — arithmetic with marks, bare mode (§15) -/

/-- A quantity: a verified integer, or a mark carrying no bounds. -/
inductive ZQ where
  | val  : Int → ZQ
  | mark : ZQ
  deriving DecidableEq, Repr

def emb : ZQ → Fl
  | ZQ.val a => Fl.num a
  | ZQ.mark  => Fl.nan

theorem emb_inj : ∀ x y : ZQ, emb x = emb y → x = y
  | ZQ.val _, ZQ.val _, h => congrArg (fun f => match f with | Fl.num n => ZQ.val n | Fl.nan => ZQ.mark) h
  | ZQ.val _, ZQ.mark,  h => Fl.noConfusion h
  | ZQ.mark,  ZQ.val _, h => Fl.noConfusion h
  | ZQ.mark,  ZQ.mark,  _ => rfl

/-- The atom `x = y`: T or F when both are verified; the mark otherwise —
identity of a mark with itself is not earned (§15, §26 R3). -/
def zeq : ZQ → ZQ → V
  | ZQ.val a, ZQ.val b =>
      match cmp3 a b with
      | Ord3.lt => F
      | Ord3.eq => T
      | Ord3.gt => F
  | ZQ.val _, ZQ.mark  => Z
  | ZQ.mark,  ZQ.val _ => Z
  | ZQ.mark,  ZQ.mark  => Z

/-- The atom `x < y`. -/
def zlt : ZQ → ZQ → V
  | ZQ.val a, ZQ.val b =>
      match cmp3 a b with
      | Ord3.lt => T
      | Ord3.eq => F
      | Ord3.gt => F
  | ZQ.val _, ZQ.mark  => Z
  | ZQ.mark,  ZQ.val _ => Z
  | ZQ.mark,  ZQ.mark  => Z

/-- The atom `x > y` — read off the same comparison, so that no order lemma
on ℤ is needed anywhere (they all carry propext, measured). -/
def zgt : ZQ → ZQ → V
  | ZQ.val a, ZQ.val b =>
      match cmp3 a b with
      | Ord3.lt => F
      | Ord3.eq => F
      | Ord3.gt => T
  | ZQ.val _, ZQ.mark  => Z
  | ZQ.mark,  ZQ.val _ => Z
  | ZQ.mark,  ZQ.mark  => Z

/-- The mark flows through `+` and `−` (the lazy register). -/
def zadd : ZQ → ZQ → ZQ
  | ZQ.val a, ZQ.val b => ZQ.val (a + b)
  | ZQ.val _, ZQ.mark  => ZQ.mark
  | ZQ.mark,  ZQ.val _ => ZQ.mark
  | ZQ.mark,  ZQ.mark  => ZQ.mark

def zsub : ZQ → ZQ → ZQ
  | ZQ.val a, ZQ.val b => ZQ.val (a - b)
  | ZQ.val _, ZQ.mark  => ZQ.mark
  | ZQ.mark,  ZQ.val _ => ZQ.mark
  | ZQ.mark,  ZQ.mark  => ZQ.mark

/-- `×` with forcedness: `0 · mark` is an EARNED 0 — every reading of the
mark gives 0 on ℤ (§15, `zarith.py`). Elsewhere the mark flows. -/
def zmul : ZQ → ZQ → ZQ
  | ZQ.val a, ZQ.val b => ZQ.val (a * b)
  | ZQ.val a, ZQ.mark  =>
      match decide (a = 0) with
      | true  => ZQ.val 0
      | false => ZQ.mark
  | ZQ.mark,  ZQ.val b =>
      match decide (b = 0) with
      | true  => ZQ.val 0
      | false => ZQ.mark
  | ZQ.mark,  ZQ.mark  => ZQ.mark

/-! ### 2. Infection is the lazy register -/

/-- **`+` IS A HOMOMORPHISM**: a mark flows exactly as a NaN does. -/
theorem emb_add : ∀ x y : ZQ, emb (zadd x y) = fadd (emb x) (emb y)
  | ZQ.val _, ZQ.val _ => rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

theorem emb_sub : ∀ x y : ZQ, emb (zsub x y) = fsub (emb x) (emb y)
  | ZQ.val _, ZQ.val _ => rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-- `×` agrees on verified numbers and on two marks… -/
theorem emb_mul_val (a b : Int) : emb (zmul (ZQ.val a) (ZQ.val b)) = fmul (Fl.num a) (Fl.num b) := rfl
theorem emb_mul_marks : emb (zmul ZQ.mark ZQ.mark) = fmul Fl.nan Fl.nan := rfl

/-- …and on a nonzero number against a mark. -/
theorem emb_mul_nonzero (a : Int) (h : decide (a = 0) = false) :
    emb (zmul (ZQ.val a) ZQ.mark) = fmul (Fl.num a) Fl.nan := by
  show emb (match decide (a = 0) with | true => ZQ.val 0 | false => ZQ.mark) = Fl.nan
  rw [h]
  rfl

/-- **THE BOUNDARY OF THE ARITHMETIC HALF.** `0 × NaN = NaN` for them;
`0 · mark = 0` for us, earned by forcedness on ℤ (§15). The homomorphism
fails on exactly this cell. -/
theorem zero_times_mark :
    fmul (Fl.num 0) Fl.nan = Fl.nan ∧ emb (zmul (ZQ.val 0) ZQ.mark) = Fl.num 0 := ⟨rfl, rfl⟩

theorem emb_mul_not_hom :
    emb (zmul (ZQ.val 0) ZQ.mark) ≠ fmul (emb (ZQ.val 0)) (emb ZQ.mark) := by decide

/-! ### 3. Every ordered predicate is the T-sign of a ZTL atom -/

/-- `<` is `SignT` of the atom `x < y`. -/
theorem pLT_signT : ∀ x y : ZQ, pLT (rel (emb x) (emb y)) = SignT (zlt x y)
  | ZQ.val a, ZQ.val b => by
      show pLT (ofOrd3 (cmp3 a b)) = SignT (match cmp3 a b with | Ord3.lt => T | Ord3.eq => F | Ord3.gt => F)
      cases cmp3 a b <;> rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-- `==` is `SignT` of the atom `x = y`. -/
theorem pEQ_signT : ∀ x y : ZQ, pEQ (rel (emb x) (emb y)) = SignT (zeq x y)
  | ZQ.val a, ZQ.val b => by
      show pEQ (ofOrd3 (cmp3 a b)) = SignT (match cmp3 a b with | Ord3.lt => F | Ord3.eq => T | Ord3.gt => F)
      cases cmp3 a b <;> rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-- `>` is `SignT` of the atom `x > y`. -/
theorem pGT_signT : ∀ x y : ZQ, pGT (rel (emb x) (emb y)) = SignT (zgt x y)
  | ZQ.val a, ZQ.val b => by
      show pGT (ofOrd3 (cmp3 a b)) = SignT (match cmp3 a b with | Ord3.lt => F | Ord3.eq => F | Ord3.gt => T)
      cases cmp3 a b <;> rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-- `<=` is `SignT` of the GREEDY disjunction `x < y ∨ x = y` — on a mark
`zor Z Z = F`, and IEEE's `<=` is false there too. -/
theorem pLE_signT : ∀ x y : ZQ, pLE (rel (emb x) (emb y)) = SignT (zor (zlt x y) (zeq x y))
  | ZQ.val a, ZQ.val b => by
      show pLE (ofOrd3 (cmp3 a b)) =
        SignT (zor (match cmp3 a b with | Ord3.lt => T | Ord3.eq => F | Ord3.gt => F)
                   (match cmp3 a b with | Ord3.lt => F | Ord3.eq => T | Ord3.gt => F))
      cases cmp3 a b <;> rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

theorem pGE_signT : ∀ x y : ZQ, pGE (rel (emb x) (emb y)) = SignT (zor (zgt x y) (zeq x y))
  | ZQ.val a, ZQ.val b => by
      show pGE (ofOrd3 (cmp3 a b)) =
        SignT (zor (match cmp3 a b with | Ord3.lt => F | Ord3.eq => F | Ord3.gt => T)
                   (match cmp3 a b with | Ord3.lt => F | Ord3.eq => T | Ord3.gt => F))
      cases cmp3 a b <;> rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-! ### 4. The unordered predicate is the mark test -/

/-- `x ? y` is `SignT (isZ …)` of the atom: IEEE's "unordered" is ZTL's
"quarantined", detectable from inside (§1). -/
theorem pUN_isZ : ∀ x y : ZQ, pUN (rel (emb x) (emb y)) = SignT (isZ (zeq x y))
  | ZQ.val a, ZQ.val b => by
      show pUN (ofOrd3 (cmp3 a b)) = SignT (isZ (match cmp3 a b with | Ord3.lt => F | Ord3.eq => T | Ord3.gt => F))
      cases cmp3 a b <;> rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-! ### 5. `!=` is the one N-sign -/

/-- **`!=` IS `SignN` OF THE EQUALITY ATOM** — "not earned T", the weak
sign of the tableaux, not the T-sign of anything. -/
theorem pNE_signN : ∀ x y : ZQ, pNE (rel (emb x) (emb y)) = SignN (zeq x y)
  | ZQ.val a, ZQ.val b => by
      show pNE (ofOrd3 (cmp3 a b)) = SignN (match cmp3 a b with | Ord3.lt => F | Ord3.eq => T | Ord3.gt => F)
      cases cmp3 a b <;> rfl
  | ZQ.val _, ZQ.mark  => rfl
  | ZQ.mark,  ZQ.val _ => rfl
  | ZQ.mark,  ZQ.mark  => rfl

/-- Off the mark, `!=` IS the T-sign of the greedily negated atom… -/
theorem pNE_negation_off_mark (a b : Int) :
    pNE (rel (Fl.num a) (Fl.num b)) = SignT (znot (zeq (ZQ.val a) (ZQ.val b))) := by
  show pNE (ofOrd3 (cmp3 a b)) = SignT (znot (match cmp3 a b with | Ord3.lt => F | Ord3.eq => T | Ord3.gt => F))
  cases cmp3 a b <;> rfl

/-- …**AND ON THE MARK IT IS NOT**: IEEE affirms `x != y`, ZTL's `¬(x = y)`
is `¬Z = F`. This is where the two collapses part: IEEE folds "unordered"
INTO the predicate; ZTL's negation is a connective over the atom and
collapses the mark to F. -/
theorem pNE_not_negation_on_mark : ∀ x y : ZQ, (x = ZQ.mark ∨ y = ZQ.mark) →
    pNE (rel (emb x) (emb y)) = true ∧ znot (zeq x y) = F
  | ZQ.val _, ZQ.val _, h => by
      cases h with
      | inl h => exact ZQ.noConfusion h
      | inr h => exact ZQ.noConfusion h
  | ZQ.val _, ZQ.mark,  _ => ⟨rfl, rfl⟩
  | ZQ.mark,  ZQ.val _, _ => ⟨rfl, rfl⟩
  | ZQ.mark,  ZQ.mark,  _ => ⟨rfl, rfl⟩

/-- **THE NaN SIGNATURE, SPLIT.** Both refuse `x == x` on the mark. IEEE
then AFFIRMS `x != x`; ZTL refuses `¬(x = x)` as well — one refusal and an
affirmation against two refusals (§18: neither membership nor non-membership
is earned). -/
theorem nan_signature :
    pEQ (rel Fl.nan Fl.nan) = false ∧ pNE (rel Fl.nan Fl.nan) = true
  ∧ zeq ZQ.mark ZQ.mark = Z ∧ znot (zeq ZQ.mark ZQ.mark) = F := ⟨rfl, rfl, rfl, rfl⟩

end ZNaN

#print axioms ZNaN.pNE_compl
#print axioms ZNaN.both_polarities_false
#print axioms ZNaN.emb_inj
#print axioms ZNaN.emb_add
#print axioms ZNaN.emb_sub
#print axioms ZNaN.emb_mul_nonzero
#print axioms ZNaN.zero_times_mark
#print axioms ZNaN.emb_mul_not_hom
#print axioms ZNaN.pLT_signT
#print axioms ZNaN.pEQ_signT
#print axioms ZNaN.pGT_signT
#print axioms ZNaN.pLE_signT
#print axioms ZNaN.pGE_signT
#print axioms ZNaN.pUN_isZ
#print axioms ZNaN.pNE_signN
#print axioms ZNaN.pNE_negation_off_mark
#print axioms ZNaN.pNE_not_negation_on_mark
#print axioms ZNaN.nan_signature
