/-!
# ZLrat — an LRAT checker whose soundness is a theorem, so a SAT solver's refutation is checked by the kernel.

The solver (CaDiCaL) SEARCHES and writes an LRAT certificate; this file CHECKS it. `check_sound`: if the checker
accepts a certificate for a formula, the formula has no satisfying assignment. The checker is run by the kernel
(`rfl`), so a result proved this way rests on the empty axiom list — no compiled code is trusted.

Only RUP steps (the hints of each added clause, in order, make every hint clause unit or the last one empty under
the negation of the added clause). RAT steps (negative hints) are rejected: the checker answers false, which is
sound — a refusal never proves anything.

WHY (2026-11-06, the curator: "если есть решение и к нему можно прикрутить судью — идём сюда"). The SAT solver built
into our Lean toolchain (`bv_decide`, CaDiCaL) leaves `_native.bv_decide` on the axiom list: its certificate is
accepted by compiled code, so ZTL reads such a result as ON CREDIT to that code. Checking the certificate in the
kernel makes it EARNED, and the cost grows with the certificate, not with the 2^n assignments (measured on
van der Waerden numbers, `ZLratVdw`).

NOT CLAIMED: that `vdw N k` means what its comment says is read off the definition, not proved as a separate
lemma; a fast checker (the kernel check is slow and memory-hungry on large certificates — W(3,6), 622 LRAT
lines: ~50 s, 8.8 GB, MEASURED 2026-11-06, left out of the build for that reason).
-/

namespace ZLrat

structure Lit where
  v : Nat
  neg : Bool

def p (v : Nat) : Lit := ⟨v, false⟩
def n (v : Nat) : Lit := ⟨v, true⟩

/-- value of a literal under a total assignment -/
def lval (a : Nat → Bool) (l : Lit) : Bool := bne (a l.v) l.neg

def csat (a : Nat → Bool) : List Lit → Bool
  | [] => false
  | l :: c => lval a l || csat a c

def fsat (a : Nat → Bool) : List (List Lit) → Bool
  | [] => true
  | c :: f => csat a c && fsat a f

def nlit (l : Lit) : Lit := ⟨l.v, !l.neg⟩

def leq (l m : Lit) : Bool := Nat.beq l.v m.v && (l.neg == m.neg)

def memL (l : Lit) : List Lit → Bool
  | [] => false
  | m :: A => leq l m || memL l A

/-- `l` is false under the partial assignment `A` (a list of literals taken as true) -/
def isF (A : List Lit) (l : Lit) : Bool := memL (nlit l) A

/-- the literals of a clause not yet false under `A` -/
def unk (A : List Lit) : List Lit → List Lit
  | [] => []
  | l :: c => cond (isF A l) (unk A c) (l :: unk A c)

def negs : List Lit → List Lit
  | [] => []
  | l :: c => nlit l :: negs c

abbrev DB := List (Nat × List Lit)

def look (i : Nat) : DB → Option (List Lit)
  | [] => none
  | (j, c) :: db => cond (Nat.beq i j) (some c) (look i db)

def del1 (i : Nat) : DB → DB
  | [] => []
  | (j, c) :: db => cond (Nat.beq i j) (del1 i db) ((j, c) :: del1 i db)

def delAll : List Nat → DB → DB
  | [], db => db
  | i :: is, db => delAll is (del1 i db)

/-- unit propagation along the hints: true iff the last hint clause becomes empty -/
def rup (db : DB) : List Lit → List Nat → Bool
  | _, [] => false
  | A, h :: hs =>
    match look h db with
    | none => false
    | some D =>
      match unk A D with
      | [] => true
      | [l] => rup db (l :: A) hs
      | _ :: _ :: _ => false

inductive Step where
  | add (id : Nat) (c : List Lit) (hints : List Nat)
  | del (ids : List Nat)

def isNil : List Lit → Bool
  | [] => true
  | _ :: _ => false

/-- accept iff every added clause is RUP and some added clause is empty -/
def check : DB → List Step → Bool
  | _, [] => false
  | db, .add i c hs :: ps => cond (rup db (negs c) hs) (cond (isNil c) true (check ((i, c) :: db) ps)) false
  | db, .del ids :: ps => check (delAll ids db) ps

def index : Nat → List (List Lit) → DB
  | _, [] => []
  | i, c :: f => (i, c) :: index (i + 1) f

/-! ## Soundness -/

def dsat (a : Nat → Bool) : DB → Bool
  | [] => true
  | (_, c) :: db => csat a c && dsat a db

def allT (a : Nat → Bool) : List Lit → Bool
  | [] => true
  | l :: A => lval a l && allT a A

theorem and_l {x y : Bool} (h : (x && y) = true) : x = true := by cases x <;> cases y <;> first | rfl | exact h
theorem and_r {x y : Bool} (h : (x && y) = true) : y = true := by cases x <;> cases y <;> first | rfl | exact h
theorem and_i {x y : Bool} (hx : x = true) (hy : y = true) : (x && y) = true := by rw [hx, hy]; rfl
theorem or_cases {x y : Bool} (h : (x || y) = true) : x = true ∨ y = true := by
  cases x
  · exact Or.inr h
  · exact Or.inl rfl
theorem false_ne_true' (h : false = true) : False := Bool.noConfusion h

theorem beq_eq {i j : Nat} (h : Nat.beq i j = true) : i = j := Nat.eq_of_beq_eq_true h

theorem bool_beq_eq {x y : Bool} (h : (x == y) = true) : x = y := by
  cases x <;> cases y <;> first | rfl | exact absurd h (fun h => Bool.noConfusion h)

theorem leq_eq {l m : Lit} (h : leq l m = true) : l = m := by
  cases l with
  | mk v1 n1 => cases m with
    | mk v2 n2 =>
      have hv : v1 = v2 := beq_eq (and_l h)
      have hn : n1 = n2 := bool_beq_eq (and_r h)
      rw [hv, hn]

theorem memL_val (a : Nat → Bool) (l : Lit) : ∀ A : List Lit, allT a A = true → memL l A = true → lval a l = true
  | [], _, h => absurd h (fun h => Bool.noConfusion h)
  | m :: A, hA, h => by
    cases or_cases h with
    | inl e => rw [leq_eq e]; exact and_l hA
    | inr e => exact memL_val a l A (and_r hA) e

theorem lval_nlit (a : Nat → Bool) (l : Lit) : lval a (nlit l) = !(lval a l) := by
  cases l with
  | mk v ng =>
    show bne (a v) (!ng) = !(bne (a v) ng)
    cases a v <;> cases ng <;> rfl

theorem isF_false (a : Nat → Bool) (A : List Lit) (l : Lit) (hA : allT a A = true) (h : isF A l = true) :
    lval a l = false := by
  have e : lval a (nlit l) = true := memL_val a (nlit l) A hA h
  rw [lval_nlit] at e
  cases hl : lval a l
  · rfl
  · rw [hl] at e; exact absurd e (fun h => Bool.noConfusion h)

theorem unk_nil (a : Nat → Bool) (A : List Lit) (hA : allT a A = true) :
    ∀ D : List Lit, csat a D = true → unk A D = [] → False
  | [], hD, _ => false_ne_true' hD
  | m :: D, hD, hu => by
    cases hf : isF A m
    · have : (m :: unk A D) = [] := by
        have q : unk A (m :: D) = cond (isF A m) (unk A D) (m :: unk A D) := rfl
        rw [q, hf] at hu; exact hu
      cases this
    · have hu' : unk A D = [] := by
        have q : unk A (m :: D) = cond (isF A m) (unk A D) (m :: unk A D) := rfl
        rw [q, hf] at hu; exact hu
      cases or_cases hD with
      | inl e => rw [isF_false a A m hA hf] at e; exact false_ne_true' e
      | inr e => exact unk_nil a A hA D e hu'

theorem unk_one (a : Nat → Bool) (A : List Lit) (hA : allT a A = true) :
    ∀ (D : List Lit) (l : Lit), csat a D = true → unk A D = [l] → lval a l = true
  | [], _, hD, _ => absurd hD (fun h => Bool.noConfusion h)
  | m :: D, l, hD, hu => by
    have q : unk A (m :: D) = cond (isF A m) (unk A D) (m :: unk A D) := rfl
    cases hf : isF A m
    · rw [q, hf] at hu
      have hu2 : m :: unk A D = l :: [] := hu
      injection hu2 with hml hrest
      cases or_cases hD with
      | inl e => rw [← hml]; exact e
      | inr e => exact absurd (unk_nil a A hA D e hrest) id
    · rw [q, hf] at hu
      cases or_cases hD with
      | inl e => rw [isF_false a A m hA hf] at e; exact absurd e (fun h => Bool.noConfusion h)
      | inr e => exact unk_one a A hA D l e hu

theorem look_sat (a : Nat → Bool) (i : Nat) : ∀ (db : DB) (c : List Lit), dsat a db = true → look i db = some c →
    csat a c = true
  | [], _, _, h => by cases h
  | (j, d) :: db, c, hd, h => by
    have q : look i ((j, d) :: db) = cond (Nat.beq i j) (some d) (look i db) := rfl
    cases hb : Nat.beq i j
    · rw [q, hb] at h; exact look_sat a i db c (and_r hd) h
    · rw [q, hb] at h
      have h2 : some d = some c := h
      injection h2 with e
      rw [← e]; exact and_l hd

theorem rup_sound (a : Nat → Bool) (db : DB) (hdb : dsat a db = true) :
    ∀ (hs : List Nat) (A : List Lit), allT a A = true → rup db A hs = true → False
  | [], _, _, h => false_ne_true' h
  | h :: hs, A, hA, hr => by
    have q : rup db A (h :: hs) =
      (match look h db with
        | none => false
        | some D => match unk A D with
          | [] => true
          | [l] => rup db (l :: A) hs
          | _ :: _ :: _ => false) := rfl
    rw [q] at hr
    cases hl : look h db with
    | none => rw [hl] at hr; exact false_ne_true' hr
    | some D =>
      rw [hl] at hr
      have hr2 : (match unk A D with
          | [] => true
          | [l] => rup db (l :: A) hs
          | _ :: _ :: _ => false) = true := hr
      have hD : csat a D = true := look_sat a h db D hdb hl
      cases hu : unk A D with
      | nil => exact unk_nil a A hA D hD hu
      | cons l rest =>
        cases rest with
        | nil =>
          rw [hu] at hr2
          have hv : lval a l = true := unk_one a A hA D l hD hu
          exact rup_sound a db hdb hs (l :: A) (and_i hv hA) hr2
        | cons m rest' => rw [hu] at hr2; exact false_ne_true' hr2

theorem negs_allT (a : Nat → Bool) : ∀ c : List Lit, csat a c = false → allT a (negs c) = true
  | [], _ => rfl
  | l :: c, h => by
    cases hl : lval a l
    · have hc : csat a c = false := by
        have q : csat a (l :: c) = (lval a l || csat a c) := rfl
        rw [q, hl] at h; exact h
      have e : lval a (nlit l) = true := by rw [lval_nlit, hl]; rfl
      exact and_i e (negs_allT a c hc)
    · have q : csat a (l :: c) = (lval a l || csat a c) := rfl
      rw [q, hl] at h; exact absurd h (fun h => Bool.noConfusion h)

/-- a RUP clause is satisfied by every assignment that satisfies the database -/
theorem add_sound (a : Nat → Bool) (db : DB) (hdb : dsat a db = true) (c : List Lit) (hs : List Nat)
    (h : rup db (negs c) hs = true) : csat a c = true := by
  cases hc : csat a c
  · exact absurd (rup_sound a db hdb hs (negs c) (negs_allT a c hc) h) id
  · rfl

theorem del1_sat (a : Nat → Bool) (i : Nat) : ∀ db : DB, dsat a db = true → dsat a (del1 i db) = true
  | [], h => h
  | (j, c) :: db, h => by
    have q : del1 i ((j, c) :: db) = cond (Nat.beq i j) (del1 i db) ((j, c) :: del1 i db) := rfl
    cases hb : Nat.beq i j
    · rw [q, hb]; exact and_i (and_l h) (del1_sat a i db (and_r h))
    · rw [q, hb]; exact del1_sat a i db (and_r h)

theorem delAll_sat (a : Nat → Bool) : ∀ (is : List Nat) (db : DB), dsat a db = true → dsat a (delAll is db) = true
  | [], _, h => h
  | i :: is, db, h => delAll_sat a is (del1 i db) (del1_sat a i db h)

theorem check_sound_db (a : Nat → Bool) : ∀ (ps : List Step) (db : DB), dsat a db = true → check db ps = true → False
  | [], _, _, h => false_ne_true' h
  | .add i c hs :: ps, db, hdb, h => by
    have q : check db (.add i c hs :: ps) =
      cond (rup db (negs c) hs) (cond (isNil c) true (check ((i, c) :: db) ps)) false := rfl
    rw [q] at h
    cases hr : rup db (negs c) hs
    · rw [hr] at h; exact false_ne_true' h
    · rw [hr] at h
      have hc : csat a c = true := add_sound a db hdb c hs hr
      cases c with
      | nil => exact false_ne_true' hc
      | cons l c' =>
        exact check_sound_db a ps ((i, l :: c') :: db) (and_i hc hdb) h
  | .del ids :: ps, db, hdb, h => check_sound_db a ps (delAll ids db) (delAll_sat a ids db hdb) h

theorem index_sat (a : Nat → Bool) : ∀ (i : Nat) (f : List (List Lit)), fsat a f = true → dsat a (index i f) = true
  | _, [], _ => rfl
  | i, _ :: f, h => and_i (and_l h) (index_sat a (i + 1) f (and_r h))

/-- **Soundness.** If the checker accepts a certificate for `f` (clauses numbered from 1), `f` is unsatisfiable. -/
theorem check_sound (f : List (List Lit)) (ps : List Step) (h : check (index 1 f) ps = true) :
    ∀ a : Nat → Bool, fsat a f = false := by
  intro a
  cases hf : fsat a f
  · rfl
  · exact absurd (check_sound_db a ps (index 1 f) (index_sat a 1 f hf) h) id

#print axioms check_sound

/-! ## van der Waerden formulas: variable v true = colour 1. Colour 1 has no 3-term progression, colour 0 no
k-term progression. Unsatisfiable on 1..N exactly when every 2-colouring of 1..N has one of them. -/

def kap (a d : Nat) : Nat → List Lit
  | 0 => []
  | i + 1 => p a :: kap (a + d) d i

def clausesAt (N k d a : Nat) : List (List Lit) :=
  cond (Nat.ble (a + 2 * d) N) [[n a, n (a + d), n (a + 2 * d)]] [] ++
  cond (Nat.ble (a + (k - 1) * d) N) [kap a d k] []

def loopA (N k d : Nat) : Nat → Nat → List (List Lit)
  | _, 0 => []
  | a, fuel + 1 => clausesAt N k d a ++ loopA N k d (a + 1) fuel

def loopD (N k : Nat) : Nat → Nat → List (List Lit)
  | _, 0 => []
  | d, fuel + 1 => loopA N k d 1 N ++ loopD N k (d + 1) fuel

def vdw (N k : Nat) : List (List Lit) := loopD N k 1 (N - 1)

end ZLrat
