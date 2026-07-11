import ZSets
import ZGround

/-!
# Lean twins of the expeditions E6–E10. Zero axioms.

E6 (reals): digit streams — the equality atom never earns T, apartness
is earned by a finite witness and persists, Cantor's diagonal earns its
non-membership (strict F) against every registry entry.
E7 (functions): taint kills the injectivity certificate — a single
marked pair collapses the ∀-fold, even for the identity function.
E8 (arithmetic): decorrelation, interval apartness, unearned identity.
E9 (probability): verdicts as the {0,1}-thresholds of Bel/Pl.
E10 (modal): atom verdicts are the □/◇ thresholds over completions;
the ¬¬-cell separates the local ladder from global supervaluation.

E11 (Russell): the greedy/parity side is in Facts.lean; the grounding
side (8 of 9 facts classical) needs constants ⊤/⊥ in Fm — recorded as
an honest remainder, not silently skipped.
-/

namespace V

/-! ## E6: streams — unearned identity, earned apartness -/

abbrev Str := Nat → Nat

/-- The stream-equality atom at time t: F on a finite witness of
difference, Z while prefixes agree. T is never earned. -/
def eqStream (x y : Str) : Nat → V
  | 0 => Z
  | t + 1 => if x t = y t then eqStream x y t else F

theorem eqStream_never_T (x y : Str) : ∀ t, eqStream x y t ≠ T := by
  intro t
  induction t with
  | zero => exact fun h => nomatch h
  | succ t ih =>
    show (if x t = y t then eqStream x y t else F) ≠ T
    by_cases h : x t = y t
    · rw [if_pos h]; exact ih
    · rw [if_neg h]; exact fun h => nomatch h

/-- Identity is not earned even by a stream against itself. -/
theorem eqStream_self (x : Str) : ∀ t, eqStream x x t = Z := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show (if x t = x t then eqStream x x t else F) = Z
    rw [if_pos rfl]; exact ih

theorem eqStream_F_mono (x y : Str) (t : Nat)
    (hf : eqStream x y t = F) : eqStream x y (t + 1) = F := by
  show (if x t = y t then eqStream x y t else F) = F
  by_cases h : x t = y t
  · rw [if_pos h]; exact hf
  · rw [if_neg h]

/-- Earned apartness persists: what is refuted stays refuted. -/
theorem eqStream_F_persist (x y : Str) : ∀ u t, t ≤ u →
    eqStream x y t = F → eqStream x y u = F := by
  intro u
  induction u with
  | zero =>
    intro t h hf
    rw [show t = 0 from Nat.le_zero.mp h] at hf
    exact hf
  | succ u ih =>
    intro t h hf
    cases Nat.eq_or_lt_of_le h with
    | inl he => rw [← he]; exact hf
    | inr hlt =>
      exact eqStream_F_mono x y u (ih t (Nat.le_of_lt_succ hlt) hf)

/-- One finite witness earns apartness. -/
theorem eqStream_apart (x y : Str) : ∀ t i, i < t → x i ≠ y i →
    eqStream x y t = F := by
  intro t
  induction t with
  | zero => intro i h _; exact absurd h (Nat.not_lt_zero i)
  | succ t ih =>
    intro i hi hne
    show (if x t = y t then eqStream x y t else F) = F
    by_cases h : x t = y t
    · rw [if_pos h]
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with
      | inl he => exact absurd (by rw [he]; exact h) hne
      | inr hlt => exact ih i hlt hne
    · rw [if_neg h]

/-- k-th stream of a registry (off the end: the zero stream). -/
def nthS : List Str → Nat → Str
  | [], _ => fun _ => 0
  | x :: _, 0 => x
  | _ :: r, k + 1 => nthS r k

/-- Cantor's diagonal: flip the k-th digit of the k-th entry. -/
def diag (reg : List Str) : Str := fun i => nthS reg i i + 1

/-- Membership as an indexed ∃-fold of equality atoms. -/
def memIdx (x : Str) (reg : List Str) (t : Nat) : Nat → V
  | 0 => F
  | k + 1 => zor (eqStream x (nthS reg k) t) (memIdx x reg t k)

theorem zor_no_T : ∀ a b : V, a ≠ T → b ≠ T → zor a b ≠ T := by decide

/-- Failure #1 (non-registrability): a registry of streams certifies
NO membership — not even of its own rows. -/
theorem mem_never_T (x : Str) (reg : List Str) (t : Nat) :
    ∀ k, memIdx x reg t k ≠ T := by
  intro k
  induction k with
  | zero => exact fun h => nomatch h
  | succ k ih => exact zor_no_T _ _ (eqStream_never_T x (nthS reg k) t) ih

/-- Failure #2 (Cantorian): the diagonal EARNS its non-membership —
strict F against every entry, by finite witnesses. -/
theorem diag_not_member (reg : List Str) (t : Nat)
    (ht : reg.length ≤ t) : ∀ k, k ≤ reg.length →
    memIdx (diag reg) reg t k = F := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hlt : k < t := Nat.lt_of_lt_of_le hk ht
    have hdiff : diag reg k ≠ nthS reg k k :=
      Nat.succ_ne_self (nthS reg k k)
    have h1 := eqStream_apart (diag reg) (nthS reg k) t k hlt hdiff
    have h2 := ih (Nat.le_of_succ_le hk)
    show zor (eqStream (diag reg) (nthS reg k) t) (memIdx _ _ _ k) = F
    rw [h1, h2]
    rfl

/-! ## E7: taint kills the injectivity certificate -/

/-- A verified function on values; on marks — taint with a pedigree. -/
def taint (f : Nat → Nat) : El → El
  | .v n => .v (f n)
  | .z i => .z (i + 1)

theorem eqAtom_z_right : ∀ (x : El) (i : Nat), eqAtom x (.z i) = Z := by
  intro x i; cases x <;> rfl

/-- The injectivity certificate: the ∀-fold of eq(f a, f b) → eq(a, b). -/
def injFold (f : El → El) : List (El × El) → V
  | [] => T
  | (a, b) :: r =>
      zand (zimp (eqAtom (f a) (f b)) (eqAtom a b)) (injFold f r)

/-- ONE marked pair collapses the certificate — for every function,
including the identity: Z→Z = F fells the fold. -/
theorem inj_cert_marked (f : Nat → Nat) (a : El) (i : Nat)
    (r : List (El × El)) : injFold (taint f) ((a, El.z i) :: r) = F := by
  show zand (zimp (eqAtom (taint f a) (taint f (.z i)))
                  (eqAtom a (.z i))) (injFold _ r) = F
  rw [show taint f (El.z i) = El.z (i + 1) from rfl,
      eqAtom_z_right (taint f a) (i + 1), eqAtom_z_right a i]
  exact zandFX _

-- clean domains still certify; a mark fells even id
example : injFold (taint id) [(El.v 1, El.v 2)] = T := rfl
example : injFold (taint id) [(El.v 1, El.z 7)] = F := rfl

/-! ## E8: intervals — decorrelation and earned apartness -/

structure Iv where
  lo : Int
  hi : Int
deriving DecidableEq, Repr

def addI (x y : Iv) : Iv := ⟨x.lo + y.lo, x.hi + y.hi⟩
def subI (x y : Iv) : Iv := ⟨x.lo - y.hi, x.hi - y.lo⟩

def ltAtomI (x y : Iv) : V :=
  if x.hi < y.lo then T else if y.hi ≤ x.lo then F else Z

def eqAtomI (x y : Iv) : V :=
  if x.hi < y.lo ∨ y.hi < x.lo then F
  else if x.lo = x.hi ∧ x.lo = y.lo ∧ y.lo = y.hi then T else Z

-- decorrelation: m − m ≠ 0 (two independent readings of one mark)
example : subI ⟨0, 9⟩ ⟨0, 9⟩ = ⟨-9, 9⟩ := rfl
-- apartness EARNED by separated intervals
example : eqAtomI ⟨3, 5⟩ ⟨10, 12⟩ = F := rfl
example : ltAtomI ⟨3, 5⟩ ⟨10, 12⟩ = T := rfl
-- overlap: not forced
example : ltAtomI ⟨3, 5⟩ ⟨4, 6⟩ = Z := rfl
-- verification = narrowing earns the verdict
example : ltAtomI ⟨4, 4⟩ ⟨5, 7⟩ = T := rfl
-- full verification earns identity
example : eqAtomI ⟨5, 5⟩ ⟨5, 5⟩ = T := rfl

/-- Nat-interval twin for general statements (core's Int order lemmas
are omega-proved and carry propext; Int stays for computations). -/
structure IvN where
  lo : Nat
  hi : Nat

def eqAtomN (x y : IvN) : V :=
  if x.hi < y.lo ∨ y.hi < x.lo then F
  else if x.lo = x.hi ∧ x.lo = y.lo ∧ y.lo = y.hi then T else Z

/-- Identity is earned by nothing short of full verification: a
nondegenerate mark does not equal even itself. -/
theorem mark_self_not_earned (lo hi : Nat) (h : lo < hi) :
    eqAtomN ⟨lo, hi⟩ ⟨lo, hi⟩ = Z := by
  show (if hi < lo ∨ hi < lo then F
        else if lo = hi ∧ lo = lo ∧ lo = hi then T else Z) = Z
  rw [if_neg (fun hc : hi < lo ∨ hi < lo =>
        Nat.lt_irrefl lo (Nat.lt_trans h (hc.elim id id))),
      if_neg (fun hc : lo = hi ∧ lo = lo ∧ lo = hi =>
        absurd (hc.1 ▸ h) (Nat.lt_irrefl hi))]

/-! ## E9: verdicts as Dempster–Shafer thresholds -/

/-- T ⟺ Bel = 1 (forced by all readings), F ⟺ Pl = 0 (excluded by
all), else Z. Masses in halves: m({a}) = 1, m({a,b,c}) = 1, total 2. -/
def dsV (bel pl total : Nat) : V :=
  if bel = total then T else if pl = 0 then F else Z

example : dsV 2 2 2 = T := rfl     -- event {a,b,c}: certain
example : dsV 1 2 2 = Z := rfl     -- event {a}: supported, not forced
example : dsV 0 1 2 = Z := rfl     -- event {b}: merely possible
example : dsV 0 0 2 = F := rfl     -- event ∅: excluded by all

/-! ## E10: atom verdicts are the modal thresholds over completions -/

def boxA (x : V) : Bool := (subs x).all (fun b => b)
def diaA (x : V) : Bool := (subs x).any (fun b => b)

/-- Totally: T ⟺ □, F ⟺ ¬◇, Z ⟺ contingency. -/
theorem atom_thresholds : ∀ x : V,
    ((x = T) ↔ boxA x = true) ∧
    ((x = F) ↔ diaA x = false) ∧
    ((x = Z) ↔ (boxA x = false ∧ diaA x = true)) := by decide

/-- Duality ◇ = ¬□¬ over completions. -/
theorem box_dia_duality : ∀ x : V,
    diaA x = !((subs x).all (fun b => !b)) := by decide

/-- Global supervaluation of ¬¬p over the completions of p. -/
def supDN (x : V) : V :=
  if (subs x).all (fun b => !!b) then T
  else if (subs x).any (fun b => !!b) then Z else F

/-- The separating cell: the local ladder earns ¬¬Z = T where the
global □ goes mute — incomparability, machine-checked. -/
theorem ladder_vs_global :
    znot (znot Z) = T ∧ supDN Z = Z ∧ supDN T = T ∧ supDN F = F :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms eqStream_never_T
#print axioms eqStream_self
#print axioms eqStream_apart
#print axioms mem_never_T
#print axioms diag_not_member
#print axioms inj_cert_marked
#print axioms mark_self_not_earned
#print axioms atom_thresholds
#print axioms ladder_vs_global

end V
