import ZTL
import ZOrigin
import ZDirty
/-!
# ZOne — everything from one Z: one occurrence gives a chain; under doubt one atom gives every value; two readings. Zero axioms.
(2026-11-06)

WHY. The curator: "это всё один параметр, который мутирует. А для построения нужны два, отсюда два Z" — and,
when the file was first named ZTwo: "разве смысл не в том, что всё из одного?". The source is one; the two is
how the logic reads it. `ZOrigin` showed Z, F, T born from ONE atom (¬p = F, ¬¬p = T). Here:

  1. ONE OCCURRENCE GIVES A CHAIN. A formula of atoms and connectives (no constants) with exactly one atom
     occurrence is a chain of negations ¬…¬p (`single_is_chain`); under doubt its values run Z, F, T, F, T, …
     (`chain_alternates`). Every binary connective reads two occurrences (`bin_two`).
  2. UNDER PURE DOUBT THE VALUES DO NOT DEPEND ON WHICH ATOMS. With every atom Z, every formula, over any atoms,
     has the value of the same formula with every atom replaced by one atom (`all_from_one`). In particular p ⋆ p
     has the value of p ⋆ q for each binary connective (`table_reads_two`): the table reads one dirty atom used
     twice exactly as two different dirty atoms. Values under pure doubt only: with p clean and q dirty, p ∧ p = T
     and p ∧ q = F.
  3. TWO READINGS OF p ⋆ p. The table reads the two occurrences independently — a rule of ZTL, the dirty rule (a
     value nobody checked may change between two reads), not a discovery. The stable reading (`liftS`: one value at
     both occurrences) differs from it, over all sixteen binary Boolean functions, exactly for those true on the
     diagonal and false somewhere off it (`one_vs_two`); of the five, exactly → and ↔ (`five_split`): p → p and
     p ↔ p are F read independently and T read stably. The stable reading earns whatever the independent one earns
     (`two_earned_one_earned`): the independent reading is the cautious one. On clean values the two coincide
     (`clean_coincide`). Beyond p ⋆ p they part too: p ∨ ¬p is F independently and T stably (`beyond_pp`).
     The judge's IF STABLE is this kind of reading (one value at every occurrence, `ZDirty`), mirrored, not imported;
     the link to `ZChoiceRead.same_pick` is an analogy.

  4. THE VALUE FLIPS — A CASE THE DIRTY READING ALREADY CONTAINS (2026-11-06, the curator: "а если грязный параметр будет стремить значение к
     противоположному?"). Two cases. An owner who sets each read to defeat the verdict is the adversary of `ZGames`
     — ZTL's own semantics (`check_scope_is_ztl`, proved there, not here). A dirty value whose second read is the
     negation of the first is one way to read p ⋆ p (`liftA`; clean values do not flip, by definition): it makes
     p ∨ p and p ⊕ p true and p ↔ p false (`flip_table`). The dirty reading earns exactly what both the same-value
     and the flipping readings earn (`dirty_is_both`, at Z): two reads of a Boolean value are either equal or
     opposite, and it allows both — so flipping is one of its two cases, not a new option.
  5. THE BOUNDARIES OF 4, CLOSED (the curator: "почему бы не попытаться их закрыть?").
     * Only Z can flip (`flip_needs_dirty`): given the readings of the values (`subs`), the clause "clean values do
       not flip" follows; it is not a separate choice.
     * n reads, in a MODEL (`DirtyN`, `StableN`, `FlipN`: reads as a list, a claim as a test on it; tied to ZTL's
       own evaluation in 6): the dirty reading earns only what both earn, for
       every n (`dirtyN_both`); with two reads the converse holds for every claim (`two_reads`); from three reads on
       it fails (`three_reads`): (r₁ = r₂) ∨ (r₂ ≠ r₃), on the first three reads, holds at every same-value and every flipping pattern and
       fails at (T, F, F) — an owner who is neither, against whom the dirty reading still guards.
     * Self-reference, minimally — the revision theory of truth (Gupta and Belnap 1993) in miniature (the full
       theory revises the whole extension of the truth predicate through transfinite stages; here one sentence,
       finitely many steps): a
       sentence is a map from the value it is read to have to its value, read again by revising. The liar's
       revisions are exactly the flipping pattern (`liar_flips`), the truth-teller's exactly the same-value one
       (`truthteller_stable`); the liar has no stable value, the truth-teller two (`liar_no_fixed`). Reading the
       liar's revisions as a flipping owner is our link, not part of that theory.

  6. THE MODEL IS ZTL'S CAUTIOUS REGISTER (the curator: "Да, пробуй закрыть"). Reading a formula's occurrences left
     to right (`rval`), the values it takes over all lists of reads are exactly its dirty readings (`reads_exact`,
     against `ZDirty.rd`). Hence under pure doubt "true at every list of reads" is exactly the strong Kleene T
     (`model_is_kleene`) — the whole-formula adversary of `ZGames` — and implies the decisive table's T
     (`model_implies_decisive`), not conversely: (p ∧ p) → p holds at every same-value and every flipping list of
     three reads, fails at (T, T, F), is not Kleene-T, and the decisive table grants it (`three_reads_in_ztl`):
     the table records p ∧ p as checked-false and then grants F → p.

READING, not proved: classical logic never has to choose between the two readings — its values are clean, and on
clean values they coincide. With an unchecked value they come apart; ZTL picks the cautious one and treats "the same
value both times" as an extra assumption, as it treats a choice used consistently.
-/
namespace ZOne
open V

/-! ### 1. One occurrence only mutates -/

/-- Atom occurrences. -/
def occ : Fm → Nat
  | .atom _   => 1
  | .top      => 0
  | .bot      => 0
  | .neg φ    => occ φ
  | .conj φ ψ => occ φ + occ ψ
  | .disj φ ψ => occ φ + occ ψ
  | .imp φ ψ  => occ φ + occ ψ
  | .xor φ ψ  => occ φ + occ ψ
  | .xnor φ ψ => occ φ + occ ψ

theorem occ_pos : ∀ φ : Fm, ZOrigin.Pure φ → 1 ≤ occ φ
  | .atom _, _ => Nat.le_refl 1
  | .top, hp => False.elim hp
  | .bot, hp => False.elim hp
  | .neg φ, hp => occ_pos φ hp
  | .conj φ _, hp => Nat.le_trans (occ_pos φ hp.1) (Nat.le_add_right _ _)
  | .disj φ _, hp => Nat.le_trans (occ_pos φ hp.1) (Nat.le_add_right _ _)
  | .imp φ _, hp => Nat.le_trans (occ_pos φ hp.1) (Nat.le_add_right _ _)
  | .xor φ _, hp => Nat.le_trans (occ_pos φ hp.1) (Nat.le_add_right _ _)
  | .xnor φ _, hp => Nat.le_trans (occ_pos φ hp.1) (Nat.le_add_right _ _)

/-- A binary step over pure parts reads at least two occurrences. -/
theorem bin_two (φ ψ : Fm) (h1 : ZOrigin.Pure φ) (h2 : ZOrigin.Pure ψ) : 2 ≤ occ φ + occ ψ :=
  Nat.add_le_add (occ_pos φ h1) (occ_pos ψ h2)

/-- k negations. -/
def negs : Nat → Fm → Fm
  | 0, φ => φ
  | k + 1, φ => .neg (negs k φ)

theorem single_is_chain : ∀ φ : Fm, ZOrigin.Pure φ → occ φ = 1 → ∃ n k, φ = negs k (.atom n)
  | .atom n, _, _ => ⟨n, 0, rfl⟩
  | .top, hp, _ => False.elim hp
  | .bot, hp, _ => False.elim hp
  | .neg φ, hp, h => by
      obtain ⟨n, k, e⟩ := single_is_chain φ hp h
      exact ⟨n, k + 1, by rw [e]; rfl⟩
  | .conj φ ψ, hp, h => by
      have h2 := bin_two φ ψ hp.1 hp.2
      have h' : occ φ + occ ψ = 1 := h
      rw [h'] at h2; exact absurd h2 (by decide)
  | .disj φ ψ, hp, h => by
      have h2 := bin_two φ ψ hp.1 hp.2
      have h' : occ φ + occ ψ = 1 := h
      rw [h'] at h2; exact absurd h2 (by decide)
  | .imp φ ψ, hp, h => by
      have h2 := bin_two φ ψ hp.1 hp.2
      have h' : occ φ + occ ψ = 1 := h
      rw [h'] at h2; exact absurd h2 (by decide)
  | .xor φ ψ, hp, h => by
      have h2 := bin_two φ ψ hp.1 hp.2
      have h' : occ φ + occ ψ = 1 := h
      rw [h'] at h2; exact absurd h2 (by decide)
  | .xnor φ ψ, hp, h => by
      have h2 := bin_two φ ψ hp.1 hp.2
      have h' : occ φ + occ ψ = 1 := h
      rw [h'] at h2; exact absurd h2 (by decide)

/-- The chain from one dirty occurrence: Z, then F, then T, then it alternates. -/
theorem chain_alternates (v : Nat → V) (n : Nat) (hz : v n = Z) :
    evalF v (negs 0 (.atom n)) = Z ∧ evalF v (negs 1 (.atom n)) = F ∧ evalF v (negs 2 (.atom n)) = T ∧
    ∀ k, evalF v (negs (k + 3) (.atom n)) = evalF v (negs (k + 1) (.atom n)) := by
  refine ⟨hz, ?_, ?_, ?_⟩
  · show znot (v n) = F; rw [hz]; decide
  · show znot (znot (v n)) = T; rw [hz]; decide
  · intro k
    show znot (znot (evalF v (negs (k + 1) (.atom n)))) = evalF v (negs (k + 1) (.atom n))
    cases hx : evalF v (negs (k + 1) (.atom n)) with
    | T => decide
    | F => decide
    | Z =>
        have hc := lift1_classical (fun a => !a) (evalF v (negs k (.atom n)))
        have hx' : lift1 (fun a => !a) (evalF v (negs k (.atom n))) = Z := hx
        rw [hx'] at hc
        cases hc with
        | inl h => exact absurd h (by decide)
        | inr h => exact absurd h (by decide)

/-! ### 2. One atom is enough -/

/-- Every atom replaced by atom 0. -/
def toOne : Fm → Fm
  | .atom _   => .atom 0
  | .top      => .top
  | .bot      => .bot
  | .neg φ    => .neg (toOne φ)
  | .conj φ ψ => .conj (toOne φ) (toOne ψ)
  | .disj φ ψ => .disj (toOne φ) (toOne ψ)
  | .imp φ ψ  => .imp (toOne φ) (toOne ψ)
  | .xor φ ψ  => .xor (toOne φ) (toOne ψ)
  | .xnor φ ψ => .xnor (toOne φ) (toOne ψ)

/-- Under pure doubt, any formula has the value of its one-atom version. -/
theorem all_from_one (v : Nat → V) (hz : ZOrigin.AllZ v) : ∀ φ : Fm, evalF v φ = evalF v (toOne φ)
  | .atom n => by show v n = v 0; rw [hz n, hz 0]
  | .top => rfl
  | .bot => rfl
  | .neg φ => by show znot (evalF v φ) = znot (evalF v (toOne φ)); rw [all_from_one v hz φ]
  | .conj φ ψ => by
      show zand (evalF v φ) (evalF v ψ) = zand (evalF v (toOne φ)) (evalF v (toOne ψ))
      rw [all_from_one v hz φ, all_from_one v hz ψ]
  | .disj φ ψ => by
      show zor (evalF v φ) (evalF v ψ) = zor (evalF v (toOne φ)) (evalF v (toOne ψ))
      rw [all_from_one v hz φ, all_from_one v hz ψ]
  | .imp φ ψ => by
      show zimp (evalF v φ) (evalF v ψ) = zimp (evalF v (toOne φ)) (evalF v (toOne ψ))
      rw [all_from_one v hz φ, all_from_one v hz ψ]
  | .xor φ ψ => by
      show zxor (evalF v φ) (evalF v ψ) = zxor (evalF v (toOne φ)) (evalF v (toOne ψ))
      rw [all_from_one v hz φ, all_from_one v hz ψ]
  | .xnor φ ψ => by
      show zxnor (evalF v φ) (evalF v ψ) = zxnor (evalF v (toOne φ)) (evalF v (toOne ψ))
      rw [all_from_one v hz φ, all_from_one v hz ψ]


theorem table_reads_two (v : Nat → V) (h0 : v 0 = Z) (h1 : v 1 = Z) :
    evalF v (.conj (.atom 0) (.atom 0)) = evalF v (.conj (.atom 0) (.atom 1)) ∧
    evalF v (.disj (.atom 0) (.atom 0)) = evalF v (.disj (.atom 0) (.atom 1)) ∧
    evalF v (.imp (.atom 0) (.atom 0)) = evalF v (.imp (.atom 0) (.atom 1)) ∧
    evalF v (.xor (.atom 0) (.atom 0)) = evalF v (.xor (.atom 0) (.atom 1)) ∧
    evalF v (.xnor (.atom 0) (.atom 0)) = evalF v (.xnor (.atom 0) (.atom 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show zand (v 0) (v 0) = zand (v 0) (v 1); rw [h0, h1]
  · show zor (v 0) (v 0) = zor (v 0) (v 1); rw [h0, h1]
  · show zimp (v 0) (v 0) = zimp (v 0) (v 1); rw [h0, h1]
  · show zxor (v 0) (v 0) = zxor (v 0) (v 1); rw [h0, h1]
  · show zxnor (v 0) (v 0) = zxnor (v 0) (v 1); rw [h0, h1]

/-! ### 3. One Z is a stipulation -/

/-- The stable reading of x ⋆ x: one classical value at both occurrences. -/
def liftS (f : Bool → Bool → Bool) (x : V) : V :=
  if (subs x).all (fun a => f a a) then T else F

/-- A binary Boolean function by its four cells: f T T, f T F, f F T, f F F. -/
def tbl (a b c d : Bool) : Bool → Bool → Bool :=
  fun x y => if x then (if y then a else b) else (if y then c else d)

/-- One Z and two Z differ exactly on functions true on the diagonal and not everywhere. -/
theorem one_vs_two : ∀ a b c d : Bool,
    (liftS (tbl a b c d) Z ≠ lift2 (tbl a b c d) Z Z) ↔ ((a && d) = true ∧ (b && c) = false) := by
  decide

/-- Of the five binary connectives, exactly → and ↔ split: the laws of identity. -/
theorem five_split :
    liftS (fun a b => !a || b) Z = T ∧ zimp Z Z = F ∧
    liftS (fun a b => a == b) Z = T ∧ zxnor Z Z = F ∧
    liftS (fun a b => a && b) Z = zand Z Z ∧ liftS (fun a b => a || b) Z = zor Z Z ∧
    liftS (fun a b => a != b) Z = zxor Z Z := by
  decide

/-- What the table (two Z) earns, the stable reading (one Z) earns too. -/
theorem two_earned_one_earned : ∀ a b c d : Bool, ∀ x : V,
    lift2 (tbl a b c d) x x = T → liftS (tbl a b c d) x = T := by
  decide

/-- On clean values the two readings coincide. -/
theorem clean_coincide : ∀ a b c d : Bool, ∀ x : V, x ≠ Z →
    liftS (tbl a b c d) x = lift2 (tbl a b c d) x x := by
  decide

/-- Beyond p ⋆ p: p ∨ ¬p at Z is F read independently, and true at each stable reading. -/
theorem beyond_pp : zor Z (znot Z) = F ∧ ∀ a : Bool, (a || !a) = true := by
  refine ⟨by decide, ?_⟩
  intro a; cases a <;> rfl

/-! ### 4. The value flips at the second read: a case of the dirty reading -/

/-- The flipping reading of x ⋆ x: at a dirty x the second read is the negation of the first (a clean value
cannot flip, and is read as it is). -/
def liftA (f : Bool → Bool → Bool) (x : V) : V :=
  match x with
  | Z => if [true, false].all (fun a => f a (!a)) then T else F
  | T => lift2 f T T
  | F => lift2 f F F

/-- What the dirty reading earns, the flipping reading earns too. -/
theorem dirty_earned_flip_earned : ∀ a b c d : Bool, ∀ x : V,
    lift2 (tbl a b c d) x x = T → liftA (tbl a b c d) x = T := by
  decide

/-- At Z, for p ⋆ p, the dirty reading earns exactly what both the same-value and the flipping reading earn:
two reads of a Boolean value are either equal or opposite, and the dirty reading allows both. -/
theorem dirty_is_both : ∀ a b c d : Bool,
    lift2 (tbl a b c d) Z Z = T ↔ (liftS (tbl a b c d) Z = T ∧ liftA (tbl a b c d) Z = T) := by
  decide

/-- The flipping reading (the liar's revisions, `liar_flips`) makes p ∨ p and p ⊕ p true and p ↔ p false; the dirty
reading earns none of the three. -/
theorem flip_table :
    liftA (fun a b => a || b) Z = T ∧ liftA (fun a b => a != b) Z = T ∧
    liftA (fun a b => a == b) Z = F ∧ liftA (fun a b => a && b) Z = F ∧
    liftA (fun a b => !a || b) Z = F ∧
    zor Z Z = F ∧ zxor Z Z = F ∧ zxnor Z Z = F := by
  decide

/-! ### 5. Closing the boundaries of section 4 -/

/-- Only Z can flip: a value with both a reading and its negation is Z. (Given `subs`, the clause "clean values
do not flip" in `liftA` follows.) -/
theorem flip_needs_dirty : ∀ (x : V) (a : Bool),
    (subs x).contains a = true → (subs x).contains (!a) = true → x = Z := by
  decide

/-- n reads, all the same. -/
def rep : Nat → Bool → List Bool
  | 0, _ => []
  | n + 1, a => a :: rep n a

/-- n reads, each the negation of the one before. -/
def alt : Nat → Bool → List Bool
  | 0, _ => []
  | n + 1, a => a :: alt n (!a)

theorem rep_length : ∀ (n : Nat) (a : Bool), (rep n a).length = n
  | 0, _ => rfl
  | n + 1, a => by show (rep n a).length + 1 = n + 1; rw [rep_length n a]

/-- A claim about n reads of one value, as a test on the reads. Earned by the dirty reading: true at every
pattern of reads. -/
def DirtyN (n : Nat) (f : List Bool → Bool) : Prop := ∀ s : List Bool, s.length = n → f s = true
def StableN (n : Nat) (f : List Bool → Bool) : Prop := ∀ a, f (rep n a) = true
def FlipN (n : Nat) (f : List Bool → Bool) : Prop := ∀ a, f (alt n a) = true

theorem alt_length : ∀ (n : Nat) (a : Bool), (alt n a).length = n
  | 0, _ => rfl
  | n + 1, a => by show (alt n (!a)).length + 1 = n + 1; rw [alt_length n (!a)]

theorem dirtyN_both (n : Nat) (f : List Bool → Bool) (h : DirtyN n f) : StableN n f ∧ FlipN n f :=
  ⟨fun a => h (rep n a) (rep_length n a), fun a => h (alt n a) (alt_length n a)⟩

/-- With two reads, "the same" and "the opposite" are all there is: the two readings together are the dirty one,
for every claim about the two reads. -/
theorem two_reads (f : List Bool → Bool) : DirtyN 2 f ↔ StableN 2 f ∧ FlipN 2 f := by
  refine ⟨dirtyN_both 2 f, fun ⟨hs, hf⟩ s hl => ?_⟩
  cases s with
  | nil => exact absurd hl (by decide)
  | cons x t =>
    cases t with
    | nil => exact Nat.noConfusion (Nat.succ.inj hl)
    | cons y t =>
      cases t with
      | nil =>
        cases x <;> cases y
        · exact hs false
        · exact hf false
        · exact hf true
        · exact hs true
      | cons z t => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj hl))

/-- From three reads on, they are not: some claim holds at every same-value and every flipping pattern and fails
at another — an owner who is neither. -/
def three (s : List Bool) : Bool :=
  match s with
  | [] => true
  | [_] => true
  | [_, _] => true
  | x :: y :: z :: _ => (x == y) || (y != z)

theorem three_reads (m : Nat) :
    StableN (m + 3) three ∧ FlipN (m + 3) three ∧ ¬ DirtyN (m + 3) three := by
  refine ⟨fun a => ?_, fun a => ?_, fun h => ?_⟩
  · show ((a == a) || (a != a)) = true
    cases a <;> rfl
  · show ((a == !a) || ((!a) != (!!a))) = true
    cases a <;> rfl
  · have hl : (true :: false :: false :: rep m false).length = m + 3 := by
      show (rep m false).length + 1 + 1 + 1 = m + 3
      rw [rep_length m false]
    have h2 : ((true == false) || (false != false)) = true := h _ hl
    exact Bool.noConfusion h2

/-! Self-reference, minimally (revision theory of truth: Gupta and Belnap, *The Revision Theory of Truth*, 1993).
A sentence that speaks of its own value is a map `L : Bool → Bool` (its value, given the value it is read to have);
reading it again means revising: r₀ = a, r₍ₖ₊₁₎ = L rₖ. -/

/-- n revisions of a self-referential sentence from the start value a. -/
def revise (L : Bool → Bool) : Nat → Bool → List Bool
  | 0, _ => []
  | n + 1, a => a :: revise L n (L a)

/-- The liar ("I am false", L = not): its revisions are exactly the flipping pattern, from either start. -/
theorem liar_flips : ∀ (n : Nat) (a : Bool), revise (fun v => !v) n a = alt n a
  | 0, _ => rfl
  | n + 1, a => by show a :: revise (fun v => !v) n (!a) = a :: alt n (!a); rw [liar_flips n (!a)]

/-- The truth-teller ("I am true", L = id): its revisions are exactly the same-value pattern. -/
theorem truthteller_stable : ∀ (n : Nat) (a : Bool), revise (fun v => v) n a = rep n a
  | 0, _ => rfl
  | n + 1, a => by show a :: revise (fun v => v) n a = a :: rep n a; rw [truthteller_stable n a]

/-- The liar has no stable value; the truth-teller has two, and nothing picks between them. -/
theorem liar_no_fixed : (∀ a : Bool, (!a) ≠ a) ∧ (∀ a : Bool, (fun v : Bool => v) a = a) := by
  refine ⟨fun a => ?_, fun _ => rfl⟩
  cases a <;> decide

/-! ### 6. The model of reads is ZTL's cautious register

Section 5 counts reads in a model: a list of T/F, a claim as a test on it. Here the model is tied to ZTL's own
evaluation. A formula's occurrences are read left to right (`rval`: the first `occ φ` reads go to φ, the rest to
ψ). Under pure doubt, "true at every list of reads" is exactly the strong Kleene value T (`model_is_kleene`) — the
cautious register, ZTL's whole-formula adversary (`ZGames.formula_scope_is_kleene`) — and it implies the decisive
table's T (`model_implies_decisive`), not conversely: (p ∧ p) → p holds at every same-value and every flipping list
of three reads, fails at (T, T, F), and the decisive table grants it (`three_reads_in_ztl`). -/

def tk : Nat → List Bool → List Bool
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, a :: l => a :: tk n l

def dp : Nat → List Bool → List Bool
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, _ :: l => dp n l

theorem len_app : ∀ s t : List Bool, (s ++ t).length = s.length + t.length
  | [], t => (Nat.zero_add t.length).symm
  | a :: s, t => by
      show (s ++ t).length + 1 = (s.length + 1) + t.length
      rw [len_app s t, Nat.add_right_comm]

theorem tk_app : ∀ s t : List Bool, tk s.length (s ++ t) = s
  | [], _ => rfl
  | a :: s, t => by show a :: tk s.length (s ++ t) = a :: s; rw [tk_app s t]

theorem dp_app : ∀ s t : List Bool, dp s.length (s ++ t) = t
  | [], _ => rfl
  | _ :: s, t => dp_app s t

theorem tk_len : ∀ (a b : Nat) (s : List Bool), s.length = a + b → (tk a s).length = a
  | 0, _, _, _ => rfl
  | a + 1, b, [], h => by
      have h' : 0 = (a + b) + 1 := by rw [Nat.add_right_comm] at h; exact h
      exact Nat.noConfusion h'
  | a + 1, b, x :: l, h => by
      have h' : l.length + 1 = (a + b) + 1 := by rw [Nat.add_right_comm] at h; exact h
      show (tk a l).length + 1 = a + 1
      rw [tk_len a b l (Nat.succ.inj h')]

theorem dp_len : ∀ (a b : Nat) (s : List Bool), s.length = a + b → (dp a s).length = b
  | 0, b, s, h => by show s.length = b; rw [h, Nat.zero_add]
  | a + 1, b, [], h => by
      have h' : 0 = (a + b) + 1 := by rw [Nat.add_right_comm] at h; exact h
      exact Nat.noConfusion h'
  | a + 1, b, x :: l, h => by
      have h' : l.length + 1 = (a + b) + 1 := by rw [Nat.add_right_comm] at h; exact h
      exact dp_len a b l (Nat.succ.inj h')

/-- The classical value of φ when its occurrences are read, left to right, as the list s. -/
def rval : Fm → List Bool → Bool
  | .atom _, [] => false
  | .atom _, r :: _ => r
  | .top, _ => true
  | .bot, _ => false
  | .neg φ, s => !rval φ s
  | .conj φ ψ, s => rval φ (tk (occ φ) s) && rval ψ (dp (occ φ) s)
  | .disj φ ψ, s => rval φ (tk (occ φ) s) || rval ψ (dp (occ φ) s)
  | .imp φ ψ, s => !rval φ (tk (occ φ) s) || rval ψ (dp (occ φ) s)
  | .xor φ ψ, s => rval φ (tk (occ φ) s) != rval ψ (dp (occ φ) s)
  | .xnor φ ψ, s => rval φ (tk (occ φ) s) == rval ψ (dp (occ φ) s)

theorem any2 (h : Bool → Bool) : ([true, false].any h = true) ↔ ∃ a, h a = true := by
  constructor
  · intro e
    cases ht : h true
    · cases hf : h false
      · have e' : (h true || (h false || false)) = true := e
        rw [ht, hf] at e'; exact Bool.noConfusion e'
      · exact ⟨false, hf⟩
    · exact ⟨true, ht⟩
  · intro ⟨a, ha⟩
    show (h true || (h false || false)) = true
    cases a
    · rw [ha]; cases h true <;> rfl
    · rw [ha]; rfl

theorem and3 (x y z : Bool) : (x && y && z) = true ↔ (x = true ∧ y = true ∧ z = true) := by
  cases x <;> cases y <;> cases z <;> exact ⟨fun h => by first | exact Bool.noConfusion h | exact ⟨rfl, rfl, rfl⟩,
    fun ⟨a, b, c⟩ => by first | exact Bool.noConfusion a | exact Bool.noConfusion b | exact Bool.noConfusion c | rfl⟩

theorem not_eq (x : Bool) : ((!x) = true) ↔ (x = false) := by
  cases x <;> exact ⟨fun h => by first | rfl | exact Bool.noConfusion h, fun h => by first | rfl | exact Bool.noConfusion h⟩

/-- The binary step: the readings of φ ⋆ ψ are exactly the pairs of readings of φ and ψ, split by position. -/
theorem bin_reads (g : Bool → Bool → Bool) (φ ψ : Fm) (p q : Bool × Bool)
    (ihφ : ∀ b, ok b p = true ↔ ∃ s : List Bool, s.length = occ φ ∧ rval φ s = b)
    (ihψ : ∀ b, ok b q = true ↔ ∃ s : List Bool, s.length = occ ψ ∧ rval ψ s = b) (b : Bool) :
    (∃ a c, ok a p = true ∧ ok c q = true ∧ g a c = b) ↔
    ∃ s : List Bool, s.length = occ φ + occ ψ ∧ g (rval φ (tk (occ φ) s)) (rval ψ (dp (occ φ) s)) = b := by
  constructor
  · intro ⟨a, c, ha, hc, hg⟩
    obtain ⟨s1, l1, v1⟩ := (ihφ a).1 ha
    obtain ⟨s2, l2, v2⟩ := (ihψ c).1 hc
    refine ⟨s1 ++ s2, by rw [len_app, l1, l2], ?_⟩
    rw [← l1, tk_app, dp_app, v1, v2]; exact hg
  · intro ⟨s, l, hg⟩
    exact ⟨_, _, (ihφ _).2 ⟨_, tk_len _ _ s l, rfl⟩, (ihψ _).2 ⟨_, dp_len _ _ s l, rfl⟩, hg⟩

theorem comb_true (g : Bool → Bool → Bool) (p q : Bool × Bool) :
    ok true (comb g p q) = true ↔ ∃ a c, ok a p = true ∧ ok c q = true ∧ g a c = true := by
  show ([true, false].any (fun a => [true, false].any (fun c => ok a p && ok c q && g a c))) = true ↔ _
  constructor
  · intro h
    obtain ⟨a, h⟩ := (any2 _).1 h; obtain ⟨c, h⟩ := (any2 _).1 h; obtain ⟨x, y, z⟩ := (and3 _ _ _).1 h
    exact ⟨a, c, x, y, z⟩
  · intro ⟨a, c, x, y, z⟩; exact (any2 _).2 ⟨a, (any2 _).2 ⟨c, (and3 _ _ _).2 ⟨x, y, z⟩⟩⟩

theorem comb_false (g : Bool → Bool → Bool) (p q : Bool × Bool) :
    ok false (comb g p q) = true ↔ ∃ a c, ok a p = true ∧ ok c q = true ∧ g a c = false := by
  show ([true, false].any (fun a => [true, false].any (fun c => ok a p && ok c q && !(g a c)))) = true ↔ _
  constructor
  · intro h
    obtain ⟨a, h⟩ := (any2 _).1 h; obtain ⟨c, h⟩ := (any2 _).1 h; obtain ⟨x, y, z⟩ := (and3 _ _ _).1 h
    exact ⟨a, c, x, y, (not_eq _).1 z⟩
  · intro ⟨a, c, x, y, z⟩; exact (any2 _).2 ⟨a, (any2 _).2 ⟨c, (and3 _ _ _).2 ⟨x, y, (not_eq _).2 z⟩⟩⟩

theorem comb_ok (g : Bool → Bool → Bool) (p q : Bool × Bool) (b : Bool) :
    ok b (comb g p q) = true ↔ ∃ a c, ok a p = true ∧ ok c q = true ∧ g a c = b := by
  cases b
  · exact comb_false g p q
  · exact comb_true g p q

/-- Under pure doubt, the readings of φ (`rd`, the dirty reading of ZDirty) are exactly the values `rval φ` takes
over all lists of `occ φ` reads. -/
theorem reads_exact (v : Nat → V) (hz : ZOrigin.AllZ v) :
    ∀ (φ : Fm) (b : Bool), ok b (rd v φ) = true ↔ ∃ s : List Bool, s.length = occ φ ∧ rval φ s = b
  | .atom n, b => by
      have e : rd v (.atom n) = (true, true) := by
        show ((subs (v n)).contains true, (subs (v n)).contains false) = (true, true); rw [hz n]; rfl
      rw [e]
      exact ⟨fun _ => ⟨[b], rfl, rfl⟩, fun _ => by cases b <;> rfl⟩
  | .top, b => by
      cases b
      · exact ⟨fun h => Bool.noConfusion h, fun ⟨_, _, h⟩ => Bool.noConfusion h⟩
      · exact ⟨fun _ => ⟨[], rfl, rfl⟩, fun _ => rfl⟩
  | .bot, b => by
      cases b
      · exact ⟨fun _ => ⟨[], rfl, rfl⟩, fun _ => rfl⟩
      · exact ⟨fun h => Bool.noConfusion h, fun ⟨_, _, h⟩ => Bool.noConfusion h⟩
  | .neg φ, b => by
      have ih := reads_exact v hz φ (!b)
      have sw : ok b (rd v (.neg φ)) = ok (!b) (rd v φ) := by
        show ok b ((rd v φ).2, (rd v φ).1) = ok (!b) (rd v φ); cases b <;> rfl
      rw [sw]
      refine ih.trans ⟨?_, ?_⟩
      · intro ⟨s, l, h⟩; exact ⟨s, l, by show (!rval φ s) = b; rw [h]; cases b <;> rfl⟩
      · intro ⟨s, l, h⟩
        have h' : (!rval φ s) = b := h
        exact ⟨s, l, by rw [← h']; cases rval φ s <;> rfl⟩
  | .conj φ ψ, b => by
      show ok b (comb _ (rd v φ) (rd v ψ)) = true ↔ _
      exact (comb_ok _ _ _ b).trans (bin_reads _ φ ψ _ _ (reads_exact v hz φ) (reads_exact v hz ψ) b)
  | .disj φ ψ, b => by
      show ok b (comb _ (rd v φ) (rd v ψ)) = true ↔ _
      exact (comb_ok _ _ _ b).trans (bin_reads _ φ ψ _ _ (reads_exact v hz φ) (reads_exact v hz ψ) b)
  | .imp φ ψ, b => by
      show ok b (comb _ (rd v φ) (rd v ψ)) = true ↔ _
      exact (comb_ok _ _ _ b).trans (bin_reads (fun a c => !a || c) φ ψ _ _ (reads_exact v hz φ) (reads_exact v hz ψ) b)
  | .xor φ ψ, b => by
      show ok b (comb _ (rd v φ) (rd v ψ)) = true ↔ _
      exact (comb_ok _ _ _ b).trans (bin_reads _ φ ψ _ _ (reads_exact v hz φ) (reads_exact v hz ψ) b)
  | .xnor φ ψ, b => by
      show ok b (comb _ (rd v φ) (rd v ψ)) = true ↔ _
      exact (comb_ok _ _ _ b).trans (bin_reads _ φ ψ _ _ (reads_exact v hz φ) (reads_exact v hz ψ) b)

theorem enc_T : ∀ x : V, enc x = (true, false) → x = T := by decide

/-- **The model of reads is the cautious register.** Under pure doubt, φ is true at every list of reads exactly
when its strong Kleene value is T. -/
theorem model_is_kleene (v : Nat → V) (hz : ZOrigin.AllZ v) (φ : Fm) :
    kev v φ = T ↔ DirtyN (occ φ) (rval φ) := by
  have hr := reads_exact v hz φ
  have k := rd_is_kleene v φ
  constructor
  · intro h s l
    cases e : rval φ s
    · have w := (hr false).2 ⟨s, l, e⟩
      rw [k, h] at w; exact Bool.noConfusion w
    · rfl
  · intro hd
    apply enc_T
    rw [← k]
    have h1 : ok true (rd v φ) = true := (hr true).2 ⟨rep (occ φ) true, rep_length _ _, hd _ (rep_length _ _)⟩
    have h2 : ok false (rd v φ) = false := by
      cases e : ok false (rd v φ)
      · rfl
      · obtain ⟨s, l, hs⟩ := (hr false).1 e
        rw [hd s l] at hs; exact Bool.noConfusion hs
    revert h1 h2; cases rd v φ with
    | mk t f => intro h1 h2; have h1' : t = true := h1; have h2' : f = false := h2; rw [h1', h2']

/-- True at every list of reads ⇒ the decisive table grants T. -/
theorem model_implies_decisive (v : Nat → V) (hz : ZOrigin.AllZ v) (φ : Fm) (h : DirtyN (occ φ) (rval φ)) :
    evalF v φ = T := by
  apply never_stricter
  cases e : (rd v φ).2
  · rfl
  · have e' : ok false (rd v φ) = true := e
    obtain ⟨s, l, hs⟩ := (reads_exact v hz φ false).1 e'
    rw [h s l] at hs; exact Bool.noConfusion hs

/-- (p ∧ p) → p: three reads; true at every same-value and every flipping list, false at (T, T, F); its strong
Kleene value is not T; the decisive table grants it. -/
def p3 : Fm := .imp (.conj (.atom 0) (.atom 0)) (.atom 0)

theorem three_reads_in_ztl :
    occ p3 = 3 ∧ StableN 3 (rval p3) ∧ FlipN 3 (rval p3) ∧ rval p3 [true, true, false] = false ∧
    kev (fun _ => Z) p3 ≠ T ∧ evalF (fun _ => Z) p3 = T := by
  refine ⟨rfl, fun a => ?_, fun a => ?_, rfl, by decide, by decide⟩
  · cases a <;> rfl
  · cases a <;> rfl

end ZOne

#print axioms ZOne.occ_pos
#print axioms ZOne.bin_two
#print axioms ZOne.single_is_chain
#print axioms ZOne.chain_alternates
#print axioms ZOne.all_from_one
#print axioms ZOne.table_reads_two
#print axioms ZOne.one_vs_two
#print axioms ZOne.five_split
#print axioms ZOne.two_earned_one_earned
#print axioms ZOne.clean_coincide
#print axioms ZOne.beyond_pp
#print axioms ZOne.dirty_earned_flip_earned
#print axioms ZOne.dirty_is_both
#print axioms ZOne.flip_table
#print axioms ZOne.flip_needs_dirty
#print axioms ZOne.rep_length
#print axioms ZOne.alt_length
#print axioms ZOne.dirtyN_both
#print axioms ZOne.two_reads
#print axioms ZOne.three_reads
#print axioms ZOne.liar_flips
#print axioms ZOne.truthteller_stable
#print axioms ZOne.liar_no_fixed
#print axioms ZOne.len_app
#print axioms ZOne.tk_app
#print axioms ZOne.dp_app
#print axioms ZOne.tk_len
#print axioms ZOne.dp_len
#print axioms ZOne.any2
#print axioms ZOne.and3
#print axioms ZOne.not_eq
#print axioms ZOne.bin_reads
#print axioms ZOne.comb_true
#print axioms ZOne.comb_false
#print axioms ZOne.comb_ok
#print axioms ZOne.reads_exact
#print axioms ZOne.enc_T
#print axioms ZOne.model_is_kleene
#print axioms ZOne.model_implies_decisive
#print axioms ZOne.three_reads_in_ztl
