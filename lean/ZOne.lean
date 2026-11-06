import ZTL
import ZOrigin
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
     * Only Z can flip (`flip_needs_dirty`): the clause "clean values do not flip" is forced, not chosen.
     * n reads (`DirtyN`, `StableN`, `FlipN` over lists of reads): the dirty reading earns only what both earn, for
       every n (`dirtyN_both`); with two reads the converse holds for every claim (`two_reads`); from three reads on
       it fails (`three_reads`): (r₁ = r₂) ∨ (r₂ ≠ r₃) holds at every same-value and every flipping pattern and
       fails at (T, F, F) — an owner who is neither, against whom the dirty reading still guards.
     * Self-reference, minimally — the revision theory of truth (Gupta and Belnap 1993) is the predecessor: a
       sentence is a map from the value it is read to have to its value, read again by revising. The liar's
       revisions are exactly the flipping pattern (`liar_flips`), the truth-teller's exactly the same-value one
       (`truthteller_stable`); the liar has no stable value, the truth-teller two (`liar_no_fixed`).

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

/-- Only Z can flip: a value with both a reading and its negation is Z. (The clause "clean values do not flip"
in `liftA` is forced, not chosen.) -/
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
