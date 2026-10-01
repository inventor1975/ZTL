import ZTopology

/-!
# ZMajority — what a coalition needs to capture a tree of triples

The no-centre layer of the agent-accountability kit decides a fact by a tree of
triples: `3^d` seats, grouped in threes, each triple decided 2-of-3, and the
results grouped in threes again, up to one verdict. Leaves carry ZTL values:
`T` an honest statement, `F` a lie, `Z` an empty seat (nobody spoke). A triple
says `T` or `F` only on two equal voices, else `Z` — the table the kit computes
with the ZTL judge.

Proved here, on the empty axiom list:

1. `triple_T_iff_earned`, `triple_F_iff_refuted` — the triple table is the ZTL
   judge's disposition of the majority formula `(a∧b)∨(a∧c)∨(b∧c)` over the three
   voices: the triple says `T` exactly when the formula is EARNED, `F` exactly when
   it is REFUTED (`ZTopology`'s definitions, which match ztljudge on 5 400 of 5 400
   markings — measured there, not proved), `Z` otherwise. NOT its value: ZTL connectives are
   two-valued, and the formula's value is `F` on every undecided triple (measured:
   13 of 27 cells differ) — the kit reads the disposition, and so does this file.
2. `lie_needs` — a tree of depth `d` says `F` only if at least `2^d` of its
   leaves are `F`. Empty seats never help a lie: `Z` leaves are not counted.
   The mirror `truth_needs` holds for `T`.
3. `lie_suffices` — and `2^d` lies are enough: there is a tree with exactly
   `2^d` lies, every other leaf honest, that says `F`.
4. `depth4` — at depth 4 that is 16 seats of 81: a coalition of about 20%,
   placed right, captures the verdict over 65 honest seats.

What this says about the kit, stated plainly: the tree on its own is WEAKER
than a flat majority against an adversary who chooses the seats. Its protection
against collusion comes from elsewhere — seats drawn by public randomness and
re-drawn for every fact, so a coalition cannot choose where it sits, and the
contested-triple alarm. Those are probabilistic and measured by simulation in
the kit; they are not proved here.
-/

namespace ZMajority

open V

/-! ## The triple -/

/-- Two equal voices decide a triple; otherwise it is undecided. Written out in
full: an overlapping wildcard row pulls `propext` in through the compiled matcher
(measured here, as in `ZTL.lean`). -/
def maj3 : V → V → V → V
  | T, T, T => T | T, T, F => T | T, T, Z => T
  | T, F, T => T | T, F, F => F | T, F, Z => Z
  | T, Z, T => T | T, Z, F => Z | T, Z, Z => Z
  | F, T, T => T | F, T, F => F | F, T, Z => Z
  | F, F, T => F | F, F, F => F | F, F, Z => F
  | F, Z, T => Z | F, Z, F => F | F, Z, Z => Z
  | Z, T, T => T | Z, T, F => Z | Z, T, Z => Z
  | Z, F, T => Z | Z, F, F => F | Z, F, Z => Z
  | Z, Z, T => Z | Z, Z, F => Z | Z, Z, Z => Z

/-- A triple says `F` only if two of its three voices are `F`. -/
theorem maj3_F : ∀ a b c : V, maj3 a b c = F →
    (a = F ∧ b = F) ∨ (a = F ∧ c = F) ∨ (b = F ∧ c = F) := by
  intro a b c h
  cases a <;> cases b <;> cases c <;>
    first
    | (cases h; done)
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- A triple says `T` only if two of its three voices are `T`. -/
theorem maj3_T : ∀ a b c : V, maj3 a b c = T →
    (a = T ∧ b = T) ∨ (a = T ∧ c = T) ∨ (b = T ∧ c = T) := by
  intro a b c h
  cases a <;> cases b <;> cases c <;>
    first
    | (cases h; done)
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    | exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-! ## The triple is the judge's disposition of the majority formula -/

open ZTopology

/-- `(a0 ∧ a1) ∨ (a0 ∧ a2) ∨ (a1 ∧ a2)` — the formula the kit hands to the judge. -/
def majF : Fm :=
  .disj (.disj (.conj (.atom 0) (.atom 1)) (.conj (.atom 0) (.atom 2)))
        (.conj (.atom 1) (.atom 2))

/-- The marking of three voices: atom 0, 1, 2. -/
def mark (a b c : V) : Nat → V
  | 0 => a
  | 1 => b
  | _ => c

/-- The triple table is strong Kleene on the majority formula. -/
theorem maj3_kleene : ∀ a b c : V, kevalF (mark a b c) majF = maj3 a b c := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-- Every unknown made false / made true: a refinement. -/
def toF : V → V
  | T => T | F => F | Z => F
def toT : V → V
  | T => T | F => F | Z => T

theorem le_toF : ∀ x : V, leqb x (toF x) = true := by decide
theorem le_toT : ∀ x : V, leqb x (toT x) = true := by decide

theorem triple_T_iff_earned (a b c : V) : maj3 a b c = T ↔ earned majF (mark a b c) := by
  constructor
  · intro h
    exact kleene_sub_earned ((maj3_kleene a b c).trans h)
  · intro h
    have hw := h (fun n => toF (mark a b c n)) (fun n => le_toF (mark a b c n))
    revert hw
    cases a <;> cases b <;> cases c <;> intro hw <;> first | rfl | (cases hw; done)

theorem triple_F_iff_refuted (a b c : V) : maj3 a b c = F ↔ refuted majF (mark a b c) := by
  constructor
  · intro h
    exact kleene_sub_refuted ((maj3_kleene a b c).trans h)
  · intro h
    have hw := h (fun n => toT (mark a b c n)) (fun n => le_toT (mark a b c n))
    revert hw
    cases a <;> cases b <;> cases c <;> intro hw <;> first | rfl | (cases hw; done)

/-! ## The tree -/

/-- A full tree of triples of depth `d`: `3^d` seats. -/
inductive Tree : Nat → Type where
  | leaf : V → Tree 0
  | node {d : Nat} : Tree d → Tree d → Tree d → Tree (d + 1)

/-- The verdict: every triple decided 2-of-3, bottom up. -/
def Tree.fold : {d : Nat} → Tree d → V
  | _, .leaf v => v
  | _, .node a b c => maj3 a.fold b.fold c.fold

/-- Indicator of a lie, and of an honest voice (no `BEq`: kept off the axiom list). -/
def isF : V → Nat
  | T => 0 | F => 1 | Z => 0

def isT : V → Nat
  | T => 1 | F => 0 | Z => 0

/-- Leaves that lie. -/
def Tree.lies : {d : Nat} → Tree d → Nat
  | _, .leaf v => isF v
  | _, .node a b c => a.lies + b.lies + c.lies

/-- Leaves that are honest. -/
def Tree.honest : {d : Nat} → Tree d → Nat
  | _, .leaf v => isT v
  | _, .node a b c => a.honest + b.honest + c.honest

/-- All seats. -/
def Tree.seats : {d : Nat} → Tree d → Nat
  | _, .leaf _ => 1
  | _, .node a b c => a.seats + b.seats + c.seats

/-- `2^d` and `3^d`, by addition only. -/
def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => pow2 n + pow2 n

def pow3 : Nat → Nat
  | 0 => 1
  | n + 1 => pow3 n + pow3 n + pow3 n

theorem seats_eq : ∀ {d : Nat} (t : Tree d), t.seats = pow3 d
  | _, .leaf _ => rfl
  | _, .node a b c => by
      show a.seats + b.seats + c.seats = _
      rw [seats_eq a, seats_eq b, seats_eq c]; rfl

/-! ## A lie needs `2^d` seats -/

/-- Two summands each at least `p` make at least `p + p`, whichever two they are. -/
theorem two_of_three {x y z p : Nat}
    (h : (p ≤ x ∧ p ≤ y) ∨ (p ≤ x ∧ p ≤ z) ∨ (p ≤ y ∧ p ≤ z)) :
    p + p ≤ x + y + z := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hz⟩ | ⟨hy, hz⟩
  · exact Nat.le_trans (Nat.add_le_add hx hy) (Nat.le_add_right _ _)
  · have h1 : p + p ≤ x + z := Nat.add_le_add hx hz
    have h2 : x + z ≤ x + y + z :=
      Nat.add_le_add_right (Nat.le_add_right x y) z
    exact Nat.le_trans h1 h2
  · have h1 : p + p ≤ y + z := Nat.add_le_add hy hz
    have h2 : y + z ≤ x + y + z :=
      Nat.add_le_add_right (Nat.le_add_left y x) z
    exact Nat.le_trans h1 h2

/-- A tree of depth `d` says `F` only if at least `2^d` of its leaves lie. -/
theorem lie_needs : ∀ {d : Nat} (t : Tree d), t.fold = F → pow2 d ≤ t.lies
  | _, .leaf v, h => by
      show 1 ≤ isF v
      cases v with
      | T => cases h
      | F => exact Nat.le_refl 1
      | Z => cases h
  | _, .node a b c, h => by
      show pow2 _ + pow2 _ ≤ a.lies + b.lies + c.lies
      apply two_of_three
      rcases maj3_F a.fold b.fold c.fold h with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
      · exact Or.inl ⟨lie_needs a ha, lie_needs b hb⟩
      · exact Or.inr (Or.inl ⟨lie_needs a ha, lie_needs c hc⟩)
      · exact Or.inr (Or.inr ⟨lie_needs b hb, lie_needs c hc⟩)

/-- The same bound for the truth. -/
theorem truth_needs : ∀ {d : Nat} (t : Tree d), t.fold = T → pow2 d ≤ t.honest
  | _, .leaf v, h => by
      show 1 ≤ isT v
      cases v with
      | T => exact Nat.le_refl 1
      | F => cases h
      | Z => cases h
  | _, .node a b c, h => by
      show pow2 _ + pow2 _ ≤ a.honest + b.honest + c.honest
      apply two_of_three
      rcases maj3_T a.fold b.fold c.fold h with ⟨ha, hb⟩ | ⟨ha, hc⟩ | ⟨hb, hc⟩
      · exact Or.inl ⟨truth_needs a ha, truth_needs b hb⟩
      · exact Or.inr (Or.inl ⟨truth_needs a ha, truth_needs c hc⟩)
      · exact Or.inr (Or.inr ⟨truth_needs b hb, truth_needs c hc⟩)

/-- Fewer than `2^d` lies can never produce the lie. -/
theorem few_lies_safe {d : Nat} (t : Tree d) (h : t.lies < pow2 d) : t.fold ≠ F :=
  fun hf => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (lie_needs t hf))

/-! ## And `2^d` lies suffice -/

/-- Every seat honest. -/
def allT : (d : Nat) → Tree d
  | 0 => .leaf T
  | d + 1 => .node (allT d) (allT d) (allT d)

theorem allT_fold : ∀ d, (allT d).fold = T
  | 0 => rfl
  | d + 1 => by
      show maj3 (allT d).fold (allT d).fold (allT d).fold = T
      rw [allT_fold d]; rfl

theorem allT_lies : ∀ d, (allT d).lies = 0
  | 0 => rfl
  | d + 1 => by
      show (allT d).lies + (allT d).lies + (allT d).lies = 0
      rw [allT_lies d]

theorem allT_honest : ∀ d, (allT d).honest = pow3 d
  | 0 => rfl
  | d + 1 => by
      show (allT d).honest + (allT d).honest + (allT d).honest = _
      rw [allT_honest d]; rfl

/-- The capture: lies in two branches of every triple on one path, all else honest. -/
def capture : (d : Nat) → Tree d
  | 0 => .leaf F
  | d + 1 => .node (capture d) (capture d) (allT d)

theorem capture_fold : ∀ d, (capture d).fold = F
  | 0 => rfl
  | d + 1 => by
      show maj3 (capture d).fold (capture d).fold (allT d).fold = F
      rw [capture_fold d, allT_fold d]; rfl

theorem capture_lies : ∀ d, (capture d).lies = pow2 d
  | 0 => rfl
  | d + 1 => by
      show (capture d).lies + (capture d).lies + (allT d).lies = _
      rw [capture_lies d, allT_lies d]; rfl

/-- In the capture every seat that does not lie is honest: no empty seat is needed. -/
theorem capture_full : ∀ d, (capture d).lies + (capture d).honest = pow3 d
  | 0 => rfl
  | d + 1 => by
      show ((capture d).lies + (capture d).lies + (allT d).lies)
          + ((capture d).honest + (capture d).honest + (allT d).honest)
          = pow3 d + pow3 d + pow3 d
      rw [allT_lies d, allT_honest d, Nat.add_zero, ← Nat.add_assoc,
        Nat.add_add_add_comm, capture_full d]

/-- `2^d` lies suffice, and that is tight with `lie_needs`. -/
theorem lie_suffices (d : Nat) :
    ∃ t : Tree d, t.fold = F ∧ t.lies = pow2 d ∧ t.lies + t.honest = pow3 d :=
  ⟨capture d, capture_fold d, capture_lies d, capture_full d⟩

/-- At depth 4: 16 lies of 81 seats capture the verdict over 65 honest ones. -/
theorem depth4 : pow2 4 = 16 ∧ pow3 4 = 81 ∧ (capture 4).fold = F ∧
    (capture 4).lies = 16 ∧ (capture 4).honest = 65 :=
  ⟨rfl, rfl, capture_fold 4, capture_lies 4, rfl⟩

end ZMajority

#print axioms ZMajority.maj3_kleene
#print axioms ZMajority.triple_T_iff_earned
#print axioms ZMajority.triple_F_iff_refuted
#print axioms ZMajority.capture_full
#print axioms ZMajority.lie_needs
#print axioms ZMajority.truth_needs
#print axioms ZMajority.few_lies_safe
#print axioms ZMajority.lie_suffices
#print axioms ZMajority.depth4
