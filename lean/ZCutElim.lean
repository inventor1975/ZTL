/-
  ZCutElim.lean — E55: SYNTACTIC CUT ELIMINATION, AND THE BOUND AS A FUNCTION.

  §5 settled that cut is ADMISSIBLE: `ZSequent.cut_admissible`, proved through
  completeness (`closes_iff`) — a fact about the refutability RELATION. What it
  did not give is a PROCEDURE: take a derivation that uses cut, produce one
  that does not, and say how much larger it is. This file is that procedure,
  with its size bound as a computable function, and nothing in the procedure
  goes through a model: every step is an induction on derivations. The one
  place `SAT` appears is the bridge back to the engine (`sound`,
  `closes_of_der`), which is not part of the elimination.

  THE CALCULUS. A sequent is an environment `e` (a sign per atom: the cell it
  has been narrowed to) and a list of signed formulas. The rules are exactly
  those of `TableauCert.closes`, read as a table: `Ax` (an empty cell; a
  constant refused by its sign; a compound given a sign that admits neither
  verdict), `Der.atom` (an atom narrows its cell — the only rule that touches
  the environment), `RuleC` (the one-premise steps: `¬ ∧ ∨` in one polarity,
  the rewrites of `→ ⊕ ↔` into the basis) and `Rule2` (the two-premise steps:
  `F:∧` and `T:∨`). The engine works on the HEAD of its list; the calculus lets
  a rule act on ANY node (`Pick`), which is what makes exchange free and
  weakening size-preserving; `der_of_closes` says the engine is the special
  case that always picks the head.

  THE MEASURE IS SIZE, NOT HEIGHT. In a consuming calculus every branch is
  bounded by the size of its sequent, so height cannot blow up; what a cut buys
  is WIDTH — the number of closed branches — and that is what `Der k` indexes:
  a derivation with at most `k` leaves (`pad` makes the index an upper bound).

  THE RESULT. `cutP` / `cut_TN` / `cut_FP`: a derivation of `S, T:φ` with `k₁`
  leaves and one of `S, N:φ` with `k₂` leaves yield a derivation of `S` with at
  most `B0 true k₁ k₂ (basis φ)` leaves — where `B0` is the recursion of the
  procedure itself. An atom MULTIPLIES (`cut_env`: a cell split two ways, the
  two derivations merged leaf against leaf). `¬` flips the pair `T/N` into
  `F/P` and costs nothing. `∧` and `∨` cut the two subformulas in turn, the
  second cut fed by the result of the first — and on the side that BRANCHES
  the whole first result is fed in, which is where the product becomes a
  power: a chain of `d` disjunctions multiplies by `k₁` at every level
  (`bound_or_chain`: 2 · 2 → 32 at depth 4). That is the classical shape.
  MEASURED (`zcutelim.py`, the same procedure as a program, every tree it
  builds re-verified against the table): the bound holds on every cut instance
  of the E16 pool and of a deeper random pool, and the pool it cannot run is
  the pool where the bound says the output would not fit — the blow-up is met,
  not narrated.

  WHERE ZTL SHOWS. Not in the bound — the branching skeleton is the classical
  one, and Z changes only which ATOMIC sequents are axioms. It shows in the
  pair: the classical cut, `T` against `F`, is REFUSED on atoms
  (`tf_cut_fails_on_atoms`: `{N:p, P:p}` is open, with `p = Z`, while both
  `T:p` and `F:p` close it) and GRANTED on compounds (`tf_cut_compound`), because
  on a compound `F` and `N` are the same two bits (`der_swap`) — the
  greediness theorem seen from inside the calculus. The covering pairs `T/N`
  and `F/P` are the ones that cut everywhere.

  FORM. Own `Pick` / `Ins` / `Perm` / `Swap` on lists; own `appAssoc`, `appNil`,
  `addMul` (`List.append_assoc`, `List.append_nil`, `Nat.add_mul`,
  `Nat.mul_assoc` carry propext — measured 2026-09-06); signs and environments
  compared pointwise, so no funext; every `match` cell explicit; inductions by
  the `induction` tactic where a `cases` inside a pattern-matching proof would
  hide the structural decrease. Empty axiom list throughout.
-/
import TableauCert

namespace ZCut

open V

/-! ### Bool and Nat facts, each `decide`d or by own induction -/

theorem orT : ∀ a b : Bool, (a || b) = true → a = true ∨ b = true := by decide
theorem andT : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by decide
theorem andI : ∀ a b : Bool, a = true → b = true → (a && b) = true := by decide
theorem notT : ∀ a : Bool, ¬ a = true → a = false := by decide
theorem bandComm : ∀ a b : Bool, (a && b) = (b && a) := by decide
theorem bandAssoc : ∀ a b c : Bool, ((a && b) && c) = (a && (b && c)) := by decide

theorem le_dest : ∀ {a b : Nat}, a ≤ b → ∃ d, a + d = b
  | _, _, Nat.le.refl => ⟨0, rfl⟩
  | _, _, Nat.le.step h => by
      have ⟨d, hd⟩ := le_dest h
      exact ⟨d + 1, by rw [← hd]; rfl⟩

theorem addMul : ∀ a b c : Nat, (a + b) * c = a * c + b * c
  | _, _, 0 => rfl
  | a, b, c + 1 => by
      show (a + b) * c + (a + b) = (a * c + a) + (b * c + b)
      rw [addMul a b c, Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm (b * c) a b]

/-! ### Lists: own append lemmas -/

theorem appAssoc : ∀ (l₁ l₂ l₃ : List Node), (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃)
  | [], _, _ => rfl
  | x :: l₁, l₂, l₃ => by
      show x :: ((l₁ ++ l₂) ++ l₃) = x :: (l₁ ++ (l₂ ++ l₃))
      rw [appAssoc l₁ l₂ l₃]

theorem appNil : ∀ l : List Node, l ++ [] = l
  | [] => rfl
  | x :: l => by
      show x :: (l ++ []) = x :: l
      rw [appNil l]

/-! ### Pick a node, insert a node, permute -/

/-- `Pick S x S'`: `x` occurs in `S` and `S'` is `S` with that occurrence removed. -/
inductive Pick : List Node → Node → List Node → Prop
  | here  {x : Node} {l : List Node} : Pick (x :: l) x l
  | there {x y : Node} {l l' : List Node} : Pick l x l' → Pick (y :: l) x (y :: l')

/-- `Ins x S Sw`: `Sw` is `S` with `x` inserted somewhere. -/
inductive Ins : Node → List Node → List Node → Prop
  | here  {x : Node} {l : List Node} : Ins x l (x :: l)
  | there {x y : Node} {l l' : List Node} : Ins x l l' → Ins x (y :: l) (y :: l')

inductive Perm : List Node → List Node → Prop
  | nil : Perm [] []
  | cons {x : Node} {l l' : List Node} : Perm l l' → Perm (x :: l) (x :: l')
  | swap {x y : Node} {l : List Node} : Perm (y :: x :: l) (x :: y :: l)
  | trans {l₁ l₂ l₃ : List Node} : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

/-- Two picks from one list: the same occurrence, or each survives the other. -/
theorem pick_pick : ∀ {S : List Node} {x y : Node} {S₁ S₂ : List Node},
    Pick S x S₁ → Pick S y S₂ →
    (x = y ∧ S₁ = S₂) ∨ ∃ S₃, Pick S₁ y S₃ ∧ Pick S₂ x S₃
  | _, _, _, _, _, Pick.here, Pick.here => Or.inl ⟨rfl, rfl⟩
  | _, _, _, _, _, Pick.here, Pick.there q => Or.inr ⟨_, q, Pick.here⟩
  | _, _, _, _, _, Pick.there p, Pick.here => Or.inr ⟨_, Pick.here, p⟩
  | _, _, _, _, _, Pick.there p, Pick.there q => by
      cases pick_pick p q with
      | inl h => exact Or.inl ⟨h.1, by rw [h.2]⟩
      | inr h =>
          have ⟨S₃, h1, h2⟩ := h
          exact Or.inr ⟨_, Pick.there h1, Pick.there h2⟩

/-- A pick survives an insertion elsewhere. -/
theorem pick_ins : ∀ {S S' Sw : List Node} {x nd : Node},
    Pick S x S' → Ins nd S Sw → ∃ S'w, Pick Sw x S'w ∧ Ins nd S' S'w
  | _, _, _, _, _, p, Ins.here => ⟨_, Pick.there p, Ins.here⟩
  | _, _, _, _, _, Pick.here, Ins.there i => ⟨_, Pick.here, i⟩
  | _, _, _, _, _, Pick.there p, Ins.there i => by
      have ⟨S'w, p', i'⟩ := pick_ins p i
      exact ⟨_, Pick.there p', Ins.there i'⟩

theorem ins_append (nd : Node) : ∀ (ns : List Node) {S Sw : List Node},
    Ins nd S Sw → Ins nd (ns ++ S) (ns ++ Sw)
  | [], _, _, i => i
  | _ :: ns, _, _, i => Ins.there (ins_append nd ns i)

theorem pick_append : ∀ (ns : List Node) {S S' : List Node} {x : Node},
    Pick S x S' → Pick (ns ++ S) x (ns ++ S')
  | [], _, _, _, p => p
  | _ :: ns, _, _, _, p => Pick.there (pick_append ns p)

theorem perm_refl : ∀ l : List Node, Perm l l
  | [] => Perm.nil
  | _ :: l => Perm.cons (perm_refl l)

theorem perm_symm : ∀ {l l' : List Node}, Perm l l' → Perm l' l
  | _, _, Perm.nil => Perm.nil
  | _, _, Perm.cons p => Perm.cons (perm_symm p)
  | _, _, Perm.swap => Perm.swap
  | _, _, Perm.trans p q => Perm.trans (perm_symm q) (perm_symm p)

theorem perm_append_left : ∀ (l : List Node) {a b : List Node}, Perm a b → Perm (l ++ a) (l ++ b)
  | [], _, _, p => p
  | _ :: l, _, _, p => Perm.cons (perm_append_left l p)

theorem perm_append_right (r : List Node) : ∀ {a b : List Node}, Perm a b → Perm (a ++ r) (b ++ r)
  | _, _, Perm.nil => perm_refl r
  | _, _, Perm.cons p => Perm.cons (perm_append_right r p)
  | _, _, Perm.swap => Perm.swap
  | _, _, Perm.trans p q => Perm.trans (perm_append_right r p) (perm_append_right r q)

/-- A node in front moves to the middle. -/
theorem perm_middle (x : Node) : ∀ (l₁ l₂ : List Node), Perm (x :: (l₁ ++ l₂)) (l₁ ++ x :: l₂)
  | [], _ => perm_refl _
  | y :: l₁, l₂ => Perm.trans Perm.swap (Perm.cons (perm_middle x l₁ l₂))

theorem perm_append_comm : ∀ (a b : List Node), Perm (a ++ b) (b ++ a)
  | [], b => by rw [appNil b]; exact perm_refl b
  | x :: a, b => Perm.trans (Perm.cons (perm_append_comm a b)) (perm_middle x b a)

/-- A pick transports along a permutation. -/
theorem perm_pick : ∀ {S S' : List Node}, Perm S S' → ∀ {y : Node} {S_y : List Node},
    Pick S y S_y → ∃ S'_y, Pick S' y S'_y ∧ Perm S_y S'_y
  | _, _, Perm.nil, _, _, p => nomatch p
  | _, _, Perm.cons q, _, _, Pick.here => ⟨_, Pick.here, q⟩
  | _, _, Perm.cons q, _, _, Pick.there p => by
      have ⟨S'_y, p', q'⟩ := perm_pick q p
      exact ⟨_, Pick.there p', Perm.cons q'⟩
  | _, _, Perm.swap, _, _, Pick.here => ⟨_, Pick.there Pick.here, perm_refl _⟩
  | _, _, Perm.swap, _, _, Pick.there Pick.here => ⟨_, Pick.here, perm_refl _⟩
  | _, _, Perm.swap, _, _, Pick.there (Pick.there p) =>
      ⟨_, Pick.there (Pick.there p), Perm.swap⟩
  | _, _, Perm.trans q₁ q₂, _, _, p => by
      have ⟨S₁, p₁, r₁⟩ := perm_pick q₁ p
      have ⟨S₂, p₂, r₂⟩ := perm_pick q₂ p₁
      exact ⟨S₂, p₂, Perm.trans r₁ r₂⟩

/-! ### Signs and environments, pointwise -/

/-- Two environments equal cell by cell, point by point. -/
def EnvEq (e e' : Env) : Prop := ∀ n x, e n x = e' n x

/-- `e'` refines `e`: every cell of `e'` sits inside the cell of `e`. -/
def Sub (e' e : Env) : Prop := ∀ n x, e' n x = true → e n x = true

theorem envEq_refl (e : Env) : EnvEq e e := fun _ _ => rfl
theorem envEq_symm {e e' : Env} (h : EnvEq e e') : EnvEq e' e := fun n x => (h n x).symm
theorem envEq_trans {e e' e'' : Env} (h : EnvEq e e') (h' : EnvEq e' e'') : EnvEq e e'' :=
  fun n x => (h n x).trans (h' n x)
theorem sub_refl (e : Env) : Sub e e := fun _ _ h => h
theorem sub_of_envEq {e e' : Env} (h : EnvEq e' e) : Sub e' e := fun n x hx => (h n x) ▸ hx

theorem sIsEmpty_congr {s s' : Sign} (h : ∀ x, s x = s' x) : sIsEmpty s = sIsEmpty s' := by
  show (!(s T || s F || s Z)) = (!(s' T || s' F || s' Z))
  rw [h T, h F, h Z]

theorem notOr3 : ∀ a b c : Bool, (!(a || b || c)) = true → a = false ∧ b = false ∧ c = false := by
  decide
theorem notOr3F : ∀ a b c : Bool, (!(a || b || c)) = false → a = true ∨ b = true ∨ c = true := by
  decide

/-- An empty sign holds nothing. -/
theorem empty_none {s : Sign} (h : sIsEmpty s = true) : ∀ x, s x = false := by
  have ⟨hT, hF, hZ⟩ := notOr3 _ _ _ h
  intro x
  cases x with
  | T => exact hT
  | F => exact hF
  | Z => exact hZ

/-- A sign holding nothing is empty. -/
theorem none_empty {s : Sign} (h : ∀ x, s x = false) : sIsEmpty s = true := by
  show (!(s T || s F || s Z)) = true
  rw [h T, h F, h Z]
  rfl

/-- A nonempty sign holds something. -/
theorem nonempty_some {s : Sign} (h : sIsEmpty s = false) : ∃ x, s x = true := by
  cases notOr3F _ _ _ h with
  | inl hT => exact ⟨T, hT⟩
  | inr h' =>
      cases h' with
      | inl hF => exact ⟨F, hF⟩
      | inr hZ => exact ⟨Z, hZ⟩

/-- A subsign of an empty sign is empty. -/
theorem empty_sub {s s' : Sign} (h : sIsEmpty s = true) (hs : ∀ x, s' x = true → s x = true) :
    sIsEmpty s' = true := by
  apply none_empty
  intro x
  cases hx : s' x with
  | true => have := empty_none h x; rw [hs x hx] at this; cases this
  | false => rfl

theorem inter_mem {a b : Sign} {x : V} : inter a b x = true ↔ (a x = true ∧ b x = true) :=
  ⟨fun h => andT _ _ h, fun ⟨h1, h2⟩ => andI _ _ h1 h2⟩

theorem upd_same (e : Env) (n : Nat) (s : Sign) : upd e n s n = s := if_pos rfl
theorem upd_other (e : Env) {n m : Nat} (s : Sign) (h : ¬ m = n) : upd e n s m = e m := if_neg h

/-- Narrowing two different cells commutes. -/
theorem upd_comm (e : Env) {n m : Nat} (hnm : ¬ n = m) (a b : Sign) :
    EnvEq (upd (upd e n a) m b) (upd (upd e m b) n a) := by
  intro k x
  cases Decidable.em (k = m) with
  | inl hk =>
      rw [hk, upd_same, upd_other _ _ (fun h => hnm h.symm), upd_same]
  | inr hk =>
      rw [upd_other _ _ hk]
      cases Decidable.em (k = n) with
      | inl hk' => rw [hk', upd_same, upd_same]
      | inr hk' => rw [upd_other _ _ hk', upd_other _ _ hk', upd_other _ _ hk]

/-- Narrowing one cell twice narrows it once, by the intersection. -/
theorem upd_twice (e : Env) (n : Nat) (a b : Sign) :
    EnvEq (upd (upd e n a) n b) (upd e n b) := by
  intro k x
  cases Decidable.em (k = n) with
  | inl hk => rw [hk, upd_same, upd_same]
  | inr hk => rw [upd_other _ _ hk, upd_other _ _ hk, upd_other _ _ hk]

/-- Narrowing a cell to a sign it already sits inside changes nothing. -/
theorem upd_absorb (e : Env) (n : Nat) (s : Sign) (h : ∀ x, e n x = true → s x = true) :
    EnvEq (upd e n (inter (e n) s)) e := by
  intro k x
  cases Decidable.em (k = n) with
  | inl hk =>
      rw [hk, upd_same]
      show (e n x && s x) = e n x
      cases hx : e n x with
      | true => exact andI _ _ rfl (h x hx)
      | false => rfl
  | inr hk => rw [upd_other _ _ hk]

theorem upd_congr {e e' : Env} (h : EnvEq e e') (n : Nat) {s s' : Sign} (hs : ∀ x, s x = s' x) :
    EnvEq (upd e n s) (upd e' n s') := by
  intro k x
  cases Decidable.em (k = n) with
  | inl hk => rw [hk, upd_same, upd_same]; exact hs x
  | inr hk => rw [upd_other _ _ hk, upd_other _ _ hk]; exact h k x

theorem upd_sub {e e' : Env} (h : Sub e' e) (n : Nat) {s s' : Sign} (hs : ∀ x, s' x = true → s x = true) :
    Sub (upd e' n s') (upd e n s) := by
  intro k x hx
  cases Decidable.em (k = n) with
  | inl hk => rw [hk, upd_same] at hx; rw [hk, upd_same]; exact hs x hx
  | inr hk => rw [upd_other _ _ hk] at hx; rw [upd_other _ _ hk]; exact h k x hx

/-! ### The rules, as a table read off `closes` -/

/-- Axioms: an empty cell; a constant refused by its sign; a compound given a
sign that admits neither verdict (a compound is never Z). -/
inductive Ax : Env → Node → Prop
  | atom {e : Env} {s : Sign} {n : Nat} : sIsEmpty (inter (e n) s) = true → Ax e (s, .atom n)
  | top  {e : Env} {s : Sign} : s T = false → Ax e (s, .top)
  | bot  {e : Env} {s : Sign} : s F = false → Ax e (s, .bot)
  | neg  {e : Env} {s : Sign} {φ : Fm} : s T = false → s F = false → Ax e (s, .neg φ)
  | conj {e : Env} {s : Sign} {φ ψ : Fm} : s T = false → s F = false → Ax e (s, .conj φ ψ)
  | disj {e : Env} {s : Sign} {φ ψ : Fm} : s T = false → s F = false → Ax e (s, .disj φ ψ)

/-- One-premise rules that do not touch the environment: the nodes they put in
front. (The atom rule, which narrows a cell, is `Der.atom` itself.) -/
inductive RuleC : Node → List Node → Prop
  | top  {s : Sign} : s T = true → RuleC (s, .top) []
  | bot  {s : Sign} : s F = true → RuleC (s, .bot) []
  | negDrop  {s : Sign} {φ : Fm} : s T = true → s F = true → RuleC (s, .neg φ) []
  | negT     {s : Sign} {φ : Fm} : s T = true → s F = false → RuleC (s, .neg φ) [(SignF, φ)]
  | negF     {s : Sign} {φ : Fm} : s T = false → s F = true → RuleC (s, .neg φ) [(SignP, φ)]
  | conjDrop {s : Sign} {φ ψ : Fm} : s T = true → s F = true → RuleC (s, .conj φ ψ) []
  | conjT    {s : Sign} {φ ψ : Fm} : s T = true → s F = false →
      RuleC (s, .conj φ ψ) [(SignT, φ), (SignT, ψ)]
  | disjDrop {s : Sign} {φ ψ : Fm} : s T = true → s F = true → RuleC (s, .disj φ ψ) []
  | disjF    {s : Sign} {φ ψ : Fm} : s T = false → s F = true →
      RuleC (s, .disj φ ψ) [(SignN, φ), (SignN, ψ)]
  | imp  {s : Sign} {φ ψ : Fm} : RuleC (s, .imp φ ψ) [(s, .disj (.neg φ) ψ)]
  | xor  {s : Sign} {φ ψ : Fm} :
      RuleC (s, .xor φ ψ) [(s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ))]
  | xnor {s : Sign} {φ ψ : Fm} :
      RuleC (s, .xnor φ ψ) [(s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ)))]

/-- Two-premise rules: the two branches. -/
inductive Rule2 : Node → List Node → List Node → Prop
  | conjF {s : Sign} {φ ψ : Fm} : s T = false → s F = true → Rule2 (s, .conj φ ψ) [(SignN, φ)] [(SignN, ψ)]
  | disjT {s : Sign} {φ ψ : Fm} : s T = true → s F = false → Rule2 (s, .disj φ ψ) [(SignT, φ)] [(SignT, ψ)]

/-- **Derivations, indexed by an upper bound on their number of leaves.** A rule
acts on any node; new nodes go in front of the rest; an atom narrows its cell. -/
inductive Der : Nat → Env → List Node → Prop
  | ax   {e : Env} {S S' : List Node} {x : Node} : Pick S x S' → Ax e x → Der 1 e S
  | atom {e : Env} {S S' : List Node} {s : Sign} {n : Nat} {k : Nat} :
      Pick S (s, .atom n) S' → sIsEmpty (inter (e n) s) = false →
      Der k (upd e n (inter (e n) s)) S' → Der k e S
  | one  {e : Env} {S S' : List Node} {x : Node} {ns : List Node} {k : Nat} :
      Pick S x S' → RuleC x ns → Der k e (ns ++ S') → Der k e S
  | two  {e : Env} {S S' : List Node} {x : Node} {ns₁ ns₂ : List Node} {k₁ k₂ : Nat} :
      Pick S x S' → Rule2 x ns₁ ns₂ → Der k₁ e (ns₁ ++ S') → Der k₂ e (ns₂ ++ S') →
      Der (k₁ + k₂) e S
  | pad  {e : Env} {S : List Node} {k : Nat} : Der k e S → Der (k + 1) e S

/-! ### The table is a partition: axioms, one-premise, two-premise never overlap -/

theorem ax_ruleC {e : Env} {x : Node} {ns : List Node} (a : Ax e x) (r : RuleC x ns) : False := by
  cases a with
  | atom _ => cases r
  | top h1 => cases r with | top h2 => rw [h1] at h2; cases h2
  | bot h1 => cases r with | bot h2 => rw [h1] at h2; cases h2
  | neg h1 h2 =>
      cases r with
      | negDrop h3 _ => rw [h1] at h3; cases h3
      | negT h3 _ => rw [h1] at h3; cases h3
      | negF _ h3 => rw [h2] at h3; cases h3
  | conj h1 h2 =>
      cases r with
      | conjDrop h3 _ => rw [h1] at h3; cases h3
      | conjT h3 _ => rw [h1] at h3; cases h3
  | disj h1 h2 =>
      cases r with
      | disjDrop h3 _ => rw [h1] at h3; cases h3
      | disjF _ h3 => rw [h2] at h3; cases h3

theorem ax_rule2 {e : Env} {x : Node} {n₁ n₂ : List Node} (a : Ax e x) (r : Rule2 x n₁ n₂) : False := by
  cases a with
  | atom _ => cases r
  | top _ => cases r
  | bot _ => cases r
  | neg _ _ => cases r
  | conj h1 h2 => cases r with | conjF _ h3 => rw [h2] at h3; cases h3
  | disj h1 h2 => cases r with | disjT h3 _ => rw [h1] at h3; cases h3

theorem ruleC_rule2 {x : Node} {ns n₁ n₂ : List Node} (r : RuleC x ns) (r2 : Rule2 x n₁ n₂) : False := by
  cases r with
  | conjDrop h1 h2 => cases r2 with | conjF h3 _ => rw [h1] at h3; cases h3
  | conjT h1 h2 => cases r2 with | conjF _ h3 => rw [h2] at h3; cases h3
  | disjDrop h1 h2 => cases r2 with | disjT _ h3 => rw [h2] at h3; cases h3
  | disjF h1 h2 => cases r2 with | disjT h3 _ => rw [h1] at h3; cases h3
  | top _ => cases r2
  | bot _ => cases r2
  | negDrop _ _ => cases r2
  | negT _ _ => cases r2
  | negF _ _ => cases r2
  | imp => cases r2
  | xor => cases r2
  | xnor => cases r2

theorem ruleC_not_atom {s : Sign} {n : Nat} {ns : List Node} (r : RuleC (s, .atom n) ns) : False := by
  cases r

theorem ruleC_det {x : Node} {ns ns' : List Node} (r : RuleC x ns) (r' : RuleC x ns') : ns = ns' := by
  cases r with
  | top _ => cases r' with | top _ => rfl
  | bot _ => cases r' with | bot _ => rfl
  | negDrop h1 h2 =>
      cases r' with
      | negDrop _ _ => rfl
      | negT _ h3 => rw [h2] at h3; cases h3
      | negF h3 _ => rw [h1] at h3; cases h3
  | negT h1 h2 =>
      cases r' with
      | negDrop _ h3 => rw [h2] at h3; cases h3
      | negT _ _ => rfl
      | negF h3 _ => rw [h1] at h3; cases h3
  | negF h1 h2 =>
      cases r' with
      | negDrop h3 _ => rw [h1] at h3; cases h3
      | negT h3 _ => rw [h1] at h3; cases h3
      | negF _ _ => rfl
  | conjDrop h1 h2 =>
      cases r' with
      | conjDrop _ _ => rfl
      | conjT _ h3 => rw [h2] at h3; cases h3
  | conjT h1 h2 =>
      cases r' with
      | conjDrop _ h3 => rw [h2] at h3; cases h3
      | conjT _ _ => rfl
  | disjDrop h1 h2 =>
      cases r' with
      | disjDrop _ _ => rfl
      | disjF h3 _ => rw [h1] at h3; cases h3
  | disjF h1 h2 =>
      cases r' with
      | disjDrop h3 _ => rw [h1] at h3; cases h3
      | disjF _ _ => rfl
  | imp => cases r' with | imp => rfl
  | xor => cases r' with | xor => rfl
  | xnor => cases r' with | xnor => rfl

theorem rule2_det {x : Node} {n₁ n₂ m₁ m₂ : List Node} (r : Rule2 x n₁ n₂) (r' : Rule2 x m₁ m₂) :
    n₁ = m₁ ∧ n₂ = m₂ := by
  cases r with
  | conjF _ _ => cases r' with | conjF _ _ => exact ⟨rfl, rfl⟩
  | disjT _ _ => cases r' with | disjT _ _ => exact ⟨rfl, rfl⟩

/-! ### Structural lemmas -/

theorem der_add : ∀ (d : Nat) {k : Nat} {e : Env} {S : List Node}, Der k e S → Der (k + d) e S
  | 0, _, _, _, h => h
  | d + 1, _, _, _, h => Der.pad (der_add d h)

/-- The index is an upper bound: it may always be raised. -/
theorem der_mono {k k' : Nat} {e : Env} {S : List Node} (h : Der k e S) (hk : k ≤ k') : Der k' e S := by
  have ⟨d, hd⟩ := le_dest hk
  rw [← hd]
  exact der_add d h

theorem der_pos : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S → 1 ≤ k
  | _, _, _, Der.ax _ _ => Nat.le_refl 1
  | _, _, _, Der.atom _ _ d => der_pos d
  | _, _, _, Der.one _ _ d => der_pos d
  | _, _, _, Der.two _ _ d₁ _ => Nat.le_trans (der_pos d₁) (Nat.le_add_right _ _)
  | _, _, _, Der.pad d => Nat.le_trans (der_pos d) (Nat.le_add_right _ 1)

/-- An axiom survives a refinement of the environment. -/
theorem ax_sub {e e' : Env} (h : Sub e' e) {x : Node} : Ax e x → Ax e' x
  | Ax.atom hemp => Ax.atom (empty_sub hemp (fun v hv => by
      have ⟨h1, h2⟩ := inter_mem.mp hv
      exact inter_mem.mpr ⟨h _ _ h1, h2⟩))
  | Ax.top h1 => Ax.top h1
  | Ax.bot h1 => Ax.bot h1
  | Ax.neg h1 h2 => Ax.neg h1 h2
  | Ax.conj h1 h2 => Ax.conj h1 h2
  | Ax.disj h1 h2 => Ax.disj h1 h2

theorem ax_congr {e e' : Env} (h : EnvEq e e') {x : Node} (a : Ax e x) : Ax e' x :=
  ax_sub (sub_of_envEq (envEq_symm h)) a

/-- The narrowed cell sits inside the old one. -/
theorem upd_inter_sub (e : Env) (n : Nat) (s : Sign) : Sub (upd e n (inter (e n) s)) e := by
  intro k x hx
  cases Decidable.em (k = n) with
  | inl hk => rw [hk, upd_same] at hx; rw [hk]; exact (inter_mem.mp hx).1
  | inr hk => rw [upd_other _ _ hk] at hx; exact hx

theorem inter_congr_left {e e' : Env} (h : EnvEq e e') (n : Nat) (s : Sign) :
    ∀ x, inter (e n) s x = inter (e' n) s x :=
  fun x => by show (e n x && s x) = (e' n x && s x); rw [h n x]

/-- Derivations respect pointwise-equal environments. -/
theorem der_congr : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S →
    ∀ {e' : Env}, EnvEq e e' → Der k e' S := by
  intro k e S d
  induction d with
  | ax p a => intro e' h; exact Der.ax p (ax_congr h a)
  | @atom e S S' s n k p hne d ih =>
      intro e' h
      have hne' : sIsEmpty (inter (e' n) s) = false := by
        rw [← sIsEmpty_congr (inter_congr_left h n s)]; exact hne
      exact Der.atom p hne' (ih (upd_congr h n (inter_congr_left h n s)))
  | one p r _ ih => intro e' h; exact Der.one p r (ih h)
  | two p r _ _ ih₁ ih₂ => intro e' h; exact Der.two p r (ih₁ h) (ih₂ h)
  | pad _ ih => intro e' h; exact Der.pad (ih h)

/-- **REFINING THE ENVIRONMENT CAN ONLY HELP.** A derivation under `e` is one
under any `e'` whose cells sit inside those of `e`, with no more leaves. -/
theorem der_refine : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S →
    ∀ {e' : Env}, Sub e' e → Der k e' S := by
  intro k e S d
  induction d with
  | ax p a => intro e' h; exact Der.ax p (ax_sub h a)
  | @atom e S S' s n k p hne d ih =>
      intro e' h
      cases hne' : sIsEmpty (inter (e' n) s) with
      | true => exact der_mono (Der.ax p (Ax.atom hne')) (der_pos d)
      | false =>
          have hsub : Sub (upd e' n (inter (e' n) s)) (upd e n (inter (e n) s)) :=
            upd_sub h n (fun x hx => by
              have ⟨h1, h2⟩ := inter_mem.mp hx
              exact inter_mem.mpr ⟨h n x h1, h2⟩)
          exact Der.atom p hne' (ih hsub)
  | one p r _ ih => intro e' h; exact Der.one p r (ih h)
  | two p r _ _ ih₁ ih₂ => intro e' h; exact Der.two p r (ih₁ h) (ih₂ h)
  | pad _ ih => intro e' h; exact Der.pad (ih h)

/-- **WEAKENING IS FREE.** Insert a node anywhere: same leaves. -/
theorem der_weak : ∀ {k : Nat} {e : Env} {S Sw : List Node} {nd : Node},
    Der k e S → Ins nd S Sw → Der k e Sw
  | _, _, _, _, _, Der.ax p a, i => by
      have ⟨_, p', _⟩ := pick_ins p i
      exact Der.ax p' a
  | _, _, _, _, _, Der.atom p hne d, i => by
      have ⟨_, p', i'⟩ := pick_ins p i
      exact Der.atom p' hne (der_weak d i')
  | _, _, _, _, _, Der.one p r d, i => by
      have ⟨_, p', i'⟩ := pick_ins p i
      exact Der.one p' r (der_weak d (ins_append _ _ i'))
  | _, _, _, _, _, Der.two p r d₁ d₂, i => by
      have ⟨_, p', i'⟩ := pick_ins p i
      exact Der.two p' r (der_weak d₁ (ins_append _ _ i')) (der_weak d₂ (ins_append _ _ i'))
  | _, _, _, _, _, Der.pad d, i => Der.pad (der_weak d i)

/-- **EXCHANGE IS FREE.** -/
theorem der_perm : ∀ {k : Nat} {e : Env} {S S' : List Node}, Der k e S → Perm S S' → Der k e S'
  | _, _, _, _, Der.ax p a, q => by
      have ⟨_, p', _⟩ := perm_pick q p
      exact Der.ax p' a
  | _, _, _, _, Der.atom p hne d, q => by
      have ⟨_, p', q'⟩ := perm_pick q p
      exact Der.atom p' hne (der_perm d q')
  | _, _, _, _, Der.one p r d, q => by
      have ⟨_, p', q'⟩ := perm_pick q p
      exact Der.one p' r (der_perm d (perm_append_left _ q'))
  | _, _, _, _, Der.two p r d₁ d₂, q => by
      have ⟨_, p', q'⟩ := perm_pick q p
      exact Der.two p' r (der_perm d₁ (perm_append_left _ q')) (der_perm d₂ (perm_append_left _ q'))
  | _, _, _, _, Der.pad d, q => Der.pad (der_perm d q)

/-- Two blocks in front may be swapped. -/
theorem der_swap_front {k : Nat} {e : Env} (a b R : List Node) (d : Der k e (a ++ (b ++ R))) :
    Der k e (b ++ (a ++ R)) := by
  apply der_perm d
  rw [← appAssoc a b R, ← appAssoc b a R]
  exact perm_append_right R (perm_append_comm a b)

/-! ### Inversion — height-preserving, at any position -/

/-- **A ONE-PREMISE RULE CAN BE APPLIED FIRST.** If a derivation exists and a
node admits such a rule, the premise of that rule is derivable with no more
leaves — whatever the derivation did first. -/
theorem inv1 : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S →
    ∀ {x : Node} {S' ns : List Node}, Pick S x S' → RuleC x ns → Der k e (ns ++ S') := by
  intro k e S d
  induction d with
  | @ax e S Sy y p a =>
      intro x S' ns px r
      cases pick_pick p px with
      | inl h => rw [h.1] at a; exact absurd r (ax_ruleC a)
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          exact Der.ax (pick_append ns p2) a
  | @atom e S Sy s n k p hne d ih =>
      intro x S' ns px r
      cases pick_pick p px with
      | inl h => rw [← h.1] at r; exact absurd r ruleC_not_atom
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          exact Der.atom (pick_append ns p2) hne (ih p1 r)
  | @one e S Sy y ns₂ k p r₂ d ih =>
      intro x S' ns px r
      cases pick_pick p px with
      | inl h =>
          rw [← h.1] at r
          rw [ruleC_det r r₂, ← h.2]
          exact d
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          have d' := ih (pick_append ns₂ p1) r
          exact Der.one (pick_append ns p2) r₂ (der_swap_front ns ns₂ S₃ d')
  | @two e S Sy y n₁ n₂ k₁ k₂ p r₂ d₁ d₂ ih₁ ih₂ =>
      intro x S' ns px r
      cases pick_pick p px with
      | inl h => rw [← h.1] at r; exact absurd r₂ (ruleC_rule2 r)
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          have d₁' := ih₁ (pick_append n₁ p1) r
          have d₂' := ih₂ (pick_append n₂ p1) r
          exact Der.two (pick_append ns p2) r₂ (der_swap_front ns n₁ S₃ d₁') (der_swap_front ns n₂ S₃ d₂')
  | pad _ ih => intro x S' ns px r; exact Der.pad (ih px r)

/-- **A TWO-PREMISE RULE CAN BE APPLIED FIRST**, each branch with the whole bound. -/
theorem inv2 : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S →
    ∀ {x : Node} {S' n₁ n₂ : List Node}, Pick S x S' → Rule2 x n₁ n₂ →
      Der k e (n₁ ++ S') ∧ Der k e (n₂ ++ S') := by
  intro k e S d
  induction d with
  | @ax e S Sy y p a =>
      intro x S' n₁ n₂ px r
      cases pick_pick p px with
      | inl h => rw [h.1] at a; exact absurd r (ax_rule2 a)
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          exact ⟨Der.ax (pick_append n₁ p2) a, Der.ax (pick_append n₂ p2) a⟩
  | @atom e S Sy s n k p hne d ih =>
      intro x S' n₁ n₂ px r
      cases pick_pick p px with
      | inl h => rw [← h.1] at r; cases r
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          have ⟨d₁, d₂⟩ := ih p1 r
          exact ⟨Der.atom (pick_append n₁ p2) hne d₁, Der.atom (pick_append n₂ p2) hne d₂⟩
  | @one e S Sy y ns k p rc d ih =>
      intro x S' n₁ n₂ px r
      cases pick_pick p px with
      | inl h => rw [← h.1] at r; exact absurd r (ruleC_rule2 rc)
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          have ⟨d₁, d₂⟩ := ih (pick_append ns p1) r
          exact ⟨Der.one (pick_append n₁ p2) rc (der_swap_front n₁ ns S₃ d₁),
                 Der.one (pick_append n₂ p2) rc (der_swap_front n₂ ns S₃ d₂)⟩
  | @two e S Sy y m₁ m₂ k₁ k₂ p r₂ d₁ d₂ ih₁ ih₂ =>
      intro x S' n₁ n₂ px r
      cases pick_pick p px with
      | inl h =>
          rw [← h.1] at r
          have ⟨e1, e2⟩ := rule2_det r₂ r
          rw [← e1, ← e2, ← h.2]
          exact ⟨der_mono d₁ (Nat.le_add_right _ _), der_mono d₂ (Nat.le_add_left _ _)⟩
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          have ⟨a₁, a₂⟩ := ih₁ (pick_append m₁ p1) r
          have ⟨b₁, b₂⟩ := ih₂ (pick_append m₂ p1) r
          exact ⟨Der.two (pick_append n₁ p2) r₂ (der_swap_front n₁ m₁ S₃ a₁) (der_swap_front n₁ m₂ S₃ b₁),
                 Der.two (pick_append n₂ p2) r₂ (der_swap_front n₂ m₁ S₃ a₂) (der_swap_front n₂ m₂ S₃ b₂)⟩
  | pad _ ih =>
      intro x S' n₁ n₂ px r
      have ⟨d₁, d₂⟩ := ih px r
      exact ⟨Der.pad d₁, Der.pad d₂⟩

/-- Narrowing one cell by two signs, in either order, is one narrowing. -/
theorem upd_twice_inter (e : Env) (n : Nat) (a b : Sign) :
    EnvEq (upd (upd e n (inter (e n) a)) n (inter (upd e n (inter (e n) a) n) b))
          (upd (upd e n (inter (e n) b)) n (inter (upd e n (inter (e n) b) n) a)) := by
  intro k x
  cases Decidable.em (k = n) with
  | inl hk =>
      rw [hk, upd_same, upd_same, upd_same, upd_same]
      show ((e n x && a x) && b x) = ((e n x && b x) && a x)
      rw [bandAssoc, bandAssoc, bandComm (a x) (b x)]
  | inr hk => rw [upd_other _ _ hk, upd_other _ _ hk, upd_other _ _ hk, upd_other _ _ hk]

/-- **AN ATOM CAN BE NARROWED FIRST.** Either its cell dies, or the derivation
continues under the narrowed cell with no more leaves. -/
theorem inv_atom : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S →
    ∀ {s : Sign} {n : Nat} {S' : List Node}, Pick S (s, .atom n) S' →
      sIsEmpty (inter (e n) s) = true ∨
      (sIsEmpty (inter (e n) s) = false ∧ Der k (upd e n (inter (e n) s)) S') := by
  intro k e S d
  induction d with
  | @ax e S Sy y p a =>
      intro s n S' px
      cases pick_pick p px with
      | inl h =>
          rw [h.1] at a
          cases a with
          | atom hemp => exact Or.inl hemp
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          cases hne : sIsEmpty (inter (e n) s) with
          | true => exact Or.inl rfl
          | false => exact Or.inr ⟨rfl, Der.ax p2 (ax_sub (upd_inter_sub e n s) a)⟩
  | @atom e S Sy s' m k p hne' d ih =>
      intro s n S' px
      cases pick_pick p px with
      | inl h =>
          have h1 : s' = s := congrArg Prod.fst h.1
          have h2 : m = n := Fm.atom.inj (congrArg Prod.snd h.1)
          rw [← h1, ← h2, ← h.2]
          exact Or.inr ⟨hne', d⟩
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          cases hne : sIsEmpty (inter (e n) s) with
          | true => exact Or.inl rfl
          | false =>
              refine Or.inr ⟨rfl, ?_⟩
              cases Decidable.em (m = n) with
              | inl hmn =>
                  rw [hmn] at hne' d p2 ih
                  cases ih p1 with
                  | inl hemp =>
                      -- the second narrowing kills the cell: `y` is an axiom under `e[n∩s]`
                      refine der_mono (Der.ax p2 (Ax.atom ?_)) (der_pos d)
                      rw [upd_same]
                      rw [sIsEmpty_congr (fun x => by
                        show ((e n x && s x) && s' x) = ((e n x && s' x) && s x)
                        rw [bandAssoc, bandAssoc, bandComm (s x) (s' x)])]
                      rw [upd_same] at hemp
                      exact hemp
                  | inr hd =>
                      have ⟨hne2, d2⟩ := hd
                      refine Der.atom p2 ?_ (der_congr d2 (envEq_symm (upd_twice_inter e n s s')))
                      rw [upd_same]
                      rw [sIsEmpty_congr (fun x => by
                        show ((e n x && s x) && s' x) = ((e n x && s' x) && s x)
                        rw [bandAssoc, bandAssoc, bandComm (s x) (s' x)])]
                      rw [upd_same] at hne2
                      exact hne2
              | inr hmn =>
                  have hcell : ∀ x, inter (upd e m (inter (e m) s') n) s x = inter (e n) s x :=
                    fun x => by rw [upd_other _ _ (fun h => hmn h.symm)]
                  cases ih p1 with
                  | inl hemp =>
                      rw [sIsEmpty_congr hcell] at hemp
                      rw [hemp] at hne
                      cases hne
                  | inr hd =>
                      have ⟨_, d2⟩ := hd
                      refine Der.atom p2 ?_ ?_
                      · rw [upd_other _ _ hmn]; exact hne'
                      · refine der_congr d2 ?_
                        refine envEq_trans (upd_congr (envEq_refl _) n hcell) ?_
                        refine envEq_trans (upd_comm e hmn _ _) ?_
                        exact upd_congr (envEq_refl _) m (fun x => by rw [upd_other _ _ hmn])
  | @one e S Sy y ns k p rc d ih =>
      intro s n S' px
      cases pick_pick p px with
      | inl h => rw [h.1] at rc; exact absurd rc ruleC_not_atom
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          cases ih (pick_append ns p1) with
          | inl hemp => exact Or.inl hemp
          | inr hd => exact Or.inr ⟨hd.1, Der.one p2 rc hd.2⟩
  | @two e S Sy y n₁ n₂ k₁ k₂ p r₂ d₁ d₂ ih₁ ih₂ =>
      intro s n S' px
      cases pick_pick p px with
      | inl h => rw [h.1] at r₂; cases r₂
      | inr h =>
          have ⟨S₃, p1, p2⟩ := h
          cases ih₁ (pick_append n₁ p1) with
          | inl hemp => exact Or.inl hemp
          | inr hd₁ =>
              cases ih₂ (pick_append n₂ p1) with
              | inl hemp => exact Or.inl hemp
              | inr hd₂ => exact Or.inr ⟨hd₁.1, Der.two p2 r₂ hd₁.2 hd₂.2⟩
  | pad _ ih =>
      intro s n S' px
      cases ih px with
      | inl hemp => exact Or.inl hemp
      | inr hd => exact Or.inr ⟨hd.1, Der.pad hd.2⟩

/-! ### The atomic cut: one cell, split two ways -/

/-- Narrowing by `a` and then by `s` is narrowing by `a ∩ s`. -/
theorem upd_upd_same_inter (e : Env) (n : Nat) (a s : Sign) :
    EnvEq (upd (upd e n (inter (e n) a)) n (inter (upd e n (inter (e n) a) n) s))
          (upd e n (inter (inter (e n) a) s)) := by
  intro k x
  cases Decidable.em (k = n) with
  | inl hk => rw [hk, upd_same, upd_same, upd_same]
  | inr hk => rw [upd_other _ _ hk, upd_other _ _ hk, upd_other _ _ hk]

/-- A middle sign that the outer two already force is absorbed. -/
theorem inter_absorb_mid (u a s : Sign) (h : ∀ x, u x = true → s x = true → a x = true) :
    ∀ x, inter (inter u a) s x = inter u s x := by
  intro x
  show ((u x && a x) && s x) = (u x && s x)
  cases hu : u x with
  | false => rfl
  | true =>
      cases hs : s x with
      | false => cases a x <;> rfl
      | true => rw [h x hu hs]; rfl

theorem inter_swap (u a s : Sign) : ∀ x, inter (inter u a) s x = inter (inter u s) a x := by
  intro x
  show ((u x && a x) && s x) = ((u x && s x) && a x)
  rw [bandAssoc, bandAssoc, bandComm (a x) (s x)]

/-- **THE ATOMIC CUT.** A derivation under the cell narrowed by `a` and one under
the cell narrowed by `b`, with `a ∪ b` covering the cell, give a derivation
under the cell itself — with at most the PRODUCT of the two leaf counts. -/
theorem cut_env : ∀ {k₁ : Nat} {e : Env} {S : List Node}, Der k₁ e S →
    ∀ {k₂ : Nat} {n : Nat} {a b : Sign} {e₀ : Env},
      EnvEq e (upd e₀ n (inter (e₀ n) a)) →
      Der k₂ (upd e₀ n (inter (e₀ n) b)) S →
      (∀ x, e₀ n x = true → a x = true ∨ b x = true) →
      sIsEmpty (e₀ n) = false →
      Der (k₁ * k₂) e₀ S := by
  intro k₁ e S d
  induction d with
  | @ax e S Sy y p ax =>
      intro k₂ n a' b e₀ he d₂ hcov hne0
      have hk : 1 ≤ 1 * k₂ := by rw [Nat.one_mul]; exact der_pos d₂
      cases ax with
      | @atom s' m hemp =>
          cases Decidable.em (m = n) with
          | inr hmn =>
              have hemp' : sIsEmpty (inter (e₀ m) s') = true := by
                rw [← sIsEmpty_congr (fun x => by
                  show (e m x && s' x) = (e₀ m x && s' x)
                  rw [he m x, upd_other _ _ hmn])]
                exact hemp
              exact der_mono (Der.ax p (Ax.atom hemp')) hk
          | inl hmn =>
              rw [hmn] at hemp p
              have hemp' : sIsEmpty (inter (inter (e₀ n) a') s') = true := by
                rw [← sIsEmpty_congr (fun x => by
                  show (e n x && s' x) = ((e₀ n x && a' x) && s' x)
                  rw [he n x, upd_same]; rfl)]
                exact hemp
              cases inv_atom d₂ p with
              | inl hemp2 =>
                  rw [upd_same] at hemp2
                  refine der_mono (Der.ax p (Ax.atom ?_)) hk
                  apply none_empty
                  intro x
                  cases hx : inter (e₀ n) s' x with
                  | false => rfl
                  | true =>
                      have ⟨h1, h2⟩ := inter_mem.mp hx
                      cases hcov x h1 with
                      | inl ha =>
                          have := empty_none hemp' x
                          rw [show inter (inter (e₀ n) a') s' x = true from
                                andI _ _ (andI _ _ h1 ha) h2] at this
                          cases this
                      | inr hb =>
                          have := empty_none hemp2 x
                          rw [show inter (inter (e₀ n) b) s' x = true from
                                andI _ _ (andI _ _ h1 hb) h2] at this
                          cases this
              | inr hd =>
                  have ⟨hne2, d2'⟩ := hd
                  rw [upd_same] at hne2 d2'
                  have hb : ∀ x, e₀ n x = true → s' x = true → b x = true := by
                    intro x h1 h2
                    cases hcov x h1 with
                    | inr h => exact h
                    | inl ha =>
                        have := empty_none hemp' x
                        rw [show inter (inter (e₀ n) a') s' x = true from
                              andI _ _ (andI _ _ h1 ha) h2] at this
                        cases this
                  have d3 : Der k₂ (upd e₀ n (inter (e₀ n) s')) Sy :=
                    der_congr d2' (envEq_trans (upd_twice e₀ n _ _)
                      (upd_congr (envEq_refl _) n (inter_absorb_mid (e₀ n) b s' hb)))
                  have hne3 : sIsEmpty (inter (e₀ n) s') = false := by
                    rw [← sIsEmpty_congr (inter_absorb_mid (e₀ n) b s' hb)]
                    exact hne2
                  exact der_mono (Der.atom p hne3 d3) (by rw [Nat.one_mul]; exact Nat.le_refl _)
      | top h1 => exact der_mono (Der.ax p (Ax.top h1)) hk
      | bot h1 => exact der_mono (Der.ax p (Ax.bot h1)) hk
      | neg h1 h2 => exact der_mono (Der.ax p (Ax.neg h1 h2)) hk
      | conj h1 h2 => exact der_mono (Der.ax p (Ax.conj h1 h2)) hk
      | disj h1 h2 => exact der_mono (Der.ax p (Ax.disj h1 h2)) hk
  | @atom e S Sy s' m k₁ p hne' d ih =>
      intro k₂ n a' b e₀ he d₂ hcov hne0
      have h1k : 1 ≤ k₁ * k₂ := Nat.le_trans (der_pos d) (Nat.le_mul_of_pos_right k₁ (der_pos d₂))
      cases Decidable.em (m = n) with
      | inr hmn =>
          have hnm : ¬ n = m := fun h => hmn h.symm
          have hcell : ∀ x, inter (e m) s' x = inter (e₀ m) s' x :=
            fun x => by show (e m x && s' x) = (e₀ m x && s' x); rw [he m x, upd_other _ _ hmn]
          cases inv_atom d₂ p with
          | inl hemp2 =>
              rw [upd_other _ _ hmn] at hemp2
              exact der_mono (Der.ax p (Ax.atom hemp2)) h1k
          | inr hd =>
              have ⟨hne2, d2'⟩ := hd
              rw [upd_other _ _ hmn] at hne2 d2'
              -- the IH at the environment narrowed on cell m
              have he' : EnvEq (upd e m (inter (e m) s'))
                  (upd (upd e₀ m (inter (e₀ m) s')) n (inter (upd e₀ m (inter (e₀ m) s') n) a')) := by
                refine envEq_trans (upd_congr he m hcell) ?_
                refine envEq_trans (upd_comm e₀ hnm _ _) ?_
                exact upd_congr (envEq_refl _) n (fun x => by
                  show (e₀ n x && a' x) = (upd e₀ m (inter (e₀ m) s') n x && a' x)
                  rw [upd_other _ _ hnm])
              have d3 : Der k₂ (upd (upd e₀ m (inter (e₀ m) s')) n
                  (inter (upd e₀ m (inter (e₀ m) s') n) b)) Sy := by
                refine der_congr d2' ?_
                refine envEq_trans (upd_comm e₀ hnm _ _) ?_
                exact upd_congr (envEq_refl _) n (fun x => by
                  show (e₀ n x && b x) = (upd e₀ m (inter (e₀ m) s') n x && b x)
                  rw [upd_other _ _ hnm])
              have hcov' : ∀ x, upd e₀ m (inter (e₀ m) s') n x = true → a' x = true ∨ b x = true := by
                intro x hx; rw [upd_other _ _ hnm] at hx; exact hcov x hx
              have hne0' : sIsEmpty (upd e₀ m (inter (e₀ m) s') n) = false := by
                rw [upd_other _ _ hnm]; exact hne0
              have d4 := ih he' d3 hcov' hne0'
              have hne3 : sIsEmpty (inter (e₀ m) s') = false := by
                rw [← sIsEmpty_congr hcell]; exact hne'
              exact Der.atom p hne3 d4
      | inl hmn =>
          rw [hmn] at hne' d p ih
          have hcell : ∀ x, inter (e n) s' x = inter (inter (e₀ n) a') s' x :=
            fun x => by show (e n x && s' x) = ((e₀ n x && a' x) && s' x); rw [he n x, upd_same]; rfl
          have hneA : sIsEmpty (inter (inter (e₀ n) a') s') = false := by
            rw [← sIsEmpty_congr hcell]; exact hne'
          have hneS : sIsEmpty (inter (e₀ n) s') = false := by
            have ⟨x, hx⟩ := nonempty_some hneA
            have ⟨h12, h3⟩ := inter_mem.mp hx
            exact sNonempty_of_mem (inter_mem.mpr ⟨(inter_mem.mp h12).1, h3⟩)
          -- the narrowed environment of `d`, in terms of `e₀`
          have hd : EnvEq (upd e n (inter (e n) s')) (upd e₀ n (inter (inter (e₀ n) a') s')) :=
            envEq_trans (upd_congr he n hcell) (upd_twice e₀ n _ _)
          cases inv_atom d₂ p with
          | inl hemp2 =>
              rw [upd_same] at hemp2
              have ha : ∀ x, e₀ n x = true → s' x = true → a' x = true := by
                intro x h1 h2
                cases hcov x h1 with
                | inl h => exact h
                | inr hb =>
                    have := empty_none hemp2 x
                    rw [show inter (inter (e₀ n) b) s' x = true from
                          andI _ _ (andI _ _ h1 hb) h2] at this
                    cases this
              have d' : Der k₁ (upd e₀ n (inter (e₀ n) s')) Sy :=
                der_congr d (envEq_trans hd
                  (upd_congr (envEq_refl _) n (inter_absorb_mid (e₀ n) a' s' ha)))
              exact der_mono (Der.atom p hneS d') (Nat.le_mul_of_pos_right k₁ (der_pos d₂))
          | inr hd2 =>
              have ⟨hne2, d2'⟩ := hd2
              rw [upd_same] at hne2 d2'
              -- the IH at the environment narrowed by s'
              have he' : EnvEq (upd e n (inter (e n) s'))
                  (upd (upd e₀ n (inter (e₀ n) s')) n (inter (upd e₀ n (inter (e₀ n) s') n) a')) := by
                refine envEq_trans hd ?_
                refine envEq_trans ?_ (envEq_symm (upd_upd_same_inter e₀ n s' a'))
                exact upd_congr (envEq_refl _) n (inter_swap (e₀ n) a' s')
              have d3 : Der k₂ (upd (upd e₀ n (inter (e₀ n) s')) n
                  (inter (upd e₀ n (inter (e₀ n) s') n) b)) Sy := by
                refine der_congr d2' ?_
                refine envEq_trans (upd_twice e₀ n _ _) ?_
                refine envEq_trans ?_ (envEq_symm (upd_upd_same_inter e₀ n s' b))
                exact upd_congr (envEq_refl _) n (inter_swap (e₀ n) b s')
              have hcov' : ∀ x, upd e₀ n (inter (e₀ n) s') n x = true → a' x = true ∨ b x = true := by
                intro x hx; rw [upd_same] at hx; exact hcov x (inter_mem.mp hx).1
              have hne0' : sIsEmpty (upd e₀ n (inter (e₀ n) s') n) = false := by
                rw [upd_same]; exact hneS
              exact Der.atom p hneS (ih he' d3 hcov' hne0')
  | @one e S Sy y ns k₁ p rc d ih =>
      intro k₂ n a' b e₀ he d₂ hcov hne0
      exact Der.one p rc (ih he (inv1 d₂ p rc) hcov hne0)
  | @two e S Sy y n₁ n₂ k₁ k₂ p r₂ d₁ d₂ ih₁ ih₂ =>
      intro k₂' n a' b e₀ he d₃ hcov hne0
      have ⟨a₁, a₂⟩ := inv2 d₃ p r₂
      rw [addMul]
      exact Der.two p r₂ (ih₁ he a₁ hcov hne0) (ih₂ he a₂ hcov hne0)
  | @pad e S k₁ d ih =>
      intro k₂ n a' b e₀ he d₂ hcov hne0
      have d' := ih he d₂ hcov hne0
      exact der_mono d' (by rw [addMul]; exact Nat.le_add_right _ _)

/-! ### The cut, by the rank of its formula — and its bound as a function -/

theorem tT : SignT T = true := by decide
theorem tF : SignT F = false := by decide
theorem fT : SignF T = false := by decide
theorem fF : SignF F = true := by decide
theorem pT : SignP T = true := by decide
theorem pF : SignP F = false := by decide
theorem nT : SignN T = false := by decide
theorem nF : SignN F = true := by decide
theorem covTN : ∀ x : V, SignT x = true ∨ SignN x = true := by decide
theorem covFP : ∀ x : V, SignF x = true ∨ SignP x = true := by decide

/-- The two covering pairs: `T` against `N` ("not T") and `F` against `P`
("not F"). `¬` turns one into the other. -/
def sig1 : Bool → Sign
  | true  => SignT
  | false => SignF
def sig2 : Bool → Sign
  | true  => SignN
  | false => SignP

/-- The rewrites of `→ ⊕ ↔` into the basis `{¬, ∧, ∨}`, as the engine performs them. -/
def basis : Fm → Fm
  | .atom n   => .atom n
  | .top      => .top
  | .bot      => .bot
  | .neg φ    => .neg (basis φ)
  | .conj φ ψ => .conj (basis φ) (basis ψ)
  | .disj φ ψ => .disj (basis φ) (basis ψ)
  | .imp φ ψ  => .disj (.neg (basis φ)) (basis ψ)
  | .xor φ ψ  => .disj (.conj (basis φ) (.neg (basis ψ))) (.conj (.neg (basis φ)) (basis ψ))
  | .xnor φ ψ => .disj (.conj (basis φ) (basis ψ)) (.conj (.neg (basis φ)) (.neg (basis ψ)))

/-- **THE BOUND.** `B0 pol k₁ k₂ φ` is the number of leaves the cut-free
derivation may have after cutting `φ` (on the pair `sig1 pol / sig2 pol`)
between derivations of `k₁` and `k₂` leaves. Read it as the recursion of the
procedure: an atom multiplies; `¬` flips the pair; `∧` and `∨` cut the two
subformulas in turn, the second cut fed by the first — and on the side that
BRANCHES, the whole first result is fed in. The rows for `→ ⊕ ↔` are never
reached: the bound is taken on `basis φ`. -/
def B0 : Bool → Nat → Nat → Fm → Nat
  | true,  k₁, k₂, .atom _ => k₁ * k₂
  | false, k₁, k₂, .atom _ => k₁ * k₂
  | true,  k₁, k₂, .top => k₁ * k₂
  | false, k₁, k₂, .top => k₁ * k₂
  | true,  k₁, k₂, .bot => k₁ * k₂
  | false, k₁, k₂, .bot => k₁ * k₂
  | true,  k₁, k₂, .neg ψ => B0 false k₁ k₂ ψ
  | false, k₁, k₂, .neg ψ => B0 false k₂ k₁ ψ
  | true,  k₁, k₂, .conj ψ χ => B0 true (B0 true k₁ k₂ ψ) k₂ χ
  | false, k₁, k₂, .conj ψ χ => B0 true (B0 true k₂ k₁ ψ) k₁ χ
  | true,  k₁, k₂, .disj ψ χ => B0 true k₁ (B0 true k₁ k₂ ψ) χ
  | false, k₁, k₂, .disj ψ χ => B0 true k₂ (B0 true k₂ k₁ ψ) χ
  | true,  k₁, k₂, .imp _ _ => k₁ * k₂
  | false, k₁, k₂, .imp _ _ => k₁ * k₂
  | true,  k₁, k₂, .xor _ _ => k₁ * k₂
  | false, k₁, k₂, .xor _ _ => k₁ * k₂
  | true,  k₁, k₂, .xnor _ _ => k₁ * k₂
  | false, k₁, k₂, .xnor _ _ => k₁ * k₂

/-- Cut on an atom, for any covering pair of signs. -/
theorem cut_atom {s₁ s₂ : Sign} (hcov : ∀ x, s₁ x = true ∨ s₂ x = true)
    {k₁ k₂ : Nat} {e : Env} {n : Nat} {S : List Node}
    (d₁ : Der k₁ e ((s₁, .atom n) :: S)) (d₂ : Der k₂ e ((s₂, .atom n) :: S))
    (he : ∀ n, sIsEmpty (e n) = false) : Der (k₁ * k₂) e S := by
  cases inv_atom d₁ Pick.here with
  | inl h1 =>
      cases inv_atom d₂ Pick.here with
      | inl h2 =>
          exfalso
          have ⟨x, hx⟩ := nonempty_some (he n)
          cases hcov x with
          | inl hs => have := empty_none h1 x; rw [inter_mem.mpr ⟨hx, hs⟩] at this; cases this
          | inr hs => have := empty_none h2 x; rw [inter_mem.mpr ⟨hx, hs⟩] at this; cases this
      | inr h2 =>
          have habs : ∀ x, e n x = true → s₂ x = true := by
            intro x hx
            cases hcov x with
            | inl hs => have := empty_none h1 x; rw [inter_mem.mpr ⟨hx, hs⟩] at this; cases this
            | inr hs => exact hs
          exact der_mono (der_congr h2.2 (upd_absorb e n s₂ habs))
            (Nat.le_mul_of_pos_left k₂ (der_pos d₁))
  | inr h1 =>
      cases inv_atom d₂ Pick.here with
      | inl h2 =>
          have habs : ∀ x, e n x = true → s₁ x = true := by
            intro x hx
            cases hcov x with
            | inl hs => exact hs
            | inr hs => have := empty_none h2 x; rw [inter_mem.mpr ⟨hx, hs⟩] at this; cases this
          exact der_mono (der_congr h1.2 (upd_absorb e n s₁ habs))
            (Nat.le_mul_of_pos_right k₁ (der_pos d₂))
      | inr h2 => exact cut_env h1.2 (envEq_refl _) h2.2 (fun x _ => hcov x) (he n)

theorem le_pred_succ {a m : Nat} (h : a + 1 ≤ m + 1) : a ≤ m := Nat.le_of_succ_le_succ h
theorem le_of_add2 {a m : Nat} (h : a + 2 ≤ m + 1) : a ≤ m :=
  Nat.le_trans (Nat.le_succ a) (Nat.le_of_succ_le_succ h)
theorem le_of_add3 {a m : Nat} (h : a + 3 ≤ m + 1) : a + 1 ≤ m :=
  Nat.le_trans (Nat.le_succ (a + 1)) (Nat.le_of_succ_le_succ h)

/-- **SYNTACTIC CUT ELIMINATION, WITH ITS BOUND.** For every formula `φ` and
either covering pair: derivations of `S, sig1:φ` with `k₁` leaves and of
`S, sig2:φ` with `k₂` leaves yield a derivation of `S` with at most
`B0 pol k₁ k₂ (basis φ)` leaves. By recursion on the rank of `φ`; every step
is an inversion, a weakening, or a smaller cut — never a model. -/
theorem cutP : ∀ (m : Nat) (pol : Bool) (φ : Fm), Fm.size φ ≤ m →
    ∀ {k₁ k₂ : Nat} {e : Env} {S : List Node},
      Der k₁ e ((sig1 pol, φ) :: S) → Der k₂ e ((sig2 pol, φ) :: S) →
      (∀ n, sIsEmpty (e n) = false) → Der (B0 pol k₁ k₂ (basis φ)) e S
  | _, true,  .atom _, _ => fun d₁ d₂ he => cut_atom covTN d₁ d₂ he
  | _, false, .atom _, _ => fun d₁ d₂ he => cut_atom covFP d₁ d₂ he
  | _, true,  .top, _ => fun d₁ d₂ _ =>
      der_mono (inv1 d₁ Pick.here (RuleC.top tT)) (Nat.le_mul_of_pos_right _ (der_pos d₂))
  | _, false, .top, _ => fun d₁ d₂ _ =>
      der_mono (inv1 d₂ Pick.here (RuleC.top pT)) (Nat.le_mul_of_pos_left _ (der_pos d₁))
  | _, true,  .bot, _ => fun d₁ d₂ _ =>
      der_mono (inv1 d₂ Pick.here (RuleC.bot nF)) (Nat.le_mul_of_pos_left _ (der_pos d₁))
  | _, false, .bot, _ => fun d₁ d₂ _ =>
      der_mono (inv1 d₁ Pick.here (RuleC.bot fF)) (Nat.le_mul_of_pos_right _ (der_pos d₂))
  | 0, _, .neg _, hs => absurd hs (Nat.not_succ_le_zero _)
  | 0, _, .conj _ _, hs => absurd hs (Nat.not_succ_le_zero _)
  | 0, _, .disj _ _, hs => absurd hs (Nat.not_succ_le_zero _)
  | 0, _, .imp _ _, hs => absurd hs (Nat.not_succ_le_zero _)
  | 0, _, .xor _ _, hs => absurd hs (Nat.not_succ_le_zero _)
  | 0, _, .xnor _ _, hs => absurd hs (Nat.not_succ_le_zero _)
  | m + 1, true, .neg ψ, hs => fun d₁ d₂ he =>
      cutP m false ψ (le_pred_succ hs)
        (inv1 d₁ Pick.here (RuleC.negT tT tF)) (inv1 d₂ Pick.here (RuleC.negF nT nF)) he
  | m + 1, false, .neg ψ, hs => fun d₁ d₂ he =>
      cutP m false ψ (le_pred_succ hs)
        (inv1 d₂ Pick.here (RuleC.negT pT pF)) (inv1 d₁ Pick.here (RuleC.negF fT fF)) he
  | m + 1, true, .conj ψ χ, hs => fun d₁ d₂ he => by
      have hm : Fm.size ψ + Fm.size χ ≤ m := le_pred_succ hs
      have hψ : Fm.size ψ ≤ m := Nat.le_trans (Nat.le_add_right _ _) hm
      have hχ : Fm.size χ ≤ m := Nat.le_trans (Nat.le_add_left _ _) hm
      have a := inv1 d₁ Pick.here (RuleC.conjT tT tF)
      have ⟨b₁, b₂⟩ := inv2 d₂ Pick.here (Rule2.conjF nT nF)
      have c := cutP m true ψ hψ a (der_weak b₁ (Ins.there Ins.here)) he
      exact cutP m true χ hχ c b₂ he
  | m + 1, false, .conj ψ χ, hs => fun d₁ d₂ he => by
      have hm : Fm.size ψ + Fm.size χ ≤ m := le_pred_succ hs
      have hψ : Fm.size ψ ≤ m := Nat.le_trans (Nat.le_add_right _ _) hm
      have hχ : Fm.size χ ≤ m := Nat.le_trans (Nat.le_add_left _ _) hm
      have ⟨a₁, a₂⟩ := inv2 d₁ Pick.here (Rule2.conjF fT fF)
      have b := inv1 d₂ Pick.here (RuleC.conjT pT pF)
      have c := cutP m true ψ hψ b (der_weak a₁ (Ins.there Ins.here)) he
      exact cutP m true χ hχ c a₂ he
  | m + 1, true, .disj ψ χ, hs => fun d₁ d₂ he => by
      have hm : Fm.size ψ + Fm.size χ ≤ m := le_pred_succ hs
      have hψ : Fm.size ψ ≤ m := Nat.le_trans (Nat.le_add_right _ _) hm
      have hχ : Fm.size χ ≤ m := Nat.le_trans (Nat.le_add_left _ _) hm
      have ⟨a₁, a₂⟩ := inv2 d₁ Pick.here (Rule2.disjT tT tF)
      have b := inv1 d₂ Pick.here (RuleC.disjF nT nF)
      have c := cutP m true ψ hψ (der_weak a₁ (Ins.there Ins.here)) b he
      exact cutP m true χ hχ a₂ c he
  | m + 1, false, .disj ψ χ, hs => fun d₁ d₂ he => by
      have hm : Fm.size ψ + Fm.size χ ≤ m := le_pred_succ hs
      have hψ : Fm.size ψ ≤ m := Nat.le_trans (Nat.le_add_right _ _) hm
      have hχ : Fm.size χ ≤ m := Nat.le_trans (Nat.le_add_left _ _) hm
      have a := inv1 d₁ Pick.here (RuleC.disjF fT fF)
      have ⟨b₁, b₂⟩ := inv2 d₂ Pick.here (Rule2.disjT pT pF)
      have c := cutP m true ψ hψ (der_weak b₁ (Ins.there Ins.here)) a he
      exact cutP m true χ hχ b₂ c he
  | m + 1, pol, .imp ψ χ, hs => fun d₁ d₂ he =>
      cutP m pol (.disj (.neg ψ) χ) (le_of_add2 hs)
        (inv1 d₁ Pick.here RuleC.imp) (inv1 d₂ Pick.here RuleC.imp) he
  | m + 1, pol, .xor ψ χ, hs => fun d₁ d₂ he =>
      cutP m pol (.disj (.conj ψ (.neg χ)) (.conj (.neg ψ) χ)) (le_of_add3 hs)
        (inv1 d₁ Pick.here RuleC.xor) (inv1 d₂ Pick.here RuleC.xor) he
  | m + 1, pol, .xnor ψ χ, hs => fun d₁ d₂ he =>
      cutP m pol (.disj (.conj ψ χ) (.conj (.neg ψ) (.neg χ))) (le_of_add3 hs)
        (inv1 d₁ Pick.here RuleC.xnor) (inv1 d₂ Pick.here RuleC.xnor) he

/-- The headline form: cut on `T / N`, at the head, with the bound. -/
theorem cut_TN {k₁ k₂ : Nat} {e : Env} {S : List Node} (φ : Fm)
    (d₁ : Der k₁ e ((SignT, φ) :: S)) (d₂ : Der k₂ e ((SignN, φ) :: S))
    (he : ∀ n, sIsEmpty (e n) = false) : Der (B0 true k₁ k₂ (basis φ)) e S :=
  cutP (Fm.size φ) true φ (Nat.le_refl _) d₁ d₂ he

/-- …and on the dual pair `F / P`. -/
theorem cut_FP {k₁ k₂ : Nat} {e : Env} {S : List Node} (φ : Fm)
    (d₁ : Der k₁ e ((SignF, φ) :: S)) (d₂ : Der k₂ e ((SignP, φ) :: S))
    (he : ∀ n, sIsEmpty (e n) = false) : Der (B0 false k₁ k₂ (basis φ)) e S :=
  cutP (Fm.size φ) false φ (Nat.le_refl _) d₁ d₂ he

/-! ### The engine is the special case that always picks the head -/

/-- **EVERY CLOSED RUN OF THE ENGINE IS A DERIVATION** — with `Pick.here` at
every step, since the engine always works on the head. -/
theorem der_of_closes : ∀ (fuel : Nat) (e : Env) (ws : List Node),
    closes fuel e ws = true → ∃ k, Der k e ws := by
  intro fuel
  induction fuel with
  | zero => intro e ws h; exact nomatch h
  | succ fuel ih =>
    intro e ws h
    match ws with
    | [] => exact nomatch h
    | (s, .atom n) :: rest =>
      have h' : (if sIsEmpty (inter (e n) s) = true then true
                 else closes fuel (upd e n (inter (e n) s)) rest) = true := h
      split at h'
      · next hemp => exact ⟨1, Der.ax Pick.here (Ax.atom hemp)⟩
      · next hemp =>
          have ⟨k, d⟩ := ih _ rest h'
          exact ⟨k, Der.atom Pick.here (bNotTrue _ hemp) d⟩
    | (s, .top) :: rest =>
      have h' : (if s T = true then closes fuel e rest else true) = true := h
      split at h'
      · next hT => have ⟨k, d⟩ := ih _ rest h'; exact ⟨k, Der.one Pick.here (RuleC.top hT) d⟩
      · next hT => exact ⟨1, Der.ax Pick.here (Ax.top (bNotTrue _ hT))⟩
    | (s, .bot) :: rest =>
      have h' : (if s F = true then closes fuel e rest else true) = true := h
      split at h'
      · next hF => have ⟨k, d⟩ := ih _ rest h'; exact ⟨k, Der.one Pick.here (RuleC.bot hF) d⟩
      · next hF => exact ⟨1, Der.ax Pick.here (Ax.bot (bNotTrue _ hF))⟩
    | (s, .neg φ) :: rest =>
      have h' : (if s T = true then
                   if s F = true then closes fuel e rest
                   else closes fuel e ((SignF, φ) :: rest)
                 else
                   if s F = true then closes fuel e ((SignP, φ) :: rest)
                   else true) = true := h
      split at h'
      · next hT =>
        split at h'
        · next hF => have ⟨k, d⟩ := ih _ rest h'; exact ⟨k, Der.one Pick.here (RuleC.negDrop hT hF) d⟩
        · next hF => have ⟨k, d⟩ := ih _ _ h'; exact ⟨k, Der.one Pick.here (RuleC.negT hT (bNotTrue _ hF)) d⟩
      · next hT =>
        split at h'
        · next hF => have ⟨k, d⟩ := ih _ _ h'; exact ⟨k, Der.one Pick.here (RuleC.negF (bNotTrue _ hT) hF) d⟩
        · next hF => exact ⟨1, Der.ax Pick.here (Ax.neg (bNotTrue _ hT) (bNotTrue _ hF))⟩
    | (s, .conj φ ψ) :: rest =>
      have h' : (if s T = true then
                   if s F = true then closes fuel e rest
                   else closes fuel e ((SignT, φ) :: (SignT, ψ) :: rest)
                 else
                   if s F = true then
                     closes fuel e ((SignN, φ) :: rest) && closes fuel e ((SignN, ψ) :: rest)
                   else true) = true := h
      split at h'
      · next hT =>
        split at h'
        · next hF => have ⟨k, d⟩ := ih _ rest h'; exact ⟨k, Der.one Pick.here (RuleC.conjDrop hT hF) d⟩
        · next hF => have ⟨k, d⟩ := ih _ _ h'; exact ⟨k, Der.one Pick.here (RuleC.conjT hT (bNotTrue _ hF)) d⟩
      · next hT =>
        split at h'
        · next hF =>
            have ⟨h1, h2⟩ := (andEqTrue _ _).mp h'
            have ⟨k₁, d₁⟩ := ih _ _ h1
            have ⟨k₂, d₂⟩ := ih _ _ h2
            exact ⟨k₁ + k₂, Der.two Pick.here (Rule2.conjF (bNotTrue _ hT) hF) d₁ d₂⟩
        · next hF => exact ⟨1, Der.ax Pick.here (Ax.conj (bNotTrue _ hT) (bNotTrue _ hF))⟩
    | (s, .disj φ ψ) :: rest =>
      have h' : (if s T = true then
                   if s F = true then closes fuel e rest
                   else closes fuel e ((SignT, φ) :: rest) && closes fuel e ((SignT, ψ) :: rest)
                 else
                   if s F = true then closes fuel e ((SignN, φ) :: (SignN, ψ) :: rest)
                   else true) = true := h
      split at h'
      · next hT =>
        split at h'
        · next hF => have ⟨k, d⟩ := ih _ rest h'; exact ⟨k, Der.one Pick.here (RuleC.disjDrop hT hF) d⟩
        · next hF =>
            have ⟨h1, h2⟩ := (andEqTrue _ _).mp h'
            have ⟨k₁, d₁⟩ := ih _ _ h1
            have ⟨k₂, d₂⟩ := ih _ _ h2
            exact ⟨k₁ + k₂, Der.two Pick.here (Rule2.disjT hT (bNotTrue _ hF)) d₁ d₂⟩
      · next hT =>
        split at h'
        · next hF => have ⟨k, d⟩ := ih _ _ h'; exact ⟨k, Der.one Pick.here (RuleC.disjF (bNotTrue _ hT) hF) d⟩
        · next hF => exact ⟨1, Der.ax Pick.here (Ax.disj (bNotTrue _ hT) (bNotTrue _ hF))⟩
    | (s, .imp φ ψ) :: rest =>
      have h' : closes fuel e ((s, .disj (.neg φ) ψ) :: rest) = true := h
      have ⟨k, d⟩ := ih _ _ h'
      exact ⟨k, Der.one Pick.here RuleC.imp d⟩
    | (s, .xor φ ψ) :: rest =>
      have h' : closes fuel e ((s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) :: rest) = true := h
      have ⟨k, d⟩ := ih _ _ h'
      exact ⟨k, Der.one Pick.here RuleC.xor d⟩
    | (s, .xnor φ ψ) :: rest =>
      have h' : closes fuel e ((s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) :: rest) = true := h
      have ⟨k, d⟩ := ih _ _ h'
      exact ⟨k, Der.one Pick.here RuleC.xnor d⟩

/-! ### Soundness of the calculus — the one place a model appears, and only
to connect back to the engine -/

theorem satL_pick (v : Nat → V) : ∀ {S : List Node} {x : Node} {S' : List Node},
    Pick S x S' → (satL v S ↔ (satN v x ∧ satL v S'))
  | _, _, _, Pick.here => Iff.rfl
  | _, _, _, @Pick.there x y l l' p => by
      show (satN v y ∧ satL v l) ↔ (satN v x ∧ (satN v y ∧ satL v l'))
      constructor
      · intro ⟨hy, hl⟩
        have ⟨hx, hl'⟩ := (satL_pick v p).mp hl
        exact ⟨hx, hy, hl'⟩
      · intro ⟨hx, hy, hl'⟩
        exact ⟨hy, (satL_pick v p).mpr ⟨hx, hl'⟩⟩

theorem SAT_pick {e : Env} {S : List Node} {x : Node} {S' : List Node} (p : Pick S x S') :
    SAT e S ↔ SAT e (x :: S') :=
  ⟨fun ⟨v, hOK, hs⟩ => ⟨v, hOK, (satL_pick v p).mp hs⟩,
   fun ⟨v, hOK, hs⟩ => ⟨v, hOK, (satL_pick v p).mpr hs⟩⟩

/-- **A DERIVATION HAS NO MODEL.** -/
theorem sound : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S → SAT e S → False := by
  intro k e S d
  induction d with
  | @ax e S S' x p a =>
      intro hS
      have hS' := (SAT_pick p).mp hS
      cases a with
      | @atom s n hemp =>
          have ⟨v, hOK, h1, _⟩ := hS'
          have hmem : inter (e n) s (v n) = true := (andEqTrue _ _).mpr ⟨hOK n, h1⟩
          have := sNonempty_of_mem hmem
          rw [hemp] at this
          cases this
      | @top s hT =>
          have hno : ∀ v, ¬ satN v (s, Fm.top) := fun _ h1 => by
            have h1' : s T = true := h1
            rw [hT] at h1'; cases h1'
          exact SAT_head_false hno hS'
      | @bot s hF =>
          have hno : ∀ v, ¬ satN v (s, Fm.bot) := fun _ h1 => by
            have h1' : s F = true := h1
            rw [hF] at h1'; cases h1'
          exact SAT_head_false hno hS'
      | @neg s φ hT hF =>
          have hcls : ∀ v, znot (evalF v φ) = T ∨ znot (evalF v φ) = F := fun v => lift1_classical _ _
          have hno : ∀ v, ¬ satN v (s, .neg φ) := fun v => not_mem_cls (hcls v) hT hF
          exact SAT_head_false hno hS'
      | @conj s φ ψ hT hF =>
          have hcls : ∀ v, zand (evalF v φ) (evalF v ψ) = T ∨ zand (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hno : ∀ v, ¬ satN v (s, .conj φ ψ) := fun v => not_mem_cls (hcls v) hT hF
          exact SAT_head_false hno hS'
      | @disj s φ ψ hT hF =>
          have hcls : ∀ v, zor (evalF v φ) (evalF v ψ) = T ∨ zor (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hno : ∀ v, ¬ satN v (s, .disj φ ψ) := fun v => not_mem_cls (hcls v) hT hF
          exact SAT_head_false hno hS'
  | @atom e S S' s n k p hne d ih =>
      intro hS
      exact ih (SAT_atom.mp ((SAT_pick p).mp hS))
  | @one e S S' x ns k p r d ih =>
      intro hS
      have hS' := (SAT_pick p).mp hS
      cases r with
      | @top s hT =>
          have hh : ∀ v, satN v (s, Fm.top) := fun _ => hT
          exact ih ((SAT_head_true hh).mp hS')
      | @bot s hF =>
          have hh : ∀ v, satN v (s, Fm.bot) := fun _ => hF
          exact ih ((SAT_head_true hh).mp hS')
      | @negDrop s φ hT hF =>
          have hcls : ∀ v, znot (evalF v φ) = T ∨ znot (evalF v φ) = F := fun v => lift1_classical _ _
          have hh : ∀ v, satN v (s, .neg φ) := fun v => mem_cls_both (hcls v) hT hF
          exact ih ((SAT_head_true hh).mp hS')
      | @negT s φ hT hF =>
          have hcls : ∀ v, znot (evalF v φ) = T ∨ znot (evalF v φ) = F := fun v => lift1_classical _ _
          have hpt : ∀ v, satN v (s, .neg φ) ↔ satN v (SignF, φ) := fun v =>
            (mem_cls_T (hcls v) hT hF).trans ((cover_not_T _).trans (vF _).symm)
          exact ih ((SAT_head_congr hpt).mp hS')
      | @negF s φ hT hF =>
          have hcls : ∀ v, znot (evalF v φ) = T ∨ znot (evalF v φ) = F := fun v => lift1_classical _ _
          have hpt : ∀ v, satN v (s, .neg φ) ↔ satN v (SignP, φ) := fun v =>
            (mem_cls_F (hcls v) hT hF).trans ((cover_not_F _).trans (vP _).symm)
          exact ih ((SAT_head_congr hpt).mp hS')
      | @conjDrop s φ ψ hT hF =>
          have hcls : ∀ v, zand (evalF v φ) (evalF v ψ) = T ∨ zand (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hh : ∀ v, satN v (s, .conj φ ψ) := fun v => mem_cls_both (hcls v) hT hF
          exact ih ((SAT_head_true hh).mp hS')
      | @conjT s φ ψ hT hF =>
          have hcls : ∀ v, zand (evalF v φ) (evalF v ψ) = T ∨ zand (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hpt : ∀ v, satN v (s, .conj φ ψ) ↔ (satN v (SignT, φ) ∧ satN v (SignT, ψ)) := fun v =>
            (mem_cls_T (hcls v) hT hF).trans ((cover_and_T _ _).trans (andCongr (vT _).symm (vT _).symm))
          exact ih ((SAT_head_split2 hpt).mp hS')
      | @disjDrop s φ ψ hT hF =>
          have hcls : ∀ v, zor (evalF v φ) (evalF v ψ) = T ∨ zor (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hh : ∀ v, satN v (s, .disj φ ψ) := fun v => mem_cls_both (hcls v) hT hF
          exact ih ((SAT_head_true hh).mp hS')
      | @disjF s φ ψ hT hF =>
          have hcls : ∀ v, zor (evalF v φ) (evalF v ψ) = T ∨ zor (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hpt : ∀ v, satN v (s, .disj φ ψ) ↔ (satN v (SignN, φ) ∧ satN v (SignN, ψ)) := fun v =>
            (mem_cls_F (hcls v) hT hF).trans ((cover_or_F _ _).trans (andCongr (vN _).symm (vN _).symm))
          exact ih ((SAT_head_split2 hpt).mp hS')
      | @imp s φ ψ =>
          have hpt : ∀ v, satN v (s, .imp φ ψ) ↔ satN v (s, .disj (.neg φ) ψ) := fun v =>
            iffOfEq (congrArg (fun x => s x = true) (imp_def (evalF v φ) (evalF v ψ)))
          exact ih ((SAT_head_congr hpt).mp hS')
      | @xor s φ ψ =>
          have hpt : ∀ v, satN v (s, .xor φ ψ) ↔
              satN v (s, .disj (.conj φ (.neg ψ)) (.conj (.neg φ) ψ)) := fun v =>
            iffOfEq (congrArg (fun x => s x = true) (xor_def (evalF v φ) (evalF v ψ)))
          exact ih ((SAT_head_congr hpt).mp hS')
      | @xnor s φ ψ =>
          have hpt : ∀ v, satN v (s, .xnor φ ψ) ↔
              satN v (s, .disj (.conj φ ψ) (.conj (.neg φ) (.neg ψ))) := fun v =>
            iffOfEq (congrArg (fun x => s x = true) (xnor_def (evalF v φ) (evalF v ψ)))
          exact ih ((SAT_head_congr hpt).mp hS')
  | @two e S S' x n₁ n₂ k₁ k₂ p r d₁ d₂ ih₁ ih₂ =>
      intro hS
      have hS' := (SAT_pick p).mp hS
      cases r with
      | @conjF s φ ψ hT hF =>
          have hcls : ∀ v, zand (evalF v φ) (evalF v ψ) = T ∨ zand (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hpt : ∀ v, satN v (s, .conj φ ψ) ↔ (satN v (SignN, φ) ∨ satN v (SignN, ψ)) := fun v =>
            (mem_cls_F (hcls v) hT hF).trans ((cover_and_F _ _).trans (orCongr (vN _).symm (vN _).symm))
          cases (SAT_head_or hpt).mp hS' with
          | inl h1 => exact ih₁ h1
          | inr h2 => exact ih₂ h2
      | @disjT s φ ψ hT hF =>
          have hcls : ∀ v, zor (evalF v φ) (evalF v ψ) = T ∨ zor (evalF v φ) (evalF v ψ) = F :=
            fun v => lift2_classical _ _ _
          have hpt : ∀ v, satN v (s, .disj φ ψ) ↔ (satN v (SignT, φ) ∨ satN v (SignT, ψ)) := fun v =>
            (mem_cls_T (hcls v) hT hF).trans ((cover_or_T _ _).trans (orCongr (vT _).symm (vT _).symm))
          cases (SAT_head_or hpt).mp hS' with
          | inl h1 => exact ih₁ h1
          | inr h2 => exact ih₂ h2
  | pad _ ih => intro hS; exact ih hS

/-- Back to the engine, through completeness. -/
theorem closes_of_der {k : Nat} {e : Env} {S : List Node} (d : Der k e S)
    (he : ∀ n, sIsEmpty (e n) = false) : closes (wsize S + 1) e S = true :=
  (closes_iff _ e S (Nat.lt_succ_self _) he).mpr (fun h => sound d h)

/-- **THE PROCEDURE COVERS THE ENGINE.** Two closed runs with the cut formula in
front give derivations `k₁`, `k₂`; the procedure produces one of `S` with at
most `B0 true k₁ k₂ (basis φ)` leaves; and it closes in the engine. -/
theorem cut_closes_with_bound (e : Env) (S : List Node) (φ : Fm)
    (he : ∀ n, sIsEmpty (e n) = false)
    (h1 : closes (wsize ((SignT, φ) :: S) + 1) e ((SignT, φ) :: S) = true)
    (h2 : closes (wsize ((SignN, φ) :: S) + 1) e ((SignN, φ) :: S) = true) :
    ∃ k₁ k₂, Der k₁ e ((SignT, φ) :: S) ∧ Der k₂ e ((SignN, φ) :: S) ∧
      Der (B0 true k₁ k₂ (basis φ)) e S ∧ closes (wsize S + 1) e S = true := by
  have ⟨k₁, d₁⟩ := der_of_closes _ e _ h1
  have ⟨k₂, d₂⟩ := der_of_closes _ e _ h2
  have d := cut_TN φ d₁ d₂ he
  exact ⟨k₁, k₂, d₁, d₂, d, closes_of_der d he⟩

/-! ### The classical cut, T against F: refused on atoms, granted on compounds -/

/-- Replace one occurrence of a node. -/
inductive Swap : Node → Node → List Node → List Node → Prop
  | here  {x y : Node} {l : List Node} : Swap x y (x :: l) (y :: l)
  | there {x y z : Node} {l l' : List Node} : Swap x y l l' → Swap x y (z :: l) (z :: l')

theorem swap_pick : ∀ {x y : Node} {S S₂ : List Node}, Swap x y S S₂ →
    ∀ {z : Node} {Sz : List Node}, Pick S z Sz →
      (z = x ∧ Pick S₂ y Sz) ∨ ∃ S₂', Pick S₂ z S₂' ∧ Swap x y Sz S₂'
  | _, _, _, _, Swap.here, _, _, Pick.here => Or.inl ⟨rfl, Pick.here⟩
  | _, _, _, _, Swap.here, _, _, Pick.there p => Or.inr ⟨_, Pick.there p, Swap.here⟩
  | _, _, _, _, Swap.there sw, _, _, Pick.here => Or.inr ⟨_, Pick.here, sw⟩
  | _, _, _, _, Swap.there sw, _, _, Pick.there p => by
      cases swap_pick sw p with
      | inl h => exact Or.inl ⟨h.1, Pick.there h.2⟩
      | inr h =>
          have ⟨S₂', p', sw'⟩ := h
          exact Or.inr ⟨_, Pick.there p', Swap.there sw'⟩

theorem swap_append (ns : List Node) : ∀ {x y : Node} {l l' : List Node},
    Swap x y l l' → Swap x y (ns ++ l) (ns ++ l')
  | _, _, _, _, sw => by
      induction ns with
      | nil => exact sw
      | cons _ _ ih => exact Swap.there ih

/-- The two bits a compound reads off its sign. -/
def BitsEq (s s' : Sign) : Prop := s T = s' T ∧ s F = s' F

def notAtom : Fm → Bool
  | .atom _ => false
  | .top => true
  | .bot => true
  | .neg _ => true
  | .conj _ _ => true
  | .disj _ _ => true
  | .imp _ _ => true
  | .xor _ _ => true
  | .xnor _ _ => true

theorem ax_swap {e : Env} {s s' : Sign} {φ : Fm} (hφ : notAtom φ = true) (hb : BitsEq s s')
    (a : Ax e (s, φ)) : Ax e (s', φ) := by
  cases a with
  | atom _ => cases hφ
  | top h => exact Ax.top (hb.1 ▸ h)
  | bot h => exact Ax.bot (hb.2 ▸ h)
  | neg h1 h2 => exact Ax.neg (hb.1 ▸ h1) (hb.2 ▸ h2)
  | conj h1 h2 => exact Ax.conj (hb.1 ▸ h1) (hb.2 ▸ h2)
  | disj h1 h2 => exact Ax.disj (hb.1 ▸ h1) (hb.2 ▸ h2)

/-- A one-premise rule survives the swap; the rewrites carry the sign into
their premise, which is why the induction below must swap there too. -/
theorem ruleC_swap {s s' : Sign} {φ : Fm} {ns : List Node} (hb : BitsEq s s')
    (r : RuleC (s, φ) ns) :
    RuleC (s', φ) ns ∨ ∃ ρ, ns = [(s, ρ)] ∧ RuleC (s', φ) [(s', ρ)] ∧ notAtom ρ = true := by
  cases r with
  | top h => exact Or.inl (RuleC.top (hb.1 ▸ h))
  | bot h => exact Or.inl (RuleC.bot (hb.2 ▸ h))
  | negDrop h1 h2 => exact Or.inl (RuleC.negDrop (hb.1 ▸ h1) (hb.2 ▸ h2))
  | negT h1 h2 => exact Or.inl (RuleC.negT (hb.1 ▸ h1) (hb.2 ▸ h2))
  | negF h1 h2 => exact Or.inl (RuleC.negF (hb.1 ▸ h1) (hb.2 ▸ h2))
  | conjDrop h1 h2 => exact Or.inl (RuleC.conjDrop (hb.1 ▸ h1) (hb.2 ▸ h2))
  | conjT h1 h2 => exact Or.inl (RuleC.conjT (hb.1 ▸ h1) (hb.2 ▸ h2))
  | disjDrop h1 h2 => exact Or.inl (RuleC.disjDrop (hb.1 ▸ h1) (hb.2 ▸ h2))
  | disjF h1 h2 => exact Or.inl (RuleC.disjF (hb.1 ▸ h1) (hb.2 ▸ h2))
  | imp => exact Or.inr ⟨_, rfl, RuleC.imp, rfl⟩
  | xor => exact Or.inr ⟨_, rfl, RuleC.xor, rfl⟩
  | xnor => exact Or.inr ⟨_, rfl, RuleC.xnor, rfl⟩

theorem rule2_swap {s s' : Sign} {φ : Fm} {n₁ n₂ : List Node} (hb : BitsEq s s')
    (r : Rule2 (s, φ) n₁ n₂) : Rule2 (s', φ) n₁ n₂ := by
  cases r with
  | conjF h1 h2 => exact Rule2.conjF (hb.1 ▸ h1) (hb.2 ▸ h2)
  | disjT h1 h2 => exact Rule2.disjT (hb.1 ▸ h1) (hb.2 ▸ h2)

/-- **ON A COMPOUND, A SIGN IS ITS TWO BITS.** Swapping a sign for one with
the same bits, on any non-atom node anywhere, keeps the derivation and its
size. This is the greediness theorem seen from the calculus: a compound is
never Z, so `F` and `N` ("not T") cannot be told apart on it, nor `T` and `P`. -/
theorem der_swap : ∀ {k : Nat} {e : Env} {S : List Node}, Der k e S →
    ∀ {s s' : Sign} {φ : Fm} {S₂ : List Node}, notAtom φ = true → BitsEq s s' →
      Swap (s, φ) (s', φ) S S₂ → Der k e S₂ := by
  intro k e S d
  induction d with
  | @ax e S S' x p a =>
      intro s s' φ S₂ hφ hb sw
      cases swap_pick sw p with
      | inl h => rw [h.1] at a; exact Der.ax h.2 (ax_swap hφ hb a)
      | inr h => have ⟨_, p', _⟩ := h; exact Der.ax p' a
  | @atom e S S' s₀ n k p hne d ih =>
      intro s s' φ S₂ hφ hb sw
      cases swap_pick sw p with
      | inl h =>
          have : φ = .atom n := (congrArg Prod.snd h.1).symm
          rw [this] at hφ; cases hφ
      | inr h =>
          have ⟨S₂', p', sw'⟩ := h
          exact Der.atom p' hne (ih hφ hb sw')
  | @one e S S' x ns k p r d ih =>
      intro s s' φ S₂ hφ hb sw
      cases swap_pick sw p with
      | inl h =>
          rw [h.1] at r
          cases ruleC_swap hb r with
          | inl r' => exact Der.one h.2 r' d
          | inr hr =>
              have ⟨ρ, hns, r', hρ⟩ := hr
              subst hns
              exact Der.one h.2 r' (ih hρ hb Swap.here)
      | inr h =>
          have ⟨S₂', p', sw'⟩ := h
          exact Der.one p' r (ih hφ hb (swap_append ns sw'))
  | @two e S S' x n₁ n₂ k₁ k₂ p r d₁ d₂ ih₁ ih₂ =>
      intro s s' φ S₂ hφ hb sw
      cases swap_pick sw p with
      | inl h =>
          rw [h.1] at r
          exact Der.two h.2 (rule2_swap hb r) d₁ d₂
      | inr h =>
          have ⟨S₂', p', sw'⟩ := h
          exact Der.two p' r (ih₁ hφ hb (swap_append n₁ sw')) (ih₂ hφ hb (swap_append n₂ sw'))
  | pad _ ih => intro s s' φ S₂ hφ hb sw; exact Der.pad (ih hφ hb sw)

theorem bits_F_N : BitsEq SignF SignN := ⟨by decide, by decide⟩

/-- **THE CLASSICAL CUT IS GRANTED ON COMPOUNDS**: `T` against `F` cuts any
non-atom, with the same bound — because on a compound `F` is `N`. -/
theorem tf_cut_compound {k₁ k₂ : Nat} {e : Env} {S : List Node} (φ : Fm) (hφ : notAtom φ = true)
    (d₁ : Der k₁ e ((SignT, φ) :: S)) (d₂ : Der k₂ e ((SignF, φ) :: S))
    (he : ∀ n, sIsEmpty (e n) = false) : Der (B0 true k₁ k₂ (basis φ)) e S :=
  cut_TN φ d₁ (der_swap d₂ hφ bits_F_N Swap.here) he

/-- **…AND REFUSED ON ATOMS.** `S = {N:p, P:p}` — "p not T" and "p not F" — is
open: `p = Z` satisfies it. Yet `S, T:p` closes (T against N) and `S, F:p`
closes (F against P). The classical cut on `p` would close `S`, and there is
no such derivation: Z escapes exactly where the mark lives. -/
theorem tf_cut_fails_on_atoms :
    Der 1 e0 ((SignT, .atom 0) :: [(SignN, .atom 0), (SignP, .atom 0)]) ∧
    Der 1 e0 ((SignF, .atom 0) :: [(SignN, .atom 0), (SignP, .atom 0)]) ∧
    ¬ ∃ k, Der k e0 [(SignN, .atom 0), (SignP, .atom 0)] := by
  refine ⟨?_, ?_, ?_⟩
  · exact Der.atom Pick.here (by decide) (Der.ax Pick.here (Ax.atom (by decide)))
  · exact Der.atom Pick.here (by decide) (Der.ax (Pick.there Pick.here) (Ax.atom (by decide)))
  · intro ⟨k, d⟩
    exact sound d ⟨fun _ => Z, fun _ => rfl,
      (by show SignN Z = true; decide), (by show SignP Z = true; decide), trivial⟩

/-! ### The bound, computed: three shapes, `k₁ = k₂ = 2` -/

/-- A chain of `∨`: each level multiplies by `k₁`. -/
theorem bound_or_chain :
    B0 true 2 2 (basis (.disj (.disj (.disj (.atom 0) (.atom 1)) (.atom 2)) (.atom 3))) = 32 := by
  decide
/-- A chain of `∧`: each level multiplies by `k₂`. -/
theorem bound_and_chain :
    B0 true 2 2 (basis (.conj (.conj (.conj (.atom 0) (.atom 1)) (.atom 2)) (.atom 3))) = 32 := by
  decide
/-- `¬` costs nothing: it flips the pair. -/
theorem bound_neg : B0 true 2 3 (basis (.neg (.neg (.atom 0)))) = 6 := by decide
/-- `→` is its rewrite. -/
theorem bound_imp : B0 true 2 2 (basis (.imp (.atom 0) (.atom 1))) = 8 := by decide

end ZCut



#print axioms ZCut.pick_pick
#print axioms ZCut.perm_pick
#print axioms ZCut.perm_append_comm
#print axioms ZCut.upd_comm
#print axioms ZCut.der_congr
#print axioms ZCut.der_refine
#print axioms ZCut.der_weak
#print axioms ZCut.der_perm
#print axioms ZCut.inv1
#print axioms ZCut.inv2
#print axioms ZCut.inv_atom
#print axioms ZCut.cut_env
#print axioms ZCut.cut_atom
#print axioms ZCut.cutP
#print axioms ZCut.cut_TN
#print axioms ZCut.cut_FP
#print axioms ZCut.der_of_closes
#print axioms ZCut.sound
#print axioms ZCut.closes_of_der
#print axioms ZCut.cut_closes_with_bound
#print axioms ZCut.der_swap
#print axioms ZCut.tf_cut_compound
#print axioms ZCut.tf_cut_fails_on_atoms
#print axioms ZCut.bound_or_chain
#print axioms ZCut.bound_and_chain
#print axioms ZCut.bound_neg
#print axioms ZCut.bound_imp
