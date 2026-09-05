/-
  ZParamEngine.lean — E48: THE SEARCH, AND THE LAYER IT NEEDED.

  E47 stopped at a design fact: a search must DECIDE closure, but a sign in
  this development is a function `V → Bool`, and functions cannot be compared.
  This file builds the layer that was missing and then the search on top of it.

  THE LAYER. A node carries a TAG — one of four constructors `t f p n` — and
  a translation `tagSign` sends each tag to the sign it names (T, F, P =
  "not F", N = "not T"). Formulas get decidable equality (`deriving`,
  measured: no axioms). With both, `closedB` decides whether a branch carries
  two clashing tags on one formula, and `closedB_sound` says a branch it calls
  closed IS closed in the sense of `ZParamClosure` — so it has no model.

  THE FOUR TAGS ARE NOT FOUR VALUES. ZTL is two-valued with a mark
  (`ZTL-TABLES.txt`): verdicts are T or F, and Z is the operand's mark that a
  connective collapses to F when made to answer. A tag speaks about which
  VERDICTS a node admits — `n` is "the value is not T", i.e. F or the still
  unanswered Z — and P and N do not clash precisely because both admit the
  mark. The clash table `clashTag` has three pairs: T/F, T/N, F/P.

  THE SEARCH. `search fuel worklist` takes the first branch: if it is closed,
  the branch is discharged; otherwise the first node with an applicable rule
  that adds something new is expanded and its successors go back on the list.
  Fuel bounds the recursion, and running out claims nothing (§6: FO-ZTL is
  undecidable, so a terminating search must be allowed to give up).

  WHICH RULES THE SEARCH APPLIES — exactly those proved sound on the empty
  axiom list, and no other. The eight propositional steps of `ZParamProp`,
  γ on T:∀ and F:∃, δ on T:∃ (`ZParamTableau`). F:∀ — the fourth quantifier
  rule, the one that needs `¬∀ → ∃¬` — is DELIBERATELY ABSENT: `expandF` maps
  `QFm.all` to `none`. So the search cannot prove the fallen bridge, and the
  last example below shows it declining to.

  E51, THE SAME DAY. Atoms take any number of places (`atom : Nat → List
  Trm`; `trmVals_fresh` and `trmVals_inst` carry the two load-bearing lemmas
  over argument lists), and the search gets the two rules the first version
  lacked: in the greedy register EVERY COMPOUND ANSWERS T OR F
  (`compound_two_valued` — `evalF_classical` for the parameter language), so
  N on a compound is promoted to F and P to T; only atoms keep a weak sign.
  Before that a compound CONCLUSION had no rule and `P(c) ⊢ P(c) ∨ Q(c)` was
  `stuck`. Two repairs found by the kernel runs, not by reading: γ's
  candidates are the parameters IN PLAY (a bound that grew with the branch
  made γ spawn instances forever), and δ fires ONCE (it re-fired with a fresh
  parameter every round). The valid quantifier swap ∃x∀y R ⊢ ∀y∃x R now
  returns `stuck` for the honest reason: its conclusion N:∀ promotes to F:∀,
  the one rule this search does not have.

  WHAT IS PROVED. `search_sound`: if the search reports every branch closed,
  no branch on the initial list has a model — for every parameter assignment,
  under totality of the interpretation. And on top of it the end-to-end
  statement `entails_of_closed`: a closed run on Γ ⊢ φ (premises tagged t,
  conclusion tagged n) is a proof that every total model making each premise
  T makes φ T. Constructive: the conclusion's value is PRODUCED by totality
  and shown to be T, not obtained by refuting its negation.

  WHAT IS NOT PROVED. Completeness — that a valid sequent's search closes for
  some fuel. §6 argues it by Hintikka saturation and the paper says so.

  FORM. Bool splits are `decide`d lemmas; `Bool.or_eq_true`, `List.mem_cons`,
  `Nat.le_max_left` carry propext (measured 2026-09-05) and are not used. The
  fresh parameter is a SUM of parameter indices, not a max, so no max lemma is
  needed. List membership lemmas are written out. Fresh-parameter freshness
  is a theorem (`freshFor_fresh`), not an assumption.
-/
import ZParamSearch

namespace ZParamEngine

open V
open ZParamSyntax
open ZParamTableau
open ZParamProp
open ZParamClosure
open ZParamSearch

variable {α : Type}

/-! ### Bool splits, each `decide`d -/

theorem orT : ∀ a b : Bool, (a || b) = true → a = true ∨ b = true := by decide
theorem andT : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by decide
theorem orF : ∀ a b : Bool, a = false → b = false → (a || b) = false := by decide
theorem notT : ∀ a : Bool, ¬ a = true → a = false := by decide

/-! ### Tags -/

inductive Tag where
  | t | f | p | n
  deriving DecidableEq, Repr

/-- Enumeration of the four tags is decidable — the `decide` below lives on this. -/
instance (p : Tag → Prop) [DecidablePred p] : Decidable (∀ x : Tag, p x) :=
  decidable_of_iff (p Tag.t ∧ p Tag.f ∧ p Tag.p ∧ p Tag.n)
    ⟨fun ⟨a, b, c, d⟩ x => match x with
        | Tag.t => a | Tag.f => b | Tag.p => c | Tag.n => d,
     fun h => ⟨h Tag.t, h Tag.f, h Tag.p, h Tag.n⟩⟩

def tagSign : Tag → Sign
  | Tag.t => SignT
  | Tag.f => SignF
  | Tag.p => SignP
  | Tag.n => SignN

/-- The three clashing pairs, both ways. P and N both admit the mark Z. -/
def clashTag : Tag → Tag → Bool
  | Tag.t, Tag.t => false | Tag.t, Tag.f => true  | Tag.t, Tag.p => false | Tag.t, Tag.n => true
  | Tag.f, Tag.t => true  | Tag.f, Tag.f => false | Tag.f, Tag.p => true  | Tag.f, Tag.n => false
  | Tag.p, Tag.t => false | Tag.p, Tag.f => true  | Tag.p, Tag.p => false | Tag.p, Tag.n => false
  | Tag.n, Tag.t => true  | Tag.n, Tag.f => false | Tag.n, Tag.p => false | Tag.n, Tag.n => false

/-- **A clashing pair of tags is a clashing pair of signs** — `clash` of
`ZParamClosure`, written out so that `decide` can see it. -/
theorem clashTag_sound : ∀ a b : Tag, clashTag a b = true →
    ∀ v : V, ¬(tagSign a v = true ∧ tagSign b v = true) := by decide

/-! ### Decidable equality on the syntax -/

deriving instance DecidableEq for Trm
deriving instance DecidableEq for QFm

abbrev TNode := Tag × QFm
abbrev TBranch := List TNode

def toNode (nd : TNode) : QNode := (tagSign nd.1, nd.2)

def toBranch : TBranch → Branch
  | [] => []
  | nd :: r => toNode nd :: toBranch r

theorem mem_toBranch {nd : TNode} : ∀ {b : TBranch}, nd ∈ b → toNode nd ∈ toBranch b
  | x :: r, h => by
      cases h with
      | head => exact List.Mem.head (toBranch r)
      | tail _ h' => exact List.Mem.tail (toNode x) (mem_toBranch h')

theorem mem_toBranch_inv : ∀ {b : TBranch} {x : QNode}, x ∈ toBranch b →
    ∃ nd, nd ∈ b ∧ x = toNode nd
  | [], _, h => nomatch h
  | nd :: r, x, h => by
      cases h with
      | head => exact ⟨nd, List.Mem.head r, rfl⟩
      | tail _ h' =>
          have ⟨y, hy, he⟩ := mem_toBranch_inv h'
          exact ⟨y, List.Mem.tail nd hy, he⟩

def memB (nd : TNode) : TBranch → Bool
  | [] => false
  | x :: r => decide (nd = x) || memB nd r

/-! ### Decidable closure -/

def clashesWith (nd : TNode) : TBranch → Bool
  | [] => false
  | x :: r => (clashTag nd.1 x.1 && decide (nd.2 = x.2)) || clashesWith nd r

def closedB : TBranch → Bool
  | [] => false
  | nd :: r => clashesWith nd r || closedB r

theorem clashesWith_sound (nd : TNode) : ∀ (r : TBranch), clashesWith nd r = true →
    ∃ x, x ∈ r ∧ clashTag nd.1 x.1 = true ∧ nd.2 = x.2
  | [], h => Bool.noConfusion h
  | x :: r, h => by
      cases orT _ _ h with
      | inl h1 =>
          have ⟨hc, he⟩ := andT _ _ h1
          exact ⟨x, List.Mem.head r, hc, of_decide_eq_true he⟩
      | inr h2 =>
          have ⟨y, hy, hc, he⟩ := clashesWith_sound nd r h2
          exact ⟨y, List.Mem.tail x hy, hc, he⟩

/-- **WHAT `closedB` CALLS CLOSED IS CLOSED** — and so, by `closed_unsat`, has
no model. -/
theorem closedB_sound : ∀ (b : TBranch), closedB b = true → Closed (toBranch b)
  | [], h => Bool.noConfusion h
  | nd :: r, h => by
      cases orT _ _ h with
      | inl h1 =>
          have ⟨x, hx, hc, he⟩ := clashesWith_sound nd r h1
          refine ⟨tagSign nd.1, tagSign x.1, nd.2, List.Mem.head _, ?_, clashTag_sound _ _ hc⟩
          rw [he]
          exact List.Mem.tail _ (mem_toBranch hx)
      | inr h2 =>
          have ⟨s, t, φ, hs, ht, hc⟩ := closedB_sound r h2
          exact ⟨s, t, φ, List.Mem.tail _ hs, List.Mem.tail _ ht, hc⟩

/-! ### The fresh parameter — a sum, so that it is provably fresh -/

def parBoundT : Trm → Nat
  | Trm.bvar _ => 0
  | Trm.par p  => p + 1

def parBoundL : List Trm → Nat
  | []     => 0
  | t :: r => parBoundT t + parBoundL r

def parBound : QFm → Nat
  | QFm.atom _ ts => parBoundL ts
  | QFm.neg φ    => parBound φ
  | QFm.conj φ ψ => parBound φ + parBound ψ
  | QFm.disj φ ψ => parBound φ + parBound ψ
  | QFm.imp φ ψ  => parBound φ + parBound ψ
  | QFm.all φ    => parBound φ
  | QFm.ex φ     => parBound φ

def parBoundB : TBranch → Nat
  | [] => 0
  | nd :: r => parBound nd.2 + parBoundB r

theorem le_of_add_le_left {a b c : Nat} (h : a + b ≤ c) : a ≤ c :=
  Nat.le_trans (Nat.le_add_right a b) h
theorem le_of_add_le_right {a b c : Nat} (h : a + b ≤ c) : b ≤ c :=
  Nat.le_trans (Nat.le_add_left b a) h

theorem occursT_bound (c : Nat) : ∀ t : Trm, parBoundT t ≤ c → occursT c t = false
  | Trm.bvar _, _ => rfl
  | Trm.par p, h => by
      show Nat.beq p c = false
      apply notT
      intro hb
      have hpc : p = c := Nat.eq_of_beq_eq_true hb
      rw [hpc] at h
      exact Nat.lt_irrefl c h

theorem occursL_bound (c : Nat) : ∀ ts : List Trm, parBoundL ts ≤ c → occursL c ts = false
  | [], _ => rfl
  | t :: r, h => by
      show (occursT c t || occursL c r) = false
      exact orF _ _ (occursT_bound c t (le_of_add_le_left h)) (occursL_bound c r (le_of_add_le_right h))

theorem occurs_bound (c : Nat) : ∀ φ : QFm, parBound φ ≤ c → occurs c φ = false
  | QFm.atom _ ts, h => occursL_bound c ts h
  | QFm.neg φ, h => occurs_bound c φ h
  | QFm.conj φ ψ, h => by
      show (occurs c φ || occurs c ψ) = false
      exact orF _ _ (occurs_bound c φ (le_of_add_le_left h)) (occurs_bound c ψ (le_of_add_le_right h))
  | QFm.disj φ ψ, h => by
      show (occurs c φ || occurs c ψ) = false
      exact orF _ _ (occurs_bound c φ (le_of_add_le_left h)) (occurs_bound c ψ (le_of_add_le_right h))
  | QFm.imp φ ψ, h => by
      show (occurs c φ || occurs c ψ) = false
      exact orF _ _ (occurs_bound c φ (le_of_add_le_left h)) (occurs_bound c ψ (le_of_add_le_right h))
  | QFm.all φ, h => occurs_bound c φ h
  | QFm.ex φ, h => occurs_bound c φ h

theorem parBound_mem : ∀ {b : TBranch} {nd : TNode}, nd ∈ b → parBound nd.2 ≤ parBoundB b
  | x :: r, nd, h => by
      cases h with
      | head =>
          show parBound x.2 ≤ parBound x.2 + parBoundB r
          exact Nat.le_add_right _ _
      | tail _ h' =>
          show parBound nd.2 ≤ parBound x.2 + parBoundB r
          exact Nat.le_trans (parBound_mem h') (Nat.le_add_left _ _)

/-- The fresh parameter of a branch: one past every index that occurs on it. -/
def fresh (b : TBranch) : Nat := parBoundB b

theorem fresh_not_occurs {b : TBranch} {nd : TNode} (h : nd ∈ b) :
    occurs (fresh b) nd.2 = false :=
  occurs_bound (fresh b) nd.2 (parBound_mem h)

/-- **THE FRESH PARAMETER IS FRESH** — a theorem about the branch, not a
side condition left to the caller. -/
theorem freshFor_fresh (b : TBranch) : freshFor (fresh b) (toBranch b) := by
  intro x hx
  have ⟨nd, hnd, he⟩ := mem_toBranch_inv hx
  rw [he]
  exact fresh_not_occurs hnd

theorem freshFor_cons {c : Nat} {x : QNode} {b : Branch} (hx : x ∈ b)
    (h : freshFor c b) : freshFor c (x :: b) := by
  intro y hy
  cases hy with
  | head => exact h x hx
  | tail _ hy' => exact h y hy'

/-! ### Expansion: one node, the successors its rule produces -/

/-- The parameters that occur on the branch — γ's candidates. Instantiating
with a parameter nobody mentions is sound but useless, and a bound that
grows with the branch made γ spawn instances forever (measured: the fallen
bridge came back `noFuel` instead of `stuck`). With the parameters in play
γ SATURATES, and the search stops on its own. -/
def parsT : Trm → List Nat
  | Trm.bvar _ => []
  | Trm.par p  => [p]

def parsL : List Trm → List Nat
  | []     => []
  | t :: r => parsT t ++ parsL r

def pars : QFm → List Nat
  | QFm.atom _ ts => parsL ts
  | QFm.neg φ    => pars φ
  | QFm.conj φ ψ => pars φ ++ pars ψ
  | QFm.disj φ ψ => pars φ ++ pars ψ
  | QFm.imp φ ψ  => pars φ ++ pars ψ
  | QFm.all φ    => pars φ
  | QFm.ex φ     => pars φ

def parsB : TBranch → List Nat
  | []      => []
  | nd :: r => pars nd.2 ++ parsB r

/-- Parameter 0 when the branch mentions none. -/
def candidates (b : TBranch) : List Nat :=
  match parsB b with
  | []      => [0]
  | c :: cs => c :: cs

def anyNew : List TNode → TBranch → Bool
  | [], _ => false
  | x :: r, b => !memB x b || anyNew r b

/-- A non-branching step: the new nodes on top of the branch, provided at
least one of them is not there already. -/
def one (ns : List TNode) (b : TBranch) : Option (List TBranch) :=
  match anyNew ns b with
  | true  => some [ns ++ b]
  | false => none

/-- A branching step: two successors, provided at least one node is new. -/
def two (n1 n2 : TNode) (b : TBranch) : Option (List TBranch) :=
  match (!memB n1 b || !memB n2 b) with
  | true  => some [n1 :: b, n2 :: b]
  | false => none

/-- The first parameter among the candidates whose instance is not yet on
the branch. -/
def firstNew (tg : Tag) (φ : QFm) : List Nat → TBranch → Option Nat
  | [], _ => none
  | c :: cs, b =>
      match memB (tg, inst c 0 φ) b with
      | false => some c
      | true  => firstNew tg φ cs b

/-- Is some instance of `φ` (over the candidates) already on the branch? -/
def anyInstance (tg : Tag) (φ : QFm) : List Nat → TBranch → Bool
  | [], _ => false
  | c :: cs, b => memB (tg, inst c 0 φ) b || anyInstance tg φ cs b

/-- δ on T:∃ — a FRESH parameter, ONCE: a T:∃ node whose instance is already
on the branch is spent. Without this the rule re-fired with a new parameter
every round and the search never saturated (measured: the valid quantifier
swap came back `noFuel`). -/
def deltaT (φ : QFm) (b : TBranch) : Option (List TBranch) :=
  match anyInstance Tag.t φ (candidates b) b with
  | true  => none
  | false => one [(Tag.t, inst (fresh b) 0 φ)] b

/-- γ on T:∀ — any parameter in play, the first whose instance is new. -/
def gammaT (φ : QFm) (b : TBranch) : Option (List TBranch) :=
  match firstNew Tag.t φ (candidates b) b with
  | some c => some [(Tag.t, inst c 0 φ) :: b]
  | none   => none

/-- γ on F:∃ — the weak sign N on the instance. -/
def gammaF (φ : QFm) (b : TBranch) : Option (List TBranch) :=
  match firstNew Tag.n φ (candidates b) b with
  | some c => some [(Tag.n, inst c 0 φ) :: b]
  | none   => none

def expandT : QFm → TBranch → Option (List TBranch)
  | QFm.atom _ _, _ => none
  | QFm.neg φ,    b => one [(Tag.f, φ)] b
  | QFm.conj φ ψ, b => one [(Tag.t, φ), (Tag.t, ψ)] b
  | QFm.disj φ ψ, b => two (Tag.t, φ) (Tag.t, ψ) b
  | QFm.imp φ ψ,  b => two (Tag.f, φ) (Tag.t, ψ) b
  | QFm.all φ,    b => gammaT φ b
  | QFm.ex φ,     b => deltaT φ b

def expandF : QFm → TBranch → Option (List TBranch)
  | QFm.atom _ _, _ => none
  | QFm.neg φ,    b => one [(Tag.p, φ)] b
  | QFm.conj φ ψ, b => two (Tag.n, φ) (Tag.n, ψ) b
  | QFm.disj φ ψ, b => one [(Tag.n, φ), (Tag.n, ψ)] b
  | QFm.imp φ ψ,  b => one [(Tag.p, φ), (Tag.n, ψ)] b
  | QFm.all _,    _ => none        -- δ₂, the classical rule: deliberately absent
  | QFm.ex φ,     b => gammaF φ b

/-- Weak signs on a COMPOUND are promoted: in the greedy register every
connective and both quantifiers answer T or F (`compound_two_valued`), so
N:φ is F:φ and P:φ is T:φ there. On an ATOM the weak sign stays — the mark
lives only on atoms — and takes part in closure alone. -/
def expandN : QFm → TBranch → Option (List TBranch)
  | QFm.atom _ _, _ => none
  | QFm.neg φ,    b => one [(Tag.f, QFm.neg φ)] b
  | QFm.conj φ ψ, b => one [(Tag.f, QFm.conj φ ψ)] b
  | QFm.disj φ ψ, b => one [(Tag.f, QFm.disj φ ψ)] b
  | QFm.imp φ ψ,  b => one [(Tag.f, QFm.imp φ ψ)] b
  | QFm.all φ,    b => one [(Tag.f, QFm.all φ)] b
  | QFm.ex φ,     b => one [(Tag.f, QFm.ex φ)] b

def expandP : QFm → TBranch → Option (List TBranch)
  | QFm.atom _ _, _ => none
  | QFm.neg φ,    b => one [(Tag.t, QFm.neg φ)] b
  | QFm.conj φ ψ, b => one [(Tag.t, QFm.conj φ ψ)] b
  | QFm.disj φ ψ, b => one [(Tag.t, QFm.disj φ ψ)] b
  | QFm.imp φ ψ,  b => one [(Tag.t, QFm.imp φ ψ)] b
  | QFm.all φ,    b => one [(Tag.t, QFm.all φ)] b
  | QFm.ex φ,     b => one [(Tag.t, QFm.ex φ)] b

def expand (nd : TNode) (b : TBranch) : Option (List TBranch) :=
  match nd.1 with
  | Tag.t => expandT nd.2 b
  | Tag.f => expandF nd.2 b
  | Tag.p => expandP nd.2 b
  | Tag.n => expandN nd.2 b

/-! ### The greedy register answers on every compound -/

theorem znot_two : ∀ u : V, znot u = T ∨ znot u = F := by decide
theorem zand_two : ∀ u w : V, zand u w = T ∨ zand u w = F := by decide
theorem zor_two  : ∀ u w : V, zor u w = T ∨ zor u w = F := by decide
theorem zimp_two : ∀ u w : V, zimp u w = T ∨ zimp u w = F := by decide

def isAtom : QFm → Bool
  | QFm.atom _ _ => true
  | QFm.neg _    => false
  | QFm.conj _ _ => false
  | QFm.disj _ _ => false
  | QFm.imp _ _  => false
  | QFm.all _    => false
  | QFm.ex _     => false

/-- **THE MARK LIVES ONLY ON ATOMS.** Every compound formula takes T or F —
the connectives by the greedy tables, the quantifiers by their clause. This
is `evalF_classical` of the propositional core, now for the parameter
language. -/
theorem compound_two_valued (I : Nat → List α → V) (ρ : Nat → α) (d : α) (η : List α) :
    ∀ (φ : QFm) (v : V), isAtom φ = false → Holds I ρ d η φ v → v = T ∨ v = F
  | QFm.atom _ _, _, h, _ => Bool.noConfusion h
  | QFm.neg _, v, _, hv => by
      have ⟨u, _, he⟩ := hv
      rw [← he]; exact znot_two u
  | QFm.conj _ _, v, _, hv => by
      have ⟨u, w, _, _, he⟩ := hv
      rw [← he]; exact zand_two u w
  | QFm.disj _ _, v, _, hv => by
      have ⟨u, w, _, _, he⟩ := hv
      rw [← he]; exact zor_two u w
  | QFm.imp _ _, v, _, hv => by
      have ⟨u, w, _, _, he⟩ := hv
      rw [← he]; exact zimp_two u w
  | QFm.all _, _, _, hv => hv.2
  | QFm.ex _, _, _, hv => hv.2

theorem signN_T : SignN T = false := by decide
theorem signP_F : SignP F = false := by decide
theorem signF_F : SignF F = true := by decide
theorem signT_T' : SignT T = true := by decide

/-- N on a compound is F on it. -/
theorem promote_N (I : Nat → List α → V) (ρ : Nat → α) (d : α) (b : Branch) (φ : QFm)
    (hat : isAtom φ = false) (hb : satBranch I ρ d b) (hmem : (SignN, φ) ∈ b) :
    satBranch I ρ d ((SignF, φ) :: b) := by
  intro nd hnd
  cases hnd with
  | head =>
      have ⟨v, hv, hs⟩ := hb _ hmem
      cases compound_two_valued I ρ d [] φ v hat hv with
      | inl hT => rw [hT] at hs; exact absurd hs (show ¬ SignN T = true by decide)
      | inr hF => exact ⟨v, hv, by rw [hF]; exact signF_F⟩
  | tail _ h => exact hb nd h

/-- P on a compound is T on it. -/
theorem promote_P (I : Nat → List α → V) (ρ : Nat → α) (d : α) (b : Branch) (φ : QFm)
    (hat : isAtom φ = false) (hb : satBranch I ρ d b) (hmem : (SignP, φ) ∈ b) :
    satBranch I ρ d ((SignT, φ) :: b) := by
  intro nd hnd
  cases hnd with
  | head =>
      have ⟨v, hv, hs⟩ := hb _ hmem
      cases compound_two_valued I ρ d [] φ v hat hv with
      | inl hT => exact ⟨v, hv, by rw [hT]; exact signT_T'⟩
      | inr hF => rw [hF] at hs; exact absurd hs (show ¬ SignP F = true by decide)
  | tail _ h => exact hb nd h

theorem one_sound {ns : List TNode} {b : TBranch} {succs : List TBranch} :
    one ns b = some succs → succs = [ns ++ b] := by
  unfold one
  cases anyNew ns b with
  | true  => intro h; exact (Option.some.inj h).symm
  | false => intro h; cases h

theorem two_sound {n1 n2 : TNode} {b : TBranch} {succs : List TBranch} :
    two n1 n2 b = some succs → succs = [n1 :: b, n2 :: b] := by
  unfold two
  cases (!memB n1 b || !memB n2 b) with
  | true  => intro h; exact (Option.some.inj h).symm
  | false => intro h; cases h

theorem deltaT_sound {φ : QFm} {b : TBranch} {succs : List TBranch} :
    deltaT φ b = some succs → succs = [(Tag.t, inst (fresh b) 0 φ) :: b] := by
  unfold deltaT
  cases anyInstance Tag.t φ (candidates b) b with
  | true  => intro h; cases h
  | false => intro h; exact one_sound h

theorem gammaT_sound {φ : QFm} {b : TBranch} {succs : List TBranch} :
    gammaT φ b = some succs → ∃ c, succs = [(Tag.t, inst c 0 φ) :: b] := by
  unfold gammaT
  cases firstNew Tag.t φ (candidates b) b with
  | some c => intro h; exact ⟨c, (Option.some.inj h).symm⟩
  | none   => intro h; cases h

theorem gammaF_sound {φ : QFm} {b : TBranch} {succs : List TBranch} :
    gammaF φ b = some succs → ∃ c, succs = [(Tag.n, inst c 0 φ) :: b] := by
  unfold gammaF
  cases firstNew Tag.n φ (candidates b) b with
  | some c => intro h; exact ⟨c, (Option.some.inj h).symm⟩
  | none   => intro h; cases h

/-- **EVERY EXPANSION IS A SOUND STEP.** If the node is on a satisfied branch
and the rule fires, some successor is satisfied — under the same assignment
for every rule but δ, which moves the fresh parameter onto the witness.
One case per rule, each read off its lemma in `ZParamProp` / `ZParamTableau`. -/
theorem expand_sound (I : Nat → List α → V) (d : α) (htot : ∀ ρ, Total I ρ d)
    (ρ : Nat → α) (nd : TNode) (b : TBranch) (succs : List TBranch)
    (hmem : nd ∈ b) (hexp : expand nd b = some succs)
    (hb : satBranch I ρ d (toBranch b)) :
    ∃ s, s ∈ succs ∧ ∃ ρ', satBranch I ρ' d (toBranch s) := by
  match nd, hmem, hexp with
  | (Tag.t, QFm.atom _ _), _, h =>
      have h' : (none : Option (List TBranch)) = some succs := h
      nomatch h'
  | (Tag.t, QFm.neg φ), hm, h =>
      have h' : one [(Tag.f, φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, step_not_T I ρ d (toBranch b) φ hb (mem_toBranch hm)⟩
  | (Tag.t, QFm.conj φ ψ), hm, h =>
      have h' : one [(Tag.t, φ), (Tag.t, ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, step_and_T I ρ d (toBranch b) φ ψ hb (mem_toBranch hm)⟩
  | (Tag.t, QFm.disj φ ψ), hm, h =>
      have h' : two (Tag.t, φ) (Tag.t, ψ) b = some succs := h
      rw [two_sound h']
      cases step_or_T I ρ d (toBranch b) φ ψ hb (mem_toBranch hm) with
      | inl h1 => exact ⟨_, List.Mem.head _, ρ, h1⟩
      | inr h2 => exact ⟨_, List.Mem.tail _ (List.Mem.head _), ρ, h2⟩
  | (Tag.t, QFm.imp φ ψ), hm, h =>
      have h' : two (Tag.f, φ) (Tag.t, ψ) b = some succs := h
      rw [two_sound h']
      cases step_imp_T I ρ d (toBranch b) φ ψ hb (mem_toBranch hm) with
      | inl h1 => exact ⟨_, List.Mem.head _, ρ, h1⟩
      | inr h2 => exact ⟨_, List.Mem.tail _ (List.Mem.head _), ρ, h2⟩
  | (Tag.t, QFm.all φ), hm, h =>
      have h' : gammaT φ b = some succs := h
      have ⟨c, e⟩ := gammaT_sound h'
      rw [e]
      exact ⟨_, List.Mem.head _, ρ, gamma_all_step I ρ d (toBranch b) φ c hb (mem_toBranch hm)⟩
  | (Tag.t, QFm.ex φ), hm, h =>
      have h' : deltaT φ b = some succs := h
      rw [deltaT_sound h']
      have hfresh : freshFor (fresh b) ((SignT, QFm.ex φ) :: toBranch b) :=
        freshFor_cons (mem_toBranch hm) (freshFor_fresh b)
      have ⟨a, ha⟩ := delta_ex_step I ρ d (toBranch b) φ (fresh b) hb (mem_toBranch hm) hfresh
      exact ⟨_, List.Mem.head _, upd ρ (fresh b) a, ha⟩
  | (Tag.f, QFm.atom _ _), _, h =>
      have h' : (none : Option (List TBranch)) = some succs := h
      nomatch h'
  | (Tag.f, QFm.neg φ), hm, h =>
      have h' : one [(Tag.p, φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, step_not_F I ρ d (toBranch b) φ hb (mem_toBranch hm)⟩
  | (Tag.f, QFm.conj φ ψ), hm, h =>
      have h' : two (Tag.n, φ) (Tag.n, ψ) b = some succs := h
      rw [two_sound h']
      cases step_and_F I ρ d (toBranch b) φ ψ hb (mem_toBranch hm) with
      | inl h1 => exact ⟨_, List.Mem.head _, ρ, h1⟩
      | inr h2 => exact ⟨_, List.Mem.tail _ (List.Mem.head _), ρ, h2⟩
  | (Tag.f, QFm.disj φ ψ), hm, h =>
      have h' : one [(Tag.n, φ), (Tag.n, ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, step_or_F I ρ d (toBranch b) φ ψ hb (mem_toBranch hm)⟩
  | (Tag.f, QFm.imp φ ψ), hm, h =>
      have h' : one [(Tag.p, φ), (Tag.n, ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, step_imp_F I ρ d (toBranch b) φ ψ hb (mem_toBranch hm)⟩
  | (Tag.f, QFm.all _), _, h =>
      have h' : (none : Option (List TBranch)) = some succs := h
      nomatch h'
  | (Tag.f, QFm.ex φ), hm, h =>
      have h' : gammaF φ b = some succs := h
      have ⟨c, e⟩ := gammaF_sound h'
      rw [e]
      exact ⟨_, List.Mem.head _, ρ, gamma_ex_step I ρ d (htot ρ) (toBranch b) φ c hb (mem_toBranch hm)⟩
  | (Tag.p, QFm.atom _ _), _, h =>
      have h' : (none : Option (List TBranch)) = some succs := h
      nomatch h'
  | (Tag.p, QFm.neg φ), hm, h =>
      have h' : one [(Tag.t, QFm.neg φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_P I ρ d (toBranch b) (QFm.neg φ) rfl hb (mem_toBranch hm)⟩
  | (Tag.p, QFm.conj φ ψ), hm, h =>
      have h' : one [(Tag.t, QFm.conj φ ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_P I ρ d (toBranch b) (QFm.conj φ ψ) rfl hb (mem_toBranch hm)⟩
  | (Tag.p, QFm.disj φ ψ), hm, h =>
      have h' : one [(Tag.t, QFm.disj φ ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_P I ρ d (toBranch b) (QFm.disj φ ψ) rfl hb (mem_toBranch hm)⟩
  | (Tag.p, QFm.imp φ ψ), hm, h =>
      have h' : one [(Tag.t, QFm.imp φ ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_P I ρ d (toBranch b) (QFm.imp φ ψ) rfl hb (mem_toBranch hm)⟩
  | (Tag.p, QFm.all φ), hm, h =>
      have h' : one [(Tag.t, QFm.all φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_P I ρ d (toBranch b) (QFm.all φ) rfl hb (mem_toBranch hm)⟩
  | (Tag.p, QFm.ex φ), hm, h =>
      have h' : one [(Tag.t, QFm.ex φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_P I ρ d (toBranch b) (QFm.ex φ) rfl hb (mem_toBranch hm)⟩
  | (Tag.n, QFm.atom _ _), _, h =>
      have h' : (none : Option (List TBranch)) = some succs := h
      nomatch h'
  | (Tag.n, QFm.neg φ), hm, h =>
      have h' : one [(Tag.f, QFm.neg φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_N I ρ d (toBranch b) (QFm.neg φ) rfl hb (mem_toBranch hm)⟩
  | (Tag.n, QFm.conj φ ψ), hm, h =>
      have h' : one [(Tag.f, QFm.conj φ ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_N I ρ d (toBranch b) (QFm.conj φ ψ) rfl hb (mem_toBranch hm)⟩
  | (Tag.n, QFm.disj φ ψ), hm, h =>
      have h' : one [(Tag.f, QFm.disj φ ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_N I ρ d (toBranch b) (QFm.disj φ ψ) rfl hb (mem_toBranch hm)⟩
  | (Tag.n, QFm.imp φ ψ), hm, h =>
      have h' : one [(Tag.f, QFm.imp φ ψ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_N I ρ d (toBranch b) (QFm.imp φ ψ) rfl hb (mem_toBranch hm)⟩
  | (Tag.n, QFm.all φ), hm, h =>
      have h' : one [(Tag.f, QFm.all φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_N I ρ d (toBranch b) (QFm.all φ) rfl hb (mem_toBranch hm)⟩
  | (Tag.n, QFm.ex φ), hm, h =>
      have h' : one [(Tag.f, QFm.ex φ)] b = some succs := h
      rw [one_sound h']
      exact ⟨_, List.Mem.head _, ρ, promote_N I ρ d (toBranch b) (QFm.ex φ) rfl hb (mem_toBranch hm)⟩

/-! ### Picking a node, and the search -/

/-- The first node of `scan` whose rule fires on the branch `b`. -/
def pick : TBranch → TBranch → Option (List TBranch)
  | [], _ => none
  | nd :: r, b =>
      match expand nd b with
      | some succs => some succs
      | none       => pick r b

theorem pick_sound (I : Nat → List α → V) (d : α) (htot : ∀ ρ, Total I ρ d) (ρ : Nat → α) :
    ∀ (scan b : TBranch) (succs : List TBranch),
    (∀ nd, nd ∈ scan → nd ∈ b) → pick scan b = some succs →
    satBranch I ρ d (toBranch b) →
    ∃ s, s ∈ succs ∧ ∃ ρ', satBranch I ρ' d (toBranch s)
  | [], _, succs, _, h, _ =>
      have h' : (none : Option (List TBranch)) = some succs := h
      nomatch h'
  | nd :: r, b, succs, hsub, h, hb => by
      unfold pick at h
      cases hexp : expand nd b with
      | some s =>
          rw [hexp] at h
          have e : s = succs := Option.some.inj h
          rw [← e]
          exact expand_sound I d htot ρ nd b s (hsub nd (List.Mem.head r)) hexp hb
      | none =>
          rw [hexp] at h
          exact pick_sound I d htot ρ r b succs (fun x hx => hsub x (List.Mem.tail nd hx)) h hb

inductive Verdict where
  | closed   -- every branch closed
  | stuck    -- a branch with no applicable rule that is not closed
  | noFuel
  deriving DecidableEq, Repr

/-- The search over a worklist of branches. Structural on fuel. -/
def search : Nat → List TBranch → Verdict
  | _, [] => Verdict.closed
  | 0, _ :: _ => Verdict.noFuel
  | fuel + 1, b :: rest =>
      match closedB b with
      | true  => search fuel rest
      | false =>
          match pick b b with
          | some succs => search fuel (succs ++ rest)
          | none       => Verdict.stuck

theorem mem_append_left {x : TBranch} : ∀ {l r : List TBranch}, x ∈ l → x ∈ l ++ r
  | y :: l, r, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail y (mem_append_left h')

theorem mem_append_right {x : TBranch} : ∀ {l r : List TBranch}, x ∈ r → x ∈ l ++ r
  | [], _, h => h
  | y :: _, _, h => List.Mem.tail y (mem_append_right h)

/-- **SOUNDNESS OF THE SEARCH.** A run that closes every branch shows that no
branch on the initial list has a model — under any assignment, for a total
interpretation. Induction on fuel; closure by `closedB_sound` + `closed_unsat`,
expansion by `pick_sound`. -/
theorem search_sound (I : Nat → List α → V) (d : α) (htot : ∀ ρ, Total I ρ d) :
    ∀ (fuel : Nat) (bs : List TBranch), search fuel bs = Verdict.closed →
    ∀ b, b ∈ bs → ∀ ρ, ¬ satBranch I ρ d (toBranch b)
  | _, [], _, _, hb, _, _ => nomatch hb
  | 0, _ :: _, h, _, _, _, _ =>
      have h' : Verdict.noFuel = Verdict.closed := h
      nomatch h'
  | fuel + 1, b0 :: rest, h, b, hb, ρ, hsat => by
      unfold search at h
      cases hc : closedB b0 with
      | true =>
          rw [hc] at h
          cases hb with
          | head => exact closed_unsat I ρ d (toBranch b0) (closedB_sound b0 hc) hsat
          | tail _ hb' => exact search_sound I d htot fuel rest h b hb' ρ hsat
      | false =>
          rw [hc] at h
          cases hp : pick b0 b0 with
          | some succs =>
              rw [hp] at h
              cases hb with
              | head =>
                  have ⟨s, hs, ρ', hs'⟩ :=
                    pick_sound I d htot ρ b0 b0 succs (fun _ hx => hx) hp hsat
                  exact search_sound I d htot fuel (succs ++ rest) h s (mem_append_left hs) ρ' hs'
              | tail _ hb' =>
                  exact search_sound I d htot fuel (succs ++ rest) h b (mem_append_right hb') ρ hsat
          | none =>
              rw [hp] at h
              cases h

/-! ### End to end: a closed run is a proof of entailment -/

def tagAll : List QFm → TBranch
  | [] => []
  | γ :: r => (Tag.t, γ) :: tagAll r

/-- Premises tagged `t`, the conclusion tagged `n` ("not T"): the branch a
countermodel to Γ ⊢ φ would have to satisfy. -/
def initBranch (Γ : List QFm) (φ : QFm) : TBranch := (Tag.n, φ) :: tagAll Γ

theorem mem_tagAll_inv : ∀ {Γ : List QFm} {x : QNode}, x ∈ toBranch (tagAll Γ) →
    ∃ γ, γ ∈ Γ ∧ x = (SignT, γ)
  | [], _, h => nomatch h
  | γ :: r, x, h => by
      cases h with
      | head => exact ⟨γ, List.Mem.head r, rfl⟩
      | tail _ h' =>
          have ⟨δ, hδ, he⟩ := mem_tagAll_inv h'
          exact ⟨δ, List.Mem.tail γ hδ, he⟩

theorem signT_T : SignT T = true := by decide
theorem signN_false : ∀ v : V, SignN v = false → v = T := by decide

/-- **A CLOSED RUN ON Γ ⊢ φ IS A PROOF OF ENTAILMENT.** Every total model that
makes each premise T makes φ T. The value of φ is produced by totality and
shown to be T; nothing is refuted twice. -/
theorem entails_of_closed (Γ : List QFm) (φ : QFm) (fuel : Nat)
    (h : search fuel [initBranch Γ φ] = Verdict.closed)
    (I : Nat → List α → V) (d : α) (htot : ∀ ρ, Total I ρ d) (ρ : Nat → α)
    (hΓ : ∀ γ, γ ∈ Γ → Holds I ρ d [] γ T) : Holds I ρ d [] φ T := by
  have ⟨v, hv⟩ := htot ρ φ []
  have hunsat := search_sound I d htot fuel [initBranch Γ φ] h (initBranch Γ φ) (List.Mem.head _) ρ
  have hn : SignN v = false := by
    apply notT
    intro hN
    apply hunsat
    intro nd hnd
    cases hnd with
    | head => exact ⟨v, hv, hN⟩
    | tail _ hnd' =>
        have ⟨γ, hγ, he⟩ := mem_tagAll_inv hnd'
        rw [he]
        exact ⟨T, hΓ γ hγ, signT_T⟩
  have hvT : v = T := signN_false v hn
  rw [hvT] at hv
  exact hv

/-! ### Three runs, evaluated by the kernel

  P is predicate 0; `par 3` is a parameter. -/

/-- ∀x P(x) ⊢ P(c): γ instantiates at c and the branch closes. -/
theorem run_all_inst :
    search 8 [initBranch [QFm.all (QFm.atom 0 [Trm.bvar 0])] (QFm.atom 0 [Trm.par 3])]
      = Verdict.closed := by decide

/-- P(c) ∧ Q(c) ⊢ Q(c): one propositional step, then closure. -/
theorem run_and_elim :
    search 8 [initBranch [QFm.conj (QFm.atom 0 [Trm.par 1]) (QFm.atom 1 [Trm.par 1])]
                         (QFm.atom 1 [Trm.par 1])]
      = Verdict.closed := by decide

/-- **THE FALLEN BRIDGE STAYS FALLEN.** ¬∀x P(x) ⊢ ∃x ¬P(x): T:¬∀ yields F:∀,
for which there is no rule, and N:∃ has none either. The search reports
`stuck`, not `closed` — exactly what §6 says of `¬∀ ⊭ ∃¬`. -/
theorem run_fallen_bridge :
    search 8 [initBranch [QFm.neg (QFm.all (QFm.atom 0 [Trm.bvar 0]))]
                         (QFm.ex (QFm.neg (QFm.atom 0 [Trm.bvar 0])))]
      = Verdict.stuck := by decide

/-! ### E51: two-place predicates, and compound conclusions

  R is predicate 0 with two places; `bvar 1` is the outer bound variable. -/

/-- P(c) ⊢ P(c) ∨ Q(c): the conclusion is compound, N is promoted to F, F:∨
splits into N:P(c), N:Q(c), and N:P(c) clashes with T:P(c). Before E51 the
N-node had no rule and this was `stuck`. -/
theorem run_or_intro :
    search 8 [initBranch [QFm.atom 0 [Trm.par 1]]
                         (QFm.disj (QFm.atom 0 [Trm.par 1]) (QFm.atom 1 [Trm.par 1]))]
      = Verdict.closed := by decide

/-- ∀x∀y R(x,y) ⊢ R(a,b): two γ steps on a two-place atom. -/
theorem run_two_place :
    search 12 [initBranch [QFm.all (QFm.all (QFm.atom 0 [Trm.bvar 1, Trm.bvar 0]))]
                          (QFm.atom 0 [Trm.par 1, Trm.par 2])]
      = Verdict.closed := by decide

/-- ∃x R(x,x) ⊢ ∃x∃y R(x,y): δ names the witness c; the conclusion's N is
promoted to F twice with a γ on F:∃ between, down to N:R(c,c). -/
theorem run_diag_to_pair :
    search 16 [initBranch [QFm.ex (QFm.atom 0 [Trm.bvar 0, Trm.bvar 0])]
                          (QFm.ex (QFm.ex (QFm.atom 0 [Trm.bvar 1, Trm.bvar 0])))]
      = Verdict.closed := by decide

/-- **THE VALID QUANTIFIER SWAP IS OUT OF REACH, HONESTLY.** ∃x∀y R(x,y) ⊢
∀y∃x R(x,y) holds in ZTL, but the conclusion N:∀ is promoted to F:∀ — the
one rule this search does not have, because it is the classical one. `stuck`,
and the reason is the same axiom split as in `ZParamSound`. -/
theorem run_swap_needs_classical :
    search 16 [initBranch [QFm.ex (QFm.all (QFm.atom 0 [Trm.bvar 1, Trm.bvar 0]))]
                          (QFm.all (QFm.ex (QFm.atom 0 [Trm.bvar 0, Trm.bvar 1])))]
      = Verdict.stuck := by decide

end ZParamEngine

#print axioms ZParamEngine.clashTag_sound
#print axioms ZParamEngine.closedB_sound
#print axioms ZParamEngine.freshFor_fresh
#print axioms ZParamEngine.expand_sound
#print axioms ZParamEngine.pick_sound
#print axioms ZParamEngine.search_sound
#print axioms ZParamEngine.entails_of_closed
#print axioms ZParamEngine.run_all_inst
#print axioms ZParamEngine.run_and_elim
#print axioms ZParamEngine.run_fallen_bridge
#print axioms ZParamEngine.compound_two_valued
#print axioms ZParamEngine.promote_N
#print axioms ZParamEngine.promote_P
#print axioms ZParamEngine.run_or_intro
#print axioms ZParamEngine.run_two_place
#print axioms ZParamEngine.run_diag_to_pair
#print axioms ZParamEngine.run_swap_needs_classical
