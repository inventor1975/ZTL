/-
  ZParamHintikka.lean — E54: THE FINITE HALF OF COMPLETENESS, ON THE EMPTY
  AXIOM LIST.

  §6 said of the parameter tableaux: "completeness is the standard
  Hintikka-saturation argument — argued, not measured." This file measures
  the half of it that a finite run can carry, and it turns out to be a
  theorem with no axioms behind it.

  WHAT COMPLETENESS SPLITS INTO. Soundness (`ZParamEngine.entails_of_closed`)
  says a closed run is a proof. Completeness says the converse: a valid
  sequent's run closes. Its contrapositive has two halves:

    (H) if the run STOPS OPEN — `stuck`, a branch on which no rule fires and
        no clash stands — then there is a countermodel, read off that branch;
    (K) if the run never stops — `noFuel` at every fuel — there is an
        infinite open branch, and a countermodel on its infinite domain.

  (H) is here. The branch is finite, so its parameters are finitely many, so
  the model is FINITE and its universal quantifier is a fold: totality is
  computed, not assumed, and nothing classical enters. (K) is not here: it
  needs a fair strategy (E54 gave the engine one), König's lemma, and a
  total model over an infinite domain — that last is the survey of a domain
  ZTL declines to call an act, and it is exactly the step δ₂'s soundness
  needs. (K) stays argued, with its parts named.

  THE MODEL IS NOT CLASSICAL. Its domain is the parameters on the branch;
  its atoms read the branch: `t` gives T, `f` gives F, and an atom carrying
  only a weak sign — P "not F", N "not T" — or none at all gets the MARK Z.
  A classical countermodel has no Z to give. The fallen bridge `¬∀xP ⊢ ∃x¬P`
  is refuted by exactly this model, with `P(c*) = Z`.

  AND THE TABLES ARE WHAT MAKES IT WORK. Every rule of the engine was read
  off a cover lemma of §5 — the exact preimage of a sign. Here each rule is
  read BACKWARDS: if the successors are satisfied, so is the parent, and that
  is a cell of `ZTL-TABLES.txt` each time, checked by `decide`. The cell to
  look at is `F:(φ∨ψ) ⟹ N:φ, N:ψ`: backwards it needs `Z ∨ Z = F`. Under a
  Kleene lift `Z ∨ Z = Z` and the weak-sign rule would not be complete.
  The asymmetry the logic is criticised for is what carries this proof.

  δ₂ IN THIS HALF IS CONSTRUCTIVE. `F:∀xφ ⟹ N:φ(c*)` costs `¬∀ → ∃¬` for
  soundness (`ZParamSound`, the probe outside the corpus). Backwards it costs
  nothing: one instance that is not T refutes the universal by `holds_det`.
  One rule, classical in one direction and free in the other — that is the
  measurement this file adds. `Delta2Sat` is the saturation clause for it;
  `search true` discharges it by construction, `search false` cannot, and
  `countermodel_of_saturated` takes it as a hypothesis so both engines are
  covered honestly.

  FORM. Recursion on the SIZE of a formula, not its structure: an instance
  φ(c) is not a subterm of ∀xφ, and `size_inst` says it is no bigger.
  Formulas on the initial branch must be CLOSED (`closedAt 0`): the term
  model reads atoms through their parameters, and a free bound variable has
  none. Closedness is not threaded through the search — the satisfaction
  lemma carries it down from parent to successor, which is all it needs.
  Nat-indexed everything, own list recursions, `decide` on the tables, no
  wildcard rows: the traps of 2026-09-05.
-/
import ZParamEngine

namespace ZParamHintikka

open V
open ZParamSyntax
open ZParamTableau
open ZParamProp
open ZParamClosure
open ZParamSearch
open ZParamEngine

variable {α : Type}

/-! ### Bool splits, each `decide`d -/

theorem andI : ∀ a b : Bool, a = true → b = true → (a && b) = true := by decide
theorem orFF : ∀ a b : Bool, (a || b) = false → a = false ∧ b = false := by decide
theorem notF : ∀ a : Bool, (!a) = false → a = true := by decide
theorem andFF : ∀ a b : Bool, (!a && !b) = false → a = true ∨ b = true := by decide
theorem andTrueF : ∀ a : Bool, (a && true) = false → a = false := by decide

/-! ### Size, and instantiation keeps it -/

def size : QFm → Nat
  | QFm.atom _ _ => 0
  | QFm.neg φ    => size φ + 1
  | QFm.conj φ ψ => size φ + size ψ + 1
  | QFm.disj φ ψ => size φ + size ψ + 1
  | QFm.imp φ ψ  => size φ + size ψ + 1
  | QFm.all φ    => size φ + 1
  | QFm.ex φ     => size φ + 1

theorem size_inst (c : Nat) : ∀ (φ : QFm) (k : Nat), size (inst c k φ) = size φ
  | QFm.atom _ _, _ => rfl
  | QFm.neg φ, k => by
      show size (inst c k φ) + 1 = size φ + 1
      rw [size_inst c φ k]
  | QFm.conj φ ψ, k => by
      show size (inst c k φ) + size (inst c k ψ) + 1 = size φ + size ψ + 1
      rw [size_inst c φ k, size_inst c ψ k]
  | QFm.disj φ ψ, k => by
      show size (inst c k φ) + size (inst c k ψ) + 1 = size φ + size ψ + 1
      rw [size_inst c φ k, size_inst c ψ k]
  | QFm.imp φ ψ, k => by
      show size (inst c k φ) + size (inst c k ψ) + 1 = size φ + size ψ + 1
      rw [size_inst c φ k, size_inst c ψ k]
  | QFm.all φ, k => by
      show size (inst c (k + 1) φ) + 1 = size φ + 1
      rw [size_inst c φ (k + 1)]
  | QFm.ex φ, k => by
      show size (inst c (k + 1) φ) + 1 = size φ + 1
      rw [size_inst c φ (k + 1)]

/-! ### Closed formulas, and instantiation keeps them closed -/

/-- `j < k` on naturals, own recursion so that it computes and stays clean. -/
def ltB : Nat → Nat → Bool
  | 0,     0     => false
  | _ + 1, 0     => false
  | 0,     _ + 1 => true
  | j + 1, k + 1 => ltB j k

theorem ltB_zero : ∀ j : Nat, ltB j 0 = false
  | 0     => rfl
  | _ + 1 => rfl

theorem ltB_succ_of_ne : ∀ j k : Nat, ltB j (k + 1) = true → Nat.beq j k = false → ltB j k = true
  | 0,     0,     _, h => Bool.noConfusion h
  | 0,     _ + 1, _, _ => rfl
  | j + 1, 0,     h, _ => by
      have h' : ltB j 0 = true := h
      rw [ltB_zero j] at h'
      exact Bool.noConfusion h'
  | j + 1, k + 1, h, hne => ltB_succ_of_ne j k h hne

def closedT (k : Nat) : Trm → Bool
  | Trm.bvar j => ltB j k
  | Trm.par _  => true

def closedL (k : Nat) : List Trm → Bool
  | []     => true
  | t :: r => closedT k t && closedL k r

def closedAt : Nat → QFm → Bool
  | k, QFm.atom _ ts => closedL k ts
  | k, QFm.neg φ    => closedAt k φ
  | k, QFm.conj φ ψ => closedAt k φ && closedAt k ψ
  | k, QFm.disj φ ψ => closedAt k φ && closedAt k ψ
  | k, QFm.imp φ ψ  => closedAt k φ && closedAt k ψ
  | k, QFm.all φ    => closedAt (k + 1) φ
  | k, QFm.ex φ     => closedAt (k + 1) φ

theorem closedT_inst (c : Nat) : ∀ (t : Trm) (k : Nat),
    closedT (k + 1) t = true → closedT k (instT c k t) = true
  | Trm.par _, _, _ => rfl
  | Trm.bvar j, k, h => by
      show closedT k (match Nat.beq j k with | true => Trm.par c | false => Trm.bvar j) = true
      cases hj : Nat.beq j k with
      | true  => rfl
      | false =>
          show ltB j k = true
          exact ltB_succ_of_ne j k h hj

theorem closedL_inst (c : Nat) : ∀ (ts : List Trm) (k : Nat),
    closedL (k + 1) ts = true → closedL k (instL c k ts) = true
  | [], _, _ => rfl
  | t :: r, k, h => by
      have ⟨h1, h2⟩ := andT _ _ h
      show (closedT k (instT c k t) && closedL k (instL c k r)) = true
      exact andI _ _ (closedT_inst c t k h1) (closedL_inst c r k h2)

theorem closed_inst (c : Nat) : ∀ (φ : QFm) (k : Nat),
    closedAt (k + 1) φ = true → closedAt k (inst c k φ) = true
  | QFm.atom _ ts, k, h => closedL_inst c ts k h
  | QFm.neg φ, k, h => closed_inst c φ k h
  | QFm.conj φ ψ, k, h => by
      have ⟨h1, h2⟩ := andT _ _ h
      show (closedAt k (inst c k φ) && closedAt k (inst c k ψ)) = true
      exact andI _ _ (closed_inst c φ k h1) (closed_inst c ψ k h2)
  | QFm.disj φ ψ, k, h => by
      have ⟨h1, h2⟩ := andT _ _ h
      show (closedAt k (inst c k φ) && closedAt k (inst c k ψ)) = true
      exact andI _ _ (closed_inst c φ k h1) (closed_inst c ψ k h2)
  | QFm.imp φ ψ, k, h => by
      have ⟨h1, h2⟩ := andT _ _ h
      show (closedAt k (inst c k φ) && closedAt k (inst c k ψ)) = true
      exact andI _ _ (closed_inst c φ k h1) (closed_inst c ψ k h2)
  | QFm.all φ, k, h => closed_inst c φ (k + 1) h
  | QFm.ex φ, k, h => closed_inst c φ (k + 1) h

/-! ### Membership, both ways -/

def memN (n : Nat) : List Nat → Bool
  | []     => false
  | c :: r => Nat.beq n c || memN n r

theorem mem_of_memB (nd : TNode) : ∀ b : TBranch, memB nd b = true → nd ∈ b
  | [], h => Bool.noConfusion h
  | x :: r, h => by
      cases orT _ _ h with
      | inl h1 =>
          have : nd = x := of_decide_eq_true h1
          rw [this]
          exact List.Mem.head r
      | inr h2 => exact List.Mem.tail x (mem_of_memB nd r h2)

theorem memB_of_mem (nd : TNode) : ∀ b : TBranch, nd ∈ b → memB nd b = true
  | x :: r, h => by
      cases h with
      | head =>
          show (decide (nd = nd) || memB nd r) = true
          rw [decide_eq_true rfl]
          rfl
      | tail _ h' =>
          show (decide (nd = x) || memB nd r) = true
          rw [memB_of_mem nd r h']
          cases decide (nd = x) with
          | true => rfl
          | false => rfl

theorem memN_append_left (c : Nat) : ∀ (l r : List Nat), memN c l = true → memN c (l ++ r) = true
  | [], _, h => Bool.noConfusion h
  | c' :: l, r, h => by
      show (Nat.beq c c' || memN c (l ++ r)) = true
      cases orT _ _ h with
      | inl h1 => rw [h1]; rfl
      | inr h2 =>
          rw [memN_append_left c l r h2]
          cases Nat.beq c c' with
          | true => rfl
          | false => rfl

theorem memN_append_right (c : Nat) : ∀ (l r : List Nat), memN c r = true → memN c (l ++ r) = true
  | [], _, h => h
  | c' :: l, r, h => by
      show (Nat.beq c c' || memN c (l ++ r)) = true
      rw [memN_append_right c l r h]
      cases Nat.beq c c' with
      | true => rfl
      | false => rfl

theorem memN_head (c : Nat) (r : List Nat) : memN c (c :: r) = true := by
  show (Nat.beq c c || memN c r) = true
  rw [natBeq_refl c]
  rfl

/-! ### The parameters of an atom on the branch are candidates -/

theorem memN_parsL (c : Nat) : ∀ ts : List Trm, Trm.par c ∈ ts → memN c (parsL ts) = true
  | t :: r, h => by
      cases h with
      | head => exact memN_head c (parsL r)
      | tail _ h' =>
          show memN c (parsT t ++ parsL r) = true
          exact memN_append_right c (parsT t) (parsL r) (memN_parsL c r h')

theorem memN_parsB (c : Nat) : ∀ (b : TBranch) (nd : TNode), nd ∈ b →
    memN c (pars nd.2) = true → memN c (parsB b) = true
  | x :: r, nd, h, hc => by
      cases h with
      | head =>
          show memN c (pars x.2 ++ parsB r) = true
          exact memN_append_left c (pars x.2) (parsB r) hc
      | tail _ h' =>
          show memN c (pars x.2 ++ parsB r) = true
          exact memN_append_right c (pars x.2) (parsB r) (memN_parsB c r nd h' hc)

theorem memN_cands (c : Nat) (b : TBranch) (h : memN c (parsB b) = true) :
    memN c (candidates b) = true := by
  unfold candidates
  cases hp : parsB b with
  | nil => rw [hp] at h; exact Bool.noConfusion h
  | cons c' cs => rw [hp] at h; exact h

/-- A parameter inside an atom on the branch is a candidate. -/
theorem atom_par_cand (b : TBranch) (tg : Tag) (P : Nat) (ts : List Trm) (c : Nat)
    (hmem : (tg, QFm.atom P ts) ∈ b) (ht : Trm.par c ∈ ts) : memN c (candidates b) = true :=
  memN_cands c b (memN_parsB c b (tg, QFm.atom P ts) hmem (memN_parsL c ts ht))

/-! ### The term model of a branch -/

/-- The first candidate — parameter 0 when the branch mentions none. -/
def base (b : TBranch) : Nat :=
  match parsB b with
  | []     => 0
  | c :: _ => c

theorem base_mem (b : TBranch) : memN (base b) (candidates b) = true := by
  unfold base candidates
  cases hp : parsB b with
  | nil => rfl
  | cons c cs => exact memN_head c cs

/-- Every natural number, folded onto the candidates: itself if it is one,
`base` otherwise. The domain of the model is `Nat`; its VALUES are the
candidates, and `norm` is how a quantifier over `Nat` becomes a fold. -/
def norm (b : TBranch) (a : Nat) : Nat :=
  match memN a (candidates b) with
  | true  => a
  | false => base b

theorem norm_mem (b : TBranch) (a : Nat) : memN (norm b a) (candidates b) = true := by
  unfold norm
  cases h : memN a (candidates b) with
  | true  => exact h
  | false => exact base_mem b

theorem norm_id (b : TBranch) (a : Nat) (h : memN a (candidates b) = true) : norm b a = a := by
  unfold norm
  rw [h]

theorem norm_norm (b : TBranch) (a : Nat) : norm b (norm b a) = norm b a :=
  norm_id b (norm b a) (norm_mem b a)

theorem norm_base (b : TBranch) : norm b (base b) = base b :=
  norm_id b (base b) (base_mem b)

def mapNorm (b : TBranch) : List Nat → List Nat
  | []     => []
  | v :: r => norm b v :: mapNorm b r

theorem mapNorm_norm (b : TBranch) : ∀ l : List Nat, mapNorm b (mapNorm b l) = mapNorm b l
  | [] => rfl
  | v :: r => by
      show norm b (norm b v) :: mapNorm b (mapNorm b r) = norm b v :: mapNorm b r
      rw [norm_norm b v, mapNorm_norm b r]

def parsOf : List Nat → List Trm
  | []     => []
  | v :: r => Trm.par v :: parsOf r

/-- What the branch says about an atom: `t` gives T, `f` gives F, anything
else — a weak sign only, or no sign — gives the MARK. -/
def atomVal (b : TBranch) (P : Nat) (ts : List Trm) : V :=
  match memB (Tag.t, QFm.atom P ts) b with
  | true  => T
  | false =>
      match memB (Tag.f, QFm.atom P ts) b with
      | true  => F
      | false => Z

/-- The interpretation reads the branch through the normalised values. -/
def termI (b : TBranch) : Nat → List Nat → V :=
  fun P vs => atomVal b P (parsOf (mapNorm b vs))

def termρ (b : TBranch) : Nat → Nat := norm b
def termd (b : TBranch) : Nat := base b

theorem termρ_norm (b : TBranch) (p : Nat) : termρ b p = norm b (termρ b p) :=
  (norm_norm b p).symm

theorem termd_norm (b : TBranch) : termd b = norm b (termd b) :=
  (norm_base b).symm

/-! ### The model sees values only through `norm` -/

theorem stackVal_mapNorm (b : TBranch) (d : Nat) :
    ∀ (η : List Nat) (k : Nat), stackVal (norm b d) (mapNorm b η) k = norm b (stackVal d η k)
  | [],     _     => rfl
  | _ :: _, 0     => rfl
  | _ :: r, k + 1 => stackVal_mapNorm b d r k

theorem trmVal_norm (b : TBranch) (ρ ρ' : Nat → Nat) (hρ : ∀ p, ρ' p = norm b (ρ p))
    (d d' : Nat) (hd : d' = norm b d) (η : List Nat) :
    ∀ t : Trm, trmVal ρ' (mapNorm b η) d' t = norm b (trmVal ρ η d t)
  | Trm.par p  => hρ p
  | Trm.bvar k => by
      show stackVal d' (mapNorm b η) k = norm b (stackVal d η k)
      rw [hd]
      exact stackVal_mapNorm b d η k

theorem trmVals_norm (b : TBranch) (ρ ρ' : Nat → Nat) (hρ : ∀ p, ρ' p = norm b (ρ p))
    (d d' : Nat) (hd : d' = norm b d) (η : List Nat) :
    ∀ ts : List Trm, trmVals ρ' (mapNorm b η) d' ts = mapNorm b (trmVals ρ η d ts)
  | [] => rfl
  | t :: r => by
      show trmVal ρ' (mapNorm b η) d' t :: trmVals ρ' (mapNorm b η) d' r
         = norm b (trmVal ρ η d t) :: mapNorm b (trmVals ρ η d r)
      rw [trmVal_norm b ρ ρ' hρ d d' hd η t, trmVals_norm b ρ ρ' hρ d d' hd η r]

theorem termI_mapNorm (b : TBranch) (P : Nat) (vs : List Nat) :
    termI b P (mapNorm b vs) = termI b P vs := by
  show atomVal b P (parsOf (mapNorm b (mapNorm b vs))) = atomVal b P (parsOf (mapNorm b vs))
  rw [mapNorm_norm b vs]

/-- **NORMALISING THE ASSIGNMENT AND THE STACK CHANGES NO VERDICT.** Stated
with the normalised assignment as a separate function agreeing pointwise, so
that no function extensionality is needed. -/
theorem holds_norm (b : TBranch) :
    ∀ (φ : QFm) (ρ ρ' : Nat → Nat), (∀ p, ρ' p = norm b (ρ p)) →
    ∀ (d d' : Nat), d' = norm b d →
    ∀ (η η' : List Nat), η' = mapNorm b η →
    ∀ (v : V), (Holds (termI b) ρ d η φ v ↔ Holds (termI b) ρ' d' η' φ v)
  | QFm.atom P ts, ρ, ρ', hρ, d, d', hd, η, η', hη, v => by
      show termI b P (trmVals ρ η d ts) = v ↔ termI b P (trmVals ρ' η' d' ts) = v
      rw [hη, trmVals_norm b ρ ρ' hρ d d' hd η ts, termI_mapNorm]
  | QFm.neg φ, ρ, ρ', hρ, d, d', hd, η, η', hη, v => by
      constructor
      · intro ⟨u, hu, he⟩
        exact ⟨u, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mp hu, he⟩
      · intro ⟨u, hu, he⟩
        exact ⟨u, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mpr hu, he⟩
  | QFm.conj φ ψ, ρ, ρ', hρ, d, d', hd, η, η', hη, v => by
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mp hu,
                     (holds_norm b ψ ρ ρ' hρ d d' hd η η' hη w).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mpr hu,
                     (holds_norm b ψ ρ ρ' hρ d d' hd η η' hη w).mpr hw, he⟩
  | QFm.disj φ ψ, ρ, ρ', hρ, d, d', hd, η, η', hη, v => by
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mp hu,
                     (holds_norm b ψ ρ ρ' hρ d d' hd η η' hη w).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mpr hu,
                     (holds_norm b ψ ρ ρ' hρ d d' hd η η' hη w).mpr hw, he⟩
  | QFm.imp φ ψ, ρ, ρ', hρ, d, d', hd, η, η', hη, v => by
      constructor
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mp hu,
                     (holds_norm b ψ ρ ρ' hρ d d' hd η η' hη w).mp hw, he⟩
      · intro ⟨u, w, hu, hw, he⟩
        exact ⟨u, w, (holds_norm b φ ρ ρ' hρ d d' hd η η' hη u).mpr hu,
                     (holds_norm b ψ ρ ρ' hρ d d' hd η η' hη w).mpr hw, he⟩
  | QFm.all φ, ρ, ρ', hρ, d, d', hd, η, η', hη, v => by
      -- the normalised side is a fixed point of normalising again
      have hρ' : ∀ p, ρ' p = norm b (ρ' p) := fun p => by rw [hρ p, norm_norm]
      have hd' : d' = norm b d' := by rw [hd, norm_norm]
      have hη' : η' = mapNorm b η' := by rw [hη, mapNorm_norm]
      have key : (∀ a, Holds (termI b) ρ d (a :: η) φ T) ↔
                 (∀ a, Holds (termI b) ρ' d' (a :: η') φ T) := by
        constructor
        · intro hall a
          have h1 : Holds (termI b) ρ' d' (norm b a :: η') φ T :=
            (holds_norm b φ ρ ρ' hρ d d' hd (a :: η) (norm b a :: η')
              (by show norm b a :: η' = norm b a :: mapNorm b η; rw [hη]) T).mp (hall a)
          exact (holds_norm b φ ρ' ρ' hρ' d' d' hd' (a :: η') (norm b a :: η')
              (by show norm b a :: η' = norm b a :: mapNorm b η'; rw [← hη']) T).mpr h1
        · intro hall a
          have h1 : Holds (termI b) ρ' d' (norm b a :: η') φ T :=
            (holds_norm b φ ρ' ρ' hρ' d' d' hd' (a :: η') (norm b a :: η')
              (by show norm b a :: η' = norm b a :: mapNorm b η'; rw [← hη']) T).mp (hall a)
          exact (holds_norm b φ ρ ρ' hρ d d' hd (a :: η) (norm b a :: η')
              (by show norm b a :: η' = norm b a :: mapNorm b η; rw [hη]) T).mpr h1
      constructor
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv => key.mp (hiff.mp hv), fun hall => hiff.mpr (key.mpr hall)⟩, hcl⟩
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv => key.mpr (hiff.mp hv), fun hall => hiff.mpr (key.mp hall)⟩, hcl⟩
  | QFm.ex φ, ρ, ρ', hρ, d, d', hd, η, η', hη, v => by
      have hρ' : ∀ p, ρ' p = norm b (ρ' p) := fun p => by rw [hρ p, norm_norm]
      have hd' : d' = norm b d' := by rw [hd, norm_norm]
      have hη' : η' = mapNorm b η' := by rw [hη, mapNorm_norm]
      have key : (∃ a, Holds (termI b) ρ d (a :: η) φ T) ↔
                 (∃ a, Holds (termI b) ρ' d' (a :: η') φ T) := by
        constructor
        · intro ⟨a, ha⟩
          refine ⟨norm b a, ?_⟩
          exact (holds_norm b φ ρ ρ' hρ d d' hd (a :: η) (norm b a :: η')
              (by show norm b a :: η' = norm b a :: mapNorm b η; rw [hη]) T).mp ha
        · intro ⟨a, ha⟩
          refine ⟨a, ?_⟩
          have h1 : Holds (termI b) ρ' d' (norm b a :: η') φ T :=
            (holds_norm b φ ρ' ρ' hρ' d' d' hd' (a :: η') (norm b a :: η')
              (by show norm b a :: η' = norm b a :: mapNorm b η'; rw [← hη']) T).mp ha
          exact (holds_norm b φ ρ ρ' hρ d d' hd (a :: η) (norm b a :: η')
              (by show norm b a :: η' = norm b a :: mapNorm b η; rw [hη]) T).mpr h1
      constructor
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv => key.mp (hiff.mp hv), fun hex => hiff.mpr (key.mpr hex)⟩, hcl⟩
      · intro ⟨hiff, hcl⟩
        exact ⟨⟨fun hv => key.mpr (hiff.mp hv), fun hex => hiff.mpr (key.mp hex)⟩, hcl⟩

/-! ### The model is total — computed, over the finite candidates -/

def allG (p : Nat → Bool) : List Nat → Bool
  | []     => true
  | c :: r => p c && allG p r

def anyG (p : Nat → Bool) : List Nat → Bool
  | []     => false
  | c :: r => p c || anyG p r

theorem allG_mem (p : Nat → Bool) : ∀ l : List Nat, allG p l = true →
    ∀ c, memN c l = true → p c = true
  | [], _, _, h => Bool.noConfusion h
  | c' :: r, h, c, hc => by
      have ⟨h1, h2⟩ := andT _ _ h
      cases orT _ _ hc with
      | inl e => rw [Nat.eq_of_beq_eq_true e]; exact h1
      | inr hr => exact allG_mem p r h2 c hr

theorem allG_of_all (p : Nat → Bool) : ∀ l : List Nat,
    (∀ c, memN c l = true → p c = true) → allG p l = true
  | [], _ => rfl
  | c' :: r, h => by
      show (p c' && allG p r) = true
      exact andI _ _ (h c' (memN_head c' r))
        (allG_of_all p r (fun c hc => h c (by
          show (Nat.beq c c' || memN c r) = true
          rw [hc]
          cases Nat.beq c c' with
          | true => rfl
          | false => rfl)))

theorem anyG_mem (p : Nat → Bool) : ∀ l : List Nat, anyG p l = true →
    ∃ c, memN c l = true ∧ p c = true
  | [], h => Bool.noConfusion h
  | c' :: r, h => by
      cases orT _ _ h with
      | inl h1 => exact ⟨c', memN_head c' r, h1⟩
      | inr h2 =>
          have ⟨c, hc, hp⟩ := anyG_mem p r h2
          refine ⟨c, ?_, hp⟩
          show (Nat.beq c c' || memN c r) = true
          rw [hc]
          cases Nat.beq c c' with
          | true => rfl
          | false => rfl

theorem anyG_of_mem (p : Nat → Bool) : ∀ l : List Nat, ∀ c, memN c l = true → p c = true →
    anyG p l = true
  | [], _, h, _ => Bool.noConfusion h
  | c' :: r, c, hc, hp => by
      show (p c' || anyG p r) = true
      cases orT _ _ hc with
      | inl e => rw [Nat.eq_of_beq_eq_true e] at hp; rw [hp]; rfl
      | inr hr =>
          rw [anyG_of_mem p r c hr hp]
          cases p c' with
          | true => rfl
          | false => rfl

/-- The evaluator: the greedy tables on the connectives, folds over the
candidates on the quantifiers. -/
def evalQ (b : TBranch) (ρ : Nat → Nat) (d : Nat) : List Nat → QFm → V
  | η, QFm.atom P ts => termI b P (trmVals ρ η d ts)
  | η, QFm.neg φ    => znot (evalQ b ρ d η φ)
  | η, QFm.conj φ ψ => zand (evalQ b ρ d η φ) (evalQ b ρ d η ψ)
  | η, QFm.disj φ ψ => zor (evalQ b ρ d η φ) (evalQ b ρ d η ψ)
  | η, QFm.imp φ ψ  => zimp (evalQ b ρ d η φ) (evalQ b ρ d η ψ)
  | η, QFm.all φ    =>
      match allG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
      | true  => T
      | false => F
  | η, QFm.ex φ     =>
      match anyG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
      | true  => T
      | false => F

/-- **THE EVALUATOR REALISES THE RELATION** on a normalised assignment and
stack. The universal clause is where the finiteness pays: a fold over the
candidates decides `∀ a : Nat` because every `a` normalises to a candidate. -/
theorem holds_evalQ (b : TBranch) :
    ∀ (φ : QFm) (ρ : Nat → Nat), (∀ p, ρ p = norm b (ρ p)) →
    ∀ (d : Nat), d = norm b d → ∀ (η : List Nat), η = mapNorm b η →
      Holds (termI b) ρ d η φ (evalQ b ρ d η φ)
  | QFm.atom P ts, ρ, _, d, _, η, _ => rfl
  | QFm.neg φ, ρ, hρ, d, hd, η, hη =>
      ⟨evalQ b ρ d η φ, holds_evalQ b φ ρ hρ d hd η hη, rfl⟩
  | QFm.conj φ ψ, ρ, hρ, d, hd, η, hη =>
      ⟨evalQ b ρ d η φ, evalQ b ρ d η ψ, holds_evalQ b φ ρ hρ d hd η hη,
       holds_evalQ b ψ ρ hρ d hd η hη, rfl⟩
  | QFm.disj φ ψ, ρ, hρ, d, hd, η, hη =>
      ⟨evalQ b ρ d η φ, evalQ b ρ d η ψ, holds_evalQ b φ ρ hρ d hd η hη,
       holds_evalQ b ψ ρ hρ d hd η hη, rfl⟩
  | QFm.imp φ ψ, ρ, hρ, d, hd, η, hη =>
      ⟨evalQ b ρ d η φ, evalQ b ρ d η ψ, holds_evalQ b φ ρ hρ d hd η hη,
       holds_evalQ b ψ ρ hρ d hd η hη, rfl⟩
  | QFm.all φ, ρ, hρ, d, hd, η, hη => by
      -- a candidate stacked on a normalised stack is a normalised stack
      have hcand : ∀ c, memN c (candidates b) = true → c :: η = mapNorm b (c :: η) := by
        intro c hc
        show c :: η = norm b c :: mapNorm b η
        rw [norm_id b c hc, ← hη]
      -- the fold says T exactly when every instance over Nat is T
      have key : allG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) = true ↔
                 ∀ a, Holds (termI b) ρ d (a :: η) φ T := by
        constructor
        · intro hall a
          have hc := allG_mem _ (candidates b) hall (norm b a) (norm_mem b a)
          have he : evalQ b ρ d (norm b a :: η) φ = T := of_decide_eq_true hc
          have h1 : Holds (termI b) ρ d (norm b a :: η) φ T := by
            have := holds_evalQ b φ ρ hρ d hd (norm b a :: η) (hcand (norm b a) (norm_mem b a))
            rw [he] at this
            exact this
          exact (holds_norm b φ ρ ρ hρ d d hd (a :: η) (norm b a :: η)
            (by show norm b a :: η = norm b a :: mapNorm b η; rw [← hη]) T).mpr h1
        · intro hall
          apply allG_of_all
          intro c hc
          apply decide_eq_true
          have h1 := holds_evalQ b φ ρ hρ d hd (c :: η) (hcand c hc)
          exact holds_det (termI b) ρ d φ (c :: η) _ T h1 (hall c)
      show ((match allG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
              | true => T | false => F) = T ↔ ∀ a, Holds (termI b) ρ d (a :: η) φ T) ∧
           ((match allG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
              | true => T | false => F) = T ∨
            (match allG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
              | true => T | false => F) = F)
      cases hg : allG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
      | true =>
          rw [hg] at key
          exact ⟨⟨fun _ => key.mp rfl, fun _ => rfl⟩, Or.inl rfl⟩
      | false =>
          rw [hg] at key
          exact ⟨⟨fun h => V.noConfusion h,
                  fun hall => Bool.noConfusion (key.mpr hall)⟩, Or.inr rfl⟩
  | QFm.ex φ, ρ, hρ, d, hd, η, hη => by
      have hcand : ∀ c, memN c (candidates b) = true → c :: η = mapNorm b (c :: η) := by
        intro c hc
        show c :: η = norm b c :: mapNorm b η
        rw [norm_id b c hc, ← hη]
      have key : anyG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) = true ↔
                 ∃ a, Holds (termI b) ρ d (a :: η) φ T := by
        constructor
        · intro hany
          have ⟨c, hc, hp⟩ := anyG_mem _ (candidates b) hany
          have he : evalQ b ρ d (c :: η) φ = T := of_decide_eq_true hp
          refine ⟨c, ?_⟩
          have := holds_evalQ b φ ρ hρ d hd (c :: η) (hcand c hc)
          rw [he] at this
          exact this
        · intro ⟨a, ha⟩
          have h1 : Holds (termI b) ρ d (norm b a :: η) φ T :=
            (holds_norm b φ ρ ρ hρ d d hd (a :: η) (norm b a :: η)
              (by show norm b a :: η = norm b a :: mapNorm b η; rw [← hη]) T).mp ha
          have h2 := holds_evalQ b φ ρ hρ d hd (norm b a :: η) (hcand (norm b a) (norm_mem b a))
          have he : evalQ b ρ d (norm b a :: η) φ = T :=
            holds_det (termI b) ρ d φ (norm b a :: η) _ T h2 h1
          exact anyG_of_mem _ (candidates b) (norm b a) (norm_mem b a) (decide_eq_true he)
      show ((match anyG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
              | true => T | false => F) = T ↔ ∃ a, Holds (termI b) ρ d (a :: η) φ T) ∧
           ((match anyG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
              | true => T | false => F) = T ∨
            (match anyG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
              | true => T | false => F) = F)
      cases hg : anyG (fun c => decide (evalQ b ρ d (c :: η) φ = T)) (candidates b) with
      | true =>
          rw [hg] at key
          exact ⟨⟨fun _ => key.mp rfl, fun _ => rfl⟩, Or.inl rfl⟩
      | false =>
          rw [hg] at key
          exact ⟨⟨fun h => V.noConfusion h,
                  fun hex => Bool.noConfusion (key.mpr hex)⟩, Or.inr rfl⟩

/-- **THE TERM MODEL IS TOTAL, for every assignment** — an arbitrary
assignment is first normalised, which changes no verdict. -/
theorem total_term (b : TBranch) : ∀ ρ, Total (termI b) ρ (termd b) := by
  intro ρ φ η
  have hρ' : ∀ p, (fun q => norm b (ρ q)) p = norm b ((fun q => norm b (ρ q)) p) :=
    fun p => (norm_norm b (ρ p)).symm
  have hd' : termd b = norm b (termd b) := termd_norm b
  have hη' : mapNorm b η = mapNorm b (mapNorm b η) := (mapNorm_norm b η).symm
  refine ⟨evalQ b (fun q => norm b (ρ q)) (termd b) (mapNorm b η) φ, ?_⟩
  exact (holds_norm b φ ρ (fun q => norm b (ρ q)) (fun p => rfl) (termd b) (termd b) hd' η
    (mapNorm b η) rfl _).mpr
    (holds_evalQ b φ (fun q => norm b (ρ q)) hρ' (termd b) hd' (mapNorm b η) hη')

/-! ### What an open branch says about clashes -/

theorem clashTag_symm : ∀ a c : Tag, clashTag a c = clashTag c a := by decide
theorem clashTag_refl : ∀ a : Tag, clashTag a a = false := by decide

theorem clashesWith_false (nd : TNode) : ∀ r : TBranch, clashesWith nd r = false →
    ∀ x, x ∈ r → nd.2 = x.2 → clashTag nd.1 x.1 = false
  | [], _, _, h, _ => nomatch h
  | x' :: r, h, x, hx, he => by
      have ⟨h1, h2⟩ := orFF _ _ h
      cases hx with
      | head =>
          rw [decide_eq_true he] at h1
          exact andTrueF _ h1
      | tail _ hx' => exact clashesWith_false nd r h2 x hx' he

/-- **NO TWO CLASHING SIGNS ON ONE FORMULA** — what `closedB b = false` says,
node by node. -/
theorem open_no_clash : ∀ b : TBranch, closedB b = false →
    ∀ x y : TNode, x ∈ b → y ∈ b → x.2 = y.2 → clashTag x.1 y.1 = false
  | [], _, _, _, hx, _, _ => nomatch hx
  | z :: r, h, x, y, hx, hy, he => by
      have ⟨h1, h2⟩ := orFF _ _ h
      cases hx with
      | head =>
          cases hy with
          | head => exact clashTag_refl _
          | tail _ hy' => exact clashesWith_false z r h1 y hy' he
      | tail _ hx' =>
          cases hy with
          | head =>
              rw [clashTag_symm]
              exact clashesWith_false z r h1 x hx' he.symm
          | tail _ hy' => exact open_no_clash r h2 x y hx' hy' he

/-! ### What saturation says, rule by rule -/

theorem anyNew_false : ∀ (ns : List TNode) (b : TBranch), anyNew ns b = false →
    ∀ x, x ∈ ns → memB x b = true
  | [], _, _, _, h => nomatch h
  | x' :: r, b, h, x, hx => by
      have ⟨h1, h2⟩ := orFF _ _ h
      cases hx with
      | head => exact notF _ h1
      | tail _ hx' => exact anyNew_false r b h2 x hx'

theorem one_none {ns : List TNode} {b : TBranch} (h : one ns b = none) :
    ∀ x, x ∈ ns → memB x b = true := by
  unfold one at h
  cases ha : anyNew ns b with
  | true => rw [ha] at h; cases h
  | false => exact anyNew_false ns b ha

theorem two_none {n1 n2 : TNode} {b : TBranch} (h : two n1 n2 b = none) :
    memB n1 b = true ∨ memB n2 b = true := by
  unfold two at h
  cases ha : (!memB n1 b && !memB n2 b) with
  | true => rw [ha] at h; cases h
  | false => exact andFF _ _ ha

theorem firstNew_none (tg : Tag) (φ : QFm) (b : TBranch) : ∀ cs : List Nat,
    firstNew tg φ cs b = none → ∀ c, memN c cs = true → memB (tg, inst c 0 φ) b = true
  | [], _, _, hc => Bool.noConfusion hc
  | c' :: cs, h, c, hc => by
      unfold firstNew at h
      cases hm : memB (tg, inst c' 0 φ) b with
      | false => rw [hm] at h; cases h
      | true =>
          rw [hm] at h
          cases orT _ _ hc with
          | inl e => rw [Nat.eq_of_beq_eq_true e]; exact hm
          | inr hr => exact firstNew_none tg φ b cs h c hr

theorem anyInstance_true (tg : Tag) (φ : QFm) (b : TBranch) : ∀ cs : List Nat,
    anyInstance tg φ cs b = true → ∃ c, memN c cs = true ∧ memB (tg, inst c 0 φ) b = true
  | [], h => Bool.noConfusion h
  | c' :: cs, h => by
      cases orT _ _ h with
      | inl h1 => exact ⟨c', memN_head c' cs, h1⟩
      | inr h2 =>
          have ⟨c, hc, hm⟩ := anyInstance_true tg φ b cs h2
          refine ⟨c, ?_, hm⟩
          show (Nat.beq c c' || memN c cs) = true
          rw [hc]
          cases Nat.beq c c' with
          | true => rfl
          | false => rfl

theorem gammaT_none {φ : QFm} {b : TBranch} (h : gammaT φ b = none) :
    firstNew Tag.t φ (candidates b) b = none := by
  unfold gammaT at h
  cases hf : firstNew Tag.t φ (candidates b) b with
  | some c => rw [hf] at h; cases h
  | none => rfl

theorem gammaF_none {φ : QFm} {b : TBranch} (h : gammaF φ b = none) :
    firstNew Tag.n φ (candidates b) b = none := by
  unfold gammaF at h
  cases hf : firstNew Tag.n φ (candidates b) b with
  | some c => rw [hf] at h; cases h
  | none => rfl

theorem deltaT_none {φ : QFm} {b : TBranch} (h : deltaT φ b = none) :
    ∃ c, memB (Tag.t, inst c 0 φ) b = true := by
  unfold deltaT at h
  cases ha : anyInstance Tag.t φ (candidates b) b with
  | true =>
      have ⟨c, _, hm⟩ := anyInstance_true Tag.t φ b (candidates b) ha
      exact ⟨c, hm⟩
  | false =>
      rw [ha] at h
      exact ⟨fresh b, one_none h _ (List.Mem.head [])⟩

theorem delta2_none {φ : QFm} {b : TBranch} (h : delta2 φ b = none) :
    ∃ c, memB (Tag.n, inst c 0 φ) b = true := by
  unfold delta2 at h
  cases ha : anyInstance Tag.n φ (candidates b) b with
  | true =>
      have ⟨c, _, hm⟩ := anyInstance_true Tag.n φ b (candidates b) ha
      exact ⟨c, hm⟩
  | false =>
      rw [ha] at h
      exact ⟨fresh b, one_none h _ (List.Mem.head [])⟩

/-- The saturation clause of δ₂: every `F:∀xφ` on the branch has an instance
under N. `search true` discharges it by construction (`delta2Sat_of_sat`);
`search false` cannot, and takes it as a hypothesis. -/
def Delta2Sat (b : TBranch) : Prop :=
  ∀ φ, (Tag.f, QFm.all φ) ∈ b → ∃ c, (Tag.n, inst c 0 φ) ∈ b

theorem delta2Sat_of_sat (b : TBranch) (hsat : ∀ nd, nd ∈ b → expand true nd b = none) :
    Delta2Sat b := by
  intro φ hmem
  have h : delta2 φ b = none := hsat _ hmem
  have ⟨c, hc⟩ := delta2_none h
  exact ⟨c, mem_of_memB _ b hc⟩

/-! ### The tables, read backwards — each cell by `decide` -/

theorem znot_F : znot F = T := by decide
theorem znot_weak : ∀ u : V, (u = T ∨ u = Z) → znot u = F := by decide
theorem zand_TT : zand T T = T := by decide
theorem zand_weak_l : ∀ u w : V, (u = F ∨ u = Z) → zand u w = F := by decide
theorem zand_weak_r : ∀ u w : V, (w = F ∨ w = Z) → zand u w = F := by decide
theorem zor_T_l : ∀ w : V, zor T w = T := by decide
theorem zor_T_r : ∀ u : V, zor u T = T := by decide
/-- The cell the proof stands on: `Z ∨ Z = F`. -/
theorem zor_weak : ∀ u w : V, (u = F ∨ u = Z) → (w = F ∨ w = Z) → zor u w = F := by decide
theorem zimp_F_l : ∀ w : V, zimp F w = T := by decide
theorem zimp_T_r : ∀ u : V, zimp u T = T := by decide
theorem zimp_weak : ∀ u w : V, (u = T ∨ u = Z) → (w = F ∨ w = Z) → zimp u w = F := by decide

/-! ### The satisfaction lemma -/

/-- The four clauses, one per tag, for one formula on one branch. -/
def satT (b : TBranch) (φ : QFm) : Prop :=
  (Tag.t, φ) ∈ b → ∃ v, Holds (termI b) (termρ b) (termd b) [] φ v ∧ SignT v = true
def satF (b : TBranch) (φ : QFm) : Prop :=
  (Tag.f, φ) ∈ b → ∃ v, Holds (termI b) (termρ b) (termd b) [] φ v ∧ SignF v = true
def satP (b : TBranch) (φ : QFm) : Prop :=
  (Tag.p, φ) ∈ b → ∃ v, Holds (termI b) (termρ b) (termd b) [] φ v ∧ SignP v = true
def satN (b : TBranch) (φ : QFm) : Prop :=
  (Tag.n, φ) ∈ b → ∃ v, Holds (termI b) (termρ b) (termd b) [] φ v ∧ SignN v = true
def SatAll (b : TBranch) (φ : QFm) : Prop := satT b φ ∧ satF b φ ∧ satP b φ ∧ satN b φ

/-- The parameters of a closed atom on the branch are its own terms, once
read through the model: normalising a candidate is the identity. -/
theorem atom_terms (b : TBranch) : ∀ ts : List Trm, closedL 0 ts = true →
    (∀ c, Trm.par c ∈ ts → memN c (candidates b) = true) →
    parsOf (mapNorm b (trmVals (termρ b) [] (termd b) ts)) = ts
  | [], _, _ => rfl
  | Trm.bvar j :: _, h, _ => by
      have h1 : closedT 0 (Trm.bvar j) = true := (andT _ _ h).1
      have : ltB j 0 = true := h1
      rw [ltB_zero j] at this
      exact Bool.noConfusion this
  | Trm.par c :: r, h, hp => by
      have h2 : closedL 0 r = true := (andT _ _ h).2
      have hc : memN c (candidates b) = true := hp c (List.Mem.head r)
      show Trm.par (norm b (norm b c)) :: parsOf (mapNorm b (trmVals (termρ b) [] (termd b) r))
         = Trm.par c :: r
      rw [norm_norm b c, norm_id b c hc,
          atom_terms b r h2 (fun c' hc' => hp c' (List.Mem.tail _ hc'))]

/-- **ATOMS: what the branch says is what the model says.** The three
clashes of `clashTag` are exactly what keeps the four clauses consistent. -/
theorem sat_atom (b : TBranch) (hopen : closedB b = false) (P : Nat) (ts : List Trm)
    (hc : closedAt 0 (QFm.atom P ts) = true) : SatAll b (QFm.atom P ts) := by
  -- the model's reading of this atom is `atomVal b P ts`, whatever the tag
  have hread : ∀ tg, (tg, QFm.atom P ts) ∈ b →
      Holds (termI b) (termρ b) (termd b) [] (QFm.atom P ts) (atomVal b P ts) := by
    intro tg hmem
    show atomVal b P (parsOf (mapNorm b (trmVals (termρ b) [] (termd b) ts))) = atomVal b P ts
    rw [atom_terms b ts hc (fun c hc' => atom_par_cand b tg P ts c hmem hc')]
  have noclash : ∀ tg tg', (tg, QFm.atom P ts) ∈ b → (tg', QFm.atom P ts) ∈ b →
      clashTag tg tg' = false :=
    fun tg tg' h1 h2 => open_no_clash b hopen _ _ h1 h2 rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmem
    refine ⟨atomVal b P ts, hread Tag.t hmem, ?_⟩
    unfold atomVal
    rw [memB_of_mem _ b hmem]
    show SignT T = true
    decide
  · intro hmem
    refine ⟨atomVal b P ts, hread Tag.f hmem, ?_⟩
    unfold atomVal
    cases ht : memB (Tag.t, QFm.atom P ts) b with
    | true =>
        have := noclash Tag.f Tag.t hmem (mem_of_memB _ b ht)
        exact Bool.noConfusion this
    | false =>
        rw [memB_of_mem _ b hmem]
        show SignF F = true
        decide
  · intro hmem
    refine ⟨atomVal b P ts, hread Tag.p hmem, ?_⟩
    unfold atomVal
    cases ht : memB (Tag.t, QFm.atom P ts) b with
    | true =>
        show SignP T = true
        decide
    | false =>
        cases hf : memB (Tag.f, QFm.atom P ts) b with
        | true =>
            have := noclash Tag.p Tag.f hmem (mem_of_memB _ b hf)
            exact Bool.noConfusion this
        | false =>
            show SignP Z = true
            decide
  · intro hmem
    refine ⟨atomVal b P ts, hread Tag.n hmem, ?_⟩
    unfold atomVal
    cases ht : memB (Tag.t, QFm.atom P ts) b with
    | true =>
        have := noclash Tag.n Tag.t hmem (mem_of_memB _ b ht)
        exact Bool.noConfusion this
    | false =>
        cases hf : memB (Tag.f, QFm.atom P ts) b with
        | true =>
            show SignN F = true
            decide
        | false =>
            show SignN Z = true
            decide

theorem le_succ_pred {a n : Nat} (h : a + 1 ≤ n + 1) : a ≤ n := Nat.le_of_succ_le_succ h

/-- **EVERY NODE OF AN OPEN SATURATED BRANCH IS SATISFIED** in the term
model — by recursion on the size of the formula, each compound read
backwards through its rule. -/
theorem sat_saturated (d2 : Bool) (b : TBranch) (hopen : closedB b = false)
    (hsat : ∀ nd, nd ∈ b → expand d2 nd b = none) (hδ₂ : Delta2Sat b) :
    ∀ (n : Nat) (φ : QFm), size φ ≤ n → closedAt 0 φ = true → SatAll b φ
  | _, QFm.atom P ts, _, hc => sat_atom b hopen P ts hc
  | 0, QFm.neg _, hs, _ => absurd hs (Nat.not_succ_le_zero _)
  | 0, QFm.conj _ _, hs, _ => absurd hs (Nat.not_succ_le_zero _)
  | 0, QFm.disj _ _, hs, _ => absurd hs (Nat.not_succ_le_zero _)
  | 0, QFm.imp _ _, hs, _ => absurd hs (Nat.not_succ_le_zero _)
  | 0, QFm.all _, hs, _ => absurd hs (Nat.not_succ_le_zero _)
  | 0, QFm.ex _, hs, _ => absurd hs (Nat.not_succ_le_zero _)
  | n + 1, QFm.neg φ, hs, hc => by
      have ih := sat_saturated d2 b hopen hsat hδ₂ n φ (le_succ_pred hs) hc
      have ht : satT b (QFm.neg φ) := by
        intro hmem
        have h : one [(Tag.f, φ)] b = none := hsat _ hmem
        have ⟨u, hu, hs'⟩ := ih.2.1 (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        refine ⟨znot u, ⟨u, hu, rfl⟩, ?_⟩
        rw [(vF u).mp hs', znot_F]
        decide
      have hf : satF b (QFm.neg φ) := by
        intro hmem
        have h : one [(Tag.p, φ)] b = none := hsat _ hmem
        have ⟨u, hu, hs'⟩ := ih.2.2.1 (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        refine ⟨znot u, ⟨u, hu, rfl⟩, ?_⟩
        rw [znot_weak u ((vP u).mp hs')]
        decide
      refine ⟨ht, hf, ?_, ?_⟩
      · intro hmem
        have h : one [(Tag.t, QFm.neg φ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := ht (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vT v).mp hs']; decide⟩
      · intro hmem
        have h : one [(Tag.f, QFm.neg φ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := hf (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vF v).mp hs']; decide⟩
  | n + 1, QFm.conj φ ψ, hs, hc => by
      have hs' : size φ + size ψ ≤ n := le_succ_pred hs
      have ⟨hc1, hc2⟩ := andT _ _ hc
      have ih1 := sat_saturated d2 b hopen hsat hδ₂ n φ (le_of_add_le_left hs') hc1
      have ih2 := sat_saturated d2 b hopen hsat hδ₂ n ψ (le_of_add_le_right hs') hc2
      have ht : satT b (QFm.conj φ ψ) := by
        intro hmem
        have h : one [(Tag.t, φ), (Tag.t, ψ)] b = none := hsat _ hmem
        have ⟨u, hu, hsu⟩ := ih1.1 (mem_of_memB _ b (one_none h _ (List.Mem.head _)))
        have ⟨w, hw, hsw⟩ := ih2.1 (mem_of_memB _ b (one_none h _ (List.Mem.tail _ (List.Mem.head _))))
        refine ⟨zand u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
        rw [(vT u).mp hsu, (vT w).mp hsw, zand_TT]
        decide
      have hf : satF b (QFm.conj φ ψ) := by
        intro hmem
        have h : two (Tag.n, φ) (Tag.n, ψ) b = none := hsat _ hmem
        cases two_none h with
        | inl h1 =>
            have ⟨u, hu, hsu⟩ := ih1.2.2.2 (mem_of_memB _ b h1)
            have ⟨w, hw⟩ := total_term b (termρ b) ψ []
            refine ⟨zand u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
            rw [zand_weak_l u w ((vN u).mp hsu)]
            decide
        | inr h2 =>
            have ⟨w, hw, hsw⟩ := ih2.2.2.2 (mem_of_memB _ b h2)
            have ⟨u, hu⟩ := total_term b (termρ b) φ []
            refine ⟨zand u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
            rw [zand_weak_r u w ((vN w).mp hsw)]
            decide
      refine ⟨ht, hf, ?_, ?_⟩
      · intro hmem
        have h : one [(Tag.t, QFm.conj φ ψ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := ht (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vT v).mp hs']; decide⟩
      · intro hmem
        have h : one [(Tag.f, QFm.conj φ ψ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := hf (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vF v).mp hs']; decide⟩
  | n + 1, QFm.disj φ ψ, hs, hc => by
      have hs' : size φ + size ψ ≤ n := le_succ_pred hs
      have ⟨hc1, hc2⟩ := andT _ _ hc
      have ih1 := sat_saturated d2 b hopen hsat hδ₂ n φ (le_of_add_le_left hs') hc1
      have ih2 := sat_saturated d2 b hopen hsat hδ₂ n ψ (le_of_add_le_right hs') hc2
      have ht : satT b (QFm.disj φ ψ) := by
        intro hmem
        have h : two (Tag.t, φ) (Tag.t, ψ) b = none := hsat _ hmem
        cases two_none h with
        | inl h1 =>
            have ⟨u, hu, hsu⟩ := ih1.1 (mem_of_memB _ b h1)
            have ⟨w, hw⟩ := total_term b (termρ b) ψ []
            refine ⟨zor u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
            rw [(vT u).mp hsu, zor_T_l]
            decide
        | inr h2 =>
            have ⟨w, hw, hsw⟩ := ih2.1 (mem_of_memB _ b h2)
            have ⟨u, hu⟩ := total_term b (termρ b) φ []
            refine ⟨zor u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
            rw [(vT w).mp hsw, zor_T_r]
            decide
      have hf : satF b (QFm.disj φ ψ) := by
        intro hmem
        have h : one [(Tag.n, φ), (Tag.n, ψ)] b = none := hsat _ hmem
        have ⟨u, hu, hsu⟩ := ih1.2.2.2 (mem_of_memB _ b (one_none h _ (List.Mem.head _)))
        have ⟨w, hw, hsw⟩ := ih2.2.2.2 (mem_of_memB _ b (one_none h _ (List.Mem.tail _ (List.Mem.head _))))
        refine ⟨zor u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
        rw [zor_weak u w ((vN u).mp hsu) ((vN w).mp hsw)]
        decide
      refine ⟨ht, hf, ?_, ?_⟩
      · intro hmem
        have h : one [(Tag.t, QFm.disj φ ψ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := ht (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vT v).mp hs']; decide⟩
      · intro hmem
        have h : one [(Tag.f, QFm.disj φ ψ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := hf (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vF v).mp hs']; decide⟩
  | n + 1, QFm.imp φ ψ, hs, hc => by
      have hs' : size φ + size ψ ≤ n := le_succ_pred hs
      have ⟨hc1, hc2⟩ := andT _ _ hc
      have ih1 := sat_saturated d2 b hopen hsat hδ₂ n φ (le_of_add_le_left hs') hc1
      have ih2 := sat_saturated d2 b hopen hsat hδ₂ n ψ (le_of_add_le_right hs') hc2
      have ht : satT b (QFm.imp φ ψ) := by
        intro hmem
        have h : two (Tag.f, φ) (Tag.t, ψ) b = none := hsat _ hmem
        cases two_none h with
        | inl h1 =>
            have ⟨u, hu, hsu⟩ := ih1.2.1 (mem_of_memB _ b h1)
            have ⟨w, hw⟩ := total_term b (termρ b) ψ []
            refine ⟨zimp u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
            rw [(vF u).mp hsu, zimp_F_l]
            decide
        | inr h2 =>
            have ⟨w, hw, hsw⟩ := ih2.1 (mem_of_memB _ b h2)
            have ⟨u, hu⟩ := total_term b (termρ b) φ []
            refine ⟨zimp u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
            rw [(vT w).mp hsw, zimp_T_r]
            decide
      have hf : satF b (QFm.imp φ ψ) := by
        intro hmem
        have h : one [(Tag.p, φ), (Tag.n, ψ)] b = none := hsat _ hmem
        have ⟨u, hu, hsu⟩ := ih1.2.2.1 (mem_of_memB _ b (one_none h _ (List.Mem.head _)))
        have ⟨w, hw, hsw⟩ := ih2.2.2.2 (mem_of_memB _ b (one_none h _ (List.Mem.tail _ (List.Mem.head _))))
        refine ⟨zimp u w, ⟨u, w, hu, hw, rfl⟩, ?_⟩
        rw [zimp_weak u w ((vP u).mp hsu) ((vN w).mp hsw)]
        decide
      refine ⟨ht, hf, ?_, ?_⟩
      · intro hmem
        have h : one [(Tag.t, QFm.imp φ ψ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := ht (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vT v).mp hs']; decide⟩
      · intro hmem
        have h : one [(Tag.f, QFm.imp φ ψ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := hf (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vF v).mp hs']; decide⟩
  | n + 1, QFm.all φ, hs, hc => by
      have hsn : size φ ≤ n := le_succ_pred hs
      -- an instance is closed and no bigger, so the recursion reaches it
      have inst_ih : ∀ c, SatAll b (inst c 0 φ) := fun c =>
        sat_saturated d2 b hopen hsat hδ₂ n (inst c 0 φ)
          (by rw [size_inst]; exact hsn) (closed_inst c φ 0 hc)
      -- a verdict on an instance is a verdict on the formula at that value
      have unfold_inst : ∀ (c : Nat) (v : V),
          Holds (termI b) (termρ b) (termd b) [] (inst c 0 φ) v →
          Holds (termI b) (termρ b) (termd b) (termρ b c :: []) φ v :=
        fun c v h => (holds_inst (termI b) (termρ b) (termd b) c φ [] v 0).mp h
      have fold_inst : ∀ (c : Nat) (v : V),
          Holds (termI b) (termρ b) (termd b) (termρ b c :: []) φ v →
          Holds (termI b) (termρ b) (termd b) [] (inst c 0 φ) v :=
        fun c v h => (holds_inst (termI b) (termρ b) (termd b) c φ [] v 0).mpr h
      -- and a verdict at `norm a` is a verdict at `a`
      have at_norm : ∀ (a : Nat) (v : V),
          Holds (termI b) (termρ b) (termd b) (norm b a :: []) φ v ↔
          Holds (termI b) (termρ b) (termd b) (a :: []) φ v :=
        fun a v => (holds_norm b φ (termρ b) (termρ b) (termρ_norm b) (termd b) (termd b)
          (termd_norm b) (a :: []) (norm b a :: []) rfl v).symm
      have ht : satT b (QFm.all φ) := by
        intro hmem
        have h : gammaT φ b = none := hsat _ hmem
        have hall : ∀ a, Holds (termI b) (termρ b) (termd b) (a :: []) φ T := by
          intro a
          have hm := firstNew_none Tag.t φ b (candidates b) (gammaT_none h) (norm b a) (norm_mem b a)
          have ⟨u, hu, hsu⟩ := (inst_ih (norm b a)).1 (mem_of_memB _ b hm)
          rw [(vT u).mp hsu] at hu
          have h1 := unfold_inst (norm b a) T hu
          have h2 : termρ b (norm b a) = norm b a := norm_norm b a
          rw [h2] at h1
          exact (at_norm a T).mp h1
        exact ⟨T, ⟨⟨fun _ => hall, fun _ => rfl⟩, Or.inl rfl⟩, rfl⟩
      have hf : satF b (QFm.all φ) := by
        intro hmem
        have ⟨c, hcm⟩ := hδ₂ φ hmem
        have ⟨w, hw, hsw⟩ := (inst_ih c).2.2.2 hcm
        have hwT : ¬ w = T := (vN_neq w).mp ((vN w).mp hsw)
        refine ⟨F, ⟨⟨fun h => V.noConfusion h, fun hall => ?_⟩, Or.inr rfl⟩, rfl⟩
        have h1 : Holds (termI b) (termρ b) (termd b) [] (inst c 0 φ) T :=
          fold_inst c T (hall (termρ b c))
        exact absurd (holds_det (termI b) (termρ b) (termd b) (inst c 0 φ) [] w T hw h1) hwT
      refine ⟨ht, hf, ?_, ?_⟩
      · intro hmem
        have h : one [(Tag.t, QFm.all φ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := ht (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vT v).mp hs']; decide⟩
      · intro hmem
        have h : one [(Tag.f, QFm.all φ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := hf (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vF v).mp hs']; decide⟩
  | n + 1, QFm.ex φ, hs, hc => by
      have hsn : size φ ≤ n := le_succ_pred hs
      have inst_ih : ∀ c, SatAll b (inst c 0 φ) := fun c =>
        sat_saturated d2 b hopen hsat hδ₂ n (inst c 0 φ)
          (by rw [size_inst]; exact hsn) (closed_inst c φ 0 hc)
      have unfold_inst : ∀ (c : Nat) (v : V),
          Holds (termI b) (termρ b) (termd b) [] (inst c 0 φ) v →
          Holds (termI b) (termρ b) (termd b) (termρ b c :: []) φ v :=
        fun c v h => (holds_inst (termI b) (termρ b) (termd b) c φ [] v 0).mp h
      have at_norm : ∀ (a : Nat) (v : V),
          Holds (termI b) (termρ b) (termd b) (norm b a :: []) φ v ↔
          Holds (termI b) (termρ b) (termd b) (a :: []) φ v :=
        fun a v => (holds_norm b φ (termρ b) (termρ b) (termρ_norm b) (termd b) (termd b)
          (termd_norm b) (a :: []) (norm b a :: []) rfl v).symm
      have ht : satT b (QFm.ex φ) := by
        intro hmem
        have h : deltaT φ b = none := hsat _ hmem
        have ⟨c, hcm⟩ := deltaT_none h
        have ⟨u, hu, hsu⟩ := (inst_ih c).1 (mem_of_memB _ b hcm)
        rw [(vT u).mp hsu] at hu
        exact ⟨T, ⟨⟨fun _ => ⟨termρ b c, unfold_inst c T hu⟩, fun _ => rfl⟩, Or.inl rfl⟩, rfl⟩
      have hf : satF b (QFm.ex φ) := by
        intro hmem
        have h : gammaF φ b = none := hsat _ hmem
        refine ⟨F, ⟨⟨fun h' => V.noConfusion h', fun hex => ?_⟩, Or.inr rfl⟩, rfl⟩
        have ⟨a, ha⟩ := hex
        have ha' := (at_norm a T).mpr ha
        have hm := firstNew_none Tag.n φ b (candidates b) (gammaF_none h) (norm b a) (norm_mem b a)
        have ⟨w, hw, hsw⟩ := (inst_ih (norm b a)).2.2.2 (mem_of_memB _ b hm)
        have hwT : ¬ w = T := (vN_neq w).mp ((vN w).mp hsw)
        have h1 := unfold_inst (norm b a) w hw
        have h2 : termρ b (norm b a) = norm b a := norm_norm b a
        rw [h2] at h1
        exact absurd (holds_det (termI b) (termρ b) (termd b) φ (norm b a :: []) w T h1 ha') hwT
      refine ⟨ht, hf, ?_, ?_⟩
      · intro hmem
        have h : one [(Tag.t, QFm.ex φ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := ht (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vT v).mp hs']; decide⟩
      · intro hmem
        have h : one [(Tag.f, QFm.ex φ)] b = none := hsat _ hmem
        have ⟨v, hv, hs'⟩ := hf (mem_of_memB _ b (one_none h _ (List.Mem.head [])))
        exact ⟨v, hv, by rw [(vF v).mp hs']; decide⟩

/-! ### From a stuck run to its open saturated branch -/

theorem memT_append_left {x : TNode} : ∀ {l r : List TNode}, x ∈ l → x ∈ l ++ r
  | y :: l, r, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail y (memT_append_left h')

theorem memT_append_right {x : TNode} : ∀ {l r : List TNode}, x ∈ r → x ∈ l ++ r
  | [], _, h => h
  | y :: _, _, h => List.Mem.tail y (memT_append_right h)

theorem memBr_append_split {x : TBranch} : ∀ {l r : List TBranch}, x ∈ l ++ r → x ∈ l ∨ x ∈ r
  | [], _, h => Or.inr h
  | y :: l, r, h => by
      cases h with
      | head => exact Or.inl (List.Mem.head l)
      | tail _ h' =>
          cases memBr_append_split h' with
          | inl hl => exact Or.inl (List.Mem.tail y hl)
          | inr hr => exact Or.inr hr

/-- **A STEP ONLY ADDS.** Every node of the branch is on every successor. -/
theorem expand_extends (d2 : Bool) : ∀ (nd : TNode) (b : TBranch) (succs : List TBranch),
    expand d2 nd b = some succs → ∀ s, s ∈ succs → ∀ x, x ∈ b → x ∈ s
  | (Tag.t, QFm.atom _ _), _, _, h => nomatch h
  | (Tag.t, QFm.neg φ), b, succs, h => by
      have h' : one [(Tag.f, φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.t, QFm.conj φ ψ), b, succs, h => by
      have h' : one [(Tag.t, φ), (Tag.t, ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.t, QFm.disj φ ψ), b, succs, h => by
      have h' : two (Tag.t, φ) (Tag.t, ψ) b = some succs := h
      rw [two_sound h']
      intro s hs x hx
      cases hs with
      | head => exact List.Mem.tail _ hx
      | tail _ hs' =>
          cases hs' with
          | head => exact List.Mem.tail _ hx
          | tail _ hs'' => nomatch hs''
  | (Tag.t, QFm.imp φ ψ), b, succs, h => by
      have h' : two (Tag.f, φ) (Tag.t, ψ) b = some succs := h
      rw [two_sound h']
      intro s hs x hx
      cases hs with
      | head => exact List.Mem.tail _ hx
      | tail _ hs' =>
          cases hs' with
          | head => exact List.Mem.tail _ hx
          | tail _ hs'' => nomatch hs''
  | (Tag.t, QFm.all φ), b, succs, h => by
      have h' : gammaT φ b = some succs := h
      have ⟨c, e⟩ := gammaT_sound h'
      rw [e]
      intro s hs x hx
      cases hs with
      | head => exact List.Mem.tail _ hx
      | tail _ hs' => nomatch hs'
  | (Tag.t, QFm.ex φ), b, succs, h => by
      have h' : deltaT φ b = some succs := h
      rw [deltaT_sound h']
      intro s hs x hx
      cases hs with
      | head => exact List.Mem.tail _ hx
      | tail _ hs' => nomatch hs'
  | (Tag.f, QFm.atom _ _), _, _, h => nomatch h
  | (Tag.f, QFm.neg φ), b, succs, h => by
      have h' : one [(Tag.p, φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.f, QFm.conj φ ψ), b, succs, h => by
      have h' : two (Tag.n, φ) (Tag.n, ψ) b = some succs := h
      rw [two_sound h']
      intro s hs x hx
      cases hs with
      | head => exact List.Mem.tail _ hx
      | tail _ hs' =>
          cases hs' with
          | head => exact List.Mem.tail _ hx
          | tail _ hs'' => nomatch hs''
  | (Tag.f, QFm.disj φ ψ), b, succs, h => by
      have h' : one [(Tag.n, φ), (Tag.n, ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.f, QFm.imp φ ψ), b, succs, h => by
      have h' : one [(Tag.p, φ), (Tag.n, ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.f, QFm.all φ), b, succs, h => by
      cases hd : d2 with
      | false =>
          rw [hd] at h
          have h' : (none : Option (List TBranch)) = some succs := h
          nomatch h'
      | true =>
          rw [hd] at h
          have h' : delta2 φ b = some succs := h
          rw [delta2_sound h']
          intro s hs x hx
          cases hs with
          | head => exact List.Mem.tail _ hx
          | tail _ hs' => nomatch hs'
  | (Tag.f, QFm.ex φ), b, succs, h => by
      have h' : gammaF φ b = some succs := h
      have ⟨c, e⟩ := gammaF_sound h'
      rw [e]
      intro s hs x hx
      cases hs with
      | head => exact List.Mem.tail _ hx
      | tail _ hs' => nomatch hs'
  | (Tag.p, QFm.atom _ _), _, _, h => nomatch h
  | (Tag.p, QFm.neg φ), b, succs, h => by
      have h' : one [(Tag.t, QFm.neg φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.p, QFm.conj φ ψ), b, succs, h => by
      have h' : one [(Tag.t, QFm.conj φ ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.p, QFm.disj φ ψ), b, succs, h => by
      have h' : one [(Tag.t, QFm.disj φ ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.p, QFm.imp φ ψ), b, succs, h => by
      have h' : one [(Tag.t, QFm.imp φ ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.p, QFm.all φ), b, succs, h => by
      have h' : one [(Tag.t, QFm.all φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.p, QFm.ex φ), b, succs, h => by
      have h' : one [(Tag.t, QFm.ex φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.n, QFm.atom _ _), _, _, h => nomatch h
  | (Tag.n, QFm.neg φ), b, succs, h => by
      have h' : one [(Tag.f, QFm.neg φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.n, QFm.conj φ ψ), b, succs, h => by
      have h' : one [(Tag.f, QFm.conj φ ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.n, QFm.disj φ ψ), b, succs, h => by
      have h' : one [(Tag.f, QFm.disj φ ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.n, QFm.imp φ ψ), b, succs, h => by
      have h' : one [(Tag.f, QFm.imp φ ψ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.n, QFm.all φ), b, succs, h => by
      have h' : one [(Tag.f, QFm.all φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'
  | (Tag.n, QFm.ex φ), b, succs, h => by
      have h' : one [(Tag.f, QFm.ex φ)] b = some succs := h
      rw [one_sound h']
      intro s hs x hx
      cases hs with
      | head => exact memT_append_right hx
      | tail _ hs' => nomatch hs'

theorem pick_extends (d2 : Bool) : ∀ (scan b : TBranch) (succs : List TBranch),
    pick d2 scan b = some succs → ∀ s, s ∈ succs → ∀ x, x ∈ b → x ∈ s
  | [], _, _, h => nomatch h
  | nd :: r, b, succs, h => by
      unfold pick at h
      cases hexp : expand d2 nd b with
      | some s' =>
          rw [hexp] at h
          rw [← Option.some.inj h]
          exact expand_extends d2 nd b s' hexp
      | none =>
          rw [hexp] at h
          exact pick_extends d2 r b succs h

theorem pick_none (d2 : Bool) : ∀ (scan b : TBranch), pick d2 scan b = none →
    ∀ nd, nd ∈ scan → expand d2 nd b = none
  | [], _, _, _, h => nomatch h
  | nd' :: r, b, h, nd, hnd => by
      unfold pick at h
      cases hexp : expand d2 nd' b with
      | some s' => rw [hexp] at h; cases h
      | none =>
          rw [hexp] at h
          cases hnd with
          | head => exact hexp
          | tail _ hnd' => exact pick_none d2 r b h nd hnd'

/-- **A STUCK RUN EXPOSES ITS BRANCH:** open, saturated, and extending one
of the branches the run started from. -/
theorem stuck_branch (d2 : Bool) : ∀ (fuel : Nat) (bs : List TBranch),
    search d2 fuel bs = Verdict.stuck →
    ∃ b, closedB b = false ∧ (∀ nd, nd ∈ b → expand d2 nd b = none) ∧
      ∃ b0, b0 ∈ bs ∧ ∀ x, x ∈ b0 → x ∈ b
  | 0, [], h => nomatch h
  | _ + 1, [], h => nomatch h
  | 0, _ :: _, h => nomatch h
  | fuel + 1, b0 :: rest, h => by
      unfold search at h
      cases hc : closedB b0 with
      | true =>
          rw [hc] at h
          have ⟨b, hopen, hsat, b1, hb1, hsub⟩ := stuck_branch d2 fuel rest h
          exact ⟨b, hopen, hsat, b1, List.Mem.tail b0 hb1, hsub⟩
      | false =>
          rw [hc] at h
          cases hp : pick d2 (revB b0) b0 with
          | some succs =>
              rw [hp] at h
              have ⟨b, hopen, hsat, b1, hb1, hsub⟩ := stuck_branch d2 fuel (succs ++ rest) h
              cases memBr_append_split hb1 with
              | inl hl =>
                  refine ⟨b, hopen, hsat, b0, List.Mem.head rest, ?_⟩
                  intro x hx
                  exact hsub x (pick_extends d2 (revB b0) b0 succs hp b1 hl x hx)
              | inr hr => exact ⟨b, hopen, hsat, b1, List.Mem.tail b0 hr, hsub⟩
          | none =>
              rw [hp] at h
              refine ⟨b0, hc, ?_, b0, List.Mem.head rest, fun _ hx => hx⟩
              intro nd hnd
              exact pick_none d2 (revB b0) b0 hp nd (mem_revB_of_mem hnd)

/-! ### The theorem -/

theorem mem_tagAll : ∀ (Γ : List QFm) (γ : QFm), γ ∈ Γ → (Tag.t, γ) ∈ tagAll Γ
  | γ' :: r, γ, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (mem_tagAll r γ h')

/-- **THE HINTIKKA LEMMA.** An open saturated branch extending `Γ ⊢ φ`, with
its δ₂ clause discharged, refutes the sequent: a total finite model makes
every premise T and the conclusion not T. On the empty axiom list. -/
theorem countermodel_of_saturated (d2 : Bool) (Γ : List QFm) (φ : QFm) (b : TBranch)
    (hopen : closedB b = false) (hsat : ∀ nd, nd ∈ b → expand d2 nd b = none)
    (hδ₂ : Delta2Sat b) (hsub : ∀ x, x ∈ initBranch Γ φ → x ∈ b)
    (hΓc : ∀ γ, γ ∈ Γ → closedAt 0 γ = true) (hφc : closedAt 0 φ = true) :
    (∀ ρ', Total (termI b) ρ' (termd b)) ∧
    (∀ γ, γ ∈ Γ → Holds (termI b) (termρ b) (termd b) [] γ T) ∧
    ¬ Holds (termI b) (termρ b) (termd b) [] φ T := by
  refine ⟨total_term b, ?_, ?_⟩
  · intro γ hγ
    have hmem : (Tag.t, γ) ∈ b := hsub _ (List.Mem.tail _ (mem_tagAll Γ γ hγ))
    have ⟨v, hv, hs⟩ :=
      (sat_saturated d2 b hopen hsat hδ₂ (size γ) γ (Nat.le_refl _) (hΓc γ hγ)).1 hmem
    rw [(vT v).mp hs] at hv
    exact hv
  · intro hT
    have hmem : (Tag.n, φ) ∈ b := hsub _ (List.Mem.head _)
    have ⟨w, hw, hs⟩ :=
      (sat_saturated d2 b hopen hsat hδ₂ (size φ) φ (Nat.le_refl _) hφc).2.2.2 hmem
    have hwT : ¬ w = T := (vN_neq w).mp ((vN w).mp hs)
    exact hwT (holds_det (termI b) (termρ b) (termd b) φ [] w T hw hT)

/-- **A STUCK RUN WITH δ₂ IS A COUNTERMODEL.** For closed Γ and φ: if
`search true` stops open, there is a total model over `Nat` making every
premise T and φ not T — so Γ ⊬ φ, in the sense `entails_of_closed` proves. -/
theorem stuck_refutes (Γ : List QFm) (φ : QFm) (fuel : Nat)
    (h : search true fuel [initBranch Γ φ] = Verdict.stuck)
    (hΓc : ∀ γ, γ ∈ Γ → closedAt 0 γ = true) (hφc : closedAt 0 φ = true) :
    ∃ (I : Nat → List Nat → V) (d : Nat) (ρ : Nat → Nat),
      (∀ ρ', Total I ρ' d) ∧ (∀ γ, γ ∈ Γ → Holds I ρ d [] γ T) ∧ ¬ Holds I ρ d [] φ T := by
  have ⟨b, hopen, hsat, b0, hb0, hsub⟩ := stuck_branch true fuel [initBranch Γ φ] h
  have hb0' : b0 = initBranch Γ φ := by
    cases hb0 with
    | head => rfl
    | tail _ h' => nomatch h'
  rw [hb0'] at hsub
  exact ⟨termI b, termd b, termρ b,
    countermodel_of_saturated true Γ φ b hopen hsat (delta2Sat_of_sat b hsat) hsub hΓc hφc⟩

/-- **SOUNDNESS AND THIS HALF OF COMPLETENESS, FACE TO FACE.** With δ₂, for
closed inputs: a closed run proves the sequent under the classical
hypothesis; a stuck run refutes it with no hypothesis at all. The one rule
is classical in the first direction and free in the second. -/
theorem closed_or_stuck_decides (Γ : List QFm) (φ : QFm) (fuel : Nat)
    (hΓc : ∀ γ, γ ∈ Γ → closedAt 0 γ = true) (hφc : closedAt 0 φ = true) :
    (search true fuel [initBranch Γ φ] = Verdict.closed →
      ∀ (I : Nat → List α → V) (d : α), (∀ ρ, Total I ρ d) → Delta2Step I d →
        ∀ ρ, (∀ γ, γ ∈ Γ → Holds I ρ d [] γ T) → Holds I ρ d [] φ T) ∧
    (search true fuel [initBranch Γ φ] = Verdict.stuck →
      ∃ (I : Nat → List Nat → V) (d : Nat) (ρ : Nat → Nat),
        (∀ ρ', Total I ρ' d) ∧ (∀ γ, γ ∈ Γ → Holds I ρ d [] γ T) ∧ ¬ Holds I ρ d [] φ T) :=
  ⟨fun h I d htot hδ ρ hΓ => entails_of_closed Γ φ true fuel h I d htot (fun _ => hδ) ρ hΓ,
   fun h => stuck_refutes Γ φ fuel h hΓc hφc⟩

end ZParamHintikka

#print axioms ZParamHintikka.size_inst
#print axioms ZParamHintikka.closed_inst
#print axioms ZParamHintikka.holds_norm
#print axioms ZParamHintikka.holds_evalQ
#print axioms ZParamHintikka.total_term
#print axioms ZParamHintikka.open_no_clash
#print axioms ZParamHintikka.delta2Sat_of_sat
#print axioms ZParamHintikka.zor_weak
#print axioms ZParamHintikka.sat_atom
#print axioms ZParamHintikka.sat_saturated
#print axioms ZParamHintikka.expand_extends
#print axioms ZParamHintikka.stuck_branch
#print axioms ZParamHintikka.countermodel_of_saturated
#print axioms ZParamHintikka.stuck_refutes
#print axioms ZParamHintikka.closed_or_stuck_decides
