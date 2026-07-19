/-!
# EpochBoundary — the Epoch Boundary Theorem, machine-checked

The first joint scientific object of the ZTL / Institutional Computation
collaboration (named by A., 2026-07-18), within its agreed claim ceiling:
everything below is stated INSIDE this model — markings over {T, F, Z},
the greedy ZTL evaluation, and two event kinds:

    verify  : a mark Z resolves to an earned classical value
              (epistemic refinement — learning about the same world);
    expire  : an earned value returns to Z
              (a validity-changing event — the world becoming different).

`Reach` is the reflexive-transitive closure of single legal events. A
verdict is **epoch-blind** at `m` if it is invariant along EVERY such
path — i.e. if the protocol refuses to distinguish learning from world
change.

**Theorem `epoch_boundary_iff`** (the Epoch Boundary Theorem): a verdict
is epoch-blind iff it is CONSTANT over all markings whatsoever — i.e.
iff the assertion reads none of its grounds (a frame; a test that cannot
fail). Contentful conclusions cannot survive unrestricted epoch
crossing: the empirical census of the stand `zexpire.py` (2,906
formulas, 0 contentful survivors) is here replaced by a structural
proof for EVERY formula of the language — not an enumeration.

**Theorem `epochs_matter`** (the separation): there is a formula and a
marking that are `Hereditary` (invariant under every epistemic
refinement — the intra-epoch warranty of `ZTime.lean`) yet NOT
epoch-blind. So the intra-epoch warranty and cross-epoch persistence
are provably different notions, and the epoch boundary is not an
administrative convenience but a logical necessity: a protocol that
does not distinguish learning more about the same world from the world
becoming different can keep non-trivial guarantees only for
tautological conclusions.

VR discipline: self-contained (no imports, no mathlib); `#print axioms`
at the end — the whole file must stand on the EMPTY axiom list. The
proofs are structural (pointwise invariants; no function
extensionality, no decide over infinite spaces).
-/

namespace EpochBoundary

inductive V where
  | T
  | F
  | Z
deriving DecidableEq, Repr

namespace V

def subs : V → List Bool
  | T => [true]
  | F => [false]
  | Z => [true, false]

def lift1 (f : Bool → Bool) (x : V) : V :=
  if (subs x).all (fun a => f a) then T else F

def lift2 (f : Bool → Bool → Bool) (x y : V) : V :=
  if (subs x).all (fun a => (subs y).all (fun b => f a b)) then T else F

def znot  : V → V     := lift1 (fun a => !a)
def zand  : V → V → V := lift2 (fun a b => a && b)
def zor   : V → V → V := lift2 (fun a b => a || b)
def zimp  : V → V → V := lift2 (fun a b => !a || b)
def zxor  : V → V → V := lift2 (fun a b => a != b)
def zxnor : V → V → V := lift2 (fun a b => a == b)

end V

open V

inductive Fm where
  | atom : Nat → Fm
  | neg  : Fm → Fm
  | conj : Fm → Fm → Fm
  | disj : Fm → Fm → Fm
  | imp  : Fm → Fm → Fm
  | xor  : Fm → Fm → Fm
  | xnor : Fm → Fm → Fm
  | top  : Fm
  | bot  : Fm

def Marking := Nat → V

def evalF (m : Marking) : Fm → V
  | .atom n   => m n
  | .top      => V.T
  | .bot      => V.F
  | .neg φ    => znot (evalF m φ)
  | .conj φ ψ => zand (evalF m φ) (evalF m ψ)
  | .disj φ ψ => zor (evalF m φ) (evalF m ψ)
  | .imp φ ψ  => zimp (evalF m φ) (evalF m ψ)
  | .xor φ ψ  => zxor (evalF m φ) (evalF m ψ)
  | .xnor φ ψ => zxnor (evalF m φ) (evalF m ψ)

/-! ## Occurrence and the congruence of evaluation -/

/-- Does atom `n` occur in the formula? Executable, no list machinery. -/
def occursB (n : Nat) : Fm → Bool
  | .atom k   => if n = k then true else false
  | .top      => false
  | .bot      => false
  | .neg φ    => occursB n φ
  | .conj φ ψ => occursB n φ || occursB n ψ
  | .disj φ ψ => occursB n φ || occursB n ψ
  | .imp φ ψ  => occursB n φ || occursB n ψ
  | .xor φ ψ  => occursB n φ || occursB n ψ
  | .xnor φ ψ => occursB n φ || occursB n ψ

theorem or_true_elim {a b : Bool} (h : (a || b) = true) :
    a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem or_intro_left {a : Bool} (b : Bool) (h : a = true) :
    (a || b) = true := by
  rw [h]; rfl

theorem or_intro_right (a : Bool) {b : Bool} (h : b = true) :
    (a || b) = true := by
  rw [h]; cases a <;> rfl

/-- Evaluation reads the marking only at occurring atoms. -/
theorem evalF_congr_on {m1 m2 : Marking} :
    ∀ φ : Fm, (∀ n, occursB n φ = true → m1 n = m2 n) →
    evalF m1 φ = evalF m2 φ := by
  intro φ
  induction φ with
  | atom k =>
      intro h
      show m1 k = m2 k
      apply h k
      show (if k = k then true else false) = true
      rw [if_pos rfl]
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih =>
      intro h
      show znot (evalF m1 φ) = znot (evalF m2 φ)
      rw [ih (fun n hn => h n hn)]
  | conj φ ψ ihφ ihψ =>
      intro h
      show zand (evalF m1 φ) (evalF m1 ψ) = zand (evalF m2 φ) (evalF m2 ψ)
      rw [ihφ (fun n hn => h n (or_intro_left _ hn)),
          ihψ (fun n hn => h n (or_intro_right _ hn))]
  | disj φ ψ ihφ ihψ =>
      intro h
      show zor (evalF m1 φ) (evalF m1 ψ) = zor (evalF m2 φ) (evalF m2 ψ)
      rw [ihφ (fun n hn => h n (or_intro_left _ hn)),
          ihψ (fun n hn => h n (or_intro_right _ hn))]
  | imp φ ψ ihφ ihψ =>
      intro h
      show zimp (evalF m1 φ) (evalF m1 ψ) = zimp (evalF m2 φ) (evalF m2 ψ)
      rw [ihφ (fun n hn => h n (or_intro_left _ hn)),
          ihψ (fun n hn => h n (or_intro_right _ hn))]
  | xor φ ψ ihφ ihψ =>
      intro h
      show zxor (evalF m1 φ) (evalF m1 ψ) = zxor (evalF m2 φ) (evalF m2 ψ)
      rw [ihφ (fun n hn => h n (or_intro_left _ hn)),
          ihψ (fun n hn => h n (or_intro_right _ hn))]
  | xnor φ ψ ihφ ihψ =>
      intro h
      show zxnor (evalF m1 φ) (evalF m1 ψ) = zxnor (evalF m2 φ) (evalF m2 ψ)
      rw [ihφ (fun n hn => h n (or_intro_left _ hn)),
          ihψ (fun n hn => h n (or_intro_right _ hn))]

/-- A syntactic bound on the occurring atoms (sum avoids max-lemmas). -/
def atomBound : Fm → Nat
  | .atom n   => n
  | .top      => 0
  | .bot      => 0
  | .neg φ    => atomBound φ
  | .conj φ ψ => atomBound φ + atomBound ψ
  | .disj φ ψ => atomBound φ + atomBound ψ
  | .imp φ ψ  => atomBound φ + atomBound ψ
  | .xor φ ψ  => atomBound φ + atomBound ψ
  | .xnor φ ψ => atomBound φ + atomBound ψ

theorem occurs_le_bound {n : Nat} :
    ∀ φ : Fm, occursB n φ = true → n ≤ atomBound φ := by
  intro φ
  induction φ with
  | atom k =>
      intro h
      show n ≤ k
      by_cases hk : n = k
      · exact hk ▸ Nat.le_refl n
      · exact absurd h (by show (if n = k then true else false) ≠ true
                           rw [if_neg hk]
                           intro hh
                           exact Bool.noConfusion hh)
  | top => intro h; exact Bool.noConfusion h
  | bot => intro h; exact Bool.noConfusion h
  | neg φ ih => intro h; exact ih h
  | conj φ ψ ihφ ihψ =>
      intro h
      cases or_true_elim h with
      | inl hl => exact Nat.le_trans (ihφ hl) (Nat.le_add_right _ _)
      | inr hr => exact Nat.le_trans (ihψ hr) (Nat.le_add_left _ _)
  | disj φ ψ ihφ ihψ =>
      intro h
      cases or_true_elim h with
      | inl hl => exact Nat.le_trans (ihφ hl) (Nat.le_add_right _ _)
      | inr hr => exact Nat.le_trans (ihψ hr) (Nat.le_add_left _ _)
  | imp φ ψ ihφ ihψ =>
      intro h
      cases or_true_elim h with
      | inl hl => exact Nat.le_trans (ihφ hl) (Nat.le_add_right _ _)
      | inr hr => exact Nat.le_trans (ihψ hr) (Nat.le_add_left _ _)
  | xor φ ψ ihφ ihψ =>
      intro h
      cases or_true_elim h with
      | inl hl => exact Nat.le_trans (ihφ hl) (Nat.le_add_right _ _)
      | inr hr => exact Nat.le_trans (ihψ hr) (Nat.le_add_left _ _)
  | xnor φ ψ ihφ ihψ =>
      intro h
      cases or_true_elim h with
      | inl hl => exact Nat.le_trans (ihφ hl) (Nat.le_add_right _ _)
      | inr hr => exact Nat.le_trans (ihψ hr) (Nat.le_add_left _ _)

/-! ## The two event kinds and the epoch-crossing reachability -/

def update (m : Marking) (a : Nat) (t : V) : Marking :=
  fun n => if n = a then t else m n

/-- One legal event: an epistemic refinement (verify) or a
validity-changing event (expire). -/
inductive Step : Marking → Marking → Prop where
  | verify (m : Marking) (a : Nat) (t : V) :
      m a = V.Z → t ≠ V.Z → Step m (update m a t)
  | expire (m : Marking) (a : Nat) :
      m a ≠ V.Z → Step m (update m a V.Z)

/-- Finite chains of legal events. -/
inductive Reach : Marking → Marking → Prop where
  | refl (m : Marking) : Reach m m
  | tail {m1 m2 m3 : Marking} :
      Reach m1 m2 → Step m2 m3 → Reach m1 m3

theorem update_at (m : Marking) (a : Nat) (t : V) :
    update m a t a = t := by
  show (if a = a then t else m a) = t
  rw [if_pos rfl]

theorem update_ne (m : Marking) {a n : Nat} (t : V) (h : n ≠ a) :
    update m a t n = m n := by
  show (if n = a then t else m n) = m n
  rw [if_neg h]

/-! ## Epoch-blindness, hereditary, and the theorems -/

/-- The verdict is invariant along EVERY chain of events — the protocol
refuses to distinguish learning from world change. -/
def EpochBlind (φ : Fm) (m : Marking) : Prop :=
  ∀ m', Reach m m' → evalF m' φ = evalF m φ

/-- Intra-epoch refinement (the `ZTime.lean` notion): earned ground is
kept, only marks may resolve. -/
def Refines (m' m : Marking) : Prop :=
  ∀ n, m n ≠ V.Z → m' n = m n

/-- The intra-epoch warranty: invariant under every refinement. -/
def Hereditary (φ : Fm) (m : Marking) : Prop :=
  ∀ m', Refines m' m → evalF m' φ = evalF m φ

/-- Any single coordinate can be driven to any target value by at most
two legal events — the walking lemma. The statement is pointwise
(agreement at coordinates), never functional equality. -/
theorem walk_one (m : Marking) (a : Nat) (t : V) :
    ∃ mm, Reach m mm ∧ mm a = t ∧ ∀ n, n ≠ a → mm n = m n := by
  by_cases h0 : m a = t
  · exact ⟨m, Reach.refl m, h0, fun _ _ => rfl⟩
  · by_cases hz : t = V.Z
    · -- target is Z, current is not (else h0): one expire
      have hne : m a ≠ V.Z := fun hc => h0 (hc.trans hz.symm)
      refine ⟨update m a V.Z,
              Reach.tail (Reach.refl m) (Step.expire m a hne), ?_, ?_⟩
      · rw [update_at, hz]
      · intro n hn; exact update_ne m V.Z hn
    · by_cases hmz : m a = V.Z
      · -- current is Z, target classical: one verify
        refine ⟨update m a t,
                Reach.tail (Reach.refl m) (Step.verify m a t hmz hz), ?_, ?_⟩
        · exact update_at m a t
        · intro n hn; exact update_ne m t hn
      · -- both classical, different: expire then verify
        have s1 : Step m (update m a V.Z) := Step.expire m a hmz
        have hmidz : update m a V.Z a = V.Z := update_at m a V.Z
        have s2 : Step (update m a V.Z) (update (update m a V.Z) a t) :=
          Step.verify (update m a V.Z) a t hmidz hz
        refine ⟨update (update m a V.Z) a t,
                Reach.tail (Reach.tail (Reach.refl m) s1) s2, ?_, ?_⟩
        · exact update_at (update m a V.Z) a t
        · intro n hn
          rw [update_ne (update m a V.Z) t hn, update_ne m V.Z hn]

/-- Walk the first `k` coordinates of `m` onto `target` by legal events. -/
theorem walk_below (m target : Marking) :
    ∀ k : Nat, ∃ mm, Reach m mm ∧ ∀ n, n < k → mm n = target n := by
  intro k
  induction k with
  | zero =>
      exact ⟨m, Reach.refl m, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ k ih =>
      have ⟨mm, hr, hag⟩ := ih
      have ⟨mm2, hr2, hat, hkeep⟩ := walk_one mm k (target k)
      refine ⟨mm2, ?_, ?_⟩
      · -- glue the two reaches (transitivity, proven inline)
        clear hag hat hkeep
        induction hr2 with
        | refl => exact hr
        | tail _ s ih2 => exact Reach.tail ih2 s
      · intro n hn
        by_cases hnk : n = k
        · rw [hnk]; exact hat
        · have hlt : n < k := by
            cases Nat.lt_succ_iff_lt_or_eq.mp hn with
            | inl h => exact h
            | inr h => exact absurd h hnk
          rw [hkeep n hnk]; exact hag n hlt

/-- **The Epoch Boundary Theorem.** A verdict is epoch-blind iff it is
constant over ALL markings — iff the assertion reads none of its
grounds. A protocol that does not distinguish epistemic refinement from
validity-changing events can keep non-trivial guarantees only for
frames: contentful conclusions cannot survive unrestricted epoch
crossing. (Within this model: {T,F,Z}-markings, greedy evaluation,
verify/expire events — the agreed claim ceiling.) -/
theorem epoch_boundary_iff (φ : Fm) (m : Marking) :
    EpochBlind φ m ↔ (∀ m' : Marking, evalF m' φ = evalF m φ) := by
  constructor
  · intro h m'
    have ⟨mm, hr, hag⟩ := walk_below m m' (atomBound φ + 1)
    have e1 : evalF mm φ = evalF m φ := h mm hr
    have e2 : evalF mm φ = evalF m' φ :=
      evalF_congr_on φ (fun n hn =>
        hag n (Nat.lt_succ_of_le (occurs_le_bound φ hn)))
    exact e2.symm.trans e1
  · intro h m' _
    exact h m'

/-- **Epochs matter.** The intra-epoch warranty (`Hereditary`) does NOT
imply epoch-blindness: the witness is the bare verified fact `atom 0`
at an all-T marking — hereditary under every refinement, destroyed by
one expire. So cross-epoch persistence is strictly stronger than the
verification warranty, and the epoch boundary is a logical necessity,
not an administrative convenience. -/
theorem epochs_matter :
    ∃ (φ : Fm) (m : Marking), Hereditary φ m ∧ ¬ EpochBlind φ m := by
  refine ⟨Fm.atom 0, fun _ => V.T, ?_, ?_⟩
  · intro m' href
    show m' 0 = V.T
    exact href 0 (fun hc => V.noConfusion hc)
  · intro h
    have hstep : Step (fun _ => V.T)
        (update (fun _ => V.T) 0 V.Z) :=
      Step.expire (fun _ => V.T) 0 (fun hc => V.noConfusion hc)
    have hreach := Reach.tail (Reach.refl (fun _ => V.T)) hstep
    have := h _ hreach
    -- evalF of the expired marking at atom 0 is Z; at the original, T
    have hz : evalF (update (fun _ => V.T) 0 V.Z) (Fm.atom 0) = V.Z :=
      update_at (fun _ => V.T) 0 V.Z
    rw [hz] at this
    exact V.noConfusion this

/-! ## Axiom audit — every line must print "does not depend on any axioms" -/

#print axioms evalF_congr_on
#print axioms walk_one
#print axioms walk_below
#print axioms epoch_boundary_iff
#print axioms epochs_matter

end EpochBoundary
