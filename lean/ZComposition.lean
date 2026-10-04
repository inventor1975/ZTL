/-
  ZComposition.lean — NO PROMOTION WITHOUT A COMPOSITION WITNESS. Local validity is not compositional
  validity: grounds that each hold in their own context cannot be promoted together into one EARNED state
  when what joins them is an atom no act can ever verify.

  Asked 2026-10-04 by the curator after Hardy.lean, for Arkady's reading of it: "individually valid facts do
  not necessarily compose into a valid operational conclusion" — Griffiths' single-framework rule as an
  admissibility condition. Hardy.lean proved ONE instance; this file states the general law, proves it for
  every formula and every marking, and re-derives Hardy as a corollary.

  THE SETTING.
    A marking `m` is the present state of checking (T, F checked; Z not). A REPERTOIRE `R` names the atoms
    some future act can still check. A future `m'` is REACHABLE when it refines `m` and touches only atoms
    in `R`. A HOLE is an atom that is Z now and outside the repertoire: it stays Z in every reachable future.
    EARNED at `m'` = verdict T and hereditary (no further refinement revokes it).

  THE THEOREM (`no_promotion_without_witness`). Suppose that, however the checkable atoms come out
  (any classical valuation `b` agreeing with what is already checked), some values of the HOLES make φ
  classically false. Then in NO reachable future is φ EARNED.
  Read backwards: a φ that ever becomes EARNED has a COMPOSITION WITNESS — an outcome of the checkable atoms
  under which φ holds for EVERY value of the holes. The holes are where "facts from incompatible frameworks"
  live (Hardy: the answers to the questions not asked); the theorem forbids promoting a conjunction across
  them, whatever each conjunct's own standing.

  THE CONVERSE FAILS, and that is proved too (`witness_not_sufficient`): `h ∨ ¬h` over a hole h is
  classically true for every value of h, yet it is F in every reachable future — ZTL does not even promote a
  classically valid composition across a hole, because each occurrence of an unverified atom is read
  independently. The witness is NECESSARY, not sufficient: the law is a ceiling, stated as one.

  THE COROLLARY (`hardy_never_promoted`): the Hardy chain in the contested run (Hardy.lean's grounding; the
  two unasked answers are holes) is EARNED in no reachable future.

  What is NOT claimed: that the operational reading of an unasked question is the true one (a realist
  rejects it — Stapp, Bohm); the theorem is about what may be promoted GIVEN which atoms are holes. Which
  atoms are holes is the modelling input (in Hardy: computed non-commutation, Hardy.lean `incompatible`).

  VR discipline: self-contained (no imports, no mathlib), `#print axioms` at the end — the EMPTY axiom list.
  No `simp`, no `funext` (it would bring Quot.sound), no wildcard match rows (propext).
-/

namespace ZComposition

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

def znot : V → V     := lift1 (fun a => !a)
def zand : V → V → V := lift2 (fun a b => a && b)
def zor  : V → V → V := lift2 (fun a b => a || b)
def zimp : V → V → V := lift2 (fun a b => !a || b)

end V

open V

inductive Fm where
  | atom : Nat → Fm
  | neg  : Fm → Fm
  | conj : Fm → Fm → Fm
  | disj : Fm → Fm → Fm
  | imp  : Fm → Fm → Fm

def Marking := Nat → V

def evalF (m : Marking) : Fm → V
  | .atom n   => m n
  | .neg φ    => znot (evalF m φ)
  | .conj φ ψ => zand (evalF m φ) (evalF m ψ)
  | .disj φ ψ => zor (evalF m φ) (evalF m ψ)
  | .imp φ ψ  => zimp (evalF m φ) (evalF m ψ)

/-- Classical evaluation over a Boolean valuation. -/
def evalB (b : Nat → Bool) : Fm → Bool
  | .atom n   => b n
  | .neg φ    => !(evalB b φ)
  | .conj φ ψ => evalB b φ && evalB b ψ
  | .disj φ ψ => evalB b φ || evalB b ψ
  | .imp φ ψ  => !(evalB b φ) || evalB b ψ

def Refines (m' m : Marking) : Prop :=
  ∀ n, m n ≠ V.Z → m' n = m n

def Hereditary (φ : Fm) (m : Marking) : Prop :=
  ∀ m', Refines m' m → evalF m' φ = evalF m φ

/-- EARNED: true, and no refinement revokes it. -/
def Earned (φ : Fm) (m : Marking) : Prop :=
  evalF m φ = V.T ∧ Hereditary φ m

/-- A future the repertoire can reach: it refines `m` and touches only atoms in `R`. -/
def Reachable (R : Nat → Bool) (m m' : Marking) : Prop :=
  Refines m' m ∧ ∀ n, R n = false → m' n = m n

def ofBool : Bool → V
  | true  => V.T
  | false => V.F

def toBool : V → Bool
  | V.T => true
  | V.F => false
  | V.Z => true

theorem toBool_ofBool (a : Bool) : toBool (ofBool a) = a := by
  cases a <;> rfl

theorem ofBool_ne_Z (a : Bool) : ofBool a ≠ V.Z := by
  cases a <;> decide

/-! ## On a marking with no Z, ZTL is classical (the classical-agreement lemma, re-proved here) -/

theorem znot_ofBool (a : Bool) : znot (ofBool a) = ofBool (!a) := by cases a <;> rfl
theorem zand_ofBool (a b : Bool) : zand (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl
theorem zor_ofBool (a b : Bool) : zor (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl
theorem zimp_ofBool (a b : Bool) : zimp (ofBool a) (ofBool b) = ofBool (!a || b) := by
  cases a <;> cases b <;> rfl

theorem evalF_classical_of_noZ (c : Marking) (hc : ∀ n, c n ≠ V.Z) :
    ∀ φ, evalF c φ = ofBool (evalB (fun n => toBool (c n)) φ) := by
  intro φ
  induction φ with
  | atom n =>
      show c n = ofBool (toBool (c n))
      cases h : c n with
      | T => rfl
      | F => rfl
      | Z => exact absurd h (hc n)
  | neg φ ih =>
      show znot (evalF c φ) = ofBool (!(evalB (fun n => toBool (c n)) φ))
      rw [ih]; exact znot_ofBool _
  | conj φ ψ ihφ ihψ =>
      show zand (evalF c φ) (evalF c ψ) = ofBool (evalB _ φ && evalB _ ψ)
      rw [ihφ, ihψ]; exact zand_ofBool _ _
  | disj φ ψ ihφ ihψ =>
      show zor (evalF c φ) (evalF c ψ) = ofBool (evalB _ φ || evalB _ ψ)
      rw [ihφ, ihψ]; exact zor_ofBool _ _
  | imp φ ψ ihφ ihψ =>
      show zimp (evalF c φ) (evalF c ψ) = ofBool (!(evalB _ φ) || evalB _ ψ)
      rw [ihφ, ihψ]; exact zimp_ofBool _ _

theorem evalB_congr (f g : Nat → Bool) (h : ∀ n, f n = g n) : ∀ φ, evalB f φ = evalB g φ := by
  intro φ
  induction φ with
  | atom n => exact h n
  | neg φ ih => show (!(evalB f φ)) = !(evalB g φ); rw [ih]
  | conj φ ψ ihφ ihψ => show (evalB f φ && evalB f ψ) = (evalB g φ && evalB g ψ); rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ => show (evalB f φ || evalB f ψ) = (evalB g φ || evalB g ψ); rw [ihφ, ihψ]
  | imp φ ψ ihφ ihψ => show (!(evalB f φ) || evalB f ψ) = (!(evalB g φ) || evalB g ψ); rw [ihφ, ihψ]

/-! ## The law -/

/-- No composition witness: however the checkable atoms come out (a classical `b` agreeing with what is
already checked), the HOLES (Z now, outside the repertoire) can be set so that φ is classically false. -/
def NoWitness (R : Nat → Bool) (m : Marking) (φ : Fm) : Prop :=
  ∀ b : Nat → Bool, (∀ n, m n = V.T → b n = true) → (∀ n, m n = V.F → b n = false) →
    ∃ p : Nat → Bool, (∀ n, ¬ (m n = V.Z ∧ R n = false) → p n = b n) ∧ evalB p φ = false

/-- **NO PROMOTION WITHOUT A COMPOSITION WITNESS.** If no outcome of the checkable atoms makes φ true for
every value of the holes, then φ is EARNED in no future the repertoire can reach. -/
theorem no_promotion_without_witness (R : Nat → Bool) (m : Marking) (φ : Fm)
    (hnw : NoWitness R m φ) : ∀ m', Reachable R m m' → ¬ Earned φ m' := by
  intro m' hreach hearn
  have hT : evalF m' φ = V.T := hearn.1
  -- the classical reading of the future, Z read as true (any choice would do)
  have agreeT : ∀ n, m n = V.T → toBool (m' n) = true := by
    intro n hn
    have hne : m n ≠ V.Z := by rw [hn]; decide
    rw [hreach.1 n hne, hn]; rfl
  have agreeF : ∀ n, m n = V.F → toBool (m' n) = false := by
    intro n hn
    have hne : m n ≠ V.Z := by rw [hn]; decide
    rw [hreach.1 n hne, hn]; rfl
  match hnw (fun n => toBool (m' n)) agreeT agreeF with
  | ⟨p, hp, hfalse⟩ =>
    -- complete the future: its Z atoms (holes, and checkable atoms not yet checked) take p's values
    let c : Marking := fun n => if m' n = V.Z then ofBool (p n) else m' n
    have hcref : Refines c m' := by
      intro n hn
      show (if m' n = V.Z then ofBool (p n) else m' n) = m' n
      rw [if_neg hn]
    have hnoZ : ∀ n, c n ≠ V.Z := by
      intro n
      show (if m' n = V.Z then ofBool (p n) else m' n) ≠ V.Z
      cases hz : decide (m' n = V.Z) with
      | true => rw [if_pos (of_decide_eq_true hz)]; exact ofBool_ne_Z _
      | false => rw [if_neg (of_decide_eq_false hz)]; exact of_decide_eq_false hz
    have hpt : ∀ n, toBool (c n) = p n := by
      intro n
      show toBool (if m' n = V.Z then ofBool (p n) else m' n) = p n
      cases hz : decide (m' n = V.Z) with
      | true => rw [if_pos (of_decide_eq_true hz)]; exact toBool_ofBool _
      | false =>
          have hnz : m' n ≠ V.Z := of_decide_eq_false hz
          rw [if_neg hnz]
          -- n is not a hole: a hole stays Z in every reachable future
          have nothole : ¬ (m n = V.Z ∧ R n = false) := by
            intro ⟨hmz, hr⟩
            exact hnz (by rw [hreach.2 n hr]; exact hmz)
          exact (hp n nothole).symm
    have hcF : evalF c φ = V.F := by
      rw [evalF_classical_of_noZ c hnoZ φ, evalB_congr _ p hpt φ, hfalse]; rfl
    have hsame : evalF c φ = evalF m' φ := hearn.2 c hcref
    rw [hcF, hT] at hsame
    exact V.noConfusion hsame

/-! ## The converse fails: a witness is necessary, not sufficient -/

/-- `h ∨ ¬h` over a hole h (atom 0; marking all Z; empty repertoire): classically true for both values of
h, yet F in every reachable future — ZTL does not promote even a classically valid composition across a
hole, since each occurrence of an unverified atom is read independently. -/
def allZ : Marking := fun _ => V.Z
def none : Nat → Bool := fun _ => false
def lem : Fm := .disj (.atom 0) (.neg (.atom 0))

theorem witness_not_sufficient :
    (∀ b : Nat → Bool, evalB b lem = true) ∧
    (∀ m', Reachable none allZ m' → evalF m' lem = V.F) := by
  refine ⟨?_, ?_⟩
  · intro b
    show (b 0 || !(b 0)) = true
    cases b 0 <;> rfl
  · intro m' hreach
    have h0 : m' 0 = V.Z := hreach.2 0 rfl
    show zor (m' 0) (znot (m' 0)) = V.F
    rw [h0]; decide

/-! ## Corollary: Hardy (the grounding of Hardy.lean, re-stated on this file's language) -/

def xa : Fm := .atom 0
def xb : Fm := .atom 1
def za : Fm := .atom 2
def zb : Fm := .atom 3
def hardyChain : Fm :=
  .conj xa (.conj xb (.conj (.imp xa zb) (.conj (.imp xb za) (.neg (.conj za zb)))))

/-- The contested run: both asked X and got −; the Z answers were not asked (holes). -/
def contested : Marking := fun n =>
  if n = 0 then V.T else if n = 1 then V.T else V.Z

theorem hardy_no_witness : NoWitness none contested hardyChain := by
  intro b hT _
  have b0 : b 0 = true := hT 0 rfl
  have b1 : b 1 = true := hT 1 rfl
  refine ⟨b, fun _ _ => rfl, ?_⟩
  show (b 0 && (b 1 && ((!(b 0) || b 3) && ((!(b 1) || b 2) && !(b 2 && b 3))))) = false
  rw [b0, b1]
  cases b 2 <;> cases b 3 <;> rfl

/-- **Hardy, as a corollary**: the chain is EARNED in no reachable future — the three laws, each earned
in its own context (Hardy.lean `control_earned`), are not promoted together across the unasked answers. -/
theorem hardy_never_promoted : ∀ m', Reachable none contested m' → ¬ Earned hardyChain m' :=
  no_promotion_without_witness none contested hardyChain hardy_no_witness

/-! ## Economy: an account that rests only on what was witnessed, against one that says anything definite
about the holes (curator 2026-10-04: "prove the economy machine-wise; leave philosophy to philosophers")

An ACCOUNT is a list of claims. The theorem compares two accounts of the same marking: one whose claims are all
EARNED now, and one that contains a claim with no composition witness. The first is fully earned already; the
second is fully earned in NO reachable future. It is not a theorem about which account is TRUE — both may be
consistent — but about which one ever stands on verified ground. -/

def FullyEarned (A : List Fm) (m : Marking) : Prop := ∀ φ, φ ∈ A → Earned φ m

/-- **ECONOMY.** If every claim of A is earned now, and B contains a claim with no composition witness, then A is
fully earned already, and B is fully earned in no future the repertoire can reach. -/
theorem economy (R : Nat → Bool) (m : Marking) (A B : List Fm) (hA : FullyEarned A m)
    (ψ : Fm) (hψ : ψ ∈ B) (hnw : NoWitness R m ψ) :
    FullyEarned A m ∧ ∀ m', Reachable R m m' → ¬ FullyEarned B m' :=
  ⟨hA, fun m' hr hB => no_promotion_without_witness R m ψ hnw m' hr (hB ψ hψ)⟩

/-! ### Hardy: the account of what was witnessed, against any claim about the unasked answers -/

/-- The account that asserts only what was witnessed in the contested run: X_A = −, X_B = −. -/
def witnessed : List Fm := [xa, xb]

theorem witnessed_earned : FullyEarned witnessed contested := by
  intro φ hφ
  cases hφ with
  | head =>
      refine ⟨rfl, ?_⟩
      intro m' h
      show m' 0 = contested 0
      exact h 0 (by decide)
  | tail _ h1 =>
      cases h1 with
      | head =>
          refine ⟨rfl, ?_⟩
          intro m' h
          show m' 1 = contested 1
          exact h 1 (by decide)
      | tail _ h2 => cases h2

/-- Set the two unasked answers (atoms 2, 3) to chosen values, keep everything else. -/
def setHoles (b : Nat → Bool) (v2 v3 : Bool) : Nat → Bool := fun n =>
  if n = 2 then v2 else if n = 3 then v3 else b n

theorem setHoles_agrees (b : Nat → Bool) (v2 v3 : Bool) :
    ∀ n, ¬ (contested n = V.Z ∧ none n = false) → setHoles b v2 v3 n = b n := by
  intro n hn
  show (if n = 2 then v2 else if n = 3 then v3 else b n) = b n
  cases h2 : decide (n = 2) with
  | true =>
      have e : n = 2 := of_decide_eq_true h2
      exact absurd ⟨by rw [e]; rfl, rfl⟩ hn
  | false =>
      rw [if_neg (of_decide_eq_false h2)]
      cases h3 : decide (n = 3) with
      | true =>
          have e : n = 3 := of_decide_eq_true h3
          exact absurd ⟨by rw [e]; rfl, rfl⟩ hn
      | false => rw [if_neg (of_decide_eq_false h3)]

theorem setHoles_0 (b : Nat → Bool) (v2 v3 : Bool) : setHoles b v2 v3 0 = b 0 := rfl
theorem setHoles_1 (b : Nat → Bool) (v2 v3 : Bool) : setHoles b v2 v3 1 = b 1 := rfl
theorem setHoles_2 (b : Nat → Bool) (v2 v3 : Bool) : setHoles b v2 v3 2 = v2 := rfl
theorem setHoles_3 (b : Nat → Bool) (v2 v3 : Bool) : setHoles b v2 v3 3 = v3 := rfl

/-- A claim about the unasked answers has no composition witness when, for every checkable outcome, the holes
can be set to falsify it; `holeNoWitness` builds that from two hole values and a falsification. -/
theorem holeNoWitness (φ : Fm) (v2 v3 : Bool)
    (hf : ∀ b : Nat → Bool, b 0 = true → b 1 = true → evalB (setHoles b v2 v3) φ = false) :
    NoWitness none contested φ := by
  intro b hT _
  exact ⟨setHoles b v2 v3, setHoles_agrees b v2 v3, hf b (hT 0 rfl) (hT 1 rfl)⟩

/-- **Every definite claim about the unasked answers has no witness** — a value (Z_A = 1, Z_B = 1, or their
negations) or a law applied to the unasked answer in this run ("had Bob asked Z he would get 1": X_A = − → Z_B = 1;
its mirror; and "not both 1"). These are the claims a counterfactual account of this run needs. -/
theorem counterfactual_claims_no_witness :
    NoWitness none contested za ∧ NoWitness none contested zb ∧
    NoWitness none contested (.neg za) ∧ NoWitness none contested (.neg zb) ∧
    NoWitness none contested (.imp xa zb) ∧ NoWitness none contested (.imp xb za) ∧
    NoWitness none contested (.neg (.conj za zb)) := by
  refine ⟨holeNoWitness za false false (fun b _ _ => rfl),
          holeNoWitness zb false false (fun b _ _ => rfl),
          holeNoWitness (.neg za) true true (fun b _ _ => rfl),
          holeNoWitness (.neg zb) true true (fun b _ _ => rfl),
          holeNoWitness (.imp xa zb) false false (fun b h0 _ => ?_),
          holeNoWitness (.imp xb za) false false (fun b _ h1 => ?_),
          holeNoWitness (.neg (.conj za zb)) true true (fun b _ _ => rfl)⟩
  · show (!(setHoles b false false 0) || setHoles b false false 3) = false
    rw [setHoles_0, h0]; rfl
  · show (!(setHoles b false false 1) || setHoles b false false 2) = false
    rw [setHoles_1, h1]; rfl

/-- **ECONOMY, Hardy.** The account of what was witnessed is fully earned now; ANY account containing a definite
claim about the unasked answers — a value, or a law applied to them in this run — is fully earned in no
reachable future. Which account is true is not decided here; which one stands on verified ground is. -/
theorem hardy_economy (B : List Fm)
    (hB : za ∈ B ∨ zb ∈ B ∨ Fm.neg za ∈ B ∨ Fm.neg zb ∈ B ∨ Fm.imp xa zb ∈ B ∨ Fm.imp xb za ∈ B ∨
          Fm.neg (Fm.conj za zb) ∈ B) :
    FullyEarned witnessed contested ∧ ∀ m', Reachable none contested m' → ¬ FullyEarned B m' := by
  match counterfactual_claims_no_witness with
  | ⟨n1, n2, n3, n4, n5, n6, n7⟩ =>
    refine ⟨witnessed_earned, ?_⟩
    intro m' hr hfe
    rcases hB with h | h | h | h | h | h | h
    · exact (economy none contested witnessed B witnessed_earned _ h n1).2 m' hr hfe
    · exact (economy none contested witnessed B witnessed_earned _ h n2).2 m' hr hfe
    · exact (economy none contested witnessed B witnessed_earned _ h n3).2 m' hr hfe
    · exact (economy none contested witnessed B witnessed_earned _ h n4).2 m' hr hfe
    · exact (economy none contested witnessed B witnessed_earned _ h n5).2 m' hr hfe
    · exact (economy none contested witnessed B witnessed_earned _ h n6).2 m' hr hfe
    · exact (economy none contested witnessed B witnessed_earned _ h n7).2 m' hr hfe

#print axioms economy
#print axioms witnessed_earned
#print axioms setHoles_agrees
#print axioms holeNoWitness
#print axioms counterfactual_claims_no_witness
#print axioms hardy_economy
#print axioms toBool_ofBool
#print axioms znot_ofBool
#print axioms zand_ofBool
#print axioms zor_ofBool
#print axioms zimp_ofBool
#print axioms evalF_classical_of_noZ
#print axioms evalB_congr
#print axioms no_promotion_without_witness
#print axioms witness_not_sufficient
#print axioms hardy_no_witness
#print axioms hardy_never_promoted

end ZComposition
