/-!
# ZTime — the temporal layer of ZTL, machine-checked (E24's settled laws)

Course A ("time = the arrival of ground", word-spec agreed 2026-07-18):
ZTL's only clock is verification — one tick = one act `verify` resolving
a mark `Z` into an earned classical value. A moment is a marking; the
future is the branching tree of refinements. The warranty ladder of
E12/E21 is read temporally: `Hereditary` = true always along every path,
`Sound` = true at every ending, until-verification = true now.

This file proves the three laws that the stand `ztime.py` measured
(29,812 + 78,354 ticks, 0 violations), as STRUCTURAL theorems — for
EVERY formula, every marking, every tick, not a finite enumeration:

  1. `hereditary_absorbing` — a hereditary verdict survives any tick
     with its grade: the (v, H) states absorb (the automaton law).
  2. `grounded_hereditary`  — a fully verified marking is hereditary:
     every completed trace ends on the shelf (the arrow of logical time).
  3. `hereditary_sound`     — the ladder inclusion: hereditary ⟹ sound
     (completions are refinements).

Also here: the REFUTATION of the E24 conjecture "sound-only is a birth
grade, never entered by a tick" — born of shallow (depth ≤ 2) hunts and
killed the same day by a constructed witness. The selector
`φ = (a ∧ X) ∨ (¬a ∧ p)` with `X = ¬¬p ∨ (q ∨ ¬q)` (the E21 insured
cell) walks U → S → H from the all-marked start: soundness is EARNED by
the tick that verifies which world you are in, and the full strict
ladder is realized rung by rung (`strict_ladder`, kernel-checked over
the formula's atom triple).

VR discipline: self-contained (no imports, no mathlib), `#print axioms`
at the end — the whole file must stand on the EMPTY axiom list.
-/

namespace ZTime

inductive V where
  | T
  | F
  | Z
deriving DecidableEq, Repr

namespace V

/-- Classical readings of a value: Z reads both as truth and as falsehood. -/
def subs : V → List Bool
  | T => [true]
  | F => [false]
  | Z => [true, false]

/-- Zero-trust lift of a unary classical connective. -/
def lift1 (f : Bool → Bool) (x : V) : V :=
  if (subs x).all (fun a => f a) then T else F

/-- Zero-trust lift of a binary classical connective. -/
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

/-- The formula language (mirror of ZTL.lean's `Fm`). -/
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

/-- A marking: every atom carries a value, `Z` = "marked, unverified". -/
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

/-! ## Time: refinements and the tick -/

/-- `m'` refines `m`: all earned ground is kept; only marks may resolve. -/
def Refines (m' m : Marking) : Prop :=
  ∀ n, m n ≠ V.Z → m' n = m n

theorem refines_refl (m : Marking) : Refines m m :=
  fun _ _ => rfl

theorem refines_trans {m₂ m₁ m : Marking}
    (h₂ : Refines m₂ m₁) (h₁ : Refines m₁ m) : Refines m₂ m := by
  intro n hn
  have e₁ : m₁ n = m n := h₁ n hn
  have hn₁ : m₁ n ≠ V.Z := by rw [e₁]; exact hn
  rw [h₂ n hn₁, e₁]

/-- The tick of logical time: one act of verification at atom `a`. -/
def verify (m : Marking) (a : Nat) (v : V) : Marking :=
  fun n => if n = a then v else m n

/-- A tick is a refinement — verification never overwrites earned ground. -/
theorem verify_refines {m : Marking} {a : Nat} {v : V}
    (h : m a = V.Z) : Refines (verify m a v) m := by
  intro n hn
  unfold verify
  split
  · next heq => rw [heq] at hn; exact absurd h hn
  · rfl

/-! ## The grades, temporally -/

/-- HEREDITARY = true always along every path: the verdict is invariant
under every refinement (the shelf-life warranty of E12/E21). -/
def Hereditary (φ : Fm) (m : Marking) : Prop :=
  ∀ m', Refines m' m → evalF m' φ = evalF m φ

/-- A completion: a refinement with no marks left (an ending of time). -/
def Completion (c m : Marking) : Prop :=
  Refines c m ∧ ∀ n, c n ≠ V.Z

/-- SOUND = true at every ending: all completions agree with the verdict. -/
def Sound (φ : Fm) (m : Marking) : Prop :=
  ∀ c, Completion c m → evalF c φ = evalF m φ

/-! ## Law 1: hereditary is absorbing (the automaton law) -/

/-- **A hereditary verdict survives any tick, value and grade both** —
the (v, H) states of the grade automaton absorb. Measured: 0 violations
on 29,812 ticks; here proved for every formula, marking, atom, value. -/
theorem hereditary_absorbing {φ : Fm} {m : Marking} {a : Nat} {v : V}
    (hH : Hereditary φ m) (ha : m a = V.Z) :
    evalF (verify m a v) φ = evalF m φ ∧ Hereditary φ (verify m a v) := by
  have hr : Refines (verify m a v) m := verify_refines ha
  refine ⟨hH _ hr, ?_⟩
  intro m'' h''
  rw [hH _ (refines_trans h'' hr), hH _ hr]

/-! ## Law 2: the arrow of logical time -/

/-- Evaluation depends on the marking pointwise. -/
theorem evalF_congr {m' m : Marking} (h : ∀ n, m' n = m n) :
    ∀ φ, evalF m' φ = evalF m φ := by
  intro φ
  induction φ with
  | atom n => exact h n
  | top => rfl
  | bot => rfl
  | neg φ ih =>
      show znot (evalF m' φ) = znot (evalF m φ)
      rw [ih]
  | conj φ ψ ihφ ihψ =>
      show zand (evalF m' φ) (evalF m' ψ) = zand (evalF m φ) (evalF m ψ)
      rw [ihφ, ihψ]
  | disj φ ψ ihφ ihψ =>
      show zor (evalF m' φ) (evalF m' ψ) = zor (evalF m φ) (evalF m ψ)
      rw [ihφ, ihψ]
  | imp φ ψ ihφ ihψ =>
      show zimp (evalF m' φ) (evalF m' ψ) = zimp (evalF m φ) (evalF m ψ)
      rw [ihφ, ihψ]
  | xor φ ψ ihφ ihψ =>
      show zxor (evalF m' φ) (evalF m' ψ) = zxor (evalF m φ) (evalF m ψ)
      rw [ihφ, ihψ]
  | xnor φ ψ ihφ ihψ =>
      show zxnor (evalF m' φ) (evalF m' ψ) = zxnor (evalF m φ) (evalF m ψ)
      rw [ihφ, ihψ]

/-- **Every completed verification path ends hereditary** — a marking
with no marks left admits only itself as a refinement, so its verdict
is on the shelf. Measured: 130/130 traces; here proved in general. -/
theorem grounded_hereditary {φ : Fm} {m : Marking}
    (hg : ∀ n, m n ≠ V.Z) : Hereditary φ m := by
  intro m' hr
  exact evalF_congr (fun n => hr n (hg n)) φ

/-! ## Law 3: the ladder inclusion -/

/-- **Hereditary ⟹ sound**: an ending of time is a refinement, so what
holds along every path holds at every ending. (The converse is FALSE —
measured witnesses in zverify.py §2; the grades separate.) -/
theorem hereditary_sound {φ : Fm} {m : Marking}
    (hH : Hereditary φ m) : Sound φ m :=
  fun c hc => hH c hc.1

/-! ## The witness: sound IS earned (the refutation, kernel-checked)

The conjecture "sound-only is a birth grade" is FALSE. Refinements and
completions are bounded here to the formula's three atoms — faithful,
since evaluation is pointwise and marks outside the formula never touch
it; the unbounded cross-check is the stand (`ztime.py` §6). -/

namespace Witness

-- Non-overlapping matches: an overlapping wildcard row pulls propext in
-- through the compiled matcher (measured; the kand/kor pitfall of ZTL.lean).

/-- One-coordinate refinements: ground stays; a mark may stay or resolve. -/
def ref1 : V → List V
  | V.T => [V.T]
  | V.F => [V.F]
  | V.Z => [V.Z, V.T, V.F]

/-- One-coordinate completions: a mark must resolve. -/
def comp1 : V → List V
  | V.T => [V.T]
  | V.F => [V.F]
  | V.Z => [V.T, V.F]

/-- The selector over the E21 insured cell:
`φ = (a ∧ (¬¬p ∨ (q ∨ ¬q))) ∨ (¬a ∧ p)`, evaluated directly. -/
def eval3 (a p q : V) : V :=
  zor (zand a (zor (znot (znot p)) (zor q (znot q))))
      (zand (znot a) p)

/-- Hereditary, bounded to the atom triple (Bool level — the
ZClone pattern: no tactic-built instances, no propext). -/
def hered3 (a p q : V) : Bool :=
  (ref1 a).all fun a' => (ref1 p).all fun p' => (ref1 q).all fun q' =>
    eval3 a' p' q' == eval3 a p q

/-- Sound, bounded to the atom triple. -/
def sound3 (a p q : V) : Bool :=
  (comp1 a).all fun a' => (comp1 p).all fun p' => (comp1 q).all fun q' =>
    eval3 a' p' q' == eval3 a p q

/-- **The strict ladder, rung by rung — and the entry into sound.**
All marked: neither sound nor hereditary (U). Tick `a:=T`: sound but
not hereditary — sound-only is ENTERED, the birth-grade conjecture
falls. Tick `p:=T`: hereditary (H). -/
theorem strict_ladder :
    (sound3 V.Z V.Z V.Z = false ∧ hered3 V.Z V.Z V.Z = false)
  ∧ (sound3 V.T V.Z V.Z = true  ∧ hered3 V.T V.Z V.Z = false)
  ∧ hered3 V.T V.T V.Z = true := by decide

end Witness

/-! ## Axiom audit — every line must print "does not depend on any axioms" -/

#print axioms refines_trans
#print axioms verify_refines
#print axioms hereditary_absorbing
#print axioms evalF_congr
#print axioms grounded_hereditary
#print axioms hereditary_sound
#print axioms Witness.strict_ladder

end ZTime
