/-
  KochenSpecker.lean — the Mermin–Peres square as the NEGATIVE CONTROL of the grounding rule, kernel-checked:
  the physics exactly (integer 4×4 matrices), the rule, both encodings, the path, and the run space.

  Companion of `dilemmas/kochen_specker.py` (2026-10-04; prediction written before the run, point 1 FAILED as
  worded — see the stand). Curator 2026-10-04: "Kochen–Specker, bring it to Lean like Hardy".
  `Contextuality.lean` already proves the combinatorial core (0 of 512 valuations); this file adds the
  run-level reading: what the grounding rule makes of a run that asked ONE context, and the control.

  THE PHYSICS, exactly. The nine observables XI, IX, XX / IZ, ZI, ZZ / XZ, ZX, YY are integer 4×4 matrices —
  YY too: σy⊗σy = −(J⊗J) with J = [[0,−1],[1,0]]. Proved: each row multiplies to +I, columns 1–2 to +I,
  column 3 to −I; the three observables of a context commute; every pair in different row AND column does
  not (18 pairs). Integers as pairs of naturals (Int would bring propext).

  THE RULE (hardy.py's, extended): a run asks one context and gets three ±1 answers (+1 ↦ T). An asked cell is
  witnessed; an unasked cell is Z — and every unasked cell fails to commute with some asked one (proved
  below), so it is a HOLE (Z_PERMANENT). Atoms: E1 (non-contextual) cell (r,c) ↦ 3r+c; E2 (contextual) the
  row-context value ↦ 3r+c, the column-context value ↦ 9+3r+c.

  THE THEOREMS.
    physics            the six identities, commutation inside contexts, 18 non-commuting cross pairs
    holes              in every run, each unasked cell fails to commute with some asked cell
    e1_false_now / e1_false_every_completion
                       E1, run "row 1 = (+,+,+)": the six laws together F, and F in EVERY completion
    e1_path_reads_T    …but after checking v(2,1)=F, v(2,2)=T, v(3,1)=F, v(3,2)=T the verdict reads T:
                       the F is not hereditary (that is why the judge says OPEN, not REFUTED)
    e1_laws_alone      each law alone can still be made T
    e2_completion_T    E2 (contextual, Bohm), the same run: a completion makes all six laws T — NOT refuted.
                       THE CONTROL: had this failed, the lens would kill Bohm
    run_space_*        for each of the 6 contexts and each outcome physics allows, every law can be made T
                       under the rule's grounding — the rule never refutes a law of physics

  VR discipline: self-contained (no imports, no mathlib), `#print axioms` at the end — the EMPTY axiom list.
-/

namespace KochenSpecker

/-! ## The physics, in integers -/

/-- A signed integer p − n. -/
abbrev S := Nat × Nat

def sadd (x y : S) : S := (x.1 + y.1, x.2 + y.2)
def smul (x y : S) : S := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def sneg (x : S) : S := (x.2, x.1)
def seq (x y : S) : Bool := Nat.beq (x.1 + y.2) (y.1 + x.2)

def one : S := (1, 0)
def zero : S := (0, 0)
def mone : S := (0, 1)

/-- Matrices as entry functions. -/
def M := Nat → Nat → S

def p2 (a b c d : S) : M := fun i j =>
  if i = 0 then (if j = 0 then a else b) else (if j = 0 then c else d)

def pI : M := p2 one zero zero one
def pX : M := p2 zero one one zero
def pZ : M := p2 one zero zero mone
def pJ : M := p2 zero mone one zero          -- σy = i·J, so σy⊗σy = −(J⊗J)

def kron (a b : M) : M := fun i j => smul (a (i / 2) (j / 2)) (b (i % 2) (j % 2))
def mneg (a : M) : M := fun i j => sneg (a i j)

def mmul (a b : M) : M := fun i j =>
  sadd (sadd (smul (a i 0) (b 0 j)) (smul (a i 1) (b 1 j)))
       (sadd (smul (a i 2) (b 2 j)) (smul (a i 3) (b 3 j)))

def idx : List Nat := [0, 1, 2, 3]

def meq (a b : M) : Bool := idx.all (fun i => idx.all (fun j => seq (a i j) (b i j)))

def id4 : M := fun i j => if i = j then one else zero

/-- The square, cell (r,c) ↦ 3r+c. -/
def obs : Nat → M
  | 0 => kron pX pI
  | 1 => kron pI pX
  | 2 => kron pX pX
  | 3 => kron pI pZ
  | 4 => kron pZ pI
  | 5 => kron pZ pZ
  | 6 => kron pX pZ
  | 7 => kron pZ pX
  | 8 => mneg (kron pJ pJ)
  | _ => id4

/-- Context k: rows 0–2, columns 3–5; its j-th cell. -/
def cell (k j : Nat) : Nat := if k < 3 then 3 * k + j else (k - 3) + 3 * j

/-- The sign each context multiplies to: column 3 (k = 5) is −I. -/
def sign (k : Nat) : Bool := !(Nat.beq k 5)

def ctxs : List Nat := [0, 1, 2, 3, 4, 5]
def cells : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8]

def commutes (a b : Nat) : Bool := meq (mmul (obs a) (obs b)) (mmul (obs b) (obs a))

def inCtx (k n : Nat) : Bool := Nat.beq n (cell k 0) || Nat.beq n (cell k 1) || Nat.beq n (cell k 2)

def sameLine (a b : Nat) : Bool := Nat.beq (a / 3) (b / 3) || Nat.beq (a % 3) (b % 3)

/-- **The physics.** Each context multiplies to its sign times I; inside a context everything commutes; every
pair in a different row AND a different column fails to commute. -/
def physicsOK : Bool :=
  ctxs.all (fun k =>
    meq (mmul (mmul (obs (cell k 0)) (obs (cell k 1))) (obs (cell k 2)))
        (if sign k then id4 else mneg id4) &&
    commutes (cell k 0) (cell k 1) && commutes (cell k 0) (cell k 2) && commutes (cell k 1) (cell k 2)) &&
  cells.all (fun a => cells.all (fun b => sameLine a b || !(commutes a b)))

theorem physics : physicsOK = true := by decide

/-- **The holes.** In a run asking context k, every unasked cell fails to commute with some asked cell — so by
the rule it is Z and no act in this run can witness it. -/
def holesOK : Bool :=
  ctxs.all (fun k => cells.all (fun n =>
    inCtx k n || !(commutes n (cell k 0)) || !(commutes n (cell k 1)) || !(commutes n (cell k 2))))

theorem holes : holesOK = true := by decide

/-! ## The logic (a mirror of the core) -/

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
def zxnor : V → V → V := lift2 (fun a b => a == b)

end V

open V

inductive Fm where
  | atom : Nat → Fm
  | neg  : Fm → Fm
  | conj : Fm → Fm → Fm
  | xnor : Fm → Fm → Fm

def Marking := Nat → V

def evalF (m : Marking) : Fm → V
  | .atom n   => m n
  | .neg φ    => znot (evalF m φ)
  | .conj φ ψ => zand (evalF m φ) (evalF m ψ)
  | .xnor φ ψ => zxnor (evalF m φ) (evalF m ψ)

def evalB (b : Nat → Bool) : Fm → Bool
  | .atom n   => b n
  | .neg φ    => !(evalB b φ)
  | .conj φ ψ => evalB b φ && evalB b ψ
  | .xnor φ ψ => evalB b φ == evalB b ψ

def Refines (m' m : Marking) : Prop := ∀ n, m n ≠ V.Z → m' n = m n
def Completion (c m : Marking) : Prop := Refines c m ∧ ∀ n, c n ≠ V.Z

def ofBool : Bool → V
  | true  => V.T
  | false => V.F

def toBool : V → Bool
  | V.T => true
  | V.F => false
  | V.Z => true

theorem znot_ofBool (a : Bool) : znot (ofBool a) = ofBool (!a) := by cases a <;> rfl
theorem zand_ofBool (a b : Bool) : zand (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl
theorem zxnor_ofBool (a b : Bool) : zxnor (ofBool a) (ofBool b) = ofBool (a == b) := by
  cases a <;> cases b <;> rfl

/-- On a marking with no Z, the value is the classical one. -/
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
  | xnor φ ψ ihφ ihψ =>
      show zxnor (evalF c φ) (evalF c ψ) = ofBool (evalB _ φ == evalB _ ψ)
      rw [ihφ, ihψ]; exact zxnor_ofBool _ _

/-! ## The laws, both encodings -/

/-- A parity law over three atoms: product +1 ↔ an even number of −1 (F); column 3 odd. -/
def law (a b c : Nat) (s : Bool) : Fm :=
  if s then .xnor (.atom a) (.xnor (.atom b) (.atom c))
  else .neg (.xnor (.atom a) (.xnor (.atom b) (.atom c)))

def lawE1 (k : Nat) : Fm := law (cell k 0) (cell k 1) (cell k 2) (sign k)
/-- E2: rows use the row-context atoms, columns the column-context atoms (offset 9). -/
def off (k : Nat) : Nat := if k < 3 then 0 else 9
def lawE2 (k : Nat) : Fm := law (off k + cell k 0) (off k + cell k 1) (off k + cell k 2) (sign k)

def all6 (L : Nat → Fm) : Fm :=
  .conj (L 0) (.conj (L 1) (.conj (L 2) (.conj (L 3) (.conj (L 4) (L 5)))))

def chainE1 : Fm := all6 lawE1
def chainE2 : Fm := all6 lawE2

/-! ## E1, the run "row 1 = (+,+,+)" -/

def run1 : Marking := fun n => if n < 3 then V.T else V.Z

theorem e1_false_now : evalF run1 chainE1 = V.F := by decide

/-- The six laws as one Boolean expression of the nine cells. -/
theorem e1_classical (b : Nat → Bool) :
    evalB b chainE1 =
      ((b 0 == (b 1 == b 2)) && ((b 3 == (b 4 == b 5)) && ((b 6 == (b 7 == b 8)) &&
       ((b 0 == (b 3 == b 6)) && ((b 1 == (b 4 == b 7)) && !(b 2 == (b 5 == b 8))))))) := rfl

/-- **Kochen–Specker, the run-level reading**: whatever the six unasked cells are, the six laws are false —
non-contextual values do not exist. (The same 0-of-512 fact as `Contextuality.mermin_square_no_valuation`,
here for every completion of this run.) -/
theorem e1_false_every_completion : ∀ c, Completion c run1 → evalF c chainE1 = V.F := by
  intro c hc
  rw [evalF_classical_of_noZ c hc.2 chainE1, e1_classical]
  generalize toBool (c 0) = b0
  generalize toBool (c 1) = b1
  generalize toBool (c 2) = b2
  generalize toBool (c 3) = b3
  generalize toBool (c 4) = b4
  generalize toBool (c 5) = b5
  generalize toBool (c 6) = b6
  generalize toBool (c 7) = b7
  generalize toBool (c 8) = b8
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;>
    cases b8 <;> rfl

/-- **The path that reads T** — why the F is not hereditary (and the judge says OPEN): after checking
v(2,1) = F, v(2,2) = T, v(3,1) = F, v(3,2) = T with v(2,3), v(3,3) still unchecked, the verdict is T, because
the laws over the two unchecked cells hold ON CREDIT (Z ↔ Z is F, and its negation T). -/
def path : Marking := fun n =>
  if n < 3 then V.T else if n = 3 then V.F else if n = 4 then V.T else if n = 6 then V.F
  else if n = 7 then V.T else V.Z

theorem path_refines : Refines path run1 := by
  intro n hn
  cases h : decide (n < 3) with
  | true =>
      have hl : n < 3 := of_decide_eq_true h
      show (if n < 3 then V.T else _) = (if n < 3 then V.T else V.Z)
      rw [if_pos hl, if_pos hl]
  | false =>
      have hl : ¬ n < 3 := of_decide_eq_false h
      exact absurd (show run1 n = V.Z from (show (if n < 3 then V.T else V.Z) = V.Z by rw [if_neg hl])) hn

theorem e1_path_reads_T : evalF path chainE1 = V.T := by decide

instance {p : Bool → Prop} [DecidablePred p] : Decidable (∃ b, p b) :=
  decidable_of_iff (p false ∨ p true)
    ⟨fun h => h.elim (fun hf => ⟨false, hf⟩) (fun ht => ⟨true, ht⟩),
     fun ⟨b, hb⟩ => by cases b
                       · exact Or.inl hb
                       · exact Or.inr hb⟩

instance {p : Bool → Prop} [DecidablePred p] : Decidable (∀ b, p b) :=
  decidable_of_iff (p false ∧ p true)
    ⟨fun h b => match b with
       | false => h.1
       | true  => h.2,
     fun h => ⟨h false, h true⟩⟩

/-- Fill the Z atoms among three named ones with x, y, z — a refinement by construction. -/
def fill3 (m : Marking) (a b c : Nat) (x y z : Bool) : Marking := fun n =>
  if m n = V.Z then (if n = a then ofBool x else if n = b then ofBool y else if n = c then ofBool z else m n)
  else m n

theorem fill3_refines (m : Marking) (a b c : Nat) (x y z : Bool) : Refines (fill3 m a b c x y z) m := by
  intro n hn
  show (if m n = V.Z then _ else m n) = m n
  rw [if_neg hn]

/-- The law of context k can be made T by filling its own unchecked atoms. -/
abbrev TurnableE1 (m : Marking) (k : Nat) : Prop :=
  ∃ x y z : Bool, evalF (fill3 m (cell k 0) (cell k 1) (cell k 2) x y z) (lawE1 k) = V.T

/-- Each of the six laws ALONE can still be made T in the run — none is refuted alone; only their
conjunction is false in every completion. -/
theorem e1_laws_alone :
    TurnableE1 run1 0 ∧ TurnableE1 run1 1 ∧ TurnableE1 run1 2 ∧
    TurnableE1 run1 3 ∧ TurnableE1 run1 4 ∧ TurnableE1 run1 5 := by decide

/-! ## E2, the contextual encoding (Bohm) — THE CONTROL -/

/-- The same run in E2: only the row-1 context's atoms (0, 1, 2) are witnessed. -/
def run2 : Marking := fun n => if n < 3 then V.T else if n < 18 then V.Z else V.F

/-- An explicit completion: every row-context value +1; column-context values +1 except the bottom of
column 3 (−1), so column 3 multiplies to −1. -/
def bohm : Marking := fun n => if n = 17 then V.F else if n < 18 then V.T else V.F

theorem bohm_completes : Completion bohm run2 := by
  refine ⟨?_, ?_⟩
  · intro n hn
    cases h : decide (n < 3) with
    | true =>
        have hl : n < 3 := of_decide_eq_true h
        have h17 : ¬ n = 17 := fun e => by rw [e] at hl; exact absurd hl (by decide)
        have h18 : n < 18 := Nat.lt_trans hl (by decide)
        show (if n = 17 then V.F else if n < 18 then V.T else V.F) = (if n < 3 then V.T else _)
        rw [if_neg h17, if_pos h18, if_pos hl]
    | false =>
        have hl : ¬ n < 3 := of_decide_eq_false h
        cases h' : decide (n < 18) with
        | true =>
            have h18 : n < 18 := of_decide_eq_true h'
            exact absurd (show run2 n = V.Z from
              (show (if n < 3 then V.T else if n < 18 then V.Z else V.F) = V.Z by rw [if_neg hl, if_pos h18])) hn
        | false =>
            have h18 : ¬ n < 18 := of_decide_eq_false h'
            have h17 : ¬ n = 17 := fun e => h18 (by rw [e]; decide)
            show (if n = 17 then V.F else if n < 18 then V.T else V.F) =
                 (if n < 3 then V.T else if n < 18 then V.Z else V.F)
            rw [if_neg h17, if_neg h18, if_neg hl, if_neg h18]
  · intro n
    show (if n = 17 then V.F else if n < 18 then V.T else V.F) ≠ V.Z
    cases h : decide (n = 17) with
    | true => rw [if_pos (of_decide_eq_true h)]; decide
    | false =>
        rw [if_neg (of_decide_eq_false h)]
        cases h' : decide (n < 18) with
        | true => rw [if_pos (of_decide_eq_true h')]; decide
        | false => rw [if_neg (of_decide_eq_false h')]; decide

/-- **THE CONTROL.** In the contextual encoding the same run is NOT refuted: a completion makes all six laws
true. The lens refutes non-contextual values (E1) and leaves contextual ones (Bohm) standing. -/
theorem e2_completion_T : evalF bohm chainE2 = V.T := by decide

/-! ## The run space: the rule never refutes a law of physics -/

/-- The rule's grounding of a run that asked context k and got answers s0 s1 s2 (E1). -/
def ground (k : Nat) (s0 s1 s2 : Bool) : Marking := fun n =>
  if n = cell k 0 then ofBool s0 else if n = cell k 1 then ofBool s1 else if n = cell k 2 then ofBool s2
  else if n < 9 then V.Z else V.F

/-- Physics allows exactly the answers whose product is the context's sign. -/
def allowed (k : Nat) (s0 s1 s2 : Bool) : Bool := (s0 == (s1 == s2)) == sign k

/-- In the run (k; s0 s1 s2), the law of context j can be made T. -/
abbrev TurnableIn (k : Nat) (s0 s1 s2 : Bool) (j : Nat) : Prop :=
  ∃ x y z : Bool, evalF (fill3 (ground k s0 s1 s2) (cell j 0) (cell j 1) (cell j 2) x y z) (lawE1 j) = V.T

abbrev AllTurnable (k : Nat) (s0 s1 s2 : Bool) : Prop :=
  TurnableIn k s0 s1 s2 0 ∧ TurnableIn k s0 s1 s2 1 ∧ TurnableIn k s0 s1 s2 2 ∧
  TurnableIn k s0 s1 s2 3 ∧ TurnableIn k s0 s1 s2 4 ∧ TurnableIn k s0 s1 s2 5

theorem run_space_row1 : ∀ s0 s1 s2 : Bool, allowed 0 s0 s1 s2 = true → AllTurnable 0 s0 s1 s2 := by decide
theorem run_space_row2 : ∀ s0 s1 s2 : Bool, allowed 1 s0 s1 s2 = true → AllTurnable 1 s0 s1 s2 := by decide
theorem run_space_row3 : ∀ s0 s1 s2 : Bool, allowed 2 s0 s1 s2 = true → AllTurnable 2 s0 s1 s2 := by decide
theorem run_space_col1 : ∀ s0 s1 s2 : Bool, allowed 3 s0 s1 s2 = true → AllTurnable 3 s0 s1 s2 := by decide
theorem run_space_col2 : ∀ s0 s1 s2 : Bool, allowed 4 s0 s1 s2 = true → AllTurnable 4 s0 s1 s2 := by decide
theorem run_space_col3 : ∀ s0 s1 s2 : Bool, allowed 5 s0 s1 s2 = true → AllTurnable 5 s0 s1 s2 := by decide

#print axioms physics
#print axioms holes
#print axioms evalF_classical_of_noZ
#print axioms e1_false_now
#print axioms e1_false_every_completion
#print axioms path_refines
#print axioms e1_path_reads_T
#print axioms fill3_refines
#print axioms e1_laws_alone
#print axioms bohm_completes
#print axioms e2_completion_T
#print axioms run_space_row1
#print axioms run_space_row2
#print axioms run_space_row3
#print axioms run_space_col1
#print axioms run_space_col2
#print axioms run_space_col3

end KochenSpecker
