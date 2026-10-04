/-
  Hardy.lean — Hardy's paradox through the ZTL lens, kernel-checked: the physics (exact, in integers),
  the mechanical grounding rule, the verdicts and their grades.

  Companion of `dilemmas/hardy.py` (2026-10-04, prediction written before the run). The curator asked for
  the stand to stand on the same floor as the logic: a theorem, not only a program with asserts.

  THE PHYSICS, exactly. |ψ⟩ ∝ |00⟩ + |01⟩ + |10⟩ (norm² 3); Z-basis vectors (1,0), (0,1) (norm² 1);
  X-basis vectors (1,1), (1,−1) (norm² 2). With UNNORMALIZED integer vectors the amplitude ⟨a⊗b|ψ⟩ is an
  integer, and P = amp² / (‖a‖²·‖b‖²·3). So:
    amp(X−, X−) = −1        → P = 1/(2·2·3) = 1/12   (the contested run happens)
    amp(X−, Z0) = 0, amp(Z0, X−) = 0, amp(Z1, Z1) = 0  (the three certainties)
  and 2·P(X−) = [[1,−1],[−1,1]] does not commute with P(Z1) = [[0,0],[0,1]] — the two questions cannot
  be asked together. All of it by `decide` on integers.

  THE RULE (the same as the stand's). In a run each party asked ONE question:
    an atom about the asked question → T/F by the answer; an atom about the other (non-commuting)
    question → Z. Atoms: 0 = "X_A = −", 1 = "X_B = −", 2 = "Z_A = 1", 3 = "Z_B = 1".

  THE THEOREMS.
    contested_occurs        the run X_A = X_B = − has nonzero amplitude
    contested_false         the chain evaluates F
    contested_hereditary    and stays F along EVERY refinement (REFUTED, not merely sound)
    laws_alone_survive      each of the three laws alone can still turn T (none refuted alone)
    control_earned          a run where Bob ASKED Z after X_A = −: "Z_B = 1" and its law earned, hereditary
    no_law_refuted          the run space: for every run that happens (nonzero amplitude) and every law,
                            some refinement makes the law T — the rule never refutes a law of physics

  The honest split, as in Contextuality.lean: Lean checks the arithmetic, the rule as written, and the
  logic. That "unasked and non-commuting ↦ Z" is the right reading of an unasked question is the rule —
  a premise, stated, not derived.

  VR discipline: self-contained (no imports, no mathlib), `#print axioms` at the end — the whole file
  stands on the EMPTY axiom list.
-/

namespace Hardy

/-! ## The physics, in integers

Signed integers as pairs of naturals (positive part, negative part), compared through `Nat` — `Int`'s
decidable equality would pull `propext` into every theorem (measured on the first draft of this file). -/

/-- A signed integer p − n. -/
abbrev S := Nat × Nat

def sadd (x y : S) : S := (x.1 + y.1, x.2 + y.2)
def smul (x y : S) : S := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
/-- x = y as integers. -/
def seq (x y : S) : Bool := Nat.beq (x.1 + y.2) (y.1 + x.2)

def one : S := (1, 0)
def zero : S := (0, 0)
def neg1 : S := (0, 1)

/-- A question's answer vector, unnormalized: (question X?, answer bit). Z: 0 ↦ (1,0), 1 ↦ (0,1);
X: "+" (false) ↦ (1,1), "−" (true) ↦ (1,−1). -/
def vec : Bool → Bool → S × S
  | false, false => (one, zero)
  | false, true  => (zero, one)
  | true,  false => (one, one)
  | true,  true  => (one, neg1)

/-- ψ ∝ |00⟩ + |01⟩ + |10⟩. -/
def psi : Bool → Bool → S                      -- every row written out: a wildcard row would pull
  | false, false => one                          -- propext through the compiled matcher (Lean trap)
  | false, true  => one
  | true,  false => one
  | true,  true  => zero

def comp (v : S × S) : Bool → S
  | false => v.1
  | true  => v.2

/-- The integer amplitude ⟨a⊗b|ψ⟩ (A asks qa, answers oa; B asks qb, answers ob). -/
def amp (qa oa qb ob : Bool) : S :=
  sadd (sadd (smul (smul (comp (vec qa oa) false) (comp (vec qb ob) false)) (psi false false))
             (smul (smul (comp (vec qa oa) false) (comp (vec qb ob) true))  (psi false true)))
       (sadd (smul (smul (comp (vec qa oa) true)  (comp (vec qb ob) false)) (psi true false))
             (smul (smul (comp (vec qa oa) true)  (comp (vec qb ob) true))  (psi true true)))

/-- The run happens: nonzero amplitude. -/
def occurs (qa oa qb ob : Bool) : Bool := !(seq (amp qa oa qb ob) zero)

/-- The contested run happens: amp(X−, X−) = −1, i.e. P = 1/(2·2·3) = 1/12. -/
theorem contested_occurs : seq (amp true true true true) neg1 = true := by decide

/-- The three certainties: P(X_A=−, Z_B=0) = P(Z_A=0, X_B=−) = P(Z_A=1, Z_B=1) = 0. -/
theorem certainties :
    occurs true true false false = false ∧ occurs false false true true = false ∧
    occurs false true false true = false := by
  decide

/-- 2×2 signed matrices. -/
structure M2 where
  a : S
  b : S
  c : S
  d : S

def mmul (x y : M2) : M2 :=
  ⟨sadd (smul x.a y.a) (smul x.b y.c), sadd (smul x.a y.b) (smul x.b y.d),
   sadd (smul x.c y.a) (smul x.d y.c), sadd (smul x.c y.b) (smul x.d y.d)⟩

def meq (x y : M2) : Bool := seq x.a y.a && seq x.b y.b && seq x.c y.c && seq x.d y.d

/-- Projector onto Z = 1, and twice the projector onto X = −. -/
def pZ1 : M2 := ⟨zero, zero, zero, one⟩
def pXm2 : M2 := ⟨one, neg1, neg1, one⟩

/-- The two questions do not commute: [P(Z=1), 2P(X=−)] ≠ 0. -/
theorem incompatible : meq (mmul pZ1 pXm2) (mmul pXm2 pZ1) = false := by decide

/-! ## The logic (a mirror of ZTime.lean's core, as every file here carries its own) -/

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
def zimp : V → V → V := lift2 (fun a b => !a || b)

end V

open V

inductive Fm where
  | atom : Nat → Fm
  | neg  : Fm → Fm
  | conj : Fm → Fm → Fm
  | imp  : Fm → Fm → Fm

def Marking := Nat → V

def evalF (m : Marking) : Fm → V
  | .atom n   => m n
  | .neg φ    => znot (evalF m φ)
  | .conj φ ψ => zand (evalF m φ) (evalF m ψ)
  | .imp φ ψ  => zimp (evalF m φ) (evalF m ψ)

def Refines (m' m : Marking) : Prop :=
  ∀ n, m n ≠ V.Z → m' n = m n

def Hereditary (φ : Fm) (m : Marking) : Prop :=
  ∀ m', Refines m' m → evalF m' φ = evalF m φ

/-! ## The chain and its three laws -/

def xa : Fm := .atom 0
def xb : Fm := .atom 1
def za : Fm := .atom 2
def zb : Fm := .atom 3

def law1 : Fm := .imp xa zb                      -- X_A = − → Z_B = 1
def law2 : Fm := .imp xb za                      -- X_B = − → Z_A = 1
def law3 : Fm := .neg (.conj za zb)              -- never Z_A = 1 ∧ Z_B = 1
def chain : Fm := .conj xa (.conj xb (.conj law1 (.conj law2 law3)))

/-! ## The rule -/

def ofBool : Bool → V
  | true  => V.T
  | false => V.F

/-- THE RULE: A asked qa (X? true) and got oa; B asked qb, got ob. An atom about the asked question is
T/F by the answer ("X = −" ↔ X asked and answer bit true; "Z = 1" ↔ Z asked and answer bit true); an
atom about the question not asked is Z. -/
def ground (qa oa qb ob : Bool) : Marking := fun n =>
  if n = 0 then (if qa then ofBool oa else V.Z)
  else if n = 1 then (if qb then ofBool ob else V.Z)
  else if n = 2 then (if qa then V.Z else ofBool oa)
  else if n = 3 then (if qb then V.Z else ofBool ob)
  else V.F

/-- The contested run grounded by the rule. -/
def contested : Marking := ground true true true true

theorem contested_marks :
    contested 0 = V.T ∧ contested 1 = V.T ∧ contested 2 = V.Z ∧ contested 3 = V.Z := by decide

/-- The chain's value depends on the four atoms only. -/
def chainV (a b c d : V) : V :=
  zand a (zand b (zand (zimp a d) (zand (zimp b c) (znot (zand c d)))))

theorem chain_eval (m : Marking) : evalF m chain = chainV (m 0) (m 1) (m 2) (m 3) := rfl

theorem contested_false : evalF contested chain = V.F := by decide

/-- **REFUTED, not merely sound**: along every refinement of the contested run the chain stays F —
whatever the two unasked answers turn out to be, and at every step on the way. -/
theorem contested_hereditary : Hereditary chain contested := by
  intro m' h
  have h0 : m' 0 = V.T := h 0 (by decide)
  have h1 : m' 1 = V.T := h 1 (by decide)
  rw [chain_eval, chain_eval, h0, h1]
  generalize m' 2 = c
  generalize m' 3 = d
  cases c <;> cases d <;> decide

/-- Fill the Z atoms of `m` by `g` — a refinement by construction. -/
def fill (m : Marking) (g : Nat → V) : Marking := fun n => if m n = V.Z then g n else m n

theorem fill_refines (m : Marking) (g : Nat → V) : Refines (fill m g) m := by
  intro n hn
  show (if m n = V.Z then g n else m n) = m n
  rw [if_neg hn]

def four (b0 b1 b2 b3 : Bool) : Nat → V := fun n =>
  if n = 0 then ofBool b0 else if n = 1 then ofBool b1 else if n = 2 then ofBool b2 else ofBool b3

instance {p : Bool → Prop} [DecidablePred p] : Decidable (∃ b, p b) :=
  decidable_of_iff (p false ∨ p true)
    ⟨fun h => h.elim (fun hf => ⟨false, hf⟩) (fun ht => ⟨true, ht⟩),
     fun ⟨b, hb⟩ => by cases b
                       · exact Or.inl hb
                       · exact Or.inr hb⟩

/-- In the contested run each law ALONE can still turn T (law3 is T already, on credit): none of the
three is refuted alone — only their conjunction is. -/
theorem laws_alone_survive :
    (∃ b0 b1 b2 b3 : Bool, evalF (fill contested (four b0 b1 b2 b3)) law1 = V.T) ∧
    (∃ b0 b1 b2 b3 : Bool, evalF (fill contested (four b0 b1 b2 b3)) law2 = V.T) ∧
    (∃ b0 b1 b2 b3 : Bool, evalF (fill contested (four b0 b1 b2 b3)) law3 = V.T) := by decide

/-! ## The control: where the rule could have failed -/

/-- Alice asked X and got −, Bob ASKED Z: the run happens only with Z_B = 1 (amplitude), and there the
rule earns "Z_B = 1" and the law X_A = − → Z_B = 1, hereditarily. -/
theorem control_occurs : occurs true true false true = true ∧ occurs true true false false = false := by
  decide

def control : Marking := ground true true false true

theorem control_earned :
    evalF control zb = V.T ∧ evalF control law1 = V.T ∧ Hereditary law1 control := by
  refine ⟨by decide, by decide, ?_⟩
  intro m' h
  have h0 : m' 0 = V.T := h 0 (by decide)
  have h3 : m' 3 = V.T := h 3 (by decide)
  show zimp (m' 0) (m' 3) = zimp (control 0) (control 3)
  rw [h0, h3]
  decide

/-- The mirror: Bob got X = −, Alice ASKED Z → "Z_A = 1" and law2 earned. -/
theorem control_mirror :
    occurs false true true true = true ∧ occurs false false true true = false ∧
    evalF (ground false true true true) za = V.T ∧ evalF (ground false true true true) law2 = V.T := by
  decide

/-! ## The run space: the rule never refutes a law of physics -/

/-- For every run that happens (nonzero amplitude) and each of the three laws, some refinement of the
rule's grounding makes the law T — no law is ever refuted (REFUTED needs F along every refinement). -/
theorem no_law_refuted :
    ∀ qa oa qb ob : Bool, occurs qa oa qb ob = true →
      (∃ b0 b1 b2 b3 : Bool, evalF (fill (ground qa oa qb ob) (four b0 b1 b2 b3)) law1 = V.T) ∧
      (∃ b0 b1 b2 b3 : Bool, evalF (fill (ground qa oa qb ob) (four b0 b1 b2 b3)) law2 = V.T) ∧
      (∃ b0 b1 b2 b3 : Bool, evalF (fill (ground qa oa qb ob) (four b0 b1 b2 b3)) law3 = V.T) := by
  decide

/-- How many of the 16 question/answer combinations happen: 13 (the stand's count). -/
def happens : List (Bool × Bool × Bool × Bool) :=
  [false, true].foldr (fun qa acc => [false, true].foldr (fun oa acc => [false, true].foldr
    (fun qb acc => [false, true].foldr (fun ob acc =>
      if occurs qa oa qb ob then (qa, oa, qb, ob) :: acc else acc) acc) acc) acc) []

theorem thirteen_runs : happens.length = 13 := by decide

#print axioms contested_occurs
#print axioms certainties
#print axioms incompatible
#print axioms contested_marks
#print axioms contested_false
#print axioms contested_hereditary
#print axioms fill_refines
#print axioms laws_alone_survive
#print axioms control_occurs
#print axioms control_earned
#print axioms control_mirror
#print axioms no_law_refuted
#print axioms thirteen_runs

end Hardy
