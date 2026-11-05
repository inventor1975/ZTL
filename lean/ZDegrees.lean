/-
  ZDegrees.lean — EVERY TABLE OF ZTL IS THE {lower = 1}-THRESHOLD OF ITS DEGREES.

  THE CLAIM (2026-11-05). ZTL with degrees: a statement may carry a probability of being true. The three published
  values are three degrees — T is [1,1], F is [0,0], Z is the whole [0,1] — and how two statements are joined is
  NOT known (the dirty parameter). The degree of a connective's result is then the interval over every joint
  distribution that keeps each argument's own degree (Boole, Fréchet). ZTL's table answers T exactly when the lower
  end of that interval is 1 — when EVERY such joint puts all its weight where the connective holds — and F
  otherwise. MEASURED on all 16 + 4 published tables (zfrechet_tables.py, 0 differ); PROVED here for EVERY binary
  and unary connective, so a table that is not published (or a published one mistyped) cannot slip past.

  THE ENCODING IS PROBABILITY'S, NOT OURS. A joint of two statements is a weight on each of the four worlds; the
  weights are natural numbers, as in ZDempster (E35): the threshold "all the weight" is scale-free, so nothing is
  lost and no rational arithmetic is imported. "a has degree 1" is "no weight on the worlds where a is false",
  "degree 0" is "no weight where a is true", Z constrains nothing. Nothing about ZTL's `lift2` enters these
  definitions — the correspondence would prove nothing if one side were defined out of the other.

  WHAT ELSE IS SAID, BECAUSE IT IS TRUE. A COMPOUND is read node by node: each connective projects, then the next
  one reads that T or F. That is NOT the threshold of the whole formula's degree — ¬(a∧b) at Z, Z is T in ZTL
  (a∧b is not forced, so it is F, and ¬F is T), while some joint gives ¬(a∧b) degree 0. Both readings are ZTL's:
  the TABLES are the node-by-node one, the JUDGE's dispositions the whole-formula one (zfrechet.py, measured on
  10 800 verdicts). `compound_is_node_by_node` pins the difference down.

  FORM. The proof goes through the connective's own truth table `tab p q r s` and returns to an arbitrary f by
  `rfl` — `lift2` and `mass` only ever look at f on the four worlds — so no `funext` (which carries Quot.sound).
  Arithmetic by hand, no `omega`, no `simp`: both measured to carry propext here.
-/
import ZTL

namespace ZDegrees

open V

/-! ### The probability side -/

/-- A joint distribution of two statements: a weight on each world (a, b). -/
structure J where
  tt : Nat
  tf : Nat
  ft : Nat
  ff : Nat

def total (μ : J) : Nat := μ.tt + μ.tf + μ.ft + μ.ff

/-- The weight of a world if the connective holds there, else nothing. -/
def sel : Bool → Nat → Nat
  | true,  n => n
  | false, _ => 0

/-- The weight the joint gives to the worlds where `f` holds. -/
def mass (f : Bool → Bool → Bool) (μ : J) : Nat :=
  sel (f true true) μ.tt + sel (f true false) μ.tf + sel (f false true) μ.ft + sel (f false false) μ.ff

/-- A value as a degree, i.e. a constraint on one marginal: `w1` the weight where the statement is true, `w0`
where it is false. T: degree 1 (nothing where false); F: degree 0 (nothing where true); Z: [0,1], no constraint. -/
def deg : V → Nat → Nat → Prop
  | T, _,  w0 => w0 = 0
  | F, w1, _  => w1 = 0
  | Z, _,  _  => True

/-- The joint keeps each argument's own degree — the Fréchet set for these two degrees. -/
def adm (x y : V) (μ : J) : Prop :=
  deg x (μ.tt + μ.tf) (μ.ft + μ.ff) ∧ deg y (μ.tt + μ.ft) (μ.tf + μ.ff)

/-! ### The same for one statement -/

structure J1 where
  t : Nat
  f : Nat

def total1 (μ : J1) : Nat := μ.t + μ.f
def mass1 (g : Bool → Bool) (μ : J1) : Nat := sel (g true) μ.t + sel (g false) μ.f
def adm1 (x : V) (μ : J1) : Prop := deg x μ.t μ.f

/-! ### The connective as its own truth table -/

def tab (p q r s : Bool) : Bool → Bool → Bool
  | true,  true  => p
  | true,  false => q
  | false, true  => r
  | false, false => s

def tab1 (p q : Bool) : Bool → Bool
  | true  => p
  | false => q

/-! ### Arithmetic, by hand -/

theorem z2 {a b : Nat} (h : a + b = 0) : a = 0 ∧ b = 0 := by
  cases b with
  | zero   => exact ⟨h, rfl⟩
  | succ n => exact Nat.noConfusion h

/-! ### The theorem on a truth table -/

/-- ZTL's lift of the table answers T iff every joint keeping the degrees puts all its weight where it holds. -/
theorem table_projection (p q r s : Bool) (x y : V) :
    lift2 (tab p q r s) x y = T ↔ ∀ μ : J, adm x y μ → mass (tab p q r s) μ = total μ := by
  constructor
  · intro hf μ hμ
    obtain ⟨a, b, c, d⟩ := μ
    cases x <;> cases y
    -- (T, T): no weight off (true, true)
    · obtain ⟨h1, h2⟩ := hμ
      obtain ⟨hc, hd⟩ := z2 h1
      obtain ⟨hb, -⟩ := z2 h2
      subst hc hd hb
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (T, F)
    · obtain ⟨h1, h2⟩ := hμ
      obtain ⟨hc, hd⟩ := z2 h1
      obtain ⟨ha, -⟩ := z2 h2
      subst hc hd ha
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (T, Z)
    · obtain ⟨h1, -⟩ := hμ
      obtain ⟨hc, hd⟩ := z2 h1
      subst hc hd
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (F, T)
    · obtain ⟨h1, h2⟩ := hμ
      obtain ⟨ha, hb⟩ := z2 h1
      obtain ⟨-, hd⟩ := z2 h2
      subst ha hb hd
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (F, F)
    · obtain ⟨h1, h2⟩ := hμ
      obtain ⟨ha, hb⟩ := z2 h1
      obtain ⟨-, hc⟩ := z2 h2
      subst ha hb hc
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (F, Z)
    · obtain ⟨h1, -⟩ := hμ
      obtain ⟨ha, hb⟩ := z2 h1
      subst ha hb
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (Z, T)
    · obtain ⟨-, h2⟩ := hμ
      obtain ⟨hb, hd⟩ := z2 h2
      subst hb hd
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (Z, F)
    · obtain ⟨-, h2⟩ := hμ
      obtain ⟨ha, hc⟩ := z2 h2
      subst ha hc
      cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
    -- (Z, Z): no constraint
    · cases p <;> cases q <;> cases r <;> cases s <;> first | rfl | exact absurd hf (by decide)
  · intro h
    -- where the lift answers F, a point mass on an allowed world where the table fails refutes the right side
    cases x <;> cases y <;> cases p <;> cases q <;> cases r <;> cases s <;>
      first
      | rfl
      | exact absurd (h ⟨1, 0, 0, 0⟩ ⟨by first | rfl | trivial, by first | rfl | trivial⟩) (by decide)
      | exact absurd (h ⟨0, 1, 0, 0⟩ ⟨by first | rfl | trivial, by first | rfl | trivial⟩) (by decide)
      | exact absurd (h ⟨0, 0, 1, 0⟩ ⟨by first | rfl | trivial, by first | rfl | trivial⟩) (by decide)
      | exact absurd (h ⟨0, 0, 0, 1⟩ ⟨by first | rfl | trivial, by first | rfl | trivial⟩) (by decide)

theorem table_projection1 (p q : Bool) (x : V) :
    lift1 (tab1 p q) x = T ↔ ∀ μ : J1, adm1 x μ → mass1 (tab1 p q) μ = total1 μ := by
  constructor
  · intro hf μ hμ
    obtain ⟨a, b⟩ := μ
    cases x
    · have hb : b = 0 := hμ
      subst hb
      cases p <;> cases q <;> first | rfl | exact absurd hf (by decide)
    · have ha : a = 0 := hμ
      subst ha
      cases p <;> cases q <;> first | rfl | exact absurd hf (by decide)
    · cases p <;> cases q <;> first | rfl | exact absurd hf (by decide)
  · intro h
    cases x <;> cases p <;> cases q <;>
      first
      | rfl
      | exact absurd (h ⟨1, 0⟩ (by first | rfl | trivial)) (by decide)
      | exact absurd (h ⟨0, 1⟩ (by first | rfl | trivial)) (by decide)

/-! ### Back to an arbitrary connective, by `rfl` -/

theorem lift2_tab (f : Bool → Bool → Bool) (x y : V) :
    lift2 f x y = lift2 (tab (f true true) (f true false) (f false true) (f false false)) x y := by
  cases x <;> cases y <;> rfl

theorem mass_tab (f : Bool → Bool → Bool) (μ : J) :
    mass f μ = mass (tab (f true true) (f true false) (f false true) (f false false)) μ := rfl

theorem lift1_tab (g : Bool → Bool) (x : V) : lift1 g x = lift1 (tab1 (g true) (g false)) x := by
  cases x <;> rfl

theorem mass1_tab (g : Bool → Bool) (μ : J1) : mass1 g μ = mass1 (tab1 (g true) (g false)) μ := rfl

/-- THE THEOREM. For EVERY binary connective and every pair of inputs among T, F, Z: ZTL's table answers T exactly
when every joint distribution keeping the inputs' degrees gives the connective all its weight — the lower end of
the Fréchet interval is 1. (Two-valued output: otherwise the table answers F, `lift2_classical`.) -/
theorem projection (f : Bool → Bool → Bool) (x y : V) :
    lift2 f x y = T ↔ ∀ μ : J, adm x y μ → mass f μ = total μ := by
  rw [lift2_tab f x y]
  exact ⟨fun h μ hμ => (mass_tab f μ).trans ((table_projection _ _ _ _ x y).mp h μ hμ),
         fun h => (table_projection _ _ _ _ x y).mpr (fun μ hμ => (mass_tab f μ).symm.trans (h μ hμ))⟩

/-- The same for every one-argument connective (identity, negation, the two constants). -/
theorem projection1 (g : Bool → Bool) (x : V) :
    lift1 g x = T ↔ ∀ μ : J1, adm1 x μ → mass1 g μ = total1 μ := by
  rw [lift1_tab g x]
  exact ⟨fun h μ hμ => (mass1_tab g μ).trans ((table_projection1 _ _ x).mp h μ hμ),
         fun h => (table_projection1 _ _ x).mpr (fun μ hμ => (mass1_tab g μ).symm.trans (h μ hμ))⟩

/-- The six connectives of the code, as instances. -/
theorem and_projection (x y : V) : zand x y = T ↔ ∀ μ : J, adm x y μ → mass (fun a b => a && b) μ = total μ :=
  projection _ x y
theorem or_projection (x y : V) : zor x y = T ↔ ∀ μ : J, adm x y μ → mass (fun a b => a || b) μ = total μ :=
  projection _ x y
theorem imp_projection (x y : V) : zimp x y = T ↔ ∀ μ : J, adm x y μ → mass (fun a b => !a || b) μ = total μ :=
  projection _ x y
theorem not_projection (x : V) : znot x = T ↔ ∀ μ : J1, adm1 x μ → mass1 (fun a => !a) μ = total1 μ :=
  projection1 _ x

/-! ### A compound is projected node by node, not as a whole -/

/-- ¬(a ∧ b) at Z, Z: ZTL's table says T (the inner ∧ is not forced, F, and ¬F is T), yet a joint keeping both
degrees — all the weight on (true, true) — gives ¬(a ∧ b) no weight at all. The tables are the node-by-node
projection; the whole formula's threshold is the judge's reading, not the table's. -/
theorem compound_is_node_by_node :
    znot (zand Z Z) = T ∧ ∃ μ : J, adm Z Z μ ∧ mass (fun a b => !(a && b)) μ ≠ total μ :=
  ⟨rfl, ⟨1, 0, 0, 0⟩, ⟨trivial, trivial⟩, by decide⟩

end ZDegrees

#print axioms ZDegrees.z2
#print axioms ZDegrees.table_projection
#print axioms ZDegrees.table_projection1
#print axioms ZDegrees.projection
#print axioms ZDegrees.projection1
#print axioms ZDegrees.and_projection
#print axioms ZDegrees.not_projection
#print axioms ZDegrees.compound_is_node_by_node
