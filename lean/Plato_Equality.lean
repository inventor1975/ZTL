/-
  Plato_Equality.lean  —  ZTL / dilemmas
  ---------------------------------------------------------------------------
  The Phaedo argument for the Form of Equality (74a–75b), formalised.

  Plato's argument, as usually reconstructed:

    P1  We judge sensible things to be equal.
    P2  (deficiency)  No sensibles are exactly equal; they "fall short".
    P3  We know that they fall short — so we possess the standard.
    P4  (no abstraction)  A standard cannot be got from instances that all
        deviate from it: to call something a deviation you must already hold
        the standard.
    C   Therefore the standard was not acquired from sense — the Equal Itself
        is prior and separate (anamnesis).

  Formalised below: P2 is a dilemma (Part I), P4 is false wherever deviation
  is measurable (Part II), and the Forms package that C delivers is outright
  inconsistent (Part III), with the load-bearing premise isolated by models.

  Self-contained: no imports, no mathlib.  Check with:

      lean Plato_Equality.lean

  Verified: Lean 4.29.1, no errors, no sorry.  All eleven public objects print
  "does not depend on any axioms" — the empty axiom list, not even propext.
-/

namespace Plato

/-! ## Part I.  The deficiency premise is a dilemma

Reading (a): "nothing sensible is exactly equal to anything sensible".
Read universally it denies self-identity, and is refuted by one line. -/

theorem deficiency_universal_absurd {S : Type} (eq : S → S → Prop)
    (rfl' : ∀ x, eq x x) (x : S) (h : ∀ a b, ¬ eq a b) : False :=
  h x x (rfl' x)

/-- Reading (b): distinct sensibles never share a magnitude exactly.  Here
`m x` is the magnitude of `x` — what a measurement returns. -/
def Deficiency {S M : Type} (m : S → M) : Prop := ∀ x y, x ≠ y → m x ≠ m y

/-- First finding, half one: injectivity of the magnitude map gives the
premise. -/
theorem injective_imp_deficiency {S M : Type} (m : S → M)
    (inj : ∀ x y, m x = m y → x = y) : Deficiency m :=
  fun x y hxy hm => hxy (inj x y hm)

/-- First finding, half two: the converse holds only if identity on sensibles
is already decidable.  So read, the premise is not a claim about deficiency at
all — it says the magnitude map is injective, i.e. that there are at least as
many magnitudes as things — and it says even that only on the assumption that
sensibles are exactly distinguishable from one another.  The exactness Plato
denies to the sensible world is required to state his denial. -/
theorem deficiency_imp_injective {S M : Type} (m : S → M)
    (dec : ∀ x y : S, x = y ∨ x ≠ y) (h : Deficiency m) :
    ∀ x y, m x = m y → x = y := by
  intro x y hm
  cases dec x y with
  | inl he  => exact he
  | inr hne => exact absurd hm (h x y hne)

/-- Second finding: so read, the premise is false as soon as magnitudes are
discrete and fewer than the things measured.  Two distinct bearers, one
magnitude, exact equality present in the sensible world. -/
theorem deficiency_fails_discrete :
    ¬ Deficiency (fun _ : Bool => (0 : Nat)) :=
  fun h => h true false (fun hc => Bool.noConfusion hc) rfl

/-! ## Part II.  The standard is the zero of the deviation

P4 says the standard cannot be extracted from the deviations.  But a deviation
is already a magnitude: `d a b` is *how far* a falls short of b.  Exactness is
then not a separate object glimpsed elsewhere — it is the vanishing of that
same measure.  The proof is one line, and the one line is the finding. -/

/-- `a` and `b` agree within tolerance `ε`. -/
def Approx {M : Type} (d : M → M → Nat) (ε : Nat) (a b : M) : Prop := d a b ≤ ε

theorem le_zero_eq {n : Nat} (h : n ≤ 0) : n = 0 := by
  cases n with
  | zero => rfl
  | succ k => exact absurd h (Nat.not_succ_le_zero k)

/-- Exact equality is `Approx` at tolerance 0.  Nothing is added to the
apparatus of approximation to obtain it; the limit case is inside the family,
not above it. -/
theorem exact_is_approx_zero {M : Type} (d : M → M → Nat)
    (sep : ∀ a b, d a b = 0 → a = b) (rfl' : ∀ a, d a a = 0) (a b : M) :
    Approx d 0 a b ↔ a = b := by
  constructor
  · intro h; exact sep a b (le_zero_eq h)
  · intro h; subst h; exact Nat.le_of_eq (rfl' a)

/-- P4 refuted: the standard is *definable* from the deviation data alone.
Whoever can say how far short a thing falls can say when it falls short by
nothing, and that is the standard.  No prior possession is required. -/
theorem standard_from_deviation {M : Type} (d : M → M → Nat)
    (sep : ∀ a b, d a b = 0 → a = b) (rfl' : ∀ a, d a a = 0) (a b : M) :
    a = b ↔ d a b = 0 :=
  ⟨fun h => by subst h; exact rfl' a, fun h => sep a b h⟩

/-- And in the discrete case the standard is not merely definable but
decidable: no faculty, no recollection, one comparison. -/
def standard_decidable (a b : Nat) : Decidable (a = b) := Nat.decEq a b

/-! ## Part III.  What the conclusion buys: the Forms package is inconsistent

The classical premises (Vlastos' reconstruction of the Third Man):

  OM  one over many — whatever bears the character has a Form in virtue of
      which it bears it;
  SP  self-predication — the Form of Equality is itself equal;
  NI  non-identity — the Form is not one of the things it is the Form of;
  U   uniqueness — one Form per character.

`f x` is the Form in virtue of which `x` bears the character. -/

structure Forms where
  D : Type
  Bears : D → Prop
  f : D → D
  witness : D
  bears_witness : Bears witness
  SP : ∀ x, Bears x → Bears (f x)
  NI : ∀ x, Bears x → f x ≠ x
  U  : ∀ x y, Bears x → Bears y → f x = f y

/-- The four premises are jointly inconsistent.  Three lines: the Form is a
bearer (SP), so by uniqueness it is its own Form, which non-identity forbids. -/
theorem third_man (P : Forms) : False :=
  P.NI (P.f P.witness) (P.SP _ P.bears_witness)
    (P.U _ _ P.bears_witness (P.SP _ P.bears_witness)).symm

/-! ### Discrimination: which premise carries the contradiction

An impossibility proved about nothing in particular proves nothing.  Two
models show that the collapse is located exactly at NI — at *separation*. -/

/-- Drop NI, keep OM, SP, U: consistent.  The model is the fixed point — the
Form is its own Form, the ground is not other than the grounded. -/
structure Forms_noNI where
  D : Type
  Bears : D → Prop
  f : D → D
  witness : D
  bears_witness : Bears witness
  SP : ∀ x, Bears x → Bears (f x)
  U  : ∀ x y, Bears x → Bears y → f x = f y

def selfGrounding : Forms_noNI where
  D := Unit
  Bears := fun _ => True
  f := id
  witness := ()
  bears_witness := trivial
  SP := fun _ _ => trivial
  U := fun _ _ _ _ => rfl

/-- Drop U instead, keep OM, SP, NI: also consistent — but the model is the
successor, i.e. an unending tower of Forms.  Consistency is bought with
regress. -/
structure Forms_noU where
  D : Type
  Bears : D → Prop
  f : D → D
  witness : D
  bears_witness : Bears witness
  SP : ∀ x, Bears x → Bears (f x)
  NI : ∀ x, Bears x → f x ≠ x

def tower : Forms_noU where
  D := Nat
  Bears := fun _ => True
  f := Nat.succ
  witness := 0
  bears_witness := trivial
  SP := fun _ _ => trivial
  NI := fun n _ => Nat.succ_ne_self n

/-! ## Part IV.  The tower never grounds

If separation is kept, no finite chain of Forms terminates: at every floor the
explanation is still owed.  Grounding and separation cannot both be had. -/

def iter {D : Type} (f : D → D) : Nat → D → D
  | 0,     x => x
  | (n+1), x => f (iter f n x)

theorem no_grounded_regress {D : Type} (f : D → D)
    (NI : ∀ x, f x ≠ x) (x : D) (n : Nat) : iter f n x ≠ iter f (n+1) x :=
  fun h => NI (iter f n x) h.symm

/-! ## Verdict

  P2  is a dilemma: universal, it is absurd (deficiency_universal_absurd);
      restricted, it is not about deficiency but about injectivity of the
      magnitude map (injective_imp_deficiency, deficiency_imp_injective), and
      that reading itself needs decidable identity on sensibles — the very
      exactness the premise denies them; and it fails outright where
      magnitudes are discrete (deficiency_fails_discrete).
  P4  is false wherever falling-short is measurable at all: the standard is
      the zero of the very measure (standard_from_deviation), and in the
      discrete case it is decided, not recollected (standard_decidable).
  C   is not merely unsupported but inconsistent (third_man), and the
      inconsistency sits in NI — in the demand that the ground be *other*
      than the grounded (selfGrounding), the alternative being an ungrounded
      tower (tower, no_grounded_regress).

So the answer to "is it legitimate, or is it a paradox" is: a paradox, and a
locatable one.  What survives is the negative core Plato himself supplies —
the character cannot be a further thing of the same kind.  The operational
reading takes exactly that and drops the separation: the ground of equality is
the fixed point, the operation applied zero times, not a second object above
the first.
-/

end Plato

#print axioms Plato.deficiency_universal_absurd
#print axioms Plato.injective_imp_deficiency
#print axioms Plato.deficiency_imp_injective
#print axioms Plato.standard_decidable
#print axioms Plato.deficiency_fails_discrete
#print axioms Plato.exact_is_approx_zero
#print axioms Plato.standard_from_deviation
#print axioms Plato.third_man
#print axioms Plato.selfGrounding
#print axioms Plato.tower
#print axioms Plato.no_grounded_regress
