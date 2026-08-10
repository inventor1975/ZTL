/-!
# ZNum — the numeric floor: narrowing is monotone, forced verdicts are hereditary

The kernel-checked half of expedition E37 (`znum.py`). The measured bet:
on numeric atoms a verdict forced by the current intervals can never be
revoked by any further verification (narrowing) — hereditary in ONE pass,
against the m−1-deep enumeration the propositional grade requires (§19 of
the preprint).

Semantics: an expression's meaning is its SET OF READINGS. A quantity
reads any value inside its interval; every occurrence chooses its reading
independently — decorrelation (fork F1) is built into the derivation
structure, one choice per subterm. Narrowing shrinks every leaf's reading
set, hence (structurally) every expression's reading set; a verdict
quantified over all readings therefore survives. Division is excluded
from this kernel: an interval divisor containing 0 makes the subterm
undefined and the atom takes the mark — that path is measured in
`znum.py`, not proved here.

VR discipline: `#print axioms` at the end — the whole module must stand
on the empty axiom list.
-/

/-- An interval of integer readings, bounds inclusive. Well-formedness
(`lo ≤ hi`) is not needed for heredity; it enters only in the
nonvacuity theorem. -/
structure Iv where
  lo : Int
  hi : Int

/-- `v` is a reading of the interval. -/
def Iv.mem (i : Iv) (v : Int) : Prop := i.lo ≤ v ∧ v ≤ i.hi

/-- Numeric expressions over indexed quantities and constants. -/
inductive Expr where
  | const : Int → Expr
  | qty   : Nat → Expr
  | add   : Expr → Expr → Expr
  | sub   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr

/-- A marking: the current interval of every quantity. -/
def Marking := Nat → Iv

/-- The reading relation. Decorrelated by construction: each occurrence
of a quantity carries its own derivation, hence its own choice. -/
inductive Reads (m : Marking) : Expr → Int → Prop where
  | const : Reads m (.const c) c
  | qty   : (m i).mem v → Reads m (.qty i) v
  | add   : Reads m a x → Reads m b y → Reads m (.add a b) (x + y)
  | sub   : Reads m a x → Reads m b y → Reads m (.sub a b) (x - y)
  | mul   : Reads m a x → Reads m b y → Reads m (.mul a b) (x * y)

/-- `m'` narrows `m`: every quantity's reading set shrinks. (Extensional
form; the endpoint form implies it — `endpoint_narrows` below.) -/
def Narrows (m' m : Marking) : Prop := ∀ i v, (m' i).mem v → (m i).mem v

/-- Monotonicity: a reading under the narrowed marking is a reading under
the wide one. Pure structural induction — no arithmetic enters. -/
theorem reads_mono {m' m : Marking} (h : Narrows m' m) :
    ∀ {e : Expr} {v : Int}, Reads m' e v → Reads m e v := by
  intro e v r
  induction r with
  | const => exact .const
  | qty hv => exact .qty (h _ _ hv)
  | add _ _ ia ib => exact .add ia ib
  | sub _ _ ia ib => exact .sub ia ib
  | mul _ _ ia ib => exact .mul ia ib

/-! ## Forced verdicts — the generating principle over readings

A comparison is `T` when forced under EVERY reading, `F` when its
negation is forced; otherwise the atom keeps the mark. Six shapes:
the T-side and the F-side of `≤`, `<`, `=`. -/

def ForcedLE (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, Reads m a x → Reads m b y → x ≤ y

def ForcedNotLE (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, Reads m a x → Reads m b y → y < x

def ForcedLT (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, Reads m a x → Reads m b y → x < y

def ForcedNotLT (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, Reads m a x → Reads m b y → y ≤ x

def ForcedEQ (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, Reads m a x → Reads m b y → x = y

def ForcedNE (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, Reads m a x → Reads m b y → x ≠ y

/-! ## THE BET, kernel-checked

Every forced shape survives every narrowing. Each proof is the same one
line: route the narrowed readings through `reads_mono`. This is why the
numeric grade needs one pass and no enumeration: heredity is not an
extra property to check, it is the shape of forcing itself. -/

theorem forcedLE_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedLE m a b → ForcedLE m' a b :=
  fun f _ _ ra rb => f _ _ (reads_mono h ra) (reads_mono h rb)

theorem forcedNotLE_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedNotLE m a b → ForcedNotLE m' a b :=
  fun f _ _ ra rb => f _ _ (reads_mono h ra) (reads_mono h rb)

theorem forcedLT_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedLT m a b → ForcedLT m' a b :=
  fun f _ _ ra rb => f _ _ (reads_mono h ra) (reads_mono h rb)

theorem forcedNotLT_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedNotLT m a b → ForcedNotLT m' a b :=
  fun f _ _ ra rb => f _ _ (reads_mono h ra) (reads_mono h rb)

theorem forcedEQ_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedEQ m a b → ForcedEQ m' a b :=
  fun f _ _ ra rb => f _ _ (reads_mono h ra) (reads_mono h rb)

theorem forcedNE_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedNE m a b → ForcedNE m' a b :=
  fun f _ _ ra rb => f _ _ (reads_mono h ra) (reads_mono h rb)

/-! ## Bridges and nonvacuity -/

/-- Endpoint narrowing (`lo` may only rise, `hi` may only fall) implies
extensional narrowing. Transitivity of `≤` is taken as a hypothesis:
core's `Int.le_trans` (and even `Int.le_refl`) carry `propext` in this
toolchain — the §8 disinfection pitfall, measured again here — so the
clean module states the bridge generically and concrete markings
discharge the bound by `decide`. -/
theorem endpoint_narrows {m' m : Marking}
    (htrans : ∀ {a b c : Int}, a ≤ b → b ≤ c → a ≤ c)
    (h : ∀ i, (m i).lo ≤ (m' i).lo ∧ (m' i).hi ≤ (m i).hi) :
    Narrows m' m :=
  fun i _ hv => ⟨htrans (h i).1 hv.1, htrans hv.2 (h i).2⟩

/-- Narrowing composes: verification paths of any length are covered by
the one-step theorems. -/
theorem narrows_trans {m'' m' m : Marking}
    (h1 : Narrows m'' m') (h2 : Narrows m' m) : Narrows m'' m :=
  fun i v hv => h2 i v (h1 i v hv)

/-- Nonvacuity: under a nonempty marking every expression has a reading,
so forced verdicts speak about actual readings — a forced `T` is never
the emptiness of the quantifier. (Nonemptiness is the hypothesis itself:
"each interval contains a value"; for concrete markings it is a
`decide`.) -/
theorem reads_exists {m : Marking} (wf : ∀ i, ∃ v, (m i).mem v) :
    ∀ e : Expr, ∃ v, Reads m e v := by
  intro e
  induction e with
  | const c => exact ⟨c, .const⟩
  | qty i => obtain ⟨v, hv⟩ := wf i; exact ⟨v, .qty hv⟩
  | add a b ia ib =>
      obtain ⟨x, rx⟩ := ia
      obtain ⟨y, ry⟩ := ib
      exact ⟨x + y, .add rx ry⟩
  | sub a b ia ib =>
      obtain ⟨x, rx⟩ := ia
      obtain ⟨y, ry⟩ := ib
      exact ⟨x - y, .sub rx ry⟩
  | mul a b ia ib =>
      obtain ⟨x, rx⟩ := ia
      obtain ⟨y, ry⟩ := ib
      exact ⟨x * y, .mul rx ry⟩

/-- The decorrelation witness (fork F1), kernel-checked: over m = [0, 9]
the expression m − m reads 9 (choose 9 then 0) — the readings of the two
occurrences are independent, so the difference is NOT forced to 0, exactly
as measured (`znum.py`: m − m ∈ [−9, 9]). -/
theorem decorrelation_witness :
    Reads (fun _ => ⟨0, 9⟩) (.sub (.qty 0) (.qty 0)) 9 := by
  have h : (9 : Int) - 0 = 9 := by decide
  exact h ▸ Reads.sub
    (.qty (show Iv.mem ⟨0, 9⟩ 9 from ⟨by decide, by decide⟩))
    (.qty (show Iv.mem ⟨0, 9⟩ 0 from ⟨by decide, by decide⟩))

/-! The asymmetry this module fixes, stated once in prose: narrowing can
SETTLE an atom (a mark becomes a forced verdict — verification earns) but
can never UNSETTLE one (the six heredity theorems). In the propositional
core the same warranty costs an enumeration of depth m−1 (§19); on the
numeric floor it is the shape of forcing. The remaining gap between this
model and `znum.py` is division (undefined subterms → the mark), measured
there and excluded here by the expression grammar. -/

#print axioms reads_mono
#print axioms forcedLE_hereditary
#print axioms forcedNotLE_hereditary
#print axioms forcedLT_hereditary
#print axioms forcedNotLT_hereditary
#print axioms forcedEQ_hereditary
#print axioms forcedNE_hereditary
#print axioms endpoint_narrows
#print axioms narrows_trans
#print axioms reads_exists
#print axioms decorrelation_witness
