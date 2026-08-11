import ZNum

/-!
# ZNumCoherent — the same bet under the COHERENT reading. Zero axioms.

`ZNum.lean` proves narrowing-heredity for the DECORRELATED reading: every
occurrence of a quantity chooses its value independently. Since
2026-08-11 that is no longer the numeric floor's default — it is the
`sample` mode, kept for the case it was always right about (the same rod
measured twice). The default now says a repeated name denotes ONE THING
in the world, so all its occurrences co-refer; `m - m` is 0 and `x + x`
is `2x`, which is what makes an unknown solvable at all.

A change of semantics invalidates the old proof for the new default, and
this project does not carry a claim it has stopped proving. So the bet is
proved again, from scratch, for the coherent reading — and three further
facts are recorded, because they are what the change actually bought and
cost:

  * `coherent_refines` — every coherent reading is a decorrelated one.
    The new semantics only ever REMOVES readings.
  * `forced_sample_implies_coherent` — therefore anything forced in the
    `sample` mode stays forced in the default one. Nothing that was
    earned under the old semantics is lost under the new.
  * `coherent_strictly_finer` — and the converse fails, exhibited on
    `x - x`: coherently it reads 0 and nothing else, decorrelated it also
    reads 3. That single witness is the whole reason for the change.

Division is excluded here as it is there: an interval divisor containing
zero makes the subterm undefined and the atom takes the mark, which is
measured in `znum.py` rather than proved.

VR discipline: `#print axioms` at the end — empty list, no exceptions.
-/


namespace Coherent

/-- An assignment gives one value per NAME — not per occurrence. That
single sentence is the whole difference from `ZNum.Reads`. -/
def Assign := Nat → Int

/-- The assignment lies inside the current marking. -/
def InBox (m : Marking) (a : Assign) : Prop := ∀ i, (m i).mem (a i)

/-- Coherent evaluation is a FUNCTION: with the names fixed, an
expression has one value, so there is nothing left to choose. -/
def eval (a : Assign) : Expr → Int
  | .const c => c
  | .qty i   => a i
  | .add x y => eval a x + eval a y
  | .sub x y => eval a x - eval a y
  | .mul x y => eval a x * eval a y

/-- `v` is a coherent reading: some admissible assignment produces it. -/
def CReads (m : Marking) (e : Expr) (v : Int) : Prop :=
  ∃ a : Assign, InBox m a ∧ eval a e = v

/-- Monotonicity, and note how cheap it became: no induction over the
expression at all. A narrowed box admits fewer assignments, and the value
is a function of the assignment, so the reading set shrinks with it. The
decorrelated proof needed structural induction precisely because its
choices were spread over the derivation. -/
theorem creads_mono {m' m : Marking} (h : Narrows m' m) {e : Expr}
    {v : Int} : CReads m' e v → CReads m e v := by
  intro ⟨a, hin, hv⟩
  exact ⟨a, fun i => h i (a i) (hin i), hv⟩

/-! ## The six forced shapes, coherently -/

def ForcedLE (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, CReads m a x → CReads m b y → x ≤ y

def ForcedNotLE (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, CReads m a x → CReads m b y → y < x

def ForcedLT (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, CReads m a x → CReads m b y → x < y

def ForcedNotLT (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, CReads m a x → CReads m b y → y ≤ x

def ForcedEQ (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, CReads m a x → CReads m b y → x = y

def ForcedNE (m : Marking) (a b : Expr) : Prop :=
  ∀ x y, CReads m a x → CReads m b y → x ≠ y

/-! ## THE BET AGAIN, kernel-checked under the new default -/

theorem forcedLE_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedLE m a b → ForcedLE m' a b :=
  fun f _ _ ra rb => f _ _ (creads_mono h ra) (creads_mono h rb)

theorem forcedNotLE_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedNotLE m a b → ForcedNotLE m' a b :=
  fun f _ _ ra rb => f _ _ (creads_mono h ra) (creads_mono h rb)

theorem forcedLT_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedLT m a b → ForcedLT m' a b :=
  fun f _ _ ra rb => f _ _ (creads_mono h ra) (creads_mono h rb)

theorem forcedNotLT_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedNotLT m a b → ForcedNotLT m' a b :=
  fun f _ _ ra rb => f _ _ (creads_mono h ra) (creads_mono h rb)

theorem forcedEQ_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedEQ m a b → ForcedEQ m' a b :=
  fun f _ _ ra rb => f _ _ (creads_mono h ra) (creads_mono h rb)

theorem forcedNE_hereditary {m' m a b} (h : Narrows m' m) :
    ForcedNE m a b → ForcedNE m' a b :=
  fun f _ _ ra rb => f _ _ (creads_mono h ra) (creads_mono h rb)

/-! ## How the two readings stand to each other -/

/-- Every coherent reading is also a decorrelated one: the coherent
semantics only removes readings, never invents them. -/
theorem coherent_refines {m : Marking} :
    ∀ (e : Expr) (a : Assign), InBox m a → Reads m e (eval a e) := by
  intro e a hin
  induction e with
  | const c => exact .const
  | qty i   => exact .qty (hin i)
  | add x y ihx ihy => exact .add ihx ihy
  | sub x y ihx ihy => exact .sub ihx ihy
  | mul x y ihx ihy => exact .mul ihx ihy

/-- Hence anything forced under the OLD (sample) semantics is still
forced under the new default. The change cost no earned verdict. -/
theorem forced_sample_implies_coherent {m : Marking} {a b : Expr} :
    _root_.ForcedLE m a b → ForcedLE m a b := by
  intro f x y ⟨p, hp, hx⟩ ⟨q, hq, hy⟩
  exact hx ▸ hy ▸ f _ _ (coherent_refines a p hp) (coherent_refines b q hq)

/-- `a - a = 0` on the empty axiom list. Core's `Int.sub_self` carries
`propext` in this toolchain (measured), and so does `Int.add_right_neg`;
`Int.sub_eq_add_neg` and `Int.subNatNat_self` are clean, so the fact is
rebuilt from those two. The same §8 disinfection pitfall as elsewhere in
the corpus: the lemma is fine, its proof is not ours to inherit. -/
theorem int_sub_self : ∀ a : Int, a - a = 0 := by
  intro a
  rw [Int.sub_eq_add_neg]
  cases a with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ k => exact Int.subNatNat_self (k + 1)
  | negSucc n => exact Int.subNatNat_self (n + 1)

/-- And the converse fails — the witness that made the change worth
making. With x ranging over [0, 3], the coherent reading of `x - x` is 0
and nothing else, while the decorrelated one also reads 3. -/
theorem coherent_strictly_finer :
    (∀ v, CReads (fun _ => ⟨0, 3⟩) (.sub (.qty 0) (.qty 0)) v → v = 0)
    ∧ Reads (fun _ => ⟨0, 3⟩) (.sub (.qty 0) (.qty 0)) 3 := by
  constructor
  · intro v ⟨a, _, hv⟩
    have hz : eval a (.sub (.qty 0) (.qty 0)) = 0 := int_sub_self (a 0)
    exact hv ▸ hz
  · -- `Iv.mem` is a def, so the membership must be SHOWN, not decided —
    -- the same pitfall `decorrelation_witness` hit in ZNum.lean
    have h : (3 : Int) - 0 = 3 := by decide
    exact h ▸ Reads.sub
      (.qty (show Iv.mem ⟨0, 3⟩ 3 from ⟨by decide, by decide⟩))
      (.qty (show Iv.mem ⟨0, 3⟩ 0 from ⟨by decide, by decide⟩))

#print axioms int_sub_self
#print axioms creads_mono
#print axioms forcedLE_hereditary
#print axioms forcedEQ_hereditary
#print axioms coherent_refines
#print axioms forced_sample_implies_coherent
#print axioms coherent_strictly_finer

end Coherent
