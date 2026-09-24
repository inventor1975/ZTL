import ZNumCoherent
import ZNumPrice

/-!
# ZNumNames — a name is ONE NUMBER across the whole claim. Zero axioms.

Decided by the curator on 2026-09-24, in two steps: (1) for numbers
`m - m = 0`, and `m - m ≠ 0` only for a `sample`, where each occurrence is a
separate act of measurement; (2) `==` over numbers is arithmetic, so
`m == m` is true. The ZTL table (Z ↔ Z = F) belongs to the logical
connective, not to numbers: «в логике не бывает m==m, а бывает m nxor m».

`Coherent.Forced*` (ZNumCoherent.lean) read the two sides of a comparison
with SEPARATE assignments: a name co-refers within a side only. The decided
semantics reads the WHOLE claim under ONE assignment. This module defines
that reading and proves what it costs and what it buys:

  * `forced*_joint`        everything forced separately stays forced jointly
                           — the decision revokes no verdict;
  * `jforced*_hereditary`  narrowing never revokes a joint verdict;
  * `self_eq_joint`        `m == m` is jointly forced, and
    `self_eq_not_separate` separately it is not — the witness that made the
                           decision necessary;
  * `comm_forced_numbers`, `unit_forced_numbers`, `sub_self_forced_numbers`
                           for numbers x + y = y + x, x + 0 = x, m - m = 0 are
                           forced. `ZNumPrice.comm_not_earned` and
                           `unit_not_earned` stay true — of SAMPLES.

Clean lemmas only (the kernel's `Int.add_comm`/`Int.sub_self` carry `propext`
in this toolchain, measured 2026-09-07): `ZNumPrice.int_add_comm`,
`Coherent.int_sub_self`, and `Int.add_zero`, which is clean.
VR discipline: `#print axioms` at the end — empty list, no exceptions.
-/

namespace ZNumNames

/-! ## The joint reading: one assignment for the whole claim -/

def JForcedLE (m : Marking) (a b : Expr) : Prop :=
  ∀ s : Coherent.Assign, Coherent.InBox m s → Coherent.eval s a ≤ Coherent.eval s b

def JForcedNotLE (m : Marking) (a b : Expr) : Prop :=
  ∀ s : Coherent.Assign, Coherent.InBox m s → Coherent.eval s b < Coherent.eval s a

def JForcedLT (m : Marking) (a b : Expr) : Prop :=
  ∀ s : Coherent.Assign, Coherent.InBox m s → Coherent.eval s a < Coherent.eval s b

def JForcedNotLT (m : Marking) (a b : Expr) : Prop :=
  ∀ s : Coherent.Assign, Coherent.InBox m s → Coherent.eval s b ≤ Coherent.eval s a

def JForcedEQ (m : Marking) (a b : Expr) : Prop :=
  ∀ s : Coherent.Assign, Coherent.InBox m s → Coherent.eval s a = Coherent.eval s b

def JForcedNE (m : Marking) (a b : Expr) : Prop :=
  ∀ s : Coherent.Assign, Coherent.InBox m s → Coherent.eval s a ≠ Coherent.eval s b

/-! ## The decision revokes nothing: separately forced ⇒ jointly forced -/

theorem forcedLE_joint {m : Marking} {a b : Expr} :
    Coherent.ForcedLE m a b → JForcedLE m a b :=
  fun f s h => f _ _ ⟨s, h, rfl⟩ ⟨s, h, rfl⟩

theorem forcedNotLE_joint {m : Marking} {a b : Expr} :
    Coherent.ForcedNotLE m a b → JForcedNotLE m a b :=
  fun f s h => f _ _ ⟨s, h, rfl⟩ ⟨s, h, rfl⟩

theorem forcedLT_joint {m : Marking} {a b : Expr} :
    Coherent.ForcedLT m a b → JForcedLT m a b :=
  fun f s h => f _ _ ⟨s, h, rfl⟩ ⟨s, h, rfl⟩

theorem forcedNotLT_joint {m : Marking} {a b : Expr} :
    Coherent.ForcedNotLT m a b → JForcedNotLT m a b :=
  fun f s h => f _ _ ⟨s, h, rfl⟩ ⟨s, h, rfl⟩

theorem forcedEQ_joint {m : Marking} {a b : Expr} :
    Coherent.ForcedEQ m a b → JForcedEQ m a b :=
  fun f s h => f _ _ ⟨s, h, rfl⟩ ⟨s, h, rfl⟩

theorem forcedNE_joint {m : Marking} {a b : Expr} :
    Coherent.ForcedNE m a b → JForcedNE m a b :=
  fun f s h => f _ _ ⟨s, h, rfl⟩ ⟨s, h, rfl⟩

/-! ## Narrowing never revokes a joint verdict -/

theorem jforcedLE_hereditary {m' m : Marking} {a b : Expr} (h : Narrows m' m) :
    JForcedLE m a b → JForcedLE m' a b :=
  fun f s hin => f s (fun i => h i (s i) (hin i))

theorem jforcedNotLE_hereditary {m' m : Marking} {a b : Expr} (h : Narrows m' m) :
    JForcedNotLE m a b → JForcedNotLE m' a b :=
  fun f s hin => f s (fun i => h i (s i) (hin i))

theorem jforcedLT_hereditary {m' m : Marking} {a b : Expr} (h : Narrows m' m) :
    JForcedLT m a b → JForcedLT m' a b :=
  fun f s hin => f s (fun i => h i (s i) (hin i))

theorem jforcedNotLT_hereditary {m' m : Marking} {a b : Expr} (h : Narrows m' m) :
    JForcedNotLT m a b → JForcedNotLT m' a b :=
  fun f s hin => f s (fun i => h i (s i) (hin i))

theorem jforcedEQ_hereditary {m' m : Marking} {a b : Expr} (h : Narrows m' m) :
    JForcedEQ m a b → JForcedEQ m' a b :=
  fun f s hin => f s (fun i => h i (s i) (hin i))

theorem jforcedNE_hereditary {m' m : Marking} {a b : Expr} (h : Narrows m' m) :
    JForcedNE m a b → JForcedNE m' a b :=
  fun f s hin => f s (fun i => h i (s i) (hin i))

/-! ## What the decision buys -/

/-- `m == m` — and `e == e` for every expression — is jointly forced. -/
theorem self_eq_joint (m : Marking) (e : Expr) : JForcedEQ m e e :=
  fun _ _ => rfl

/-- …while under the separate reading it is not: with x over [0, 3] the left
side may read 0 and the right side 3. That witness is why the curator had
to decide, and what the judge showed as OPEN until 2026-09-24. -/
theorem self_eq_not_separate :
    ¬ Coherent.ForcedEQ (fun _ => ⟨0, 3⟩) (.qty 0) (.qty 0) := by
  intro f
  have h := f 0 3
    ⟨fun _ => 0, fun _ => (show Iv.mem ⟨0, 3⟩ 0 from ⟨by decide, by decide⟩), rfl⟩
    ⟨fun _ => 3, fun _ => (show Iv.mem ⟨0, 3⟩ 3 from ⟨by decide, by decide⟩), rfl⟩
  exact absurd h (by decide)

/-- For numbers the commutativity of addition is forced (`comm_not_earned`
stays true of samples, where the two sides are two acts). -/
theorem comm_forced_numbers (m : Marking) (i j : Nat) :
    JForcedEQ m (.add (.qty i) (.qty j)) (.add (.qty j) (.qty i)) :=
  fun s _ => ZNumPrice.int_add_comm (s i) (s j)

/-- For numbers the unit is forced (`unit_not_earned` stays true of samples). -/
theorem unit_forced_numbers (m : Marking) (i : Nat) :
    JForcedEQ m (.add (.qty i) (.const 0)) (.qty i) :=
  fun s _ => Int.add_zero (s i)

/-- For numbers `m - m = 0` is forced — decision (1), now in the kernel. -/
theorem sub_self_forced_numbers (m : Marking) (i : Nat) :
    JForcedEQ m (.sub (.qty i) (.qty i)) (.const 0) :=
  fun s _ => Coherent.int_sub_self (s i)

#print axioms forcedLE_joint
#print axioms forcedNotLE_joint
#print axioms forcedLT_joint
#print axioms forcedNotLT_joint
#print axioms forcedEQ_joint
#print axioms forcedNE_joint
#print axioms jforcedLE_hereditary
#print axioms jforcedNotLE_hereditary
#print axioms jforcedLT_hereditary
#print axioms jforcedNotLT_hereditary
#print axioms jforcedEQ_hereditary
#print axioms jforcedNE_hereditary
#print axioms self_eq_joint
#print axioms self_eq_not_separate
#print axioms comm_forced_numbers
#print axioms unit_forced_numbers
#print axioms sub_self_forced_numbers

end ZNumNames
