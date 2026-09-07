import ZNum

/-!
# The price list on the numeric floor: what survives at the interval level and
# what falls at the verdict. Zero axioms. (E62)

§15 measured (`zarith.py`, "Laws: price-list inheritance") that commutativity
of addition and the unit survive at the level of intervals — x+y and y+x, x+0
and x have the same bounds — while the equations, read as atoms on a mark, are
not earned: the verdict is Z. Here both halves are theorems over `ZNum`'s
reading semantics, where an expression means its SET OF READINGS and every
occurrence chooses independently.

    add_comm_readings  :  Reads m (a + b) v ↔ Reads m (b + a) v
    add_zero_readings  :  Reads m (a + 0) v ↔ Reads m a v
    comm_not_earned    :  two readings of one mark →
                          ¬ForcedEQ (x+y) (y+x) ∧ ¬ForcedNE (x+y) (y+x)
    unit_not_earned    :  two readings of one mark →
                          ¬ForcedEQ (x+0) x ∧ ¬ForcedNE (x+0) x

The reading sets coincide, so the interval arithmetic inherits both laws; the
atoms are neither forced true nor forced false, so the verdict keeps the mark.
That is regularity R1 (§26) on the numeric floor: coincidence of bounds is not
identity, and identity is earned by nothing short of full verification. The
mechanism is the decorrelation `decorrelation_witness` already exhibits for
m − m: the two occurrences of x in `x + 0 = x` read independently.

Forcedness on products (0·w) is not here because it was already a theorem:
`ZNaN.zero_times_mark` / `emb_mul_not_hom` (§27). The sentence of §15 that
still called both "measured only" was written before either landed.

`zarith_instance` is the stand's own cell — x ∈ [1,3], y ∈ [2,4] — as a theorem.
-/

namespace ZNumPrice

/-- Commutativity of `Int` addition, from the definition of `Int.add` — core's
`Int.add_comm` carries `propext` in this toolchain (measured), as do its
cancellation lemmas; `Nat.add_comm` and `Int.ofNat_inj` are clean. -/
theorem int_add_comm : ∀ a b : Int, a + b = b + a := by
  intro a b
  cases a with
  | ofNat m =>
      cases b with
      | ofNat n => exact congrArg Int.ofNat (Nat.add_comm m n)
      | negSucc n => rfl
  | negSucc m =>
      cases b with
      | ofNat n => rfl
      | negSucc n => exact congrArg Int.negSucc (congrArg Nat.succ (Nat.add_comm m n))

/-- Right cancellation on `Nat`, by induction — core's is not clean here. -/
theorem nat_add_right_cancel : ∀ (c : Nat) {a b : Nat}, a + c = b + c → a = b := by
  intro c
  induction c with
  | zero => intro a b h; exact h
  | succ k ih => intro a b h; exact ih (Nat.succ.inj h)

/-- Commutativity survives at the interval level: the reading sets coincide. -/
theorem add_comm_readings (m : Marking) (a b : Expr) (v : Int) :
    Reads m (.add a b) v ↔ Reads m (.add b a) v := by
  constructor
  · intro h
    cases h with
    | add ra rb =>
        have h' := Reads.add rb ra
        rw [int_add_comm] at h'
        exact h'
  · intro h
    cases h with
    | add rb ra =>
        have h' := Reads.add ra rb
        rw [int_add_comm] at h'
        exact h'

/-- The unit survives at the interval level: the reading sets coincide. -/
theorem add_zero_readings (m : Marking) (a : Expr) (v : Int) :
    Reads m (.add a (.const 0)) v ↔ Reads m a v := by
  constructor
  · intro h
    cases h with
    | add ra rc =>
        cases rc
        rw [Int.add_zero]
        exact ra
  · intro h
    have h' : Reads m (.add a (.const 0)) (v + 0) := Reads.add h Reads.const
    rw [Int.add_zero] at h'
    exact h'

/-- The equation `x + y = y + x` is not earned on a mark: with two readings of
`x` and any reading of `y`, it is neither forced true nor forced false. Readings
are taken in `ℕ ⊂ ℤ`, where cancellation is clean; the stand's cell lives there. -/
theorem comm_not_earned (m : Marking) (i j : Nat) (u w z : Nat)
    (hu : (m i).mem (Int.ofNat u)) (hw : (m i).mem (Int.ofNat w)) (huw : u ≠ w)
    (hz : (m j).mem (Int.ofNat z)) :
    ¬ ForcedEQ m (.add (.qty i) (.qty j)) (.add (.qty j) (.qty i))
    ∧ ¬ ForcedNE m (.add (.qty i) (.qty j)) (.add (.qty j) (.qty i)) := by
  constructor
  · intro h
    have e := h (Int.ofNat u + Int.ofNat z) (Int.ofNat z + Int.ofNat w)
      (Reads.add (.qty hu) (.qty hz)) (Reads.add (.qty hz) (.qty hw))
    have e' : Int.ofNat (u + z) = Int.ofNat (z + w) := e
    have e'' : u + z = z + w := Int.ofNat_inj.1 e'
    rw [Nat.add_comm z w] at e''
    exact huw (nat_add_right_cancel z e'')
  · intro h
    have e := h (Int.ofNat u + Int.ofNat z) (Int.ofNat z + Int.ofNat u)
      (Reads.add (.qty hu) (.qty hz)) (Reads.add (.qty hz) (.qty hu))
    apply e
    exact int_add_comm _ _

/-- The equation `x + 0 = x` is not earned on a mark either: the two occurrences
of `x` read independently. -/
theorem unit_not_earned (m : Marking) (i : Nat) (u w : Int)
    (hu : (m i).mem u) (hw : (m i).mem w) (huw : u ≠ w) :
    ¬ ForcedEQ m (.add (.qty i) (.const 0)) (.qty i)
    ∧ ¬ ForcedNE m (.add (.qty i) (.const 0)) (.qty i) := by
  constructor
  · intro h
    have e := h (u + 0) w (Reads.add (.qty hu) Reads.const) (.qty hw)
    apply huw
    rw [Int.add_zero] at e
    exact e
  · intro h
    have e := h (u + 0) u (Reads.add (.qty hu) Reads.const) (.qty hu)
    apply e
    exact Int.add_zero u

/-- The stand's cell: x ∈ [1,3] (quantity 0), y ∈ [2,4] (quantity 1). -/
def zarithMarking : Marking := fun n => match n with
  | 0 => ⟨1, 3⟩
  | _ + 1 => ⟨2, 4⟩

theorem zarith_instance :
    (¬ ForcedEQ zarithMarking (.add (.qty 0) (.qty 1)) (.add (.qty 1) (.qty 0))
      ∧ ¬ ForcedNE zarithMarking (.add (.qty 0) (.qty 1)) (.add (.qty 1) (.qty 0)))
    ∧ (¬ ForcedEQ zarithMarking (.add (.qty 0) (.const 0)) (.qty 0)
      ∧ ¬ ForcedNE zarithMarking (.add (.qty 0) (.const 0)) (.qty 0)) :=
  ⟨comm_not_earned zarithMarking 0 1 1 3 2
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide) ⟨by decide, by decide⟩,
   unit_not_earned zarithMarking 0 1 3
      ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by decide)⟩

#print axioms int_add_comm
#print axioms nat_add_right_cancel
#print axioms add_comm_readings
#print axioms add_zero_readings
#print axioms comm_not_earned
#print axioms unit_not_earned
#print axioms zarith_instance

end ZNumPrice
