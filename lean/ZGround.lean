import TableauCert

/-!
# The general Knaster–Tarski theorem for the lazy jump. Zero axioms.

The two-register architecture (§9) rested on per-instance measurements:
this module proves it once and for all finite systems. A system is a
list of defining formulas (sentence i defined by the i-th formula, over
atoms Tr(0), Tr(1), …). The lazy (strong Kleene) evaluation is monotone
in the information order over the WHOLE language; hence the lazy jump
is monotone, the iteration from ⊥ (all-Z) ascends and stabilizes within
n+1 steps at THE least fixed point; and the grounded part is identical
in every fixed point — quarantine is well-defined. The greedy register's
non-monotonicity (ZTL.lean, Part II) completes the necessity of two
registers. No omega, no by_contra, no List membership — hand-rolled
Nat arithmetic and boolean list predicates throughout.
-/

namespace V

/-! ## The lazy register over the whole language -/

def kimp (a b : V) : V := kor (knot a) b

def kxor : V → V → V
  | T, T => F | T, F => T | T, Z => Z
  | F, T => T | F, F => F | F, Z => Z
  | Z, T => Z | Z, F => Z | Z, Z => Z

def kxnor : V → V → V
  | T, T => T | T, F => F | T, Z => Z
  | F, T => F | F, F => T | F, Z => Z
  | Z, T => Z | Z, F => Z | Z, Z => Z

theorem kimp_monotone : ∀ a b c d, leqb a c = true → leqb b d = true →
    leqb (kimp a b) (kimp c d) = true := by decide
theorem kxor_monotone : ∀ a b c d, leqb a c = true → leqb b d = true →
    leqb (kxor a b) (kxor c d) = true := by decide
theorem kxnor_monotone : ∀ a b c d, leqb a c = true → leqb b d = true →
    leqb (kxnor a b) (kxnor c d) = true := by decide

/-- Lazy (strong Kleene) evaluation of the full language. -/
def evalK (v : Nat → V) : Fm → V
  | .atom n   => v n
  | .neg φ    => knot (evalK v φ)
  | .conj φ ψ => kand (evalK v φ) (evalK v ψ)
  | .disj φ ψ => kor (evalK v φ) (evalK v ψ)
  | .imp φ ψ  => kimp (evalK v φ) (evalK v ψ)
  | .xor φ ψ  => kxor (evalK v φ) (evalK v ψ)
  | .xnor φ ψ => kxnor (evalK v φ) (evalK v ψ)

/-- Monotonicity of lazy evaluation over the whole language. -/
theorem evalK_mono {v w : Nat → V} (h : ∀ n, leqb (v n) (w n) = true) :
    ∀ φ : Fm, leqb (evalK v φ) (evalK w φ) = true := by
  intro φ
  induction φ with
  | atom n => exact h n
  | neg φ ih => exact kleene_not_monotone _ _ ih
  | conj φ ψ ih1 ih2 => exact kleene_and_monotone _ _ _ _ ih1 ih2
  | disj φ ψ ih1 ih2 => exact kleene_or_monotone _ _ _ _ ih1 ih2
  | imp φ ψ ih1 ih2 => exact kimp_monotone _ _ _ _ ih1 ih2
  | xor φ ψ ih1 ih2 => exact kxor_monotone _ _ _ _ ih1 ih2
  | xnor φ ψ ih1 ih2 => exact kxnor_monotone _ _ _ _ ih1 ih2

/-! ## Finite systems, valuations, the jump -/

abbrev Val := List V
abbrev Sys := List Fm

/-- Read a valuation list (off the end = Z: nothing is granted). -/
def getZ : Val → Nat → V
  | [], _ => Z
  | a :: _, 0 => a
  | _ :: v, n + 1 => getZ v n

/-- The lazy jump: re-evaluate every definition. -/
def jumpL (d : Sys) (v : Val) : Val := d.map (fun φ => evalK (getZ v) φ)

/-- Pointwise information order on valuations. -/
def valLeq : Val → Val → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: v, b :: w => leqb a b && valLeq v w

/-- Boolean equality of valuations (avoiding decidable-instance leaks). -/
def valEq : Val → Val → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: v, b :: w => (a == b) && valEq v w

theorem vbeq : ∀ a b : V, (a == b) = true ↔ a = b := by decide
theorem leqZ : ∀ b : V, leqb Z b = true := by decide
theorem leq_ne_z : ∀ a b : V, leqb a b = true → ¬(a = b) →
    (a = Z ∧ ¬(b = Z)) := by decide
theorem leq_nz : ∀ a b : V, leqb a b = true → ¬(a = Z) → b = a := by decide

theorem valEq_iff : ∀ v w : Val, valEq v w = true ↔ v = w := by
  intro v
  induction v with
  | nil =>
    intro w
    cases w with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons b w => exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
  | cons a v ih =>
    intro w
    cases w with
    | nil => exact ⟨(fun h => nomatch h), fun h => nomatch h⟩
    | cons b w =>
      refine ((andEqTrue _ _).trans (andCongr (vbeq a b) (ih w))).trans ?_
      constructor
      · rintro ⟨rfl, rfl⟩; rfl
      · intro h; cases h; exact ⟨rfl, rfl⟩

theorem getZ_mono : ∀ v w : Val, valLeq v w = true →
    ∀ n, leqb (getZ v n) (getZ w n) = true := by
  intro v
  induction v with
  | nil =>
    intro w h n
    cases w with
    | nil => exact leqZ _
    | cons b w => exact nomatch h
  | cons a v ih =>
    intro w h n
    cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hp := (andEqTrue _ _).mp h
      cases n with
      | zero => exact hp.1
      | succ n => exact ih w hp.2 n

theorem jumpL_mono (d : Sys) {v w : Val} (h : valLeq v w = true) :
    valLeq (jumpL d v) (jumpL d w) = true := by
  induction d with
  | nil => rfl
  | cons φ d ih =>
    exact (andEqTrue _ _).mpr ⟨evalK_mono (getZ_mono v w h) φ, ih⟩

/-! ## The ascending iteration from ⊥ -/

def bot (n : Nat) : Val := List.replicate n Z

def iter (d : Sys) : Nat → Val
  | 0 => bot d.length
  | k + 1 => jumpL d (iter d k)

theorem replicate_leq : ∀ w : Val, valLeq (List.replicate w.length Z) w = true := by
  intro w
  induction w with
  | nil => rfl
  | cons b w ih => exact (andEqTrue _ _).mpr ⟨leqZ b, ih⟩

-- Core's List.length_map/length_replicate carry propext (simp-proved);
-- hand-rolled replacements keep the ledger empty.
theorem jumpL_length (d : Sys) (v : Val) :
    (jumpL d v).length = d.length := by
  induction d with
  | nil => rfl
  | cons φ d ih => exact congrArg Nat.succ ih

theorem bot_leq {w : Val} {n : Nat} (hw : w.length = n) :
    valLeq (bot n) w = true := by
  have h := replicate_leq w
  rw [hw] at h
  exact h

theorem iter_length (d : Sys) : ∀ k, (iter d k).length = d.length := by
  intro k
  cases k with
  | zero =>
    show (List.replicate d.length Z).length = d.length
    induction d.length with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  | succ k => exact jumpL_length d _

/-- The iteration is an ascending chain. -/
theorem chain (d : Sys) : ∀ k, valLeq (iter d k) (iter d (k + 1)) = true := by
  intro k
  induction k with
  | zero => exact bot_leq (iter_length d 1)
  | succ k ih => exact jumpL_mono d ih

/-! ## The information measure and stabilization -/

/-- How many coordinates have earned a classical value. -/
def info : Val → Nat
  | [] => 0
  | a :: v => (if a = Z then 0 else 1) + info v

theorem info_le_length : ∀ v : Val, info v ≤ v.length := by
  intro v
  induction v with
  | nil => exact Nat.le_refl 0
  | cons a v ih =>
    by_cases h : a = Z
    · rw [show info (a :: v) = 0 + info v from by rw [info, if_pos h]]
      rw [Nat.zero_add]
      exact Nat.le_trans ih (Nat.le_succ _)
    · rw [show info (a :: v) = 1 + info v from by rw [info, if_neg h]]
      rw [Nat.add_comm]
      exact Nat.succ_le_succ ih

theorem info_mono : ∀ v w : Val, valLeq v w = true → info v ≤ info w := by
  intro v
  induction v with
  | nil =>
    intro w h
    cases w with
    | nil => exact Nat.le_refl 0
    | cons b w => exact nomatch h
  | cons a v ih =>
    intro w h
    cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hp := (andEqTrue _ _).mp h
      have ihw := ih w hp.2
      by_cases ha : a = Z
      · rw [show info (a :: v) = 0 + info v from by rw [info, if_pos ha],
            Nat.zero_add]
        exact Nat.le_trans ihw (Nat.le_add_left _ _)
      · have hb : b = a := leq_nz a b hp.1 ha
        have hbz : ¬(b = Z) := fun hz => ha (hb ▸ hz : a = Z)
        rw [show info (a :: v) = 1 + info v from by rw [info, if_neg ha],
            show info (b :: w) = 1 + info w from by rw [info, if_neg hbz]]
        exact Nat.add_le_add_left ihw 1

theorem info_strict : ∀ v w : Val, valLeq v w = true → ¬(v = w) →
    info v < info w := by
  intro v
  induction v with
  | nil =>
    intro w h hne
    cases w with
    | nil => exact absurd rfl hne
    | cons b w => exact nomatch h
  | cons a v ih =>
    intro w h hne
    cases w with
    | nil => exact nomatch h
    | cons b w =>
      have hp := (andEqTrue _ _).mp h
      by_cases hab : a = b
      · have hvw : ¬(v = w) := fun ht => hne (hab ▸ ht ▸ rfl)
        have hlt := ih w hp.2 hvw
        subst hab
        by_cases ha : a = Z
        · rw [show info (a :: v) = 0 + info v from by rw [info, if_pos ha],
              show info (a :: w) = 0 + info w from by rw [info, if_pos ha],
              Nat.zero_add, Nat.zero_add]
          exact hlt
        · rw [show info (a :: v) = 1 + info v from by rw [info, if_neg ha],
              show info (a :: w) = 1 + info w from by rw [info, if_neg ha]]
          exact Nat.add_lt_add_left hlt 1
      · have ⟨haz, hbz⟩ := leq_ne_z a b hp.1 hab
        rw [show info (a :: v) = 0 + info v from by rw [info, if_pos haz],
            show info (b :: w) = 1 + info w from by rw [info, if_neg hbz],
            Nat.zero_add, Nat.add_comm]
        exact Nat.lt_succ_of_le (info_mono v w hp.2)

/-- One fixed step stays fixed. -/
theorem persist (d : Sys) {m : Nat} (h : iter d m = iter d (m + 1)) :
    iter d (m + 1) = iter d (m + 2) := congrArg (jumpL d) h

/-- Either the iteration has stabilized at m, or it has earned ≥ m
classical coordinates. -/
theorem fix_or_grow (d : Sys) : ∀ m : Nat,
    iter d m = iter d (m + 1) ∨ m ≤ info (iter d m) := by
  intro m
  induction m with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ m ih =>
    cases hb : valEq (iter d m) (iter d (m + 1)) with
    | true => exact Or.inl (persist d ((valEq_iff _ _).mp hb))
    | false =>
      have hne : ¬(iter d m = iter d (m + 1)) := fun he => by
        rw [(valEq_iff _ _).mpr he] at hb
        exact nomatch hb
      cases ih with
      | inl hfix => exact absurd hfix hne
      | inr hgrow =>
        exact Or.inr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hgrow
          (info_strict _ _ (chain d m) hne)))

/-- THE LEAST FIXED POINT: the iteration stabilizes within n+1 steps. -/
def lfp (d : Sys) : Val := iter d (d.length + 1)

/-- Knaster–Tarski, existence: lfp is a fixed point of the lazy jump. -/
theorem kt_fixed (d : Sys) : jumpL d (lfp d) = lfp d := by
  cases fix_or_grow d (d.length + 1) with
  | inl h => exact h.symm
  | inr h =>
    exact absurd (Nat.le_trans h (Nat.le_trans
      (info_le_length _) (Nat.le_of_eq (iter_length d _))))
      (Nat.not_succ_le_self d.length)

/-- Knaster–Tarski, minimality: lfp lies below every fixed point. -/
theorem kt_least (d : Sys) (w : Val) (hw : w.length = d.length)
    (hfix : jumpL d w = w) : valLeq (lfp d) w = true := by
  have key : ∀ k, valLeq (iter d k) w = true := by
    intro k
    induction k with
    | zero => exact bot_leq hw
    | succ k ih =>
      have h := jumpL_mono d ih
      rw [hfix] at h
      exact h
  exact key (d.length + 1)

/-- Quarantine is well-defined: a coordinate grounded in the least
fixed point carries the SAME classical value in every fixed point. -/
theorem grounded_absolute (d : Sys) (w : Val) (hw : w.length = d.length)
    (hfix : jumpL d w = w) (n : Nat) (hg : ¬(getZ (lfp d) n = Z)) :
    getZ w n = getZ (lfp d) n :=
  leq_nz _ _ (getZ_mono _ _ (kt_least d w hw hfix) n) hg

#print axioms evalK_mono
#print axioms jumpL_mono
#print axioms kt_fixed
#print axioms kt_least
#print axioms grounded_absolute

end V
