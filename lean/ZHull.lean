import ZSuperpose

/-!
# ZHull — `znumsolve._hull`, the narrowing rule of the numeric solver: sound, and exact on the bound it moves. Zero axioms.

Written 2026-11-27, the curator's audit «каждая деталь судьи — теорема». `znumsolve` narrows a quantity x by a linear
constraint `k·x + (c0 + Σ c_j·p_j) ⋈ 0`, the other quantities p_j in their boxes: it computes the REST's range
`[rlo, rhi]` by the signs of the coefficients and keeps
    `le`:  k·x ≤ −rlo          `ge`:  k·x ≥ −rhi          `eq`:  −rhi ≤ k·x ≤ −rlo
(then divides by k in exact rationals — a run step, as in `ZSuperpose`). Until today: "sound by construction", measured
on a grid in `znumsolve.py` §3.

PROVED HERE, over any ordered ring with the laws of `ZLP.OMul` (ℤ instantiated; ℚ has the same laws):
  `hull_le_sound`   a value x that satisfies `k·x + rest ≤ 0` for SOME choice of the others in their boxes keeps
                    `k·x ≤ −rlo` — nothing that can satisfy the constraint is dropped;
  `hull_le_exact`   and every x with `k·x ≤ −rlo` DOES satisfy it, at the corner the signs pick — nothing that
                    cannot be satisfied is kept: the narrowed bound is the exact one, not an enclosure;
  `hull_ge_sound`, `hull_ge_exact`   the same for `≥ 0` with `rhi`;
  `hull_eq_sound`   `= 0` keeps `−rhi ≤ k·x ≤ −rlo`.
NOT PROVED: exactness of the `eq` interval inside (it needs every intermediate value of the rest, a convexity argument);
strict `<` (the laws have no strict order); the division by k.
-/

namespace ZHull
open ZLP ZSuperpose

variable {α : Type}

theorem zero_add (R : OMul α) (a : α) : R.add R.zero a = a := by rw [R.add_comm]; exact R.add_zero a

/-- a + b ≤ 0 ⇒ a ≤ −b. -/
theorem le_neg_of_add_le (R : OMul α) {a b : α} (h : R.le (R.add a b) R.zero) : R.le a (R.neg b) := by
  have h2 := R.add_le_add_right (R.neg b) h
  rw [R.add_assoc, R.add_neg, R.add_zero, zero_add] at h2
  exact h2

/-- a ≤ −b ⇒ a + b ≤ 0. -/
theorem add_le_of_le_neg (R : OMul α) {a b : α} (h : R.le a (R.neg b)) : R.le (R.add a b) R.zero := by
  have h2 := R.add_le_add_right b h
  rw [R.add_comm (R.neg b) b, R.add_neg] at h2
  exact h2

/-- 0 ≤ a + b ⇒ −b ≤ a. -/
theorem neg_le_of_le_add (R : OMul α) {a b : α} (h : R.le R.zero (R.add a b)) : R.le (R.neg b) a := by
  have h2 := R.add_le_add_right (R.neg b) h
  rw [R.add_assoc, R.add_neg, R.add_zero, zero_add] at h2
  exact h2

/-- −b ≤ a ⇒ 0 ≤ a + b. -/
theorem le_add_of_neg_le (R : OMul α) {a b : α} (h : R.le (R.neg b) a) : R.le R.zero (R.add a b) := by
  have h2 := R.add_le_add_right b h
  rw [R.add_comm (R.neg b) b, R.add_neg] at h2
  exact h2

/-- The rest at a choice, and its two ends. -/
def rest (R : OMul α) (c0 : α) (l : List (STerm α)) : α := R.add c0 (sumWith R (fun t => t.p) l)
def rlo (R : OMul α) (c0 : α) (l : List (STerm α)) : α := R.add c0 (sumWith R lowEnd l)
def rhi (R : OMul α) (c0 : α) (l : List (STerm α)) : α := R.add c0 (sumWith R highEnd l)

/-- `≤ 0`: SOUND. -/
theorem hull_le_sound (R : OMul α) (k x c0 : α) (l : List (STerm α)) (hl : ∀ t, List.Mem t l → STermOK R t)
    (h : R.le (R.add (R.mul k x) (rest R c0 l)) R.zero) : R.le (R.mul k x) (R.neg (rlo R c0 l)) := by
  apply le_neg_of_add_le R
  exact R.le_trans (R.add_le_add_left (R.mul k x) (affine_low_le R c0 l hl)) h

/-- `≤ 0`: EXACT — the corner the signs pick satisfies the constraint. -/
theorem hull_le_exact (R : OMul α) (k x c0 : α) (l : List (STerm α))
    (h : R.le (R.mul k x) (R.neg (rlo R c0 l))) : R.le (R.add (R.mul k x) (rest R c0 (l.map atLow))) R.zero := by
  have e : rest R c0 (l.map atLow) = rlo R c0 l := (affine_attained R c0 l).1
  rw [e]; exact add_le_of_le_neg R h

/-- `≥ 0`: SOUND. -/
theorem hull_ge_sound (R : OMul α) (k x c0 : α) (l : List (STerm α)) (hl : ∀ t, List.Mem t l → STermOK R t)
    (h : R.le R.zero (R.add (R.mul k x) (rest R c0 l))) : R.le (R.neg (rhi R c0 l)) (R.mul k x) := by
  apply neg_le_of_le_add R
  exact R.le_trans h (R.add_le_add_left (R.mul k x) (affine_high_ge R c0 l hl))

/-- `≥ 0`: EXACT. -/
theorem hull_ge_exact (R : OMul α) (k x c0 : α) (l : List (STerm α))
    (h : R.le (R.neg (rhi R c0 l)) (R.mul k x)) : R.le R.zero (R.add (R.mul k x) (rest R c0 (l.map atHigh))) := by
  have e : rest R c0 (l.map atHigh) = rhi R c0 l := (affine_attained R c0 l).2
  rw [e]; exact le_add_of_neg_le R h

/-- `= 0`: SOUND, both sides. -/
theorem hull_eq_sound (R : OMul α) (k x c0 : α) (l : List (STerm α)) (hl : ∀ t, List.Mem t l → STermOK R t)
    (h : R.add (R.mul k x) (rest R c0 l) = R.zero) :
    R.le (R.neg (rhi R c0 l)) (R.mul k x) ∧ R.le (R.mul k x) (R.neg (rlo R c0 l)) :=
  ⟨hull_ge_sound R k x c0 l hl (h ▸ R.le_refl _), hull_le_sound R k x c0 l hl (h ▸ R.le_refl _)⟩

theorem mem_map_inv' {β γ} (f : β → γ) {y : γ} : ∀ {l : List β}, List.Mem y (l.map f) → ∃ x, List.Mem x l ∧ f x = y
  | x :: l, h => by
      cases h with
      | head => exact ⟨x, List.Mem.head _, rfl⟩
      | tail _ h' =>
          obtain ⟨z, hz, e⟩ := mem_map_inv' f h'
          exact ⟨z, List.Mem.tail _ hz, e⟩

/-- The picked corner lies in the box (so the witness of exactness is admissible). -/
theorem corner_in_box (R : OMul α) (l : List (STerm α)) (hb : ∀ t, List.Mem t l → R.le t.lo t.hi) :
    ∀ t, List.Mem t (l.map atLow) → R.le t.lo t.p ∧ R.le t.p t.hi := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := mem_map_inv' atLow ht
  exact (ends_in_box R u (hb u hu)).1

end ZHull

/-- On ℤ: `2·x + (3 + 1·p)` with p ∈ [-1, 4] — the rest is in [2, 7]; `≤ 0` keeps 2·x ≤ −2. -/
example : ZHull.rlo ZLP.intOMul 3 [⟨1, -1, 4, 0, true⟩] = 2 := by decide

#print axioms ZHull.zero_add
#print axioms ZHull.le_neg_of_add_le
#print axioms ZHull.add_le_of_le_neg
#print axioms ZHull.neg_le_of_le_add
#print axioms ZHull.le_add_of_neg_le
#print axioms ZHull.hull_le_sound
#print axioms ZHull.hull_le_exact
#print axioms ZHull.hull_ge_sound
#print axioms ZHull.hull_ge_exact
#print axioms ZHull.hull_eq_sound
#print axioms ZHull.mem_map_inv'
#print axioms ZHull.corner_in_box
