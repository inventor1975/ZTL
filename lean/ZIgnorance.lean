/-
  ZIgnorance.lean — E42: IGNORANCE DOES NOT BECOME A NUMBER.

  §16's two remaining claims, measured there and proved here.

  1. REPARAMETRIZATION (a discrete Bertrand). Told only that a quantity lies
     somewhere in its whole range, a Bayesian with a uniform prior answers the
     question "is it in the lower quarter?" with one number; a Bayesian with a
     uniform prior on the SQUARE of the same quantity — the same ignorance,
     relabelled — answers with another. Both are computed here and shown
     different, by cross-multiplication, with no division and no rationals.

     Our verdict is Z in both, and not by luck: the verdict depends on the
     RANGE and the threshold alone, so ANY strictly monotone relabelling
     leaves it where it was. That is the invariance §16 claims, proved for
     every relabelling rather than for the two the example uses.

  2. ELLSBERG. A verified fifty-fifty urn against an urn of unknown
     composition. "The unknown urn is no worse" gets F — and the point is
     WHY: not because the unknown urn is judged worse, but because the claim
     is not forced, and a denial of the unforced is classical (¬Z = F, §3.1).
     Default deny. The same question about the verified urn gets T. The
     famous "irrationality" of Ellsberg's subjects is the distinction between
     a verified probability and a mark, which a point prior cannot see.

  WHAT THIS DOES NOT SAY. Nothing here shows a Bayesian is wrong. It shows
  that the number depends on the parametrization while the ignorance does
  not, and that a logic which refuses to produce a number is not thereby
  saying less — it is declining to import what it was not given.
-/
import ZAbsInt

namespace ZIgnorance

open V
open ZAbsInt

/-! ### 1. Two priors, two numbers, one ignorance -/

/-- How many of `0 … n` are at most `c`. The counting a uniform prior does. -/
def countLe (n c : Nat) : Nat := mn c n + 1
where
  mn (a b : Nat) : Nat := match Nat.ble a b with | true => a | false => b

/-- The quantity runs over 0…4 (quarters of the range); the question is
"is it in the lower quarter", i.e. at most 1. -/
theorem prior_on_w : countLe 4 1 = 2 ∧ 4 + 1 = 5 := ⟨rfl, rfl⟩

/-- Relabel by squaring: the same quantity now runs over 0…16, and the same
question is "at most 1" again — but the prior spreads over seventeen points
instead of five. -/
theorem prior_on_w_squared : countLe 16 1 = 2 ∧ 16 + 1 = 17 := ⟨rfl, rfl⟩

/-- **ONE IGNORANCE, TWO NUMBERS.** 2/5 against 2/17, compared by
cross-multiplication so that no division is imported into a file about not
importing things. -/
theorem bertrand_two_numbers : countLe 4 1 * 17 ≠ countLe 16 1 * 5 := by decide

/-! ### …and our verdict does not move -/

/-- The atom is Z exactly in the gap: the threshold strictly above the floor
and not above the ceiling. -/
theorem absLt_Z_of_strictly_inside (lo hi c : Nat) (h1 : lo < c) (h2 : c ≤ hi) :
    absLt lo hi c = Z := by
  unfold absLt
  rw [ble_false_of_lt (hi + 1) c (Nat.lt_succ_of_le h2),
      ble_false_of_lt c lo h1]

/-- **THE VERDICT IS REPARAMETRIZATION-INVARIANT.** Any strictly monotone
relabelling of the quantity carries the gap to a gap, so the verdict stays Z.
The Bayesian number moves; this does not. -/
theorem verdict_reparam_invariant (f : Nat → Nat)
    (mono : ∀ a b, a < b → f a < f b) (lo hi c : Nat)
    (h1 : lo < c) (h2 : c ≤ hi) :
    absLt lo hi c = Z ∧ absLt (f lo) (f hi) (f c) = Z := by
  refine ⟨absLt_Z_of_strictly_inside lo hi c h1 h2, ?_⟩
  refine absLt_Z_of_strictly_inside (f lo) (f hi) (f c) (mono lo c h1) ?_
  cases Nat.lt_or_ge c hi with
  | inl hlt => exact Nat.le_of_lt (mono c hi hlt)
  | inr hge => rw [Nat.le_antisymm h2 hge]; exact Nat.le_refl _

/-! ### 2. Ellsberg -/

/-- The verified urn: fifty out of a hundred, earned. -/
def known : Nat × Nat := (50, 50)

/-- The unknown urn: anything at all. -/
def unknown : Nat × Nat := (0, 100)

/-- "This urn is no worse than fifty-fifty", read as the denial of "it is
below fifty". -/
def noWorse (u : Nat × Nat) : V := znot (absLt u.1 u.2 50)

/-- **THE VERIFIED URN EARNS THE CLAIM.** -/
theorem known_no_worse : noWorse known = T := rfl

/-- **THE UNKNOWN URN DOES NOT — AND THAT IS A DEFAULT DENY, NOT A JUDGEMENT.**
The atom itself is Z: the claim is neither forced nor excluded. The denial of
an unforced claim is classical, so the answer is F, and the chooser takes the
verified urn. Ellsberg's subjects were reading a mark, not miscomputing a
probability. -/
theorem unknown_not_earned :
    absLt unknown.1 unknown.2 50 = Z ∧ noWorse unknown = F := ⟨rfl, rfl⟩

/-- The pair, side by side: same question, same threshold, different tier of
evidence — and the logic separates them without preferring either urn on its
merits. -/
theorem ellsberg : noWorse known = T ∧ noWorse unknown = F := ⟨rfl, rfl⟩

end ZIgnorance

#print axioms ZIgnorance.bertrand_two_numbers
#print axioms ZIgnorance.absLt_Z_of_strictly_inside
#print axioms ZIgnorance.verdict_reparam_invariant
#print axioms ZIgnorance.known_no_worse
#print axioms ZIgnorance.unknown_not_earned
#print axioms ZIgnorance.ellsberg
