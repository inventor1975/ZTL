import ZTL
import ZRead

/-!
# ZTopology — hereditary verdicts as the topology of partial information

The curator's line of 2026-09-29, from the swarm work: ZTL describes more than two
values, so it should say something *exact from partial data*. Measured first
(against ztljudge: 5 400 of 5 400 markings; the sandwich on 520 formulas, 0 violations);
proved here.

Setting. A valuation `v : Nat → V` is a state of partial information; `refines v w`
says `w` knows at least what `v` knows (the order `leqb`: Z below T and F). Upward
closed sets are the open sets of the Alexandrov (= Scott, on this order) topology.

* `earned φ v`  — φ is T at v and at every refinement of v: the HEREDITARY T (verdict T, grade
  hereditary);
* `refuted φ v` — the same for F: the hereditary F.

Vocabulary (2026-10-30). The identifiers `earned`/`refuted` predate the judge's vocabulary of
2026-10-29, in which EARNED / REFUTED mean forced T / F — under every reading of every occurrence (stronger: item 3 below), EARNED IF
STABLE means T in every cleaning, and ON CREDIT a T as written that is not earned. Below, the
identifiers are kept (they are cited elsewhere); the prose says "hereditary T / F".

Proved, all on the empty axiom list:
1. `earned_open`, `refuted_open` — hereditary T and hereditary F are open: more data never
   overturns them. This is "exact from partial data".
2. `earned_sub_super` — hereditary T ⊆ supervaluation-T (true on every total refinement).
3. `forced_sub_earned`, `forced_sub_refuted` — forced T / F (the judge's EARNED / REFUTED: T / F under
   every reading of every occurrence, `ZRead.rd`) ⊆ hereditary T / F.
4. Both inclusions are STRICT: `not_a_and_not_a` is hereditary T where it is not forced (the judge:
   EARNED IF STABLE); `excluded_middle` is supervaluation-T and not hereditary T (F as written; the
   judge: EARNED IF STABLE).

So hereditary ZTL decides more than the forced reading and less than supervaluation, and what it decides
is stable under new data. What it does NOT give (measured): its present value
on the boundary is not a prediction of the outcome.
-/

namespace ZTopology

open V

/-! ## Partial information -/

/-- `w` knows at least what `v` knows. -/
def refines (v w : Nat → V) : Prop := ∀ n, leqb (v n) (w n) = true

theorem leqb_refl : ∀ a : V, leqb a a = true := by decide

theorem leqb_trans : ∀ a b c : V, leqb a b = true → leqb b c = true → leqb a c = true := by
  decide

theorem refines_refl (v : Nat → V) : refines v v := fun n => leqb_refl (v n)

theorem refines_trans {u v w : Nat → V} (h1 : refines u v) (h2 : refines v w) :
    refines u w := fun n => leqb_trans (u n) (v n) (w n) (h1 n) (h2 n)

/-- A total valuation: nothing left dirty. -/
def total (w : Nat → V) : Prop := ∀ n, w n ≠ Z

/-! ## The hereditary verdicts -/

/-- Hereditary T: T now and after any further data. (Not the judge's EARNED, which is the forced T;
see the header.) -/
def earned (φ : Fm) (v : Nat → V) : Prop := ∀ w, refines v w → evalF w φ = T

/-- Hereditary F: F now and after any further data. (Not the judge's REFUTED; see the header.) -/
def refuted (φ : Fm) (v : Nat → V) : Prop := ∀ w, refines v w → evalF w φ = F

/-- Supervaluation: T on every total refinement. -/
def superT (φ : Fm) (v : Nat → V) : Prop := ∀ w, refines v w → total w → evalF w φ = T

theorem earned_now {φ : Fm} {v : Nat → V} (h : earned φ v) : evalF v φ = T :=
  h v (refines_refl v)

theorem refuted_now {φ : Fm} {v : Nat → V} (h : refuted φ v) : evalF v φ = F :=
  h v (refines_refl v)

/-- 1. Hereditary T is open: new data never overturns it. -/
theorem earned_open {φ : Fm} {v w : Nat → V} (h : earned φ v) (hw : refines v w) :
    earned φ w :=
  fun u hu => h u (refines_trans hw hu)

/-- 1'. Hereditary F is open. -/
theorem refuted_open {φ : Fm} {v w : Nat → V} (h : refuted φ v) (hw : refines v w) :
    refuted φ w :=
  fun u hu => h u (refines_trans hw hu)

/-- 2. Hereditary T ⊆ supervaluation-T. -/
theorem earned_sub_super {φ : Fm} {v : Nat → V} (h : earned φ v) : superT φ v :=
  fun w hw _ => h w hw

/-! ## The dirty reading (ZRead), the forced register -/

theorem leqb_refinesR : ∀ a b : V, leqb a b = true → a ≠ Z → b = a := by decide

theorem toR {v w : Nat → V} (h : refines v w) : V.refinesR v w := fun n => leqb_refinesR (v n) (w n) (h n)

/-- 3. Forced T (the judge's EARNED: T under every reading of every occurrence) ⊆ hereditary T. -/
theorem forced_sub_earned {φ : Fm} {v : Nat → V} (h : V.earnedR v φ) : earned φ v :=
  fun w hw => V.earnedR_verdict (V.earnedR_open (toR hw) h)

/-- 3'. Forced F (the judge's REFUTED) ⊆ hereditary F. -/
theorem forced_sub_refuted {φ : Fm} {v : Nat → V} (h : V.refutedR v φ) : refuted φ v :=
  fun w hw => V.refutedR_verdict (V.refutedR_open (toR hw) h)

/-! ## 4. Both inclusions are strict -/

/-- Nothing observed. -/
def blank : Nat → V := fun _ => Z

/-- ¬(a ∧ ¬a). -/
def nonContradiction : Fm := .neg (.conj (.atom 0) (.neg (.atom 0)))

/-- a ∨ ¬a. -/
def excludedMiddle : Fm := .disj (.atom 0) (.neg (.atom 0))

theorem nc_value : ∀ a : V, znot (zand a (znot a)) = T := by decide

/-- ¬(a ∧ ¬a) on no data: hereditary T (the judge: EARNED IF STABLE) ... -/
theorem not_a_and_not_a_earned : earned nonContradiction blank :=
  fun w _ => nc_value (w 0)

/-- ... while it is not forced (a reading of the two occurrences makes it false): forced T ⊊ hereditary T. -/
theorem not_a_and_not_a_not_forced : ¬ V.earnedR blank nonContradiction := by
  unfold V.earnedR; intro h; exact absurd h (by decide)

theorem em_total : ∀ a : V, a ≠ Z → zor a (znot a) = T := by decide

/-- a ∨ ¬a on no data: supervaluation-T ... -/
theorem excluded_middle_super : superT excludedMiddle blank :=
  fun w _ ht => em_total (w 0) (ht 0)

/-- ... and not hereditary T: hereditary T ⊊ supervaluation. Truth is not granted as written
for reasoning about what nobody checked (it is F as written; the judge: EARNED IF STABLE). -/
theorem excluded_middle_not_earned : ¬ earned excludedMiddle blank := by
  intro h
  have h0 : evalF blank excludedMiddle = T := earned_now h
  have h1 : evalF blank excludedMiddle = F := rfl
  exact V.noConfusion (h1.symm.trans h0)

end ZTopology

#print axioms ZTopology.earned_open
#print axioms ZTopology.refuted_open
#print axioms ZTopology.earned_sub_super
#print axioms ZTopology.forced_sub_earned
#print axioms ZTopology.forced_sub_refuted
#print axioms ZTopology.not_a_and_not_a_earned
#print axioms ZTopology.not_a_and_not_a_not_forced
#print axioms ZTopology.excluded_middle_super
#print axioms ZTopology.excluded_middle_not_earned
