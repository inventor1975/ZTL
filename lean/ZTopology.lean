import ZTL

/-!
# ZTopology — the judge's dispositions as the topology of partial information

The curator's line of 2026-09-29, from the swarm work: ZTL describes more than two
values, so it should say something *exact from partial data*. Measured first
(against ztljudge: 5 400 of 5 400 markings; the sandwich on 520 formulas, 0 violations);
proved here.

Setting. A valuation `v : Nat → V` is a state of partial information; `refines v w`
says `w` knows at least what `v` knows (the order `leqb`: Z below T and F). Upward
closed sets are the open sets of the Alexandrov (= Scott, on this order) topology.

* `earned φ v`  — φ is T at v and at every refinement of v (the judge's EARNED:
  verdict T, grade hereditary);
* `refuted φ v` — the same for F.

Proved, all on the empty axiom list:
1. `earned_open`, `refuted_open` — EARNED and REFUTED are open: more data never
   overturns them. This is "exact from partial data".
2. `earned_sub_super` — EARNED ⊆ supervaluation-T (true on every total refinement).
3. `kleene_sub_earned`, `kleene_sub_refuted` — strong Kleene ⊆ EARNED / REFUTED.
   The engine is `kleene_agrees`: wherever Kleene decides, the greedy value agrees.
4. Both inclusions are STRICT: `not_a_and_not_a` is EARNED where Kleene is silent;
   `excluded_middle` is supervaluation-T and not EARNED.

So ZTL decides more than Kleene and less than supervaluation, and what it decides
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

/-- A total valuation: nothing left unverified. -/
def total (w : Nat → V) : Prop := ∀ n, w n ≠ Z

/-! ## The judge's stable verdicts -/

/-- EARNED: T now and after any further data. -/
def earned (φ : Fm) (v : Nat → V) : Prop := ∀ w, refines v w → evalF w φ = T

/-- REFUTED: F now and after any further data. -/
def refuted (φ : Fm) (v : Nat → V) : Prop := ∀ w, refines v w → evalF w φ = F

/-- Supervaluation: T on every total refinement. -/
def superT (φ : Fm) (v : Nat → V) : Prop := ∀ w, refines v w → total w → evalF w φ = T

theorem earned_now {φ : Fm} {v : Nat → V} (h : earned φ v) : evalF v φ = T :=
  h v (refines_refl v)

theorem refuted_now {φ : Fm} {v : Nat → V} (h : refuted φ v) : evalF v φ = F :=
  h v (refines_refl v)

/-- 1. EARNED is open: new data never overturns it. -/
theorem earned_open {φ : Fm} {v w : Nat → V} (h : earned φ v) (hw : refines v w) :
    earned φ w :=
  fun u hu => h u (refines_trans hw hu)

/-- 1'. REFUTED is open. -/
theorem refuted_open {φ : Fm} {v w : Nat → V} (h : refuted φ v) (hw : refines v w) :
    refuted φ w :=
  fun u hu => h u (refines_trans hw hu)

/-- 2. EARNED ⊆ supervaluation-T. -/
theorem earned_sub_super {φ : Fm} {v : Nat → V} (h : earned φ v) : superT φ v :=
  fun w hw _ => h w hw

/-! ## Strong Kleene, the monotone register -/

/-- Non-overlapping tables (an overlapping wildcard row pulls propext, measured in ZTL.lean). -/
def kimp (a b : V) : V := kor (knot a) b

def kxor : V → V → V
  | T, T => F | T, F => T | T, Z => Z
  | F, T => T | F, F => F | F, Z => Z
  | Z, T => Z | Z, F => Z | Z, Z => Z

def kxnor : V → V → V
  | T, T => T | T, F => F | T, Z => Z
  | F, T => F | F, F => T | F, Z => Z
  | Z, T => Z | Z, F => Z | Z, Z => Z

def kevalF (v : Nat → V) : Fm → V
  | .atom n   => v n
  | .top      => T
  | .bot      => F
  | .neg φ    => knot (kevalF v φ)
  | .conj φ ψ => kand (kevalF v φ) (kevalF v ψ)
  | .disj φ ψ => kor (kevalF v φ) (kevalF v ψ)
  | .imp φ ψ  => kimp (kevalF v φ) (kevalF v ψ)
  | .xor φ ψ  => kxor (kevalF v φ) (kevalF v ψ)
  | .xnor φ ψ => kxnor (kevalF v φ) (kevalF v ψ)

/-- "Where Kleene decides, the greedy value agrees" — for one input. -/
def agreesAt (k g : V) : Prop := (k = T → g = T) ∧ (k = F → g = F)

instance (k g : V) : Decidable (agreesAt k g) := by unfold agreesAt; exact inferInstance

theorem agree_neg : ∀ k g : V, agreesAt k g → agreesAt (knot k) (znot g) := by decide
theorem agree_conj : ∀ k g k' g' : V, agreesAt k g → agreesAt k' g' →
    agreesAt (kand k k') (zand g g') := by decide
theorem agree_disj : ∀ k g k' g' : V, agreesAt k g → agreesAt k' g' →
    agreesAt (kor k k') (zor g g') := by decide
theorem agree_imp : ∀ k g k' g' : V, agreesAt k g → agreesAt k' g' →
    agreesAt (kimp k k') (zimp g g') := by decide
theorem agree_xor : ∀ k g k' g' : V, agreesAt k g → agreesAt k' g' →
    agreesAt (kxor k k') (zxor g g') := by decide
theorem agree_xnor : ∀ k g k' g' : V, agreesAt k g → agreesAt k' g' →
    agreesAt (kxnor k k') (zxnor g g') := by decide

/-- 3, the engine: wherever strong Kleene decides, the greedy ZTL value agrees. -/
theorem kleene_agrees (v : Nat → V) : ∀ φ : Fm, agreesAt (kevalF v φ) (evalF v φ)
  | .atom _   => ⟨fun h => h, fun h => h⟩
  | .top      => ⟨fun _ => rfl, fun h => V.noConfusion h⟩
  | .bot      => ⟨fun h => V.noConfusion h, fun _ => rfl⟩
  | .neg φ    => agree_neg _ _ (kleene_agrees v φ)
  | .conj φ ψ => agree_conj _ _ _ _ (kleene_agrees v φ) (kleene_agrees v ψ)
  | .disj φ ψ => agree_disj _ _ _ _ (kleene_agrees v φ) (kleene_agrees v ψ)
  | .imp φ ψ  => agree_imp _ _ _ _ (kleene_agrees v φ) (kleene_agrees v ψ)
  | .xor φ ψ  => agree_xor _ _ _ _ (kleene_agrees v φ) (kleene_agrees v ψ)
  | .xnor φ ψ => agree_xnor _ _ _ _ (kleene_agrees v φ) (kleene_agrees v ψ)

theorem kimp_monotone : ∀ a b c d : V, leqb a c = true → leqb b d = true →
    leqb (kimp a b) (kimp c d) = true := by decide
theorem kxor_monotone : ∀ a b c d : V, leqb a c = true → leqb b d = true →
    leqb (kxor a b) (kxor c d) = true := by decide
theorem kxnor_monotone : ∀ a b c d : V, leqb a c = true → leqb b d = true →
    leqb (kxnor a b) (kxnor c d) = true := by decide

/-- Strong Kleene is monotone: more data only decides, never flips. -/
theorem kleene_monotone {v w : Nat → V} (h : refines v w) :
    ∀ φ : Fm, leqb (kevalF v φ) (kevalF w φ) = true
  | .atom n   => h n
  | .top      => rfl
  | .bot      => rfl
  | .neg φ    => kleene_not_monotone _ _ (kleene_monotone h φ)
  | .conj φ ψ => kleene_and_monotone _ _ _ _ (kleene_monotone h φ) (kleene_monotone h ψ)
  | .disj φ ψ => kleene_or_monotone _ _ _ _ (kleene_monotone h φ) (kleene_monotone h ψ)
  | .imp φ ψ  => kimp_monotone _ _ _ _ (kleene_monotone h φ) (kleene_monotone h ψ)
  | .xor φ ψ  => kxor_monotone _ _ _ _ (kleene_monotone h φ) (kleene_monotone h ψ)
  | .xnor φ ψ => kxnor_monotone _ _ _ _ (kleene_monotone h φ) (kleene_monotone h ψ)

theorem leqb_T : ∀ a : V, leqb T a = true → a = T := by decide
theorem leqb_F : ∀ a : V, leqb F a = true → a = F := by decide

/-- 3. Strong Kleene ⊆ EARNED. -/
theorem kleene_sub_earned {φ : Fm} {v : Nat → V} (h : kevalF v φ = T) : earned φ v := by
  intro w hw
  have hk : kevalF w φ = T := leqb_T _ (h ▸ kleene_monotone hw φ)
  exact (kleene_agrees w φ).1 hk

/-- 3'. Strong Kleene ⊆ REFUTED. -/
theorem kleene_sub_refuted {φ : Fm} {v : Nat → V} (h : kevalF v φ = F) : refuted φ v := by
  intro w hw
  have hk : kevalF w φ = F := leqb_F _ (h ▸ kleene_monotone hw φ)
  exact (kleene_agrees w φ).2 hk

/-! ## 4. Both inclusions are strict -/

/-- Nothing observed. -/
def blank : Nat → V := fun _ => Z

/-- ¬(a ∧ ¬a). -/
def nonContradiction : Fm := .neg (.conj (.atom 0) (.neg (.atom 0)))

/-- a ∨ ¬a. -/
def excludedMiddle : Fm := .disj (.atom 0) (.neg (.atom 0))

theorem nc_value : ∀ a : V, znot (zand a (znot a)) = T := by decide

/-- ¬(a ∧ ¬a) on no data: EARNED ... -/
theorem not_a_and_not_a_earned : earned nonContradiction blank :=
  fun w _ => nc_value (w 0)

/-- ... while strong Kleene is silent: Kleene ⊊ EARNED. -/
theorem not_a_and_not_a_kleene_silent : kevalF blank nonContradiction = Z := rfl

theorem em_total : ∀ a : V, a ≠ Z → zor a (znot a) = T := by decide

/-- a ∨ ¬a on no data: supervaluation-T ... -/
theorem excluded_middle_super : superT excludedMiddle blank :=
  fun w _ ht => em_total (w 0) (ht 0)

/-- ... and not EARNED: EARNED ⊊ supervaluation. Truth is not granted on credit
for reasoning about what nobody checked. -/
theorem excluded_middle_not_earned : ¬ earned excludedMiddle blank := by
  intro h
  have h0 : evalF blank excludedMiddle = T := earned_now h
  have h1 : evalF blank excludedMiddle = F := rfl
  exact V.noConfusion (h1.symm.trans h0)

end ZTopology

#print axioms ZTopology.earned_open
#print axioms ZTopology.refuted_open
#print axioms ZTopology.earned_sub_super
#print axioms ZTopology.kleene_agrees
#print axioms ZTopology.kleene_monotone
#print axioms ZTopology.kleene_sub_earned
#print axioms ZTopology.kleene_sub_refuted
#print axioms ZTopology.not_a_and_not_a_earned
#print axioms ZTopology.not_a_and_not_a_kleene_silent
#print axioms ZTopology.excluded_middle_super
#print axioms ZTopology.excluded_middle_not_earned
