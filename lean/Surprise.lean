import ZTime

/-!
# Surprise — the surprise examination on ZTL's own time (ZTime)

The teacher, on Friday: next week there is exactly one exam, and on the morning of that day you will
not know it is today. The class reasons backwards — not the last day (we would know that morning),
so not the day before, and so on — and concludes there can be no exam. Midweek the papers are handed
out and everyone is surprised.

ZTL has a clock already (ZTime, E24): its only tick is `verify`, which resolves a dirty mark `Z` into
an earned value. The week is read on that clock and nothing is added to the kernel:

  * atom `i` = "the exam is on day i" (days `0 … n-1`); on Friday every atom is `Z` — the teacher's,
    not the class's;
  * the morning of day `d` = the marking in which the days before `d` have been verified `F`
    (`morning d`), or, once the exam has happened on day `e`, verified up to `d` (`hist e d`);
  * to KNOW is to hold an earned verdict on the shelf: the value is `T` AND it is hereditary — no
    later verification can change it (`Knows`). A `T` that a later tick can overturn is a value on
    credit, not knowledge. (Compound formulas in ZTL are two-valued, so a `T` alone says little: on
    Monday "no exam this week" already evaluates to `T` — on credit, theorem 5.)

What is proved, for every week length `n`, every day, every formula:

  1. `today_unknown` — on the morning of ANY day `d`, the last one included, the class does not know
     "the exam is today"; and `surprise_guaranteed` — whatever it does know that morning is equally
     true in the world with the exam today and in the world with no exam at all. No known formula,
     however phrased, singles out today. The last day is a surprise too: the class does not even know
     there will be an exam.
  2. `ann_never_known_before_exam` — before the exam has happened, the class never knows the
     announcement ("exactly one exam"), on any morning whatever.
  3. `ann_known_iff_week_over` — after the exam on day `e`, the announcement is known exactly when the
     whole week has been verified: "there is an exam" is earned on the exam day
     (`exam_known_after_it`), "exactly one" only when no later day can bring a second one. The
     receipt the class spends on Monday is dated at the end of the week.
  4. `last_step_conditional` — on the last morning the conditional "if the announcement holds, the
     exam is today" evaluates to `T` (as written; heredity is not stated); what it lacks is the antecedent (theorem 2). The
     backward induction is valid; its first step spends an announcement it has not earned.
  5. `no_exam_on_credit` — on Monday "there will be no exam" evaluates to `T` and is not hereditary:
     the class's conclusion is a value on credit, overturned by the tick of the exam day.
  6. `liar_when_exam_today` / `grounded_when_no_exam` — for perfect knowers the announcement about a
     day reads `A = (E ∧ ¬A)`: no admissible ending when the exam is that day (the liar), an
     admissible one when it is not. Only the idealisation puts a liar in the calendar.

Honest size: the model is the one of the stand `dilemmas/surprise.py`, now on ZTime's clock; the
resolution "the class cannot know the announcement in advance" is Quine's (1953) and the liar reading
is Shaw's/Fitch's line. What is added is that both are theorems of ZTL's existing temporal layer,
with knowledge = a hereditary earned verdict, for every `n` and every formula — not a new logic and
not a new idea of the paradox.

Discipline: no mathlib; `#print axioms` at the end — target: the empty axiom list.
-/

namespace Surprise
open ZTime ZTime.V

/-! ## The week -/

/-- "The exam is on one of the days before `k`". -/
def some_ : Nat → Fm
  | 0 => .bot
  | k + 1 => .disj (some_ k) (.atom k)

/-- "Among the days before `k`, an exam on a day means none before it" — at most one exam. -/
def atMost : Nat → Fm
  | 0 => .top
  | k + 1 => .conj (atMost k) (.imp (.atom k) (.neg (some_ k)))

/-- The announcement, its checkable part: exactly one exam among the `n` days. -/
def ann (n : Nat) : Fm := .conj (some_ n) (atMost n)

/-- To know: an earned verdict on the shelf — `T`, and no verification can change it. -/
def Knows (m : Marking) (φ : Fm) : Prop := evalF m φ = V.T ∧ Hereditary φ m

/-- The morning of day `d` before any exam: earlier days verified "no exam", the rest dirty. -/
def morning (d : Nat) : Marking := fun i => if i < d then V.F else V.Z

/-- The morning of day `d` after the exam on day `e < d`. -/
def hist (e d : Nat) : Marking := fun i => if i < d then (if i = e then V.T else V.F) else V.Z

/-- A finished week with the exam on day `e`. -/
def exam (e : Nat) : Marking := fun i => if i = e then V.T else V.F

/-- A finished week with no exam at all. -/
def noExam : Marking := fun _ => V.F

/-- A finished week with two exams, on days `e` and `k`. -/
def two (e k : Nat) : Marking := fun i => if i = e then V.T else if i = k then V.T else V.F

/-! ## The values, as the kernel computes them -/

theorem zor_T_left (y : V) : zor V.T y = V.T := by cases y <;> rfl
theorem zor_T_right (x : V) : zor x V.T = V.T := by cases x <;> rfl
theorem zand_F_left (y : V) : zand V.F y = V.F := by cases y <;> rfl
theorem zand_F_right (x : V) : zand x V.F = V.F := by cases x <;> rfl
theorem zimp_F_left (y : V) : zimp V.F y = V.T := by cases y <;> rfl

theorem morning_FZ (d i : Nat) : morning d i = V.F ∨ morning d i = V.Z := by
  unfold morning; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Before any exam, "there is an exam" never evaluates to `T` on a morning. -/
theorem some_morning (d : Nat) : ∀ k, evalF (morning d) (some_ k) = V.F
  | 0 => rfl
  | k + 1 => by
      show zor (evalF (morning d) (some_ k)) (morning d k) = V.F
      rw [some_morning d k]
      rcases morning_FZ d k with h | h <;> rw [h] <;> rfl

theorem some_noExam : ∀ k, evalF noExam (some_ k) = V.F
  | 0 => rfl
  | k + 1 => by
      show zor (evalF noExam (some_ k)) V.F = V.F
      rw [some_noExam k]; rfl

/-- Once day `e` holds `T`, "there is an exam before `k`" is `T` for every `k > e`. -/
theorem some_of_T {m : Marking} {e : Nat} (he : m e = V.T) : ∀ k, e < k → evalF m (some_ k) = V.T
  | 0, h => absurd h (Nat.not_lt_zero e)
  | k + 1, h => by
      show zor (evalF m (some_ k)) (m k) = V.T
      rcases Nat.lt_or_ge e k with hk | hk
      · rw [some_of_T he k hk]; exact zor_T_left _
      · have hek : e = k := Nat.le_antisymm (Nat.le_of_lt_succ h) hk
        rw [← hek, he]; exact zor_T_right _

theorem some_exam_le {e : Nat} : ∀ k, k ≤ e → evalF (exam e) (some_ k) = V.F
  | 0, _ => rfl
  | k + 1, h => by
      show zor (evalF (exam e) (some_ k)) (exam e k) = V.F
      have hk : k ≠ e := Nat.ne_of_lt h
      have hx : exam e k = V.F := if_neg hk
      rw [some_exam_le k (Nat.le_of_succ_le h), hx]; rfl

theorem atMost_noExam : ∀ k, evalF noExam (atMost k) = V.T
  | 0 => rfl
  | k + 1 => by
      show zand (evalF noExam (atMost k)) (zimp V.F (znot (evalF noExam (some_ k)))) = V.T
      rw [atMost_noExam k, zimp_F_left]; rfl

theorem atMost_exam (e : Nat) : ∀ k, evalF (exam e) (atMost k) = V.T
  | 0 => rfl
  | k + 1 => by
      show zand (evalF (exam e) (atMost k)) (zimp (exam e k) (znot (evalF (exam e) (some_ k)))) = V.T
      rw [atMost_exam e k]
      by_cases hk : k = e
      · have hx : exam e k = V.T := if_pos hk
        rw [hx, some_exam_le k (Nat.le_of_eq hk)]; rfl
      · have hx : exam e k = V.F := if_neg hk
        rw [hx, zimp_F_left]; rfl

/-- Two exams, on `e < k < n`: "at most one" is `F`. -/
theorem atMost_two {e k : Nat} (hek : e < k) : ∀ n, k < n → evalF (two e k) (atMost n) = V.F
  | 0, h => absurd h (Nat.not_lt_zero k)
  | n + 1, h => by
      show zand (evalF (two e k) (atMost n)) (zimp (two e k n) (znot (evalF (two e k) (some_ n)))) = V.F
      rcases Nat.lt_or_ge k n with hkn | hkn
      · rw [atMost_two hek n hkn]; exact zand_F_left _
      · have hkn' : k = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hkn
        have hTe : two e k e = V.T := if_pos rfl
        have hTk : two e k n = V.T := by
          show (if n = e then V.T else if n = k then V.T else V.F) = V.T
          have : n ≠ e := by
            intro h'
            have hee : e < e := by
              have := hek
              rw [hkn', h'] at this
              exact this
            exact Nat.lt_irrefl e hee
          rw [if_neg this, if_pos hkn'.symm]
        rw [hTk, some_of_T hTe n (hkn' ▸ hek)]
        exact zand_F_right _

/-- The week's formulas read only the week's days. -/
theorem some_congr {m m' : Marking} : ∀ k, (∀ i, i < k → m' i = m i) →
    evalF m' (some_ k) = evalF m (some_ k)
  | 0, _ => rfl
  | k + 1, h => by
      show zor (evalF m' (some_ k)) (m' k) = zor (evalF m (some_ k)) (m k)
      rw [some_congr k (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem atMost_congr {m m' : Marking} : ∀ k, (∀ i, i < k → m' i = m i) →
    evalF m' (atMost k) = evalF m (atMost k)
  | 0, _ => rfl
  | k + 1, h => by
      have h' : ∀ i, i < k → m' i = m i := fun i hi => h i (Nat.lt_succ_of_lt hi)
      show zand (evalF m' (atMost k)) (zimp (m' k) (znot (evalF m' (some_ k))))
         = zand (evalF m (atMost k)) (zimp (m k) (znot (evalF m (some_ k))))
      rw [atMost_congr k h', some_congr k h', h k (Nat.lt_succ_self k)]

theorem ann_congr {m m' : Marking} (n : Nat) (h : ∀ i, i < n → m' i = m i) :
    evalF m' (ann n) = evalF m (ann n) := by
  show zand (evalF m' (some_ n)) (evalF m' (atMost n)) = zand (evalF m (some_ n)) (evalF m (atMost n))
  rw [some_congr n h, atMost_congr n h]

/-! ## The refinements: what the coming days may bring -/

theorem noExam_refines_morning (d : Nat) : Refines noExam (morning d) := by
  intro i hi
  unfold morning at hi ⊢
  split
  · rfl
  · next h => exact absurd (if_neg h) hi

theorem exam_refines_morning {d e : Nat} (h : d ≤ e) : Refines (exam e) (morning d) := by
  intro i hi
  unfold morning at hi ⊢
  split
  · next hid =>
      show (if i = e then V.T else V.F) = V.F
      exact if_neg (Nat.ne_of_lt (Nat.lt_of_lt_of_le hid h))
  · next hid => exact absurd (if_neg hid) hi

theorem two_refines_hist {e d : Nat} : Refines (two e d) (hist e d) := by
  intro i hi
  unfold hist at hi ⊢
  split
  · next hid =>
      show (if i = e then V.T else if i = d then V.T else V.F) = (if i = e then V.T else V.F)
      by_cases hie : i = e
      · rw [if_pos hie, if_pos hie]
      · rw [if_neg hie, if_neg hie, if_neg (Nat.ne_of_lt hid)]
  · next hid => exact absurd (if_neg hid) hi

/-! ## 1. Every day is a surprise, the last one included -/

/-- **On the morning of any day, the class does not know "the exam is today".** -/
theorem today_unknown (d : Nat) : ¬ Knows (morning d) (.atom d) := by
  intro h
  have hz : morning d d = V.Z := if_neg (Nat.lt_irrefl d)
  have hT : evalF (morning d) (.atom d) = V.T := h.1
  rw [show evalF (morning d) (.atom d) = morning d d from rfl, hz] at hT
  exact V.noConfusion hT

/-- **No known formula singles out today.** Whatever the class knows on the morning of day `d` is
true both in the week with the exam today and in the week with no exam at all. -/
theorem surprise_guaranteed {d : Nat} {φ : Fm} (h : Knows (morning d) φ) :
    evalF (exam d) φ = V.T ∧ evalF noExam φ = V.T :=
  ⟨(h.2 _ (exam_refines_morning (Nat.le_refl d))).trans h.1, (h.2 _ (noExam_refines_morning d)).trans h.1⟩

/-! ## 2–3. The announcement is earned only when the week is over -/

/-- **Before the exam, the announcement is never known**, on any morning whatever. -/
theorem ann_never_known_before_exam (n d : Nat) : ¬ Knows (morning d) (ann n) := by
  intro h
  have e1 : evalF noExam (ann n) = evalF (morning d) (ann n) := h.2 _ (noExam_refines_morning d)
  have e2 : evalF noExam (ann n) = V.F := by
    show zand (evalF noExam (some_ n)) (evalF noExam (atMost n)) = V.F
    rw [some_noExam n]; exact zand_F_left _
  rw [h.1, e2] at e1
  exact V.noConfusion e1

/-- **"There is an exam" is earned on the exam day** and stays earned. -/
theorem exam_known_after_it {e d n : Nat} (hed : e < d) (hen : e < n) :
    Knows (hist e d) (some_ n) := by
  have hT : hist e d e = V.T := by
    show (if e < d then (if e = e then V.T else V.F) else V.Z) = V.T
    rw [if_pos hed, if_pos rfl]
  refine ⟨some_of_T hT n hen, ?_⟩
  intro m' hr
  have hT' : m' e = V.T := by rw [hr e (by rw [hT]; exact V.noConfusion)]; exact hT
  rw [some_of_T hT' n hen, some_of_T hT n hen]

/-- **"Exactly one exam" is known exactly when the whole week has been verified.** -/
theorem ann_known_iff_week_over {e d n : Nat} (hed : e < d) (hen : e < n) :
    Knows (hist e d) (ann n) ↔ n ≤ d := by
  have hagree : ∀ i, i < d → hist e d i = exam e i := by
    intro i hi; show (if i < d then (if i = e then V.T else V.F) else V.Z) = _; rw [if_pos hi]; rfl
  have hexam : evalF (exam e) (ann n) = V.T := by
    show zand (evalF (exam e) (some_ n)) (evalF (exam e) (atMost n)) = V.T
    have hTe : exam e e = V.T := if_pos rfl
    rw [some_of_T hTe n hen, atMost_exam e n]; rfl
  constructor
  · intro h
    rcases Nat.lt_or_ge d n with hdn | hdn
    · exfalso
      have e1 : evalF (two e d) (ann n) = evalF (hist e d) (ann n) := h.2 _ two_refines_hist
      have e2 : evalF (two e d) (ann n) = V.F := by
        show zand (evalF (two e d) (some_ n)) (evalF (two e d) (atMost n)) = V.F
        rw [atMost_two hed n hdn]; exact zand_F_right _
      rw [h.1, e2] at e1
      exact V.noConfusion e1
    · exact hdn
  · intro hnd
    have hval : evalF (hist e d) (ann n) = V.T := by
      rw [ann_congr n (fun i hi => hagree i (Nat.lt_of_lt_of_le hi hnd))]; exact hexam
    refine ⟨hval, ?_⟩
    intro m' hr
    have hkeep : ∀ i, i < n → m' i = hist e d i := by
      intro i hi
      apply hr i
      show (if i < d then (if i = e then V.T else V.F) else V.Z) ≠ V.Z
      rw [if_pos (Nat.lt_of_lt_of_le hi hnd)]
      split <;> exact V.noConfusion
    rw [ann_congr n hkeep]

/-! ## 4. The backward step: a valid conditional on an unearned antecedent -/

/-- **On the last morning "if the announcement holds, the exam is today" evaluates to `T`** (as written; the
theorem does not state heredity) — and `ann_never_known_before_exam` says the class does not hold the antecedent. -/
theorem last_step_conditional (k : Nat) :
    evalF (morning k) (.imp (ann (k + 1)) (.atom k)) = V.T := by
  show zimp (zand (zor (evalF (morning k) (some_ k)) (morning k k)) (evalF (morning k) (atMost (k + 1))))
            (morning k k) = V.T
  rw [some_morning k k]
  have hz : morning k k = V.Z := if_neg (Nat.lt_irrefl k)
  rw [hz]
  show zimp (zand V.F _) V.Z = V.T
  rw [zand_F_left]; rfl

/-! ## 5. The class's conclusion is a value on credit -/

/-- **On Monday "there will be no exam" evaluates to `T` — and is not hereditary**: the tick of an
exam day overturns it. A `T` on credit, not knowledge. -/
theorem no_exam_on_credit (k : Nat) :
    evalF (morning 0) (.neg (some_ (k + 1))) = V.T ∧ ¬ Hereditary (.neg (some_ (k + 1))) (morning 0) := by
  have hv : evalF (morning 0) (.neg (some_ (k + 1))) = V.T := by
    show znot (evalF (morning 0) (some_ (k + 1))) = V.T
    rw [some_morning 0 (k + 1)]; rfl
  refine ⟨hv, ?_⟩
  intro hH
  have e1 := hH _ (exam_refines_morning (Nat.zero_le 0))
  have hT0 : exam 0 0 = V.T := if_pos rfl
  have e2 : evalF (exam 0) (.neg (some_ (k + 1))) = V.F := by
    show znot (evalF (exam 0) (some_ (k + 1))) = V.F
    rw [some_of_T hT0 (k + 1) (Nat.succ_pos k)]; rfl
  rw [e2, hv] at e1
  exact V.noConfusion e1

/-! ## 7. The class's logic is right; the teacher keeps the promise

The two statements that close the account. First, the backward induction itself, classically: if the
class KNEW the whole announcement — "exactly one exam, on a day you will not be able to single out" —
the set of possible exam days would have to be a fixed point of "a day is possible only if a later
possible day remains", and the only fixed point is empty. The class's logic is sound; what it lacks is
the premise (`ann_never_known_before_exam`). Second, the teacher: for every exam day the announcement is
earned once the week is over, and on that morning the class did not know. Both sides are right, at
different times — which is all the paradox ever was. -/

/-- A classical candidate set of exam days, `W i` for the days `i < n`, is CONSISTENT WITH KNOWING THE
WHOLE ANNOUNCEMENT when a day is possible exactly if, on its morning, a later possible day would still
be open (otherwise the class would single it out, and the surprise clause would fail). -/
def KnownFixed (n : Nat) (W : Nat → Bool) : Prop :=
  ∀ e, e < n → (W e = true ↔ ∃ j, e < j ∧ j < n ∧ W j = true)

/-- **The class's backward induction is valid**: with the announcement known, no day is possible. -/
theorem classical_elimination {n : Nat} {W : Nat → Bool} (h : KnownFixed n W) :
    ∀ e, e < n → W e = false := by
  -- by the distance to the end of the week, without subtraction: `Q t` covers the days `e` with `n ≤ e + t`
  have step : ∀ t e, n ≤ e + t → e < n → W e = false := by
    intro t
    induction t with
    | zero => intro e hle hlt; exact absurd hlt (Nat.not_lt_of_le hle)
    | succ t ih =>
        intro e hle hlt
        cases hW : W e with
        | false => rfl
        | true =>
            match (h e hlt).1 hW with
            | ⟨j, hej, hjn, hWj⟩ =>
                have hj : n ≤ j + t := Nat.le_trans hle (by
                  show e + (t + 1) ≤ j + t
                  rw [← Nat.add_assoc, Nat.add_right_comm]
                  exact Nat.add_le_add_right hej t)
                rw [ih j hj hjn] at hWj
                exact absurd hWj Bool.false_ne_true
  intro e he
  exact step n e (Nat.le_add_left n e) he

/-- **The teacher keeps the promise.** For every exam day `e` of the week: the announcement is known
once the whole week is verified, and on the morning of day `e` the class did not know the exam was
that day — nor anything that would single it out (`surprise_guaranteed`). -/
theorem teacher_keeps_promise {n e : Nat} (hen : e < n) :
    Knows (hist e n) (ann n) ∧ ¬ Knows (morning e) (.atom e) :=
  ⟨(ann_known_iff_week_over hen hen).2 (Nat.le_refl n), today_unknown e⟩

/-! ## 6. Perfect knowers: the liar in the calendar -/

/-- Row 0 is the announcement about one day for knowers whose knowledge is instantaneous and
perfect: `A = (E ∧ ¬A)`; row 1 is `E`, "the exam is that day", a free atom. -/
def surpriseSys : System
  | 0 => some (.conj (.atom 1) (.neg (.atom 0)))
  | _ + 1 => none

/-- **With the exam that day, no ending is admissible** — the liar. -/
theorem liar_when_exam_today {m : Marking} (h1 : m 1 = V.T) : ¬ Completable surpriseSys m := by
  intro hc
  match hc with
  | ⟨c, hcomp, ha⟩ =>
      have hc1 : c 1 = V.T := by rw [hcomp.1 1 (by rw [h1]; exact V.noConfusion)]; exact h1
      have h0 : c 0 = zand (c 1) (znot (c 0)) := ha 0 _ rfl
      rw [hc1] at h0
      have hne := hcomp.2 0
      revert h0 hne
      cases c 0 <;> decide

/-- **With no exam that day, an ending is admissible** — the equation is grounded. -/
theorem grounded_when_no_exam {m : Marking} (h1 : m 1 = V.F) (hz : ∀ i, i ≠ 1 → m i = V.Z) :
    Completable surpriseSys m := by
  refine ⟨noExam, ⟨?_, fun _ => V.noConfusion⟩, ?_⟩
  · intro i hi
    by_cases h : i = 1
    · rw [h, h1]; rfl
    · exact absurd (hz i h) hi
  · intro i φ hφ
    match i, hφ with
    | 0, h => rw [← Option.some.inj h]; rfl

end Surprise

#print axioms Surprise.today_unknown
#print axioms Surprise.surprise_guaranteed
#print axioms Surprise.ann_never_known_before_exam
#print axioms Surprise.exam_known_after_it
#print axioms Surprise.ann_known_iff_week_over
#print axioms Surprise.last_step_conditional
#print axioms Surprise.no_exam_on_credit
#print axioms Surprise.liar_when_exam_today
#print axioms Surprise.grounded_when_no_exam
#print axioms Surprise.classical_elimination
#print axioms Surprise.teacher_keeps_promise
