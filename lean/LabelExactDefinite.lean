import ZReceiptHard

/-!
# The receipt names nothing idle — on a linear claim, under a DEFINITE reading.
# Zero axioms. (E60)

`label_exact_linear` (LabelExact.lean) proves that on a linear claim every atom
on the receipt is pivotal: some reading of the other unverified grounds — and
`pivotal` lets that reading stay partial — makes `a := T` and `a := F` give
different verdicts. The paper's sentence was stronger: a DEFINITE reading of
the others. E59 (2026-09-07) found the gap between prose and theorem, softened
the prose, and measured the strong form — 57,969 named atoms on 48,759 pending
linear cells, no failure. This file proves it.

    pivotalD v φ a               :  pivotal, both readings definite on φ's atoms
    label_exact_linear_definite  :  linMarks v φ → labF v φ a = true → pivotalD v φ a

NOT A REWRITE. The partial pair (w₁, w₂) that `label_exact_linear` gives is the
start. If both verdicts are definite, filling every remaining mark inside φ to
T (`fillOn`) keeps them: the lazy register is monotone (`evalK_mono`), and a
definite value has nothing above it. If one side reads Z, that side is a
pending LINEAR claim at a marking of its own — a refinement only loses marks
(`linMarks_of_fills`) — so `drivable` pushes it to the value the other side
does not have, while the other side, definite, stays where it was; then fill.
Nine pairs of verdicts: three are excluded by the pair disagreeing, two are
filled, four are driven.

The one fact needed about `a` itself — that `v` has it unverified — is not a
lemma about `labF`; it is read off the pair: `w₁ a = T ≠ F = w₂ a`, while both
agree with `v` wherever `v` is verified.

MEASURED FIRST (`zlabelexactdef.py`, the judge's own lazy evaluator): on all
formulas of depth ≤ 2 over three atoms under all 27 markings, every named atom
of every pending linear cell is pivotal under a DEFINITE reading of the others
— and outside the linear class the same census finds named atoms that are
not, `p ∧ ¬p` first among them.
-/

namespace V

/-- Definite on the atoms the claim reads. -/
def definiteOn (w : Nat → V) (φ : Fm) : Prop :=
  ∀ n, occurs n φ = true → w n ≠ Z

/-- `pivotal`, with both readings definite on the atoms of φ. -/
def pivotalD (v : Nat → V) (φ : Fm) (a : Nat) : Prop :=
  ∃ w1 w2 : Nat → V, fills v w1 φ ∧ fills v w2 φ ∧
    definiteOn w1 φ ∧ definiteOn w2 φ ∧
    w1 a = T ∧ w2 a = F ∧
    (∀ n, n ≠ a → w1 n = w2 n) ∧ evalK w1 φ ≠ evalK w2 φ

theorem pivotalD_pivotal (v : Nat → V) (φ : Fm) (a : Nat) (h : pivotalD v φ a) :
    pivotal v φ a := by
  obtain ⟨w1, w2, hf1, hf2, _, _, ha1, ha2, hd, hne⟩ := h
  exact ⟨w1, w2, hf1, hf2, ha1, ha2, hd, hne⟩

/-! ## Refinement bookkeeping -/

theorem fills_trans (v w u : Nat → V) (φ : Fm) (hvw : fills v w φ) (hwu : fills w u φ) :
    fills v u φ := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have h1 : w n = v n := hvw.1 n hn
    have h2 : w n ≠ Z := by rw [h1]; exact hn
    rw [hwu.1 n h2, h1]
  · intro n hn
    rw [hwu.2 n hn, hvw.2 n hn]

/-- A refinement only loses marks, so linearity survives it. -/
theorem linMarks_of_fills (v w : Nat → V) (φ : Fm) (hlin : linMarks v φ) (hf : fills v w φ) :
    linMarks w φ := by
  intro n hz
  cases hv : decide (v n = Z) with
  | true => exact hlin n (of_decide_eq_true hv)
  | false =>
      have hvn : v n ≠ Z := of_decide_eq_false hv
      have h := hf.1 n hvn
      rw [h] at hz
      exact absurd hz hvn

theorem leqb_Z_left : ∀ x : V, leqb Z x = true := by decide

theorem leqb_F_eq : ∀ y : V, leqb F y = true → y = F := by
  intro y h
  cases y with
  | T => exact absurd h (by decide)
  | F => rfl
  | Z => exact absurd h (by decide)

/-- Above a definite value there is nothing but itself. -/
theorem def_of_leqb : ∀ x y : V, x ≠ Z → leqb x y = true → y = x := by
  intro x y hx h
  cases x with
  | T => exact leqb_T_eq y h
  | F => exact leqb_F_eq y h
  | Z => exact absurd rfl hx

/-- A refinement sits above in the information order. -/
theorem leqb_of_fills (w u : Nat → V) (φ : Fm) (hf : fills w u φ) :
    ∀ n, leqb (w n) (u n) = true := by
  intro n
  cases hw : decide (w n = Z) with
  | true =>
      rw [of_decide_eq_true hw]; exact leqb_Z_left (u n)
  | false =>
      have hne : w n ≠ Z := of_decide_eq_false hw
      rw [hf.1 n hne]; exact leqb_refl (w n)

/-- Re-pointing `a` inside a refinement of `v` is still a refinement of `v`,
provided `v` has `a` unverified and the claim reads `a`. -/
theorem fills_setA (v u : Nat → V) (φ : Fm) (a : Nat) (x : V)
    (hva : v a = Z) (ho : occurs a φ = true) (hf : fills v u φ) :
    fills v (setA a x u) φ := by
  refine ⟨?_, ?_⟩
  · intro n hn
    have hna : n ≠ a := fun he => by rw [he, hva] at hn; exact hn rfl
    rw [setA_other x u hna]; exact hf.1 n hn
  · intro n hn
    have hna : n ≠ a := fun he => by rw [he, ho] at hn; exact Bool.noConfusion hn
    rw [setA_other x u hna]; exact hf.2 n hn

/-- If `w` sits below `u` off `a` and reads `x` at `a`, it sits below `setA a x u`. -/
theorem leqb_setA_of (w u : Nat → V) (a : Nat) (x : V)
    (hwa : w a = x) (hoff : ∀ n, n ≠ a → leqb (w n) (u n) = true) :
    ∀ n, leqb (w n) (setA a x u n) = true := by
  intro n
  cases hna : decide (n = a) with
  | true =>
      have he : n = a := of_decide_eq_true hna
      rw [he, setA_self, hwa]; exact leqb_refl x
  | false =>
      have hne : n ≠ a := of_decide_eq_false hna
      rw [setA_other x u hne]; exact hoff n hne

/-! ## Filling: every mark inside φ goes to T, everything else stays -/

def fillV : V → V
  | T => T
  | F => F
  | Z => T

theorem fillV_ne_Z : ∀ x : V, fillV x ≠ Z := by decide

theorem fillV_of_ne_Z : ∀ x : V, x ≠ Z → fillV x = x := by
  intro x h
  cases x with
  | T => rfl
  | F => rfl
  | Z => exact absurd rfl h

def fillOn (φ : Fm) (w : Nat → V) : Nat → V :=
  fun n => match occurs n φ with
    | true => fillV (w n)
    | false => w n

theorem fillOn_occ (φ : Fm) (w : Nat → V) (n : Nat) (h : occurs n φ = true) :
    fillOn φ w n = fillV (w n) := by
  show (match occurs n φ with | true => fillV (w n) | false => w n) = fillV (w n)
  rw [h]

theorem fillOn_nocc (φ : Fm) (w : Nat → V) (n : Nat) (h : occurs n φ = false) :
    fillOn φ w n = w n := by
  show (match occurs n φ with | true => fillV (w n) | false => w n) = w n
  rw [h]

theorem fills_fillOn (w : Nat → V) (φ : Fm) : fills w (fillOn φ w) φ := by
  refine ⟨?_, ?_⟩
  · intro n hn
    cases ho : occurs n φ with
    | true => rw [fillOn_occ φ w n ho]; exact fillV_of_ne_Z (w n) hn
    | false => exact fillOn_nocc φ w n ho
  · intro n hn
    exact fillOn_nocc φ w n hn

theorem definiteOn_fillOn (w : Nat → V) (φ : Fm) : definiteOn (fillOn φ w) φ := by
  intro n hn
  rw [fillOn_occ φ w n hn]
  exact fillV_ne_Z (w n)

theorem fillOn_agree (φ : Fm) (w1 w2 : Nat → V) (a : Nat)
    (hd : ∀ n, n ≠ a → w1 n = w2 n) :
    ∀ n, n ≠ a → fillOn φ w1 n = fillOn φ w2 n := by
  intro n hn
  cases ho : occurs n φ with
  | true => rw [fillOn_occ φ w1 n ho, fillOn_occ φ w2 n ho, hd n hn]
  | false => rw [fillOn_nocc φ w1 n ho, fillOn_nocc φ w2 n ho, hd n hn]

theorem fillOn_at (φ : Fm) (w : Nat → V) (a : Nat) (x : V) (ho : occurs a φ = true)
    (hx : x ≠ Z) (hw : w a = x) : fillOn φ w a = x := by
  rw [fillOn_occ φ w a ho, hw]
  exact fillV_of_ne_Z x hx

/-- From a pair of readings with definite, different verdicts: the definite pair. -/
theorem pivotalD_of_pair (v : Nat → V) (φ : Fm) (a : Nat) (u1 u2 : Nat → V)
    (ho : occurs a φ = true)
    (hf1 : fills v u1 φ) (hf2 : fills v u2 φ) (ha1 : u1 a = T) (ha2 : u2 a = F)
    (hd : ∀ n, n ≠ a → u1 n = u2 n)
    (x y : V) (hx : x ≠ Z) (hy : y ≠ Z) (hxy : x ≠ y)
    (h1 : evalK u1 φ = x) (h2 : evalK u2 φ = y) : pivotalD v φ a := by
  refine ⟨fillOn φ u1, fillOn φ u2,
          fills_trans v u1 _ φ hf1 (fills_fillOn u1 φ),
          fills_trans v u2 _ φ hf2 (fills_fillOn u2 φ),
          definiteOn_fillOn u1 φ, definiteOn_fillOn u2 φ,
          fillOn_at φ u1 a T ho (by decide) ha1,
          fillOn_at φ u2 a F ho (by decide) ha2,
          fillOn_agree φ u1 u2 a hd, ?_⟩
  have e1 : evalK (fillOn φ u1) φ = x := by
    have hm := evalK_mono (leqb_of_fills u1 (fillOn φ u1) φ (fills_fillOn u1 φ)) φ
    rw [h1] at hm
    exact def_of_leqb x _ hx hm
  have e2 : evalK (fillOn φ u2) φ = y := by
    have hm := evalK_mono (leqb_of_fills u2 (fillOn φ u2) φ (fills_fillOn u2 φ)) φ
    rw [h2] at hm
    exact def_of_leqb y _ hy hm
  rw [e1, e2]; exact hxy

/-! ## The theorem -/

theorem label_exact_linear_definite (v : Nat → V) (a : Nat) :
    ∀ φ : Fm, linMarks v φ → labF v φ a = true → pivotalD v φ a := by
  intro φ hlin hl
  have hp := label_exact_linear v a φ hlin hl
  have ho : occurs a φ = true := pivotal_occurs v φ a hp
  obtain ⟨w1, w2, hf1, hf2, ha1, ha2, hd, hne⟩ := hp
  -- `a` is unverified in `v`: otherwise both readings would agree with `v` there
  have hva : v a = Z := by
    cases hv : decide (v a = Z) with
    | true => exact of_decide_eq_true hv
    | false =>
        have hvz : v a ≠ Z := of_decide_eq_false hv
        have e1 := hf1.1 a hvz
        have e2 := hf2.1 a hvz
        rw [ha1] at e1
        rw [ha2, ← e1] at e2
        exact absurd e2 (by decide)
  have hlin1 : linMarks w1 φ := linMarks_of_fills v w1 φ hlin hf1
  have hlin2 : linMarks w2 φ := linMarks_of_fills v w2 φ hlin hf2
  have hvu1 : ∀ u, fills w1 u φ → fills v u φ := fun u hu => fills_trans v w1 u φ hf1 hu
  have hvu2 : ∀ u, fills w2 u φ → fills v u φ := fun u hu => fills_trans v w2 u φ hf2 hu
  cases h1 : evalK w1 φ with
  | T =>
      cases h2 : evalK w2 φ with
      | T => exact absurd (h1.trans h2.symm) hne
      | F => exact pivotalD_of_pair v φ a w1 w2 ho hf1 hf2 ha1 ha2 hd T F
               (by decide) (by decide) (by decide) h1 h2
      | Z =>
          -- drive w2 to F; re-point a to T on the other side
          obtain ⟨u, hfu, hu⟩ := (drivable w2 φ hlin2 h2).2
          have hua : u a = F := by rw [hfu.1 a (by rw [ha2]; decide)]; exact ha2
          have hoff : ∀ n, n ≠ a → leqb (w1 n) (u n) = true :=
            fun n hn => by rw [hd n hn]; exact leqb_of_fills w2 u φ hfu n
          have hT : evalK (setA a T u) φ = T := by
            have hm := evalK_mono (leqb_setA_of w1 u a T ha1 hoff) φ
            rw [h1] at hm; exact leqb_T_eq _ hm
          exact pivotalD_of_pair v φ a (setA a T u) u ho
            (fills_setA v u φ a T hva ho (hvu2 u hfu)) (hvu2 u hfu)
            (setA_self a T u) hua (fun n hn => setA_other T u hn)
            T F (by decide) (by decide) (by decide) hT hu
  | F =>
      cases h2 : evalK w2 φ with
      | T => exact pivotalD_of_pair v φ a w1 w2 ho hf1 hf2 ha1 ha2 hd F T
               (by decide) (by decide) (by decide) h1 h2
      | F => exact absurd (h1.trans h2.symm) hne
      | Z =>
          -- drive w2 to T; the other side stays F
          obtain ⟨u, hfu, hu⟩ := (drivable w2 φ hlin2 h2).1
          have hua : u a = F := by rw [hfu.1 a (by rw [ha2]; decide)]; exact ha2
          have hoff : ∀ n, n ≠ a → leqb (w1 n) (u n) = true :=
            fun n hn => by rw [hd n hn]; exact leqb_of_fills w2 u φ hfu n
          have hF : evalK (setA a T u) φ = F := by
            have hm := evalK_mono (leqb_setA_of w1 u a T ha1 hoff) φ
            rw [h1] at hm; exact leqb_F_eq _ hm
          exact pivotalD_of_pair v φ a (setA a T u) u ho
            (fills_setA v u φ a T hva ho (hvu2 u hfu)) (hvu2 u hfu)
            (setA_self a T u) hua (fun n hn => setA_other T u hn)
            F T (by decide) (by decide) (by decide) hF hu
  | Z =>
      cases h2 : evalK w2 φ with
      | T =>
          -- drive w1 to F; the other side stays T
          obtain ⟨u, hfu, hu⟩ := (drivable w1 φ hlin1 h1).2
          have hua : u a = T := by rw [hfu.1 a (by rw [ha1]; decide)]; exact ha1
          have hoff : ∀ n, n ≠ a → leqb (w2 n) (u n) = true :=
            fun n hn => by rw [← hd n hn]; exact leqb_of_fills w1 u φ hfu n
          have hT : evalK (setA a F u) φ = T := by
            have hm := evalK_mono (leqb_setA_of w2 u a F ha2 hoff) φ
            rw [h2] at hm; exact leqb_T_eq _ hm
          exact pivotalD_of_pair v φ a u (setA a F u) ho
            (hvu1 u hfu) (fills_setA v u φ a F hva ho (hvu1 u hfu))
            hua (setA_self a F u) (fun n hn => (setA_other F u hn).symm)
            F T (by decide) (by decide) (by decide) hu hT
      | F =>
          -- drive w1 to T; the other side stays F
          obtain ⟨u, hfu, hu⟩ := (drivable w1 φ hlin1 h1).1
          have hua : u a = T := by rw [hfu.1 a (by rw [ha1]; decide)]; exact ha1
          have hoff : ∀ n, n ≠ a → leqb (w2 n) (u n) = true :=
            fun n hn => by rw [← hd n hn]; exact leqb_of_fills w1 u φ hfu n
          have hF : evalK (setA a F u) φ = F := by
            have hm := evalK_mono (leqb_setA_of w2 u a F ha2 hoff) φ
            rw [h2] at hm; exact leqb_F_eq _ hm
          exact pivotalD_of_pair v φ a u (setA a F u) ho
            (hvu1 u hfu) (fills_setA v u φ a F hva ho (hvu1 u hfu))
            hua (setA_self a F u) (fun n hn => (setA_other F u hn).symm)
            T F (by decide) (by decide) (by decide) hu hF
      | Z => exact absurd (h1.trans h2.symm) hne

#print axioms fills_trans
#print axioms linMarks_of_fills
#print axioms leqb_of_fills
#print axioms fills_fillOn
#print axioms pivotalD_of_pair
#print axioms pivotalD_pivotal
#print axioms label_exact_linear_definite

end V
