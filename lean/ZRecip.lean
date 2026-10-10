import ZSlopeExp

/-!
# ZRecip — reciprocals on VR's operational reals: near an interval clear of zero, `1/x` is near the kernel's
reciprocal reading (`RecipOK`, division-free), and Cauchy sequences clear of zero have Cauchy reciprocals.
Zero axioms. Used by `ZSlopeDiv` (quotients) and `ZLn` (the logarithm's slope `u'/u`).
-/

namespace ZRecip

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp

/-! ## Reciprocals -/

theorem ne_zero_of_lt {x : QExpr} (h : qlt qzero x) : ¬ qEq x qzero :=
  fun e => qlt_irrefl _ (qlt_respects (qEq_refl _) e h)

/-- The inverse is unique: `x·y = 1` gives `y = 1/x`. -/
theorem inv_unique {x y : QExpr} (hx : ¬ qEq x qzero) (h : qEq (qmul x y) qone) : qEq y (qinv' x) := by
  have c := qmul_inv'_cancel hx
  have e1 : qEq (qmul (qmul x y) (qinv' x)) (qmul y (qmul x (qinv' x))) := by rat_ring
  have e2 := qmul_respects h (qEq_refl (qinv' x))
  have e3 := qmul_respects (qEq_refl y) c
  have e4 := qone_mul (qinv' x)
  have e5 := qmul_one y
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem qinv'_neg {x : QExpr} (hx : ¬ qEq x qzero) : qEq (qinv' (qneg x)) (qneg (qinv' x)) := by
  have hnx : ¬ qEq (qneg x) qzero := fun e => hx (by
    have := qneg_respects e; have z : qEq (qneg qzero) qzero := by rat_ring
    exact qle_antisymm (by rat_linarith) (by rat_linarith))
  have c := qmul_inv'_cancel hnx
  have e : qEq (qmul x (qneg (qinv' (qneg x)))) (qmul (qneg x) (qinv' (qneg x))) := by rat_ring
  have u := inv_unique hx (qEq_trans e c)
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem qinv'_mul {x y : QExpr} (hx : ¬ qEq x qzero) (hy : ¬ qEq y qzero) :
    qEq (qinv' (qmul x y)) (qmul (qinv' x) (qinv' y)) := by
  have cx := qmul_inv'_cancel hx
  have cy := qmul_inv'_cancel hy
  have hxy : ¬ qEq (qmul x y) qzero := fun e => by
    have e1 : qEq (qmul (qmul x y) (qmul (qinv' x) (qinv' y))) (qmul (qmul x (qinv' x)) (qmul y (qinv' y))) := by
      rat_ring
    have e2 := qmul_respects e (qEq_refl (qmul (qinv' x) (qinv' y)))
    have e3 := qzero_mul (qmul (qinv' x) (qinv' y))
    have e4 := qmul_respects cx cy
    have e5 := qmul_one qone
    exact qzero_ne_one (qle_antisymm (by rat_linarith) (by rat_linarith))
  have e1 : qEq (qmul (qmul x y) (qmul (qinv' x) (qinv' y))) (qmul (qmul x (qinv' x)) (qmul y (qinv' y))) := by
    rat_ring
  have e4 := qmul_respects cx cy
  have e5 := qmul_one qone
  exact qEq_symm (inv_unique hxy (by exact qle_antisymm (by rat_linarith) (by rat_linarith)))

/-- `ε_k ≤ x, y`: `|1/x − 1/y| ≤ |x − y|·2^k·2^k`. -/
theorem recip_close {x y e : QExpr} {k : Nat} (hx : qle (qeps k) x) (hy : qle (qeps k) y) (h : qclose x y e) :
    qclose (qinv' x) (qinv' y) (qmul e (qmul (qofInt (pow2 k)) (qofInt (pow2 k)))) := by
  obtain ⟨ix0, ix1⟩ := qinv'_bound hx
  obtain ⟨iy0, iy1⟩ := qinv'_bound hy
  have cx := qmul_inv'_cancel (ne_zero_of_eps_le hx)
  have cy := qmul_inv'_cancel (ne_zero_of_eps_le hy)
  have bx : qclose (qinv' x) qzero (qofInt (pow2 k)) := by constructor <;> (unfold qsub; rat_linarith)
  have by' : qclose (qinv' y) qzero (qofInt (pow2 k)) := by constructor <;> (unfold qsub; rat_linarith)
  have d : qclose (qsub y x) qzero e := by obtain ⟨h1, h2⟩ := h; constructor <;> (unfold qsub at *; rat_linarith)
  have m := qmul_abs_bound d (qmul_abs_bound bx by')
  have e1 : qEq (qmul (qsub y x) (qmul (qinv' x) (qinv' y)))
      (qadd (qmul (qmul y (qinv' y)) (qinv' x)) (qneg (qmul (qmul x (qinv' x)) (qinv' y)))) := by
    unfold qsub; rat_ring
  have e2 := qmul_respects cy (qEq_refl (qinv' x))
  have e3 := qmul_respects cx (qEq_refl (qinv' y))
  have e4 := qone_mul (qinv' x)
  have e5 := qone_mul (qinv' y)
  obtain ⟨m1, m2⟩ := m
  constructor <;> (unfold qsub at *; rat_linarith)

/-- What the kernel checks of a reciprocal reading `[li, hi]` of `1/v`, `v ∈ [lv, hv]` not containing zero —
division-free. -/
def RecipOK (li hi lv hv : QExpr) : Prop :=
  qle lv hv ∧ ((qlt qzero lv ∧ qle (qmul li hv) qone ∧ qle qone (qmul hi lv)) ∨
               (qlt hv qzero ∧ qle qone (qmul li hv) ∧ qle (qmul hi lv) qone))

/-- On the interval itself the reciprocal lies in the reading. -/
theorem recip_exact {li hi lv hv v : QExpr} (h : RecipOK li hi lv hv) (h1 : qle lv v) (h2 : qle v hv) :
    qle li (qinv' v) ∧ qle (qinv' v) hi := by
  obtain ⟨_, ⟨hp, a, b⟩ | ⟨hn, a, b⟩⟩ := h
  · have vp : qlt qzero v := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hp) h1, fun hv =>
      (qlt_iff_le_not_le.mp hp).2 (qle_trans h1 hv)⟩
    have i0 := qinv'_nonneg_of_pos vp
    have c := qmul_inv'_cancel (ne_zero_of_lt vp)
    constructor
    · cases qle_total li qzero with
      | inl hl => exact qle_trans hl i0
      | inr hl =>
          have f1 := scale_l h2 hl
          have f2 := ZExp.scale (qle_trans f1 a) i0
          have e1 : qEq (qmul (qmul li v) (qinv' v)) (qmul li (qmul v (qinv' v))) := by rat_ring
          have e2 := qmul_respects (qEq_refl li) c
          have e3 := qmul_one li
          have e4 := qone_mul (qinv' v)
          rat_linarith
    · have hi0 : qle qzero hi := by
        cases qle_total qzero hi with
        | inl h => exact h
        | inr h =>
            have f := scale_l (qle_of_qlt hp) (by rat_linarith : qle qzero (qneg hi))
            have e : qEq (qmul (qneg hi) lv) (qneg (qmul hi lv)) := by rat_ring
            have e0 := qmul_zero (qneg hi)
            have := qle_of_qlt qone_pos
            rat_linarith
      have f1 := scale_l h1 hi0
      have f2 := ZExp.scale (qle_trans b f1) i0
      have e1 : qEq (qmul (qmul hi v) (qinv' v)) (qmul hi (qmul v (qinv' v))) := by rat_ring
      have e2 := qmul_respects (qEq_refl hi) c
      have e3 := qmul_one hi
      have e4 := qone_mul (qinv' v)
      rat_linarith
  · -- v < 0: 1/v = −1/(−v), and −v ∈ [−hv, −lv] positive
    obtain ⟨hv0, hv1⟩ := qlt_iff_le_not_le.mp hn
    have vn : qlt qzero (qneg v) :=
      qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => hv1 (qle_trans (by rat_linarith : qle qzero v) h2)⟩
    have vne : ¬ qEq v qzero := fun e => ne_zero_of_lt vn (by
      have := qneg_respects e; have z : qEq (qneg qzero) qzero := by rat_ring
      exact qle_antisymm (by rat_linarith) (by rat_linarith))
    have i0 := qinv'_nonneg_of_pos vn
    have c := qmul_inv'_cancel (ne_zero_of_lt vn)
    have ng := qinv'_neg vne
    constructor
    · -- li ≤ 1/v  ⟸  (−li)·(−v) ≥ 1·... : −li ≥ 1/(−v)
      have hli : qle li qzero := by
        cases qle_total li qzero with
        | inl h => exact h
        | inr h =>
            have := qle_of_qlt hn
            have f := scale_l this h
            have e := qmul_zero li
            have := qle_of_qlt qone_pos
            rat_linarith
      have f1 := scale_l (by rat_linarith : qle (qneg hv) (qneg v)) (by rat_linarith : qle qzero (qneg li))
      have e0 : qEq (qmul (qneg li) (qneg hv)) (qmul li hv) := by rat_ring
      have f2 := ZExp.scale (qle_trans (by rat_linarith : qle qone (qmul (qneg li) (qneg hv))) f1) i0
      have e1 : qEq (qmul (qmul (qneg li) (qneg v)) (qinv' (qneg v))) (qmul (qneg li) (qmul (qneg v) (qinv' (qneg v)))) := by
        rat_ring
      have e2 := qmul_respects (qEq_refl (qneg li)) c
      have e3 := qmul_one (qneg li)
      have e4 := qone_mul (qinv' (qneg v))
      rat_linarith
    · cases qle_total hi qzero with
      | inr hh =>
          -- 1/v ≤ 0 ≤ hi
          have := ng
          have := i0
          rat_linarith
      | inl hh =>
          have f1 := scale_l (by rat_linarith : qle (qneg v) (qneg lv)) (by rat_linarith : qle qzero (qneg hi))
          have e0 : qEq (qmul (qneg hi) (qneg lv)) (qmul hi lv) := by rat_ring
          have f2 := ZExp.scale f1 i0
          have e1 : qEq (qmul (qmul (qneg hi) (qneg v)) (qinv' (qneg v))) (qmul (qneg hi) (qmul (qneg v) (qinv' (qneg v)))) := by
            rat_ring
          have e2 := qmul_respects (qEq_refl (qneg hi)) c
          have e3 := qmul_one (qneg hi)
          have e4 := qone_mul (qinv' (qneg v))
          have f3 := ZExp.scale b i0
          have e5 := qmul_respects e0 (qEq_refl (qinv' (qneg v)))
          have := ng
          rat_linarith

/-- The point of `[lv, hv]` nearest to `x` (decidable comparisons — a computation, not a choice). -/
def clamp (x lv hv : QExpr) : QExpr :=
  match qle.decidable x lv with
  | .isTrue _ => lv
  | .isFalse _ =>
      match qle.decidable hv x with
      | .isTrue _ => hv
      | .isFalse _ => x

theorem clamp_facts {x lv hv δ : QExpr} (hlh : qle lv hv) (hδ : qle qzero δ) (h1 : qle (qsub lv δ) x)
    (h2 : qle x (qadd hv δ)) :
    qle lv (clamp x lv hv) ∧ qle (clamp x lv hv) hv ∧ qclose x (clamp x lv hv) δ := by
  unfold qsub at h1
  unfold clamp
  cases qle.decidable x lv with
  | isTrue a => exact ⟨qle_refl _, hlh, by constructor <;> (unfold qsub; rat_linarith)⟩
  | isFalse a =>
      have a' : qle lv x := by cases qle_total x lv with
        | inl h => exact absurd h a
        | inr h => exact h
      cases qle.decidable hv x with
      | isTrue b => exact ⟨hlh, qle_refl _, by constructor <;> (unfold qsub; rat_linarith)⟩
      | isFalse b =>
          have b' : qle x hv := by cases qle_total hv x with
            | inl h => exact absurd h b
            | inr h => exact h
          exact ⟨a', b', qclose_refl x δ hδ⟩

/-- Positive denominators: near `[lv, hv]` the reciprocal is near `[li, hi]`, uniformly. -/
theorem recip_near_pos {li hi lv hv : QExpr} (hlh : qle lv hv) (hp : qlt qzero lv)
    (a : qle (qmul li hv) qone) (b : qle qone (qmul hi lv)) (k : Nat) :
    ∃ J, ∀ x, qle (qsub lv (qeps J)) x → qle x (qadd hv (qeps J)) →
      qlt qzero x ∧ qle (qsub li (qeps k)) (qinv' x) ∧ qle (qinv' x) (qadd hi (qeps k)) := by
  have hR : RecipOK li hi lv hv := ⟨hlh, Or.inl ⟨hp, a, b⟩⟩
  obtain ⟨B, hB0, _⟩ := qexpr_bound hi
  have hB : qle hi (qofInt (pow2 B)) := by unfold qsub at hB0; rat_linarith
  have lv0 := qle_of_qlt hp
  -- ε_B ≤ lv: lv·2^B ≥ lv·hi ≥ 1
  have f1 := scale_l hB lv0
  have c1 : qEq (qmul lv hi) (qmul hi lv) := qmul_comm _ _
  have f2 := ZExp.scale (by rat_linarith : qle qone (qmul lv (qofInt (pow2 B)))) (qeps_nonneg B)
  have m1 : qEq (qmul (qofInt (pow2 B)) (qeps (0 + B))) (qeps 0) := qpow2_mul_eps B 0
  rw [Nat.zero_add] at m1
  have m2 : qEq (qmul (qmul lv (qofInt (pow2 B))) (qeps B)) (qmul lv (qmul (qofInt (pow2 B)) (qeps B))) := by rat_ring
  have m3 := qmul_respects (qEq_refl lv) m1
  have m4 := qmul_one lv
  have m5 := qone_mul (qeps B)
  have m6 := qeps_zero
  have m7 : qEq (qmul lv (qeps 0)) (qmul lv qone) := qmul_respects (qEq_refl lv) m6
  have lvB : qle (qeps B) lv := by rat_linarith
  refine ⟨(k + (B + 1)) + (B + 1), fun x h1 h2 => ?_⟩
  have dJ : qle (qeps ((k + (B + 1)) + (B + 1))) (qeps (B + 1)) := by
    have := qeps_le_add (B + 1) (k + (B + 1)); rw [Nat.add_comm (B + 1) (k + (B + 1))] at this; exact this
  have sB := qeps_succ_add B
  have e0 := qeps_nonneg ((k + (B + 1)) + (B + 1))
  have e1 := qeps_nonneg (B + 1)
  obtain ⟨w1, w2, wc⟩ := clamp_facts hlh e0 h1 h2
  have xB : qle (qeps (B + 1)) x := by unfold qsub at h1; rat_linarith
  have wB : qle (qeps (B + 1)) (clamp x lv hv) := by rat_linarith
  have rc := recip_close xB wB wc
  obtain ⟨r1, r2⟩ := recip_exact hR w1 w2
  -- the error: ε_J · (2^{B+1} · 2^{B+1}) = ε_k
  have p1 := qpow2_mul_eps (B + 1) (k + (B + 1))
  have p2 := qpow2_mul_eps (B + 1) k
  have p3 : qEq (qmul (qeps ((k + (B + 1)) + (B + 1))) (qmul (qofInt (pow2 (B + 1))) (qofInt (pow2 (B + 1)))))
      (qmul (qofInt (pow2 (B + 1))) (qmul (qofInt (pow2 (B + 1))) (qeps ((k + (B + 1)) + (B + 1))))) := by rat_ring
  have p4 := qmul_respects (qEq_refl (qofInt (pow2 (B + 1)))) p1
  obtain ⟨c1', c2'⟩ := rc
  have xpos : qlt qzero x := qlt_iff_le_not_le.mpr ⟨qle_trans (qeps_nonneg _) xB, fun h =>
    (qlt_iff_le_not_le.mp (qeps_pos (B + 1))).2 (qle_trans xB h)⟩
  unfold qsub at *
  exact ⟨xpos, by rat_linarith, by rat_linarith⟩

/-- NEAR `V`, THE RECIPROCAL IS NEAR ITS READING — both signs (negative through `1/(−x) = −1/x`). -/
theorem recip_near {li hi lv hv : QExpr} (h : RecipOK li hi lv hv) (k : Nat) :
    ∃ J, ∀ x, qle (qsub lv (qeps J)) x → qle x (qadd hv (qeps J)) →
      ¬ qEq x qzero ∧ qle (qsub li (qeps k)) (qinv' x) ∧ qle (qinv' x) (qadd hi (qeps k)) := by
  obtain ⟨hlh, ⟨hp, a, b⟩ | ⟨hn, a, b⟩⟩ := h
  · obtain ⟨J, hJ⟩ := recip_near_pos hlh hp a b k
    exact ⟨J, fun x h1 h2 => by obtain ⟨p, q, r⟩ := hJ x h1 h2; exact ⟨ne_zero_of_lt p, q, r⟩⟩
  · -- −x near [−hv, −lv], positive; its reading [−hi, −li]
    have hp : qlt qzero (qneg hv) := by
      obtain ⟨h0, h1⟩ := qlt_iff_le_not_le.mp hn
      exact qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => h1 (by rat_linarith)⟩
    have a' : qle (qmul (qneg hi) (qneg lv)) qone := by
      have : qEq (qmul (qneg hi) (qneg lv)) (qmul hi lv) := by rat_ring
      rat_linarith
    have b' : qle qone (qmul (qneg li) (qneg hv)) := by
      have : qEq (qmul (qneg li) (qneg hv)) (qmul li hv) := by rat_ring
      rat_linarith
    obtain ⟨J, hJ⟩ := recip_near_pos (by rat_linarith : qle (qneg hv) (qneg lv)) hp a' b' k
    refine ⟨J, fun x h1 h2 => ?_⟩
    obtain ⟨p, q, r⟩ := hJ (qneg x) (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith)
    have xne : ¬ qEq x qzero := fun e => ne_zero_of_lt p (by
      have := qneg_respects e; have z : qEq (qneg qzero) qzero := by rat_ring
      exact qle_antisymm (by rat_linarith) (by rat_linarith))
    have ng := qinv'_neg xne
    unfold qsub at *
    exact ⟨xne, by rat_linarith, by rat_linarith⟩

theorem Ev_recip {x : Nat → QExpr} {li hi lv hv : QExpr} (hx : Ev x lv hv) (h : RecipOK li hi lv hv) :
    Ev (fun n => qinv' (x n)) li hi := fun k => by
  obtain ⟨J, hJ⟩ := recip_near h k
  obtain ⟨N, hN⟩ := hx J
  exact ⟨N, fun n hn => by obtain ⟨a, b⟩ := hN n hn; obtain ⟨_, c, d⟩ := hJ (x n) a b; exact ⟨c, d⟩⟩

/-! ## Cauchy sequences of reciprocals -/

def Cauchy (x : Nat → QExpr) : Prop := ∀ k, ∃ N, ∀ m n, N ≤ m → N ≤ n → qclose (x m) (x n) (qeps k)

/-- A positive lower end, certified by `1 ≤ hi·lv`, lies above some `ε_B`. -/
theorem lv_floor {hi lv : QExpr} (hp : qlt qzero lv) (b : qle qone (qmul hi lv)) : ∃ B, qle (qeps B) lv := by
  obtain ⟨B, hB0, _⟩ := qexpr_bound hi
  have hB : qle hi (qofInt (pow2 B)) := by unfold qsub at hB0; rat_linarith
  have lv0 := qle_of_qlt hp
  have f1 := scale_l hB lv0
  have c1 : qEq (qmul lv hi) (qmul hi lv) := qmul_comm _ _
  have f2 := ZExp.scale (by rat_linarith : qle qone (qmul lv (qofInt (pow2 B)))) (qeps_nonneg B)
  have m1 : qEq (qmul (qofInt (pow2 B)) (qeps (0 + B))) (qeps 0) := qpow2_mul_eps B 0
  rw [Nat.zero_add] at m1
  have m2 : qEq (qmul (qmul lv (qofInt (pow2 B))) (qeps B)) (qmul lv (qmul (qofInt (pow2 B)) (qeps B))) := by rat_ring
  have m3 := qmul_respects (qEq_refl lv) m1
  have m4 := qmul_one lv
  have m5 := qone_mul (qeps B)
  have m7 : qEq (qmul lv (qeps 0)) (qmul lv qone) := qmul_respects (qEq_refl lv) qeps_zero
  exact ⟨B, by rat_linarith⟩

/-- Cauchy, clear of zero from some point on (`ε_B ≤ y_n`): the reciprocals are Cauchy. -/
theorem recip_cauchy_pos {y : Nat → QExpr} {B N0 : Nat} (hy : Cauchy y) (hb : ∀ n, N0 ≤ n → qle (qeps B) (y n)) :
    Cauchy (fun n => qinv' (y n)) := fun k => by
  obtain ⟨N, hN⟩ := hy ((k + B) + B)
  refine ⟨N + N0, fun m n hm hn => ?_⟩
  have rc := recip_close (hb m (Nat.le_trans (Nat.le_add_left N0 N) hm)) (hb n (Nat.le_trans (Nat.le_add_left N0 N) hn))
    (hN m n (Nat.le_trans (Nat.le_add_right N N0) hm) (Nat.le_trans (Nat.le_add_right N N0) hn))
  have p1 := qpow2_mul_eps B (k + B)
  have p2 := qpow2_mul_eps B k
  have p3 : qEq (qmul (qeps ((k + B) + B)) (qmul (qofInt (pow2 B)) (qofInt (pow2 B))))
      (qmul (qofInt (pow2 B)) (qmul (qofInt (pow2 B)) (qeps ((k + B) + B)))) := by rat_ring
  have p4 := qmul_respects (qEq_refl (qofInt (pow2 B))) p1
  exact qclose_mono rc (by rat_linarith)

theorem recip_cauchy {y : Nat → QExpr} {li hi lv hv : QExpr} (hy : Cauchy y) (hev : Ev y lv hv)
    (h : RecipOK li hi lv hv) : Cauchy (fun n => qinv' (y n)) := by
  obtain ⟨hlh, ⟨hp, a, b⟩ | ⟨hn, a, b⟩⟩ := h
  · obtain ⟨B, hB⟩ := lv_floor hp b
    obtain ⟨N0, hN0⟩ := hev (B + 1)
    refine recip_cauchy_pos (B := B + 1) (N0 := N0) hy (fun n hn => ?_)
    obtain ⟨c, _⟩ := hN0 n hn
    have := qeps_succ_add B
    unfold qsub at c; rat_linarith
  · -- through −y
    have hp' : qlt qzero (qneg hv) := by
      obtain ⟨h0, h1⟩ := qlt_iff_le_not_le.mp hn
      exact qlt_iff_le_not_le.mpr ⟨by rat_linarith, fun h => h1 (by rat_linarith)⟩
    have b' : qle qone (qmul (qneg li) (qneg hv)) := by
      have : qEq (qmul (qneg li) (qneg hv)) (qmul li hv) := by rat_ring
      rat_linarith
    obtain ⟨B, hB⟩ := lv_floor hp' b'
    obtain ⟨N0, hN0⟩ := hev (B + 1)
    have hneg : Cauchy (fun n => qneg (y n)) := fun k => by
      obtain ⟨N, hN⟩ := hy k
      exact ⟨N, fun m n hm hn => by
        obtain ⟨c1, c2⟩ := hN m n hm hn
        show qclose (qneg (y m)) (qneg (y n)) (qeps k)
        constructor <;> (unfold qsub at *; rat_linarith)⟩
    have fl : ∀ n, N0 ≤ n → qle (qeps (B + 1)) (qneg (y n)) := fun n hn => by
      obtain ⟨_, c⟩ := hN0 n hn
      have := qeps_succ_add B
      rat_linarith
    have rc := recip_cauchy_pos hneg fl
    intro k
    obtain ⟨N, hN⟩ := rc k
    refine ⟨N + N0, fun m n hm hn => ?_⟩
    have ym : ¬ qEq (y m) qzero := fun e => by
      have := fl m (Nat.le_trans (Nat.le_add_left N0 N) hm); have := qeps_pos (B + 1)
      have := qneg_respects e; have z : qEq (qneg qzero) qzero := by rat_ring
      exact (qlt_iff_le_not_le.mp (qeps_pos (B + 1))).2 (by rat_linarith)
    have yn : ¬ qEq (y n) qzero := fun e => by
      have := fl n (Nat.le_trans (Nat.le_add_left N0 N) hn)
      have := qneg_respects e; have z : qEq (qneg qzero) qzero := by rat_ring
      exact (qlt_iff_le_not_le.mp (qeps_pos (B + 1))).2 (by rat_linarith)
    have g1 := qinv'_neg ym
    have g2 := qinv'_neg yn
    obtain ⟨c1, c2⟩ := hN m n (Nat.le_trans (Nat.le_add_right N N0) hm) (Nat.le_trans (Nat.le_add_right N N0) hn)
    constructor <;> (unfold qsub at *; rat_linarith)

end ZRecip

#print axioms ZRecip.inv_unique
#print axioms ZRecip.qinv'_neg
#print axioms ZRecip.qinv'_mul
#print axioms ZRecip.recip_close
#print axioms ZRecip.recip_exact
#print axioms ZRecip.clamp_facts
#print axioms ZRecip.recip_near_pos
#print axioms ZRecip.recip_near
#print axioms ZRecip.Ev_recip
#print axioms ZRecip.recip_cauchy
