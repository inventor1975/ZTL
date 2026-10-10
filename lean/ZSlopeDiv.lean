import ZSlopeExp

/-!
# ZSlopeDiv — division in the kernel's certificate rule, with `exp`, on VR's operational reals. Zero axioms.

The grammar `+ − × / exp`. The kernel reads a quotient's value as `U × [1/V]` (`V` clear of zero — `RecipOK`,
division-free) and its derivative by the quotient rule `(Du·V − U·Dv) / (V·V)`, reading `V·V` as an independent
product. That is exactly what bounds the exact difference
    `u'/v' − u/v = (Δu·v − u·Δv) · (1/v)(1/v')`        (`quot_diff`)
with `v·v'` a product of two points of `V`. So `slope_sound` needs no intermediate point here either.

Values are sequences of rationals (`evalN`); near `V` the reciprocal is near its reading (`recip_near`, a clamp
into `V` and the Lipschitz bound of `1/x` away from zero). A quotient's value is an operational real only where
its denominator is clear of zero — so the value is built from a value reading covering the point (`valR`,
`evalN_cauchy`), and `certificate_sound` speaks of the approximants (`SLe`, `rle`'s own shape);
`certificate_sound_R` is the real order wherever a value reading covers the point.
-/

namespace ZSlopeDiv

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

/-! ## The grammar with `/` and `exp` -/

theorem Ev_congr_ev {x y : Nat → QExpr} {l h : QExpr} (N0 : Nat) (e : ∀ n, N0 ≤ n → qEq (x n) (y n))
    (hx : Ev x l h) : Ev y l h := fun k => by
  obtain ⟨N, hN⟩ := hx k
  refine ⟨N + N0, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n (Nat.le_trans (Nat.le_add_right N N0) hn)
  have := e n (Nat.le_trans (Nat.le_add_left N0 N) hn)
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- Corners scaled by `d ≥ 0` in the FIRST factor. -/
theorem corners_scale_left {m M a1 a2 b1 b2 d : QExpr} (hc : Corners m M a1 a2 b1 b2) (hd : qle qzero d) :
    Corners (qmul m d) (qmul M d) (qmul a1 d) (qmul a2 d) b1 b2 := by
  obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hc
  have r : ∀ x y : QExpr, qEq (qmul (qmul x y) d) (qmul (qmul x d) y) := fun x y => by rat_ring
  exact ⟨⟨qle_respects (qEq_refl _) (r _ _) (ZExp.scale l11 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l12 hd),
          qle_respects (qEq_refl _) (r _ _) (ZExp.scale l21 hd), qle_respects (qEq_refl _) (r _ _) (ZExp.scale l22 hd)⟩,
         ⟨qle_respects (r _ _) (qEq_refl _) (ZExp.scale h11 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h12 hd),
          qle_respects (r _ _) (qEq_refl _) (ZExp.scale h21 hd), qle_respects (r _ _) (qEq_refl _) (ZExp.scale h22 hd)⟩⟩

inductive G where
  | const : QExpr → G
  | var   : Nat → G
  | add   : G → G → G
  | sub   : G → G → G
  | mul   : G → G → G
  | div   : G → G → G
  | exp   : G → G

def evalN (n : Nat) (p : Point QExpr) : G → QExpr
  | .const c => c
  | .var i => p i
  | .add u v => qadd (evalN n p u) (evalN n p v)
  | .sub u v => qsub (evalN n p u) (evalN n p v)
  | .mul u v => qmul (evalN n p u) (evalN n p v)
  | .div u v => qmul (evalN n p u) (qinv' (evalN n p v))
  | .exp u => eseq (evalN n p u) n

/-- The kernel's value reading: a quotient is `U × [1/V]`, `V` clear of zero (`RecipOK`). -/
inductive VRead (B : Box QExpr) : G → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l c → qle c h → VRead B (.const c) l h
  | var {i : Nat} {l h : QExpr} : qle l (B i).1 → qle (B i).2 h → VRead B (.var i) l h
  | add {u v : G} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → VRead B (.add u v) l h
  | sub {u v : G} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → VRead B (.sub u v) l h
  | mul {u v : G} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      Corners l h l1 h1 l2 h2 → VRead B (.mul u v) l h
  | div {u v : G} {lu hu lv hv li hi l h : QExpr} : VRead B u lu hu → VRead B v lv hv →
      RecipOK li hi lv hv → Corners l h lu hu li hi → VRead B (.div u v) l h
  | exp {u : G} {lu hu El Eh : QExpr} : VRead B u lu hu →
      (∃ z, ExpCert lu El z) → (∃ z, ExpCert hu z Eh) → VRead B (.exp u) El Eh

theorem value_sound {B : Box QExpr} {p : Point QExpr} (hp : InBox qOrd B p) :
    ∀ {e : G} {l h : QExpr}, VRead B e l h → Ev (fun n => evalN n p e) l h := by
  intro e l h r
  induction r with
  | const h1 h2 => exact Ev_of_exact 0 (fun _ _ => ⟨h1, h2⟩)
  | var h1 h2 => exact Ev_of_exact 0 (fun _ _ => ⟨qle_trans h1 (hp _).1, qle_trans (hp _).2 h2⟩)
  | add _ _ hl hh ih1 ih2 => exact Ev_widen (Ev_add ih1 ih2) hl hh
  | sub _ _ hl hh ih1 ih2 => exact Ev_widen (Ev_sub ih1 ih2) hl hh
  | mul _ _ hc ih1 ih2 => exact Ev_mul ih1 ih2 hc
  | div _ _ hR hc ih1 ih2 => exact Ev_mul ih1 (Ev_recip ih2 hR) hc
  | exp _ cl ch ih => exact Ev_exp ih cl ch

/-- The kernel's derivative reading: the quotient rule `(Du·V − U·Dv) / (V·V)`, each product at its corners,
`V·V` read as an independent product (which is what bounds `v(p)·v(p')`). -/
inductive DRead (B : Box QExpr) (i : Nat) : G → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l qzero → qle qzero h → DRead B i (.const c) l h
  | self {l h : QExpr} : qle l qone → qle qone h → DRead B i (.var i) l h
  | other {j : Nat} {l h : QExpr} : j ≠ i → qle l qzero → qle qzero h → DRead B i (.var j) l h
  | add {u v : G} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → DRead B i (.add u v) l h
  | sub {u v : G} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → DRead B i (.sub u v) l h
  | mul {u v : G} {lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h : QExpr} :
      VRead B u lu hu → VRead B v lv hv → DRead B i u du1 du2 → DRead B i v dv1 dv2 →
      Corners m1 M1 lu hu dv1 dv2 → Corners m2 M2 lv hv du1 du2 →
      qle l (qadd m1 m2) → qle (qadd M1 M2) h → DRead B i (.mul u v) l h
  | div {u v : G} {lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 n1 n2 w1 w2 r1 r2 l h : QExpr} :
      VRead B u lu hu → VRead B v lv hv → DRead B i u du1 du2 → DRead B i v dv1 dv2 →
      Corners m1 M1 du1 du2 lv hv → Corners m2 M2 lu hu dv1 dv2 →
      qle n1 (qsub m1 M2) → qle (qsub M1 m2) n2 →
      Corners w1 w2 lv hv lv hv → RecipOK r1 r2 w1 w2 → Corners l h n1 n2 r1 r2 → DRead B i (.div u v) l h
  | exp {u : G} {lu hu El Eh du1 du2 m M l h : QExpr} :
      VRead B u lu hu → (∃ z, ExpCert lu El z) → (∃ z, ExpCert hu z Eh) → DRead B i u du1 du2 →
      Corners m M El Eh du1 du2 → qle l m → qle M h → DRead B i (.exp u) l h

/-- The quotient's difference, exactly: `u'/v' − u/v = (Δu·v − u·Δv)·(1/v)(1/v')`, `v, v' ≠ 0`. -/
theorem quot_diff {u v u' v' : QExpr} (hv : ¬ qEq v qzero) (hv' : ¬ qEq v' qzero) :
    qEq (qsub (qmul u' (qinv' v')) (qmul u (qinv' v)))
      (qmul (qsub (qmul (qsub u' u) v) (qmul u (qsub v' v))) (qinv' (qmul v v'))) := by
  have c := qmul_inv'_cancel hv
  have c' := qmul_inv'_cancel hv'
  have m := qinv'_mul hv hv'
  have e1 : qEq (qmul (qsub (qmul (qsub u' u) v) (qmul u (qsub v' v))) (qmul (qinv' v) (qinv' v')))
      (qsub (qmul (qmul u' (qmul v (qinv' v))) (qinv' v')) (qmul (qmul u (qmul v' (qinv' v'))) (qinv' v))) := by
    unfold qsub; rat_ring
  have e2 := qmul_respects (qmul_respects (qEq_refl u') c) (qEq_refl (qinv' v'))
  have e3 := qmul_respects (qmul_respects (qEq_refl u) c') (qEq_refl (qinv' v))
  have e4 : qEq (qmul (qmul u' qone) (qinv' v')) (qmul u' (qinv' v')) := by rat_ring
  have e5 : qEq (qmul (qmul u qone) (qinv' v)) (qmul u (qinv' v)) := by rat_ring
  have e6 := qmul_respects (qEq_refl (qsub (qmul (qsub u' u) v) (qmul u (qsub v' v)))) m
  unfold qsub at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem slope_sound {B : Box QExpr} {i : Nat} {p p' : Point QExpr} (hp : InBox qOrd B p)
    (hp' : InBox qOrd B p') (hfix : ∀ j, j ≠ i → p' j = p j) (hd : qle qzero (qsub (p' i) (p i))) :
    ∀ {e : G} {l h : QExpr}, DRead B i e l h →
      Ev (fun n => qsub (evalN n p' e) (evalN n p e)) (qmul l (qsub (p' i) (p i))) (qmul h (qsub (p' i) (p i))) := by
  intro e l h r
  induction r with
  | @const c l h hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub c c) qzero := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub c c); rat_linarith, by show qle (qsub c c) _; rat_linarith⟩)
  | @self l h hl hh =>
      have f1 : qle qzero (qmul (qsub qone l) (qsub (p' i) (p i))) := qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e1 : qEq (qmul (qsub qone l) (qsub (p' i) (p i)))
          (qadd (qsub (p' i) (p i)) (qneg (qmul l (qsub (p' i) (p i))))) := by unfold qsub; rat_ring
      have f2 : qle qzero (qmul (qsub h qone) (qsub (p' i) (p i))) := qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e2 : qEq (qmul (qsub h qone) (qsub (p' i) (p i)))
          (qadd (qmul h (qsub (p' i) (p i))) (qneg (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => ⟨by show qle _ (qsub (p' i) (p i)); rat_linarith,
                                       by show qle (qsub (p' i) (p i)) _; rat_linarith⟩)
  | @other j l h hj hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub (p j) (p j)) qzero := by unfold qsub; rat_ring
      exact Ev_of_exact 0 (fun n _ => by
        show qle _ (qsub (p' j) (p j)) ∧ qle (qsub (p' j) (p j)) _
        rw [hfix j hj]; exact ⟨by rat_linarith, by rat_linarith⟩)
  | @add u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd l1 l2) (qsub (p' i) (p i)))
          (qadd (qmul l1 (qsub (p' i) (p i))) (qmul l2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd h1 h2) (qsub (p' i) (p i)))
          (qadd (qmul h1 (qsub (p' i) (p i))) (qmul h2 (qsub (p' i) (p i)))) := by rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_add ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qadd (evalN n p' u) (evalN n p' v)) (qadd (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @sub u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qsub l1 h2) (qsub (p' i) (p i)))
          (qsub (qmul l1 (qsub (p' i) (p i))) (qmul h2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      have r2 : qEq (qmul (qsub h1 l2) (qsub (p' i) (p i)))
          (qsub (qmul h1 (qsub (p' i) (p i))) (qmul l2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_sub ih1 ih2)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qsub (evalN n p' u) (evalN n p' v)) (qsub (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @mul u v lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h ru rv _ _ c1 c2 hl hh ih1 ih2 =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      have r1 : qEq (qmul (qadd m1 m2) (qsub (p' i) (p i)))
          (qadd (qmul m1 (qsub (p' i) (p i))) (qmul m2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd M1 M2) (qsub (p' i) (p i)))
          (qadd (qmul M1 (qsub (p' i) (p i))) (qmul M2 (qsub (p' i) (p i)))) := by rat_ring
      have A := Ev_mul (value_sound hp' ru) ih2 (corners_scale c1 hd)
      have Bv := Ev_mul (value_sound hp rv) ih1 (corners_scale c2 hd)
      refine Ev_widen (Ev_congr (fun n => ?_) (Ev_add A Bv)) (by rat_linarith) (by rat_linarith)
      show qEq _ (qsub (qmul (evalN n p' u) (evalN n p' v)) (qmul (evalN n p u) (evalN n p v)))
      unfold qsub; rat_ring
  | @div u v lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 n1 n2 w1 w2 r1 r2 l h ru rv _ _ c1 c2 hn1 hn2 cw hR cq ih1 ih2 =>
      have d := qsub (p' i) (p i)
      -- numerator Δu·v − u·Δv in [n1·d, n2·d]
      have A := Ev_mul ih1 (value_sound hp rv) (corners_scale_left c1 hd)
      have Bu := Ev_mul (value_sound hp ru) ih2 (corners_scale c2 hd)
      have s1 := ZExp.scale hn1 hd
      have s2 := ZExp.scale hn2 hd
      have t1 : qEq (qmul (qsub m1 M2) (qsub (p' i) (p i)))
          (qsub (qmul m1 (qsub (p' i) (p i))) (qmul M2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      have t2 : qEq (qmul (qsub M1 m2) (qsub (p' i) (p i)))
          (qsub (qmul M1 (qsub (p' i) (p i))) (qmul m2 (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      have Num := Ev_widen (Ev_sub A Bu) (l' := qmul n1 (qsub (p' i) (p i))) (h' := qmul n2 (qsub (p' i) (p i)))
        (by rat_linarith) (by rat_linarith)
      -- the denominator's reciprocal 1/(v·v') in [r1, r2]
      have W := Ev_mul (value_sound hp rv) (value_sound hp' rv) cw
      have Wr := Ev_recip W hR
      have Q := Ev_mul Num Wr (corners_scale_left cq hd)
      -- eventually v, v' ≠ 0 (their product is near W, clear of zero): the exact identity
      obtain ⟨J, hJ⟩ := recip_near hR 0
      obtain ⟨N, hN⟩ := W J
      refine Ev_congr_ev N (fun n hn => ?_) Q
      obtain ⟨a, b⟩ := hN n hn
      obtain ⟨hz, _, _⟩ := hJ _ a b
      have hz' : ¬ qEq (qmul (evalN n p v) (evalN n p' v)) qzero := hz
      have nv : ¬ qEq (evalN n p v) qzero := fun e => hz' (by
        have := qmul_respects e (qEq_refl (evalN n p' v)); have z := qzero_mul (evalN n p' v)
        exact qle_antisymm (by rat_linarith) (by rat_linarith))
      have nv' : ¬ qEq (evalN n p' v) qzero := fun e => hz' (by
        have := qmul_respects (qEq_refl (evalN n p v)) e; have z := qmul_zero (evalN n p v)
        exact qle_antisymm (by rat_linarith) (by rat_linarith))
      exact qEq_symm (quot_diff (u := evalN n p u) (u' := evalN n p' u) nv nv')
  | @exp u lu hu El Eh du1 du2 m M l h ru cl ch _ hc hl hh ih =>
      have s1 := ZExp.scale hl hd
      have s2 := ZExp.scale hh hd
      exact Ev_widen (Ev_exp_slope (value_sound hp ru) (value_sound hp' ru)
        (Ev_exp (value_sound hp ru) cl ch) (Ev_exp (value_sound hp' ru) cl ch) ih (corners_scale hc hd)) s1 s2

/-! ## The value is an operational real wherever a value reading covers the point -/

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

/-- A value reading over a box makes the value at each of its points an operational real (the denominators are
clear of zero, the `exp` arguments bounded). -/
theorem evalN_cauchy {B : Box QExpr} {p : Point QExpr} (hp : InBox qOrd B p) :
    ∀ {e : G} {l h : QExpr}, VRead B e l h → Cauchy (fun n => evalN n p e) := by
  intro e l h r
  induction r with
  | const _ _ => exact fun k => ⟨0, fun _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩
  | var _ _ => exact fun k => ⟨0, fun _ _ _ _ => qclose_refl _ _ (qeps_nonneg k)⟩
  | add _ _ _ _ ih1 ih2 => exact (radd ⟨_, ih1⟩ ⟨_, ih2⟩).cauchy
  | sub _ _ _ _ ih1 ih2 => exact (radd ⟨_, ih1⟩ (rneg ⟨_, ih2⟩)).cauchy
  | mul _ _ _ ih1 ih2 => exact (rmul ⟨_, ih1⟩ ⟨_, ih2⟩).cauchy
  | div _ rv hR _ ih1 ih2 => exact (rmul ⟨_, ih1⟩ ⟨_, recip_cauchy ih2 (value_sound hp rv) hR⟩).cauchy
  | exp _ _ _ ih => exact rexpR_cauchy ⟨_, ih⟩

/-- The value at `p`, given a value reading over a box containing `p`. -/
def valR {B : Box QExpr} {p : Point QExpr} {e : G} {l h : QExpr} (hp : InBox qOrd B p) (r : VRead B e l h) : RExpr :=
  ⟨fun n => evalN n p e, evalN_cauchy hp r⟩

/-! ## Monotone, and the certificate rule -/

/-- `x ≤ y` for sequences, to every precision from some index on — `rle`'s own shape. -/
def SLe (x y : Nat → QExpr) : Prop := ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub (x n) (y n)) (qeps k)

theorem SLe_refl (x : Nat → QExpr) : SLe x x := fun k => ⟨0, fun n _ => by
  have := qeps_nonneg k; unfold qsub; have := qadd_neg (x n); rat_linarith⟩

theorem SLe_trans {x y z : Nat → QExpr} (h1 : SLe x y) (h2 : SLe y z) : SLe x z := fun k => by
  obtain ⟨N1, a⟩ := h1 (k + 1)
  obtain ⟨N2, b⟩ := h2 (k + 1)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have u := a n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  have v := b n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
  have := qeps_succ_add k
  unfold qsub at *; rat_linarith

theorem mono_up {B : Box QExpr} {i : Nat} {e : G} {l h : QExpr} (r : DRead B i e l h) (hl : qle qzero l) :
    ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun n => evalN n (upd p i (endOf B true i)) e) := by
  intro p hp k
  have hp' := upd_end_inbox qOrd i true hp
  have hu : upd p i (endOf B true i) i = (B i).2 := upd_self p i _
  have hd : qle qzero (qsub (upd p i (endOf B true i) i) (p i)) := by
    have h2 : qle (p i) (B i).2 := (hp i).2
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨N, hN⟩ := slope_sound hp hp' (upd_other p i _) hd r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s0, _⟩ := hN n hn
  have s : qle (qsub (qmul l (qsub (upd p i (endOf B true i) i) (p i))) (qeps k))
      (qsub (evalN n (upd p i (endOf B true i)) e) (evalN n p e)) := s0
  have f := qmul_nonneg hl hd
  show qle (qsub (evalN n p e) (evalN n (upd p i (endOf B true i)) e)) (qeps k)
  unfold qsub at *
  rat_linarith

theorem mono_down {B : Box QExpr} {i : Nat} {e : G} {l h : QExpr} (r : DRead B i e l h) (hh : qle h qzero) :
    ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun n => evalN n (upd p i (endOf B false i)) e) := by
  intro p hp k
  have hp' := upd_end_inbox qOrd i false hp
  have hu : upd p i (endOf B false i) i = (B i).1 := upd_self p i _
  have hfix : ∀ j, j ≠ i → p j = upd p i (endOf B false i) j := fun j hj => (upd_other p i _ j hj).symm
  have hd : qle qzero (qsub (p i) (upd p i (endOf B false i) i)) := by
    have h1 : qle (B i).1 (p i) := (hp i).1
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨N, hN⟩ := slope_sound hp' hp hfix hd r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, s0⟩ := hN n hn
  have s : qle (qsub (evalN n p e) (evalN n (upd p i (endOf B false i)) e))
      (qadd (qmul h (qsub (p i) (upd p i (endOf B false i) i))) (qeps k)) := s0
  have f : qle qzero (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i))) := qmul_nonneg (by rat_linarith) hd
  have e1 : qEq (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i)))
      (qneg (qmul h (qsub (p i) (upd p i (endOf B false i) i)))) := by rat_ring
  show qle (qsub (evalN n p e) (evalN n (upd p i (endOf B false i)) e)) (qeps k)
  unfold qsub at *
  rat_linarith

def Uses : G → Nat → Prop
  | .const _, _ => False
  | .var i, j => j = i
  | .add u v, j => Uses u j ∨ Uses v j
  | .sub u v, j => Uses u j ∨ Uses v j
  | .mul u v, j => Uses u j ∨ Uses v j
  | .div u v, j => Uses u j ∨ Uses v j
  | .exp u, j => Uses u j

theorem evalN_dep (n : Nat) (p q : Point QExpr) : ∀ e : G, (∀ j, Uses e j → p j = q j) → evalN n p e = evalN n q e
  | .const _, _ => rfl
  | .var i, h => h i rfl
  | .add u v, h => by
      show qadd _ _ = qadd _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .sub u v, h => by
      show qsub _ _ = qsub _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .mul u v, h => by
      show qmul _ _ = qmul _ _
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .div u v, h => by
      show qmul _ (qinv' _) = qmul _ (qinv' _)
      rw [evalN_dep n p q u (fun j hj => h j (Or.inl hj)), evalN_dep n p q v (fun j hj => h j (Or.inr hj))]
  | .exp u, h => by
      show eseq _ n = eseq _ n
      rw [evalN_dep n p q u h]

theorem corner_bound_S (e : G) (B : Box QExpr) (sg : Nat → Bool) :
    ∀ (ns : List Nat), (∀ i, List.Mem i ns → ∀ p, InBox qOrd B p →
        SLe (fun n => evalN n p e) (fun n => evalN n (upd p i (endOf B (sg i) i)) e)) →
      ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun n => evalN n (cornerOn B sg ns p) e) := by
  intro ns
  induction ns with
  | nil => intro _ p _; exact SLe_refl _
  | cons i ns ih =>
      intro hm p hp
      exact SLe_trans (hm i (List.Mem.head ns) p hp)
        (ih (fun j hj => hm j (List.Mem.tail i hj)) _ (upd_end_inbox qOrd i (sg i) hp))

def IvOK (e : G) (c : QExpr) (B : Box QExpr) : Prop := ∃ l h, VRead B e l h ∧ qle h c

def DerivOK (e : G) (B : Box QExpr) (i : Nat) : Bool → Prop
  | true => ∃ l h, DRead B i e l h ∧ qle qzero l
  | false => ∃ l h, DRead B i e l h ∧ qle h qzero

def LeafOK (e : G) (ns : List Nat) (c : QExpr) : Box QExpr → Leaf → Prop
  | B, .interval => IvOK e c B
  | B, .monotone sg => (∀ i, List.Mem i ns → DerivOK e B i (sg i)) ∧ IvOK e c (cornerBox B sg)

theorem iv_le {B : Box QExpr} {e : G} {c : QExpr} (h : IvOK e c B) :
    ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun _ => c) := by
  intro p hp k
  obtain ⟨l, h', r, hc⟩ := h
  obtain ⟨N, hN⟩ := value_sound hp r k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨_, b⟩ := hN n hn
  show qle (qsub (evalN n p e) c) (qeps k)
  unfold qsub; rat_linarith

/-- THE CERTIFICATE RULE IS SOUND FOR `+ − × / exp`, premise-free, on VR's operational reals: an accepted
certificate shows that at every point of the box the value's approximants are eventually below `c` to every
precision; wherever a value reading covers the point (`valR`), that is `rle` of an operational real
(`certificate_sound_R`). -/
theorem certificate_sound (e : G) (ns : List Nat) (c : QExpr) (hns : ∀ j, Uses e j → List.Mem j ns) :
    ∀ (t : Tree QExpr Leaf) (B : Box QExpr), Accepts (LeafOK e ns c) B t →
      ∀ p, InBox qOrd B p → SLe (fun n => evalN n p e) (fun _ => c) := by
  apply accepts_sound qOrd (LeafOK e ns c) (fun p => SLe (fun n => evalN n p e) (fun _ => c))
  intro B lf hok p hp
  cases lf with
  | interval => exact iv_le hok p hp
  | monotone sg =>
      obtain ⟨hd, hcorner⟩ := hok
      have step := corner_bound_S e B sg ns (fun i hi => by
        have := hd i hi
        cases hs : sg i with
        | true => rw [hs] at this; obtain ⟨_, _, r, hl⟩ := this; rw [← hs]; exact hs ▸ mono_up r hl
        | false => rw [hs] at this; obtain ⟨_, _, r, hh⟩ := this; rw [← hs]; exact hs ▸ mono_down r hh) p hp
      have same : SLe (fun n => evalN n (cornerOn B sg ns p) e) (fun n => evalN n (corner B sg) e) := by
        intro k; refine ⟨0, fun n _ => ?_⟩
        show qle (qsub (evalN n (cornerOn B sg ns p) e) (evalN n (corner B sg) e)) (qeps k)
        rw [evalN_dep n _ _ e (fun j hj => cornerOn_agrees B sg ns p j (hns j hj))]
        have := qeps_nonneg k; unfold qsub; have := qadd_neg (evalN n (corner B sg) e); rat_linarith
      have atc : InBox qOrd (cornerBox B sg) (corner B sg) := fun j => ⟨qle_refl _, qle_refl _⟩
      exact SLe_trans step (SLe_trans same (iv_le hcorner _ atc))

/-- The same as the real order, at a point some value reading covers. -/
theorem certificate_sound_R (e : G) (ns : List Nat) (c : QExpr) (hns : ∀ j, Uses e j → List.Mem j ns)
    (t : Tree QExpr Leaf) (B : Box QExpr) (hacc : Accepts (LeafOK e ns c) B t) (p : Point QExpr)
    (hp : InBox qOrd B p) {B' : Box QExpr} {l h : QExpr} (hp' : InBox qOrd B' p) (r : VRead B' e l h) :
    rle (valR hp' r) (rofQ c) :=
  certificate_sound e ns c hns t B hacc p hp

/-- Nonvacuity: `1/x` on `[1, 2]` falls. The kernel's quotient reading: `Du·V = [0, 0]`, `U·Dv = [1, 1]`,
numerator `[−1, −1]`, `V·V = [1, 4]`, its reciprocal read `[0, 1]`, the derivative `[−1, 0]` — non-positive. -/
example : ∀ p, InBox qOrd (fun _ => (qone, qnat 2)) p →
    SLe (fun n => evalN n p (.div (.const qone) (.var 0)))
        (fun n => evalN n (upd p 0 (endOf (fun _ => (qone, qnat 2)) false 0)) (.div (.const qone) (.var 0))) :=
  mono_down (l := qneg qone) (h := qzero)
    (DRead.div (lu := qone) (hu := qone) (lv := qone) (hv := qnat 2) (du1 := qzero) (du2 := qzero)
      (dv1 := qone) (dv2 := qone) (m1 := qzero) (M1 := qzero) (m2 := qone) (M2 := qone)
      (n1 := qneg qone) (n2 := qneg qone) (w1 := qone) (w2 := qnat 4) (r1 := qzero) (r2 := qone)
      (VRead.const (by decide) (by decide)) (VRead.var (by decide) (by decide))
      (DRead.const (by decide) (by decide)) (DRead.self (by decide) (by decide))
      (by unfold Corners; decide) (by unfold Corners; decide) (by decide) (by decide)
      (by unfold Corners; decide) (by unfold RecipOK; decide) (by unfold Corners; decide))
    (by decide)

end ZSlopeDiv

#print axioms ZSlopeDiv.inv_unique
#print axioms ZSlopeDiv.qinv'_neg
#print axioms ZSlopeDiv.qinv'_mul
#print axioms ZSlopeDiv.recip_close
#print axioms ZSlopeDiv.recip_exact
#print axioms ZSlopeDiv.clamp_facts
#print axioms ZSlopeDiv.recip_near_pos
#print axioms ZSlopeDiv.recip_near
#print axioms ZSlopeDiv.Ev_recip
#print axioms ZSlopeDiv.value_sound
#print axioms ZSlopeDiv.quot_diff
#print axioms ZSlopeDiv.slope_sound
#print axioms ZSlopeDiv.recip_cauchy
#print axioms ZSlopeDiv.evalN_cauchy
#print axioms ZSlopeDiv.mono_up
#print axioms ZSlopeDiv.mono_down
#print axioms ZSlopeDiv.certificate_sound
#print axioms ZSlopeDiv.certificate_sound_R
