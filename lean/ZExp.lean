import VR.Numbers.RealsOp

/-!
# ZExp — `exp` on VR's operational reals, its brackets, its slopes. Zero axioms.

The curator, 2026-10-10: "без аксиом … на континууме как в VR", then "сделай и А, и Б".

(A) `rexp x`, `x` a pre-rational: the series `S_n(x) = Σ_{k<n} x^k/k!` for `x ≥ 0` — Cauchy with an explicit
modulus (past `2x ≤ n + 1` each term halves, so the tail is at most `2·t_n`, and `t_n` decays geometrically) —
and `1/S_n(−x)` below zero (the inverse is 1-Lipschitz on `[1, ∞)`). The sign of a pre-rational is decidable,
so this is a definition, not a choice. `bracket_sound`: a rational `[lo, hi]` passing `ExpCert` — an index, the
partial sum and its tail bound — contains `exp x`. `zexpcert.py` applies the same rule to the kernel's brackets.

(B) No functional equation `e^{a+b} = e^a e^b` is needed. The partial sums have EXACT slopes term by term
(`tm_slope`: `b^{k+1} − a^{k+1}` between `(k+1)(b−a)a^k` and `(k+1)(b−a)b^k`), and for any signs
`E_slope`: `(b − a)(E(a) − t_n(R)) ≤ E(b) − E(a) ≤ (b − a)·E(b)` at every index, the error uniform on `[−R, R]`
(negative arguments through the inverse, mixed signs cut at `0` where `E = 1`). From it: monotone (`E_mono`),
uniformly convergent (`E_unif`), Lipschitz (`E_lip`), hence `rexpR`: `exp` of an operational REAL.
`ZSlopeExp` puts `exp` into the kernel's certificate rule.
-/

namespace ZExp

open VR VR.Numbers

/-- The natural number `n` as a pre-rational. -/
def qnat (n : Nat) : QExpr := qofInt (IntExpr.mk (O n) VRObj.base)

theorem qnat_zero : qEq (qnat 0) qzero := qEq_refl _

theorem qnat_succ (n : Nat) : qEq (qnat (n + 1)) (qadd (qnat n) qone) := by
  have h : IntExpr.mk (O (n + 1)) VRObj.base ≈ᵢ iadd (IntExpr.mk (O n) VRObj.base) oneI := by
    change vadd (VRObj.succ (O n)) (vadd VRObj.base VRObj.base) =
      vadd VRObj.base (vadd (O n) (VRObj.succ VRObj.base))
    vr_ring
  exact qEq_trans (qofInt_respects h) (qofInt_add _ _)

theorem qnat_nonneg : ∀ n : Nat, qle qzero (qnat n)
  | 0 => qle_refl _
  | n + 1 => by
      have h1 := qnat_succ n
      have h2 := qnat_nonneg n
      have h3 := qle_of_qlt qone_pos
      rat_linarith

theorem qnat_succ_pos (n : Nat) : qlt qzero (qnat (n + 1)) := by
  have h1 := qnat_succ n
  have h2 := qnat_nonneg n
  exact qlt_respects (qEq_refl _) (qEq_symm h1)
    (by have := qadd_pos_of_pos_of_nonneg qone_pos h2
        exact qlt_respects (qEq_refl _) (qadd_comm _ _) this)

/-- Every pre-rational is below some natural number, in absolute value. -/
theorem exists_nat_bound (x : QExpr) : ∃ K : Nat, qclose x qzero (qnat K) := by
  obtain ⟨B, hB⟩ := qexpr_bound x
  refine ⟨O_inv (vpow2 B), ?_⟩
  have : qnat (O_inv (vpow2 B)) = qofInt (pow2 B) := by
    unfold qnat pow2; rw [O_right_inv]
  rw [this]; exact hB

/-- `x ≤ y`, `d ≥ 0` give `x·d ≤ y·d`. -/
theorem scale {x y d : QExpr} (h : qle x y) (hd : qle qzero d) : qle (qmul x d) (qmul y d) := by
  have f : qle qzero (qmul (qsub y x) d) := qmul_nonneg (by unfold qsub; rat_linarith) hd
  have e : qEq (qmul (qsub y x) d) (qadd (qmul y d) (qneg (qmul x d))) := by unfold qsub; rat_ring
  rat_linarith

/-- `y ≤ z`, `c ≥ 0` give `c·y ≤ c·z`. -/
theorem scale_l {y z c : QExpr} (h : qle y z) (hc : qle qzero c) : qle (qmul c y) (qmul c z) := by
  have f : qle qzero (qmul c (qsub z y)) := qmul_nonneg hc (by unfold qsub; rat_linarith)
  have e : qEq (qmul c (qsub z y)) (qadd (qmul c z) (qneg (qmul c y))) := by unfold qsub; rat_ring
  rat_linarith

theorem qnat_mono : ∀ {m n : Nat}, m ≤ n → qle (qnat m) (qnat n)
  | m, n, h => by
      induction h with
      | refl => exact qle_refl _
      | step _ ih =>
          rename_i k _
          have h1 := qnat_succ k
          have h3 := qle_of_qlt qone_pos
          rat_linarith

theorem qnat_ne_zero (n : Nat) : ¬ qEq (qnat (n + 1)) qzero := fun h =>
  qlt_irrefl _ (qlt_respects (qEq_refl _) h (qnat_succ_pos n))

/-- `c > 0` and `c·y ≤ 0` give `y ≤ 0`. -/
theorem nonpos_of_mul {c y : QExpr} (hc : qlt qzero c) (h : qle (qmul c y) qzero) : qle y qzero := by
  have hne : ¬ qEq c qzero := fun e => qlt_irrefl _ (qlt_respects (qEq_refl _) e hc)
  have hi := qinv'_nonneg_of_pos hc
  have hcan := qmul_inv'_cancel hne
  have f : qle qzero (qmul (qinv' c) (qneg (qmul c y))) := qmul_nonneg hi (by rat_linarith)
  have e1 : qEq (qmul (qinv' c) (qneg (qmul c y))) (qneg (qmul (qmul c (qinv' c)) y)) := by rat_ring
  have e2 : qEq (qmul (qmul c (qinv' c)) y) (qmul qone y) := qmul_respects hcan (qEq_refl _)
  have e3 := qone_mul y
  rat_linarith

/-! ## The series: terms `x^k / k!`, partial sums -/

def tm (x : QExpr) : Nat → QExpr
  | 0 => qone
  | k + 1 => qmul (qmul (tm x k) x) (qinv' (qnat (k + 1)))

/-- `S x n = Σ_{k<n} x^k/k!`. -/
def S (x : QExpr) : Nat → QExpr
  | 0 => qzero
  | n + 1 => qadd (S x n) (tm x n)

theorem tm_succ (x : QExpr) (k : Nat) : qEq (qmul (qnat (k + 1)) (tm x (k + 1))) (qmul (tm x k) x) := by
  have hc := qmul_inv'_cancel (qnat_ne_zero k)
  have e : qEq (qmul (qnat (k + 1)) (qmul (qmul (tm x k) x) (qinv' (qnat (k + 1)))))
      (qmul (qmul (tm x k) x) (qmul (qnat (k + 1)) (qinv' (qnat (k + 1))))) := by rat_ring
  exact qEq_trans e (qEq_trans (qmul_respects (qEq_refl _) hc) (qmul_one _))

theorem tm_nonneg {x : QExpr} (hx : qle qzero x) : ∀ k, qle qzero (tm x k)
  | 0 => qle_of_qlt qone_pos
  | k + 1 => qmul_nonneg (qmul_nonneg (tm_nonneg hx k) hx) (qinv'_nonneg_of_pos (qnat_succ_pos k))

theorem S_mono {x : QExpr} (hx : qle qzero x) (n : Nat) : ∀ j, qle (S x n) (S x (n + j))
  | 0 => qle_refl _
  | j + 1 => by
      have h1 := S_mono hx n j
      have h2 := tm_nonneg hx (n + j)
      show qle (S x n) (qadd (S x (n + j)) (tm x (n + j)))
      rat_linarith

/-- Past `2x ≤ k + 1` each term is at most half the one before. -/
theorem tm_half {x : QExpr} (hx : qle qzero x) {k : Nat} (hk : qle (qadd x x) (qnat (k + 1))) :
    qle (qadd (tm x (k + 1)) (tm x (k + 1))) (tm x k) := by
  have hA := tm_succ x k
  have h0 := tm_nonneg hx k
  have hB : qle qzero (qmul (tm x k) (qsub (qnat (k + 1)) (qadd x x))) :=
    qmul_nonneg h0 (by unfold qsub; rat_linarith)
  have eB : qEq (qmul (tm x k) (qsub (qnat (k + 1)) (qadd x x)))
      (qadd (qmul (tm x k) (qnat (k + 1))) (qneg (qadd (qmul (tm x k) x) (qmul (tm x k) x)))) := by
    unfold qsub; rat_ring
  have eC : qEq (qmul (qnat (k + 1)) (qsub (qadd (tm x (k + 1)) (tm x (k + 1))) (tm x k)))
      (qadd (qadd (qmul (qnat (k + 1)) (tm x (k + 1))) (qmul (qnat (k + 1)) (tm x (k + 1))))
        (qneg (qmul (tm x k) (qnat (k + 1))))) := by unfold qsub; rat_ring
  have hn : qle (qmul (qnat (k + 1)) (qsub (qadd (tm x (k + 1)) (tm x (k + 1))) (tm x k))) qzero := by
    rat_linarith
  have := nonpos_of_mul (qnat_succ_pos k) hn
  unfold qsub at this
  rat_linarith

/-- Good from `K` on: `2x ≤ K + 1`. -/
def Good (x : QExpr) (K : Nat) : Prop := qle (qadd x x) (qnat (K + 1))

theorem good_mono {x : QExpr} {K n : Nat} (h : Good x K) (hn : K ≤ n) : Good x n :=
  qle_trans h (qnat_mono (Nat.succ_le_succ hn))

/-- The tail, telescoped: `S_{n+j} + 2·t_{n+j} ≤ S_n + 2·t_n` once good. -/
theorem tail_tele {x : QExpr} (hx : qle qzero x) {n : Nat} (hg : Good x n) :
    ∀ j, qle (qadd (S x (n + j)) (qadd (tm x (n + j)) (tm x (n + j)))) (qadd (S x n) (qadd (tm x n) (tm x n)))
  | 0 => qle_refl _
  | j + 1 => by
      have ih := tail_tele hx hg j
      have hh := tm_half hx (good_mono hg (Nat.le_add_right n j))
      show qle (qadd (qadd (S x (n + j)) (tm x (n + j))) (qadd (tm x (n + j + 1)) (tm x (n + j + 1)))) _
      rat_linarith

/-- The terms decay geometrically: `2^j · t_{n+j} ≤ t_n` once good. -/
theorem tm_decay {x : QExpr} (hx : qle qzero x) {n : Nat} (hg : Good x n) :
    ∀ j, qle (qmul (qofInt (pow2 j)) (tm x (n + j))) (tm x n)
  | 0 => by
      have e : qEq (qmul (qofInt (pow2 0)) (tm x (n + 0))) (tm x n) := qone_mul _
      exact qle_of_qEq e
  | j + 1 => by
      have ih := tm_decay hx hg j
      have hh := tm_half hx (good_mono hg (Nat.le_add_right n j))
      have hp : qEq (qofInt (pow2 (j + 1))) (qadd (qofInt (pow2 j)) (qofInt (pow2 j))) :=
        qEq_trans (qofInt_respects (pow2_succ j)) (qofInt_add _ _)
      have hs := scale_l hh (qofInt_le (pow2_nonneg j))
      have e : qEq (qmul (qofInt (pow2 (j + 1))) (tm x (n + j + 1)))
          (qmul (qofInt (pow2 j)) (qadd (tm x (n + j + 1)) (tm x (n + j + 1)))) :=
        qEq_trans (qmul_respects hp (qEq_refl _)) (by rat_ring)
      show qle (qmul (qofInt (pow2 (j + 1))) (tm x (n + j + 1))) (tm x n)
      rat_linarith

/-- `m ≤ n` as a witnessed difference (core's `Nat.exists_eq_add_of_le` carries `propext`). -/
theorem le_ex : ∀ {m n : Nat}, m ≤ n → ∃ k, n = m + k
  | _, _, Nat.le.refl => ⟨0, rfl⟩
  | _, _, Nat.le.step h => by
      obtain ⟨k, hk⟩ := le_ex h
      exact ⟨k + 1, by rw [hk]; rfl⟩

theorem qnat_add (a : Nat) : ∀ b, qEq (qnat (a + b)) (qadd (qnat a) (qnat b))
  | 0 => by
      have := qnat_zero
      show qEq (qnat a) (qadd (qnat a) (qnat 0))
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | b + 1 => by
      have ih := qnat_add a b
      have h1 := qnat_succ (a + b)
      have h2 := qnat_succ b
      show qEq (qnat (a + b + 1)) _
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem good_exists (x : QExpr) : ∃ K, Good x K := by
  obtain ⟨K, h1, _⟩ := exists_nat_bound x
  refine ⟨K + K, ?_⟩
  have e := qnat_add K K
  have e1 := qnat_succ (K + K)
  have h3 := qle_of_qlt qone_pos
  unfold Good; unfold qsub at h1
  rat_linarith

/-- Twice a term is eventually below any precision. -/
theorem tm_small {x : QExpr} (hx : qle qzero x) {K : Nat} (hg : Good x K) (k : Nat) :
    ∃ N, K ≤ N ∧ ∀ n, N ≤ n → qle (qadd (tm x n) (tm x n)) (qeps k) := by
  obtain ⟨C, hC, _⟩ := qexpr_bound (tm x K)
  refine ⟨K + ((k + 1) + C), Nat.le_add_right _ _, fun n hn => ?_⟩
  obtain ⟨r, hr⟩ := le_ex hn
  have hj : n = K + (((k + 1) + C) + r) := by rw [hr, Nat.add_assoc]
  rw [hj]
  have hd := tm_decay hx hg (((k + 1) + C) + r)
  have t0 := tm_nonneg hx (K + (((k + 1) + C) + r))
  have he0 : qle qzero (qeps (((k + 1) + C) + r)) := qeps_nonneg _
  have f1 := scale hd he0
  have hC' : qle (tm x K) (qofInt (pow2 C)) := by unfold qsub at hC; rat_linarith
  have f2 := scale hC' he0
  have f3 := scale_l (qeps_le_add ((k + 1) + C) r) (qofInt_le (pow2_nonneg C))
  have e1 : qEq (qmul (qofInt (pow2 (((k + 1) + C) + r))) (qeps (0 + (((k + 1) + C) + r)))) (qeps 0) :=
    qpow2_mul_eps _ 0
  rw [Nat.zero_add] at e1
  have e2 : qEq (qmul (qmul (qofInt (pow2 (((k + 1) + C) + r))) (tm x (K + (((k + 1) + C) + r))))
      (qeps (((k + 1) + C) + r)))
      (qmul (tm x (K + (((k + 1) + C) + r)))
        (qmul (qofInt (pow2 (((k + 1) + C) + r))) (qeps (((k + 1) + C) + r)))) := by rat_ring
  have e3 := qmul_respects (qEq_refl (tm x (K + (((k + 1) + C) + r)))) e1
  have e4 := qmul_one (tm x (K + (((k + 1) + C) + r)))
  have e5 := qpow2_mul_eps C (k + 1)
  have e6 := qeps_succ_add k
  have e7 := qeps_zero
  have e9 : qEq (qmul (tm x (K + (((k + 1) + C) + r))) (qeps 0))
      (qmul (tm x (K + (((k + 1) + C) + r))) qone) := qmul_respects (qEq_refl _) e7
  rat_linarith

/-- The partial sums of a non-negative argument are Cauchy, with the modulus `tm_small` gives. -/
theorem S_cauchy {x : QExpr} (hx : qle qzero x) (k : Nat) :
    ∃ N, ∀ m n, N ≤ m → N ≤ n → qclose (S x m) (S x n) (qeps k) := by
  obtain ⟨K, hg⟩ := good_exists x
  obtain ⟨N, hKN, hN⟩ := tm_small hx hg k
  refine ⟨N, fun m n hm hn => ?_⟩
  have he := qeps_nonneg k
  -- the lower index carries the bound
  have key : ∀ a b, N ≤ a → a ≤ b → qle (S x a) (S x b) ∧ qle (S x b) (qadd (S x a) (qeps k)) := by
    intro a b ha hab
    obtain ⟨j, hj⟩ := le_ex hab
    rw [hj]
    have g := good_mono hg (Nat.le_trans hKN ha)
    have t1 := tail_tele hx g j
    have t2 := tm_nonneg hx (a + j)
    have t3 := hN a ha
    exact ⟨S_mono hx a j, by rat_linarith⟩
  cases Nat.le_total m n with
  | inl h =>
      obtain ⟨k1, k2⟩ := key m n hm h
      constructor <;> (unfold qsub; rat_linarith)
  | inr h =>
      obtain ⟨k1, k2⟩ := key n m hn h
      constructor <;> (unfold qsub; rat_linarith)

/-- `exp x` for `x ≥ 0`: the series, as an operational real. -/
def rexpPos (x : QExpr) (hx : qle qzero x) : RExpr := ⟨S x, S_cauchy hx⟩

/-! ## Negative arguments: `E(x) = 1 / E(−x)` -/

theorem S_ge_one {y : QExpr} (hy : qle qzero y) (n : Nat) : qle qone (S y (n + 1)) := by
  have h := S_mono hy 1 n
  have e : qEq (S y 1) (qadd qzero qone) := qEq_refl _
  have e2 := qzero_add qone
  rw [Nat.add_comm] at h
  rat_linarith

theorem S_ge_one' {y : QExpr} (hy : qle qzero y) {m : Nat} (h : 1 ≤ m) : qle qone (S y m) := by
  obtain ⟨j, rfl⟩ := le_ex h
  have h1 := S_mono hy 1 j
  have e : qEq (S y 1) (qadd qzero qone) := qEq_refl _
  have e2 := qzero_add qone
  rat_linarith

/-- `a ≥ 1`: its inverse lies in `[0, 1]` and cancels it. -/
theorem inv_facts {a : QExpr} (ha : qle qone a) :
    qle qzero (qinv' a) ∧ qle (qinv' a) qone ∧ qEq (qmul a (qinv' a)) qone := by
  have hp : qlt qzero a := by
    have := qone_pos
    exact (qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt this) ha, fun h =>
      (qlt_iff_le_not_le.mp this).2 (qle_trans ha h)⟩)
  have hne : ¬ qEq a qzero := fun e => qlt_irrefl _ (qlt_respects (qEq_refl _) e hp)
  have h0 := qinv'_nonneg_of_pos hp
  have hc := qmul_inv'_cancel hne
  have f := scale ha h0
  have e1 := qone_mul (qinv' a)
  exact ⟨h0, by rat_linarith, hc⟩

/-- On `[1, ∞)` the inverse is 1-Lipschitz: `|1/a − 1/b| ≤ |a − b|`. -/
theorem inv_lip {a b e : QExpr} (ha : qle qone a) (hb : qle qone b) (h : qclose a b e) :
    qclose (qinv' a) (qinv' b) e := by
  obtain ⟨a0, a1, ac⟩ := inv_facts ha
  obtain ⟨b0, b1, bc⟩ := inv_facts hb
  have hp : qclose (qmul (qinv' a) (qinv' b)) qzero qone := by
    have f := scale_l b1 a0
    have f2 := qmul_nonneg a0 b0
    have e := qmul_one (qinv' a)
    constructor <;> (unfold qsub; rat_linarith)
  have hd : qclose (qsub b a) qzero e := by
    obtain ⟨h1, h2⟩ := h
    constructor <;> (unfold qsub at *; rat_linarith)
  have hm := qmul_abs_bound hd hp
  -- (b − a)·(1/a)(1/b) = 1/a − 1/b
  have e1 : qEq (qmul (qsub b a) (qmul (qinv' a) (qinv' b)))
      (qadd (qmul (qmul b (qinv' b)) (qinv' a)) (qneg (qmul (qmul a (qinv' a)) (qinv' b)))) := by
    unfold qsub; rat_ring
  have e2 : qEq (qmul (qmul b (qinv' b)) (qinv' a)) (qmul qone (qinv' a)) := qmul_respects bc (qEq_refl _)
  have e3 : qEq (qmul (qmul a (qinv' a)) (qinv' b)) (qmul qone (qinv' b)) := qmul_respects ac (qEq_refl _)
  have e4 := qone_mul (qinv' a)
  have e5 := qone_mul (qinv' b)
  have e6 := qmul_one e
  obtain ⟨m1, m2⟩ := hm
  constructor <;> (unfold qsub at *; rat_linarith)

/-- The sequence of `exp x`: the series for `x ≥ 0`, the inverse of the series of `−x` below. -/
def eseq (x : QExpr) (n : Nat) : QExpr :=
  match qle.decidable qzero x with
  | .isTrue _ => S x n
  | .isFalse _ => qinv' (S (qneg x) n)

theorem eseq_pos {x : QExpr} (hx : qle qzero x) (n : Nat) : eseq x n = S x n := by
  unfold eseq
  cases qle.decidable qzero x with
  | isTrue _ => rfl
  | isFalse h => exact absurd hx h

theorem eseq_neg {x : QExpr} (hx : ¬ qle qzero x) (n : Nat) : eseq x n = qinv' (S (qneg x) n) := by
  unfold eseq
  cases qle.decidable qzero x with
  | isTrue h => exact absurd h hx
  | isFalse _ => rfl

theorem neg_nonneg_of_not {x : QExpr} (hx : ¬ qle qzero x) : qle qzero (qneg x) := by
  cases qle_total qzero x with
  | inl h => exact absurd h hx
  | inr h => rat_linarith

theorem eseq_cauchy (x : QExpr) (k : Nat) :
    ∃ N, ∀ m n, N ≤ m → N ≤ n → qclose (eseq x m) (eseq x n) (qeps k) := by
  cases qle.decidable qzero x with
  | isTrue hx =>
      obtain ⟨N, hN⟩ := S_cauchy hx k
      exact ⟨N, fun m n hm hn => by rw [eseq_pos hx, eseq_pos hx]; exact hN m n hm hn⟩
  | isFalse hx =>
      have hy := neg_nonneg_of_not hx
      obtain ⟨N, hN⟩ := S_cauchy hy k
      refine ⟨N + 1, fun m n hm hn => ?_⟩
      rw [eseq_neg hx, eseq_neg hx]
      exact inv_lip (S_ge_one' hy (Nat.le_trans (Nat.le_add_left 1 N) hm))
        (S_ge_one' hy (Nat.le_trans (Nat.le_add_left 1 N) hn))
        (hN m n (Nat.le_of_succ_le hm) (Nat.le_of_succ_le hn))

/-- `exp x` of a pre-rational, as an operational real. -/
def rexp (x : QExpr) : RExpr := ⟨eseq x, eseq_cauchy x⟩

/-! ## (A) The bracket: a rational `[lo, hi]` with a checkable certificate contains `exp x` -/

/-- What the kernel checks for a bracket of `exp x`: a good index `n` (`2|x| ≤ n + 1`) and, from the partial
sum `L = S_n(|x|)` and `H = L + 2·t_n(|x|)` (the tail bound), `lo ≤ L`, `H ≤ hi` when `x ≥ 0`; when `x < 0`,
`lo·H ≤ 1 ≤ hi·L` (the bracket of `1/E(|x|)`, division-free). -/
def ExpCert (x lo hi : QExpr) : Prop :=
  (qle qzero x ∧ ∃ n, Good x n ∧ qle lo (S x n) ∧ qle (qadd (S x n) (qadd (tm x n) (tm x n))) hi) ∨
  (¬ qle qzero x ∧ ∃ n, Good (qneg x) n ∧
    qle (qmul lo (qadd (S (qneg x) (n + 1)) (qadd (tm (qneg x) (n + 1)) (tm (qneg x) (n + 1))))) qone ∧
    qle qone (qmul hi (S (qneg x) (n + 1))))

/-- Eventually below: the comparison `rle` asks for, from a termwise one. -/
theorem rle_of_eventually {a b : RExpr} (N : Nat) (h : ∀ n, N ≤ n → qle (a.seq n) (b.seq n)) : rle a b :=
  fun k => ⟨N, fun n hn => by have := h n hn; have := qeps_nonneg k; unfold qsub; rat_linarith⟩

/-- Bounds of the series of a non-negative argument at every later index. -/
theorem S_between {y : QExpr} (hy : qle qzero y) {n : Nat} (hg : Good y n) (m : Nat) (hm : n ≤ m) :
    qle (S y n) (S y m) ∧ qle (S y m) (qadd (S y n) (qadd (tm y n) (tm y n))) := by
  obtain ⟨j, rfl⟩ := le_ex hm
  have t1 := tail_tele hy hg j
  have t2 := tm_nonneg hy (n + j)
  exact ⟨S_mono hy n j, by rat_linarith⟩

/-- THE BRACKET IS SOUND: a certified `[lo, hi]` contains `exp x`. -/
theorem bracket_sound {x lo hi : QExpr} (h : ExpCert x lo hi) : rle (rofQ lo) (rexp x) ∧ rle (rexp x) (rofQ hi) := by
  rcases h with ⟨hx, n, hg, hlo, hhi⟩ | ⟨hx, n, hg, hlo, hhi⟩
  · refine ⟨rle_of_eventually n (fun m hm => ?_), rle_of_eventually n (fun m hm => ?_)⟩
    · show qle lo (eseq x m); rw [eseq_pos hx]; exact qle_trans hlo (S_between hx hg m hm).1
    · show qle (eseq x m) hi; rw [eseq_pos hx]; exact qle_trans (S_between hx hg m hm).2 hhi
  · have hy := neg_nonneg_of_not hx
    have hg1 := good_mono hg (Nat.le_succ n)
    refine ⟨rle_of_eventually (n + 1) (fun m hm => ?_), rle_of_eventually (n + 1) (fun m hm => ?_)⟩
    · show qle lo (eseq x m)
      rw [eseq_neg hx]
      obtain ⟨b1, b2⟩ := S_between hy hg1 m hm
      have one := S_ge_one hy n
      have am : qle qone (S (qneg x) m) := qle_trans one b1
      obtain ⟨i0, _, ic⟩ := inv_facts am
      -- lo ≤ 1/a_m: lo·a_m ≤ 1 (a_m ≤ H), times 1/a_m ≥ 0
      cases qle_total lo qzero with
      | inl hl => exact qle_trans hl i0
      | inr hl =>
          have f1 := scale_l b2 hl
          have f2 := scale (qle_trans f1 hlo) i0
          have e1 : qEq (qmul (qmul lo (S (qneg x) m)) (qinv' (S (qneg x) m)))
              (qmul lo (qmul (S (qneg x) m) (qinv' (S (qneg x) m)))) := by rat_ring
          have e2 := qmul_respects (qEq_refl lo) ic
          have e3 := qmul_one lo
          have e4 := qone_mul (qinv' (S (qneg x) m))
          rat_linarith
    · show qle (eseq x m) hi
      rw [eseq_neg hx]
      obtain ⟨b1, _⟩ := S_between hy hg1 m hm
      have one := S_ge_one hy n
      have am : qle qone (S (qneg x) m) := qle_trans one b1
      obtain ⟨i0, _, ic⟩ := inv_facts am
      -- hi > 0, and 1 ≤ hi·L ≤ hi·a_m
      have hpos : qle qzero hi := by
        cases qle_total qzero hi with
        | inl h => exact h
        | inr h =>
            have f := scale_l (qle_trans (qle_of_qlt qone_pos) one) (by rat_linarith : qle qzero (qneg hi))
            have e : qEq (qmul (qneg hi) (S (qneg x) (n + 1))) (qneg (qmul hi (S (qneg x) (n + 1)))) := by
              rat_ring
            have e0 := qmul_zero (qneg hi)
            have := qle_of_qlt qone_pos
            rat_linarith
      have f1 := scale_l b1 hpos
      have f2 := scale (qle_trans hhi f1) i0
      have e1 : qEq (qmul (qmul hi (S (qneg x) m)) (qinv' (S (qneg x) m)))
          (qmul hi (qmul (S (qneg x) m) (qinv' (S (qneg x) m)))) := by rat_ring
      have e2 := qmul_respects (qEq_refl hi) ic
      have e3 := qmul_one hi
      have e4 := qone_mul (qinv' (S (qneg x) m))
      rat_linarith

/-! ## (B) Slopes of the partial sums — exact at every index -/

/-- Divide by a positive natural: `(k+1)·y ≥ (k+1)·z` gives `y ≥ z`. -/
theorem le_of_nat_mul {k : Nat} {y z : QExpr} (h : qle (qmul (qnat (k + 1)) z) (qmul (qnat (k + 1)) y)) :
    qle z y := by
  have e : qEq (qmul (qnat (k + 1)) (qsub z y)) (qadd (qmul (qnat (k + 1)) z) (qneg (qmul (qnat (k + 1)) y))) := by
    unfold qsub; rat_ring
  have := nonpos_of_mul (qnat_succ_pos k) (by rat_linarith : qle (qmul (qnat (k + 1)) (qsub z y)) qzero)
  unfold qsub at this
  rat_linarith

theorem tm_one (x : QExpr) : qEq (tm x 1) x := by
  have h := tm_succ x 0
  have e1 : qEq (qnat (0 + 1)) (qadd (qnat 0) qone) := qnat_succ 0
  have e2 := qnat_zero
  have e3 : qEq (qmul (qnat (0 + 1)) (tm x 1)) (qmul (qadd (qnat 0) qone) (tm x 1)) := qmul_respects e1 (qEq_refl _)
  have e4 : qEq (qmul (qadd (qnat 0) qone) (tm x 1)) (qadd (qmul (qnat 0) (tm x 1)) (tm x 1)) := by rat_ring
  have e5 : qEq (qmul (qnat 0) (tm x 1)) (qmul qzero (tm x 1)) := qmul_respects e2 (qEq_refl _)
  have e6 := qzero_mul (tm x 1)
  have e7 : qEq (qmul (tm x 0) x) (qmul qone x) := qEq_refl _
  have e8 := qone_mul x
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- Terms grow with a non-negative argument. -/
theorem tm_mono {a b : QExpr} (ha : qle qzero a) (hab : qle a b) : ∀ k, qle (tm a k) (tm b k)
  | 0 => qle_refl _
  | k + 1 => by
      have ih := tm_mono ha hab k
      have hb : qle qzero b := qle_trans ha hab
      have ea := tm_succ a k
      have eb := tm_succ b k
      have f1 := scale ih hb
      have f2 := scale_l hab (tm_nonneg ha k)
      apply le_of_nat_mul (k := k)
      rat_linarith

/-- THE TERM SLOPE. `0 ≤ a ≤ b`, `d = b − a`: `d·t_k(a) ≤ t_{k+1}(b) − t_{k+1}(a) ≤ d·t_k(b)` — the
term-by-term form of `b^{k+1} − a^{k+1}` lying between `(k+1)·d·a^k` and `(k+1)·d·b^k`. -/
theorem tm_slope {a b : QExpr} (ha : qle qzero a) (hab : qle a b) :
    ∀ k, qle (qmul (qsub b a) (tm a k)) (qsub (tm b (k + 1)) (tm a (k + 1))) ∧
      qle (qsub (tm b (k + 1)) (tm a (k + 1))) (qmul (qsub b a) (tm b k))
  | 0 => by
      have e1 := tm_one a
      have e2 := tm_one b
      have e3 : qEq (qmul (qsub b a) (tm a 0)) (qmul (qsub b a) qone) := qEq_refl _
      have e4 : qEq (qmul (qsub b a) (tm b 0)) (qmul (qsub b a) qone) := qEq_refl _
      have e5 := qmul_one (qsub b a)
      constructor <;> (unfold qsub at *; rat_linarith)
  | k + 1 => by
      obtain ⟨l1, u1⟩ := tm_slope ha hab k
      have hb : qle qzero b := qle_trans ha hab
      have hd : qle qzero (qsub b a) := by unfold qsub; rat_linarith
      have ea := tm_succ a (k + 1)
      have eb := tm_succ b (k + 1)
      have ea' := tm_succ a k
      have eb' := tm_succ b k
      have m := tm_mono ha hab (k + 1)
      have t0 := tm_nonneg ha k
      have t1 := tm_nonneg ha (k + 1)
      -- (k+2)·Δ_{k+2} = Δ_{k+1}·b + t_{k+1}(a)·d
      have eΔ : qEq (qsub (qmul (tm b (k + 1)) b) (qmul (tm a (k + 1)) a))
          (qadd (qmul (qsub (tm b (k + 1)) (tm a (k + 1))) b) (qmul (tm a (k + 1)) (qsub b a))) := by
        unfold qsub; rat_ring
      have f1 := scale l1 hb                       -- d t_k(a) b ≤ Δ b
      have f2 := scale_l hab (qmul_nonneg hd t0)    -- d t_k(a) a ≤ d t_k(a) b
      have f3 := scale u1 hb                        -- Δ b ≤ d t_k(b) b
      have f4 := scale m hd                         -- t_{k+1}(a) d ≤ t_{k+1}(b) d
      have r1 : qEq (qmul (qmul (qsub b a) (tm a k)) a) (qmul (qsub b a) (qmul (tm a k) a)) := by rat_ring
      have r2 : qEq (qmul (qmul (qsub b a) (tm b k)) b) (qmul (qsub b a) (qmul (tm b k) b)) := by rat_ring
      have r3 := qmul_respects (qEq_refl (qsub b a)) ea'
      have r4 := qmul_respects (qEq_refl (qsub b a)) eb'
      have hn := qnat_succ (k + 1)
      have r5 : qEq (qmul (qnat (k + 1 + 1)) (qmul (qsub b a) (tm a (k + 1))))
          (qadd (qmul (qsub b a) (qmul (qnat (k + 1)) (tm a (k + 1)))) (qmul (tm a (k + 1)) (qsub b a))) :=
        qEq_trans (qmul_respects hn (qEq_refl _)) (by rat_ring)
      have r6 : qEq (qmul (qnat (k + 1 + 1)) (qmul (qsub b a) (tm b (k + 1))))
          (qadd (qmul (qsub b a) (qmul (qnat (k + 1)) (tm b (k + 1)))) (qmul (tm b (k + 1)) (qsub b a))) :=
        qEq_trans (qmul_respects hn (qEq_refl _)) (by rat_ring)
      have r7 : qEq (qmul (qnat (k + 1 + 1)) (qsub (tm b (k + 1 + 1)) (tm a (k + 1 + 1))))
          (qsub (qmul (qnat (k + 1 + 1)) (tm b (k + 1 + 1))) (qmul (qnat (k + 1 + 1)) (tm a (k + 1 + 1)))) := by
        unfold qsub; rat_ring
      have r8 : qEq (qsub (qmul (qnat (k + 1 + 1)) (tm b (k + 1 + 1))) (qmul (qnat (k + 1 + 1)) (tm a (k + 1 + 1))))
          (qsub (qmul (tm b (k + 1)) b) (qmul (tm a (k + 1)) a)) := by
        unfold qsub; exact qadd_respects eb (qneg_respects ea)
      constructor
      · apply le_of_nat_mul (k := k + 1); rat_linarith
      · apply le_of_nat_mul (k := k + 1); rat_linarith

/-- THE SUM SLOPE. `0 ≤ a ≤ b`: `d·S_n(a) ≤ S_{n+1}(b) − S_{n+1}(a) ≤ d·S_n(b)`. -/
theorem S_slope {a b : QExpr} (ha : qle qzero a) (hab : qle a b) :
    ∀ n, qle (qmul (qsub b a) (S a n)) (qsub (S b (n + 1)) (S a (n + 1))) ∧
      qle (qsub (S b (n + 1)) (S a (n + 1))) (qmul (qsub b a) (S b n))
  | 0 => by
      have e1 : qEq (S a 1) (qadd qzero qone) := qEq_refl _
      have e2 : qEq (S b 1) (qadd qzero qone) := qEq_refl _
      have e3 : qEq (qmul (qsub b a) (S a 0)) (qmul (qsub b a) qzero) := qEq_refl _
      have e4 : qEq (qmul (qsub b a) (S b 0)) (qmul (qsub b a) qzero) := qEq_refl _
      have e5 := qmul_zero (qsub b a)
      constructor <;> (unfold qsub at *; rat_linarith)
  | n + 1 => by
      obtain ⟨l1, u1⟩ := S_slope ha hab n
      obtain ⟨l2, u2⟩ := tm_slope ha hab n
      have e : qEq (qsub (S b (n + 1 + 1)) (S a (n + 1 + 1)))
          (qadd (qsub (S b (n + 1)) (S a (n + 1))) (qsub (tm b (n + 1)) (tm a (n + 1)))) := by
        show qEq (qsub (qadd (S b (n + 1)) (tm b (n + 1))) (qadd (S a (n + 1)) (tm a (n + 1)))) _
        unfold qsub; rat_ring
      have e2 : qEq (qmul (qsub b a) (S a (n + 1))) (qadd (qmul (qsub b a) (S a n)) (qmul (qsub b a) (tm a n))) := by
        show qEq (qmul (qsub b a) (qadd (S a n) (tm a n))) _; rat_ring
      have e3 : qEq (qmul (qsub b a) (S b (n + 1))) (qadd (qmul (qsub b a) (S b n)) (qmul (qsub b a) (tm b n))) := by
        show qEq (qmul (qsub b a) (qadd (S b n) (tm b n))) _; rat_ring
      constructor <;> rat_linarith

theorem tm_zero_succ : ∀ k, qEq (tm qzero (k + 1)) qzero := by
  intro k
  have h := tm_succ qzero k
  have e := qmul_zero (tm qzero k)
  have h1 : qle (qmul (qnat (k + 1)) (tm qzero (k + 1))) (qmul (qnat (k + 1)) qzero) := by
    have := qmul_zero (qnat (k + 1)); rat_linarith
  have h2 : qle (qmul (qnat (k + 1)) qzero) (qmul (qnat (k + 1)) (tm qzero (k + 1))) := by
    have := qmul_zero (qnat (k + 1)); rat_linarith
  exact qle_antisymm (le_of_nat_mul h1) (le_of_nat_mul h2)

theorem S_zero : ∀ n, qEq (S qzero (n + 1)) qone
  | 0 => by have := qzero_add qone; exact this
  | n + 1 => by
      have ih := S_zero n
      have h := tm_zero_succ n
      show qEq (qadd (S qzero (n + 1)) (tm qzero (n + 1))) qone
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `1/B − 1/A = (A − B)·(1/A)(1/B)` for `A, B ≥ 1`. -/
theorem inv_diff {A B : QExpr} (hA : qle qone A) (hB : qle qone B) :
    qEq (qsub (qinv' B) (qinv' A)) (qmul (qsub A B) (qmul (qinv' A) (qinv' B))) := by
  obtain ⟨_, _, ac⟩ := inv_facts hA
  obtain ⟨_, _, bc⟩ := inv_facts hB
  have e1 : qEq (qmul (qsub A B) (qmul (qinv' A) (qinv' B)))
      (qadd (qmul (qmul A (qinv' A)) (qinv' B)) (qneg (qmul (qmul B (qinv' B)) (qinv' A)))) := by
    unfold qsub; rat_ring
  have e2 : qEq (qmul (qmul A (qinv' A)) (qinv' B)) (qmul qone (qinv' B)) := qmul_respects ac (qEq_refl _)
  have e3 : qEq (qmul (qmul B (qinv' B)) (qinv' A)) (qmul qone (qinv' A)) := qmul_respects bc (qEq_refl _)
  have e4 := qone_mul (qinv' A)
  have e5 := qone_mul (qinv' B)
  unfold qsub at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE SLOPE OF `E_{n+1}`, any signs. `a ≤ b`, both within `R` of zero:
`(b − a)·(E(a) − t_n(R)) ≤ E(b) − E(a) ≤ (b − a)·E(b)` at index `n + 1` — exact, the error `t_n(R)` uniform
over the interval. -/
theorem E_slope {a b R : QExpr} (hab : qle a b) (haR : qclose a qzero R) (hbR : qclose b qzero R) (n : Nat) :
    qle (qmul (qsub b a) (qsub (eseq a (n + 1)) (tm R n))) (qsub (eseq b (n + 1)) (eseq a (n + 1))) ∧
    qle (qsub (eseq b (n + 1)) (eseq a (n + 1))) (qmul (qsub b a) (eseq b (n + 1))) := by
  obtain ⟨ra1, ra2⟩ := haR
  obtain ⟨rb1, rb2⟩ := hbR
  unfold qsub at ra1 ra2 rb1 rb2
  have hR : qle qzero R := by rat_linarith
  have hd : qle qzero (qsub b a) := by unfold qsub; rat_linarith
  cases qle.decidable qzero a with
  | isTrue ha =>
      have hb : qle qzero b := qle_trans ha hab
      rw [eseq_pos ha, eseq_pos hb]
      obtain ⟨l, u⟩ := S_slope ha hab n
      have tR := tm_mono ha (by rat_linarith : qle a R) n
      have tb := tm_nonneg hb n
      have f1 := scale_l (by show qle (qsub (S a (n + 1)) (tm R n)) (S a n)
                             unfold qsub; show qle (qadd (qadd (S a n) (tm a n)) (qneg (tm R n))) _
                             rat_linarith) hd
      have f2 := scale_l (by show qle (S b n) (S b (n + 1))
                             show qle (S b n) (qadd (S b n) (tm b n)); rat_linarith) hd
      exact ⟨qle_trans f1 l, qle_trans u f2⟩
  | isFalse ha =>
      have na := neg_nonneg_of_not ha
      cases qle.decidable qzero b with
      | isFalse hb =>
          -- both negative: A = S_{n+1}(−a) ≥ B = S_{n+1}(−b)
          have nb := neg_nonneg_of_not hb
          rw [eseq_neg ha, eseq_neg hb]
          have hab' : qle (qneg b) (qneg a) := by rat_linarith
          obtain ⟨l, u⟩ := S_slope nb hab' n
          have hA := S_ge_one' na (Nat.le_add_left 1 n)
          have hB := S_ge_one' nb (Nat.le_add_left 1 n)
          obtain ⟨iA0, iA1, _⟩ := inv_facts hA
          obtain ⟨iB0, iB1, bc⟩ := inv_facts hB
          have eD := inv_diff hA hB
          have ed : qEq (qsub (qneg a) (qneg b)) (qsub b a) := by unfold qsub; rat_ring
          have pAB := qmul_nonneg iA0 iB0
          have pAB1 : qle (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))) qone := by
            have := scale_l iB1 iA0; have := qmul_one (qinv' (S (qneg a) (n + 1))); rat_linarith
          -- multiply the S-slope by (1/A)(1/B) ≥ 0
          have g1 := scale l pAB
          have g2 := scale u pAB
          have tR := tm_mono nb (by rat_linarith : qle (qneg b) R) n
          have tn := tm_nonneg nb n
          have sb : qEq (S (qneg b) (n + 1)) (qadd (S (qneg b) n) (tm (qneg b) n)) := qEq_refl _
          have sa : qle (S (qneg a) n) (S (qneg a) (n + 1)) := by
            show qle _ (qadd (S (qneg a) n) (tm (qneg a) n)); have := tm_nonneg na n; rat_linarith
          -- lower: d·S_n(−b)·iA·iB = d·(B − t)·iA·iB ≥ d·(iA − t(R))
          have L1 : qEq (qmul (qmul (qsub (qneg a) (qneg b)) (S (qneg b) n))
              (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))))
              (qmul (qsub b a) (qadd (qmul (qinv' (S (qneg a) (n + 1))) (qmul (S (qneg b) (n + 1)) (qinv' (S (qneg b) (n + 1)))))
                (qneg (qmul (tm (qneg b) n) (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))))))) := by
            have := qmul_respects (qmul_respects ed (qEq_refl (S (qneg b) n))) (qEq_refl
              (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))))
            refine qEq_trans this ?_
            have hs : qEq (S (qneg b) n) (qsub (S (qneg b) (n + 1)) (tm (qneg b) n)) := by
              unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
            refine qEq_trans (qmul_respects (qmul_respects (qEq_refl _) hs) (qEq_refl _)) ?_
            unfold qsub; rat_ring
          have L2 : qEq (qmul (qinv' (S (qneg a) (n + 1))) (qmul (S (qneg b) (n + 1)) (qinv' (S (qneg b) (n + 1)))))
              (qinv' (S (qneg a) (n + 1))) :=
            qEq_trans (qmul_respects (qEq_refl _) bc) (qmul_one _)
          have L4 : qle (qmul (tm (qneg b) n) (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))))
              (tm R n) := by
            have := scale_l pAB1 tn; have := qmul_one (tm (qneg b) n)
            rat_linarith
          have L5 : qle (qmul (qsub b a) (qsub (qinv' (S (qneg a) (n + 1))) (tm R n)))
              (qmul (qsub b a) (qadd (qmul (qinv' (S (qneg a) (n + 1))) (qmul (S (qneg b) (n + 1)) (qinv' (S (qneg b) (n + 1)))))
                (qneg (qmul (tm (qneg b) n) (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))))))) :=
            scale_l (by unfold qsub; rat_linarith) hd
          -- upper: d·S_n(−a)·iA·iB ≤ d·A·iA·iB = d·iB
          have U1 := scale_l sa hd
          have U2 := scale U1 pAB
          obtain ⟨_, _, ac⟩ := inv_facts hA
          have U3 : qEq (qmul (qmul (qsub b a) (S (qneg a) (n + 1)))
              (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))))
              (qmul (qsub b a) (qmul (qmul (S (qneg a) (n + 1)) (qinv' (S (qneg a) (n + 1)))) (qinv' (S (qneg b) (n + 1))))) := by
            rat_ring
          have U4 : qEq (qmul (qsub b a) (qmul (qmul (S (qneg a) (n + 1)) (qinv' (S (qneg a) (n + 1)))) (qinv' (S (qneg b) (n + 1)))))
              (qmul (qsub b a) (qinv' (S (qneg b) (n + 1)))) :=
            qmul_respects (qEq_refl _) (qEq_trans (qmul_respects ac (qEq_refl _)) (qone_mul _))
          have U5 : qEq (qmul (qmul (qsub (qneg a) (qneg b)) (S (qneg a) n))
              (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1)))))
              (qmul (qmul (qsub b a) (S (qneg a) n)) (qmul (qinv' (S (qneg a) (n + 1))) (qinv' (S (qneg b) (n + 1))))) :=
            qmul_respects (qmul_respects ed (qEq_refl _)) (qEq_refl _)
          constructor
          · rat_linarith
          · rat_linarith
      | isTrue hb =>
          -- mixed: a < 0 ≤ b, split at 0 where S_{n+1}(0) = 1
          rw [eseq_neg ha, eseq_pos hb]
          have h0 := qle_refl qzero
          obtain ⟨pl, pu⟩ := S_slope h0 hb n
          obtain ⟨ql, qu⟩ := S_slope h0 na n
          have z := S_zero n
          have hN := S_ge_one' na (Nat.le_add_left 1 n)
          have hP := S_ge_one' hb (Nat.le_add_left 1 n)
          obtain ⟨i0, i1, ic⟩ := inv_facts hN
          have t0R := tm_mono h0 hR n
          have tz := tm_nonneg h0 n
          have tR0 := tm_nonneg hR n
          have sz : qEq (S qzero n) (qsub (S qzero (n + 1)) (tm qzero n)) := by
            unfold qsub; show qEq (S qzero n) (qadd (qadd (S qzero n) (tm qzero n)) (qneg (tm qzero n)))
            rat_ring
          have e1 : qEq (qsub b qzero) b := by unfold qsub; rat_ring
          have e2 : qEq (qsub (qneg a) qzero) (qneg a) := by unfold qsub; rat_ring
          -- 1 − 1/N = (N − 1)·(1/N)
          have eN : qEq (qsub qone (qinv' (S (qneg a) (n + 1))))
              (qmul (qsub (S (qneg a) (n + 1)) qone) (qinv' (S (qneg a) (n + 1)))) := by
            have : qEq (qmul (qsub (S (qneg a) (n + 1)) qone) (qinv' (S (qneg a) (n + 1))))
                (qadd (qmul (S (qneg a) (n + 1)) (qinv' (S (qneg a) (n + 1)))) (qneg (qinv' (S (qneg a) (n + 1))))) := by
              unfold qsub; rat_ring
            unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)
          -- products with b, −a, 1/N
          have m1 := scale_l (show qle (qsub qone (tm R n)) (S qzero n) by unfold qsub at *; rat_linarith) hb
          have m2 := scale_l (show qle (qsub qone (tm R n)) (S qzero n) by unfold qsub at *; rat_linarith) na
          have m3 := scale (show qle (qmul (qneg a) (S qzero n)) (qsub (S (qneg a) (n + 1)) qone) by
            have := qmul_respects (qEq_symm e2) (qEq_refl (S qzero n))
            unfold qsub at *; rat_linarith) i0
          have m4 := scale (show qle (qsub (S (qneg a) (n + 1)) qone) (qmul (qneg a) (S (qneg a) n)) by
            have := qmul_respects (qEq_symm e2) (qEq_refl (S (qneg a) n))
            unfold qsub at *; rat_linarith) i0
          have sa : qle (S (qneg a) n) (S (qneg a) (n + 1)) := by
            show qle _ (qadd (S (qneg a) n) (tm (qneg a) n)); have := tm_nonneg na n; rat_linarith
          have m5 := scale (scale_l sa na) i0
          have m6 := scale_l i1 hb
          have m7 := scale_l hP na
          have m8 := scale_l (show qle (S b n) (S b (n + 1)) by
            show qle _ (qadd (S b n) (tm b n)); have := tm_nonneg hb n; rat_linarith) hb
          have m9 := scale_l i1 tR0
          have m10 := scale (scale_l (qle_refl (qinv' (S (qneg a) (n + 1)))) i0) tR0
          have r1 : qEq (qmul (qmul (qneg a) (S (qneg a) (n + 1))) (qinv' (S (qneg a) (n + 1))))
              (qmul (qneg a) (qmul (S (qneg a) (n + 1)) (qinv' (S (qneg a) (n + 1))))) := by rat_ring
          have r2 := qmul_respects (qEq_refl (qneg a)) ic
          have r3 := qmul_one (qneg a)
          have r4 := qmul_one (tm R n)
          have r5 : qEq (qmul (qmul (qneg a) (qsub qone (tm R n))) (qinv' (S (qneg a) (n + 1))))
              (qadd (qmul (qneg a) (qinv' (S (qneg a) (n + 1))))
                (qneg (qmul (qneg a) (qmul (tm R n) (qinv' (S (qneg a) (n + 1))))))) := by unfold qsub; rat_ring
          have r6 := scale_l (show qle (qmul (tm R n) (qinv' (S (qneg a) (n + 1)))) (tm R n) by
            have := scale_l i1 tR0; rat_linarith) na
          have r7 : qEq (qmul (qsub b (qneg (qneg a))) (qsub (qinv' (S (qneg a) (n + 1))) (tm R n)))
              (qadd (qadd (qmul b (qinv' (S (qneg a) (n + 1)))) (qneg (qmul b (tm R n))))
                (qadd (qmul (qneg a) (qinv' (S (qneg a) (n + 1)))) (qneg (qmul (qneg a) (tm R n))))) := by
            unfold qsub; rat_ring
          have r8 : qEq (qsub b a) (qsub b (qneg (qneg a))) := by unfold qsub; rat_ring
          have r9 : qEq (qmul (qsub b a) (qsub (qinv' (S (qneg a) (n + 1))) (tm R n)))
              (qmul (qsub b (qneg (qneg a))) (qsub (qinv' (S (qneg a) (n + 1))) (tm R n))) :=
            qmul_respects r8 (qEq_refl _)
          have r10 : qEq (qmul (qsub b a) (S b (n + 1))) (qadd (qmul b (S b (n + 1))) (qmul (qneg a) (S b (n + 1)))) := by
            unfold qsub; rat_ring
          have r11 : qEq (qmul b (qsub qone (tm R n))) (qadd b (qneg (qmul b (tm R n)))) := by unfold qsub; rat_ring
          have r12 : qEq (qmul (qneg a) (qsub qone (tm R n))) (qadd (qneg a) (qneg (qmul (qneg a) (tm R n)))) := by
            unfold qsub; rat_ring
          have r13 := qmul_one b
          have r14 : qEq (qmul (qmul (qneg a) (S qzero n)) (qinv' (S (qneg a) (n + 1))))
              (qmul (qmul (qneg a) (S qzero n)) (qinv' (S (qneg a) (n + 1)))) := qEq_refl _
          have m11 := scale m2 i0
          unfold qsub at *
          constructor <;> rat_linarith

theorem S_nonneg {y : QExpr} (hy : qle qzero y) : ∀ n, qle qzero (S y n)
  | 0 => qle_refl _
  | n + 1 => by
      have := S_nonneg hy n; have := tm_nonneg hy n
      show qle qzero (qadd (S y n) (tm y n)); rat_linarith

/-! ## (B) Continuity: monotone, uniformly convergent on `[−R, R]`, Lipschitz — `exp` of a real -/

theorem E_mono {a b : QExpr} (hab : qle a b) (n : Nat) : qle (eseq a (n + 1)) (eseq b (n + 1)) := by
  cases qle.decidable qzero a with
  | isTrue ha =>
      have hb := qle_trans ha hab
      rw [eseq_pos ha, eseq_pos hb]
      obtain ⟨l, _⟩ := S_slope ha hab n
      have hd : qle qzero (qsub b a) := by unfold qsub; rat_linarith
      have := qmul_nonneg hd (S_nonneg ha n)
      have hs : qEq (qsub (S b (n + 1)) (S a (n + 1))) (qadd (S b (n + 1)) (qneg (S a (n + 1)))) := qEq_refl _
      rat_linarith
  | isFalse ha =>
      have na := neg_nonneg_of_not ha
      have hN := S_ge_one' na (Nat.le_add_left 1 n)
      obtain ⟨i0, i1, _⟩ := inv_facts hN
      cases qle.decidable qzero b with
      | isTrue hb =>
          rw [eseq_neg ha, eseq_pos hb]
          have := S_ge_one' hb (Nat.le_add_left 1 n)
          rat_linarith
      | isFalse hb =>
          have nb := neg_nonneg_of_not hb
          rw [eseq_neg ha, eseq_neg hb]
          have hab' : qle (qneg b) (qneg a) := by rat_linarith
          obtain ⟨l, _⟩ := S_slope nb hab' n
          have hB := S_ge_one' nb (Nat.le_add_left 1 n)
          obtain ⟨j0, _, _⟩ := inv_facts hB
          have hd : qle qzero (qsub (qneg a) (qneg b)) := by unfold qsub; rat_linarith
          have g := qmul_nonneg (qmul_nonneg hd (S_nonneg nb n)) (qmul_nonneg i0 j0)
          have g2 := scale l (qmul_nonneg i0 j0)
          have eD := inv_diff hN hB
          have hs : qEq (qsub (qinv' (S (qneg b) (n + 1))) (qinv' (S (qneg a) (n + 1))))
              (qadd (qinv' (S (qneg b) (n + 1))) (qneg (qinv' (S (qneg a) (n + 1))))) := qEq_refl _
          rat_linarith

theorem E_nonneg (x : QExpr) (n : Nat) : qle qzero (eseq x (n + 1)) := by
  cases qle.decidable qzero x with
  | isTrue hx =>
      rw [eseq_pos hx]; have := S_ge_one' hx (Nat.le_add_left 1 n); have := qle_of_qlt qone_pos
      rat_linarith
  | isFalse hx =>
      rw [eseq_neg hx]; exact (inv_facts (S_ge_one' (neg_nonneg_of_not hx) (Nat.le_add_left 1 n))).1

/-- Within `R` of zero, `E_{n+1}(x) ≤ S_{n+1}(R)`. -/
theorem E_le_SR {x R : QExpr} (h : qclose x qzero R) (n : Nat) : qle (eseq x (n + 1)) (S R (n + 1)) := by
  obtain ⟨h1, h2⟩ := h
  unfold qsub at h1 h2
  have hR : qle qzero R := by rat_linarith
  have := E_mono (by rat_linarith : qle x R) n
  rw [eseq_pos hR] at this; exact this

/-- The partial sums of `R ≥ 0` are bounded, all of them. -/
theorem S_bounded {R : QExpr} (hR : qle qzero R) : ∃ H, ∀ n, qle (S R n) H := by
  obtain ⟨K, hg⟩ := good_exists R
  refine ⟨qadd (S R K) (qadd (tm R K) (tm R K)), fun n => ?_⟩
  have t0 := tm_nonneg hR K
  cases Nat.le_total K n with
  | inl h => exact (S_between hR hg n h).2
  | inr h =>
      obtain ⟨j, rfl⟩ := le_ex h
      have := S_mono hR n j
      rat_linarith

/-- UNIFORM CONVERGENCE on `[−R, R]`: one index serves every argument there. -/
theorem E_unif {R : QExpr} (hR : qle qzero R) (k : Nat) :
    ∃ N, ∀ y, qclose y qzero R → ∀ m n, N ≤ m → N ≤ n → qclose (eseq y m) (eseq y n) (qeps k) := by
  obtain ⟨K, hg⟩ := good_exists R
  obtain ⟨N, hKN, hN⟩ := tm_small hR hg k
  -- for 0 ≤ z ≤ R, the lower index carries the bound 2·t(R)
  have key : ∀ z, qle qzero z → qle z R → ∀ a b, N ≤ a → a ≤ b →
      qle (S z a) (S z b) ∧ qle (S z b) (qadd (S z a) (qeps k)) := by
    intro z hz hzR a b ha hab
    obtain ⟨j, rfl⟩ := le_ex hab
    have gz : Good z a := by
      have := good_mono hg (Nat.le_trans hKN ha); unfold Good at *; rat_linarith
    have t1 := tail_tele hz gz j
    have t2 := tm_nonneg hz (a + j)
    have t3 := hN a ha
    have t4 := tm_mono hz hzR a
    exact ⟨S_mono hz a j, by rat_linarith⟩
  have keyc : ∀ z, qle qzero z → qle z R → ∀ m n, N ≤ m → N ≤ n → qclose (S z m) (S z n) (qeps k) := by
    intro z hz hzR m n hm hn
    cases Nat.le_total m n with
    | inl h => obtain ⟨k1, k2⟩ := key z hz hzR m n hm h; constructor <;> (unfold qsub; rat_linarith)
    | inr h => obtain ⟨k1, k2⟩ := key z hz hzR n m hn h; constructor <;> (unfold qsub; rat_linarith)
  refine ⟨N + 1, fun y hy m n hm hn => ?_⟩
  obtain ⟨y1, y2⟩ := hy
  unfold qsub at y1 y2
  cases qle.decidable qzero y with
  | isTrue h =>
      rw [eseq_pos h, eseq_pos h]
      exact keyc y h (by rat_linarith) m n (Nat.le_of_succ_le hm) (Nat.le_of_succ_le hn)
  | isFalse h =>
      have nh := neg_nonneg_of_not h
      rw [eseq_neg h, eseq_neg h]
      exact inv_lip (S_ge_one' nh (Nat.le_trans (Nat.le_add_left 1 N) hm))
        (S_ge_one' nh (Nat.le_trans (Nat.le_add_left 1 N) hn))
        (keyc (qneg y) nh (by rat_linarith) m n (Nat.le_of_succ_le hm) (Nat.le_of_succ_le hn))

/-- LIPSCHITZ on `[−R, R]`: `|E(a) − E(b)| ≤ |a − b|·S_{n+1}(R)`. -/
theorem E_lip {a b R e : QExpr} (ha : qclose a qzero R) (hb : qclose b qzero R) (h : qclose a b e) (n : Nat) :
    qclose (eseq a (n + 1)) (eseq b (n + 1)) (qmul e (S R (n + 1))) := by
  have he : qle qzero e := by obtain ⟨h1, h2⟩ := h; unfold qsub at h1 h2; rat_linarith
  obtain ⟨d1, d2⟩ := h
  unfold qsub at d1 d2
  cases qle_total a b with
  | inl hab =>
      obtain ⟨_, u⟩ := E_slope hab ha hb n
      have m := E_mono hab n
      have eb := E_le_SR hb n
      have f1 := scale (by unfold qsub; rat_linarith : qle (qsub b a) e) (E_nonneg b n)
      have f2 := scale_l eb he
      constructor <;> (unfold qsub at *; rat_linarith)
  | inr hba =>
      obtain ⟨_, u⟩ := E_slope hba hb ha n
      have m := E_mono hba n
      have ea := E_le_SR ha n
      have f1 := scale (by unfold qsub; rat_linarith : qle (qsub a b) e) (E_nonneg a n)
      have f2 := scale_l ea he
      constructor <;> (unfold qsub at *; rat_linarith)

/-- `exp` of an operational REAL: `E_n(x_n)`, Cauchy by uniform convergence and the Lipschitz bound. -/
theorem rexpR_cauchy (x : RExpr) (k : Nat) :
    ∃ N, ∀ m n, N ≤ m → N ≤ n → qclose (eseq (x.seq m) m) (eseq (x.seq n) n) (qeps k) := by
  obtain ⟨B, N0, hb⟩ := rbounded x
  have hR : qle qzero (qofInt (pow2 B)) := qofInt_le (pow2_nonneg B)
  obtain ⟨H, hH⟩ := S_bounded hR
  obtain ⟨C, hC0, _⟩ := qexpr_bound H
  have hC : qle H (qofInt (pow2 C)) := by unfold qsub at hC0; rat_linarith
  obtain ⟨N1, hU⟩ := E_unif hR (k + 1)
  obtain ⟨N2, hX⟩ := x.cauchy ((k + 1) + C)
  refine ⟨N0 + N1 + N2 + 1, fun m n hm hn => ?_⟩
  have m0 : N0 ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_add_right N0 N1) (Nat.le_add_right _ N2))
    (Nat.le_trans (Nat.le_add_right _ 1) hm)
  have n0 : N0 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_right N0 N1) (Nat.le_add_right _ N2))
    (Nat.le_trans (Nat.le_add_right _ 1) hn)
  have m1 : N1 ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_add_left N1 N0) (Nat.le_add_right _ N2))
    (Nat.le_trans (Nat.le_add_right _ 1) hm)
  have n1 : N1 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N1 N0) (Nat.le_add_right _ N2))
    (Nat.le_trans (Nat.le_add_right _ 1) hn)
  have m2 : N2 ≤ m := Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 (N0 + N1)) (Nat.le_add_right _ 1)) hm
  have n2 : N2 ≤ n := Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 (N0 + N1)) (Nat.le_add_right _ 1)) hn
  -- n = n' + 1
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    cases n with
    | zero => exact absurd hn (Nat.not_succ_le_zero _)
    | succ n' => exact ⟨n', rfl⟩
  have u1 := hU (x.seq m) (hb m m0) m (n' + 1) m1 n1
  have l1 := E_lip (hb m m0) (hb (n' + 1) n0) (hX m (n' + 1) m2 n2) n'
  have hHn := hH (n' + 1)
  have l2 := scale_l (qle_trans hHn hC) (qeps_nonneg ((k + 1) + C))
  have e1 : qEq (qmul (qeps ((k + 1) + C)) (qofInt (pow2 C))) (qmul (qofInt (pow2 C)) (qeps ((k + 1) + C))) :=
    qmul_comm _ _
  have e2 := qpow2_mul_eps C (k + 1)
  have e3 := qeps_succ_add k
  have l3 := scale_l hHn (qeps_nonneg ((k + 1) + C))
  have := qclose_trans u1 l1
  refine qclose_mono this ?_
  rat_linarith

def rexpR (x : RExpr) : RExpr := ⟨fun n => eseq (x.seq n) n, rexpR_cauchy x⟩

set_option maxRecDepth 200000 in
/-- Nonvacuity: `e ∈ [2, 3]`, certified at `n = 3` (`S_3(1) = 5/2`, the tail bound `2·t_3 = 1/3`). The
numbers are VR's unary ones, unnormalised — hence the recursion budget for this one check. -/
example : rle (rofQ (qnat 2)) (rexp (qnat 1)) ∧ rle (rexp (qnat 1)) (rofQ (qnat 3)) :=
  bracket_sound (Or.inl ⟨by decide, 3, by unfold Good; decide, by decide, by decide⟩)

end ZExp

#print axioms ZExp.qnat_succ
#print axioms ZExp.qnat_succ_pos
#print axioms ZExp.exists_nat_bound
#print axioms ZExp.nonpos_of_mul
#print axioms ZExp.tm_half
#print axioms ZExp.tail_tele
#print axioms ZExp.tm_decay
#print axioms ZExp.le_ex
#print axioms ZExp.good_exists
#print axioms ZExp.tm_small
#print axioms ZExp.S_cauchy
#print axioms ZExp.inv_lip
#print axioms ZExp.eseq_cauchy
#print axioms ZExp.rexp
#print axioms ZExp.bracket_sound
#print axioms ZExp.tm_mono
#print axioms ZExp.tm_slope
#print axioms ZExp.S_slope
#print axioms ZExp.S_zero
#print axioms ZExp.inv_diff
#print axioms ZExp.E_slope
#print axioms ZExp.E_mono
#print axioms ZExp.E_unif
#print axioms ZExp.E_lip
#print axioms ZExp.rexpR_cauchy
