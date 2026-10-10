import VR.Numbers.RealsOp

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
