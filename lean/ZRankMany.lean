import ZMonoTaylor

/-!
# ZRankMany — why `znumsolve._solve_rank_many` may read the rank-one parameters at their corners. Zero axioms.

`_solve_rank_many` solves `A(p, q) x = b(p, q)` for one parameter `p` entering with rank > 1 and every other
parameter `q` entering with rank ONE: the derivative of the augmented matrix `[∂A/∂q | ∂b/∂q]` has rank ≤ 1
identically (`_rank_one_in`, every 2×2 minor zero as a polynomial), the entries multilinear (`_mlin`). It reads the
others at the corners of their box. This file proves the reason, without determinants:

  **`rank_one_monotone`** — let `[A | b](q) = [A | b](ql) + (q − ql)·w·[y | β]` (rank one in `q`), and let the
  system have a solution `xs q` at every `q ∈ [ql, qh]`, unique there. Then every coordinate of `xs` is MONOTONE
  in `q` on `[ql, qh]` (non-decreasing or non-increasing — the kernel decides which).

The proof: with `s(q) = y·xs(q) − β` and `τ(q) = (ql − q)·s(q)`, the residual of `xs(q)` at `ql` is `τ(q)·w`; so
`τ(qh)·(xs(q) − xs(ql)) = τ(q)·(xs(qh) − xs(ql))` by uniqueness at `ql` (two kernel vectors differ by a kernel
vector). Dotted with `y`: `s(q)·e(q) = τ(qh)·s(ql)` with `e(q) = τ(qh) + (q − ql)(s(qh) − s(ql))` affine; `e` never
vanishes on the box (it would make `s(ql) = 0`), so it keeps one sign; and then
`e(q₁)e(q₂)·(xs(q₂) − xs(q₁))ᵢ = −τ(qh)·s(ql)·(xs(qh) − xs(ql))ᵢ·(q₂ − q₁)` — one sign for all `q₁ ≤ q₂`.

Parts: 1 sums, the system, the residual's shift; 2 the two-point formula; 3 the sign of `e` and
**`rank_one_monotone`**; 4 **`corners`** — monotone in each coordinate ⇒ every value lies between two corners;
5 **`rank_one_corners`** — the solver's claim: with every rank-one parameter of rank one along its line and the
solution unique on the box, every unknown's value lies between its values at two corners.

NOT covered here (a named premise, a theorem of one-variable analysis): the rank-MANY parameter's own direction —
that the extremes of `N(p)/D(p)` on `p`'s interval sit at its ends or at the real roots of `N′D − ND′` (Sturm).
-/

namespace ZRankMany
open VR VR.Numbers ZExp

/-- `Σ_{c ∈ l} f c`. -/
def lsum (f : Nat → QExpr) : List Nat → QExpr
  | [] => qzero
  | c :: l => qadd (f c) (lsum f l)

theorem lsum_congr {f g : Nat → QExpr} : ∀ l : List Nat, (∀ c, c ∈ l → qEq (f c) (g c)) → qEq (lsum f l) (lsum g l)
  | [], _ => qEq_refl _
  | c :: l, h => qadd_respects (h c (List.Mem.head _)) (lsum_congr l (fun d hd => h d (List.Mem.tail _ hd)))

theorem lsum_add (f g : Nat → QExpr) :
    ∀ l : List Nat, qEq (lsum (fun c => qadd (f c) (g c)) l) (qadd (lsum f l) (lsum g l))
  | [] => by show qEq qzero (qadd qzero qzero); q_ring
  | c :: l => by
      have ih := lsum_add f g l
      show qEq (qadd (qadd (f c) (g c)) (lsum (fun c => qadd (f c) (g c)) l)) (qadd (qadd (f c) (lsum f l)) (qadd (g c) (lsum g l)))
      refine qEq_trans (qadd_respects (qEq_refl _) ih) ?_
      q_ring

theorem lsum_smul (k : QExpr) (f : Nat → QExpr) :
    ∀ l : List Nat, qEq (lsum (fun c => qmul k (f c)) l) (qmul k (lsum f l))
  | [] => by show qEq qzero (qmul k qzero); q_ring
  | c :: l => by
      have ih := lsum_smul k f l
      show qEq (qadd (qmul k (f c)) (lsum (fun c => qmul k (f c)) l)) (qmul k (qadd (f c) (lsum f l)))
      refine qEq_trans (qadd_respects (qEq_refl _) ih) ?_
      q_ring

theorem lsum_neg (f : Nat → QExpr) : ∀ l : List Nat, qEq (lsum (fun c => qneg (f c)) l) (qneg (lsum f l))
  | [] => by show qEq qzero (qneg qzero); q_ring
  | c :: l => by
      have ih := lsum_neg f l
      show qEq (qadd (qneg (f c)) (lsum (fun c => qneg (f c)) l)) (qneg (qadd (f c) (lsum f l)))
      refine qEq_trans (qadd_respects (qEq_refl _) ih) ?_
      q_ring

/-- A linear system over the columns `cols` and the rows `rows`, its coefficients depending on `q`. -/
structure Sys where
  rows : List Nat
  cols : List Nat
  A : QExpr → Nat → Nat → QExpr
  b : QExpr → Nat → QExpr

/-- `(A(q)·u)_r`. -/
def lin (S : Sys) (q : QExpr) (u : Nat → QExpr) (r : Nat) : QExpr := lsum (fun c => qmul (S.A q r c) (u c)) S.cols

/-- The residual `(A(q)·x − b(q))_r`. -/
def res (S : Sys) (q : QExpr) (x : Nat → QExpr) (r : Nat) : QExpr := qsub (lin S q x r) (S.b q r)

/-- `x` solves the system at `q`. -/
def Solves (S : Sys) (q : QExpr) (x : Nat → QExpr) : Prop := ∀ r, r ∈ S.rows → qEq (res S q x r) qzero

/-- Solutions at `q` are unique (on the columns). -/
def Unique (S : Sys) (q : QExpr) : Prop :=
  ∀ x x' : Nat → QExpr, Solves S q x → Solves S q x' → ∀ c, c ∈ S.cols → qEq (x c) (x' c)

/-- RANK ONE in `q`, based at `ql`: `[A | b](q) = [A | b](ql) + (q − ql)·w·[y | β]`. -/
structure RankOne (S : Sys) (ql : QExpr) where
  w : Nat → QExpr
  y : Nat → QExpr
  β : QExpr
  hA : ∀ q r c, qEq (S.A q r c) (qadd (S.A ql r c) (qmul (qmul (qsub q ql) (w r)) (y c)))
  hb : ∀ q r, qEq (S.b q r) (qadd (S.b ql r) (qmul (qmul (qsub q ql) (w r)) β))

variable {S : Sys} {ql : QExpr}

/-- `y·x`. -/
def dotY (R : RankOne S ql) (x : Nat → QExpr) : QExpr := lsum (fun c => qmul (R.y c) (x c)) S.cols

/-- `s(x) = y·x − β`. -/
def sv (R : RankOne S ql) (x : Nat → QExpr) : QExpr := qsub (dotY R x) R.β

theorem lin_congr (q : QExpr) {u v : Nat → QExpr} (h : ∀ c, c ∈ S.cols → qEq (u c) (v c)) (r : Nat) :
    qEq (lin S q u r) (lin S q v r) :=
  lsum_congr S.cols (fun c hc => qmul_respects (qEq_refl _) (h c hc))

/-- The residual's SHIFT: `res(q, x) = res(ql, x) + (q − ql)·w·s(x)`. -/
theorem res_shift (R : RankOne S ql) (q : QExpr) (x : Nat → QExpr) (r : Nat) :
    qEq (res S q x r) (qadd (res S ql x r) (qmul (qmul (qsub q ql) (R.w r)) (sv R x))) := by
  have e1 : qEq (lin S q x r)
      (lsum (fun c => qadd (qmul (S.A ql r c) (x c)) (qmul (qmul (qsub q ql) (R.w r)) (qmul (R.y c) (x c)))) S.cols) :=
    lsum_congr S.cols (fun c _ => qEq_trans (qmul_respects (R.hA q r c) (qEq_refl _)) (by q_ring))
  have e2 := lsum_add (fun c => qmul (S.A ql r c) (x c)) (fun c => qmul (qmul (qsub q ql) (R.w r)) (qmul (R.y c) (x c))) S.cols
  have e3 := lsum_smul (qmul (qsub q ql) (R.w r)) (fun c => qmul (R.y c) (x c)) S.cols
  have eb := R.hb q r
  show qEq (qsub (lin S q x r) (S.b q r)) (qadd (qsub (lin S ql x r) (S.b ql r)) (qmul (qmul (qsub q ql) (R.w r)) (qsub (dotY R x) R.β)))
  have e4 : qEq (lin S q x r) (qadd (lin S ql x r) (qmul (qmul (qsub q ql) (R.w r)) (dotY R x))) :=
    qEq_trans e1 (qEq_trans e2 (qadd_respects (qEq_refl _) e3))
  refine qEq_trans (qadd_respects e4 (qneg_respects eb)) ?_
  unfold qsub; q_ring

/-- Linearity: `lin(q, a·u − b·v) = a·lin(q, u) − b·lin(q, v)`. -/
theorem lin_comb (q : QExpr) (a b : QExpr) (u v : Nat → QExpr) (r : Nat) :
    qEq (lin S q (fun c => qsub (qmul a (u c)) (qmul b (v c))) r) (qsub (qmul a (lin S q u r)) (qmul b (lin S q v r))) := by
  have e1 : qEq (lin S q (fun c => qsub (qmul a (u c)) (qmul b (v c))) r)
      (lsum (fun c => qadd (qmul a (qmul (S.A q r c) (u c))) (qneg (qmul b (qmul (S.A q r c) (v c))))) S.cols) :=
    lsum_congr S.cols (fun c _ => by unfold qsub; q_ring)
  have e2 := lsum_add (fun c => qmul a (qmul (S.A q r c) (u c))) (fun c => qneg (qmul b (qmul (S.A q r c) (v c)))) S.cols
  have e3 := lsum_smul a (fun c => qmul (S.A q r c) (u c)) S.cols
  have e4 := lsum_neg (fun c => qmul b (qmul (S.A q r c) (v c))) S.cols
  have e5 := lsum_smul b (fun c => qmul (S.A q r c) (v c)) S.cols
  refine qEq_trans e1 (qEq_trans e2 ?_)
  show qEq (qadd _ _) (qadd (qmul a (lin S q u r)) (qneg (qmul b (lin S q v r))))
  exact qadd_respects e3 (qEq_trans e4 (qneg_respects e5))

/-- `lin(q, x − x') = res(q, x) − res(q, x')`. -/
theorem lin_diff (q : QExpr) (x x' : Nat → QExpr) (r : Nat) :
    qEq (lin S q (fun c => qsub (qmul qone (x c)) (qmul qone (x' c))) r) (qsub (res S q x r) (res S q x' r)) := by
  refine qEq_trans (lin_comb q qone qone x x' r) ?_
  unfold res qsub; q_ring

/-- Uniqueness makes the kernel trivial: `lin(ql, k) = 0` on every row gives `k = 0` on the columns. -/
theorem kernel_zero (hU : Unique S ql) {x0 : Nat → QExpr} (h0 : Solves S ql x0) (k : Nat → QExpr)
    (hk : ∀ r, r ∈ S.rows → qEq (lin S ql k r) qzero) : ∀ c, c ∈ S.cols → qEq (k c) qzero := by
  have hs : Solves S ql (fun c => qadd (x0 c) (k c)) := by
    intro r hr
    have e : qEq (lin S ql (fun c => qadd (x0 c) (k c)) r) (qadd (lin S ql x0 r) (lin S ql k r)) := by
      have e1 : qEq (lin S ql (fun c => qadd (x0 c) (k c)) r)
          (lsum (fun c => qadd (qmul (S.A ql r c) (x0 c)) (qmul (S.A ql r c) (k c))) S.cols) :=
        lsum_congr S.cols (fun c _ => by q_ring)
      exact qEq_trans e1 (lsum_add _ _ S.cols)
    have h1 := h0 r hr
    have h2 := hk r hr
    show qEq (qsub (lin S ql (fun c => qadd (x0 c) (k c)) r) (S.b ql r)) qzero
    have h1' : qEq (qsub (lin S ql x0 r) (S.b ql r)) qzero := h1
    refine qEq_trans (qadd_respects e (qEq_refl _)) ?_
    unfold qsub at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  intro c hc
  have := hU _ _ hs h0 c hc
  show qEq (k c) qzero
  have e : qEq (qadd (x0 c) (k c)) (x0 c) := this
  exact qle_antisymm (by rat_linarith) (by rat_linarith)


/-! ## Small field facts on pre-rationals -/

theorem ne_zero_of_pos {P : QExpr} (h : qlt qzero P) : ¬ qEq P qzero :=
  fun e => qlt_irrefl _ (qlt_respects (qEq_refl _) e h)

theorem mul_ne_zero {a b : QExpr} (ha : ¬ qEq a qzero) (hb : ¬ qEq b qzero) : ¬ qEq (qmul a b) qzero := by
  intro h
  apply hb
  have i := qmul_inv'_cancel ha
  have e1 : qEq b (qmul (qmul a (qinv' a)) b) := qEq_trans (qEq_symm (qone_mul b)) (qmul_respects (qEq_symm i) (qEq_refl b))
  have e2 : qEq (qmul (qmul a (qinv' a)) b) (qmul (qinv' a) (qmul a b)) := by q_ring
  exact qEq_trans e1 (qEq_trans e2 (qEq_trans (qmul_respects (qEq_refl _) h) (qmul_zero _)))

theorem cancel_left {C a b : QExpr} (hC : ¬ qEq C qzero) (h : qEq (qmul C a) (qmul C b)) : qEq a b := by
  have i := qmul_inv'_cancel hC
  have e1 : qEq a (qmul (qinv' C) (qmul C a)) :=
    qEq_trans (qEq_symm (qone_mul a)) (qEq_trans (qmul_respects (qEq_symm i) (qEq_refl a)) (by q_ring))
  have e2 : qEq (qmul (qinv' C) (qmul C b)) b :=
    qEq_trans (by q_ring : qEq (qmul (qinv' C) (qmul C b)) (qmul (qmul C (qinv' C)) b)) (qEq_trans (qmul_respects i (qEq_refl b)) (qone_mul b))
  exact qEq_trans e1 (qEq_trans (qmul_respects (qEq_refl _) h) e2)

theorem nonneg_of_pos_mul {P d : QExpr} (hP : qlt qzero P) (h : qle qzero (qmul P d)) : qle qzero d := by
  have i := qmul_inv'_cancel (ne_zero_of_pos hP)
  have e : qEq (qmul (qinv' P) (qmul P d)) d :=
    qEq_trans (by q_ring : qEq (qmul (qinv' P) (qmul P d)) (qmul (qmul P (qinv' P)) d)) (qEq_trans (qmul_respects i (qEq_refl d)) (qone_mul d))
  exact qle_respects (qEq_refl _) e (qmul_nonneg (qinv'_nonneg_of_pos hP) h)

/-! ## Part 2: the two-point formula and monotonicity -/

/-- `Σ g·(a·(x − x'))`. -/
theorem lsum_comb (g x x' : Nat → QExpr) (a : QExpr) : ∀ l : List Nat,
    qEq (lsum (fun c => qmul (g c) (qmul a (qsub (x c) (x' c)))) l)
      (qmul a (qsub (lsum (fun c => qmul (g c) (x c)) l) (lsum (fun c => qmul (g c) (x' c)) l)))
  | [] => by show qEq qzero (qmul a (qsub qzero qzero)); unfold qsub; q_ring
  | c :: l => by
      have ih := lsum_comb g x x' a l
      show qEq (qadd (qmul (g c) (qmul a (qsub (x c) (x' c)))) (lsum (fun c => qmul (g c) (qmul a (qsub (x c) (x' c)))) l))
        (qmul a (qsub (qadd (qmul (g c) (x c)) (lsum (fun c => qmul (g c) (x c)) l)) (qadd (qmul (g c) (x' c)) (lsum (fun c => qmul (g c) (x' c)) l))))
      refine qEq_trans (qadd_respects (qEq_refl _) ih) ?_
      unfold qsub; q_ring

/-- `lin(q, a·(u − x0) − b·(v − x0)) = a·(res(q,u) − res(q,x0)) − b·(res(q,v) − res(q,x0))`. -/
theorem lin_two (q a b : QExpr) (u v x0 : Nat → QExpr) (r : Nat) :
    qEq (lin S q (fun c => qsub (qmul a (qsub (u c) (x0 c))) (qmul b (qsub (v c) (x0 c)))) r)
      (qsub (qmul a (qsub (res S q u r) (res S q x0 r))) (qmul b (qsub (res S q v r) (res S q x0 r)))) := by
  have e1 := lsum_comb (fun c => S.A q r c) u x0 a S.cols
  have e2 := lsum_comb (fun c => S.A q r c) v x0 b S.cols
  have e0 : qEq (lin S q (fun c => qsub (qmul a (qsub (u c) (x0 c))) (qmul b (qsub (v c) (x0 c)))) r)
      (lsum (fun c => qadd (qmul (S.A q r c) (qmul a (qsub (u c) (x0 c)))) (qneg (qmul (S.A q r c) (qmul b (qsub (v c) (x0 c)))))) S.cols) :=
    lsum_congr S.cols (fun c _ => by unfold qsub; q_ring)
  have e3 := lsum_add (fun c => qmul (S.A q r c) (qmul a (qsub (u c) (x0 c)))) (fun c => qneg (qmul (S.A q r c) (qmul b (qsub (v c) (x0 c))))) S.cols
  have e4 := lsum_neg (fun c => qmul (S.A q r c) (qmul b (qsub (v c) (x0 c)))) S.cols
  refine qEq_trans e0 (qEq_trans e3 ?_)
  refine qEq_trans (qadd_respects e1 (qEq_trans e4 (qneg_respects e2))) ?_
  unfold res lin qsub; q_ring

/-- `a − b = 0` gives `a = b`. -/
theorem eq_of_sub_zero {a b : QExpr} (h : qEq (qsub a b) qzero) : qEq a b :=
  qEq_trans (by unfold qsub; q_ring : qEq a (qadd (qsub a b) b)) (qEq_trans (qadd_respects h (qEq_refl b)) (by q_ring))

/-- Opposite signs put a root between: `e1·e2 < 0` gives `λ ∈ [0, 1]` with `λ·(e1 − e2) = e1`. -/
theorem root_between {e1 e2 : QExpr} (hn : qlt (qmul e1 e2) qzero) :
    ∃ lam, qle qzero lam ∧ qle qzero (qsub qone lam) ∧ qEq (qmul lam (qsub e1 e2)) e1 := by
  have n1 : ¬ qEq e1 qzero := fun h => qlt_irrefl _ (qlt_respects (qEq_trans (qmul_respects h (qEq_refl _)) (qzero_mul _)) (qEq_refl _) hn)
  have hd : ¬ qEq (qsub e1 e2) qzero := by
    intro h
    have e12 : qEq e1 e2 := eq_of_sub_zero h
    have p := qmul_self_pos n1
    have p' : qlt qzero (qmul e1 e2) := qlt_respects (qEq_refl _) (qmul_respects (qEq_refl _) e12) p
    exact (qlt_iff_le_not_le.mp hn).2 (qle_of_qlt p')
  have i := qmul_inv'_cancel hd
  have pd := qmul_self_nonneg (qinv' (qsub e1 e2))
  have hn' := qle_of_qlt hn
  have s1 := qmul_self_nonneg e1
  have s2 := qmul_self_nonneg e2
  have a1 : qle qzero (qmul e1 (qsub e1 e2)) := by
    have e : qEq (qmul e1 (qsub e1 e2)) (qadd (qmul e1 e1) (qneg (qmul e1 e2))) := by unfold qsub; q_ring
    exact qle_respects (qEq_refl _) (qEq_symm e) (by rat_linarith)
  have a2 : qle qzero (qmul (qneg e2) (qsub e1 e2)) := by
    have e : qEq (qmul (qneg e2) (qsub e1 e2)) (qadd (qmul e2 e2) (qneg (qmul e1 e2))) := by unfold qsub; q_ring
    exact qle_respects (qEq_refl _) (qEq_symm e) (by rat_linarith)
  refine ⟨qmul e1 (qinv' (qsub e1 e2)), ?_, ?_, ?_⟩
  · have l1 : qEq (qmul (qmul e1 (qsub e1 e2)) (qmul (qinv' (qsub e1 e2)) (qinv' (qsub e1 e2))))
        (qmul (qmul e1 (qinv' (qsub e1 e2))) (qmul (qsub e1 e2) (qinv' (qsub e1 e2)))) := by q_ring
    have l2 := qEq_trans l1 (qEq_trans (qmul_respects (qEq_refl _) i) (qmul_one _))
    exact qle_respects (qEq_refl _) l2 (qmul_nonneg a1 pd)
  · have l1 : qEq (qmul (qmul (qneg e2) (qsub e1 e2)) (qmul (qinv' (qsub e1 e2)) (qinv' (qsub e1 e2))))
        (qsub (qmul (qmul (qsub e1 e2) (qinv' (qsub e1 e2))) (qmul (qsub e1 e2) (qinv' (qsub e1 e2))))
          (qmul (qmul e1 (qinv' (qsub e1 e2))) (qmul (qsub e1 e2) (qinv' (qsub e1 e2))))) := by
      unfold qsub; q_ring
    have l2 : qEq (qsub (qmul (qmul (qsub e1 e2) (qinv' (qsub e1 e2))) (qmul (qsub e1 e2) (qinv' (qsub e1 e2))))
          (qmul (qmul e1 (qinv' (qsub e1 e2))) (qmul (qsub e1 e2) (qinv' (qsub e1 e2)))))
        (qsub qone (qmul e1 (qinv' (qsub e1 e2)))) :=
      qadd_respects (qEq_trans (qmul_respects i i) (qmul_one _)) (qneg_respects (qEq_trans (qmul_respects (qEq_refl _) i) (qmul_one _)))
    exact qle_respects (qEq_refl _) (qEq_trans l1 l2) (qmul_nonneg a2 pd)
  · exact qEq_trans (by q_ring : qEq (qmul (qmul e1 (qinv' (qsub e1 e2))) (qsub e1 e2)) (qmul e1 (qmul (qsub e1 e2) (qinv' (qsub e1 e2)))))
      (qEq_trans (qmul_respects (qEq_refl _) i) (qmul_one _))

section Box
variable (R : RankOne S ql) {qh : QExpr} (xs : QExpr → Nat → QExpr)
  (hsol : ∀ q, qle ql q → qle q qh → Solves S q (xs q))
  (hU : ∀ q, qle ql q → qle q qh → Unique S q)
include R hsol hU

/-- `s(q) = y·xs(q) − β`. -/
def sq (q : QExpr) : QExpr := sv R (xs q)
/-- `τ(q) = (ql − q)·s(q)`. -/
def tau (q : QExpr) : QExpr := qmul (qsub ql q) (sq R xs q)

omit hU in
/-- At `ql`, the residual of `xs(q)` is `τ(q)·w`. -/
theorem res_ql {q : QExpr} (h1 : qle ql q) (h2 : qle q qh) (r : Nat) (hr : r ∈ S.rows) :
    qEq (res S ql (xs q) r) (qmul (tau R xs q) (R.w r)) := by
  have e := res_shift R q (xs q) r
  have z := hsol q h1 h2 r hr
  show qEq (res S ql (xs q) r) (qmul (qmul (qsub ql q) (sv R (xs q))) (R.w r))
  have e' : qEq (qadd (res S ql (xs q) r) (qmul (qmul (qsub q ql) (R.w r)) (sv R (xs q)))) qzero := qEq_trans (qEq_symm e) z
  have k : qEq (qmul (qmul (qsub ql q) (sv R (xs q))) (R.w r)) (qneg (qmul (qmul (qsub q ql) (R.w r)) (sv R (xs q)))) := by
    unfold qsub; q_ring
  refine qEq_trans ?_ (qEq_symm k)
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE TWO-POINT FORMULA: `τ(qh)·(xs(q) − xs(ql)) = τ(q)·(xs(qh) − xs(ql))` on the columns. -/
theorem two_point (hle : qle ql qh) {q : QExpr} (h1 : qle ql q) (h2 : qle q qh) :
    ∀ c, c ∈ S.cols → qEq (qmul (tau R xs qh) (qsub (xs q c) (xs ql c))) (qmul (tau R xs q) (qsub (xs qh c) (xs ql c))) := by
  have hq0 := hsol ql (qle_refl _) hle
  have hk := kernel_zero (hU ql (qle_refl _) hle) hq0
    (fun c => qsub (qmul (tau R xs qh) (qsub (xs q c) (xs ql c))) (qmul (tau R xs q) (qsub (xs qh c) (xs ql c))))
    (fun r hr => by
      refine qEq_trans (lin_two ql (tau R xs qh) (tau R xs q) (xs q) (xs qh) (xs ql) r) ?_
      have a1 := res_ql R xs hsol h1 h2 r hr
      have a2 := res_ql R xs hsol hle (qle_refl _) r hr
      have a0 := hq0 r hr
      refine qEq_trans (qadd_respects (qmul_respects (qEq_refl _) (qadd_respects a1 (qneg_respects a0)))
        (qneg_respects (qmul_respects (qEq_refl _) (qadd_respects a2 (qneg_respects a0))))) ?_
      q_ring)
  intro c hc
  exact eq_of_sub_zero (hk c hc)

/-- Dotted with `y`: `τ(qh)·(s(q) − s(ql)) = τ(q)·(s(qh) − s(ql))`. -/
theorem two_point_s (hle : qle ql qh) {q : QExpr} (h1 : qle ql q) (h2 : qle q qh) :
    qEq (qmul (tau R xs qh) (qsub (sq R xs q) (sq R xs ql))) (qmul (tau R xs q) (qsub (sq R xs qh) (sq R xs ql))) := by
  have tp := two_point R xs hsol hU hle h1 h2
  have e1 := lsum_comb R.y (xs q) (xs ql) (tau R xs qh) S.cols
  have e2 := lsum_comb R.y (xs qh) (xs ql) (tau R xs q) S.cols
  have ec : qEq (lsum (fun c => qmul (R.y c) (qmul (tau R xs qh) (qsub (xs q c) (xs ql c)))) S.cols)
      (lsum (fun c => qmul (R.y c) (qmul (tau R xs q) (qsub (xs qh c) (xs ql c)))) S.cols) :=
    lsum_congr S.cols (fun c hc => qmul_respects (qEq_refl _) (tp c hc))
  have m := qEq_trans (qEq_symm e1) (qEq_trans ec e2)
  show qEq (qmul (tau R xs qh) (qsub (qsub (dotY R (xs q)) R.β) (qsub (dotY R (xs ql)) R.β)))
    (qmul (tau R xs q) (qsub (qsub (dotY R (xs qh)) R.β) (qsub (dotY R (xs ql)) R.β)))
  have k1 : qEq (qmul (tau R xs qh) (qsub (qsub (dotY R (xs q)) R.β) (qsub (dotY R (xs ql)) R.β)))
      (qmul (tau R xs qh) (qsub (dotY R (xs q)) (dotY R (xs ql)))) := by unfold qsub; q_ring
  have k2 : qEq (qmul (tau R xs q) (qsub (qsub (dotY R (xs qh)) R.β) (qsub (dotY R (xs ql)) R.β)))
      (qmul (tau R xs q) (qsub (dotY R (xs qh)) (dotY R (xs ql)))) := by unfold qsub; q_ring
  exact qEq_trans k1 (qEq_trans m (qEq_symm k2))

/-! ## Part 3: the sign of `e`, and monotonicity -/

/-- `e(q) = τ(qh) + (q − ql)·(s(qh) − s(ql))`. -/
def ee (qh' q : QExpr) : QExpr := qadd (tau R xs qh') (qmul (qsub q ql) (qsub (sq R xs qh') (sq R xs ql)))

theorem s_e (hle : qle ql qh) {q : QExpr} (h1 : qle ql q) (h2 : qle q qh) :
    qEq (qmul (sq R xs q) (ee R xs qh q)) (qmul (tau R xs qh) (sq R xs ql)) := by
  have t := two_point_s R xs hsol hU hle h1 h2
  have k : qEq (qmul (sq R xs q) (ee R xs qh q))
      (qadd (qmul (tau R xs qh) (sq R xs ql))
        (qsub (qmul (tau R xs qh) (qsub (sq R xs q) (sq R xs ql))) (qmul (tau R xs q) (qsub (sq R xs qh) (sq R xs ql))))) := by
    unfold ee tau qsub; q_ring
  refine qEq_trans k ?_
  have z : qEq (qsub (qmul (tau R xs qh) (qsub (sq R xs q) (sq R xs ql))) (qmul (tau R xs q) (qsub (sq R xs qh) (sq R xs ql)))) qzero := by
    refine qEq_trans (qadd_respects t (qEq_refl _)) ?_; exact qadd_neg _
  exact qEq_trans (qadd_respects (qEq_refl _) z) (by q_ring)

/-- With `s(ql) ≠ 0`, `s(q) ≠ 0` on the box (else `xs(q)` would solve at `ql`, so equal `xs(ql)`). -/
theorem s_ne (hle : qle ql qh) (h0 : ¬ qEq (sq R xs ql) qzero) {q : QExpr} (h1 : qle ql q) (h2 : qle q qh) :
    ¬ qEq (sq R xs q) qzero := by
  intro hs
  apply h0
  have sol : Solves S ql (xs q) := fun r hr => by
    refine qEq_trans (res_ql R xs hsol h1 h2 r hr) ?_
    show qEq (qmul (qmul (qsub ql q) (sq R xs q)) (R.w r)) qzero
    exact qEq_trans (qmul_respects (qmul_respects (qEq_refl _) hs) (qEq_refl _)) (by q_ring)
  have same := hU ql (qle_refl _) hle (xs q) (xs ql) sol (hsol ql (qle_refl _) hle)
  have d : qEq (dotY R (xs q)) (dotY R (xs ql)) := lsum_congr S.cols (fun c hc => qmul_respects (qEq_refl _) (same c hc))
  have e : qEq (sq R xs q) (sq R xs ql) := qadd_respects d (qEq_refl _)
  exact qEq_trans (qEq_symm e) hs

theorem e_ne (hle : qle ql qh) (hC : ¬ qEq (tau R xs qh) qzero) (h0 : ¬ qEq (sq R xs ql) qzero) {q : QExpr}
    (h1 : qle ql q) (h2 : qle q qh) : ¬ qEq (ee R xs qh q) qzero := by
  intro he
  apply mul_ne_zero hC h0
  exact qEq_trans (qEq_symm (s_e R xs hsol hU hle h1 h2)) (qEq_trans (qmul_respects (qEq_refl _) he) (qmul_zero _))

/-- `e` keeps ONE SIGN on the box: a sign change would put a root of the affine `e` inside it. -/
theorem e_prod_pos (hle : qle ql qh) (hC : ¬ qEq (tau R xs qh) qzero) (h0 : ¬ qEq (sq R xs ql) qzero)
    {q1 q2 : QExpr} (h1 : qle ql q1) (h12 : qle q1 q2) (h2 : qle q2 qh) :
    qlt qzero (qmul (ee R xs qh q1) (ee R xs qh q2)) := by
  have hq1h : qle q1 qh := qle_trans h12 h2
  have hlq2 : qle ql q2 := qle_trans h1 h12
  have n1 := e_ne R xs hsol hU hle hC h0 h1 hq1h
  have n2 := e_ne R xs hsol hU hle hC h0 hlq2 h2
  rcases qlt_trichotomy qzero (qmul (ee R xs qh q1) (ee R xs qh q2)) with hp | hz | hn
  · exact hp
  · exact absurd (qEq_symm hz) (mul_ne_zero n1 n2)
  · exfalso
    obtain ⟨lam, l0, l1, hl⟩ := root_between hn
    have hq : qle qzero (qsub q2 q1) := by unfold qsub; rat_linarith
    have s1 := qmul_nonneg l0 hq
    have s2 := qmul_nonneg l1 hq
    have e2' : qEq (qmul (qsub qone lam) (qsub q2 q1)) (qsub (qsub q2 q1) (qmul lam (qsub q2 q1))) := by unfold qsub; q_ring
    have s2' := qle_respects (qEq_refl _) e2' s2
    have qs1 : qle ql (qadd q1 (qmul lam (qsub q2 q1))) := by rat_linarith
    have qs2 : qle (qadd q1 (qmul lam (qsub q2 q1))) qh := by unfold qsub at s2' hq ⊢; rat_linarith
    apply e_ne R xs hsol hU hle hC h0 qs1 qs2
    -- e(q*) = e1 + λ(q2 − q1)T = e1 − λ(e1 − e2) = e1 − e1 = 0
    have k : qEq (ee R xs qh (qadd q1 (qmul lam (qsub q2 q1))))
        (qsub (ee R xs qh q1) (qmul lam (qsub (ee R xs qh q1) (ee R xs qh q2)))) := by
      unfold ee qsub; q_ring
    refine qEq_trans k ?_
    refine qEq_trans (qadd_respects (qEq_refl _) (qneg_respects hl)) ?_
    exact qadd_neg _

/-- THE IDENTITY: `e(q1)e(q2)·(xs(q2) − xs(q1))ᵢ = K·(q2 − q1)`, `K = −τ(qh)·s(ql)·(xs(qh) − xs(ql))ᵢ`. -/
theorem main_identity (hle : qle ql qh) (hC : ¬ qEq (tau R xs qh) qzero) {i : Nat} (hi : i ∈ S.cols)
    {q1 q2 : QExpr} (h1 : qle ql q1) (h1h : qle q1 qh) (h2l : qle ql q2) (h2 : qle q2 qh) :
    qEq (qmul (qmul (ee R xs qh q1) (ee R xs qh q2)) (qsub (xs q2 i) (xs q1 i)))
      (qmul (qneg (qmul (qmul (tau R xs qh) (sq R xs ql)) (qsub (xs qh i) (xs ql i)))) (qsub q2 q1)) := by
  apply cancel_left hC
  have F1 := two_point R xs hsol hU hle h1 h1h i hi
  have F2 := two_point R xs hsol hU hle h2l h2 i hi
  have G1 : qEq (qmul (tau R xs q1) (ee R xs qh q1)) (qmul (qsub ql q1) (qmul (tau R xs qh) (sq R xs ql))) := by
    have := s_e R xs hsol hU hle h1 h1h
    refine qEq_trans (by unfold tau; q_ring : qEq (qmul (tau R xs q1) (ee R xs qh q1)) (qmul (qsub ql q1) (qmul (sq R xs q1) (ee R xs qh q1)))) ?_
    exact qmul_respects (qEq_refl _) this
  have G2 : qEq (qmul (tau R xs q2) (ee R xs qh q2)) (qmul (qsub ql q2) (qmul (tau R xs qh) (sq R xs ql))) := by
    have := s_e R xs hsol hU hle h2l h2
    refine qEq_trans (by unfold tau; q_ring : qEq (qmul (tau R xs q2) (ee R xs qh q2)) (qmul (qsub ql q2) (qmul (sq R xs q2) (ee R xs qh q2)))) ?_
    exact qmul_respects (qEq_refl _) this
  -- C·e1e2·(X2 − X1) = e1e2·(C(X2 − X0) − C(X1 − X0)) = e1e2·(τ2 − τ1)·U = e1·U·(τ2e2) − e2·U·(τ1e1)
  have k1 : qEq (qmul (tau R xs qh) (qmul (qmul (ee R xs qh q1) (ee R xs qh q2)) (qsub (xs q2 i) (xs q1 i))))
      (qmul (qmul (ee R xs qh q1) (ee R xs qh q2))
        (qsub (qmul (tau R xs qh) (qsub (xs q2 i) (xs ql i))) (qmul (tau R xs qh) (qsub (xs q1 i) (xs ql i))))) := by
    unfold qsub; q_ring
  have k2 := qmul_respects (qEq_refl (qmul (ee R xs qh q1) (ee R xs qh q2))) (qadd_respects F2 (qneg_respects F1))
  have k3 : qEq (qmul (qmul (ee R xs qh q1) (ee R xs qh q2))
        (qsub (qmul (tau R xs q2) (qsub (xs qh i) (xs ql i))) (qmul (tau R xs q1) (qsub (xs qh i) (xs ql i)))))
      (qsub (qmul (qmul (ee R xs qh q1) (qsub (xs qh i) (xs ql i))) (qmul (tau R xs q2) (ee R xs qh q2)))
        (qmul (qmul (ee R xs qh q2) (qsub (xs qh i) (xs ql i))) (qmul (tau R xs q1) (ee R xs qh q1)))) := by
    unfold qsub; q_ring
  have k4 := qadd_respects (qmul_respects (qEq_refl (qmul (ee R xs qh q1) (qsub (xs qh i) (xs ql i)))) G2)
    (qneg_respects (qmul_respects (qEq_refl (qmul (ee R xs qh q2) (qsub (xs qh i) (xs ql i)))) G1))
  have k5 : qEq (qsub (qmul (qmul (ee R xs qh q1) (qsub (xs qh i) (xs ql i))) (qmul (qsub ql q2) (qmul (tau R xs qh) (sq R xs ql))))
        (qmul (qmul (ee R xs qh q2) (qsub (xs qh i) (xs ql i))) (qmul (qsub ql q1) (qmul (tau R xs qh) (sq R xs ql)))))
      (qmul (tau R xs qh) (qmul (qneg (qmul (qmul (tau R xs qh) (sq R xs ql)) (qsub (xs qh i) (xs ql i)))) (qsub q2 q1))) := by
    unfold ee qsub; q_ring
  exact qEq_trans k1 (qEq_trans k2 (qEq_trans k3 (qEq_trans k4 k5)))

/-- When `xs(ql)` already solves at every `q` (or the box is a point), the coordinate is CONSTANT. -/
theorem const_of_solves (hle : qle ql qh) (h : ∀ q, qle ql q → qle q qh → Solves S q (xs ql)) {i : Nat} (hi : i ∈ S.cols)
    {q : QExpr} (h1 : qle ql q) (h2 : qle q qh) : qEq (xs q i) (xs ql i) :=
  hU q h1 h2 (xs q) (xs ql) (hsol q h1 h2) (h q h1 h2) i hi

/-- **RANK ONE ⇒ MONOTONE.** Every coordinate of the solution is monotone in `q` on `[ql, qh]`. -/
theorem rank_one_monotone (hle : qle ql qh) (i : Nat) (hi : i ∈ S.cols) :
    (∀ q1 q2, qle ql q1 → qle q1 q2 → qle q2 qh → qle (xs q1 i) (xs q2 i)) ∨
    (∀ q1 q2, qle ql q1 → qle q1 q2 → qle q2 qh → qle (xs q2 i) (xs q1 i)) := by
  have const_left : (∀ q, qle ql q → qle q qh → qEq (xs q i) (xs ql i)) →
      (∀ q1 q2, qle ql q1 → qle q1 q2 → qle q2 qh → qle (xs q1 i) (xs q2 i)) ∨
      (∀ q1 q2, qle ql q1 → qle q1 q2 → qle q2 qh → qle (xs q2 i) (xs q1 i)) := fun hc =>
    Or.inl (fun q1 q2 h1 h12 h2 => by
      have a := hc q1 h1 (qle_trans h12 h2)
      have b := hc q2 (qle_trans h1 h12) h2
      exact qle_respects (qEq_symm a) (qEq_symm b) (qle_refl _))
  cases (inferInstance : Decidable (qEq (sq R xs ql) qzero)) with
  | isTrue h0 =>
      -- s(ql) = 0: xs(ql) solves at every q
      apply const_left
      intro q h1 h2
      refine const_of_solves R xs hsol hU hle (fun q' _ _ r hr => ?_) hi h1 h2
      have e := res_shift R q' (xs ql) r
      have z := hsol ql (qle_refl _) hle r hr
      refine qEq_trans e ?_
      have : qEq (qmul (qmul (qsub q' ql) (R.w r)) (sv R (xs ql))) qzero :=
        qEq_trans (qmul_respects (qEq_refl _) h0) (qmul_zero _)
      exact qEq_trans (qadd_respects z this) (by q_ring)
  | isFalse h0 =>
      cases (inferInstance : Decidable (qEq ql qh)) with
      | isTrue hq =>
          -- the box is a point: xs(q) solves at ql
          apply const_left
          intro q h1 h2
          have hq' : qEq (qsub ql q) qzero := by
            have := qle_antisymm h1 (qle_respects (qEq_refl _) (qEq_symm hq) h2)
            exact qEq_trans (qadd_respects this (qEq_refl _)) (qadd_neg _)
          have sol : Solves S ql (xs q) := fun r hr => by
            refine qEq_trans (res_ql R xs hsol h1 h2 r hr) ?_
            show qEq (qmul (qmul (qsub ql q) (sq R xs q)) (R.w r)) qzero
            exact qEq_trans (qmul_respects (qmul_respects hq' (qEq_refl _)) (qEq_refl _)) (by q_ring)
          exact hU ql (qle_refl _) hle (xs q) (xs ql) sol (hsol ql (qle_refl _) hle) i hi
      | isFalse hq =>
          have hlh : ¬ qEq (qsub ql qh) qzero := fun h => hq (eq_of_sub_zero h)
          have hC : ¬ qEq (tau R xs qh) qzero := mul_ne_zero hlh (s_ne R xs hsol hU hle h0 hle (qle_refl _))
          cases qle_total qzero (qneg (qmul (qmul (tau R xs qh) (sq R xs ql)) (qsub (xs qh i) (xs ql i)))) with
          | inl hK =>
              refine Or.inl (fun q1 q2 h1 h12 h2 => ?_)
              have hP := e_prod_pos R xs hsol hU hle hC h0 h1 h12 h2
              have I := main_identity R xs hsol hU hle hC hi h1 (qle_trans h12 h2) (qle_trans h1 h12) h2
              have hq0 : qle qzero (qsub q2 q1) := by unfold qsub; rat_linarith
              have n := nonneg_of_pos_mul hP (qle_respects (qEq_refl _) (qEq_symm I) (qmul_nonneg hK hq0))
              unfold qsub at n; rat_linarith
          | inr hK =>
              refine Or.inr (fun q1 q2 h1 h12 h2 => ?_)
              have hP := e_prod_pos R xs hsol hU hle hC h0 h1 h12 h2
              have I := main_identity R xs hsol hU hle hC hi h1 (qle_trans h12 h2) (qle_trans h1 h12) h2
              have hq0 : qle qzero (qsub q2 q1) := by unfold qsub; rat_linarith
              have nK : qle qzero (qneg (qneg (qmul (qmul (tau R xs qh) (sq R xs ql)) (qsub (xs qh i) (xs ql i))))) := by rat_linarith
              have m := qmul_nonneg nK hq0
              have I' : qEq (qmul (qmul (ee R xs qh q1) (ee R xs qh q2)) (qsub (xs q1 i) (xs q2 i)))
                  (qmul (qneg (qneg (qmul (qmul (tau R xs qh) (sq R xs ql)) (qsub (xs qh i) (xs ql i))))) (qsub q2 q1)) := by
                refine qEq_trans (by unfold qsub; q_ring : qEq (qmul (qmul (ee R xs qh q1) (ee R xs qh q2)) (qsub (xs q1 i) (xs q2 i)))
                  (qneg (qmul (qmul (ee R xs qh q1) (ee R xs qh q2)) (qsub (xs q2 i) (xs q1 i))))) ?_
                refine qEq_trans (qneg_respects I) ?_
                q_ring
              have n := nonneg_of_pos_mul hP (qle_respects (qEq_refl _) (qEq_symm I') m)
              unfold qsub at n; rat_linarith

end Box

/-! ## Part 4: monotone in each coordinate ⇒ bounded by the corners -/

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

/-- `p` with coordinate `v` set to `t`. -/
def setc (p : Nat → QExpr) (v : Nat) (t : QExpr) : Nat → QExpr := fun j => cond (Nat.beq j v) t (p j)

theorem setc_self (p : Nat → QExpr) (v : Nat) (t : QExpr) : setc p v t v = t := by
  unfold setc
  have : Nat.beq v v = true := beq_self v
  rw [this]; rfl

theorem setc_other (p : Nat → QExpr) {v j : Nat} (t : QExpr) (h : Nat.beq j v = false) : setc p v t j = p j := by
  unfold setc; rw [h]; rfl

theorem setc_same (p : Nat → QExpr) (v : Nat) : ∀ j, qEq (setc p v (p v) j) (p j) := by
  intro j
  unfold setc
  cases h : Nat.beq j v with
  | true => have e := Nat.eq_of_beq_eq_true h; subst e; exact qEq_refl _
  | false => exact qEq_refl _

/-- The box of the coordinates `full` (a plain definition, for the section's hypotheses). -/
def InB' (lo hi : Nat → QExpr) (full : List Nat) (p : Nat → QExpr) : Prop :=
  ∀ v, v ∈ full → qle (lo v) (p v) ∧ qle (p v) (hi v)

section Corners
variable (lo hi : Nat → QExpr) (full : List Nat) (F : (Nat → QExpr) → QExpr)
  (Fc : ∀ p p' : Nat → QExpr, InB' lo hi full p → (∀ j, qEq (p j) (p' j)) → qEq (F p) (F p'))

/-- The box of the coordinates `full`. -/
def InB (p : Nat → QExpr) : Prop := InB' lo hi full p

/-- `F` is monotone in each coordinate of `full`, the others fixed (the direction may depend on them). -/
def MonoEach : Prop := ∀ v, v ∈ full → ∀ p, InB lo hi full p →
  (∀ t1 t2, qle (lo v) t1 → qle t1 t2 → qle t2 (hi v) → qle (F (setc p v t1)) (F (setc p v t2))) ∨
  (∀ t1 t2, qle (lo v) t1 → qle t1 t2 → qle t2 (hi v) → qle (F (setc p v t2)) (F (setc p v t1)))

theorem inB_setc {p : Nat → QExpr} (hp : InB lo hi full p) {v : Nat} (hv : v ∈ full) {t : QExpr}
    (h1 : qle (lo v) t) (h2 : qle t (hi v)) : InB lo hi full (setc p v t) := by
  intro u hu
  cases h : Nat.beq u v with
  | true => have e := Nat.eq_of_beq_eq_true h; subst e; rw [setc_self]; exact ⟨h1, h2⟩
  | false => rw [setc_other p t h]; exact hp u hu

/-- A corner on the coordinates `L`, agreeing with `p` off them. -/
def CornerOf (L : List Nat) (p c : Nat → QExpr) : Prop :=
  (∀ u, u ∈ L → qEq (c u) (lo u) ∨ qEq (c u) (hi u)) ∧ (∀ j, ¬ j ∈ L → qEq (c j) (p j))

include Fc in
/-- **THE CORNERS BOUND EVERY VALUE**: for every point of the box there are corners below and above it. -/
theorem corners (hM : MonoEach lo hi full F) :
    ∀ L : List Nat, (∀ v, v ∈ L → v ∈ full) → ∀ p, InB lo hi full p →
      (∃ c, InB lo hi full c ∧ CornerOf lo hi L p c ∧ qle (F c) (F p)) ∧
      (∃ c, InB lo hi full c ∧ CornerOf lo hi L p c ∧ qle (F p) (F c))
  | [], _, p, hp => ⟨⟨p, hp, ⟨(fun _ h => nomatch h), (fun _ _ => qEq_refl _)⟩, qle_refl _⟩,
                     ⟨p, hp, ⟨(fun _ h => nomatch h), (fun _ _ => qEq_refl _)⟩, qle_refl _⟩⟩
  | v :: L, hL, p, hp => by
      have hv : v ∈ full := hL v (List.Mem.head _)
      have hL' : ∀ u, u ∈ L → u ∈ full := fun u hu => hL u (List.Mem.tail _ hu)
      obtain ⟨⟨c1, hc1, ⟨k1, o1⟩, f1⟩, ⟨c2, hc2, ⟨k2, o2⟩, f2⟩⟩ := corners hM L hL' p hp
      have lh1 := hc1 v hv
      have lh2 := hc2 v hv
      have lohi1 : qle (lo v) (hi v) := qle_trans lh1.1 lh1.2
      -- move coordinate v of c to the end that does not raise (resp. lower) F
      have adjust : ∀ c, InB lo hi full c → (∀ u, u ∈ L → qEq (c u) (lo u) ∨ qEq (c u) (hi u)) →
          (∀ j, ¬ j ∈ L → qEq (c j) (p j)) →
          (∃ c', InB lo hi full c' ∧ CornerOf lo hi (v :: L) p c' ∧ qle (F c') (F c)) ∧
          (∃ c', InB lo hi full c' ∧ CornerOf lo hi (v :: L) p c' ∧ qle (F c) (F c')) := by
        intro c hc kc oc
        have lc := hc v hv
        have same := Fc _ _ (inB_setc lo hi full hc hv lc.1 lc.2) (setc_same c v)
        have corner_at : ∀ t, (qEq t (lo v) ∨ qEq t (hi v)) → CornerOf lo hi (v :: L) p (setc c v t) := by
          intro t ht
          refine ⟨fun u hu => ?_, fun j hj => ?_⟩
          · cases h : Nat.beq u v with
            | true => have e := Nat.eq_of_beq_eq_true h; subst e; rw [setc_self]; exact ht
            | false =>
                rw [setc_other c t h]
                cases hu with
                | head => rw [beq_self] at h; cases h
                | tail _ hu' => exact kc u hu'
          · have hjv : Nat.beq j v = false := by
              cases h : Nat.beq j v with
              | false => rfl
              | true => exact absurd (by have e := Nat.eq_of_beq_eq_true h; subst e; exact List.Mem.head _) hj
            rw [setc_other c t hjv]
            exact oc j (fun h' => hj (List.Mem.tail _ h'))
        have inLo := inB_setc lo hi full hc hv (qle_refl _) lohi1
        have inHi := inB_setc lo hi full hc hv lohi1 (qle_refl _)
        cases hM v hv c hc with
        | inl up =>
            exact ⟨⟨setc c v (lo v), inLo, corner_at _ (Or.inl (qEq_refl _)),
                     qle_respects (qEq_refl _) same (up _ _ (qle_refl _) lc.1 lc.2)⟩,
                   ⟨setc c v (hi v), inHi, corner_at _ (Or.inr (qEq_refl _)),
                     qle_respects same (qEq_refl _) (up _ _ lc.1 lc.2 (qle_refl _))⟩⟩
        | inr dn =>
            exact ⟨⟨setc c v (hi v), inHi, corner_at _ (Or.inr (qEq_refl _)),
                     qle_respects (qEq_refl _) same (dn _ _ lc.1 lc.2 (qle_refl _))⟩,
                   ⟨setc c v (lo v), inLo, corner_at _ (Or.inl (qEq_refl _)),
                     qle_respects same (qEq_refl _) (dn _ _ (qle_refl _) lc.1 lc.2)⟩⟩
      obtain ⟨⟨d1, hd1, cd1, g1⟩, _⟩ := adjust c1 hc1 k1 o1
      obtain ⟨_, ⟨d2, hd2, cd2, g2⟩⟩ := adjust c2 hc2 k2 o2
      exact ⟨⟨d1, hd1, cd1, qle_trans g1 f1⟩, ⟨d2, hd2, cd2, qle_trans f2 g2⟩⟩

end Corners

/-! ## Part 5: the solver's claim — the rank-one parameters read at their corners -/

section Glue
variable (rows cols : List Nat) (A : (Nat → QExpr) → Nat → Nat → QExpr) (b : (Nat → QExpr) → Nat → QExpr)

/-- The system at a point `p` of the parameters. -/
def pointSys (p : Nat → QExpr) : Sys := { rows := rows, cols := cols, A := fun _ r c => A p r c, b := fun _ r => b p r }

/-- The system along coordinate `v` through `p`: the parameter `q` is coordinate `v`. -/
def lineSys (p : Nat → QExpr) (v : Nat) : Sys :=
  { rows := rows, cols := cols, A := fun q r c => A (setc p v q) r c, b := fun q r => b (setc p v q) r }

theorem solves_congr {p p' : Nat → QExpr}
    (hA : ∀ r c, qEq (A p r c) (A p' r c)) (hb : ∀ r, qEq (b p r) (b p' r)) {x : Nat → QExpr}
    (h : Solves (pointSys rows cols A b p) qzero x) : Solves (pointSys rows cols A b p') qzero x := by
  intro r hr
  have e : qEq (res (pointSys rows cols A b p') qzero x r) (res (pointSys rows cols A b p) qzero x r) :=
    qadd_respects (lsum_congr cols (fun c _ => qmul_respects (qEq_symm (hA r c)) (qEq_refl _))) (qneg_respects (qEq_symm (hb r)))
  exact qEq_trans e (h r hr)

/-- **THE CORNER READING IS SOUND.** Every rank-one parameter `v ∈ full` enters `[A | b]` with rank one along its
line (through every point of the box), and the system has a solution `xs p`, unique, at every point `p` of the
box. Then the value of every unknown at every point of the box lies between its values at two CORNERS of the
box — so the hull of the corner solutions encloses it (and is attained: the corners are points of the box). -/
theorem rank_one_corners (lo hi : Nat → QExpr) (full : List Nat) (xs : (Nat → QExpr) → Nat → QExpr)
    (hR : ∀ v, v ∈ full → ∀ p, InB lo hi full p → RankOne (lineSys rows cols A b p v) (lo v))
    (hsol : ∀ p, InB lo hi full p → Solves (pointSys rows cols A b p) qzero (xs p))
    (hU : ∀ p, InB lo hi full p → Unique (pointSys rows cols A b p) qzero)
    (hA : ∀ p p', (∀ j, qEq (p j) (p' j)) → ∀ r c, qEq (A p r c) (A p' r c))
    (hb : ∀ p p', (∀ j, qEq (p j) (p' j)) → ∀ r, qEq (b p r) (b p' r))
    (i : Nat) (hic : i ∈ cols) (p : Nat → QExpr) (hp : InB lo hi full p) :
    (∃ c, InB lo hi full c ∧ CornerOf lo hi full p c ∧ qle (xs c i) (xs p i)) ∧
    (∃ c, InB lo hi full c ∧ CornerOf lo hi full p c ∧ qle (xs p i) (xs c i)) := by
  -- F p = (xs p)_i, extended outside the box by uniqueness only where it is used
  have hM : MonoEach lo hi full (fun p => xs p i) := by
    intro v hv p hp
    have lh := hp v hv
    exact rank_one_monotone (hR v hv p hp) (fun q => xs (setc p v q))
      (fun q h1 h2 => hsol (setc p v q) (inB_setc lo hi full hp hv h1 h2))
      (fun q h1 h2 => hU (setc p v q) (inB_setc lo hi full hp hv h1 h2))
      (qle_trans lh.1 lh.2) i hic
  -- F respects equal points of the box (uniqueness there)
  have Fc : ∀ p p' : Nat → QExpr, InB' lo hi full p → (∀ j, qEq (p j) (p' j)) → qEq (xs p i) (xs p' i) := by
    intro p p' hp he
    have hp' : InB' lo hi full p' := fun v hv =>
      ⟨qle_respects (qEq_refl _) (he v) (hp v hv).1, qle_respects (he v) (qEq_refl _) (hp v hv).2⟩
    have s' := solves_congr rows cols A b (hA p' p (fun j => qEq_symm (he j))) (hb p' p (fun j => qEq_symm (he j))) (hsol p' hp')
    exact hU p hp (xs p) (xs p') (hsol p hp) s' i hic
  exact corners lo hi full (fun p => xs p i) Fc hM full (fun v hv => hv) p hp

end Glue

/-- NONVACUITY: `(1 + q)·x = 1` (one row, one column) is rank one in `q` at `0`: `w = 1, y = 1, β = 0`. -/
def exSys : Sys := { rows := [0], cols := [0], A := fun q _ _ => qadd qone q, b := fun _ _ => qone }

def exRank : RankOne exSys qzero where
  w := fun _ => qone
  y := fun _ => qone
  β := qzero
  hA := fun q _ _ => by
    show qEq (qadd qone q) (qadd (qadd qone qzero) (qmul (qmul (qsub q qzero) qone) qone)); unfold qsub; q_ring
  hb := fun q _ => by
    show qEq qone (qadd qone (qmul (qmul (qsub q qzero) qone) qzero)); unfold qsub; q_ring

end ZRankMany

#print axioms ZRankMany.res_shift
#print axioms ZRankMany.kernel_zero
#print axioms ZRankMany.two_point
#print axioms ZRankMany.two_point_s
#print axioms ZRankMany.e_prod_pos
#print axioms ZRankMany.main_identity
#print axioms ZRankMany.rank_one_monotone
#print axioms ZRankMany.corners
#print axioms ZRankMany.rank_one_corners
#print axioms ZRankMany.exRank
