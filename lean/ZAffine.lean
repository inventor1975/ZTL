import ZDeriv

/-!
# ZAffine — the kernel's AFFINE reading, sound. Zero axioms.

`zaffine.read` reads an expression over a box as `x0 + Σ x_i·ε_i ± err`, each `ε_i ∈ [−1, 1]` one input of the box
(Comba–Stolfi): linear steps exact, a product adds `rad(x)·rad(y)`, a nonlinear function its best linear stand-in plus
a proved remainder (min-range). The kernel meets it with the plain reading; it is tighter than any `VRead`, which
only widens (measured 2026-10-17: 124 readings of the integral stand). Here the affine reading on VR's operational
reals.

A form is `c + Σ_{j<S} s_j·(z_j − m_j) ± e` over a BASIS `z_j` = the value of an expression `Γ j` (a variable of
the box, or a subtree read plainly), with centre `m_j` and radius `r_j` (`s_j = t_j/r_j` against the kernel's
`t_j`: no division in the proofs). `Enc E B f F`: at every point of the box, from some index on, whenever every
basis value is within `r_j + η` of its centre (`η ≤ η₀`), `f` is within `e + η·L + ε_k` of the form. `enc_sound`:
then `f` is eventually in `[c − R, c + R]`, `R ≥ Σ |s_j|·r_j + e`.

Part 1: forms, `Enc`, its soundness; constants, the basis, a point variable, `+`, `−`, widening (the kernel's grid
rounding), `×`.
-/

namespace ZAffine

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv

structure Env where
  Γ : Nat → G
  m : Nat → QExpr
  r : Nat → QExpr
  S : Nat

structure Form where
  c : QExpr
  s : Nat → QExpr
  e : QExpr

def lin (E : Env) (s z : Nat → QExpr) : QExpr := ZTrig.bs (fun j => qmul (s j) (qsub (z j) (E.m j))) E.S
def affv (E : Env) (F : Form) (z : Nat → QExpr) : QExpr := qadd F.c (lin E F.s z)
def zv (E : Env) (n : Nat) (p : Point QExpr) : Nat → QExpr := fun j => evalN n p (E.Γ j)
def Near (E : Env) (n : Nat) (p : Point QExpr) (η : QExpr) : Prop :=
  ∀ j, j < E.S → ZTrig.Ab (qsub (zv E n p j) (E.m j)) (qadd (E.r j) η)

/-- `f` is enclosed by the form `F`. -/
def Enc (E : Env) (B : Box QExpr) (f : Nat → Point QExpr → QExpr) (F : Form) : Prop :=
  ∃ L η0, qle qzero L ∧ qlt qzero η0 ∧ qle η0 qone ∧ ∀ p, InBox qOrd B p → ∀ k, ∃ N, ∀ n, N ≤ n → ∀ η,
    qle qzero η → qle η η0 → Near E n p η →
    ZTrig.Ab (qsub (f n p) (affv E F (zv E n p))) (qadd (qadd F.e (qmul η L)) (qeps k))

/-! ## Finite sums -/

theorem ab_add {x y a b : QExpr} (h1 : ZTrig.Ab x a) (h2 : ZTrig.Ab y b) : ZTrig.Ab (qadd x y) (qadd a b) := by
  obtain ⟨a1, a2⟩ := h1; obtain ⟨b1, b2⟩ := h2; exact ⟨by rat_linarith, by rat_linarith⟩

theorem ab_congr {x y a : QExpr} (e : qEq x y) (h : ZTrig.Ab y a) : ZTrig.Ab x a := by
  obtain ⟨a1, a2⟩ := h; exact ⟨by rat_linarith, by rat_linarith⟩

theorem ab_widen {x a b : QExpr} (h : ZTrig.Ab x a) (hab : qle a b) : ZTrig.Ab x b := by
  obtain ⟨a1, a2⟩ := h; exact ⟨by rat_linarith, by rat_linarith⟩

theorem bs_abs_lt {F A : Nat → QExpr} : ∀ N, (∀ j, j < N → ZTrig.Ab (F j) (A j)) → ZTrig.Ab (ZTrig.bs F N) (ZTrig.bs A N)
  | 0, _ => ⟨by show qle (qneg qzero) qzero; rat_linarith, qle_refl _⟩
  | N + 1, h => ab_add (bs_abs_lt N (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h N (Nat.lt_succ_self N))

theorem bs_congr_lt {F G : Nat → QExpr} : ∀ N, (∀ j, j < N → qEq (F j) (G j)) → qEq (ZTrig.bs F N) (ZTrig.bs G N)
  | 0, _ => qEq_refl _
  | N + 1, h => qadd_respects (bs_congr_lt N (fun j hj => h j (Nat.lt_succ_of_lt hj))) (h N (Nat.lt_succ_self N))

theorem bs_nonneg_lt {A : Nat → QExpr} : ∀ N, (∀ j, j < N → qle qzero (A j)) → qle qzero (ZTrig.bs A N)
  | 0, _ => qle_refl _
  | N + 1, h => by
      have a := bs_nonneg_lt N (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have b := h N (Nat.lt_succ_self N)
      show qle qzero (qadd (ZTrig.bs A N) (A N)); rat_linarith

theorem bs_le_lt {A A' : Nat → QExpr} : ∀ N, (∀ j, j < N → qle (A j) (A' j)) → qle (ZTrig.bs A N) (ZTrig.bs A' N)
  | 0, _ => qle_refl _
  | N + 1, h => by
      have a := bs_le_lt N (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have b := h N (Nat.lt_succ_self N)
      show qle (qadd (ZTrig.bs A N) (A N)) (qadd (ZTrig.bs A' N) (A' N)); rat_linarith

theorem bs_scale (c : QExpr) (F : Nat → QExpr) : ∀ N, qEq (ZTrig.bs (fun j => qmul c (F j)) N) (qmul c (ZTrig.bs F N))
  | 0 => by show qEq qzero (qmul c qzero); rat_ring
  | N + 1 => by
      have ih := bs_scale c F N
      show qEq (qadd (ZTrig.bs (fun j => qmul c (F j)) N) (qmul c (F N))) (qmul c (qadd (ZTrig.bs F N) (F N)))
      generalize ZTrig.bs (fun j => qmul c (F j)) N = X at *
      generalize ZTrig.bs F N = Y at *
      have : qEq (qmul c (qadd Y (F N))) (qadd (qmul c Y) (qmul c (F N))) := by rat_ring
      generalize qmul c Y = Z at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem bs_zero : ∀ N, qEq (ZTrig.bs (fun _ => qzero) N) qzero
  | 0 => qEq_refl _
  | N + 1 => by
      have ih := bs_zero N
      show qEq (qadd (ZTrig.bs (fun _ => qzero) N) qzero) qzero
      generalize ZTrig.bs (fun _ => qzero) N = X at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The finite `max`: a common index for finitely many "from some index on". -/
theorem fin_ev (Q : Nat → Nat → Prop) : ∀ S, (∀ j, j < S → ∃ N, ∀ n, N ≤ n → Q j n) → ∃ N, ∀ n, N ≤ n → ∀ j, j < S → Q j n
  | 0, _ => ⟨0, fun _ _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | S + 1, h => by
      obtain ⟨N1, h1⟩ := fin_ev Q S (fun j hj => h j (Nat.lt_succ_of_lt hj))
      obtain ⟨N2, h2⟩ := h S (Nat.lt_succ_self S)
      refine ⟨N1 + N2, fun n hn j hj => ?_⟩
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
      | inl l => exact h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn) j l
      | inr e => subst e; exact h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)

/-! ## The linear part -/

theorem lin_add (E : Env) (s s' z : Nat → QExpr) :
    qEq (lin E (fun j => qadd (s j) (s' j)) z) (qadd (lin E s z) (lin E s' z)) := by
  unfold lin
  refine qEq_trans (bs_congr_lt _ (fun j _ => ?_)) (ZTrig.bs_add _ _ _)
  show qEq (qmul (qadd (s j) (s' j)) (qsub (z j) (E.m j))) (qadd (qmul (s j) (qsub (z j) (E.m j))) (qmul (s' j) (qsub (z j) (E.m j))))
  rat_ring

theorem lin_sub (E : Env) (s s' z : Nat → QExpr) :
    qEq (lin E (fun j => qsub (s j) (s' j)) z) (qsub (lin E s z) (lin E s' z)) := by
  unfold lin
  refine qEq_trans (bs_congr_lt _ (fun j _ => ?_)) (ZTrig.bs_sub _ _ _)
  show qEq (qmul (qsub (s j) (s' j)) (qsub (z j) (E.m j))) (qsub (qmul (s j) (qsub (z j) (E.m j))) (qmul (s' j) (qsub (z j) (E.m j))))
  unfold qsub; rat_ring

theorem lin_scale (E : Env) (a : QExpr) (s z : Nat → QExpr) :
    qEq (lin E (fun j => qmul a (s j)) z) (qmul a (lin E s z)) := by
  unfold lin
  refine qEq_trans (bs_congr_lt _ (fun j _ => ?_)) (bs_scale a _ E.S)
  show qEq (qmul (qmul a (s j)) (qsub (z j) (E.m j))) (qmul a (qmul (s j) (qsub (z j) (E.m j))))
  rat_ring

theorem lin_zero (E : Env) (z : Nat → QExpr) : qEq (lin E (fun _ => qzero) z) qzero := by
  unfold lin
  refine qEq_trans (bs_congr_lt _ (fun j _ => ?_)) (bs_zero E.S)
  show qEq (qmul qzero (qsub (z j) (E.m j))) qzero; rat_ring

theorem bs_upd_out (w : Nat → QExpr) (j : Nat) : ∀ N, N ≤ j →
    qEq (ZTrig.bs (fun k => qmul (upd (fun _ => qzero) j qone k) (w k)) N) qzero
  | 0, _ => qEq_refl _
  | N + 1, h => by
      have ih := bs_upd_out w j N (Nat.le_of_succ_le h)
      have ne : N ≠ j := fun e => by subst e; exact Nat.lt_irrefl N h
      have u := upd_other (fun _ => qzero) j qone N ne
      show qEq (qadd (ZTrig.bs (fun k => qmul (upd (fun _ => qzero) j qone k) (w k)) N)
        (qmul (upd (fun _ => qzero) j qone N) (w N))) qzero
      rw [u]
      generalize ZTrig.bs (fun k => qmul (upd (fun _ => qzero) j qone k) (w k)) N = X at *
      have : qEq (qmul ((fun _ => qzero) N) (w N)) qzero := by show qEq (qmul qzero (w N)) qzero; rat_ring
      generalize qmul ((fun _ => qzero) N) (w N) = Y at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem bs_upd_in (w : Nat → QExpr) (j : Nat) : ∀ N, j < N →
    qEq (ZTrig.bs (fun k => qmul (upd (fun _ => qzero) j qone k) (w k)) N) (w j)
  | 0, h => absurd h (Nat.not_lt_zero j)
  | N + 1, h => by
      show qEq (qadd (ZTrig.bs (fun k => qmul (upd (fun _ => qzero) j qone k) (w k)) N)
        (qmul (upd (fun _ => qzero) j qone N) (w N))) (w j)
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with
      | inl l =>
          have ih := bs_upd_in w j N l
          have ne : N ≠ j := fun e => by subst e; exact Nat.lt_irrefl N l
          rw [upd_other (fun _ => qzero) j qone N ne]
          generalize ZTrig.bs (fun k => qmul (upd (fun _ => qzero) j qone k) (w k)) N = X at *
          have : qEq (qmul ((fun _ => qzero) N) (w N)) qzero := by show qEq (qmul qzero (w N)) qzero; rat_ring
          generalize qmul ((fun _ => qzero) N) (w N) = Y at *
          exact qle_antisymm (by rat_linarith) (by rat_linarith)
      | inr e =>
          subst e
          have z := bs_upd_out w j j (Nat.le_refl j)
          rw [upd_self]
          generalize ZTrig.bs (fun k => qmul (upd (fun _ => qzero) j qone k) (w k)) j = X at *
          have : qEq (qmul qone (w j)) (w j) := by rat_ring
          generalize qmul qone (w j) = Y at *
          exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `|Σ s_j (z_j − m_j)| ≤ Σ a_j (r_j + η)` when `|s_j| ≤ a_j` and every basis value is near. -/
theorem lin_bound {E : Env} {n : Nat} {p : Point QExpr} {η : QExpr} {s a : Nat → QExpr} (hn : Near E n p η)
    (hs : ∀ j, j < E.S → ZTrig.Ab (s j) (a j)) :
    ZTrig.Ab (lin E s (zv E n p)) (qadd (ZTrig.bs (fun j => qmul (a j) (E.r j)) E.S) (qmul η (ZTrig.bs a E.S))) := by
  have h := bs_abs_lt (F := fun j => qmul (s j) (qsub (zv E n p j) (E.m j))) (A := fun j => qmul (a j) (qadd (E.r j) η))
    E.S (fun j hj => ZTrig.mul_abs (hs j hj) (hn j hj))
  have e1 : qEq (ZTrig.bs (fun j => qmul (a j) (qadd (E.r j) η)) E.S)
      (ZTrig.bs (fun j => qadd (qmul (a j) (E.r j)) (qmul η (a j))) E.S) :=
    bs_congr_lt _ (fun j _ => by show qEq (qmul (a j) (qadd (E.r j) η)) (qadd (qmul (a j) (E.r j)) (qmul η (a j))); rat_ring)
  have e2 := ZTrig.bs_add (fun j => qmul (a j) (E.r j)) (fun j => qmul η (a j)) E.S
  have e3 := bs_scale η a E.S
  obtain ⟨h1, h2⟩ := h
  unfold lin
  generalize ZTrig.bs (fun j => qmul (s j) (qsub (zv E n p j) (E.m j))) E.S = X at *
  generalize ZTrig.bs (fun j => qmul (a j) (qadd (E.r j) η)) E.S = Y at *
  generalize ZTrig.bs (fun j => qadd (qmul (a j) (E.r j)) (qmul η (a j))) E.S = Y' at *
  generalize ZTrig.bs (fun j => qmul (a j) (E.r j)) E.S = P at *
  generalize ZTrig.bs (fun j => qmul η (a j)) E.S = Q at *
  generalize qmul η (ZTrig.bs a E.S) = Q' at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## Soundness of an enclosure -/

/-- AN ENCLOSURE BOUNDS THE VALUE: the basis read in its boxes, `|s_j| ≤ a_j`, `R ≥ Σ a_j r_j + e`. -/
theorem enc_sound {E : Env} {B : Box QExpr} {f : Nat → Point QExpr → QExpr} {F : Form} (h : Enc E B f F)
    (hb : ∀ j, j < E.S → BoxEv B (E.Γ j) (qsub (E.m j) (E.r j)) (qadd (E.m j) (E.r j)))
    {a : Nat → QExpr} (ha : ∀ j, j < E.S → ZTrig.Ab (F.s j) (a j)) {R : QExpr}
    (hR : qle (qadd (ZTrig.bs (fun j => qmul (a j) (E.r j)) E.S) F.e) R) :
    ∀ p, InBox qOrd B p → Ev (fun n => f n p) (qsub F.c R) (qadd F.c R) := by
  obtain ⟨L, η0, L0, η0p, η01, hf⟩ := h
  intro p hp k
  have a0 : qle qzero (ZTrig.bs a E.S) := bs_nonneg_lt _ (fun j hj => by obtain ⟨x1, x2⟩ := ha j hj; rat_linarith)
  obtain ⟨Bc, hBc⟩ := eps_scaled (C := qadd (qadd L (ZTrig.bs a E.S)) qone) (by have := qle_of_qlt qone_pos; rat_linarith)
  obtain ⟨Bη, hBη⟩ := ZTrig.pos_floor η0p
  -- the working precision: below η₀, and scaled
  obtain ⟨N1, h1⟩ := fin_ev (fun j n => ZTrig.Ab (qsub (zv E n p j) (E.m j)) (qadd (E.r j) (qeps (k + Bc + Bη)))) E.S
    (fun j hj => by
      obtain ⟨N, hN⟩ := hb j hj p hp (k + Bc + Bη)
      exact ⟨N, fun n hn => by
        obtain ⟨u1, u2⟩ := hN n hn
        show ZTrig.Ab (qsub (evalN n p (E.Γ j)) (E.m j)) (qadd (E.r j) (qeps (k + Bc + Bη)))
        unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩)
  obtain ⟨N2, h2⟩ := hf p hp (k + Bc)
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have e0 := qeps_nonneg (k + Bc + Bη)
  have le1 : qle (qeps (k + Bc + Bη)) (qeps (k + Bc)) := qeps_le_add (k + Bc) Bη
  have le2 : qle (qeps (k + Bc + Bη)) (qeps Bη) := by
    have := qeps_le_add Bη (k + Bc); rw [Nat.add_comm Bη (k + Bc)] at this; exact this
  have ηle : qle (qeps (k + Bc + Bη)) η0 := qle_trans le2 hBη
  have near : Near E n p (qeps (k + Bc + Bη)) := h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
  have fb := h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn) (qeps (k + Bc + Bη)) e0 ηle near
  have lb := lin_bound near ha
  have sc := hBc k
  have em := qeps_nonneg (k + Bc)
  have p1 := qmul_nonneg e0 L0
  have p2 := qmul_nonneg e0 a0
  have m1 : qle (qmul (qeps (k + Bc + Bη)) L) (qmul (qeps (k + Bc)) L) :=
    by have := qmul_nonneg (show qle qzero (qsub (qeps (k + Bc)) (qeps (k + Bc + Bη))) by unfold qsub; rat_linarith) L0
       have e : qEq (qmul (qsub (qeps (k + Bc)) (qeps (k + Bc + Bη))) L) (qsub (qmul (qeps (k + Bc)) L) (qmul (qeps (k + Bc + Bη)) L)) := by
         unfold qsub; rat_ring
       unfold qsub at this e; rat_linarith
  have m2 : qle (qmul (qeps (k + Bc + Bη)) (ZTrig.bs a E.S)) (qmul (qeps (k + Bc)) (ZTrig.bs a E.S)) :=
    by have := qmul_nonneg (show qle qzero (qsub (qeps (k + Bc)) (qeps (k + Bc + Bη))) by unfold qsub; rat_linarith) a0
       have e : qEq (qmul (qsub (qeps (k + Bc)) (qeps (k + Bc + Bη))) (ZTrig.bs a E.S))
           (qsub (qmul (qeps (k + Bc)) (ZTrig.bs a E.S)) (qmul (qeps (k + Bc + Bη)) (ZTrig.bs a E.S))) := by
         unfold qsub; rat_ring
       unfold qsub at this e; rat_linarith
  have es : qEq (qmul (qeps (k + Bc)) (qadd (qadd L (ZTrig.bs a E.S)) qone))
      (qadd (qadd (qmul (qeps (k + Bc)) L) (qmul (qeps (k + Bc)) (ZTrig.bs a E.S))) (qeps (k + Bc))) := by rat_ring
  obtain ⟨f1, f2⟩ := fb
  obtain ⟨l1, l2⟩ := lb
  unfold affv at f1 f2
  show qle (qsub (qsub F.c R) (qeps k)) (f n p) ∧ qle (f n p) (qadd (qadd F.c R) (qeps k))
  unfold qsub at *
  generalize f n p = V at *
  generalize lin E F.s (zv E n p) = Lv at *
  generalize ZTrig.bs (fun j => qmul (a j) (E.r j)) E.S = P at *
  generalize ZTrig.bs a E.S = A at *
  generalize qmul (qeps (k + Bc + Bη)) L = X1 at *
  generalize qmul (qeps (k + Bc)) L = X2 at *
  generalize qmul (qeps (k + Bc + Bη)) A = Y1 at *
  generalize qmul (qeps (k + Bc)) A = Y2 at *
  generalize qmul (qeps (k + Bc)) (qadd (qadd L A) qone) = Z at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The steps -/

theorem pos_min {a b : QExpr} (ha : qlt qzero a) (hb : qlt qzero b) (a1 : qle a qone) (b1 : qle b qone) :
    ∃ m, qlt qzero m ∧ qle m qone ∧ qle m a ∧ qle m b := by
  cases qle_total a b with
  | inl h => exact ⟨a, ha, a1, qle_refl _, h⟩
  | inr h => exact ⟨b, hb, b1, h, qle_refl _⟩

theorem enc_const (E : Env) (B : Box QExpr) (v : QExpr) : Enc E B (fun _ _ => v) ⟨v, fun _ => qzero, qzero⟩ := by
  refine ⟨qzero, qone, qle_refl _, qone_pos, qle_refl _, fun p _ k => ⟨0, fun n _ η _ _ _ => ?_⟩⟩
  have z := lin_zero E (zv E n p)
  have e := qeps_nonneg k
  show ZTrig.Ab (qsub v (qadd v (lin E (fun _ => qzero) (zv E n p)))) (qadd (qadd qzero (qmul η qzero)) (qeps k))
  have m : qEq (qmul η qzero) qzero := by rat_ring
  unfold qsub
  generalize lin E (fun _ => qzero) (zv E n p) = X at *
  generalize qmul η qzero = Y at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- A basis element: `z_j` is its own form `m_j + 1·(z_j − m_j)`. -/
theorem enc_basis (E : Env) (B : Box QExpr) {j : Nat} (hj : j < E.S) :
    Enc E B (fun n p => evalN n p (E.Γ j)) ⟨E.m j, upd (fun _ => qzero) j qone, qzero⟩ := by
  refine ⟨qzero, qone, qle_refl _, qone_pos, qle_refl _, fun p _ k => ⟨0, fun n _ η _ _ _ => ?_⟩⟩
  have l : qEq (lin E (upd (fun _ => qzero) j qone) (zv E n p)) (qsub (zv E n p j) (E.m j)) :=
    bs_upd_in (fun k => qsub (zv E n p k) (E.m k)) j E.S hj
  have e := qeps_nonneg k
  have m : qEq (qmul η qzero) qzero := by rat_ring
  show ZTrig.Ab (qsub (zv E n p j) (qadd (E.m j) (lin E (upd (fun _ => qzero) j qone) (zv E n p))))
    (qadd (qadd qzero (qmul η qzero)) (qeps k))
  unfold qsub at *
  generalize lin E (upd (fun _ => qzero) j qone) (zv E n p) = X at *
  generalize qmul η qzero = Y at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- A variable whose box is a point. -/
theorem enc_point (E : Env) (B : Box QExpr) {i : Nat} {v : QExpr} (h1 : qEq (B i).1 v) (h2 : qEq (B i).2 v) :
    Enc E B (fun _ p => p i) ⟨v, fun _ => qzero, qzero⟩ := by
  refine ⟨qzero, qone, qle_refl _, qone_pos, qle_refl _, fun p hp k => ⟨0, fun n _ η _ _ _ => ?_⟩⟩
  have z := lin_zero E (zv E n p)
  have e := qeps_nonneg k
  have m : qEq (qmul η qzero) qzero := by rat_ring
  have b1 : qle (B i).1 (p i) := (hp i).1
  have b2 : qle (p i) (B i).2 := (hp i).2
  show ZTrig.Ab (qsub (p i) (qadd v (lin E (fun _ => qzero) (zv E n p)))) (qadd (qadd qzero (qmul η qzero)) (qeps k))
  unfold qsub
  generalize lin E (fun _ => qzero) (zv E n p) = X at *
  generalize qmul η qzero = Y at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- Two enclosures, one index and one `η₀` for both. -/
theorem enc_pair {E : Env} {B : Box QExpr} {f g : Nat → Point QExpr → QExpr} {F G : Form}
    (hf : Enc E B f F) (hg : Enc E B g G) :
    ∃ Lf Lg η0, qle qzero Lf ∧ qle qzero Lg ∧ qlt qzero η0 ∧ qle η0 qone ∧ ∀ p, InBox qOrd B p → ∀ k, ∃ N, ∀ n, N ≤ n →
      ∀ η, qle qzero η → qle η η0 → Near E n p η →
      ZTrig.Ab (qsub (f n p) (affv E F (zv E n p))) (qadd (qadd F.e (qmul η Lf)) (qeps k)) ∧
      ZTrig.Ab (qsub (g n p) (affv E G (zv E n p))) (qadd (qadd G.e (qmul η Lg)) (qeps k)) := by
  obtain ⟨Lf, ηf, Lf0, ηfp, ηf1, hf⟩ := hf
  obtain ⟨Lg, ηg, Lg0, ηgp, ηg1, hg⟩ := hg
  obtain ⟨η0, η0p, η01, m1, m2⟩ := pos_min ηfp ηgp ηf1 ηg1
  refine ⟨Lf, Lg, η0, Lf0, Lg0, η0p, η01, fun p hp k => ?_⟩
  obtain ⟨N1, h1⟩ := hf p hp k
  obtain ⟨N2, h2⟩ := hg p hp k
  exact ⟨N1 + N2, fun n hn η e0 e1 near =>
    ⟨h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn) η e0 (qle_trans e1 m1) near,
     h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn) η e0 (qle_trans e1 m2) near⟩⟩

theorem enc_add {E : Env} {B : Box QExpr} {f g : Nat → Point QExpr → QExpr} {F G : Form}
    (hf : Enc E B f F) (hg : Enc E B g G) :
    Enc E B (fun n p => qadd (f n p) (g n p)) ⟨qadd F.c G.c, fun j => qadd (F.s j) (G.s j), qadd F.e G.e⟩ := by
  obtain ⟨Lf, Lg, η0, Lf0, Lg0, η0p, η01, h⟩ := enc_pair hf hg
  refine ⟨qadd Lf Lg, η0, by rat_linarith, η0p, η01, fun p hp k => ?_⟩
  obtain ⟨N, hN⟩ := h p hp (k + 1)
  refine ⟨N, fun n hn η e0 e1 near => ?_⟩
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hN n hn η e0 e1 near
  have l := lin_add E F.s G.s (zv E n p)
  have es := qeps_succ_add k
  have m : qEq (qmul η (qadd Lf Lg)) (qadd (qmul η Lf) (qmul η Lg)) := by rat_ring
  show ZTrig.Ab (qsub (qadd (f n p) (g n p)) (qadd (qadd F.c G.c) (lin E (fun j => qadd (F.s j) (G.s j)) (zv E n p))))
    (qadd (qadd (qadd F.e G.e) (qmul η (qadd Lf Lg))) (qeps k))
  unfold affv at *
  unfold qsub at *
  generalize lin E (fun j => qadd (F.s j) (G.s j)) (zv E n p) = X at *
  generalize lin E F.s (zv E n p) = X1 at *
  generalize lin E G.s (zv E n p) = X2 at *
  generalize qmul η (qadd Lf Lg) = Y at *
  generalize qmul η Lf = Y1 at *
  generalize qmul η Lg = Y2 at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem enc_sub {E : Env} {B : Box QExpr} {f g : Nat → Point QExpr → QExpr} {F G : Form}
    (hf : Enc E B f F) (hg : Enc E B g G) :
    Enc E B (fun n p => qsub (f n p) (g n p)) ⟨qsub F.c G.c, fun j => qsub (F.s j) (G.s j), qadd F.e G.e⟩ := by
  obtain ⟨Lf, Lg, η0, Lf0, Lg0, η0p, η01, h⟩ := enc_pair hf hg
  refine ⟨qadd Lf Lg, η0, by rat_linarith, η0p, η01, fun p hp k => ?_⟩
  obtain ⟨N, hN⟩ := h p hp (k + 1)
  refine ⟨N, fun n hn η e0 e1 near => ?_⟩
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hN n hn η e0 e1 near
  have l := lin_sub E F.s G.s (zv E n p)
  have es := qeps_succ_add k
  have m : qEq (qmul η (qadd Lf Lg)) (qadd (qmul η Lf) (qmul η Lg)) := by rat_ring
  show ZTrig.Ab (qsub (qsub (f n p) (g n p)) (qadd (qsub F.c G.c) (lin E (fun j => qsub (F.s j) (G.s j)) (zv E n p))))
    (qadd (qadd (qadd F.e G.e) (qmul η (qadd Lf Lg))) (qeps k))
  unfold affv at *
  unfold qsub at *
  generalize lin E (fun j => qadd (F.s j) (qneg (G.s j))) (zv E n p) = X at *
  generalize lin E F.s (zv E n p) = X1 at *
  generalize lin E G.s (zv E n p) = X2 at *
  generalize qmul η (qadd Lf Lg) = Y at *
  generalize qmul η Lf = Y1 at *
  generalize qmul η Lg = Y2 at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- WIDENING (the kernel's `tidy`: coefficients onto a grid, what moved into the error). -/
theorem enc_widen {E : Env} {B : Box QExpr} {f : Nat → Point QExpr → QExpr} {F G : Form} (hf : Enc E B f F)
    {w0 : QExpr} {w : Nat → QExpr} (hc : ZTrig.Ab (qsub F.c G.c) w0) (hs : ∀ j, j < E.S → ZTrig.Ab (qsub (F.s j) (G.s j)) (w j))
    (he : qle (qadd (qadd F.e w0) (ZTrig.bs (fun j => qmul (w j) (E.r j)) E.S)) G.e) : Enc E B f G := by
  obtain ⟨L, η0, L0, η0p, η01, h⟩ := hf
  have W0 : qle qzero (ZTrig.bs w E.S) := bs_nonneg_lt _ (fun j hj => by obtain ⟨x1, x2⟩ := hs j hj; rat_linarith)
  refine ⟨qadd L (ZTrig.bs w E.S), η0, by rat_linarith, η0p, η01, fun p hp k => ?_⟩
  obtain ⟨N, hN⟩ := h p hp k
  refine ⟨N, fun n hn η e0 e1 near => ?_⟩
  obtain ⟨a1, a2⟩ := hN n hn η e0 e1 near
  obtain ⟨l1, l2⟩ := lin_bound near hs
  have l := lin_sub E F.s G.s (zv E n p)
  obtain ⟨c1, c2⟩ := hc
  have m : qEq (qmul η (qadd L (ZTrig.bs w E.S))) (qadd (qmul η L) (qmul η (ZTrig.bs w E.S))) := by rat_ring
  unfold affv at *
  unfold qsub at *
  generalize lin E (fun j => qadd (F.s j) (qneg (G.s j))) (zv E n p) = X at *
  generalize lin E F.s (zv E n p) = X1 at *
  generalize lin E G.s (zv E n p) = X2 at *
  generalize ZTrig.bs (fun j => qmul (w j) (E.r j)) E.S = P at *
  generalize qmul η (qadd L (ZTrig.bs w E.S)) = Y at *
  generalize qmul η L = Y1 at *
  generalize qmul η (ZTrig.bs w E.S) = Y2 at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `(U + ηP + ε)(V + ηQ + ε) ≤ UV + η(PV + QU + PQ + P + Q) + ε(U + V + 1)`, `η, ε ∈ [0, 1]`. -/
theorem prod_ab {x y U V P Q η ε : QExpr} (hx : ZTrig.Ab x (qadd (qadd U (qmul η P)) ε))
    (hy : ZTrig.Ab y (qadd (qadd V (qmul η Q)) ε)) (U0 : qle qzero U) (V0 : qle qzero V) (P0 : qle qzero P)
    (Q0 : qle qzero Q) (η0 : qle qzero η) (η1 : qle η qone) (ε0 : qle qzero ε) (ε1 : qle ε qone) :
    ZTrig.Ab (qmul x y) (qadd (qadd (qmul U V)
      (qmul η (qadd (qadd (qadd (qmul P V) (qmul Q U)) (qmul P Q)) (qadd P Q)))) (qmul ε (qadd (qadd U V) qone))) := by
  have m := ZTrig.mul_abs hx hy
  have t1 := qmul_nonneg (qmul_nonneg (qmul_nonneg η0 P0) Q0) (show qle qzero (qsub qone η) by unfold qsub; rat_linarith)
  have t2 := qmul_nonneg (qmul_nonneg η0 (show qle qzero (qadd P Q) by rat_linarith)) (show qle qzero (qsub qone ε) by unfold qsub; rat_linarith)
  have t3 := qmul_nonneg ε0 (show qle qzero (qsub qone ε) by unfold qsub; rat_linarith)
  have d : qle (qmul (qadd (qadd U (qmul η P)) ε) (qadd (qadd V (qmul η Q)) ε))
      (qadd (qadd (qmul U V) (qmul η (qadd (qadd (qadd (qmul P V) (qmul Q U)) (qmul P Q)) (qadd P Q)))) (qmul ε (qadd (qadd U V) qone))) := by
    unfold qsub at t1 t2 t3; rat_linarith
  exact ab_widen m d

/-- PRODUCTS: `c_x c_y + c_y·s_x + c_x·s_y`, error `|c_x| e_y + |c_y| e_x + (R_x + e_x)(R_y + e_y)`. -/
theorem enc_mul {E : Env} {B : Box QExpr} {f g : Nat → Point QExpr → QExpr} {F G : Form}
    (hf : Enc E B f F) (hg : Enc E B g G) (hr : ∀ j, j < E.S → qle qzero (E.r j))
    (Fe0 : qle qzero F.e) (Ge0 : qle qzero G.e) {cf cg : QExpr} {ax ay : Nat → QExpr}
    (hcf : ZTrig.Ab F.c cf) (hcg : ZTrig.Ab G.c cg) (hax : ∀ j, j < E.S → ZTrig.Ab (F.s j) (ax j))
    (hay : ∀ j, j < E.S → ZTrig.Ab (G.s j) (ay j)) {e : QExpr}
    (he : qle (qadd (qadd (qmul cf G.e) (qmul cg F.e))
      (qmul (qadd (ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S) F.e) (qadd (ZTrig.bs (fun j => qmul (ay j) (E.r j)) E.S) G.e))) e) :
    Enc E B (fun n p => qmul (f n p) (g n p)) ⟨qmul F.c G.c, fun j => qadd (qmul G.c (F.s j)) (qmul F.c (G.s j)), e⟩ := by
  obtain ⟨Lf, Lg, η0, Lf0, Lg0, η0p, η01, h⟩ := enc_pair hf hg
  have cf0 : qle qzero cf := by obtain ⟨x1, x2⟩ := hcf; rat_linarith
  have cg0 : qle qzero cg := by obtain ⟨x1, x2⟩ := hcg; rat_linarith
  have ax0 : ∀ j, j < E.S → qle qzero (ax j) := fun j hj => by obtain ⟨x1, x2⟩ := hax j hj; rat_linarith
  have ay0 : ∀ j, j < E.S → qle qzero (ay j) := fun j hj => by obtain ⟨x1, x2⟩ := hay j hj; rat_linarith
  have Ax0 : qle qzero (ZTrig.bs ax E.S) := bs_nonneg_lt _ ax0
  have Ay0 : qle qzero (ZTrig.bs ay E.S) := bs_nonneg_lt _ ay0
  have Rx0 : qle qzero (ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S) :=
    bs_nonneg_lt _ (fun j hj => qmul_nonneg (ax0 j hj) (hr j hj))
  have Ry0 : qle qzero (ZTrig.bs (fun j => qmul (ay j) (E.r j)) E.S) :=
    bs_nonneg_lt _ (fun j hj => qmul_nonneg (ay0 j hj) (hr j hj))
  generalize hRx : ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S = Rx at *
  generalize hRy : ZTrig.bs (fun j => qmul (ay j) (E.r j)) E.S = Ry at *
  generalize hAx : ZTrig.bs ax E.S = Ax at *
  generalize hAy : ZTrig.bs ay E.S = Ay at *
  have U0 : qle qzero (qadd Rx F.e) := by rat_linarith
  have V0 : qle qzero (qadd Ry G.e) := by rat_linarith
  have P0 : qle qzero (qadd Ax Lf) := by rat_linarith
  have Q0 : qle qzero (qadd Ay Lg) := by rat_linarith
  have LH0 : qle qzero (qadd (qadd (qmul cf Lg) (qmul cg Lf))
      (qadd (qadd (qadd (qmul (qadd Ax Lf) (qadd Ry G.e)) (qmul (qadd Ay Lg) (qadd Rx F.e))) (qmul (qadd Ax Lf) (qadd Ay Lg)))
        (qadd (qadd Ax Lf) (qadd Ay Lg)))) := by
    have := qmul_nonneg cf0 Lg0; have := qmul_nonneg cg0 Lf0; have := qmul_nonneg P0 V0; have := qmul_nonneg Q0 U0
    have := qmul_nonneg P0 Q0; rat_linarith
  refine ⟨_, η0, LH0, η0p, η01, fun p hp k => ?_⟩
  obtain ⟨Bc, hBc⟩ := eps_scaled (C := qadd (qadd (qadd cf cg) (qadd (qadd Rx F.e) (qadd Ry G.e))) qone)
    (by have := qle_of_qlt qone_pos; rat_linarith)
  obtain ⟨N, hN⟩ := h p hp (k + Bc)
  refine ⟨N, fun n hn η e0 e1 near => ?_⟩
  obtain ⟨df, dg⟩ := hN n hn η e0 e1 near
  have lbf := lin_bound near hax
  have lbg := lin_bound near hay
  rw [hRx, hAx] at lbf
  rw [hRy, hAy] at lbg
  have ε0 := qeps_nonneg (k + Bc)
  have ε1 := eps_le_one (k + Bc)
  have η1 := qle_trans e1 η01
  unfold affv at df dg
  -- the pieces
  have xf : ZTrig.Ab (qadd (lin E F.s (zv E n p)) (qsub (f n p) (qadd F.c (lin E F.s (zv E n p)))))
      (qadd (qadd (qadd Rx F.e) (qmul η (qadd Ax Lf))) (qeps (k + Bc))) := by
    have := ab_add lbf df
    refine ab_widen this (qle_of_qEq ?_)
    rat_ring
  have xg : ZTrig.Ab (qadd (lin E G.s (zv E n p)) (qsub (g n p) (qadd G.c (lin E G.s (zv E n p)))))
      (qadd (qadd (qadd Ry G.e) (qmul η (qadd Ay Lg))) (qeps (k + Bc))) := by
    have := ab_add lbg dg
    refine ab_widen this (qle_of_qEq ?_)
    rat_ring
  have pp := prod_ab xf xg U0 V0 P0 Q0 e0 η1 ε0 ε1
  have m1 := ZTrig.mul_abs hcf dg
  have m2 := ZTrig.mul_abs hcg df
  -- the identity
  have lH : qEq (lin E (fun j => qadd (qmul G.c (F.s j)) (qmul F.c (G.s j))) (zv E n p))
      (qadd (qmul G.c (lin E F.s (zv E n p))) (qmul F.c (lin E G.s (zv E n p)))) :=
    qEq_trans (lin_add E _ _ _) (qadd_respects (lin_scale E G.c F.s _) (lin_scale E F.c G.s _))
  have sc := hBc k
  show ZTrig.Ab (qsub (qmul (f n p) (g n p)) (qadd (qmul F.c G.c) (lin E (fun j => qadd (qmul G.c (F.s j)) (qmul F.c (G.s j))) (zv E n p))))
    (qadd (qadd e (qmul η _)) (qeps k))
  have idt : qEq (qsub (qmul (f n p) (g n p)) (qadd (qmul F.c G.c) (qadd (qmul G.c (lin E F.s (zv E n p))) (qmul F.c (lin E G.s (zv E n p))))))
      (qadd (qadd (qmul F.c (qsub (g n p) (qadd G.c (lin E G.s (zv E n p))))) (qmul G.c (qsub (f n p) (qadd F.c (lin E F.s (zv E n p))))))
        (qmul (qadd (lin E F.s (zv E n p)) (qsub (f n p) (qadd F.c (lin E F.s (zv E n p)))))
          (qadd (lin E G.s (zv E n p)) (qsub (g n p) (qadd G.c (lin E G.s (zv E n p))))))) := by
    unfold qsub; rat_ring
  have exp1 : qEq (qmul cf (qadd (qadd G.e (qmul η Lg)) (qeps (k + Bc))))
      (qadd (qadd (qmul cf G.e) (qmul η (qmul cf Lg))) (qmul (qeps (k + Bc)) cf)) := by rat_ring
  have exp2 : qEq (qmul cg (qadd (qadd F.e (qmul η Lf)) (qeps (k + Bc))))
      (qadd (qadd (qmul cg F.e) (qmul η (qmul cg Lf))) (qmul (qeps (k + Bc)) cg)) := by rat_ring
  have exp3 : qEq (qmul (qeps (k + Bc)) (qadd (qadd (qadd cf cg) (qadd (qadd Rx F.e) (qadd Ry G.e))) qone))
      (qadd (qadd (qmul (qeps (k + Bc)) cf) (qmul (qeps (k + Bc)) cg)) (qmul (qeps (k + Bc)) (qadd (qadd (qadd Rx F.e) (qadd Ry G.e)) qone))) := by
    rat_ring
  have exp4 : qEq (qmul η (qadd (qadd (qmul cf Lg) (qmul cg Lf))
      (qadd (qadd (qadd (qmul (qadd Ax Lf) (qadd Ry G.e)) (qmul (qadd Ay Lg) (qadd Rx F.e))) (qmul (qadd Ax Lf) (qadd Ay Lg)))
        (qadd (qadd Ax Lf) (qadd Ay Lg)))))
      (qadd (qadd (qmul η (qmul cf Lg)) (qmul η (qmul cg Lf)))
        (qmul η (qadd (qadd (qadd (qmul (qadd Ax Lf) (qadd Ry G.e)) (qmul (qadd Ay Lg) (qadd Rx F.e))) (qmul (qadd Ax Lf) (qadd Ay Lg)))
          (qadd (qadd Ax Lf) (qadd Ay Lg))))) := by rat_ring
  have exp5 : qEq (qmul (qeps (k + Bc)) (qadd (qadd (qadd Rx F.e) (qadd Ry G.e)) qone))
      (qmul (qeps (k + Bc)) (qadd (qadd (qadd Rx F.e) (qadd Ry G.e)) qone)) := qEq_refl _
  clear exp5
  obtain ⟨p1, p2⟩ := pp
  obtain ⟨q1, q2⟩ := m1
  obtain ⟨r1, r2⟩ := m2
  generalize lin E (fun j => qadd (qmul G.c (F.s j)) (qmul F.c (G.s j))) (zv E n p) = LH at *
  generalize qmul F.c (qsub (g n p) (qadd G.c (lin E G.s (zv E n p)))) = T1 at *
  generalize qmul G.c (qsub (f n p) (qadd F.c (lin E F.s (zv E n p)))) = T2 at *
  generalize qmul (qadd (lin E F.s (zv E n p)) (qsub (f n p) (qadd F.c (lin E F.s (zv E n p)))))
    (qadd (lin E G.s (zv E n p)) (qsub (g n p) (qadd G.c (lin E G.s (zv E n p))))) = T3 at *
  generalize qmul cf (qadd (qadd G.e (qmul η Lg)) (qeps (k + Bc))) = B1 at *
  generalize qmul cg (qadd (qadd F.e (qmul η Lf)) (qeps (k + Bc))) = B2 at *
  generalize qmul (qadd Rx F.e) (qadd Ry G.e) = UV at *
  generalize qmul (qeps (k + Bc)) (qadd (qadd (qadd Rx F.e) (qadd Ry G.e)) qone) = EU at *
  generalize qmul (qeps (k + Bc)) cf = Ecf at *
  generalize qmul (qeps (k + Bc)) cg = Ecg at *
  generalize qmul (qeps (k + Bc)) (qadd (qadd (qadd cf cg) (qadd (qadd Rx F.e) (qadd Ry G.e))) qone) = EC at *
  generalize qmul cf G.e = cfG at *
  generalize qmul cg F.e = cgF at *
  generalize qmul η (qmul cf Lg) = ηa at *
  generalize qmul η (qmul cg Lf) = ηb at *
  generalize qmul η (qadd (qadd (qadd (qmul (qadd Ax Lf) (qadd Ry G.e)) (qmul (qadd Ay Lg) (qadd Rx F.e))) (qmul (qadd Ax Lf) (qadd Ay Lg)))
    (qadd (qadd Ax Lf) (qadd Ay Lg))) = ηc at *
  generalize qmul η (qadd (qadd (qmul cf Lg) (qmul cg Lf))
      (qadd (qadd (qadd (qmul (qadd Ax Lf) (qadd Ry G.e)) (qmul (qadd Ay Lg) (qadd Rx F.e))) (qmul (qadd Ax Lf) (qadd Ay Lg)))
        (qadd (qadd Ax Lf) (qadd Ay Lg)))) = ηH at *
  clear df dg lbf lbg xf xg near hBc hN h hcf hcg hax hay
  unfold qsub at idt ⊢
  generalize qmul (f n p) (g n p) = FG at *
  generalize qmul F.c G.c = CC at *
  generalize qmul G.c (lin E F.s (zv E n p)) = GL at *
  generalize qmul F.c (lin E G.s (zv E n p)) = FL at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## A nonlinear step: a linear stand-in and its remainder -/

/-- `φ` (at index `n`) is `α·x + ζ` within `δ` on `[a, b]`, and within `δ + ι·L₂` on `[a − ι, b + ι]`. -/
def Rem (φ : Nat → QExpr → QExpr) (a b α ζ δ : QExpr) : Prop :=
  ∃ L2 ι0, qle qzero L2 ∧ qlt qzero ι0 ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x ι, qle qzero ι → qle ι ι0 →
    qle (qsub a ι) x → qle x (qadd b ι) →
    ZTrig.Ab (qsub (qsub (φ n x) (qmul α x)) ζ) (qadd (qadd δ (qmul ι L2)) (qeps k))

theorem eps_mono {j k : Nat} (h : j ≤ k) : qle (qeps k) (qeps j) := by
  induction h with
  | refl => exact qle_refl _
  | step _ ih => exact qle_trans (qeps_le_add _ 1) ih

/-- THE NONLINEAR STEP: `φ(f)` has the form `α·F + ζ`, error `|α|·e + δ`, when `[a, b]` holds `F`'s interval. -/
theorem enc_rem {E : Env} {B : Box QExpr} {f : Nat → Point QExpr → QExpr} {F : Form} (hf : Enc E B f F)
    (hr : ∀ j, j < E.S → qle qzero (E.r j)) (Fe0 : qle qzero F.e) {ax : Nat → QExpr}
    (hax : ∀ j, j < E.S → ZTrig.Ab (F.s j) (ax j)) {φ : Nat → QExpr → QExpr} {a b α ζ δ aα e : QExpr}
    (hrem : Rem φ a b α ζ δ)
    (ha : qle a (qsub F.c (qadd (ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S) F.e)))
    (hb : qle (qadd F.c (qadd (ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S) F.e)) b)
    (hα : ZTrig.Ab α aα) (he : qle (qadd (qmul aα F.e) δ) e) :
    Enc E B (fun n p => φ n (f n p)) ⟨qadd (qmul α F.c) ζ, fun j => qmul α (F.s j), e⟩ := by
  obtain ⟨Lf, ηf, Lf0, ηfp, ηf1, hf⟩ := hf
  obtain ⟨L2, ι0, L20, ι0p, hrem⟩ := hrem
  have aα0 : qle qzero aα := by obtain ⟨x1, x2⟩ := hα; rat_linarith
  have ax0 : ∀ j, j < E.S → qle qzero (ax j) := fun j hj => by obtain ⟨x1, x2⟩ := hax j hj; rat_linarith
  have Ax0 : qle qzero (ZTrig.bs ax E.S) := bs_nonneg_lt _ ax0
  generalize hRx : ZTrig.bs (fun j => qmul (ax j) (E.r j)) E.S = Rx at *
  generalize hAx : ZTrig.bs ax E.S = Ax at *
  -- η₀: η·(Ax + Lf) ≤ ι₀/2
  obtain ⟨Bι, hBι⟩ := ZTrig.pos_floor ι0p
  obtain ⟨Bs, hBs⟩ := eps_scaled (C := qadd (qadd Ax Lf) qone) (by have := qle_of_qlt qone_pos; rat_linarith)
  have pe := qeps_pos (Bι + 1 + Bs)
  obtain ⟨η0, η0p, η01, m1, m2⟩ := pos_min ηfp pe ηf1 (qle_trans (eps_mono (Nat.zero_le _)) (by
    have := eps_le_one 0; exact this))
  refine ⟨qadd (qmul L2 (qadd Ax Lf)) (qmul aα Lf), η0, by
    have := qmul_nonneg L20 (show qle qzero (qadd Ax Lf) by rat_linarith); have := qmul_nonneg aα0 Lf0; rat_linarith,
    η0p, η01, fun p hp k => ?_⟩
  obtain ⟨Bc, hBc⟩ := eps_scaled (C := qadd (qadd L2 aα) qone) (by have := qle_of_qlt qone_pos; rat_linarith)
  obtain ⟨N1, h1⟩ := hf p hp (k + 1 + Bc + Bι + 1)
  obtain ⟨N2, h2⟩ := hrem (k + 1)
  refine ⟨N1 + N2, fun n hn η e0 e1 near => ?_⟩
  have df := h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn) η e0 (qle_trans e1 m1) near
  have lb := lin_bound near hax
  rw [hRx, hAx] at lb
  unfold affv at df
  -- ι = η(Ax + Lf) + ε
  have ε0 := qeps_nonneg (k + 1 + Bc + Bι + 1)
  have εa : qle (qeps (k + 1 + Bc + Bι + 1)) (qeps (Bι + 1)) := eps_mono (Nat.succ_le_succ (Nat.le_add_left Bι (k + 1 + Bc)))
  have εb : qle (qeps (k + 1 + Bc + Bι + 1)) (qeps (k + 1 + Bc)) :=
    eps_mono (Nat.le_trans (Nat.le_add_right _ Bι) (Nat.le_succ _))
  have half := qeps_succ_add Bι
  have sB := hBs (Bι + 1)
  have ηC : qle (qmul η (qadd (qadd Ax Lf) qone)) (qmul (qeps (Bι + 1 + Bs)) (qadd (qadd Ax Lf) qone)) := by
    have := qmul_nonneg (show qle qzero (qsub (qeps (Bι + 1 + Bs)) η) by unfold qsub; rat_linarith)
      (show qle qzero (qadd (qadd Ax Lf) qone) by have := qle_of_qlt qone_pos; rat_linarith)
    have e : qEq (qmul (qsub (qeps (Bι + 1 + Bs)) η) (qadd (qadd Ax Lf) qone))
        (qsub (qmul (qeps (Bι + 1 + Bs)) (qadd (qadd Ax Lf) qone)) (qmul η (qadd (qadd Ax Lf) qone))) := by unfold qsub; rat_ring
    unfold qsub at this e; rat_linarith
  have ιe : qEq (qmul η (qadd (qadd Ax Lf) qone)) (qadd (qmul η (qadd Ax Lf)) η) := by rat_ring
  have ηAL0 := qmul_nonneg e0 (show qle qzero (qadd Ax Lf) by rat_linarith)
  have ι0' : qle (qadd (qmul η (qadd Ax Lf)) (qeps (k + 1 + Bc + Bι + 1))) ι0 := by rat_linarith
  have ιnn : qle qzero (qadd (qmul η (qadd Ax Lf)) (qeps (k + 1 + Bc + Bι + 1))) := by rat_linarith
  -- f's value in [a − ι, b + ι]
  obtain ⟨d1, d2⟩ := df
  obtain ⟨l1, l2⟩ := lb
  have eAL : qEq (qmul η (qadd Ax Lf)) (qadd (qmul η Ax) (qmul η Lf)) := by rat_ring
  have xa : qle (qsub a (qadd (qmul η (qadd Ax Lf)) (qeps (k + 1 + Bc + Bι + 1)))) (f n p) := by
    unfold qsub at *; rat_linarith
  have xb : qle (f n p) (qadd b (qadd (qmul η (qadd Ax Lf)) (qeps (k + 1 + Bc + Bι + 1)))) := by
    unfold qsub at *; rat_linarith
  have rm := h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn) (f n p) _ ιnn ι0' xa xb
  -- the form: α·affv F + ζ
  have lsc := lin_scale E α F.s (zv E n p)
  have mα := ZTrig.mul_abs hα (show ZTrig.Ab (qsub (f n p) (qadd F.c (lin E F.s (zv E n p))))
    (qadd (qadd F.e (qmul η Lf)) (qeps (k + 1 + Bc + Bι + 1))) from ⟨d1, d2⟩)
  have sc := hBc (k + 1)
  have es := qeps_succ_add k
  have εc : qle (qeps (k + 1 + Bc + Bι + 1)) (qeps (k + 1 + Bc)) := εb
  have m3 : qle (qmul (qeps (k + 1 + Bc + Bι + 1)) (qadd (qadd L2 aα) qone))
      (qmul (qeps (k + 1 + Bc)) (qadd (qadd L2 aα) qone)) := by
    have := qmul_nonneg (show qle qzero (qsub (qeps (k + 1 + Bc)) (qeps (k + 1 + Bc + Bι + 1))) by unfold qsub; rat_linarith)
      (show qle qzero (qadd (qadd L2 aα) qone) by have := qle_of_qlt qone_pos; rat_linarith)
    have e : qEq (qmul (qsub (qeps (k + 1 + Bc)) (qeps (k + 1 + Bc + Bι + 1))) (qadd (qadd L2 aα) qone))
        (qsub (qmul (qeps (k + 1 + Bc)) (qadd (qadd L2 aα) qone)) (qmul (qeps (k + 1 + Bc + Bι + 1)) (qadd (qadd L2 aα) qone))) := by
      unfold qsub; rat_ring
    unfold qsub at this e; rat_linarith
  have idt : qEq (qsub (φ n (f n p)) (qadd (qadd (qmul α F.c) ζ) (lin E (fun j => qmul α (F.s j)) (zv E n p))))
      (qadd (qsub (qsub (φ n (f n p)) (qmul α (f n p))) ζ) (qmul α (qsub (f n p) (qadd F.c (lin E F.s (zv E n p)))))) := by
    have := lsc
    unfold qsub at *
    generalize lin E (fun j => qmul α (F.s j)) (zv E n p) = X at *
    have e2 : qEq (qmul α (qadd (f n p) (qneg (qadd F.c (lin E F.s (zv E n p))))))
        (qadd (qmul α (f n p)) (qneg (qadd (qmul α F.c) (qmul α (lin E F.s (zv E n p)))))) := by rat_ring
    generalize qmul α (qadd (f n p) (qneg (qadd F.c (lin E F.s (zv E n p))))) = Y at *
    generalize qmul α (lin E F.s (zv E n p)) = Z at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have ex1 : qEq (qmul aα (qadd (qadd F.e (qmul η Lf)) (qeps (k + 1 + Bc + Bι + 1))))
      (qadd (qadd (qmul aα F.e) (qmul η (qmul aα Lf))) (qmul (qeps (k + 1 + Bc + Bι + 1)) aα)) := by rat_ring
  have ex2 : qEq (qmul (qadd (qmul η (qadd Ax Lf)) (qeps (k + 1 + Bc + Bι + 1))) L2)
      (qadd (qmul η (qmul L2 (qadd Ax Lf))) (qmul (qeps (k + 1 + Bc + Bι + 1)) L2)) := by rat_ring
  have ex3 : qEq (qmul η (qadd (qmul L2 (qadd Ax Lf)) (qmul aα Lf))) (qadd (qmul η (qmul L2 (qadd Ax Lf))) (qmul η (qmul aα Lf))) := by
    rat_ring
  have ex4 : qEq (qmul (qeps (k + 1 + Bc + Bι + 1)) (qadd (qadd L2 aα) qone))
      (qadd (qadd (qmul (qeps (k + 1 + Bc + Bι + 1)) L2) (qmul (qeps (k + 1 + Bc + Bι + 1)) aα)) (qeps (k + 1 + Bc + Bι + 1))) := by
    rat_ring
  obtain ⟨r1, r2⟩ := rm
  obtain ⟨q1, q2⟩ := mα
  show ZTrig.Ab (qsub (φ n (f n p)) (qadd (qadd (qmul α F.c) ζ) (lin E (fun j => qmul α (F.s j)) (zv E n p))))
    (qadd (qadd e (qmul η (qadd (qmul L2 (qadd Ax Lf)) (qmul aα Lf)))) (qeps k))
  clear d1 d2 l1 l2 xa xb h1 h2 near lsc hBc hBs hf hrem
  generalize qsub (φ n (f n p)) (qadd (qadd (qmul α F.c) ζ) (lin E (fun j => qmul α (F.s j)) (zv E n p))) = T at *
  generalize qsub (qsub (φ n (f n p)) (qmul α (f n p))) ζ = T1 at *
  generalize qmul α (qsub (f n p) (qadd F.c (lin E F.s (zv E n p)))) = T2 at *
  generalize qmul aα (qadd (qadd F.e (qmul η Lf)) (qeps (k + 1 + Bc + Bι + 1))) = B2 at *
  generalize qmul (qadd (qmul η (qadd Ax Lf)) (qeps (k + 1 + Bc + Bι + 1))) L2 = B1 at *
  generalize qmul η (qadd (qmul L2 (qadd Ax Lf)) (qmul aα Lf)) = ηH at *
  generalize qmul η (qmul L2 (qadd Ax Lf)) = ηa at *
  generalize qmul η (qmul aα Lf) = ηb at *
  generalize qmul (qeps (k + 1 + Bc + Bι + 1)) (qadd (qadd L2 aα) qone) = EC at *
  generalize qmul (qeps (k + 1 + Bc)) (qadd (qadd L2 aα) qone) = EC' at *
  generalize qmul (qeps (k + 1 + Bc + Bι + 1)) L2 = EL at *
  generalize qmul (qeps (k + 1 + Bc + Bι + 1)) aα = Ea at *
  generalize qmul aα F.e = aF at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZAffine

#print axioms ZAffine.enc_sound
#print axioms ZAffine.enc_add
#print axioms ZAffine.enc_widen
#print axioms ZAffine.enc_mul
#print axioms ZAffine.enc_rem
