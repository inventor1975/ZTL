import ZTaylor2

/-!
# ZDeriv — the symbolic derivative on the grammar, and that it IS the derivative. Zero axioms.

Layer 1 of the higher Taylor orders. `D i e` — `∂e/∂x_i` as an expression of the same grammar (`ZSlopeSqrt.G`).
`step_sound`: between two points of a box differing only in `x_i` by `δ` (`|δ| ≤ 1`),

    e(q) − e(p) − δ·(D e)(p)  is within  ε_k + δ²·H   from some index on,

`H` one constant for the whole box (from the readings of the subterms). Taylor of order 1 with an `O(δ²)` remainder,
pointwise — what the grid (`ZTrig.chord_gen`) integrates into the higher orders (layer 2).

This file: the fragment `const var + − ×` (the derivative exact up to `δ²`, no limits needed beyond the readings).
-/

namespace ZDeriv

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow

/-- `∂x_j/∂x_i`. -/
def dvar (i j : Nat) : QExpr := match Nat.decEq j i with
  | isTrue _ => qone
  | isFalse _ => qzero

/-- THE SYMBOLIC DERIVATIVE `∂e/∂x_i`, inside the grammar. -/
def D (i : Nat) : G → G
  | .const _ => .const qzero
  | .var j => .const (dvar i j)
  | .add u v => .add (D i u) (D i v)
  | .sub u v => .sub (D i u) (D i v)
  | .mul u v => .add (.mul (D i u) v) (.mul u (D i v))
  | .div u v => .div (.sub (.mul (D i u) v) (.mul u (D i v))) (.mul v v)
  | .exp u => .mul (.exp u) (D i u)
  | .ln u => .div (D i u) u
  | .sqrt u => .div (D i u) (.mul (.const (qadd qone qone)) (.sqrt u))
  | .powN _ 0 => .const qzero
  | .powN u (k + 1) => .mul (.mul (.const (qnat (k + 1))) (.powN u k)) (D i u)
  | .log10 u => .div (D i u) (.mul u (.ln (.const (qnat 10))))
  | .sin u => .mul (.cos u) (D i u)
  | .cos u => .mul (.sub (.const qzero) (.sin u)) (D i u)
  | .tan u => .mul (.add (.const qone) (.mul (.tan u) (.tan u))) (D i u)

/-- A reading eventually bounds the value at a point, by one constant for the whole box. -/
theorem read_bound {B : Box QExpr} {e : G} {l h : QExpr} (r : VRead B e l h) :
    ∃ M, qle qzero M ∧ ∀ p, InBox qOrd B p → ∃ N, ∀ n, N ≤ n → ZTrig.Ab (evalN n p e) M := by
  obtain ⟨M, _, hM0, _, m1, m2, _, _⟩ := bound4 l h l h
  have o := qle_of_qlt qone_pos
  refine ⟨qadd M qone, by rat_linarith, fun p hp => ?_⟩
  obtain ⟨N, hN⟩ := value_sound hp r 0
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n hn
  have z := qeps_zero
  obtain ⟨x1, x2⟩ := m1; obtain ⟨x3, x4⟩ := m2
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The step at two points: `e(q) − e(p) − δ·De(p)` within `ε_k + δ²·H` from some index on. -/
def StepAt (i : Nat) (e : G) (H : QExpr) (p q : Point QExpr) : Prop :=
  ∀ k, ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qsub (qsub (evalN n q e) (evalN n p e)) (qmul (qsub (q i) (p i)) (evalN n p (D i e))))
    (qadd (qeps k) (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) H))

theorem eps_scaled {C : QExpr} (hC : qle qzero C) : ∃ B, ∀ k, qle (qmul (qeps (k + B)) C) (qeps k) := by
  obtain ⟨B, hB1, _⟩ := qexpr_bound C
  have hc : qle C (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  refine ⟨B, fun k => ?_⟩
  have s := scale_l hc (qeps_nonneg (k + B))
  have e := qpow2_mul_eps B k
  have c := qmul_comm (qofInt (pow2 B)) (qeps (k + B))
  generalize qmul (qeps (k + B)) C = P at *; generalize qmul (qeps (k + B)) (qofInt (pow2 B)) = Q at *
  generalize qmul (qofInt (pow2 B)) (qeps (k + B)) = Q' at *
  rat_linarith

/-- The product's step, as algebra: the factors' steps `Eu`, `Ev` within `e + δ²·Hu`, `e + δ²·Hv`, the values
within their bounds. -/
theorem mul_step {uq up vq vp du dv δ e Hu Hv Mu Mv Mdu Mdv : QExpr}
    (hu : ZTrig.Ab (qsub (qsub uq up) (qmul δ du)) (qadd e (qmul (qmul δ δ) Hu)))
    (hv : ZTrig.Ab (qsub (qsub vq vp) (qmul δ dv)) (qadd e (qmul (qmul δ δ) Hv)))
    (bvq : ZTrig.Ab vq Mv) (bup : ZTrig.Ab up Mu) (bdu : ZTrig.Ab du Mdu) (bdv : ZTrig.Ab dv Mdv)
    (hδ : ZTrig.Ab δ qone) :
    ZTrig.Ab (qsub (qsub (qmul uq vq) (qmul up vp)) (qmul δ (qadd (qmul du vp) (qmul up dv))))
      (qadd (qmul e (qadd (qadd Mv Mu) Mdu))
        (qmul (qmul δ δ) (qadd (qadd (qmul Hu Mv) (qmul Mu Hv)) (qadd (qmul Mdu Mdv) (qmul Mdu Hv))))) := by
  obtain ⟨a1, a2⟩ := ZTrig.mul_abs hu bvq
  obtain ⟨b1, b2⟩ := ZTrig.mul_abs bup hv
  have dd : ZTrig.Ab (qmul δ δ) (qmul δ δ) := ⟨by have := qmul_self_nonneg δ; rat_linarith, qle_refl _⟩
  obtain ⟨c1, c2⟩ := ZTrig.mul_abs dd (ZTrig.mul_abs bdu bdv)
  obtain ⟨d1, d2⟩ := ZTrig.mul_abs (ZTrig.mul_abs hδ bdu) hv
  have id : qEq (qsub (qsub (qmul uq vq) (qmul up vp)) (qmul δ (qadd (qmul du vp) (qmul up dv))))
      (qadd (qadd (qmul (qsub (qsub uq up) (qmul δ du)) vq) (qmul up (qsub (qsub vq vp) (qmul δ dv))))
        (qadd (qmul (qmul δ δ) (qmul du dv)) (qmul (qmul δ du) (qsub (qsub vq vp) (qmul δ dv))))) := by
    unfold qsub; rat_ring
  have i1 : qEq (qmul (qadd e (qmul (qmul δ δ) Hu)) Mv) (qadd (qmul e Mv) (qmul (qmul δ δ) (qmul Hu Mv))) := by rat_ring
  have i2 : qEq (qmul Mu (qadd e (qmul (qmul δ δ) Hv))) (qadd (qmul e Mu) (qmul (qmul δ δ) (qmul Mu Hv))) := by rat_ring
  have i3 : qEq (qmul (qmul qone Mdu) (qadd e (qmul (qmul δ δ) Hv)))
      (qadd (qmul e Mdu) (qmul (qmul δ δ) (qmul Mdu Hv))) := by rat_ring
  have i4 : qEq (qmul (qmul δ δ) (qmul Mdu Mdv)) (qmul (qmul δ δ) (qmul Mdu Mdv)) := qEq_refl _
  have i5 : qEq (qadd (qmul e (qadd (qadd Mv Mu) Mdu))
        (qmul (qmul δ δ) (qadd (qadd (qmul Hu Mv) (qmul Mu Hv)) (qadd (qmul Mdu Mdv) (qmul Mdu Hv)))))
      (qadd (qadd (qadd (qmul e Mv) (qmul e Mu)) (qmul e Mdu))
        (qadd (qadd (qmul (qmul δ δ) (qmul Hu Mv)) (qmul (qmul δ δ) (qmul Mu Hv)))
          (qadd (qmul (qmul δ δ) (qmul Mdu Mdv)) (qmul (qmul δ δ) (qmul Mdu Hv))))) := by rat_ring
  generalize qsub (qsub (qmul uq vq) (qmul up vp)) (qmul δ (qadd (qmul du vp) (qmul up dv))) = E at *
  generalize qmul (qsub (qsub uq up) (qmul δ du)) vq = T1 at *
  generalize qmul up (qsub (qsub vq vp) (qmul δ dv)) = T2 at *
  generalize qmul (qmul δ δ) (qmul du dv) = T3 at *
  generalize qmul (qmul δ du) (qsub (qsub vq vp) (qmul δ dv)) = T4 at *
  generalize qmul (qadd e (qmul (qmul δ δ) Hu)) Mv = U1 at *
  generalize qmul Mu (qadd e (qmul (qmul δ δ) Hv)) = U2 at *
  generalize qmul (qmul qone Mdu) (qadd e (qmul (qmul δ δ) Hv)) = U3 at *
  generalize qmul (qmul δ δ) (qmul Mdu Mdv) = U4 at *
  generalize qadd (qmul e (qadd (qadd Mv Mu) Mdu))
        (qmul (qmul δ δ) (qadd (qadd (qmul Hu Mv) (qmul Mu Hv)) (qadd (qmul Mdu Mdv) (qmul Mdu Hv)))) = W at *
  generalize qmul e Mv = V1 at *; generalize qmul e Mu = V2 at *; generalize qmul e Mdu = V3 at *
  generalize qmul (qmul δ δ) (qmul Hu Mv) = X1 at *; generalize qmul (qmul δ δ) (qmul Mu Hv) = X2 at *
  generalize qmul (qmul δ δ) (qmul Mdu Hv) = X3 at *
  have s1 : qle E (qadd (qadd U1 U2) (qadd U4 U3)) := by rat_linarith
  have s2 : qle (qneg (qadd (qadd U1 U2) (qadd U4 U3))) E := by rat_linarith
  have s3 : qle (qadd (qadd U1 U2) (qadd U4 U3)) W := by rat_linarith
  have s4 : qle W (qadd (qadd U1 U2) (qadd U4 U3)) := by rat_linarith
  have s5 : qle (qneg W) (qneg (qadd (qadd U1 U2) (qadd U4 U3))) := by
    clear a1 a2 b1 b2 c1 c2 d1 d2 s1 s2 s4 id i1 i2 i3 i4 i5; rat_linarith
  exact ⟨qle_trans s5 s2, qle_trans s1 s3⟩

theorem dvar_eq (i : Nat) : dvar i i = qone := by
  unfold dvar
  cases Nat.decEq i i with
  | isTrue _ => rfl
  | isFalse h => exact absurd rfl h

theorem dvar_ne {i j : Nat} (h : j ≠ i) : dvar i j = qzero := by
  unfold dvar
  cases Nat.decEq j i with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

theorem ab_zero {E W : QExpr} (h : qEq E qzero) (hw : qle qzero W) : ZTrig.Ab E W := ⟨by rat_linarith, by rat_linarith⟩

/-! ## Outer functions with a uniform step -/

/-- A uniform step of an outer function `φ` (derivative `ψ`): on `|x| ≤ A`, `|Δ| ≤ R`, from some index on,
`φ(x + Δ) − φ(x) − Δ·ψ(x)` within `ε_k + Δ²·H`. -/
def UStep (φ ψ : QExpr → Nat → QExpr) : Prop :=
  ∀ {A R : QExpr}, qle qzero A → qle qzero R → ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x d, ZTrig.Ab x A →
    ZTrig.Ab d R → ZTrig.Ab (qsub (qsub (φ (qadd x d) n) (φ x n)) (qmul d (ψ x n))) (qadd (qeps k) (qmul (qmul d d) H))

theorem step_SR {x δ A a R : QExpr} (hx : ZTrig.Ab x A) (h1 : ZTrig.Ab δ R) (hδ : ZTrig.Ab δ a) (N : Nat) :
    ZTrig.Ab (qsub (qsub (ZTrig.Sn (qadd x δ) (N + 2)) (ZTrig.Sn x (N + 2))) (qmul δ (ZTrig.Cn x (N + 2))))
      (qadd (qadd (ZTrig.corner (tm A) (tm R) (N + 2)) (ZTrig.corner (tm A) (tm R) (N + 2)))
        (qadd (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))) (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))))) := by
  obtain ⟨_, ⟨f1, f2⟩⟩ := ZTrig.add_bounds hx h1 (N + 2)
  obtain ⟨cA, sA⟩ := ZTrig.CS_abs hx (N + 2)
  obtain ⟨m1, m2⟩ := ZTrig.mul_abs cA (ZTrig.near_S hδ N)
  obtain ⟨n1, n2⟩ := ZTrig.mul_abs sA (ZTrig.near_C hδ N)
  have e : qEq (qsub (qsub (ZTrig.Sn (qadd x δ) (N + 2)) (ZTrig.Sn x (N + 2))) (qmul δ (ZTrig.Cn x (N + 2))))
      (qadd (qsub (ZTrig.Sn (qadd x δ) (N + 2)) (qadd (qmul (ZTrig.Cn x (N + 2)) (ZTrig.Sn δ (N + 2))) (qmul (ZTrig.Sn x (N + 2)) (ZTrig.Cn δ (N + 2)))))
        (qadd (qmul (ZTrig.Cn x (N + 2)) (qsub (ZTrig.Sn δ (N + 2)) δ)) (qmul (ZTrig.Sn x (N + 2)) (qsub (ZTrig.Cn δ (N + 2)) qone)))) := by
    unfold qsub; rat_ring
  generalize qsub (ZTrig.Sn (qadd x δ) (N + 2)) (qadd (qmul (ZTrig.Cn x (N + 2)) (ZTrig.Sn δ (N + 2))) (qmul (ZTrig.Sn x (N + 2)) (ZTrig.Cn δ (N + 2)))) = P at *
  generalize qmul (ZTrig.Cn x (N + 2)) (qsub (ZTrig.Sn δ (N + 2)) δ) = Q at *
  generalize qmul (ZTrig.Sn x (N + 2)) (qsub (ZTrig.Cn δ (N + 2)) qone) = R at *
  generalize qsub (qsub (ZTrig.Sn (qadd x δ) (N + 2)) (ZTrig.Sn x (N + 2))) (qmul δ (ZTrig.Cn x (N + 2))) = L at *
  generalize ZTrig.corner (tm A) (tm R) (N + 2) = K at *
  generalize qmul (S A (N + 2)) (qmul (qmul a a) (S a N)) = T at *
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem step_CR {x δ A a R : QExpr} (hx : ZTrig.Ab x A) (h1 : ZTrig.Ab δ R) (hδ : ZTrig.Ab δ a) (N : Nat) :
    ZTrig.Ab (qsub (qsub (ZTrig.Cn (qadd x δ) (N + 2)) (ZTrig.Cn x (N + 2))) (qmul δ (qneg (ZTrig.Sn x (N + 2)))))
      (qadd (qadd (ZTrig.corner (tm A) (tm R) (N + 2)) (ZTrig.corner (tm A) (tm R) (N + 2)))
        (qadd (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))) (qmul (S A (N + 2)) (qmul (qmul a a) (S a N))))) := by
  obtain ⟨⟨f1, f2⟩, _⟩ := ZTrig.add_bounds hx h1 (N + 2)
  obtain ⟨cA, sA⟩ := ZTrig.CS_abs hx (N + 2)
  obtain ⟨m1, m2⟩ := ZTrig.mul_abs cA (ZTrig.near_C hδ N)
  obtain ⟨n1, n2⟩ := ZTrig.mul_abs sA (ZTrig.near_S hδ N)
  have e : qEq (qsub (qsub (ZTrig.Cn (qadd x δ) (N + 2)) (ZTrig.Cn x (N + 2))) (qmul δ (qneg (ZTrig.Sn x (N + 2)))))
      (qadd (qsub (ZTrig.Cn (qadd x δ) (N + 2)) (qsub (qmul (ZTrig.Cn x (N + 2)) (ZTrig.Cn δ (N + 2))) (qmul (ZTrig.Sn x (N + 2)) (ZTrig.Sn δ (N + 2)))))
        (qsub (qmul (ZTrig.Cn x (N + 2)) (qsub (ZTrig.Cn δ (N + 2)) qone)) (qmul (ZTrig.Sn x (N + 2)) (qsub (ZTrig.Sn δ (N + 2)) δ)))) := by
    unfold qsub; rat_ring
  generalize qsub (ZTrig.Cn (qadd x δ) (N + 2)) (qsub (qmul (ZTrig.Cn x (N + 2)) (ZTrig.Cn δ (N + 2))) (qmul (ZTrig.Sn x (N + 2)) (ZTrig.Sn δ (N + 2)))) = P at *
  generalize qmul (ZTrig.Cn x (N + 2)) (qsub (ZTrig.Cn δ (N + 2)) qone) = Q at *
  generalize qmul (ZTrig.Sn x (N + 2)) (qsub (ZTrig.Sn δ (N + 2)) δ) = R at *
  generalize qsub (qsub (ZTrig.Cn (qadd x δ) (N + 2)) (ZTrig.Cn x (N + 2))) (qmul δ (qneg (ZTrig.Sn x (N + 2)))) = L at *
  generalize ZTrig.corner (tm A) (tm R) (N + 2) = K at *
  generalize qmul (S A (N + 2)) (qmul (qmul a a) (S a N)) = T at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The grid `x_j = a + j·(b − a)·2^−K` -/

def xg (a b : QExpr) (K j : Nat) : QExpr := qadd a (qmul (qnat j) (qmul (qsub b a) (qeps K)))

/-- `|d|` as a bound with `|d|² = d²`, below any bound of `d`. -/
theorem abs_le {d R : QExpr} (hd : ZTrig.Ab d R) : ∃ a, ZTrig.Ab d a ∧ qEq (qmul a a) (qmul d d) ∧ qle qzero a ∧ qle a R := by
  obtain ⟨h1, h2⟩ := hd
  cases qle_total qzero d with
  | inl h => exact ⟨d, ⟨by rat_linarith, qle_refl _⟩, qEq_refl _, h, h2⟩
  | inr h => exact ⟨qneg d, ⟨qle_refl _, by rat_linarith⟩, by rat_ring, by rat_linarith, by rat_linarith⟩

/-- The bound of `step_SR`/`step_CR` against `ε_k + d²·H`, uniformly. -/
theorem sc_unif {A R : QExpr} (hA : qle qzero A) (hR : qle qzero R) : ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ m, N ≤ m + 2 →
    ∀ d a, qEq (qmul a a) (qmul d d) → qle qzero a → qle a R →
    qle (qadd (qadd (ZTrig.corner (tm A) (tm R) (m + 2)) (ZTrig.corner (tm A) (tm R) (m + 2)))
      (qadd (qmul (S A (m + 2)) (qmul (qmul a a) (S a m))) (qmul (S A (m + 2)) (qmul (qmul a a) (S a m)))))
      (qadd (qeps k) (qmul (qmul d d) H)) := by
  obtain ⟨HA, hHA⟩ := S_bounded hA
  obtain ⟨HR, hHR⟩ := S_bounded hR
  have HA0 : qle qzero HA := qle_trans (S_nonneg hA 0) (hHA 0)
  have HR0 : qle qzero HR := qle_trans (S_nonneg hR 0) (hHR 0)
  refine ⟨qadd (qmul HA HR) (qmul HA HR), by have := qmul_nonneg HA0 HR0; rat_linarith, fun k => ?_⟩
  obtain ⟨Nc, hNc⟩ := ZTrig.corner_small hA hR (k + 1)
  refine ⟨Nc, fun m hm d a aa a0 aR => ?_⟩
  have c := hNc (m + 2) hm
  have e := qeps_succ_add k
  have dd := qmul_self_nonneg d
  have sa : qle (S a m) HR := qle_trans (ZTrig.S_mono_x a0 aR m) (hHR m)
  have sa0 := S_nonneg a0 m
  have sA := hHA (m + 2)
  have sA0 := S_nonneg hA (m + 2)
  have f1 := scale_l sa (qmul_self_nonneg a)
  have f2 := scale_l f1 sA0
  have f3 := ZExp.scale sA (qmul_nonneg (qmul_self_nonneg a) HR0)
  have r1 := qmul_respects aa (qEq_refl HR)
  have r2 : qEq (qmul HA (qmul (qmul d d) HR)) (qmul (qmul d d) (qmul HA HR)) := by rat_ring
  have r3 := qmul_respects (qEq_refl HA) r1
  have r4 : qEq (qmul (qmul d d) (qadd (qmul HA HR) (qmul HA HR))) (qadd (qmul (qmul d d) (qmul HA HR)) (qmul (qmul d d) (qmul HA HR))) := by rat_ring
  generalize ZTrig.corner (tm A) (tm R) (m + 2) = K at *
  generalize qmul (S A (m + 2)) (qmul (qmul a a) (S a m)) = P1 at *
  generalize qmul (S A (m + 2)) (qmul (qmul a a) HR) = P2 at *
  generalize qmul HA (qmul (qmul a a) HR) = P3 at *
  generalize qmul HA (qmul (qmul d d) HR) = P4 at *
  generalize qmul (qmul d d) (qadd (qmul HA HR) (qmul HA HR)) = P5 at *
  generalize qmul (qmul d d) (qmul HA HR) = P6 at *
  clear hHA hHR hNc
  rat_linarith

/-- `sin` has a uniform step, derivative `cos`. -/
theorem ustep_S : UStep (fun x n => ZTrig.Sn x n) (fun x n => ZTrig.Cn x n) := by
  intro A R hA hR
  obtain ⟨H, H0, hH⟩ := sc_unif hA hR
  refine ⟨H, H0, fun k => ?_⟩
  obtain ⟨N, hN⟩ := hH k
  refine ⟨N + 2, fun n hn x d hx hd => ?_⟩
  obtain ⟨a, ha, aa, a0, aR⟩ := abs_le hd
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n' => cases n' with
    | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
    | succ m =>
      have b := hN m (Nat.le_trans (Nat.le_add_right N 2) hn) d a aa a0 aR
      obtain ⟨s1, s2⟩ := step_SR hx hd ha m
      exact ⟨qle_trans (by rat_linarith) s1, qle_trans s2 b⟩

/-- `cos` has a uniform step, derivative `−sin`. -/
theorem ustep_C : UStep (fun x n => ZTrig.Cn x n) (fun x n => qneg (ZTrig.Sn x n)) := by
  intro A R hA hR
  obtain ⟨H, H0, hH⟩ := sc_unif hA hR
  refine ⟨H, H0, fun k => ?_⟩
  obtain ⟨N, hN⟩ := hH k
  refine ⟨N + 2, fun n hn x d hx hd => ?_⟩
  obtain ⟨a, ha, aa, a0, aR⟩ := abs_le hd
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n' => cases n' with
    | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
    | succ m =>
      have b := hN m (Nat.le_trans (Nat.le_add_right N 2) hn) d a aa a0 aR
      obtain ⟨s1, s2⟩ := step_CR hx hd ha m
      exact ⟨qle_trans (by rat_linarith) s1, qle_trans s2 b⟩

theorem exp_case_pos {Eb Ea t d R H e P8 : QExpr}
    (l1 : qle (qmul d (qsub Ea t)) (qsub Eb Ea)) (u1 : qle (qsub Eb Ea) (qmul d Eb))
    (s1 : qle (qmul d (qsub Eb Ea)) (qmul d (qmul d Eb))) (s2 : qle (qmul (qmul d d) Eb) (qmul (qmul d d) H))
    (s3 : qle (qmul d t) (qmul R t)) (tl : qle (qmul R t) e) (p8 : qEq P8 (qmul (qmul d d) H)) (p80 : qle qzero P8) (e0 : qle qzero e) :
    ZTrig.Ab (qsub (qsub Eb Ea) (qmul d Ea)) (qadd e P8) := by
  have i1 : qEq (qmul d (qsub Ea t)) (qsub (qmul d Ea) (qmul d t)) := by unfold qsub; rat_ring
  have i2 : qEq (qmul d (qsub Eb Ea)) (qsub (qmul d Eb) (qmul d Ea)) := by unfold qsub; rat_ring
  have i3 : qEq (qmul d (qmul d Eb)) (qmul (qmul d d) Eb) := by rat_ring
  generalize qmul d (qsub Ea t) = P1 at *; generalize qmul d Ea = P2 at *; generalize qmul d t = P3 at *
  generalize qmul d (qsub Eb Ea) = P4 at *; generalize qmul d Eb = P5 at *
  generalize qmul d (qmul d Eb) = P6 at *; generalize qmul (qmul d d) Eb = P7 at *
  generalize qmul (qmul d d) H = P9 at *; generalize qmul R t = P10 at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem exp_case_neg {Eb Ea t d R H e P8 : QExpr}
    (l2 : qle (qmul (qneg d) (qsub Eb t)) (qsub Ea Eb)) (u2 : qle (qsub Ea Eb) (qmul (qneg d) Ea))
    (s1 : qle (qmul (qneg d) (qmul d Ea)) (qmul (qneg d) (qsub Eb Ea))) (s2 : qle (qmul (qmul d d) Ea) (qmul (qmul d d) H))
    (s3 : qle (qmul (qneg d) t) (qmul R t)) (tl : qle (qmul R t) e) (p8 : qEq P8 (qmul (qmul d d) H)) (p80 : qle qzero P8) (e0 : qle qzero e) :
    ZTrig.Ab (qsub (qsub Eb Ea) (qmul d Ea)) (qadd e P8) := by
  have i1 : qEq (qmul (qneg d) (qsub Eb t)) (qadd (qneg (qmul d Eb)) (qmul d t)) := by unfold qsub; rat_ring
  have i2 : qEq (qmul (qneg d) (qmul d Ea)) (qneg (qmul (qmul d d) Ea)) := by rat_ring
  have i3 : qEq (qmul (qneg d) (qsub Eb Ea)) (qadd (qneg (qmul d Eb)) (qmul d Ea)) := by unfold qsub; rat_ring
  have i4 : qEq (qmul (qneg d) Ea) (qneg (qmul d Ea)) := by rat_ring
  have i5 : qEq (qmul (qneg d) t) (qneg (qmul d t)) := by rat_ring
  generalize qmul (qneg d) (qsub Eb t) = P1 at *; generalize qmul (qneg d) Ea = P2 at *
  generalize qmul (qneg d) (qmul d Ea) = P3 at *; generalize qmul (qneg d) (qsub Eb Ea) = P4 at *
  generalize qmul (qneg d) t = P5 at *
  generalize qmul d Eb = Q1 at *; generalize qmul d Ea = Q2 at *; generalize qmul d t = Q3 at *
  generalize qmul (qmul d d) Ea = Q4 at *; generalize qmul (qmul d d) H = Q5 at *; generalize qmul R t = Q6 at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `exp` has a uniform step, derivative itself (`E_slope` twice). -/
theorem ustep_E : UStep (fun x n => eseq x n) (fun x n => eseq x n) := by
  intro A R hA hR
  have o := qle_of_qlt qone_pos
  have hR' : qle qzero (qadd A R) := by rat_linarith
  obtain ⟨H, hH⟩ := S_bounded hR'
  have H0 : qle qzero H := qle_trans (S_nonneg hR' 0) (hH 0)
  refine ⟨H, H0, fun k => ?_⟩
  obtain ⟨Bc, hBc⟩ := eps_scaled hR
  obtain ⟨K, hg⟩ := good_exists (qadd A R)
  obtain ⟨Nt, _, hNt⟩ := tm_small hR' hg (k + Bc)
  refine ⟨Nt + 1, fun n hn x d hx hd => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ m =>
    have ht := hNt m (Nat.le_of_succ_le_succ hn)
    have t0 := tm_nonneg hR' m
    have be := hBc k
    have sR := scale_l (show qle (tm (qadd A R) m) (qeps (k + Bc)) by rat_linarith) hR
    have c1 := qmul_comm R (qeps (k + Bc))
    obtain ⟨x1, x2⟩ := hx; obtain ⟨d1, d2⟩ := hd
    have qx : qclose x qzero (qadd A R) := by unfold qclose qsub; exact ⟨by rat_linarith, by rat_linarith⟩
    have qxd : qclose (qadd x d) qzero (qadd A R) := by unfold qclose qsub; exact ⟨by rat_linarith, by rat_linarith⟩
    have Eb := E_le_SR qxd m
    have Ea := E_le_SR qx m
    have Eb0 := E_nonneg (qadd x d) m
    have Ea0 := E_nonneg x m
    have sH := hH (m + 1)
    have dd := qmul_self_nonneg d
    have tl : qle (qmul R (tm (qadd A R) m)) (qeps k) := by
      generalize qmul R (tm (qadd A R) m) = P at *; generalize qmul R (qeps (k + Bc)) = Q at *
      generalize qmul (qeps (k + Bc)) R = Q' at *; rat_linarith
    show ZTrig.Ab (qsub (qsub (eseq (qadd x d) (m + 1)) (eseq x (m + 1))) (qmul d (eseq x (m + 1)))) _
    cases qle_total qzero d with
    | inl h =>
      obtain ⟨l1, u1⟩ := E_slope (show qle x (qadd x d) by rat_linarith) qx qxd m
      have e1 : qEq (qsub (qadd x d) x) d := by unfold qsub; rat_ring
      have l1' := qle_respects (qmul_respects e1 (qEq_refl _)) (qEq_refl _) l1
      have u1' := qle_respects (qEq_refl _) (qmul_respects e1 (qEq_refl _)) u1
      have s1 := scale_l u1' h
      have s2 := scale_l (qle_trans Eb sH) dd
      have s3 := ZExp.scale d2 t0
      exact exp_case_pos l1' u1' s1 s2 s3 tl (qEq_refl _) (qmul_nonneg dd H0) (qeps_nonneg k)
    | inr h =>
      obtain ⟨l2, u2⟩ := E_slope (show qle (qadd x d) x by rat_linarith) qxd qx m
      have e2 : qEq (qsub x (qadd x d)) (qneg d) := by unfold qsub; rat_ring
      have l2' := qle_respects (qmul_respects e2 (qEq_refl _)) (qEq_refl _) l2
      have u2' := qle_respects (qEq_refl _) (qmul_respects e2 (qEq_refl _)) u2
      -- d·E(x) ≤ E(x+d) − E(x), times −d ≥ 0
      have v : qle (qmul d (eseq x (m + 1))) (qsub (eseq (qadd x d) (m + 1)) (eseq x (m + 1))) := by
        have r : qEq (qmul (qneg d) (eseq x (m + 1))) (qneg (qmul d (eseq x (m + 1)))) := by rat_ring
        generalize qmul (qneg d) (eseq x (m + 1)) = P at *; generalize qmul d (eseq x (m + 1)) = Q at *
        unfold qsub at *; rat_linarith
      have s1 := scale_l v (show qle qzero (qneg d) by rat_linarith)
      have s2 := scale_l (qle_trans Ea sH) dd
      have s3 := ZExp.scale (show qle (qneg d) R by rat_linarith) t0
      exact exp_case_neg l2' u2' s1 s2 s3 tl (qEq_refl _) (qmul_nonneg dd H0) (qeps_nonneg k)

/-- The composition's step, as algebra: `O1` the outer step at `Δ = δ·DU + Eu`, `ψU·Eu` the inner error. -/
theorem comp_alg {O1 ψU Eu δ DU e Hφ Hu Mdu Mψ : QExpr}
    (hO1 : ZTrig.Ab O1 (qadd e (qmul (qmul (qadd (qmul δ DU) Eu) (qadd (qmul δ DU) Eu)) Hφ)))
    (hEu : ZTrig.Ab Eu (qadd e (qmul (qmul δ δ) Hu))) (hψ : ZTrig.Ab ψU Mψ) (hDU : ZTrig.Ab DU Mdu)
    (hδ : ZTrig.Ab δ qone) (e0 : qle qzero e) (e1 : qle e qone) (hHφ : qle qzero Hφ) (hHu : qle qzero Hu) :
    ZTrig.Ab (qadd O1 (qmul ψU Eu))
      (qadd (qmul e (qadd (qadd qone (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hφ)) Mψ))
        (qmul (qmul δ δ) (qadd (qmul Hφ (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)))
          (qmul Mψ Hu)))) := by
  have o := qle_of_qlt qone_pos
  have dd0 := qmul_self_nonneg δ
  obtain ⟨_, dd1⟩ := ZTrig.mul_abs hδ hδ
  have dd1' : qle (qmul δ δ) qone := by have : qEq (qmul qone qone) qone := by rat_ring
                                        generalize qmul qone qone = P at *; generalize qmul δ δ = Q at *; rat_linarith
  -- Δ² ≤ 2(δ·DU)² + 2·Eu²
  have sq := qmul_self_nonneg (qsub (qmul δ DU) Eu)
  have sqid : qEq (qmul (qadd (qmul δ DU) Eu) (qadd (qmul δ DU) Eu))
      (qsub (qadd (qadd (qmul (qmul δ δ) (qmul DU DU)) (qmul (qmul δ δ) (qmul DU DU))) (qadd (qmul Eu Eu) (qmul Eu Eu)))
        (qmul (qsub (qmul δ DU) Eu) (qsub (qmul δ DU) Eu))) := by unfold qsub; rat_ring
  obtain ⟨_, du2⟩ := ZTrig.mul_abs hDU hDU
  have a2 := scale_l du2 dd0
  have hEu1 : ZTrig.Ab Eu (qadd qone Hu) := by
    obtain ⟨u1, u2⟩ := hEu
    have s := scale_l dd1' hHu
    have r : qEq (qmul Hu (qmul δ δ)) (qmul (qmul δ δ) Hu) := qmul_comm _ _
    have r1 : qEq (qmul Hu qone) Hu := by rat_ring
    generalize qmul (qmul δ δ) Hu = P at *; generalize qmul Hu (qmul δ δ) = P' at *; generalize qmul Hu qone = P'' at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨_, eu2⟩ := ZTrig.mul_abs hEu hEu1
  -- the pieces
  obtain ⟨o1, o2⟩ := hO1
  obtain ⟨p1, p2⟩ := ZTrig.mul_abs hψ hEu
  have Dle : qle (qmul (qadd (qmul δ DU) Eu) (qadd (qmul δ DU) Eu))
      (qadd (qadd (qmul (qmul δ δ) (qmul Mdu Mdu)) (qmul (qmul δ δ) (qmul Mdu Mdu)))
        (qadd (qmul (qadd e (qmul (qmul δ δ) Hu)) (qadd qone Hu)) (qmul (qadd e (qmul (qmul δ δ) Hu)) (qadd qone Hu)))) := by
    generalize qmul (qadd (qmul δ DU) Eu) (qadd (qmul δ DU) Eu) = D2 at *
    generalize qmul (qsub (qmul δ DU) Eu) (qsub (qmul δ DU) Eu) = SQ at *
    generalize qmul (qmul δ δ) (qmul DU DU) = A1 at *; generalize qmul (qmul δ δ) (qmul Mdu Mdu) = A2 at *
    generalize qmul Eu Eu = B1 at *; generalize qmul (qadd e (qmul (qmul δ δ) Hu)) (qadd qone Hu) = B2 at *
    unfold qsub at sqid; rat_linarith
  have DH := ZExp.scale Dle hHφ
  have fin : qEq (qadd (qadd e (qmul (qadd (qadd (qmul (qmul δ δ) (qmul Mdu Mdu)) (qmul (qmul δ δ) (qmul Mdu Mdu)))
        (qadd (qmul (qadd e (qmul (qmul δ δ) Hu)) (qadd qone Hu)) (qmul (qadd e (qmul (qmul δ δ) Hu)) (qadd qone Hu)))) Hφ))
        (qmul Mψ (qadd e (qmul (qmul δ δ) Hu))))
      (qadd (qmul e (qadd (qadd qone (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hφ)) Mψ))
        (qmul (qmul δ δ) (qadd (qmul Hφ (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)))
          (qmul Mψ Hu)))) := by rat_ring
  generalize qmul (qadd (qmul δ DU) Eu) (qadd (qmul δ DU) Eu) = D2 at *
  generalize qmul (qadd (qadd (qmul (qmul δ δ) (qmul Mdu Mdu)) (qmul (qmul δ δ) (qmul Mdu Mdu)))
        (qadd (qmul (qadd e (qmul (qmul δ δ) Hu)) (qadd qone Hu)) (qmul (qadd e (qmul (qmul δ δ) Hu)) (qadd qone Hu)))) Hφ = RH at *
  generalize qmul D2 Hφ = DHφ at *
  generalize qmul Mψ (qadd e (qmul (qmul δ δ) Hu)) = MP at *
  generalize qadd (qmul e (qadd (qadd qone (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hφ)) Mψ))
        (qmul (qmul δ δ) (qadd (qmul Hφ (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)))
          (qmul Mψ Hu))) = W at *
  generalize qmul ψU Eu = PE at *
  clear sq sqid du2 a2 eu2 hEu1 Dle
  have up : qle (qadd O1 PE) W := by rat_linarith
  have lo : qle (qneg W) (qadd O1 PE) := by rat_linarith
  exact ⟨lo, up⟩

/-- THE CHAIN RULE, as a step: an outer function with a uniform step after an inner step. -/
theorem comp_step {φ ψ : QExpr → Nat → QExpr} (hφ : UStep φ ψ) (hφr : ∀ x y n, qEq x y → qEq (φ x n) (φ y n))
    {Mu Mdu Mψ Hu : QExpr} (mu0 : qle qzero Mu) (mdu0 : qle qzero Mdu) (mψ0 : qle qzero Mψ) (hu0 : qle qzero Hu) :
    ∃ H, qle qzero H ∧ ∀ (U V DU : Nat → QExpr) (δ : QExpr), ZTrig.Ab δ qone →
      (∀ k, ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qsub (qsub (V n) (U n)) (qmul δ (DU n))) (qadd (qeps k) (qmul (qmul δ δ) Hu))) →
      (∃ N, ∀ n, N ≤ n → ZTrig.Ab (U n) Mu) → (∃ N, ∀ n, N ≤ n → ZTrig.Ab (DU n) Mdu) →
      (∃ N, ∀ n, N ≤ n → ZTrig.Ab (ψ (U n) n) Mψ) →
      ∀ k, ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qsub (qsub (φ (V n) n) (φ (U n) n)) (qmul δ (qmul (ψ (U n) n) (DU n))))
        (qadd (qeps k) (qmul (qmul δ δ) H)) := by
  have o := qle_of_qlt qone_pos
  have hR : qle qzero (qadd (qadd Mdu Hu) qone) := by rat_linarith
  obtain ⟨Hφ, hφ0, hφs⟩ := hφ mu0 hR
  have two : qle qzero (qadd (qadd qone qone) (qadd Hu Hu)) := by rat_linarith
  have H0 : qle qzero (qadd (qmul Hφ (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)))
      (qmul Mψ Hu)) := by
    have := qmul_nonneg mdu0 mdu0; have := qmul_nonneg two hu0
    have := qmul_nonneg hφ0 (show qle qzero (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)) by rat_linarith)
    have := qmul_nonneg mψ0 hu0; rat_linarith
  have C0 : qle qzero (qadd (qadd qone (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hφ)) Mψ) := by
    have := qmul_nonneg two hφ0; rat_linarith
  obtain ⟨Bc, hBc⟩ := eps_scaled C0
  refine ⟨_, H0, fun U V DU δ hδ hin hbU hbD hbψ k => ?_⟩
  obtain ⟨N1, h1⟩ := hφs (k + Bc)
  obtain ⟨N2, h2⟩ := hin (k + Bc)
  obtain ⟨N3, h3⟩ := hbU
  obtain ⟨N4, h4⟩ := hbD
  obtain ⟨N5, h5⟩ := hbψ
  refine ⟨N1 + (N2 + (N3 + (N4 + N5))), fun n hn => ?_⟩
  have eu := h2 n (ZTrig.le_l' (ZTrig.le_r' hn))
  have bu := h3 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' hn)))
  have bd := h4 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn))))
  have bp := h5 n (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn))))
  have e0 := qeps_nonneg (k + Bc)
  have e1 := ZTrig.qeps_le_one (k + Bc)
  have hd : ZTrig.Ab (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n)))) (qadd (qadd Mdu Hu) qone) := by
    obtain ⟨m1, m2⟩ := ZTrig.mul_abs hδ bd
    obtain ⟨u1, u2⟩ := eu
    obtain ⟨_, dd1⟩ := ZTrig.mul_abs hδ hδ
    have dd1' : qle (qmul δ δ) qone := by
      have : qEq (qmul qone qone) qone := by rat_ring
      generalize qmul qone qone = P at *; generalize qmul δ δ = Q at *; rat_linarith
    have s := scale_l dd1' hu0
    have r : qEq (qmul Hu (qmul δ δ)) (qmul (qmul δ δ) Hu) := qmul_comm _ _
    have r1 : qEq (qmul Hu qone) Hu := by rat_ring
    have r2 : qEq (qmul qone Mdu) Mdu := by rat_ring
    generalize qmul δ (DU n) = P at *; generalize qmul (qmul δ δ) Hu = Q at *
    generalize qmul Hu (qmul δ δ) = Q1 at *; generalize qmul Hu qone = Q2 at *; generalize qmul qone Mdu = Q3 at *
    generalize qsub (qsub (V n) (U n)) P = E at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  have ho := h1 n (ZTrig.le_l' hn) (U n) _ bu hd
  have rv : qEq (qadd (U n) (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n))))) (V n) := by unfold qsub; rat_ring
  have fv := hφr _ _ n rv
  have ca := comp_alg ho eu bp bd hδ e0 e1 hφ0 hu0
  have be := hBc k
  have r : qEq (qsub (qsub (φ (V n) n) (φ (U n) n)) (qmul δ (qmul (ψ (U n) n) (DU n))))
      (qadd (qsub (qsub (φ (V n) n) (φ (U n) n))
          (qmul (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n)))) (ψ (U n) n)))
        (qmul (ψ (U n) n) (qsub (qsub (V n) (U n)) (qmul δ (DU n))))) := by unfold qsub; rat_ring
  obtain ⟨c1, c2⟩ := ca
  generalize φ (qadd (U n) (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n))))) n = F1 at *
  generalize φ (V n) n = F2 at *
  generalize qmul (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n)))) (ψ (U n) n) = M1 at *
  generalize qmul (ψ (U n) n) (qsub (qsub (V n) (U n)) (qmul δ (DU n))) = M2 at *
  generalize qsub (qsub F2 (φ (U n) n)) (qmul δ (qmul (ψ (U n) n) (DU n))) = T at *
  generalize qmul (qeps (k + Bc)) (qadd (qadd qone (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hφ)) Mψ) = P at *
  generalize qmul (qmul δ δ) (qadd (qmul Hφ (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)))
      (qmul Mψ Hu)) = X at *
  clear h1 h2 h3 h4 h5 hφs hBc hin
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem ustep_C0 : UStep (fun x n => ZTrig.Cn x n) (fun x n => qsub qzero (ZTrig.Sn x n)) := by
  intro A R hA hR
  obtain ⟨H, H0, hH⟩ := ustep_C hA hR
  refine ⟨H, H0, fun k => ?_⟩
  obtain ⟨N, hN⟩ := hH k
  refine ⟨N, fun n hn x d hx hd => ?_⟩
  obtain ⟨a, b⟩ := hN n hn x d hx hd
  have e : qEq (qmul d (qsub qzero (ZTrig.Sn x n))) (qmul d (qneg (ZTrig.Sn x n))) := by unfold qsub; rat_ring
  generalize qmul d (qsub qzero (ZTrig.Sn x n)) = P at *; generalize qmul d (qneg (ZTrig.Sn x n)) = Q at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- A uniform step on a domain: as `UStep`, only where `dom` holds at `x` and at `x + d`. -/
def UStepOn (dom : QExpr → Nat → Prop) (φ ψ : QExpr → Nat → QExpr) : Prop :=
  ∀ {A R : QExpr}, qle qzero A → qle qzero R → ∃ H, qle qzero H ∧ ∀ k, ∃ N, ∀ n, N ≤ n → ∀ x d, ZTrig.Ab x A →
    ZTrig.Ab d R → dom x n → dom (qadd x d) n →
    ZTrig.Ab (qsub (qsub (φ (qadd x d) n) (φ x n)) (qmul d (ψ x n))) (qadd (qeps k) (qmul (qmul d d) H))

/-- THE CHAIN RULE ON A DOMAIN: the outer step needed only where `dom` holds at both points. -/
theorem comp_step_on {φ ψ : QExpr → Nat → QExpr} {dom : QExpr → Nat → Prop} (hφ : UStepOn dom φ ψ)
    (hφr : ∀ x y n, qEq x y → qEq (φ x n) (φ y n)) (hdr : ∀ x y n, qEq x y → dom x n → dom y n)
    {Mu Mdu Mψ Hu : QExpr} (mu0 : qle qzero Mu) (mdu0 : qle qzero Mdu) (mψ0 : qle qzero Mψ) (hu0 : qle qzero Hu) :
    ∃ H, qle qzero H ∧ ∀ (U V DU : Nat → QExpr) (δ : QExpr), ZTrig.Ab δ qone →
      (∀ k, ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qsub (qsub (V n) (U n)) (qmul δ (DU n))) (qadd (qeps k) (qmul (qmul δ δ) Hu))) →
      (∃ N, ∀ n, N ≤ n → ZTrig.Ab (U n) Mu) → (∃ N, ∀ n, N ≤ n → ZTrig.Ab (DU n) Mdu) →
      (∃ N, ∀ n, N ≤ n → ZTrig.Ab (ψ (U n) n) Mψ) →
      (∃ N, ∀ n, N ≤ n → dom (U n) n) → (∃ N, ∀ n, N ≤ n → dom (V n) n) →
      ∀ k, ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qsub (qsub (φ (V n) n) (φ (U n) n)) (qmul δ (qmul (ψ (U n) n) (DU n))))
        (qadd (qeps k) (qmul (qmul δ δ) H)) := by
  have o := qle_of_qlt qone_pos
  have hR : qle qzero (qadd (qadd Mdu Hu) qone) := by rat_linarith
  obtain ⟨Hφ, hφ0, hφs⟩ := hφ mu0 hR
  have two : qle qzero (qadd (qadd qone qone) (qadd Hu Hu)) := by rat_linarith
  have H0 : qle qzero (qadd (qmul Hφ (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)))
      (qmul Mψ Hu)) := by
    have := qmul_nonneg mdu0 mdu0; have := qmul_nonneg two hu0
    have := qmul_nonneg hφ0 (show qle qzero (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)) by rat_linarith)
    have := qmul_nonneg mψ0 hu0; rat_linarith
  have C0 : qle qzero (qadd (qadd qone (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hφ)) Mψ) := by
    have := qmul_nonneg two hφ0; rat_linarith
  obtain ⟨Bc, hBc⟩ := eps_scaled C0
  refine ⟨_, H0, fun U V DU δ hδ hin hbU hbD hbψ hdU hdV k => ?_⟩
  obtain ⟨N1, h1⟩ := hφs (k + Bc)
  obtain ⟨N2, h2⟩ := hin (k + Bc)
  obtain ⟨N3, h3⟩ := hbU
  obtain ⟨N4, h4⟩ := hbD
  obtain ⟨N5, h5⟩ := hbψ
  obtain ⟨N6, h6⟩ := hdU
  obtain ⟨N7, h7⟩ := hdV
  refine ⟨(N1 + (N2 + (N3 + (N4 + N5)))) + (N6 + N7), fun n hn' => ?_⟩
  have hn := ZTrig.le_l' hn'
  have du := h6 n (ZTrig.le_l' (ZTrig.le_r' hn'))
  have dv := h7 n (ZTrig.le_r' (ZTrig.le_r' hn'))
  have eu := h2 n (ZTrig.le_l' (ZTrig.le_r' hn))
  have bu := h3 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' hn)))
  have bd := h4 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn))))
  have bp := h5 n (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn))))
  have e0 := qeps_nonneg (k + Bc)
  have e1 := ZTrig.qeps_le_one (k + Bc)
  have hd : ZTrig.Ab (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n)))) (qadd (qadd Mdu Hu) qone) := by
    obtain ⟨m1, m2⟩ := ZTrig.mul_abs hδ bd
    obtain ⟨u1, u2⟩ := eu
    obtain ⟨_, dd1⟩ := ZTrig.mul_abs hδ hδ
    have dd1' : qle (qmul δ δ) qone := by
      have : qEq (qmul qone qone) qone := by rat_ring
      generalize qmul qone qone = P at *; generalize qmul δ δ = Q at *; rat_linarith
    have s := scale_l dd1' hu0
    have r : qEq (qmul Hu (qmul δ δ)) (qmul (qmul δ δ) Hu) := qmul_comm _ _
    have r1 : qEq (qmul Hu qone) Hu := by rat_ring
    have r2 : qEq (qmul qone Mdu) Mdu := by rat_ring
    generalize qmul δ (DU n) = P at *; generalize qmul (qmul δ δ) Hu = Q at *
    generalize qmul Hu (qmul δ δ) = Q1 at *; generalize qmul Hu qone = Q2 at *; generalize qmul qone Mdu = Q3 at *
    generalize qsub (qsub (V n) (U n)) P = E at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  have rv : qEq (qadd (U n) (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n))))) (V n) := by unfold qsub; rat_ring
  have ho := h1 n (ZTrig.le_l' hn) (U n) _ bu hd du (hdr _ _ n (qEq_symm rv) dv)
  have fv := hφr _ _ n rv
  have ca := comp_alg ho eu bp bd hδ e0 e1 hφ0 hu0
  have be := hBc k
  have r : qEq (qsub (qsub (φ (V n) n) (φ (U n) n)) (qmul δ (qmul (ψ (U n) n) (DU n))))
      (qadd (qsub (qsub (φ (V n) n) (φ (U n) n))
          (qmul (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n)))) (ψ (U n) n)))
        (qmul (ψ (U n) n) (qsub (qsub (V n) (U n)) (qmul δ (DU n))))) := by unfold qsub; rat_ring
  obtain ⟨c1, c2⟩ := ca
  generalize φ (qadd (U n) (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n))))) n = F1 at *
  generalize φ (V n) n = F2 at *
  generalize qmul (qadd (qmul δ (DU n)) (qsub (qsub (V n) (U n)) (qmul δ (DU n)))) (ψ (U n) n) = M1 at *
  generalize qmul (ψ (U n) n) (qsub (qsub (V n) (U n)) (qmul δ (DU n))) = M2 at *
  generalize qsub (qsub F2 (φ (U n) n)) (qmul δ (qmul (ψ (U n) n) (DU n))) = T at *
  generalize qmul (qeps (k + Bc)) (qadd (qadd qone (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hφ)) Mψ) = P at *
  generalize qmul (qmul δ δ) (qadd (qmul Hφ (qadd (qadd (qmul Mdu Mdu) (qmul Mdu Mdu)) (qmul (qadd (qadd qone qone) (qadd Hu Hu)) Hu)))
      (qmul Mψ Hu)) = X at *
  clear h1 h2 h3 h4 h5 h6 h7 hφs hBc hin
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The reciprocal's step, exactly: `1/(x + d) − 1/x + d/x² = d²·(1/x)²·(1/(x + d))`. -/
theorem inv_id {x d ix iy : QExpr} (hu : qEq (qmul x ix) qone) (hv : qEq (qmul (qadd x d) iy) qone) :
    qEq (qsub (qsub iy ix) (qmul d (qneg (qmul ix ix)))) (qmul (qmul (qmul ix ix) iy) (qmul d d)) := by
  have R : qEq (qmul (qmul (qmul ix ix) iy) (qmul d d))
      (qadd (qsub (qmul (qmul ix ix) (qmul (qadd x d) (qmul (qadd x d) iy)))
        (qmul (qmul (qadd ix ix) (qmul x ix)) (qmul (qadd x d) iy))) (qmul (qmul (qmul x ix) (qmul x ix)) iy)) := by
    unfold qsub; rat_ring
  have a1 := qmul_respects (qEq_refl (qmul ix ix)) (qmul_respects (qEq_refl (qadd x d)) hv)
  have a2 := qmul_respects (qmul_respects (qEq_refl (qadd ix ix)) hu) hv
  have a3 := qmul_respects (qmul_respects hu hu) (qEq_refl iy)
  have b1 : qEq (qmul (qmul ix ix) (qmul (qadd x d) qone)) (qadd (qmul ix (qmul x ix)) (qmul d (qmul ix ix))) := by rat_ring
  have b2 := qmul_respects (qEq_refl ix) hu
  have o1 : qEq (qmul (qmul (qadd ix ix) qone) qone) (qadd ix ix) := by rat_ring
  have o2 : qEq (qmul (qmul qone qone) iy) iy := by rat_ring
  have o3 : qEq (qmul ix qone) ix := by rat_ring
  have l : qEq (qmul d (qneg (qmul ix ix))) (qneg (qmul d (qmul ix ix))) := by rat_ring
  generalize qmul (qmul (qmul ix ix) iy) (qmul d d) = P at *
  generalize qmul (qmul ix ix) (qmul (qadd x d) (qmul (qadd x d) iy)) = A1 at *
  generalize qmul (qmul (qadd ix ix) (qmul x ix)) (qmul (qadd x d) iy) = A2 at *
  generalize qmul (qmul (qmul x ix) (qmul x ix)) iy = A3 at *
  generalize qmul (qmul ix ix) (qmul (qadd x d) qone) = B1 at *
  generalize qmul (qmul (qadd ix ix) qone) qone = C1 at *
  generalize qmul (qmul qone qone) iy = C2 at *
  generalize qmul ix (qmul x ix) = C3 at *; generalize qmul ix qone = C4 at *
  generalize qmul d (qneg (qmul ix ix)) = L1 at *; generalize qmul d (qmul ix ix) = L2 at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `1/x` has a uniform step on `x ≥ c > 0`, derivative `−1/x²` (exact; the bound `d²/c³`). -/
theorem ustep_inv {c : QExpr} (hc : qlt qzero c) :
    UStepOn (fun x _ => qle c x) (fun x _ => qinv' x) (fun x _ => qneg (qmul (qinv' x) (qinv' x))) := by
  intro A R hA hR
  have ic0 := qinv'_nonneg_of_pos hc
  refine ⟨qmul (qmul (qinv' c) (qinv' c)) (qinv' c), qmul_nonneg (qmul_nonneg ic0 ic0) ic0, fun k => ⟨0, fun n _ x d _ _ hx hy => ?_⟩⟩
  have xp : qlt qzero x := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hc) hx, fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hx h)⟩
  have yp : qlt qzero (qadd x d) := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hc) hy,
    fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans hy h)⟩
  have id := inv_id (d := d) (qmul_inv'_cancel (ne_zero_of_lt xp)) (qmul_inv'_cancel (ne_zero_of_lt yp))
  obtain ⟨i0, i1⟩ := ZTrig.inv_bound hc hx
  obtain ⟨j0, j1⟩ := ZTrig.inv_bound hc hy
  have dd := qmul_self_nonneg d
  have s1 := ZExp.scale (show qle (qmul (qmul (qinv' x) (qinv' x)) (qinv' (qadd x d))) (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) by
    have t1 := scale_l i1 i0
    have t2 := ZExp.scale i1 ic0
    have t3 := scale_l j1 (qmul_nonneg i0 i0)
    have t4 := ZExp.scale (qle_trans t1 t2) ic0
    exact qle_trans t3 t4) dd
  have p0 := qmul_nonneg (qmul_nonneg i0 i0) j0
  have p1 := qmul_nonneg p0 dd
  have e0 := qeps_nonneg k
  have c1 := qmul_comm (qmul d d) (qmul (qmul (qinv' c) (qinv' c)) (qinv' c))
  show ZTrig.Ab (qsub (qsub (qinv' (qadd x d)) (qinv' x)) (qmul d (qneg (qmul (qinv' x) (qinv' x))))) _
  generalize qsub (qsub (qinv' (qadd x d)) (qinv' x)) (qmul d (qneg (qmul (qinv' x) (qinv' x)))) = E at *
  generalize qmul (qmul (qmul (qinv' x) (qinv' x)) (qinv' (qadd x d))) (qmul d d) = P at *
  generalize qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qmul d d) = Q at *
  generalize qmul (qmul d d) (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) = Q' at *
  generalize qmul (qmul (qinv' x) (qinv' x)) (qinv' (qadd x d)) = P' at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `|1/x| ≤ 1/c` for `x ≤ −c`, `c > 0`. -/
theorem inv_bound_neg {x c : QExpr} (hc : qlt qzero c) (hx : qle x (qneg c)) : ZTrig.Ab (qinv' x) (qinv' c) := by
  have nx : qle c (qneg x) := by rat_linarith
  obtain ⟨i0, i1⟩ := ZTrig.inv_bound hc nx
  have xn : ¬ qEq x qzero := fun h => (qlt_iff_le_not_le.mp hc).2 (by rat_linarith)
  have e := qinv'_neg xn
  generalize qinv' (qneg x) = P at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `1/x` has a uniform step on `x ≤ −c < 0`, derivative `−1/x²`. -/
theorem ustep_inv_neg {c : QExpr} (hc : qlt qzero c) :
    UStepOn (fun x _ => qle x (qneg c)) (fun x _ => qinv' x) (fun x _ => qneg (qmul (qinv' x) (qinv' x))) := by
  intro A R hA hR
  have ic0 := qinv'_nonneg_of_pos hc
  refine ⟨qmul (qmul (qinv' c) (qinv' c)) (qinv' c), qmul_nonneg (qmul_nonneg ic0 ic0) ic0, fun k => ⟨0, fun n _ x d _ _ hx hy => ?_⟩⟩
  have ne : ∀ y, qle y (qneg c) → ¬ qEq y qzero := fun y hy h => (qlt_iff_le_not_le.mp hc).2 (by rat_linarith)
  have id := inv_id (d := d) (qmul_inv'_cancel (ne x hx)) (qmul_inv'_cancel (ne _ hy))
  have bx := inv_bound_neg hc hx
  have by' := inv_bound_neg hc hy
  have dd : ZTrig.Ab (qmul d d) (qmul d d) := ⟨by have := qmul_self_nonneg d; rat_linarith, qle_refl _⟩
  obtain ⟨s1, s2⟩ := ZTrig.mul_abs (ZTrig.mul_abs (ZTrig.mul_abs bx bx) by') dd
  have e0 := qeps_nonneg k
  have c1 := qmul_comm (qmul d d) (qmul (qmul (qinv' c) (qinv' c)) (qinv' c))
  show ZTrig.Ab (qsub (qsub (qinv' (qadd x d)) (qinv' x)) (qmul d (qneg (qmul (qinv' x) (qinv' x))))) _
  generalize qsub (qsub (qinv' (qadd x d)) (qinv' x)) (qmul d (qneg (qmul (qinv' x) (qinv' x)))) = E at *
  generalize qmul (qmul (qmul (qinv' x) (qinv' x)) (qinv' (qadd x d))) (qmul d d) = P at *
  generalize qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qmul d d) = Q at *
  generalize qmul (qmul d d) (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) = Q' at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- The quotient rule's form: `(Du·v − u·Dv)·1/(v·v) = Du·(1/v) + u·(−(1/v)²·Dv)`, `v ≠ 0`. -/
theorem quot_form {du v u dv : QExpr} (hv : ¬ qEq v qzero) :
    qEq (qmul (qsub (qmul du v) (qmul u dv)) (qinv' (qmul v v)))
      (qadd (qmul du (qinv' v)) (qmul u (qmul (qneg (qmul (qinv' v) (qinv' v))) dv))) := by
  have m := qinv'_mul hv hv
  have c := qmul_inv'_cancel hv
  have e1 := qmul_respects (qEq_refl (qsub (qmul du v) (qmul u dv))) m
  have e2 : qEq (qmul (qsub (qmul du v) (qmul u dv)) (qmul (qinv' v) (qinv' v)))
      (qsub (qmul (qmul du (qinv' v)) (qmul v (qinv' v))) (qmul (qmul u dv) (qmul (qinv' v) (qinv' v)))) := by unfold qsub; rat_ring
  have e3 := qmul_respects (qEq_refl (qmul du (qinv' v))) c
  have o : qEq (qmul (qmul du (qinv' v)) qone) (qmul du (qinv' v)) := by rat_ring
  have e4 : qEq (qmul u (qmul (qneg (qmul (qinv' v) (qinv' v))) dv)) (qneg (qmul (qmul u dv) (qmul (qinv' v) (qinv' v)))) := by
    rat_ring
  generalize qmul (qsub (qmul du v) (qmul u dv)) (qinv' (qmul v v)) = L at *
  generalize qmul (qsub (qmul du v) (qmul u dv)) (qmul (qinv' v) (qinv' v)) = L' at *
  generalize qmul (qmul du (qinv' v)) (qmul v (qinv' v)) = P1 at *
  generalize qmul (qmul u dv) (qmul (qinv' v) (qinv' v)) = P2 at *
  generalize qmul (qmul du (qinv' v)) qone = P3 at *
  generalize qmul du (qinv' v) = P4 at *
  generalize qmul u (qmul (qneg (qmul (qinv' v) (qinv' v))) dv) = P5 at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE QUOTIENT'S STEP from `u`'s step and `1/v`'s step (`W`), the bounds, `v` clear of zero. -/
theorem div_step {i : Nat} {u v : G} {p q : Point QExpr} {Hu HW Mu Mdu Mw Mdw : QExpr}
    (hu0 : qle qzero Hu) (hw0 : qle qzero HW) (mu0 : qle qzero Mu) (mdu0 : qle qzero Mdu) (mw0 : qle qzero Mw)
    (mdw0 : qle qzero Mdw) (hδ : ZTrig.Ab (qsub (q i) (p i)) qone) (su : StepAt i u Hu p q)
    (sw : ∀ k, ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qsub (qsub (qinv' (evalN n q v)) (qinv' (evalN n p v)))
        (qmul (qsub (q i) (p i)) (qmul (qneg (qmul (qinv' (evalN n p v)) (qinv' (evalN n p v)))) (evalN n p (D i v)))))
        (qadd (qeps k) (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) HW)))
    (bw : ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qinv' (evalN n q v)) Mw) (bu : ∃ N, ∀ n, N ≤ n → ZTrig.Ab (evalN n p u) Mu)
    (bdu : ∃ N, ∀ n, N ≤ n → ZTrig.Ab (evalN n p (D i u)) Mdu)
    (bdw : ∃ N, ∀ n, N ≤ n → ZTrig.Ab (qmul (qneg (qmul (qinv' (evalN n p v)) (qinv' (evalN n p v)))) (evalN n p (D i v))) Mdw)
    (nz : ∃ N, ∀ n, N ≤ n → ¬ qEq (evalN n p v) qzero) :
    StepAt i (.div u v) (qadd (qadd (qmul Hu Mw) (qmul Mu HW)) (qadd (qmul Mdu Mdw) (qmul Mdu HW))) p q := by
  have o := qle_of_qlt qone_pos
  obtain ⟨Bc, hBc⟩ := eps_scaled (C := qadd (qadd Mw Mu) Mdu) (by rat_linarith)
  intro k
  obtain ⟨N1, h1⟩ := su (k + Bc)
  obtain ⟨N2, h2⟩ := sw (k + Bc)
  obtain ⟨N3, h3⟩ := bw
  obtain ⟨N4, h4⟩ := bu
  obtain ⟨N5, h5⟩ := bdu
  obtain ⟨N6, h6⟩ := bdw
  obtain ⟨N7, h7⟩ := nz
  refine ⟨(N1 + (N2 + (N3 + (N4 + N5)))) + (N6 + N7), fun n hn' => ?_⟩
  have hn := ZTrig.le_l' hn'
  have m := mul_step (h1 n (ZTrig.le_l' hn)) (h2 n (ZTrig.le_l' (ZTrig.le_r' hn)))
    (h3 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' hn)))) (h4 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn)))))
    (h5 n (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn))))) (h6 n (ZTrig.le_l' (ZTrig.le_r' hn'))) hδ
  have qf := quot_form (du := evalN n p (D i u)) (u := evalN n p u) (dv := evalN n p (D i v)) (h7 n (ZTrig.le_r' (ZTrig.le_r' hn')))
  have be := hBc k
  obtain ⟨m1, m2⟩ := m
  have sd := qmul_respects (qEq_refl (qsub (q i) (p i))) qf
  show ZTrig.Ab (qsub (qsub (qmul (evalN n q u) (qinv' (evalN n q v))) (qmul (evalN n p u) (qinv' (evalN n p v))))
    (qmul (qsub (q i) (p i)) (qmul (qsub (qmul (evalN n p (D i u)) (evalN n p v)) (qmul (evalN n p u) (evalN n p (D i v))))
      (qinv' (qmul (evalN n p v) (evalN n p v)))))) _
  generalize qmul (qsub (q i) (p i)) (qmul (qsub (qmul (evalN n p (D i u)) (evalN n p v)) (qmul (evalN n p u) (evalN n p (D i v))))
      (qinv' (qmul (evalN n p v) (evalN n p v)))) = T1 at *
  generalize qmul (qsub (q i) (p i)) (qadd (qmul (evalN n p (D i u)) (qinv' (evalN n p v)))
      (qmul (evalN n p u) (qmul (qneg (qmul (qinv' (evalN n p v)) (qinv' (evalN n p v)))) (evalN n p (D i v))))) = T2 at *
  generalize qmul (evalN n q u) (qinv' (evalN n q v)) = A at *
  generalize qmul (evalN n p u) (qinv' (evalN n p v)) = A' at *
  generalize qmul (qeps (k + Bc)) (qadd (qadd Mw Mu) Mdu) = P at *
  generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i)))
      (qadd (qadd (qmul Hu Mw) (qmul Mu HW)) (qadd (qmul Mdu Mdw) (qmul Mdu HW))) = X at *
  clear h1 h2 h3 h4 h5 h6 h7 hBc su sw qf
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem qadd_nn {a b : QExpr} (ha : qle qzero a) (hb : qle qzero b) : qle qzero (qadd a b) := by rat_linarith

theorem pow_abs {x A : QExpr} (hx : ZTrig.Ab x A) : ∀ k, ZTrig.Ab (qpowN x k) (qpowN A k)
  | 0 => ⟨by have := qle_of_qlt qone_pos; show qle (qneg qone) qone; rat_linarith, qle_refl _⟩
  | k + 1 => ZTrig.mul_abs (pow_abs hx k) hx

/-- The power's error constant: `H_1 = 0`, `H_{k+2} = H_{k+1}·(A + R) + (k + 1)·A^k`. -/
def Hpow (A R : QExpr) : Nat → QExpr
  | 0 => qzero
  | 1 => qzero
  | k + 2 => qadd (qmul (Hpow A R (k + 1)) (qadd A R)) (qmul (qnat (k + 1)) (qpowN A k))

theorem Hpow_nonneg {A R : QExpr} (hA : qle qzero A) (hR : qle qzero R) : ∀ k, qle qzero (Hpow A R k)
  | 0 => qle_refl _
  | 1 => qle_refl _
  | k + 2 => by
      have h := Hpow_nonneg hA hR (k + 1)
      have p := qmul_nonneg h (show qle qzero (qadd A R) by rat_linarith)
      have q := qmul_nonneg (qnat_nonneg (k + 1)) (powN_nonneg hA k)
      show qle qzero (qadd (qmul (Hpow A R (k + 1)) (qadd A R)) (qmul (qnat (k + 1)) (qpowN A k))); rat_linarith

/-- The power's step, as algebra: `E_{k+2} = E_{k+1}·(x + d) + d²·(k + 1)·x^k`. -/
theorem pow_rec (x d : QExpr) (k : Nat) :
    qEq (qsub (qsub (qpowN (qadd x d) (k + 2)) (qpowN x (k + 2))) (qmul d (qmul (qnat (k + 2)) (qpowN x (k + 1)))))
      (qadd (qmul (qsub (qsub (qpowN (qadd x d) (k + 1)) (qpowN x (k + 1))) (qmul d (qmul (qnat (k + 1)) (qpowN x k)))) (qadd x d))
        (qmul (qmul d d) (qmul (qnat (k + 1)) (qpowN x k)))) := by
  have n := qnat_succ (k + 1)
  have r := qmul_respects (qEq_refl d) (qmul_respects n (qEq_refl (qpowN x (k + 1))))
  show qEq (qsub (qsub (qmul (qpowN (qadd x d) (k + 1)) (qadd x d)) (qmul (qmul (qpowN x k) x) x))
      (qmul d (qmul (qnat (k + 2)) (qmul (qpowN x k) x)))) _
  have r' : qEq (qmul d (qmul (qnat (k + 2)) (qmul (qpowN x k) x))) (qmul d (qmul (qadd (qnat (k + 1)) qone) (qmul (qpowN x k) x))) :=
    qmul_respects (qEq_refl d) (qmul_respects n (qEq_refl _))
  have id : qEq (qsub (qsub (qmul (qpowN (qadd x d) (k + 1)) (qadd x d)) (qmul (qmul (qpowN x k) x) x))
      (qmul d (qmul (qadd (qnat (k + 1)) qone) (qmul (qpowN x k) x))))
      (qadd (qmul (qsub (qsub (qpowN (qadd x d) (k + 1)) (qmul (qpowN x k) x)) (qmul d (qmul (qnat (k + 1)) (qpowN x k)))) (qadd x d))
        (qmul (qmul d d) (qmul (qnat (k + 1)) (qpowN x k)))) := by unfold qsub; rat_ring
  generalize qmul d (qmul (qnat (k + 2)) (qmul (qpowN x k) x)) = P at *
  generalize qmul d (qmul (qadd (qnat (k + 1)) qone) (qmul (qpowN x k) x)) = Q at *
  exact qEq_trans (qle_antisymm (by unfold qsub at *; rat_linarith) (by unfold qsub at *; rat_linarith)) id

/-- THE POWER'S STEP, exactly: `(x + d)^(k+1) − x^(k+1) − d·(k + 1)x^k` within `d²·H_{k+1}`. -/
theorem pow_err {x d A R : QExpr} (hx : ZTrig.Ab x A) (hd : ZTrig.Ab d R) (hA : qle qzero A) (hR : qle qzero R) :
    ∀ k, ZTrig.Ab (qsub (qsub (qpowN (qadd x d) (k + 1)) (qpowN x (k + 1))) (qmul d (qmul (qnat (k + 1)) (qpowN x k))))
      (qmul (qmul d d) (Hpow A R (k + 1)))
  | 0 => by
      have n1 := qnat_succ 0; have n0 := qnat_zero
      have e1 : qEq (qsub (qsub (qpowN (qadd x d) 1) (qpowN x 1)) (qmul d (qmul (qnat 1) (qpowN x 0)))) qzero := by
        show qEq (qsub (qsub (qmul qone (qadd x d)) (qmul qone x)) (qmul d (qmul (qnat 1) qone))) qzero
        have r := qmul_respects (qEq_refl d) (qmul_respects (qEq_trans n1 (qadd_respects n0 (qEq_refl qone))) (qEq_refl qone))
        have o : qEq (qmul d (qmul (qadd qzero qone) qone)) d := by rat_ring
        generalize qmul d (qmul (qnat 1) qone) = P at *; generalize qmul d (qmul (qadd qzero qone) qone) = Q at *
        unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
      have h0 : qEq (qmul (qmul d d) (Hpow A R 1)) qzero := by show qEq (qmul (qmul d d) qzero) qzero; rat_ring
      generalize qsub (qsub (qpowN (qadd x d) 1) (qpowN x 1)) (qmul d (qmul (qnat 1) (qpowN x 0))) = E at *
      generalize qmul (qmul d d) (Hpow A R 1) = W at *
      exact ⟨by rat_linarith, by rat_linarith⟩
  | k + 1 => by
      have ih := pow_err hx hd hA hR k
      have hxd : ZTrig.Ab (qadd x d) (qadd A R) := by
        obtain ⟨a, b⟩ := hx; obtain ⟨c, e⟩ := hd; exact ⟨by rat_linarith, by rat_linarith⟩
      obtain ⟨a1, a2⟩ := ZTrig.mul_abs ih hxd
      have dd : ZTrig.Ab (qmul d d) (qmul d d) := ⟨by have := qmul_self_nonneg d; rat_linarith, qle_refl _⟩
      obtain ⟨b1, b2⟩ := ZTrig.mul_abs dd (ZTrig.mul_abs (show ZTrig.Ab (qnat (k + 1)) (qnat (k + 1)) from ⟨by have := qnat_nonneg (k + 1); rat_linarith, qle_refl _⟩) (pow_abs hx k))
      have rc := pow_rec x d k
      have hk : qEq (qmul (qmul d d) (Hpow A R (k + 2)))
          (qadd (qmul (qmul (qmul d d) (Hpow A R (k + 1))) (qadd A R)) (qmul (qmul d d) (qmul (qnat (k + 1)) (qpowN A k)))) := by
        show qEq (qmul (qmul d d) (qadd (qmul (Hpow A R (k + 1)) (qadd A R)) (qmul (qnat (k + 1)) (qpowN A k)))) _; rat_ring
      generalize qsub (qsub (qpowN (qadd x d) (k + 2)) (qpowN x (k + 2))) (qmul d (qmul (qnat (k + 2)) (qpowN x (k + 1)))) = E at *
      generalize qmul (qsub (qsub (qpowN (qadd x d) (k + 1)) (qpowN x (k + 1))) (qmul d (qmul (qnat (k + 1)) (qpowN x k)))) (qadd x d) = T1 at *
      generalize qmul (qmul d d) (qmul (qnat (k + 1)) (qpowN x k)) = T2 at *
      generalize qmul (qmul (qmul d d) (Hpow A R (k + 1))) (qadd A R) = U1 at *
      generalize qmul (qmul d d) (qmul (qnat (k + 1)) (qpowN A k)) = U2 at *
      generalize qmul (qmul d d) (Hpow A R (k + 2)) = W at *
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- `x^(k+1)` has a uniform step, derivative `(k + 1)·x^k` (exact). -/
theorem ustep_pow (k : Nat) : UStep (fun x _ => qpowN x (k + 1)) (fun x _ => qmul (qnat (k + 1)) (qpowN x k)) := by
  intro A R hA hR
  refine ⟨Hpow A R (k + 1), Hpow_nonneg hA hR (k + 1), fun j => ⟨0, fun n _ x d hx hd => ?_⟩⟩
  obtain ⟨a, b⟩ := pow_err hx hd hA hR k
  have e := qeps_nonneg j
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem powN_respects {x y : QExpr} (h : qEq x y) : ∀ k, qEq (qpowN x k) (qpowN y k)
  | 0 => qEq_refl _
  | k + 1 => qmul_respects (powN_respects h k) h

/-- ONE GRID STEP OF `tan` (index `m + 2`), `cos ≥ c > 0` at both points: within `(1/c)³·(T1 + T2 + T3 + T4)`. -/
theorem tan_stepR {x δ A a c R : QExpr} (hx : ZTrig.Ab x A) (h1 : ZTrig.Ab δ R) (hδ : ZTrig.Ab δ a) (hc : qlt qzero c) (m : Nat)
    (cx : qle c (ZTrig.Cn x (m + 2))) (cx' : qle c (ZTrig.Cn (qadd x δ) (m + 2))) :
    ZTrig.Ab (qsub (qsub (qmul (ZTrig.Sn (qadd x δ) (m + 2)) (qinv' (ZTrig.Cn (qadd x δ) (m + 2))))
        (qmul (ZTrig.Sn x (m + 2)) (qinv' (ZTrig.Cn x (m + 2)))))
        (qmul δ (qadd qone (qmul (qmul (ZTrig.Sn x (m + 2)) (qinv' (ZTrig.Cn x (m + 2)))) (qmul (ZTrig.Sn x (m + 2)) (qinv' (ZTrig.Cn x (m + 2))))))))
      (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c))
        (qadd (qadd (qmul (S A (m + 2)) (qmul (qmul a a) (S a m))) (qmul a (qmul a (S (qadd A R) (m + 2)))))
          (qadd (qmul (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) (S A (m + 2)))
            (qmul (qmul R (qadd (ZTrig.corner (tm A) (tm A) (m + 2)) (ZTrig.corner (tm A) (tm A) (m + 2)))) (S (qadd A R) (m + 2)))))) := by
  have o := qle_of_qlt qone_pos
  obtain ⟨x1, x2⟩ := hx
  obtain ⟨d1, d2⟩ := h1
  have hx1 : ZTrig.Ab (qadd x δ) (qadd A R) := ⟨by rat_linarith, by rat_linarith⟩
  have hxA1 : ZTrig.Ab x (qadd A R) := ⟨by rat_linarith, by rat_linarith⟩
  have hnx : ZTrig.Ab (qneg x) A := ⟨by rat_linarith, by rat_linarith⟩
  have hd : ZTrig.Ab (qsub (qadd x δ) x) a := by
    obtain ⟨e1, e2⟩ := hδ; unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩
  -- the pieces
  obtain ⟨_, eA⟩ := ZTrig.add_bounds hx1 hnx (m + 2)
  obtain ⟨eB1, eB2⟩ := ZTrig.pyth ⟨x1, x2⟩ (m + 1)
  have nS := ZTrig.near_S hδ m
  have lip := (ZTrig.CS_lip hx1 hxA1 hd (m + 2)).1
  have cA := (ZTrig.CS_abs ⟨x1, x2⟩ (m + 2)).1
  have cA1 := (ZTrig.CS_abs hx1 (m + 2)).1
  have r1 := ZTrig.Sn_respects (show qEq (qadd (qadd x δ) (qneg x)) δ by rat_ring) (m + 2)
  have r2 := ZTrig.Sn_neg x (m + 2)
  have r3 := ZTrig.Cn_neg x (m + 2)
  -- the reciprocals
  have cp : qlt qzero (ZTrig.Cn x (m + 2)) := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hc) cx,
    fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans cx h)⟩
  have cp' : qlt qzero (ZTrig.Cn (qadd x δ) (m + 2)) := qlt_iff_le_not_le.mpr ⟨qle_trans (qle_of_qlt hc) cx',
    fun h => (qlt_iff_le_not_le.mp hc).2 (qle_trans cx' h)⟩
  have hu := qmul_inv'_cancel (ne_zero_of_lt cp)
  have hv := qmul_inv'_cancel (ne_zero_of_lt cp')
  obtain ⟨i0, i1⟩ := ZTrig.inv_bound hc cx
  obtain ⟨j0, j1⟩ := ZTrig.inv_bound hc cx'
  have id := ZTrig.tan_id (S := ZTrig.Sn x (m + 2)) (S' := ZTrig.Sn (qadd x δ) (m + 2)) (δ := δ) hu hv
  -- |B|
  generalize ZTrig.Sn x (m + 2) = Sv at *; generalize ZTrig.Cn x (m + 2) = C at *
  generalize ZTrig.Sn (qadd x δ) (m + 2) = S' at *; generalize ZTrig.Cn (qadd x δ) (m + 2) = C' at *
  generalize ZTrig.Sn δ (m + 2) = Sd at *
  generalize ZTrig.Sn (qadd (qadd x δ) (qneg x)) (m + 2) = Sx at *
  generalize ZTrig.Sn (qneg x) (m + 2) = Snx at *; generalize ZTrig.Cn (qneg x) (m + 2) = Cnx at *
  have E1 : ZTrig.Ab (qsub (qsub (qmul S' C) (qmul Sv C')) Sd)
      (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) := by
    obtain ⟨g1, g2⟩ := eA
    have q1 : qEq (qmul C' Snx) (qneg (qmul C' Sv)) := by
      have := qmul_respects (qEq_refl C') r2; exact qEq_trans this (by rat_ring)
    have q2 : qEq (qmul S' Cnx) (qmul S' C) := qmul_respects (qEq_refl S') r3
    have q3 : qEq (qmul Sv C') (qmul C' Sv) := qmul_comm _ _
    generalize qmul C' Snx = P1 at *; generalize qmul S' Cnx = P2 at *
    generalize qmul S' C = P3 at *; generalize qmul Sv C' = P4 at *; generalize qmul C' Sv = P5 at *
    generalize ZTrig.corner (tm (qadd A R)) (tm A) (m + 2) = K at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have Bid : qEq (qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C'))
      (qadd (qsub (qmul C (qsub Sd δ)) (qmul δ (qsub C' C)))
        (qadd (qmul (qsub (qsub (qmul S' C) (qmul Sv C')) Sd) C) (qmul (qmul δ (qsub qone (qadd (qmul C C) (qmul Sv Sv)))) C'))) := by
    unfold qsub; rat_ring
  obtain ⟨t1, t2⟩ := ZTrig.mul_abs cA nS
  obtain ⟨t3, t4⟩ := ZTrig.mul_abs hδ lip
  obtain ⟨t5, t6⟩ := ZTrig.mul_abs E1 cA
  obtain ⟨t7, t8⟩ := ZTrig.mul_abs (ZTrig.mul_abs ⟨d1, d2⟩ ⟨eB1, eB2⟩) cA1
  have hB : ZTrig.Ab (qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C'))
      (qadd (qadd (qmul (S A (m + 2)) (qmul (qmul a a) (S a m))) (qmul a (qmul a (S (qadd A R) (m + 2)))))
          (qadd (qmul (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) (S A (m + 2)))
            (qmul (qmul R (qadd (ZTrig.corner (tm A) (tm A) (m + 2)) (ZTrig.corner (tm A) (tm A) (m + 2)))) (S (qadd A R) (m + 2))))) := by
    generalize qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C') = B at *
    generalize qmul C (qsub Sd δ) = U1 at *; generalize qmul δ (qsub C' C) = U2 at *
    generalize qmul (qsub (qsub (qmul S' C) (qmul Sv C')) Sd) C = U3 at *
    generalize qmul (qmul δ (qsub qone (qadd (qmul C C) (qmul Sv Sv)))) C' = U4 at *
    generalize qmul (S A (m + 2)) (qmul (qmul a a) (S a m)) = V1 at *
    generalize qmul a (qmul a (S (qadd A R) (m + 2))) = V2 at *
    generalize qmul (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) (S A (m + 2)) = V3 at *
    generalize qmul (qmul R (qadd (ZTrig.corner (tm A) (tm A) (m + 2)) (ZTrig.corner (tm A) (tm A) (m + 2)))) (S (qadd A R) (m + 2)) = V4 at *
    unfold qsub at Bid; exact ⟨by rat_linarith, by rat_linarith⟩
  have hI : ZTrig.Ab (qmul (qmul (qinv' C) (qinv' C)) (qinv' C')) (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) :=
    ZTrig.mul_abs (ZTrig.mul_abs ⟨by rat_linarith, i1⟩ ⟨by rat_linarith, i1⟩) ⟨by rat_linarith, j1⟩
  obtain ⟨f1, f2⟩ := ZTrig.mul_abs hI hB
  generalize qmul (qmul (qmul (qinv' C) (qinv' C)) (qinv' C'))
    (qsub (qmul (qsub (qmul S' C) (qmul Sv C')) C) (qmul (qmul δ (qadd (qmul C C) (qmul Sv Sv))) C')) = Z at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- `tan` has a uniform step where `cos ≥ c > 0` at both points (at the index), derivative `1 + tan²`. -/
theorem ustep_tan {c : QExpr} (hc : qlt qzero c) :
    UStepOn (fun x n => qle c (ZTrig.Cn x n)) (fun x n => qmul (ZTrig.Sn x n) (qinv' (ZTrig.Cn x n)))
      (fun x n => qadd qone (qmul (qmul (ZTrig.Sn x n) (qinv' (ZTrig.Cn x n))) (qmul (ZTrig.Sn x n) (qinv' (ZTrig.Cn x n))))) := by
  intro A R hA hR
  have o := qle_of_qlt qone_pos
  have hAR : qle qzero (qadd A R) := by rat_linarith
  obtain ⟨HA, hHA⟩ := S_bounded hA
  obtain ⟨HAR, hHAR⟩ := S_bounded hAR
  obtain ⟨HR, hHR⟩ := S_bounded hR
  have HA0 : qle qzero HA := qle_trans (S_nonneg hA 0) (hHA 0)
  have HAR0 : qle qzero HAR := qle_trans (S_nonneg hAR 0) (hHAR 0)
  have HR0 : qle qzero HR := qle_trans (S_nonneg hR 0) (hHR 0)
  have ic0 := qinv'_nonneg_of_pos hc
  have I0 : qle qzero (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) := qmul_nonneg (qmul_nonneg ic0 ic0) ic0
  have Hn := qmul_nonneg I0 (show qle qzero (qadd (qmul HA HR) HAR) by have := qmul_nonneg HA0 HR0; rat_linarith)
  refine ⟨qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qmul HA HR) HAR), Hn, fun k => ?_⟩
  have Y0 := qmul_nonneg I0 (show qle qzero (qadd (qadd HA HA) (qmul R (qadd HAR HAR))) by
    have := qmul_nonneg hR (show qle qzero (qadd HAR HAR) by rat_linarith); rat_linarith)
  obtain ⟨Bc, hBc⟩ := eps_scaled Y0
  obtain ⟨N1, h1⟩ := ZTrig.corner_small hAR hA (k + Bc)
  obtain ⟨N2, h2⟩ := ZTrig.corner_small hA hA (k + Bc)
  refine ⟨(N1 + N2) + 2, fun n hn x d hx hd cx cx' => ?_⟩
  obtain ⟨a, ha, aa, a0, aR⟩ := abs_le hd
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ n' => cases n' with
    | zero => exact absurd (Nat.le_of_succ_le_succ hn) (Nat.not_succ_le_zero _)
    | succ m =>
      have hm : N1 + N2 ≤ m + 2 := Nat.le_trans (Nat.le_add_right _ 2) hn
      obtain ⟨s1, s2⟩ := tan_stepR hx hd ha hc m cx cx'
      have K1 := h1 (m + 2) (ZTrig.le_l' hm)
      have K2 := h2 (m + 2) (ZTrig.le_r' hm)
      have K10 := ZTrig.corner_nonneg (tm_nonneg hA) (m + 2) (tm (qadd A R)) (tm_nonneg hAR)
      have K20 := ZTrig.corner_nonneg (tm_nonneg hA) (m + 2) (tm A) (tm_nonneg hA)
      -- T1 ≤ HA·(d²·HR), T2 ≤ d²·HAR
      have sa := qle_trans (ZTrig.S_mono_x a0 aR m) (hHR m)
      have u1 := qle_trans (scale_l (scale_l sa (qmul_self_nonneg a)) (S_nonneg hA (m + 2)))
        (ZExp.scale (hHA (m + 2)) (qmul_nonneg (qmul_self_nonneg a) HR0))
      have u2 := scale_l (scale_l (hHAR (m + 2)) a0) a0
      have u3 := scale_l (hHA (m + 2)) (show qle qzero (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))
        (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) by rat_linarith)
      have u4 := scale_l (hHAR (m + 2)) (qmul_nonneg hR (show qle qzero (qadd (ZTrig.corner (tm A) (tm A) (m + 2))
        (ZTrig.corner (tm A) (tm A) (m + 2))) by rat_linarith))
      have w1 := ZExp.scale (show qle (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)))
        (qadd (qeps (k + Bc)) (qeps (k + Bc))) by rat_linarith) HA0
      have w2 := ZExp.scale (scale_l (show qle (qadd (ZTrig.corner (tm A) (tm A) (m + 2)) (ZTrig.corner (tm A) (tm A) (m + 2)))
        (qadd (qeps (k + Bc)) (qeps (k + Bc))) by rat_linarith) hR) HAR0
      have ia : qEq (qmul HA (qmul (qmul a a) HR)) (qmul HA (qmul (qmul d d) HR)) :=
        qmul_respects (qEq_refl HA) (qmul_respects aa (qEq_refl HR))
      have ib : qEq (qmul a (qmul a HAR)) (qmul (qmul d d) HAR) := qEq_trans (by rat_ring) (qmul_respects aa (qEq_refl HAR))
      have pH : qEq (qadd (qadd (qmul HA (qmul (qmul d d) HR)) (qmul (qmul d d) HAR))
          (qadd (qmul (qadd (qeps (k + Bc)) (qeps (k + Bc))) HA) (qmul (qmul R (qadd (qeps (k + Bc)) (qeps (k + Bc)))) HAR)))
          (qadd (qmul (qmul d d) (qadd (qmul HA HR) HAR)) (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qmul R (qadd HAR HAR))))) := by
        rat_ring
      generalize hTs : qadd (qadd (qmul (S A (m + 2)) (qmul (qmul a a) (S a m))) (qmul a (qmul a (S (qadd A R) (m + 2)))))
          (qadd (qmul (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) (S A (m + 2)))
            (qmul (qmul R (qadd (ZTrig.corner (tm A) (tm A) (m + 2)) (ZTrig.corner (tm A) (tm A) (m + 2)))) (S (qadd A R) (m + 2)))) = Ts at s1 s2
      have hT : qle Ts (qadd (qmul (qmul d d) (qadd (qmul HA HR) HAR)) (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qmul R (qadd HAR HAR))))) := by
        rw [← hTs]
        generalize qmul (S A (m + 2)) (qmul (qmul a a) (S a m)) = T1 at *
        generalize qmul a (qmul a (S (qadd A R) (m + 2))) = T2 at *
        generalize qmul (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) (S A (m + 2)) = T3 at *
        generalize qmul (qmul R (qadd (ZTrig.corner (tm A) (tm A) (m + 2)) (ZTrig.corner (tm A) (tm A) (m + 2)))) (S (qadd A R) (m + 2)) = T4 at *
        generalize qmul (qadd (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2)) (ZTrig.corner (tm (qadd A R)) (tm A) (m + 2))) HA = P3 at *
        generalize qmul (qmul R (qadd (ZTrig.corner (tm A) (tm A) (m + 2)) (ZTrig.corner (tm A) (tm A) (m + 2)))) HAR = P4 at *
        generalize qmul HA (qmul (qmul a a) HR) = P1 at *; generalize qmul a (qmul a HAR) = P2 at *
        generalize qmul (qadd (qeps (k + Bc)) (qeps (k + Bc))) HA = Q1 at *
        generalize qmul (qmul R (qadd (qeps (k + Bc)) (qeps (k + Bc)))) HAR = Q2 at *
        generalize qmul HA (qmul (qmul d d) HR) = R1 at *; generalize qmul (qmul d d) HAR = R2 at *
        generalize qadd (qmul (qmul d d) (qadd (qmul HA HR) HAR)) (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qmul R (qadd HAR HAR)))) = Z at *
        rat_linarith
      have v := scale_l hT I0
      have be := hBc k
      have id : qEq (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c))
          (qadd (qmul (qmul d d) (qadd (qmul HA HR) HAR)) (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qmul R (qadd HAR HAR))))))
          (qadd (qmul (qmul d d) (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qmul HA HR) HAR)))
            (qmul (qeps (k + Bc)) (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qadd HA HA) (qmul R (qadd HAR HAR)))))) := by
        rat_ring
      generalize qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) Ts = W at *
      generalize qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c))
          (qadd (qmul (qmul d d) (qadd (qmul HA HR) HAR)) (qmul (qeps (k + Bc)) (qadd (qadd HA HA) (qmul R (qadd HAR HAR))))) = W' at *
      generalize qmul (qmul d d) (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qmul HA HR) HAR)) = X at *
      generalize qmul (qeps (k + Bc)) (qmul (qmul (qmul (qinv' c) (qinv' c)) (qinv' c)) (qadd (qadd HA HA) (qmul R (qadd HAR HAR)))) = Y at *
      clear h1 h2 hHA hHAR hHR hBc
      exact ⟨by rat_linarith, by rat_linarith⟩

/-- What the step needs from the box, node by node: the readings of the factors and their derivatives. -/
inductive StepRead (B : Box QExpr) (i : Nat) : G → Prop where
  | const {c : QExpr} : StepRead B i (.const c)
  | var {j : Nat} : StepRead B i (.var j)
  | add {u v : G} : StepRead B i u → StepRead B i v → StepRead B i (.add u v)
  | sub {u v : G} : StepRead B i u → StepRead B i v → StepRead B i (.sub u v)
  | mul {u v : G} {lu hu lv hv l1 h1 l2 h2 : QExpr} : StepRead B i u → StepRead B i v →
      VRead B u lu hu → VRead B v lv hv → VRead B (D i u) l1 h1 → VRead B (D i v) l2 h2 → StepRead B i (.mul u v)
  | exp {u : G} {lu hu l1 h1 lE hE : QExpr} : StepRead B i u → VRead B u lu hu → VRead B (D i u) l1 h1 →
      VRead B (.exp u) lE hE → StepRead B i (.exp u)
  | sin {u : G} {lu hu l1 h1 lC hC : QExpr} : StepRead B i u → VRead B u lu hu → VRead B (D i u) l1 h1 →
      VRead B (.cos u) lC hC → StepRead B i (.sin u)
  | cos {u : G} {lu hu l1 h1 lS hS : QExpr} : StepRead B i u → VRead B u lu hu → VRead B (D i u) l1 h1 →
      VRead B (.sin u) lS hS → StepRead B i (.cos u)
  | div {u v : G} {lu hu lv hv l1 h1 l2 h2 r1 r2 : QExpr} : StepRead B i u → StepRead B i v → VRead B u lu hu →
      VRead B v lv hv → RecipOK r1 r2 lv hv → VRead B (D i u) l1 h1 → VRead B (D i v) l2 h2 → StepRead B i (.div u v)
  | powZ {u : G} : StepRead B i (.powN u 0)
  | powN {u : G} {k : Nat} {lu hu l1 h1 : QExpr} : StepRead B i u → VRead B u lu hu → VRead B (D i u) l1 h1 →
      StepRead B i (.powN u (k + 1))
  | tan {u : G} {lu hu l1 h1 Tl Th : QExpr} : StepRead B i u → VRead B u lu hu → VRead B (D i u) l1 h1 →
      ZTrig.TanVal lu hu Tl Th → StepRead B i (.tan u)
/-- THE SYMBOLIC DERIVATIVE IS THE DERIVATIVE (the fragment `const var + − ×`): one constant `H` for the box. -/
theorem step_sound {B : Box QExpr} {i : Nat} : ∀ {e : G}, StepRead B i e → ∃ H, qle qzero H ∧
    ∀ p q, InBox qOrd B p → InBox qOrd B q → (∀ j, j ≠ i → q j = p j) → ZTrig.Ab (qsub (q i) (p i)) qone →
      StepAt i e H p q := by
  intro e r
  induction r with
  | @const c =>
    refine ⟨qzero, qle_refl _, fun p q _ _ _ _ k => ⟨0, fun n _ => ab_zero ?_ ?_⟩⟩
    · show qEq (qsub (qsub c c) (qmul (qsub (q i) (p i)) qzero)) qzero
      unfold qsub; rat_ring
    · have := qeps_nonneg k
      have e : qEq (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) qzero) qzero := by rat_ring
      generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) qzero = P at *; rat_linarith
  | @var j =>
    refine ⟨qzero, qle_refl _, fun p q _ _ hfix _ k => ⟨0, fun n _ => ab_zero ?_ ?_⟩⟩
    · show qEq (qsub (qsub (q j) (p j)) (qmul (qsub (q i) (p i)) (dvar i j))) qzero
      cases Nat.decEq j i with
      | isTrue h => subst h; rw [dvar_eq]; unfold qsub; rat_ring
      | isFalse h => rw [dvar_ne h, hfix j h]; unfold qsub; rat_ring
    · have := qeps_nonneg k
      have e : qEq (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) qzero) qzero := by rat_ring
      generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) qzero = P at *; rat_linarith
  | @add u v _ _ ihu ihv =>
    obtain ⟨Hu, hu0, hu⟩ := ihu
    obtain ⟨Hv, hv0, hv⟩ := ihv
    refine ⟨qadd Hu Hv, by rat_linarith, fun p q hp hq hfix hδ k => ?_⟩
    obtain ⟨N1, h1⟩ := hu p q hp hq hfix hδ (k + 1)
    obtain ⟨N2, h2⟩ := hv p q hp hq hfix hδ (k + 1)
    refine ⟨N1 + N2, fun n hn => ?_⟩
    obtain ⟨a1, a2⟩ := h1 n (ZTrig.le_l' hn)
    obtain ⟨b1, b2⟩ := h2 n (ZTrig.le_r' hn)
    have ek := qeps_succ_add k
    have id : qEq (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) (qadd Hu Hv))
        (qadd (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hu) (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hv)) := by
      rat_ring
    show ZTrig.Ab (qsub (qsub (qadd (evalN n q u) (evalN n q v)) (qadd (evalN n p u) (evalN n p v)))
      (qmul (qsub (q i) (p i)) (qadd (evalN n p (D i u)) (evalN n p (D i v))))) _
    have e2 : qEq (qsub (qsub (qadd (evalN n q u) (evalN n q v)) (qadd (evalN n p u) (evalN n p v)))
        (qmul (qsub (q i) (p i)) (qadd (evalN n p (D i u)) (evalN n p (D i v)))))
        (qadd (qsub (qsub (evalN n q u) (evalN n p u)) (qmul (qsub (q i) (p i)) (evalN n p (D i u))))
          (qsub (qsub (evalN n q v) (evalN n p v)) (qmul (qsub (q i) (p i)) (evalN n p (D i v))))) := by unfold qsub; rat_ring
    generalize qsub (qsub (qadd (evalN n q u) (evalN n q v)) (qadd (evalN n p u) (evalN n p v)))
      (qmul (qsub (q i) (p i)) (qadd (evalN n p (D i u)) (evalN n p (D i v)))) = E at *
    generalize qsub (qsub (evalN n q u) (evalN n p u)) (qmul (qsub (q i) (p i)) (evalN n p (D i u))) = Eu at *
    generalize qsub (qsub (evalN n q v) (evalN n p v)) (qmul (qsub (q i) (p i)) (evalN n p (D i v))) = Ev at *
    generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) (qadd Hu Hv) = X at *
    generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hu = Xu at *
    generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hv = Xv at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  | @sub u v _ _ ihu ihv =>
    obtain ⟨Hu, hu0, hu⟩ := ihu
    obtain ⟨Hv, hv0, hv⟩ := ihv
    refine ⟨qadd Hu Hv, by rat_linarith, fun p q hp hq hfix hδ k => ?_⟩
    obtain ⟨N1, h1⟩ := hu p q hp hq hfix hδ (k + 1)
    obtain ⟨N2, h2⟩ := hv p q hp hq hfix hδ (k + 1)
    refine ⟨N1 + N2, fun n hn => ?_⟩
    obtain ⟨a1, a2⟩ := h1 n (ZTrig.le_l' hn)
    obtain ⟨b1, b2⟩ := h2 n (ZTrig.le_r' hn)
    have ek := qeps_succ_add k
    have id : qEq (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) (qadd Hu Hv))
        (qadd (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hu) (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hv)) := by
      rat_ring
    show ZTrig.Ab (qsub (qsub (qsub (evalN n q u) (evalN n q v)) (qsub (evalN n p u) (evalN n p v)))
      (qmul (qsub (q i) (p i)) (qsub (evalN n p (D i u)) (evalN n p (D i v))))) _
    have e2 : qEq (qsub (qsub (qsub (evalN n q u) (evalN n q v)) (qsub (evalN n p u) (evalN n p v)))
        (qmul (qsub (q i) (p i)) (qsub (evalN n p (D i u)) (evalN n p (D i v)))))
        (qsub (qsub (qsub (evalN n q u) (evalN n p u)) (qmul (qsub (q i) (p i)) (evalN n p (D i u))))
          (qsub (qsub (evalN n q v) (evalN n p v)) (qmul (qsub (q i) (p i)) (evalN n p (D i v))))) := by unfold qsub; rat_ring
    generalize qsub (qsub (qsub (evalN n q u) (evalN n q v)) (qsub (evalN n p u) (evalN n p v)))
      (qmul (qsub (q i) (p i)) (qsub (evalN n p (D i u)) (evalN n p (D i v)))) = E at *
    generalize qsub (qsub (evalN n q u) (evalN n p u)) (qmul (qsub (q i) (p i)) (evalN n p (D i u))) = Eu at *
    generalize qsub (qsub (evalN n q v) (evalN n p v)) (qmul (qsub (q i) (p i)) (evalN n p (D i v))) = Ev at *
    generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) (qadd Hu Hv) = X at *
    generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hu = Xu at *
    generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) Hv = Xv at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  | @mul u v lu hu lv hv l1 h1 l2 h2 _ _ ru rv rdu rdv ihu ihv =>
    obtain ⟨Hu, hu0, hsu⟩ := ihu
    obtain ⟨Hv, hv0, hsv⟩ := ihv
    obtain ⟨Mu, mu0, bu⟩ := read_bound ru
    obtain ⟨Mv, mv0, bv⟩ := read_bound rv
    obtain ⟨Mdu, mdu0, bdu⟩ := read_bound rdu
    obtain ⟨Mdv, mdv0, bdv⟩ := read_bound rdv
    have H0 : qle qzero (qadd (qadd (qmul Hu Mv) (qmul Mu Hv)) (qadd (qmul Mdu Mdv) (qmul Mdu Hv))) := by
      have := qmul_nonneg hu0 mv0; have := qmul_nonneg mu0 hv0; have := qmul_nonneg mdu0 mdv0; have := qmul_nonneg mdu0 hv0
      rat_linarith
    obtain ⟨Bc, hBc⟩ := eps_scaled (C := qadd (qadd Mv Mu) Mdu) (by rat_linarith)
    refine ⟨_, H0, fun p q hp hq hfix hδ k => ?_⟩
    obtain ⟨N1, h1⟩ := hsu p q hp hq hfix hδ (k + Bc)
    obtain ⟨N2, h2⟩ := hsv p q hp hq hfix hδ (k + Bc)
    obtain ⟨N3, h3⟩ := bv q hq
    obtain ⟨N4, h4⟩ := bu p hp
    obtain ⟨N5, h5⟩ := bdu p hp
    obtain ⟨N6, h6⟩ := bdv p hp
    refine ⟨N1 + (N2 + (N3 + (N4 + (N5 + N6)))), fun n hn => ?_⟩
    have m := mul_step (h1 n (ZTrig.le_l' hn)) (h2 n (ZTrig.le_l' (ZTrig.le_r' hn)))
      (h3 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' hn)))) (h4 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn)))))
      (h5 n (ZTrig.le_l' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn))))))
      (h6 n (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' (ZTrig.le_r' hn)))))) hδ
    have be := hBc k
    obtain ⟨m1, m2⟩ := m
    show ZTrig.Ab (qsub (qsub (qmul (evalN n q u) (evalN n q v)) (qmul (evalN n p u) (evalN n p v)))
      (qmul (qsub (q i) (p i)) (qadd (qmul (evalN n p (D i u)) (evalN n p v)) (qmul (evalN n p u) (evalN n p (D i v)))))) _
    generalize qsub (qsub (qmul (evalN n q u) (evalN n q v)) (qmul (evalN n p u) (evalN n p v)))
      (qmul (qsub (q i) (p i)) (qadd (qmul (evalN n p (D i u)) (evalN n p v)) (qmul (evalN n p u) (evalN n p (D i v))))) = E at *
    generalize qmul (qeps (k + Bc)) (qadd (qadd Mv Mu) Mdu) = P at *
    generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i)))
      (qadd (qadd (qmul Hu Mv) (qmul Mu Hv)) (qadd (qmul Mdu Mdv) (qmul Mdu Hv))) = X at *
    exact ⟨by rat_linarith, by rat_linarith⟩
  | @exp u lu hu l1 h1 lE hE _ ru rdu rE ihu =>
    obtain ⟨Hu, hu0, hsu⟩ := ihu
    obtain ⟨Mu, mu0, bu⟩ := read_bound ru
    obtain ⟨Mdu, mdu0, bdu⟩ := read_bound rdu
    obtain ⟨Mψ, mψ0, bψ⟩ := read_bound rE
    obtain ⟨H, H0, hc⟩ := comp_step ustep_E (fun _ _ n e => eseq_respects e n) mu0 mdu0 mψ0 hu0
    exact ⟨H, H0, fun p q hp hq hfix hδ => hc (fun n => evalN n p u) (fun n => evalN n q u) (fun n => evalN n p (D i u))
      _ hδ (hsu p q hp hq hfix hδ) (bu p hp) (bdu p hp) (bψ p hp)⟩
  | @sin u lu hu l1 h1 lC hC _ ru rdu rC ihu =>
    obtain ⟨Hu, hu0, hsu⟩ := ihu
    obtain ⟨Mu, mu0, bu⟩ := read_bound ru
    obtain ⟨Mdu, mdu0, bdu⟩ := read_bound rdu
    obtain ⟨Mψ, mψ0, bψ⟩ := read_bound rC
    obtain ⟨H, H0, hc⟩ := comp_step ustep_S (fun _ _ n e => ZTrig.Sn_respects e n) mu0 mdu0 mψ0 hu0
    exact ⟨H, H0, fun p q hp hq hfix hδ => hc (fun n => evalN n p u) (fun n => evalN n q u) (fun n => evalN n p (D i u))
      _ hδ (hsu p q hp hq hfix hδ) (bu p hp) (bdu p hp) (bψ p hp)⟩
  | @cos u lu hu l1 h1 lS hS _ ru rdu rS ihu =>
    obtain ⟨Hu, hu0, hsu⟩ := ihu
    obtain ⟨Mu, mu0, bu⟩ := read_bound ru
    obtain ⟨Mdu, mdu0, bdu⟩ := read_bound rdu
    obtain ⟨Mψ, mψ0, bψ⟩ := read_bound rS
    obtain ⟨H, H0, hc⟩ := comp_step ustep_C0 (fun _ _ n e => ZTrig.Cn_respects e n) mu0 mdu0 mψ0 hu0
    refine ⟨H, H0, fun p q hp hq hfix hδ => hc (fun n => evalN n p u) (fun n => evalN n q u) (fun n => evalN n p (D i u))
      _ hδ (hsu p q hp hq hfix hδ) (bu p hp) (bdu p hp) ?_⟩
    obtain ⟨N, hN⟩ := bψ p hp
    exact ⟨N, fun n hn => by
      obtain ⟨a, b⟩ := hN n hn
      show ZTrig.Ab (qsub qzero (ZTrig.Sn (evalN n p u) n)) Mψ
      have : ZTrig.Ab (ZTrig.Sn (evalN n p u) n) Mψ := ⟨a, b⟩
      obtain ⟨c, d⟩ := this; unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩⟩
  | @div u v lu hu lv hv l1 h1 l2 h2 r1 r2 _ _ ru rv rc rdu rdv ihu ihv =>
    obtain ⟨Hu, hu0, hsu⟩ := ihu
    obtain ⟨Hv, hv0, hsv⟩ := ihv
    obtain ⟨Mu, mu0, bu⟩ := read_bound ru
    obtain ⟨Mv, mv0, bv⟩ := read_bound rv
    obtain ⟨Mdu, mdu0, bdu⟩ := read_bound rdu
    obtain ⟨Mdv, mdv0, bdv⟩ := read_bound rdv
    obtain ⟨_, ⟨lvp, _, _⟩ | ⟨hvn, _, _⟩⟩ := rc
    · obtain ⟨Bp, hBp⟩ := ZTrig.pos_floor lvp
      have ic0 := qinv'_nonneg_of_pos (qeps_pos (Bp + 1))
      have mψ0 : qle qzero (qmul (qinv' (qeps (Bp + 1))) (qinv' (qeps (Bp + 1)))) := qmul_nonneg ic0 ic0
      obtain ⟨HW, hw0, hW⟩ := comp_step_on (φ := fun x _ => qinv' x) (ψ := fun x _ => qneg (qmul (qinv' x) (qinv' x)))
        (dom := fun x (_ : Nat) => qle (qeps (Bp + 1)) x) (ustep_inv (qeps_pos (Bp + 1)))
        (fun _ _ _ e => qinv'_respects e) (fun _ _ _ e h => qle_trans h (qle_of_qEq e)) mv0 mdv0 mψ0 hv0
      have ib : ∀ y, qle (qeps (Bp + 1)) y → ZTrig.Ab (qinv' y) (qinv' (qeps (Bp + 1))) := fun y hy => by
        obtain ⟨i0, i1⟩ := ZTrig.inv_bound (qeps_pos (Bp + 1)) hy; exact ⟨by rat_linarith, i1⟩
      have nzl : ∀ y, qle (qeps (Bp + 1)) y → ¬ qEq y qzero := fun y hy h =>
        (qlt_iff_le_not_le.mp (qeps_pos (Bp + 1))).2 (by rat_linarith)
      have evd : ∀ X, InBox qOrd B X → ∃ N, ∀ n, N ≤ n → (fun x (_ : Nat) => qle (qeps (Bp + 1)) x) (evalN n X v) n := fun X hX => by
        obtain ⟨N, hN⟩ := value_sound hX rv (Bp + 1)
        exact ⟨N, fun n hn => by obtain ⟨a, _⟩ := hN n hn; have e := qeps_succ_add Bp; unfold qsub at a; rat_linarith⟩
      have mdw0 := qmul_nonneg mψ0 mdv0
      refine ⟨_, qadd_nn (qadd_nn (qmul_nonneg hu0 ic0) (qmul_nonneg mu0 hw0)) (qadd_nn (qmul_nonneg mdu0 mdw0) (qmul_nonneg mdu0 hw0)),
        fun p q hp hq hfix hδ => ?_⟩
      obtain ⟨Nu, hNu⟩ := evd p hp
      obtain ⟨Nv, hNv⟩ := evd q hq
      obtain ⟨Nd, hNd⟩ := bdv p hp
      have ψb : ∀ n, Nu ≤ n → ZTrig.Ab (qneg (qmul (qinv' (evalN n p v)) (qinv' (evalN n p v)))) (qmul (qinv' (qeps (Bp + 1))) (qinv' (qeps (Bp + 1)))) := fun n hn => by
        have ab := ib _ (hNu n hn)
        obtain ⟨c1, c2⟩ := ZTrig.mul_abs ab ab
        exact ⟨by rat_linarith, by rat_linarith⟩
      have sw := hW (fun n => evalN n p v) (fun n => evalN n q v) (fun n => evalN n p (D i v)) _ hδ (hsv p q hp hq hfix hδ)
        (bv p hp) (bdv p hp) ⟨Nu, ψb⟩ ⟨Nu, hNu⟩ ⟨Nv, hNv⟩
      exact div_step hu0 hw0 mu0 mdu0 ic0 mdw0 hδ (hsu p q hp hq hfix hδ) sw
        ⟨Nv, fun n hn => ib _ (hNv n hn)⟩ (bu p hp) (bdu p hp)
        ⟨Nu + Nd, fun n hn => ZTrig.mul_abs (ψb n (ZTrig.le_l' hn)) (hNd n (ZTrig.le_r' hn))⟩
        ⟨Nu, fun n hn => nzl _ (hNu n hn)⟩
    · obtain ⟨Bp, hBp⟩ := ZTrig.pos_floor (show qlt qzero (qneg hv) from qlt_iff_le_not_le.mpr ⟨by have := (qlt_iff_le_not_le.mp hvn).1; rat_linarith, fun h => (qlt_iff_le_not_le.mp hvn).2 (by rat_linarith)⟩)
      have ic0 := qinv'_nonneg_of_pos (qeps_pos (Bp + 1))
      have mψ0 : qle qzero (qmul (qinv' (qeps (Bp + 1))) (qinv' (qeps (Bp + 1)))) := qmul_nonneg ic0 ic0
      obtain ⟨HW, hw0, hW⟩ := comp_step_on (φ := fun x _ => qinv' x) (ψ := fun x _ => qneg (qmul (qinv' x) (qinv' x)))
        (dom := fun x (_ : Nat) => qle x (qneg (qeps (Bp + 1)))) (ustep_inv_neg (qeps_pos (Bp + 1)))
        (fun _ _ _ e => qinv'_respects e) (fun _ _ _ e h => qle_trans (qle_of_qEq (qEq_symm e)) h) mv0 mdv0 mψ0 hv0
      have ib : ∀ y, qle y (qneg (qeps (Bp + 1))) → ZTrig.Ab (qinv' y) (qinv' (qeps (Bp + 1))) := fun y hy =>
        inv_bound_neg (qeps_pos (Bp + 1)) hy
      have nzl : ∀ y, qle y (qneg (qeps (Bp + 1))) → ¬ qEq y qzero := fun y hy h =>
        (qlt_iff_le_not_le.mp (qeps_pos (Bp + 1))).2 (by rat_linarith)
      have evd : ∀ X, InBox qOrd B X → ∃ N, ∀ n, N ≤ n → (fun x (_ : Nat) => qle x (qneg (qeps (Bp + 1)))) (evalN n X v) n := fun X hX => by
        obtain ⟨N, hN⟩ := value_sound hX rv (Bp + 1)
        exact ⟨N, fun n hn => by obtain ⟨_, a⟩ := hN n hn; have e := qeps_succ_add Bp; rat_linarith⟩
      have mdw0 := qmul_nonneg mψ0 mdv0
      refine ⟨_, qadd_nn (qadd_nn (qmul_nonneg hu0 ic0) (qmul_nonneg mu0 hw0)) (qadd_nn (qmul_nonneg mdu0 mdw0) (qmul_nonneg mdu0 hw0)),
        fun p q hp hq hfix hδ => ?_⟩
      obtain ⟨Nu, hNu⟩ := evd p hp
      obtain ⟨Nv, hNv⟩ := evd q hq
      obtain ⟨Nd, hNd⟩ := bdv p hp
      have ψb : ∀ n, Nu ≤ n → ZTrig.Ab (qneg (qmul (qinv' (evalN n p v)) (qinv' (evalN n p v)))) (qmul (qinv' (qeps (Bp + 1))) (qinv' (qeps (Bp + 1)))) := fun n hn => by
        have ab := ib _ (hNu n hn)
        obtain ⟨c1, c2⟩ := ZTrig.mul_abs ab ab
        exact ⟨by rat_linarith, by rat_linarith⟩
      have sw := hW (fun n => evalN n p v) (fun n => evalN n q v) (fun n => evalN n p (D i v)) _ hδ (hsv p q hp hq hfix hδ)
        (bv p hp) (bdv p hp) ⟨Nu, ψb⟩ ⟨Nu, hNu⟩ ⟨Nv, hNv⟩
      exact div_step hu0 hw0 mu0 mdu0 ic0 mdw0 hδ (hsu p q hp hq hfix hδ) sw
        ⟨Nv, fun n hn => ib _ (hNv n hn)⟩ (bu p hp) (bdu p hp)
        ⟨Nu + Nd, fun n hn => ZTrig.mul_abs (ψb n (ZTrig.le_l' hn)) (hNd n (ZTrig.le_r' hn))⟩
        ⟨Nu, fun n hn => nzl _ (hNu n hn)⟩
  | @powZ u =>
    refine ⟨qzero, qle_refl _, fun p q _ _ _ _ k => ⟨0, fun n _ => ab_zero ?_ ?_⟩⟩
    · show qEq (qsub (qsub qone qone) (qmul (qsub (q i) (p i)) qzero)) qzero
      unfold qsub; rat_ring
    · have := qeps_nonneg k
      have e : qEq (qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) qzero) qzero := by rat_ring
      generalize qmul (qmul (qsub (q i) (p i)) (qsub (q i) (p i))) qzero = P at *; rat_linarith
  | @powN u k lu hu l1 h1 _ ru rdu ihu =>
    obtain ⟨Hu, hu0, hsu⟩ := ihu
    obtain ⟨Mu, mu0, bu⟩ := read_bound ru
    obtain ⟨Mdu, mdu0, bdu⟩ := read_bound rdu
    have mψ0 := qmul_nonneg (qnat_nonneg (k + 1)) (powN_nonneg mu0 k)
    obtain ⟨H, H0, hc⟩ := comp_step (ustep_pow k) (fun _ _ _ e => powN_respects e (k + 1)) mu0 mdu0 mψ0 hu0
    refine ⟨H, H0, fun p q hp hq hfix hδ => hc (fun n => evalN n p u) (fun n => evalN n q u) (fun n => evalN n p (D i u))
      _ hδ (hsu p q hp hq hfix hδ) (bu p hp) (bdu p hp) ?_⟩
    obtain ⟨N, hN⟩ := bu p hp
    exact ⟨N, fun n hn => ZTrig.mul_abs (show ZTrig.Ab (qnat (k + 1)) (qnat (k + 1)) from
      ⟨by have := qnat_nonneg (k + 1); rat_linarith, qle_refl _⟩) (pow_abs (hN n hn) k)⟩
  | @tan u lu hu l1 h1 Tl Th _ ru rdu tv ihu =>
    obtain ⟨Hu, hu0, hsu⟩ := ihu
    obtain ⟨Mu, mu0, bu⟩ := read_bound ru
    obtain ⟨Mdu, mdu0, bdu⟩ := read_bound rdu
    obtain ⟨MT, mt0, bT⟩ := read_bound (VRead.tan ru tv)
    obtain ⟨c0, c1, c0p, hC⟩ := ZTrig.TanVal.cos_all tv
    obtain ⟨Bp, hBp⟩ := ZTrig.pos_floor c0p
    have o := qle_of_qlt qone_pos
    have mψ0 : qle qzero (qadd qone (qmul MT MT)) := by have := qmul_nonneg mt0 mt0; rat_linarith
    obtain ⟨H, H0, hc⟩ := comp_step_on (φ := fun x n => qmul (ZTrig.Sn x n) (qinv' (ZTrig.Cn x n)))
      (ψ := fun x n => qadd qone (qmul (qmul (ZTrig.Sn x n) (qinv' (ZTrig.Cn x n))) (qmul (ZTrig.Sn x n) (qinv' (ZTrig.Cn x n)))))
      (dom := fun x n => qle (qeps (Bp + 1)) (ZTrig.Cn x n)) (ustep_tan (qeps_pos (Bp + 1)))
      (fun _ _ n e => qmul_respects (ZTrig.Sn_respects e n) (qinv'_respects (ZTrig.Cn_respects e n)))
      (fun _ _ n e h => qle_trans h (qle_of_qEq (ZTrig.Cn_respects e n))) mu0 mdu0 mψ0 hu0
    have evd : ∀ X, InBox qOrd B X → ∃ N, ∀ n, N ≤ n → qle (qeps (Bp + 1)) (ZTrig.Cn (evalN n X u) n) := fun X hX => by
      obtain ⟨N, hN⟩ := hC _ (value_sound hX ru) (Bp + 1)
      exact ⟨N, fun n hn => by obtain ⟨a, _⟩ := hN n hn; have e := qeps_succ_add Bp; unfold qsub at a; rat_linarith⟩
    refine ⟨H, H0, fun p q hp hq hfix hδ => hc (fun n => evalN n p u) (fun n => evalN n q u) (fun n => evalN n p (D i u))
      _ hδ (hsu p q hp hq hfix hδ) (bu p hp) (bdu p hp) ?_ (evd p hp) (evd q hq)⟩
    obtain ⟨N, hN⟩ := bT p hp
    exact ⟨N, fun n hn => by
      have b : ZTrig.Ab (qmul (ZTrig.Sn (evalN n p u) n) (qinv' (ZTrig.Cn (evalN n p u) n))) MT := hN n hn
      obtain ⟨c1, c2⟩ := ZTrig.mul_abs b b
      show ZTrig.Ab (qadd qone (qmul (qmul (ZTrig.Sn (evalN n p u) n) (qinv' (ZTrig.Cn (evalN n p u) n)))
        (qmul (ZTrig.Sn (evalN n p u) n) (qinv' (ZTrig.Cn (evalN n p u) n))))) _
      have q0 := qmul_self_nonneg (qmul (ZTrig.Sn (evalN n p u) n) (qinv' (ZTrig.Cn (evalN n p u) n)))
      exact ⟨by rat_linarith, by rat_linarith⟩⟩

end ZDeriv

#print axioms ZDeriv.read_bound
#print axioms ZDeriv.eps_scaled
#print axioms ZDeriv.mul_step
#print axioms ZDeriv.step_sound
#print axioms ZDeriv.ustep_S
#print axioms ZDeriv.ustep_C
#print axioms ZDeriv.ustep_E
#print axioms ZDeriv.comp_alg
#print axioms ZDeriv.comp_step
#print axioms ZDeriv.comp_step_on
#print axioms ZDeriv.inv_id
#print axioms ZDeriv.ustep_inv
#print axioms ZDeriv.ustep_inv_neg
#print axioms ZDeriv.quot_form
#print axioms ZDeriv.div_step
#print axioms ZDeriv.pow_err
#print axioms ZDeriv.ustep_pow
#print axioms ZDeriv.tan_stepR
#print axioms ZDeriv.ustep_tan
