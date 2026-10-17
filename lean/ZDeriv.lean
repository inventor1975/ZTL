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

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt

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
