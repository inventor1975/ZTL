import ZTrig5

/-!
# ZTrig6 — the addition formulas in the limit; the shifts by `ρ`. Zero axioms.

Stage 6 of the full sine. For sequences of arguments (the approximants of operational reals), `cos` and `sin` are
`cs x n = C_n(x_n)`, `sn x n = S_n(x_n)`; two sequences are EQUAL IN THE LIMIT (`Eq0`) when their difference is
eventually within every `ε_k` of `0`.

  * `corner_small` — the corner of `exp`'s series at any `a, b ≥ 0` vanishes;
  * `add_cos`, `add_sin` — `cos(x+y) = cos x cos y − sin x sin y`, `sin(x+y) = sin x cos y + cos x sin y`, in the limit;
  * `shift_sin`, `shift_cos` — `sin(x + ρ) = cos x`, `cos(x + ρ) = −sin x`.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

/-- Equal in the limit. -/
def Eq0 (u v : Nat → QExpr) : Prop := Ev (fun n => qsub (u n) (v n)) qzero qzero

def cs (x : Nat → QExpr) (n : Nat) : QExpr := Cn (x n) n
def sn (x : Nat → QExpr) (n : Nat) : QExpr := Sn (x n) n

/-- Eventually `|x_n| ≤ a`. -/
def Bnd (x : Nat → QExpr) (a : QExpr) : Prop := ∃ N, ∀ n, N ≤ n → Ab (x n) a

theorem Eq0_of {u v : Nat → QExpr} (h : ∀ k, ∃ N, ∀ n, N ≤ n → Ab (qsub (u n) (v n)) (qeps k)) : Eq0 u v := fun k => by
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n hn
  show qle (qsub qzero (qeps k)) (qsub (u n) (v n)) ∧ qle (qsub (u n) (v n)) (qadd qzero (qeps k))
  generalize qsub (u n) (v n) = d at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem Eq0_get {u v : Nat → QExpr} (h : Eq0 u v) (k : Nat) : ∃ N, ∀ n, N ≤ n → Ab (qsub (u n) (v n)) (qeps k) := by
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n hn
  have a' : qle (qsub qzero (qeps k)) (qsub (u n) (v n)) := a
  have b' : qle (qsub (u n) (v n)) (qadd qzero (qeps k)) := b
  generalize qsub (u n) (v n) = d at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The corner of `exp`'s series vanishes, at any `a, b ≥ 0`. -/
theorem corner_small {a b : QExpr} (ha : qle qzero a) (hb : qle qzero b) (k : Nat) :
    ∃ N0, ∀ n, N0 ≤ n → qle (corner (tm a) (tm b) n) (qeps k) := by
  obtain ⟨Ha, hHa⟩ := S_bounded ha
  obtain ⟨Hb, hHb⟩ := S_bounded hb
  have Ha0 : qle qzero Ha := qle_trans (S_nonneg ha 0) (hHa 0)
  have Hb0 : qle qzero Hb := qle_trans (S_nonneg hb 0) (hHb 0)
  obtain ⟨B, hB1, _⟩ := qexpr_bound (qadd (qadd Ha Ha) (qadd Hb Hb))
  have hB : qle (qadd (qadd Ha Ha) (qadd Hb Hb)) (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  obtain ⟨Ka, hga⟩ := good_exists a
  obtain ⟨Kb, hgb⟩ := good_exists b
  obtain ⟨Ma, hKa, hMa⟩ := tm_small ha hga (k + B)
  obtain ⟨Mb, hKb, hMb⟩ := tm_small hb hgb (k + B)
  refine ⟨(Ma + Mb) + (Ma + Mb), fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ := le_ex hn
  have ga : Good a (Ma + Mb) := good_mono hga (Nat.le_trans hKa (Nat.le_add_right Ma Mb))
  have gb : Good b (Ma + Mb) := good_mono hgb (Nat.le_trans hKb (Nat.le_add_left Mb Ma))
  have c := corner_exp ha hb hHa hHb ga gb j
  have ta := hMa (Ma + Mb) (Nat.le_add_right Ma Mb)
  have tb := hMb (Ma + Mb) (Nat.le_add_left Mb Ma)
  have f1 := ZExp.scale ta Hb0
  have f2 := scale_l tb Ha0
  have f3 := ZExp.scale hB (qeps_nonneg (k + B))
  have pb := qpow2_mul_eps B k
  clear hHa hHb hMa hMb ga gb hB1 hga hgb
  generalize corner (tm a) (tm b) (Ma + Mb + (Ma + Mb) + j) = K at *
  generalize tm a (Ma + Mb) = Ta at *; generalize tm b (Ma + Mb) = Tb at *
  generalize qmul (qofInt (pow2 B)) (qeps (k + B)) = P at *
  have g1 : qle K (qadd (qmul (qeps (k + B)) Hb) (qmul Ha (qeps (k + B)))) := by
    clear f3 pb hB; rat_linarith
  have g2 : qle (qadd (qmul (qeps (k + B)) Hb) (qmul Ha (qeps (k + B)))) P := by
    have := qeps_nonneg (k + B)
    have h1 := qmul_nonneg Ha0 this; have h2 := qmul_nonneg Hb0 this
    clear c ta tb f1 f2 g1; rat_linarith
  exact qle_trans g1 (qle_trans g2 (qle_of_qEq pb))

/-- The addition formulas IN THE LIMIT. -/
theorem add_lim {x y : Nat → QExpr} {a b : QExpr} (ha : qle qzero a) (hb : qle qzero b) (hx : Bnd x a) (hy : Bnd y b) :
    Eq0 (cs (fun n => qadd (x n) (y n))) (fun n => qsub (qmul (cs x n) (cs y n)) (qmul (sn x n) (sn y n))) ∧
    Eq0 (sn (fun n => qadd (x n) (y n))) (fun n => qadd (qmul (cs x n) (sn y n)) (qmul (sn x n) (cs y n))) := by
  obtain ⟨Nx, hNx⟩ := hx
  obtain ⟨Ny, hNy⟩ := hy
  constructor <;> refine Eq0_of (fun k => ?_) <;> obtain ⟨Nc, hNc⟩ := corner_small ha hb (k + 1) <;>
    refine ⟨Nx + Ny + Nc, fun n hn => ?_⟩ <;>
    have bx := hNx n (Nat.le_trans (Nat.le_trans (Nat.le_add_right Nx Ny) (Nat.le_add_right _ Nc)) hn) <;>
    have by' := hNy n (Nat.le_trans (Nat.le_trans (Nat.le_add_left Ny Nx) (Nat.le_add_right _ Nc)) hn) <;>
    have kc := hNc n (Nat.le_trans (Nat.le_add_left Nc _) hn) <;>
    obtain ⟨⟨p1, p2⟩, ⟨q1, q2⟩⟩ := add_bounds bx by' n <;>
    have e := qeps_succ_add k <;>
    unfold cs sn <;>
    generalize corner (tm a) (tm b) n = K at *
  · generalize qsub (Cn (qadd (x n) (y n)) n) (qsub (qmul (Cn (x n) n) (Cn (y n) n)) (qmul (Sn (x n) n) (Sn (y n) n))) = D at *
    clear q1 q2
    exact ⟨by rat_linarith, by rat_linarith⟩
  · generalize qsub (Sn (qadd (x n) (y n)) n) (qadd (qmul (Cn (x n) n) (Sn (y n) n)) (qmul (Sn (x n) n) (Cn (y n) n))) = D at *
    clear p1 p2
    exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## Rules for `Eq0` -/

theorem Eq0_congr {u v : Nat → QExpr} (h : ∀ n, qEq (u n) (v n)) : Eq0 u v :=
  Eq0_of (fun k => ⟨0, fun n _ => by
    have := h n; have := qeps_nonneg k
    generalize u n = a at *; generalize v n = b at *
    unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩⟩)

theorem Eq0_symm {u v : Nat → QExpr} (h : Eq0 u v) : Eq0 v u :=
  Eq0_of (fun k => by
    obtain ⟨N, hN⟩ := Eq0_get h k
    exact ⟨N, fun n hn => by
      obtain ⟨a, b⟩ := hN n hn
      generalize u n = x at *; generalize v n = y at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩)

theorem Eq0_trans {u v w : Nat → QExpr} (h1 : Eq0 u v) (h2 : Eq0 v w) : Eq0 u w :=
  Eq0_of (fun k => by
    obtain ⟨N1, hN1⟩ := Eq0_get h1 (k + 1)
    obtain ⟨N2, hN2⟩ := Eq0_get h2 (k + 1)
    exact ⟨N1 + N2, fun n hn => by
      obtain ⟨a1, a2⟩ := hN1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
      obtain ⟨b1, b2⟩ := hN2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
      have e := qeps_succ_add k
      generalize u n = x at *; generalize v n = y at *; generalize w n = z at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩)

theorem Eq0_add {u v u' v' : Nat → QExpr} (h1 : Eq0 u v) (h2 : Eq0 u' v') :
    Eq0 (fun n => qadd (u n) (u' n)) (fun n => qadd (v n) (v' n)) :=
  Eq0_of (fun k => by
    obtain ⟨N1, hN1⟩ := Eq0_get h1 (k + 1)
    obtain ⟨N2, hN2⟩ := Eq0_get h2 (k + 1)
    exact ⟨N1 + N2, fun n hn => by
      obtain ⟨a1, a2⟩ := hN1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
      obtain ⟨b1, b2⟩ := hN2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
      have e := qeps_succ_add k
      show Ab (qsub (qadd (u n) (u' n)) (qadd (v n) (v' n))) (qeps k)
      generalize u n = x at *; generalize v n = y at *; generalize u' n = x' at *; generalize v' n = y' at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩)

theorem Eq0_neg {u v : Nat → QExpr} (h : Eq0 u v) : Eq0 (fun n => qneg (u n)) (fun n => qneg (v n)) :=
  Eq0_of (fun k => by
    obtain ⟨N, hN⟩ := Eq0_get h k
    exact ⟨N, fun n hn => by
      obtain ⟨a, b⟩ := hN n hn
      show Ab (qsub (qneg (u n)) (qneg (v n))) (qeps k)
      generalize u n = x at *; generalize v n = y at *
      unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩)

/-- A bounded sequence times one that goes to `c` goes to `·c`. -/
theorem Eq0_mul_const {u w : Nat → QExpr} {H c : QExpr} (hu : ∃ N, ∀ n, N ≤ n → Ab (u n) H)
    (hw : Eq0 w (fun _ => c)) : Eq0 (fun n => qmul (u n) (w n)) (fun n => qmul (u n) c) := by
  obtain ⟨N0, hN0⟩ := hu
  obtain ⟨B, hB1, _⟩ := qexpr_bound H
  have hB : qle H (qofInt (pow2 B)) := by unfold qsub at hB1; rat_linarith
  refine Eq0_of (fun k => ?_)
  obtain ⟨N1, hN1⟩ := Eq0_get hw (k + B)
  refine ⟨N0 + N1, fun n hn => ?_⟩
  have bu := hN0 n (Nat.le_trans (Nat.le_add_right N0 N1) hn)
  have bw := hN1 n (Nat.le_trans (Nat.le_add_left N1 N0) hn)
  have m := mul_abs bu bw
  have pb := qpow2_mul_eps B k
  have H0 : qle qzero H := by obtain ⟨h1, h2⟩ := bu; rat_linarith
  have f := ZExp.scale hB (qeps_nonneg (k + B))
  have e : qEq (qmul (u n) (qsub (w n) c)) (qsub (qmul (u n) (w n)) (qmul (u n) c)) := by unfold qsub; rat_ring
  obtain ⟨m1, m2⟩ := m
  show Ab (qsub (qmul (u n) (w n)) (qmul (u n) c)) (qeps k)
  generalize qmul (u n) (qsub (w n) c) = P at *
  generalize qsub (qmul (u n) (w n)) (qmul (u n) c) = D at *
  generalize qmul H (qeps (k + B)) = Q at *
  generalize qmul (qofInt (pow2 B)) (qeps (k + B)) = R at *
  clear hN0 hN1 bu bw hB1
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- Bounded partial sums: `|C_N(x)|, |S_N(x)| ≤ S(a, N)`. -/
theorem CS_abs {x a : QExpr} (hx : Ab x a) (N : Nat) : Ab (Cn x N) (S a N) ∧ Ab (Sn x N) (S a N) := by
  rw [S_bs]
  exact ⟨bs_abs (fun m => (crci_abs hx m).1) N, bs_abs (fun m => (crci_abs hx m).2) N⟩

theorem cs_bounded {x : Nat → QExpr} {a : QExpr} (ha : qle qzero a) (hx : Bnd x a) :
    ∃ H, (∃ N, ∀ n, N ≤ n → Ab (cs x n) H) ∧ (∃ N, ∀ n, N ≤ n → Ab (sn x n) H) := by
  obtain ⟨H, hH⟩ := S_bounded ha
  obtain ⟨N, hN⟩ := hx
  refine ⟨H, ⟨N, fun n hn => ?_⟩, ⟨N, fun n hn => ?_⟩⟩
  · obtain ⟨⟨a1, a2⟩, _⟩ := CS_abs (hN n hn) n
    have := hH n; unfold cs; exact ⟨by rat_linarith, by rat_linarith⟩
  · obtain ⟨_, ⟨a1, a2⟩⟩ := CS_abs (hN n hn) n
    have := hH n; unfold sn; exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The shifts by `ρ` -/

theorem Eq0_of_Ev {u : Nat → QExpr} {c : QExpr} (h : Ev u c c) : Eq0 u (fun _ => c) := fun k => by
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨a, b⟩ := hN n hn
  show qle (qsub qzero (qeps k)) (qsub (u n) c) ∧ qle (qsub (u n) c) (qadd qzero (qeps k))
  generalize u n = x at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem rho_bnd : Bnd rho (qadd qone qone) := by
  obtain ⟨N0, hN0⟩ := rho_facts
  refine ⟨N0, fun n hn => ?_⟩
  obtain ⟨r1, r2, _, _⟩ := hN0 n hn
  have := qeps_nonneg n; have := qle_of_qlt qone_pos
  exact ⟨by rat_linarith, by rat_linarith⟩

theorem Eq0_sub {u v u' v' : Nat → QExpr} (h1 : Eq0 u v) (h2 : Eq0 u' v') :
    Eq0 (fun n => qsub (u n) (u' n)) (fun n => qsub (v n) (v' n)) :=
  Eq0_add h1 (Eq0_neg h2)

/-- `sin(x + ρ) = cos x`. -/
theorem shift_sin {x : Nat → QExpr} {a : QExpr} (ha : qle qzero a) (hx : Bnd x a) :
    Eq0 (sn (fun n => qadd (x n) (rho n))) (cs x) := by
  obtain ⟨H, hc, hs⟩ := cs_bounded ha hx
  have A := (add_lim ha two_pos hx rho_bnd).2
  have B1 := Eq0_mul_const hc (Eq0_of_Ev sin_rho)
  have B2 := Eq0_mul_const hs (Eq0_of_Ev cos_rho)
  refine Eq0_trans A (Eq0_trans (Eq0_add B1 B2) (Eq0_congr (fun n => ?_)))
  show qEq (qadd (qmul (cs x n) qone) (qmul (sn x n) qzero)) (cs x n)
  rat_ring

/-- `cos(x + ρ) = −sin x`. -/
theorem shift_cos {x : Nat → QExpr} {a : QExpr} (ha : qle qzero a) (hx : Bnd x a) :
    Eq0 (cs (fun n => qadd (x n) (rho n))) (fun n => qneg (sn x n)) := by
  obtain ⟨H, hc, hs⟩ := cs_bounded ha hx
  have A := (add_lim ha two_pos hx rho_bnd).1
  have B1 := Eq0_mul_const hc (Eq0_of_Ev cos_rho)
  have B2 := Eq0_mul_const hs (Eq0_of_Ev sin_rho)
  refine Eq0_trans A (Eq0_trans (Eq0_sub B1 B2) (Eq0_congr (fun n => ?_)))
  show qEq (qsub (qmul (cs x n) qzero) (qmul (sn x n) qone)) (qneg (sn x n))
  unfold qsub; rat_ring

end ZTrig

#print axioms ZTrig.Eq0_of
#print axioms ZTrig.corner_small
#print axioms ZTrig.add_lim
#print axioms ZTrig.Eq0_trans
#print axioms ZTrig.Eq0_mul_const
#print axioms ZTrig.cs_bounded
#print axioms ZTrig.shift_sin
#print axioms ZTrig.shift_cos
