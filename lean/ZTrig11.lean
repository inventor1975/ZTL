import ZTrig10

/-!
# ZTrig11 — the kernel's `sin` over an interval is sound (`zfunc.iv_sin`). Zero axioms.

Stage 11 of the full sine: `ZTrig10` with `sin` for `cos`.

  * `sin_abs_unif`, `sin_pm1` — `|sin| ≤ 1` to every precision — the kernel's `±1`;
  * `period_pq_S`, `near_shift_S` — whole periods for `sin`, through `sin y = cos(y + 3ρ)`;
  * `sin_win_up` — no maximum inside (`[−3ρ, ρ]`, via `cos` on `[0, 4ρ]`); `sin_win_lo` — no minimum inside
    (`[−ρ, 3ρ]`, via `sin y = cos(y − ρ)` on `[−2ρ, 2ρ]`);
  * `sin_up`, `sin_lo`, `swin_up_of`, `swin_lo_of`, `SinHi`, `SinLo`, `Ev_sin` — the rule assembled; the kernel's
    maxima `ρ + 4ρj`, minima `−ρ + 4ρj` (`HALF_PI`).
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

def six : QExpr := qadd (qadd (qadd qone qone) (qadd qone qone)) (qadd qone qone)
def t3 (x : QExpr) : QExpr := qadd (qadd x x) x

theorem six_nonneg : qle qzero six := by unfold six; have := qle_of_qlt qone_pos; rat_linarith

theorem sin_abs_unif {A : QExpr} (hA : qle qzero A) (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ x, Ab x A →
    Ab (Sn x n) (qadd qone (qeps k)) := by
  obtain ⟨N0, hN0⟩ := corner_small hA hA (k + 1)
  refine ⟨N0 + 1, fun n hn x hx => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ m =>
    obtain ⟨p1, _⟩ := pyth hx m
    have cs := hN0 (m + 1) (le_l' hn)
    have e := qeps_succ_add k
    have s2 := qmul_self_nonneg (Cn x (m + 1))
    have cc : qle (qmul (Sn x (m + 1)) (Sn x (m + 1))) (qadd qone (qeps k)) := by
      generalize corner (tm A) (tm A) (m + 1) = K at *
      generalize qmul (Cn x (m + 1)) (Cn x (m + 1)) = CC at *
      generalize qmul (Sn x (m + 1)) (Sn x (m + 1)) = SS at *
      clear hN0; unfold qsub at *; rat_linarith
    have ep := qeps_nonneg k
    have o := qle_of_qlt qone_pos
    have nn : qEq (qmul (qneg (Sn x (m + 1))) (qneg (Sn x (m + 1)))) (qmul (Sn x (m + 1)) (Sn x (m + 1))) := by rat_ring
    have m1 : qEq (qmul (Sn x (m + 1)) qone) (Sn x (m + 1)) := by rat_ring
    have m2 : qEq (qmul (qneg (Sn x (m + 1))) qone) (qneg (Sn x (m + 1))) := by rat_ring
    constructor
    · cases qle_total (qneg qone) (Sn x (m + 1)) with
      | inl h => rat_linarith
      | inr h =>
        have sc := scale_l (show qle qone (qneg (Sn x (m + 1))) by rat_linarith) (show qle qzero (qneg (Sn x (m + 1))) by rat_linarith)
        generalize qmul (Sn x (m + 1)) (Sn x (m + 1)) = SS at *
        generalize qmul (qneg (Sn x (m + 1))) (qneg (Sn x (m + 1))) = NN at *
        generalize qmul (qneg (Sn x (m + 1))) qone = N1 at *
        generalize Sn x (m + 1) = C at *
        clear hN0 cs p1 s2 hx; rat_linarith
    · cases qle_total (Sn x (m + 1)) qone with
      | inl h => rat_linarith
      | inr h =>
        have sc := scale_l h (show qle qzero (Sn x (m + 1)) by rat_linarith)
        generalize qmul (Sn x (m + 1)) (Sn x (m + 1)) = SS at *
        generalize qmul (Sn x (m + 1)) qone = C1 at *
        generalize Sn x (m + 1) = C at *
        clear hN0 cs p1 s2 hx nn m2; rat_linarith



/-- `sin` over whole periods, through `sin y = cos(y + 3ρ)`. -/
theorem period_pq_S {A : QExpr} (hA : qle qzero A) (p q k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ z z', Ab z A → Ab z' A →
    qEq (qadd z (qmul (qnat q) (four n))) (qadd z' (qmul (qnat p) (four n))) →
    Ab (qsub (Sn z n) (Sn z' n)) (qeps k) := by
  have hA6 : qle qzero (qadd A six) := by have := six_nonneg; rat_linarith
  obtain ⟨N3, h3⟩ := three_shift hA (k + 2)
  obtain ⟨Np, hp⟩ := period_pq hA6 p q (k + 2)
  obtain ⟨R, hR⟩ := rho_facts
  refine ⟨N3 + (Np + R), fun n hn z z' hz hz' e => ?_⟩
  obtain ⟨r1, r2', _, _⟩ := hR n (le_r' (le_r' hn))
  have r0 : qle qzero (rho n) := by have := qle_of_qlt qone_pos; rat_linarith
  have r2 : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  have b : ∀ w, Ab w A → Ab (qadd (qadd (qadd w (rho n)) (rho n)) (rho n)) (qadd A six) := fun w ⟨w1, w2⟩ => by
    unfold six; exact ⟨by rat_linarith, by rat_linarith⟩
  have e' : qEq (qadd (qadd (qadd (qadd z (rho n)) (rho n)) (rho n)) (qmul (qnat q) (four n)))
      (qadd (qadd (qadd (qadd z' (rho n)) (rho n)) (rho n)) (qmul (qnat p) (four n))) := by
    generalize qmul (qnat q) (four n) = Q at *; generalize qmul (qnat p) (four n) = P at *
    exact qle_antisymm (by rat_linarith) (by rat_linarith)
  obtain ⟨c1, c2⟩ := hp n (le_l' (le_r' hn)) _ _ (b z hz) (b z' hz') e'
  obtain ⟨a1, a2⟩ := h3 n (le_l' hn) z hz
  obtain ⟨b1, b2⟩ := h3 n (le_l' hn) z' hz'
  have t := three_eps k
  generalize Cn (qadd (qadd (qadd z (rho n)) (rho n)) (rho n)) n = Cz at *
  generalize Cn (qadd (qadd (qadd z' (rho n)) (rho n)) (rho n)) n = Cz' at *
  generalize Sn z n = Sz at *; generalize Sn z' n = Sz' at *
  clear h3 hp hR; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `sin` has no maximum inside `[−3ρ, ρ]`: a point there is below one of the window's ends. -/
theorem sin_win_up (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ a0 z a1, qle (qneg (qadd (qadd (rho n) (rho n)) (rho n))) a0 →
    qle a0 z → qle z a1 → qle a1 (rho n) →
    qle (Sn z n) (qadd (Sn a0 n) (qeps k)) ∨ qle (Sn z n) (qadd (Sn a1 n) (qeps k)) := by
  obtain ⟨N3, h3⟩ := three_shift six_nonneg (k + 2)
  obtain ⟨Nw, hw⟩ := cos_win_up (k + 2)
  obtain ⟨R, hR⟩ := rho_facts
  refine ⟨N3 + (Nw + R), fun n hn a0 z a1 g0 g1 g2 g3 => ?_⟩
  obtain ⟨r1, r2', _, _⟩ := hR n (le_r' (le_r' hn))
  have r0 : qle qzero (rho n) := by have := qle_of_qlt qone_pos; rat_linarith
  have r2 : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  have b : ∀ w, qle (qneg (qadd (qadd (rho n) (rho n)) (rho n))) w → qle w (rho n) → Ab w six := fun w w1 w2 => by
    unfold six; have := qle_of_qlt qone_pos; exact ⟨by rat_linarith, by rat_linarith⟩
  obtain ⟨_, za⟩ := h3 n (le_l' hn) z (b z (qle_trans g0 g1) (qle_trans g2 g3))
  obtain ⟨a01, _⟩ := h3 n (le_l' hn) a0 (b a0 g0 (qle_trans g1 (qle_trans g2 g3)))
  obtain ⟨a11, _⟩ := h3 n (le_l' hn) a1 (b a1 (qle_trans g0 (qle_trans g1 g2)) g3)
  have t := three_eps k
  have p0 := qeps_nonneg (k + 2)
  cases hw n (le_l' (le_r' hn)) (qadd (qadd (qadd a0 (rho n)) (rho n)) (rho n))
      (qadd (qadd (qadd z (rho n)) (rho n)) (rho n)) (qadd (qadd (qadd a1 (rho n)) (rho n)) (rho n))
      (by rat_linarith) (by rat_linarith) (by rat_linarith) (by unfold four; rat_linarith) with
  | inl c =>
    left
    generalize Cn (qadd (qadd (qadd z (rho n)) (rho n)) (rho n)) n = Cz at *
    generalize Cn (qadd (qadd (qadd a0 (rho n)) (rho n)) (rho n)) n = Ca at *
    generalize Sn z n = Sz at *; generalize Sn a0 n = Sa at *
    clear h3 hw hR a11; unfold qsub at *; rat_linarith
  | inr c =>
    right
    generalize Cn (qadd (qadd (qadd z (rho n)) (rho n)) (rho n)) n = Cz at *
    generalize Cn (qadd (qadd (qadd a1 (rho n)) (rho n)) (rho n)) n = Ca at *
    generalize Sn z n = Sz at *; generalize Sn a1 n = Sa at *
    clear h3 hw hR a01; unfold qsub at *; rat_linarith

/-- `sin` has no minimum inside `[−ρ, 3ρ]`: a point there is above one of the window's ends. -/
theorem sin_win_lo (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ a0 z a1, qle (qneg (rho n)) a0 →
    qle a0 z → qle z a1 → qle a1 (qadd (qadd (rho n) (rho n)) (rho n)) →
    qle (Sn a0 n) (qadd (Sn z n) (qeps k)) ∨ qle (Sn a1 n) (qadd (Sn z n) (qeps k)) := by
  obtain ⟨N1, h1⟩ := shift_unif six_nonneg (k + 2)
  obtain ⟨Nw, hw⟩ := cos_win_lo (k + 2)
  obtain ⟨R, hR⟩ := rho_facts
  refine ⟨N1 + (Nw + R), fun n hn a0 z a1 g0 g1 g2 g3 => ?_⟩
  obtain ⟨r1, r2', _, _⟩ := hR n (le_r' (le_r' hn))
  have r0 : qle qzero (rho n) := by have := qle_of_qlt qone_pos; rat_linarith
  have r2 : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  have b : ∀ w, qle (qneg (rho n)) w → qle w (qadd (qadd (rho n) (rho n)) (rho n)) → Ab (qsub w (rho n)) six :=
    fun w w1 w2 => by unfold six qsub; have := qle_of_qlt qone_pos; exact ⟨by rat_linarith, by rat_linarith⟩
  have sr : ∀ w, qEq (Sn (qadd (qsub w (rho n)) (rho n)) n) (Sn w n) := fun w =>
    Sn_respects (by unfold qsub; rat_ring) n
  obtain ⟨⟨z1, _⟩, _⟩ := h1 n (le_l' hn) _ (b z (qle_trans g0 g1) (qle_trans g2 g3))
  obtain ⟨⟨_, a02⟩, _⟩ := h1 n (le_l' hn) _ (b a0 g0 (qle_trans g1 (qle_trans g2 g3)))
  obtain ⟨⟨_, a12⟩, _⟩ := h1 n (le_l' hn) _ (b a1 (qle_trans g0 (qle_trans g1 g2)) g3)
  have e0 := sr a0; have ez := sr z; have e1 := sr a1
  have t := three_eps k
  have p0 := qeps_nonneg (k + 2)
  cases hw n (le_l' (le_r' hn)) (qsub a0 (rho n)) (qsub z (rho n)) (qsub a1 (rho n))
      (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith) (by unfold qsub; rat_linarith)
      (by unfold qsub; rat_linarith) with
  | inl c =>
    left
    generalize Cn (qsub z (rho n)) n = Cz at *; generalize Cn (qsub a0 (rho n)) n = Ca at *
    generalize Sn (qadd (qsub z (rho n)) (rho n)) n = Sz' at *; generalize Sn (qadd (qsub a0 (rho n)) (rho n)) n = Sa' at *
    generalize Sn z n = Sz at *; generalize Sn a0 n = Sa at *
    clear h1 hw hR sr a12 e1; unfold qsub at *; rat_linarith
  | inr c =>
    right
    generalize Cn (qsub z (rho n)) n = Cz at *; generalize Cn (qsub a1 (rho n)) n = Ca at *
    generalize Sn (qadd (qsub z (rho n)) (rho n)) n = Sz' at *; generalize Sn (qadd (qsub a1 (rho n)) (rho n)) n = Sa' at *
    generalize Sn z n = Sz at *; generalize Sn a1 n = Sa at *
    clear h1 hw hR sr a02 e0; unfold qsub at *; rat_linarith

theorem near_shift_S {x : Nat → QExpr} {lu hu : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu) (p q k : Nat) :
    ∃ N, ∀ n, N ≤ n → ∃ y, qle lu y ∧ qle y hu ∧
      Ab (qsub (Sn (x n) n) (Sn (qadd y (dd p q n)) n)) (qeps k) ∧
      Ab (qsub (Sn lu n) (Sn (qadd lu (dd p q n)) n)) (qeps k) ∧
      Ab (qsub (Sn hu n) (Sn (qadd hu (dd p q n)) n)) (qeps k) := by
  obtain ⟨M, _, hM0, _, ml, mh, _, _⟩ := bound4 lu hu lu hu
  have o := qle_of_qlt qone_pos
  have e8 : qle qzero eight := by unfold eight; rat_linarith
  have hA : qle qzero (qadd (qadd M qone) (qadd (qmul (qnat q) eight) (qmul (qnat p) eight))) := by
    have := qmul_nonneg (qnat_nonneg q) e8; have := qmul_nonneg (qnat_nonneg p) e8; rat_linarith
  generalize hAd : qadd (qadd M qone) (qadd (qmul (qnat q) eight) (qmul (qnat p) eight)) = A at hA
  have hMA : qle (qadd M qone) A := by
    rw [← hAd]; have := qmul_nonneg (qnat_nonneg q) e8; have := qmul_nonneg (qnat_nonneg p) e8; rat_linarith
  obtain ⟨H, hH⟩ := S_bounded hA
  obtain ⟨Bc, hB1, _⟩ := qexpr_bound H
  have hC : qle H (qofInt (pow2 Bc)) := by unfold qsub at hB1; rat_linarith
  obtain ⟨N1, h1⟩ := hx ((k + 1) + Bc)
  obtain ⟨R, hR⟩ := rho_facts
  obtain ⟨Np, hp⟩ := period_pq_S hA p q (k + 1)
  obtain ⟨Nq, hq⟩ := period_pq_S hA p q k
  refine ⟨N1 + (R + (Np + Nq)), fun n hn => ?_⟩
  obtain ⟨x1, x2⟩ := h1 n (le_l' hn)
  obtain ⟨r1, r2', _, _⟩ := hR n (le_l' (le_r' hn))
  have r0 : qle qzero (rho n) := by rat_linarith
  have r2 : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
  have e1 := qeps_le_one ((k + 1) + Bc)
  obtain ⟨y, y1, y2, yz⟩ := clamp x1 x2 hlh (qeps_nonneg _)
  obtain ⟨m1, m2⟩ := ml; obtain ⟨m3, m4⟩ := mh
  unfold qsub at m1 m2 m3 m4
  have aL : Ab lu (qadd M qone) := ⟨by rat_linarith, by rat_linarith⟩
  have aH : Ab hu (qadd M qone) := ⟨by rat_linarith, by rat_linarith⟩
  have aY : Ab y (qadd M qone) := ⟨by rat_linarith, by rat_linarith⟩
  have aX : Ab (x n) A := by unfold qsub at x1; exact ⟨by rat_linarith, by rat_linarith⟩
  have wid : ∀ w, Ab w (qadd M qone) → Ab w A := fun w ⟨a, b⟩ => ⟨by rat_linarith, by rat_linarith⟩
  have sh : ∀ w, Ab w (qadd M qone) → Ab (qadd w (dd p q n)) A := fun w hw => by
    have := dd_bound (p := p) (q := q) hw r0 r2; rw [hAd] at this; exact this
  have eq : ∀ w, qEq (qadd w (qmul (qnat q) (four n))) (qadd (qadd w (dd p q n)) (qmul (qnat p) (four n))) :=
    fun w => by unfold dd qsub; rat_ring
  have L := (CS_lip aX (wid y aY) yz n).2
  have L' := lip_eps (k := k + 1) L (hH n) hC
  have P := hp n (le_l' (le_r' (le_r' hn))) y _ (wid y aY) (sh y aY) (eq y)
  have ee := qeps_succ_add k
  refine ⟨y, y1, y2, ?_, hq n (le_r' (le_r' (le_r' hn))) lu _ (wid lu aL) (sh lu aL) (eq lu),
    hq n (le_r' (le_r' (le_r' hn))) hu _ (wid hu aH) (sh hu aH) (eq hu)⟩
  obtain ⟨l1, l2⟩ := L'; obtain ⟨p1, p2⟩ := P
  generalize Sn (x n) n = Cx at *; generalize Sn y n = Cy at *; generalize Sn (qadd y (dd p q n)) n = Cs at *
  clear hp hq hR h1 hH; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩


theorem sin_up {x : Nat → QExpr} {lu hu l1 h1 l2 h2 h : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu)
    (c1 : SinCert lu l1 h1) (c2 : SinCert hu l2 h2) (b1 : qle h1 h) (b2 : qle h2 h) (p q : Nat)
    (win : ∃ N, ∀ n, N ≤ n → qle (qneg (qadd (qadd (rho n) (rho n)) (rho n))) (qadd lu (dd p q n)) ∧
      qle (qadd hu (dd p q n)) (rho n)) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (Sn (x n) n) (qadd h (qeps k)) := by
  intro k
  obtain ⟨N1, hN1⟩ := near_shift_S hx hlh p q (k + 2)
  obtain ⟨N2, hN2⟩ := sin_win_up (k + 2)
  obtain ⟨M1, e1⟩ := cert_sin c1
  obtain ⟨M2, e2⟩ := cert_sin c2
  obtain ⟨W, hW⟩ := win
  refine ⟨N1 + (N2 + (M1 + (M2 + W))), fun n hn => ?_⟩
  obtain ⟨y, y1, y2, ⟨_, a2⟩, ⟨l1', _⟩, ⟨u1, _⟩⟩ := hN1 n (le_l' hn)
  obtain ⟨w1, w2⟩ := hW n (le_r' (le_r' (le_r' (le_r' hn))))
  obtain ⟨_, g1⟩ := e1 n (le_l' (le_r' (le_r' hn)))
  obtain ⟨_, g2⟩ := e2 n (le_l' (le_r' (le_r' (le_r' hn))))
  have t := three_eps k
  have p0 := qeps_nonneg (k + 2)
  have m1 : qle (qadd lu (dd p q n)) (qadd y (dd p q n)) := by rat_linarith
  have m2 : qle (qadd y (dd p q n)) (qadd hu (dd p q n)) := by rat_linarith
  cases hN2 n (le_l' (le_r' hn)) _ _ _ w1 m1 m2 w2 with
  | inl c =>
    generalize Sn (qadd y (dd p q n)) n = Cy at *; generalize Sn (qadd lu (dd p q n)) n = Cl at *
    generalize Sn (x n) n = Cx at *; generalize Sn lu n = C0 at *
    clear hN1 hN2 e1 e2 hW c2 g2 u1; unfold qsub at *; rat_linarith
  | inr c =>
    generalize Sn (qadd y (dd p q n)) n = Cy at *; generalize Sn (qadd hu (dd p q n)) n = Ch at *
    generalize Sn (x n) n = Cx at *; generalize Sn hu n = C0 at *
    clear hN1 hN2 e1 e2 hW c1 g1 l1'; unfold qsub at *; rat_linarith


theorem sin_lo {x : Nat → QExpr} {lu hu l1 h1 l2 h2 l : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu)
    (c1 : SinCert lu l1 h1) (c2 : SinCert hu l2 h2) (b1 : qle l l1) (b2 : qle l l2) (p q : Nat)
    (win : ∃ N, ∀ n, N ≤ n → qle (qneg (rho n)) (qadd lu (dd p q n)) ∧
      qle (qadd hu (dd p q n)) (qadd (qadd (rho n) (rho n)) (rho n))) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub l (qeps k)) (Sn (x n) n) := by
  intro k
  obtain ⟨N1, hN1⟩ := near_shift_S hx hlh p q (k + 2)
  obtain ⟨N2, hN2⟩ := sin_win_lo (k + 2)
  obtain ⟨M1, e1⟩ := cert_sin c1
  obtain ⟨M2, e2⟩ := cert_sin c2
  obtain ⟨W, hW⟩ := win
  refine ⟨N1 + (N2 + (M1 + (M2 + W))), fun n hn => ?_⟩
  obtain ⟨y, y1, y2, ⟨a1, _⟩, ⟨_, l2'⟩, ⟨_, u2⟩⟩ := hN1 n (le_l' hn)
  obtain ⟨w1, w2⟩ := hW n (le_r' (le_r' (le_r' (le_r' hn))))
  obtain ⟨g1, _⟩ := e1 n (le_l' (le_r' (le_r' hn)))
  obtain ⟨g2, _⟩ := e2 n (le_l' (le_r' (le_r' (le_r' hn))))
  have t := three_eps k
  have p0 := qeps_nonneg (k + 2)
  have m1 : qle (qadd lu (dd p q n)) (qadd y (dd p q n)) := by rat_linarith
  have m2 : qle (qadd y (dd p q n)) (qadd hu (dd p q n)) := by rat_linarith
  cases hN2 n (le_l' (le_r' hn)) _ _ _ w1 m1 m2 w2 with
  | inl c =>
    generalize Sn (qadd y (dd p q n)) n = Cy at *; generalize Sn (qadd lu (dd p q n)) n = Cl at *
    generalize Sn (x n) n = Cx at *; generalize Sn lu n = C0 at *
    clear hN1 hN2 e1 e2 hW c2 g2 u2; unfold qsub at *; rat_linarith
  | inr c =>
    generalize Sn (qadd y (dd p q n)) n = Cy at *; generalize Sn (qadd hu (dd p q n)) n = Ch at *
    generalize Sn (x n) n = Cx at *; generalize Sn hu n = C0 at *
    clear hN1 hN2 e1 e2 hW c1 g1 l2'; unfold qsub at *; rat_linarith

/-- "No maximum of `sin` inside", in rationals: the window, shifted, lies in `[−3ρ, ρ]` from some index on. -/
theorem swin_up_of {ρl ρh lu hu : QExpr} (hρ : ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) ∧ qle (rho n) ρh)
    (p q B : Nat)
    (S1 : qle (qadd (f4 (qmul (qnat p) ρh)) (qadd (f4 (qeps B)) (t3 (qeps B)))) (qadd (qadd lu (f4 (qmul (qnat q) ρl))) (t3 ρl)))
    (S2 : qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (qadd (f4 (qeps B)) (qeps B))) (qadd (f4 (qmul (qnat p) ρl)) ρl)) :
    ∃ N, ∀ n, N ≤ n → qle (qneg (qadd (qadd (rho n) (rho n)) (rho n))) (qadd lu (dd p q n)) ∧
      qle (qadd hu (dd p q n)) (rho n) := by
  obtain ⟨Nq, hq⟩ := mult_rho hρ q B
  obtain ⟨Np, hp⟩ := mult_rho hρ p B
  obtain ⟨N0, h0⟩ := hρ
  refine ⟨Nq + (Np + (N0 + B)), fun n hn => ?_⟩
  obtain ⟨q1, q2⟩ := hq n (le_l' hn)
  obtain ⟨p1, p2⟩ := hp n (le_l' (le_r' hn))
  obtain ⟨r1, _⟩ := h0 n (le_l' (le_r' (le_r' hn)))
  have en : qle (qeps n) (qeps B) := eps_anti (le_r' (le_r' (le_r' hn)))
  obtain ⟨d1, _⟩ := dd_f4 p q n
  generalize dd p q n = D at *
  generalize qmul (qnat q) (rho n) = Xq at *; generalize qmul (qnat p) (rho n) = Xp at *
  generalize qmul (qnat q) ρl = Ql at *; generalize qmul (qnat q) ρh = Qh at *
  generalize qmul (qnat p) ρl = Pl at *; generalize qmul (qnat p) ρh = Ph at *
  clear hq hp h0; unfold f4 t3 qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- "No minimum of `sin` inside", in rationals: the window, shifted, lies in `[−ρ, 3ρ]` from some index on. -/
theorem swin_lo_of {ρl ρh lu hu : QExpr} (hρ : ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) ∧ qle (rho n) ρh)
    (p q B : Nat)
    (T1 : qle (qadd (f4 (qmul (qnat p) ρh)) (qadd (f4 (qeps B)) (qeps B))) (qadd (qadd lu (f4 (qmul (qnat q) ρl))) ρl))
    (T2 : qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (qadd (f4 (qeps B)) (t3 (qeps B)))) (qadd (f4 (qmul (qnat p) ρl)) (t3 ρl))) :
    ∃ N, ∀ n, N ≤ n → qle (qneg (rho n)) (qadd lu (dd p q n)) ∧
      qle (qadd hu (dd p q n)) (qadd (qadd (rho n) (rho n)) (rho n)) := by
  obtain ⟨Nq, hq⟩ := mult_rho hρ q B
  obtain ⟨Np, hp⟩ := mult_rho hρ p B
  obtain ⟨N0, h0⟩ := hρ
  refine ⟨Nq + (Np + (N0 + B)), fun n hn => ?_⟩
  obtain ⟨q1, q2⟩ := hq n (le_l' hn)
  obtain ⟨p1, p2⟩ := hp n (le_l' (le_r' hn))
  obtain ⟨r1, _⟩ := h0 n (le_l' (le_r' (le_r' hn)))
  have en : qle (qeps n) (qeps B) := eps_anti (le_r' (le_r' (le_r' hn)))
  obtain ⟨d1, _⟩ := dd_f4 p q n
  generalize dd p q n = D at *
  generalize qmul (qnat q) (rho n) = Xq at *; generalize qmul (qnat p) (rho n) = Xp at *
  generalize qmul (qnat q) ρl = Ql at *; generalize qmul (qnat q) ρh = Qh at *
  generalize qmul (qnat p) ρl = Pl at *; generalize qmul (qnat p) ρh = Ph at *
  clear hq hp h0; unfold f4 t3 qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The kernel's `±1` for `sin`. -/
theorem sin_pm1 {x : Nat → QExpr} {lu hu : QExpr} (hx : Ev x lu hu) (k : Nat) :
    ∃ N, ∀ n, N ≤ n → Ab (Sn (x n) n) (qadd qone (qeps k)) := by
  obtain ⟨A, hA, N0, hN0⟩ := ev_bound hx
  obtain ⟨N1, hN1⟩ := sin_abs_unif hA k
  exact ⟨N0 + N1, fun n hn => hN1 n (le_r' hn) _ (hN0 n (le_l' hn))⟩

def SinHi (lu hu h : QExpr) : Prop :=
  qle qone h ∨ ∃ ρl ρh, PiBr ρl ρh ∧ (∃ l1 h1, SinCert lu l1 h1 ∧ qle h1 h) ∧ (∃ l2 h2, SinCert hu l2 h2 ∧ qle h2 h) ∧
    ∃ p q B, qle (qadd (f4 (qmul (qnat p) ρh)) (qadd (f4 (qeps B)) (t3 (qeps B)))) (qadd (qadd lu (f4 (qmul (qnat q) ρl))) (t3 ρl)) ∧
      qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (qadd (f4 (qeps B)) (qeps B))) (qadd (f4 (qmul (qnat p) ρl)) ρl)

def SinLo (lu hu l : QExpr) : Prop :=
  qle l (qneg qone) ∨ ∃ ρl ρh, PiBr ρl ρh ∧ (∃ l1 h1, SinCert lu l1 h1 ∧ qle l l1) ∧ (∃ l2 h2, SinCert hu l2 h2 ∧ qle l l2) ∧
    ∃ p q B, qle (qadd (f4 (qmul (qnat p) ρh)) (qadd (f4 (qeps B)) (qeps B))) (qadd (qadd lu (f4 (qmul (qnat q) ρl))) ρl) ∧
      qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (qadd (f4 (qeps B)) (t3 (qeps B)))) (qadd (f4 (qmul (qnat p) ρl)) (t3 ρl))

/-- THE KERNEL'S `sin` OVER AN INTERVAL IS SOUND (`zfunc.iv_sin`). -/
theorem Ev_sin {x : Nat → QExpr} {lu hu l h : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu)
    (hi : SinHi lu hu h) (lo : SinLo lu hu l) : Ev (fun n => Sn (x n) n) l h := by
  refine Ev_of_sides ?_ ?_
  · cases lo with
    | inl h1 => intro k; obtain ⟨N, hN⟩ := sin_pm1 hx k; exact ⟨N, fun n hn => by
        obtain ⟨a, _⟩ := hN n hn; unfold qsub; rat_linarith⟩
    | inr h1 =>
      obtain ⟨ρl, ρh, br, ⟨l1, h1', c1, b1⟩, ⟨l2, h2', c2, b2⟩, p, q, B, L1, L2⟩ := h1
      exact sin_lo hx hlh c1 c2 b1 b2 p q (swin_lo_of br.ev p q B L1 L2)
  · cases hi with
    | inl h1 => intro k; obtain ⟨N, hN⟩ := sin_pm1 hx k; exact ⟨N, fun n hn => by
        obtain ⟨_, a⟩ := hN n hn; rat_linarith⟩
    | inr h1 =>
      obtain ⟨ρl, ρh, br, ⟨l1, h1', c1, b1⟩, ⟨l2, h2', c2, b2⟩, p, q, B, U1, U2⟩ := h1
      exact sin_up hx hlh c1 c2 b1 b2 p q (swin_up_of br.ev p q B U1 U2)

end ZTrig

#print axioms ZTrig.sin_abs_unif
#print axioms ZTrig.period_pq_S
#print axioms ZTrig.sin_win_up
#print axioms ZTrig.sin_win_lo
#print axioms ZTrig.near_shift_S
#print axioms ZTrig.sin_up
#print axioms ZTrig.sin_lo
#print axioms ZTrig.swin_up_of
#print axioms ZTrig.swin_lo_of
#print axioms ZTrig.sin_pm1
#print axioms ZTrig.Ev_sin
