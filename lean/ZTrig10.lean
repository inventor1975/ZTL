import ZTrig9

/-!
# ZTrig10 — the kernel's `cos` over an interval is sound (`zfunc.iv_cos`). Zero axioms.

Stage 10 of the full sine.

  * `CosCert x lo hi` — a partial sum with its tail, `lo ≤ C_M(x) ∓ 2·a^M/M! ≤ hi` (`|x| ≤ a`, `M` good);
    `cert_cos` — then `C_n(x) ∈ [lo, hi]` from index `M` on;
  * `rho_ge`, `rho_le`, `rho_br`, `PiBr` — `π`'s bracket (`zfunc.PI`, Machin) is checked by `cos` at its halves:
    a certified `cos ρl > 0` puts the run past `ρl`, a certified `cos ρh < 0` stops it before `ρh`;
  * `cos_abs_unif`, `cos_pm1` — `|cos| ≤ 1` to every precision (Pythagoras) — the kernel's `±1`;
  * `period_pq`, `near_shift` — a reading near `[lu, hu]` is clamped into it (Lipschitz) and carried by whole
    periods `d_n = q·4ρ_n − p·4ρ_n` (forward shifts only);
  * `cos_up`, `cos_lo` — no maximum inside (window in `[0, 4ρ]`) ⇒ below the ends' tops; no minimum inside
    (window in `[−2ρ, 2ρ]`) ⇒ above the ends' bottoms;
  * `win_up_of`, `win_lo_of` — "no extremum inside" checked in RATIONALS against the bracket, with a margin `ε_B`;
  * `CosHi`, `CosLo`, `Ev_cos` — the rule assembled.

The witnesses `p, q, B` and the certificates are data the checker is handed; that the Python kernel's `_touches`
test always admits such witnesses is argued (its non-touching is strict), not proved here.
-/

namespace ZTrig

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt

def CosCert (x lo hi : QExpr) : Prop :=
  ∃ a M, Ab x a ∧ Good a M ∧ qle lo (qsub (Cn x M) (qadd (tm a M) (tm a M))) ∧
    qle (qadd (Cn x M) (qadd (tm a M) (tm a M))) hi

def SinCert (x lo hi : QExpr) : Prop :=
  ∃ a M, Ab x a ∧ Good a M ∧ qle lo (qsub (Sn x M) (qadd (tm a M) (tm a M))) ∧
    qle (qadd (Sn x M) (qadd (tm a M) (tm a M))) hi

theorem cert_cos {x lo hi : QExpr} (h : CosCert x lo hi) : ∃ N, ∀ n, N ≤ n → qle lo (Cn x n) ∧ qle (Cn x n) hi := by
  obtain ⟨a, M, hx, g, h1, h2⟩ := h
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨⟨t1, t2⟩, _⟩ := CS_tail hx g n hn
  generalize Cn x n = C at *; generalize Cn x M = CM at *; generalize tm a M = T at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem cert_sin {x lo hi : QExpr} (h : SinCert x lo hi) : ∃ N, ∀ n, N ≤ n → qle lo (Sn x n) ∧ qle (Sn x n) hi := by
  obtain ⟨a, M, hx, g, h1, h2⟩ := h
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨_, ⟨t1, t2⟩⟩ := CS_tail hx g n hn
  generalize Sn x n = C at *; generalize Sn x M = CM at *; generalize tm a M = T at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- A positive rational lies above some `ε_B`. -/
theorem pos_floor {x : QExpr} (h : qlt qzero x) : ∃ B, qle (qeps B) x :=
  lv_floor h (show qle qone (qmul (qinv' x) x) by
    have := qmul_inv'_cancel (ne_zero_of_lt h); have := qmul_comm (qinv' x) x; rat_linarith)

/-- A CERTIFIED `cos ρl > 0` puts the run past `ρl`: from some index on, `ρl ≤ ρ_n + 2^−n`. -/
theorem rho_ge {ρl lo hi : QExpr} (h0 : qle qzero ρl) (h2 : qle ρl (qadd qone qone)) (c : CosCert ρl lo hi)
    (hlo : qlt qzero lo) : ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) := by
  obtain ⟨B, hB⟩ := pos_floor hlo
  obtain ⟨Nc, hNc⟩ := cert_cos c
  obtain ⟨N0, hN0⟩ := rho_facts
  obtain ⟨Nk, hNk⟩ := K4_small (B + 1)
  refine ⟨Nc + (N0 + (Nk + 5)), fun n hn => ?_⟩
  obtain ⟨c1, _⟩ := hNc n (le_l' hn)
  obtain ⟨r1, r2, _, r4⟩ := hN0 n (le_l' (le_r' hn))
  have kk := hNk n (le_l' (le_r' (le_r' hn)))
  have n5 : 5 ≤ n := le_r' (le_r' (le_r' hn))
  cases qle_total ρl (qadd (rho n) (qeps n)) with
  | inl h => exact h
  | inr h =>
      have g0 : qle qzero (qadd (rho n) (qeps n)) := by have := qeps_nonneg n; have := qle_of_qlt qone_pos; rat_linarith
      have cm := cos_mono g0 h h2 n5
      have e := qeps_succ_add B
      have p := qeps_nonneg (B + 1)
      have : qle qzero (Cn (qadd (rho n) (qeps n)) n) := by
        generalize Cn (qadd (rho n) (qeps n)) n = Cg at *; generalize Cn ρl n = Cl at *; generalize K4 n = K at *
        clear r4 hN0 hNc hNk
        unfold qsub at *; rat_linarith
      exact absurd this r4

/-- A CERTIFIED `cos ρh < 0` stops the run before `ρh`: from some index on, `ρ_n ≤ ρh`. -/
theorem rho_le {ρh lo hi : QExpr} (h0 : qle qzero ρh) (c : CosCert ρh lo hi) (hhi : qlt hi qzero) :
    ∃ N, ∀ n, N ≤ n → qle (rho n) ρh := by
  have nh := (qlt_iff_le_not_le.mp hhi).2
  have l1 : qle hi qzero := (qlt_iff_le_not_le.mp hhi).1
  have p1 : qle qzero (qneg hi) := by rat_linarith
  have p2 : ¬ qle (qneg hi) qzero := fun h => nh (by have h' : qle (qneg hi) qzero := h; rat_linarith)
  obtain ⟨B, hB⟩ := pos_floor (x := qneg hi) (qlt_iff_le_not_le.mpr ⟨p1, p2⟩)
  obtain ⟨Nc, hNc⟩ := cert_cos c
  obtain ⟨N0, hN0⟩ := rho_facts
  obtain ⟨Nk, hNk⟩ := K4_small (B + 1)
  refine ⟨Nc + (N0 + (Nk + 5)), fun n hn => ?_⟩
  obtain ⟨_, c2⟩ := hNc n (le_l' hn)
  obtain ⟨_, r2, r3, _⟩ := hN0 n (le_l' (le_r' hn))
  have kk := hNk n (le_l' (le_r' (le_r' hn)))
  have n5 : 5 ≤ n := le_r' (le_r' (le_r' hn))
  cases qle_total (rho n) ρh with
  | inl h => exact h
  | inr h =>
      have g2 : qle (rho n) (qadd qone qone) := by have := qeps_nonneg n; rat_linarith
      have cm := cos_mono h0 h g2 n5
      have e := qeps_succ_add B
      have bad : qle (qeps (B + 1)) qzero := by
        generalize Cn (rho n) n = Cr at *; generalize Cn ρh n = Ch at *; generalize K4 n = K at *
        clear hN0 hNc hNk
        unfold qsub at *; rat_linarith
      exact absurd bad (qlt_iff_le_not_le.mp (qeps_pos (B + 1))).2

/-- Both sides of the bracket at once: `ρl ≤ ρ_n + 2^−n` and `ρ_n ≤ ρh`, eventually. -/
theorem rho_br {ρl ρh l1 h1 l2 h2 : QExpr} (a0 : qle qzero ρl) (a2 : qle ρl (qadd qone qone)) (cl : CosCert ρl l1 h1)
    (pl : qlt qzero l1) (b0 : qle qzero ρh) (ch : CosCert ρh l2 h2) (ph : qlt h2 qzero) :
    ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) ∧ qle (rho n) ρh := by
  obtain ⟨N1, g1⟩ := rho_ge a0 a2 cl pl
  obtain ⟨N2, g2⟩ := rho_le b0 ch ph
  exact ⟨N1 + N2, fun n hn => ⟨g1 n (le_l' hn), g2 n (le_r' hn)⟩⟩

/-- `|cos| ≤ 1`, uniformly to every precision: Pythagoras at the index, `C² ≤ C² + S² ≈ 1`. -/
theorem cos_abs_unif {A : QExpr} (hA : qle qzero A) (k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ x, Ab x A →
    Ab (Cn x n) (qadd qone (qeps k)) := by
  obtain ⟨N0, hN0⟩ := corner_small hA hA (k + 1)
  refine ⟨N0 + 1, fun n hn x hx => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_succ_le_zero _)
  | succ m =>
    obtain ⟨p1, _⟩ := pyth hx m
    have cs := hN0 (m + 1) (le_l' hn)
    have e := qeps_succ_add k
    have s2 := qmul_self_nonneg (Sn x (m + 1))
    have cc : qle (qmul (Cn x (m + 1)) (Cn x (m + 1))) (qadd qone (qeps k)) := by
      generalize corner (tm A) (tm A) (m + 1) = K at *
      generalize qmul (Sn x (m + 1)) (Sn x (m + 1)) = SS at *
      generalize qmul (Cn x (m + 1)) (Cn x (m + 1)) = CC at *
      clear hN0; unfold qsub at *; rat_linarith
    have ep := qeps_nonneg k
    have o := qle_of_qlt qone_pos
    have nn : qEq (qmul (qneg (Cn x (m + 1))) (qneg (Cn x (m + 1)))) (qmul (Cn x (m + 1)) (Cn x (m + 1))) := by rat_ring
    have m1 : qEq (qmul (Cn x (m + 1)) qone) (Cn x (m + 1)) := by rat_ring
    have m2 : qEq (qmul (qneg (Cn x (m + 1))) qone) (qneg (Cn x (m + 1))) := by rat_ring
    constructor
    · cases qle_total (qneg qone) (Cn x (m + 1)) with
      | inl h => rat_linarith
      | inr h =>
        have sc := scale_l (show qle qone (qneg (Cn x (m + 1))) by rat_linarith) (show qle qzero (qneg (Cn x (m + 1))) by rat_linarith)
        generalize qmul (Cn x (m + 1)) (Cn x (m + 1)) = CC at *
        generalize qmul (qneg (Cn x (m + 1))) (qneg (Cn x (m + 1))) = NN at *
        generalize qmul (qneg (Cn x (m + 1))) qone = N1 at *
        generalize Cn x (m + 1) = C at *
        clear hN0 cs p1 s2 hx; rat_linarith
    · cases qle_total (Cn x (m + 1)) qone with
      | inl h => rat_linarith
      | inr h =>
        have sc := scale_l h (show qle qzero (Cn x (m + 1)) by rat_linarith)
        generalize qmul (Cn x (m + 1)) (Cn x (m + 1)) = CC at *
        generalize qmul (Cn x (m + 1)) qone = C1 at *
        generalize Cn x (m + 1) = C at *
        clear hN0 cs p1 s2 hx nn m2; rat_linarith

/-- Whole periods both ways, by forward shifts only: `z + q·4ρ = z' + p·4ρ` ⇒ `C_n(z) ≈ C_n(z')`. -/
theorem period_pq {A : QExpr} (hA : qle qzero A) (p q k : Nat) : ∃ N, ∀ n, N ≤ n → ∀ z z', Ab z A → Ab z' A →
    qEq (qadd z (qmul (qnat q) (four n))) (qadd z' (qmul (qnat p) (four n))) →
    Ab (qsub (Cn z n) (Cn z' n)) (qeps k) := by
  obtain ⟨Nq, hq⟩ := period_unif hA q (k + 1)
  obtain ⟨Np, hp⟩ := period_unif hA p (k + 1)
  refine ⟨Nq + Np, fun n hn z z' hz hz' e => ?_⟩
  obtain ⟨a1, a2⟩ := hq n (le_l' hn) z hz
  obtain ⟨b1, b2⟩ := hp n (le_r' hn) z' hz'
  have c := Cn_respects e n
  have ee := qeps_succ_add k
  generalize Cn (qadd z (qmul (qnat q) (four n))) n = Zq at *
  generalize Cn (qadd z' (qmul (qnat p) (four n))) n = Zp at *
  generalize Cn z n = Cz at *; generalize Cn z' n = Cz' at *
  clear hq hp; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

theorem qeps_le_one (j : Nat) : qle (qeps j) qone := by
  have h := qeps_le_add 0 j; rw [Nat.zero_add] at h; exact h

/-- A reading slightly outside `[lu, hu]` has a point of `[lu, hu]` within the same tolerance. -/
theorem clamp {z lu hu e : QExpr} (h1 : qle (qsub lu e) z) (h2 : qle z (qadd hu e)) (hlh : qle lu hu)
    (e0 : qle qzero e) : ∃ y, qle lu y ∧ qle y hu ∧ Ab (qsub z y) e := by
  cases qle_total z lu with
  | inl h => exact ⟨lu, qle_refl _, hlh, by unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩
  | inr h =>
    cases qle_total z hu with
    | inl h' => exact ⟨z, h, h', by unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩
    | inr h' => exact ⟨hu, hlh, qle_refl _, by unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩⟩

/-- The Lipschitz bound `e·S`, with `S ≤ 2^B` and `e = ε_{k+B}`, is within `ε_k`. -/
theorem lip_eps {D S H : QExpr} {B k : Nat} (hD : Ab D (qmul (qeps (k + B)) S)) (hS : qle S H)
    (hH : qle H (qofInt (pow2 B))) : Ab D (qeps k) := by
  have sc := scale_l (qle_trans hS hH) (qeps_nonneg (k + B))
  have e := qpow2_mul_eps B k
  have c := qmul_comm (qofInt (pow2 B)) (qeps (k + B))
  obtain ⟨d1, d2⟩ := hD
  generalize qmul (qeps (k + B)) S = T at *
  generalize qmul (qeps (k + B)) (qofInt (pow2 B)) = U at *
  generalize qmul (qofInt (pow2 B)) (qeps (k + B)) = U' at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- The shift that brings a window into the base period: `d_n = q·4ρ_n − p·4ρ_n`. -/
def dd (p q n : Nat) : QExpr := qsub (qmul (qnat q) (four n)) (qmul (qnat p) (four n))

theorem dd_bound {w M : QExpr} {p q n : Nat} (hw : Ab w (qadd M qone)) (r0 : qle qzero (rho n))
    (r2 : qle (rho n) (qadd qone qone)) :
    Ab (qadd w (dd p q n)) (qadd (qadd M qone) (qadd (qmul (qnat q) eight) (qmul (qnat p) eight))) := by
  obtain ⟨f0, f8⟩ := four_facts r0 r2
  have a1 := scale_l f8 (qnat_nonneg q); have a2 := scale_l f8 (qnat_nonneg p)
  have b1 := qmul_nonneg (qnat_nonneg q) f0; have b2 := qmul_nonneg (qnat_nonneg p) f0
  obtain ⟨w1, w2⟩ := hw
  unfold dd
  generalize qmul (qnat q) (four n) = Q4 at *; generalize qmul (qnat p) (four n) = P4 at *
  generalize qmul (qnat q) eight = Q8 at *; generalize qmul (qnat p) eight = P8 at *
  unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩

/-- THE TRANSPORT: a reading near `[lu, hu]` has a point `y` there whose shift by whole periods carries `cos`
within `ε_k` — the reading's own value, and both ends'. -/
theorem near_shift {x : Nat → QExpr} {lu hu : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu) (p q k : Nat) :
    ∃ N, ∀ n, N ≤ n → ∃ y, qle lu y ∧ qle y hu ∧
      Ab (qsub (Cn (x n) n) (Cn (qadd y (dd p q n)) n)) (qeps k) ∧
      Ab (qsub (Cn lu n) (Cn (qadd lu (dd p q n)) n)) (qeps k) ∧
      Ab (qsub (Cn hu n) (Cn (qadd hu (dd p q n)) n)) (qeps k) := by
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
  obtain ⟨Np, hp⟩ := period_pq hA p q (k + 1)
  obtain ⟨Nq, hq⟩ := period_pq hA p q k
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
  have L := (CS_lip aX (wid y aY) yz n).1
  have L' := lip_eps (k := k + 1) L (hH n) hC
  have P := hp n (le_l' (le_r' (le_r' hn))) y _ (wid y aY) (sh y aY) (eq y)
  have ee := qeps_succ_add k
  refine ⟨y, y1, y2, ?_, hq n (le_r' (le_r' (le_r' hn))) lu _ (wid lu aL) (sh lu aL) (eq lu),
    hq n (le_r' (le_r' (le_r' hn))) hu _ (wid hu aH) (sh hu aH) (eq hu)⟩
  obtain ⟨l1, l2⟩ := L'; obtain ⟨p1, p2⟩ := P
  generalize Cn (x n) n = Cx at *; generalize Cn y n = Cy at *; generalize Cn (qadd y (dd p q n)) n = Cs at *
  clear hp hq hR h1 hH; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- `cos` of a reading near `[lu, hu]` stays below the ends' certified tops, once the window — shifted by whole
periods — lies in `[0, 4ρ]`, where no maximum is inside. -/
theorem cos_up {x : Nat → QExpr} {lu hu l1 h1 l2 h2 h : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu)
    (c1 : CosCert lu l1 h1) (c2 : CosCert hu l2 h2) (b1 : qle h1 h) (b2 : qle h2 h) (p q : Nat)
    (win : ∃ N, ∀ n, N ≤ n → qle qzero (qadd lu (dd p q n)) ∧ qle (qadd hu (dd p q n)) (four n)) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (Cn (x n) n) (qadd h (qeps k)) := by
  intro k
  obtain ⟨N1, hN1⟩ := near_shift hx hlh p q (k + 2)
  obtain ⟨N2, hN2⟩ := cos_win_up (k + 2)
  obtain ⟨M1, e1⟩ := cert_cos c1
  obtain ⟨M2, e2⟩ := cert_cos c2
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
    generalize Cn (qadd y (dd p q n)) n = Cy at *; generalize Cn (qadd lu (dd p q n)) n = Cl at *
    generalize Cn (x n) n = Cx at *; generalize Cn lu n = C0 at *
    clear hN1 hN2 e1 e2 hW c2 g2 u1; unfold qsub at *; rat_linarith
  | inr c =>
    generalize Cn (qadd y (dd p q n)) n = Cy at *; generalize Cn (qadd hu (dd p q n)) n = Ch at *
    generalize Cn (x n) n = Cx at *; generalize Cn hu n = C0 at *
    clear hN1 hN2 e1 e2 hW c1 g1 l1'; unfold qsub at *; rat_linarith

/-- `cos` of a reading near `[lu, hu]` stays above the ends' certified bottoms, once the window — shifted by
whole periods — lies in `[−2ρ, 2ρ]`, where no minimum is inside. -/
theorem cos_lo {x : Nat → QExpr} {lu hu l1 h1 l2 h2 l : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu)
    (c1 : CosCert lu l1 h1) (c2 : CosCert hu l2 h2) (b1 : qle l l1) (b2 : qle l l2) (p q : Nat)
    (win : ∃ N, ∀ n, N ≤ n → qle (qneg (qadd (rho n) (rho n))) (qadd lu (dd p q n)) ∧
      qle (qadd hu (dd p q n)) (qadd (rho n) (rho n))) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub l (qeps k)) (Cn (x n) n) := by
  intro k
  obtain ⟨N1, hN1⟩ := near_shift hx hlh p q (k + 2)
  obtain ⟨N2, hN2⟩ := cos_win_lo (k + 2)
  obtain ⟨M1, e1⟩ := cert_cos c1
  obtain ⟨M2, e2⟩ := cert_cos c2
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
    generalize Cn (qadd y (dd p q n)) n = Cy at *; generalize Cn (qadd lu (dd p q n)) n = Cl at *
    generalize Cn (x n) n = Cx at *; generalize Cn lu n = C0 at *
    clear hN1 hN2 e1 e2 hW c2 g2 u2; unfold qsub at *; rat_linarith
  | inr c =>
    generalize Cn (qadd y (dd p q n)) n = Cy at *; generalize Cn (qadd hu (dd p q n)) n = Ch at *
    generalize Cn (x n) n = Cx at *; generalize Cn hu n = C0 at *
    clear hN1 hN2 e1 e2 hW c1 g1 l2'; unfold qsub at *; rat_linarith

def f4 (x : QExpr) : QExpr := qadd (qadd x x) (qadd x x)

/-- Whole multiples of the bracket: `c·ρl − ε_B ≤ c·ρ_n ≤ c·ρh`, eventually. -/
theorem mult_rho {ρl ρh : QExpr} (hρ : ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) ∧ qle (rho n) ρh)
    (c B : Nat) : ∃ N, ∀ n, N ≤ n →
      qle (qsub (qmul (qnat c) ρl) (qeps B)) (qmul (qnat c) (rho n)) ∧ qle (qmul (qnat c) (rho n)) (qmul (qnat c) ρh) := by
  obtain ⟨N0, h0⟩ := hρ
  obtain ⟨C, hC1, _⟩ := qexpr_bound (qnat c)
  have hC : qle (qnat c) (qofInt (pow2 C)) := by unfold qsub at hC1; rat_linarith
  refine ⟨N0 + (B + C), fun n hn => ?_⟩
  obtain ⟨r1, r2⟩ := h0 n (le_l' hn)
  have en : qle (qeps n) (qeps (B + C)) := eps_anti (le_r' hn)
  have c0 := qnat_nonneg c
  have s1 := scale_l r1 c0
  have s2 := scale_l en c0
  have s3 := scale_l hC (qeps_nonneg (B + C))
  have e := qpow2_mul_eps C B
  have d : qEq (qmul (qnat c) (qadd (rho n) (qeps n))) (qadd (qmul (qnat c) (rho n)) (qmul (qnat c) (qeps n))) := by rat_ring
  have m1 := qmul_comm (qeps (B + C)) (qnat c)
  have m2 := qmul_comm (qeps (B + C)) (qofInt (pow2 C))
  refine ⟨?_, scale_l r2 c0⟩
  generalize qmul (qnat c) (qadd (rho n) (qeps n)) = A at *
  generalize qmul (qnat c) (rho n) = X at *; generalize qmul (qnat c) (qeps n) = Y at *
  generalize qmul (qnat c) (qeps (B + C)) = Z at *; generalize qmul (qeps (B + C)) (qnat c) = Z' at *
  generalize qmul (qeps (B + C)) (qofInt (pow2 C)) = W at *; generalize qmul (qofInt (pow2 C)) (qeps (B + C)) = W' at *
  generalize qmul (qnat c) ρl = L at *
  clear h0; unfold qsub; rat_linarith

theorem dd_f4 (p q n : Nat) :
    qEq (dd p q n) (qsub (f4 (qmul (qnat q) (rho n))) (f4 (qmul (qnat p) (rho n)))) ∧ qEq (four n) (f4 (rho n)) := by
  unfold dd four f4 qsub; exact ⟨by rat_ring, by rat_ring⟩

/-- The kernel's "no maximum inside", checked in rationals against `π`'s bracket: the window, shifted, lies in
`[0, 4ρ]` from some index on. -/
theorem win_up_of {ρl ρh lu hu : QExpr} (hρ : ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) ∧ qle (rho n) ρh)
    (p q B : Nat)
    (U1 : qle (qadd (f4 (qmul (qnat p) ρh)) (f4 (qeps B))) (qadd lu (f4 (qmul (qnat q) ρl))))
    (U2 : qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (f4 (qadd (qeps B) (qeps B)))) (qadd (f4 (qmul (qnat p) ρl)) (f4 ρl))) :
    ∃ N, ∀ n, N ≤ n → qle qzero (qadd lu (dd p q n)) ∧ qle (qadd hu (dd p q n)) (four n) := by
  obtain ⟨Nq, hq⟩ := mult_rho hρ q B
  obtain ⟨Np, hp⟩ := mult_rho hρ p B
  obtain ⟨N0, h0⟩ := hρ
  refine ⟨Nq + (Np + (N0 + B)), fun n hn => ?_⟩
  obtain ⟨q1, q2⟩ := hq n (le_l' hn)
  obtain ⟨p1, p2⟩ := hp n (le_l' (le_r' hn))
  obtain ⟨r1, _⟩ := h0 n (le_l' (le_r' (le_r' hn)))
  have en : qle (qeps n) (qeps B) := eps_anti (le_r' (le_r' (le_r' hn)))
  obtain ⟨d1, d2⟩ := dd_f4 p q n
  generalize dd p q n = D at *; generalize four n = F at *
  generalize qmul (qnat q) (rho n) = Xq at *; generalize qmul (qnat p) (rho n) = Xp at *
  generalize qmul (qnat q) ρl = Ql at *; generalize qmul (qnat q) ρh = Qh at *
  generalize qmul (qnat p) ρl = Pl at *; generalize qmul (qnat p) ρh = Ph at *
  clear hq hp h0; unfold f4 qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The kernel's "no minimum inside": the window, shifted, lies in `[−2ρ, 2ρ]` from some index on. -/
theorem win_lo_of {ρl ρh lu hu : QExpr} (hρ : ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) ∧ qle (rho n) ρh)
    (p q B : Nat)
    (L1 : qle (qadd (f4 (qmul (qnat p) ρh)) (qadd (f4 (qeps B)) (qadd (qeps B) (qeps B))))
      (qadd (qadd lu (f4 (qmul (qnat q) ρl))) (qadd ρl ρl)))
    (L2 : qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (qadd (f4 (qeps B)) (qadd (qeps B) (qeps B))))
      (qadd (f4 (qmul (qnat p) ρl)) (qadd ρl ρl))) :
    ∃ N, ∀ n, N ≤ n → qle (qneg (qadd (rho n) (rho n))) (qadd lu (dd p q n)) ∧
      qle (qadd hu (dd p q n)) (qadd (rho n) (rho n)) := by
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
  clear hq hp h0; unfold f4 qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- A reading eventually in `[lu, hu]` is eventually within a fixed bound. -/
theorem ev_bound {x : Nat → QExpr} {lu hu : QExpr} (hx : Ev x lu hu) :
    ∃ A, qle qzero A ∧ ∃ N, ∀ n, N ≤ n → Ab (x n) A := by
  obtain ⟨M, _, hM0, _, ml, mh, _, _⟩ := bound4 lu hu lu hu
  obtain ⟨N, hN⟩ := hx 0
  have o := qle_of_qlt qone_pos
  refine ⟨qadd M qone, by rat_linarith, N, fun n hn => ?_⟩
  obtain ⟨x1, x2⟩ := hN n hn
  have z := qeps_zero
  obtain ⟨m1, m2⟩ := ml; obtain ⟨m3, m4⟩ := mh
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- The kernel's `±1` (an extremum may be inside): `|cos| ≤ 1`. -/
theorem cos_pm1 {x : Nat → QExpr} {lu hu : QExpr} (hx : Ev x lu hu) (k : Nat) :
    ∃ N, ∀ n, N ≤ n → Ab (Cn (x n) n) (qadd qone (qeps k)) := by
  obtain ⟨A, hA, N0, hN0⟩ := ev_bound hx
  obtain ⟨N1, hN1⟩ := cos_abs_unif hA k
  exact ⟨N0 + N1, fun n hn => hN1 n (le_r' hn) _ (hN0 n (le_l' hn))⟩

/-- Two one-sided readings make one. -/
theorem Ev_of_sides {y : Nat → QExpr} {l h : QExpr}
    (lo : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub l (qeps k)) (y n))
    (hi : ∀ k, ∃ N, ∀ n, N ≤ n → qle (y n) (qadd h (qeps k))) : Ev y l h := fun k => by
  obtain ⟨N1, h1⟩ := lo k; obtain ⟨N2, h2⟩ := hi k
  exact ⟨N1 + N2, fun n hn => ⟨h1 n (le_l' hn), h2 n (le_r' hn)⟩⟩

/-- `π`'s bracket, certified by `cos` at its halves: `cos ρl > 0`, `cos ρh < 0` (`π = 2ρ`). -/
def PiBr (ρl ρh : QExpr) : Prop :=
  qle qzero ρl ∧ qle ρl (qadd qone qone) ∧ qle qzero ρh ∧
  (∃ a b, CosCert ρl a b ∧ qlt qzero a) ∧ (∃ a b, CosCert ρh a b ∧ qlt b qzero)

theorem PiBr.ev {ρl ρh : QExpr} (h : PiBr ρl ρh) :
    ∃ N, ∀ n, N ≤ n → qle ρl (qadd (rho n) (qeps n)) ∧ qle (rho n) ρh := by
  obtain ⟨a0, a2, b0, ⟨_, _, c1, p1⟩, ⟨_, _, c2, p2⟩⟩ := h
  exact rho_br a0 a2 c1 p1 b0 c2 p2

/-- The kernel's top of `cos` over `[lu, hu]`: `1`, or the larger certified end when no maximum can be inside. -/
def CosHi (lu hu h : QExpr) : Prop :=
  qle qone h ∨ ∃ ρl ρh, PiBr ρl ρh ∧ (∃ l1 h1, CosCert lu l1 h1 ∧ qle h1 h) ∧ (∃ l2 h2, CosCert hu l2 h2 ∧ qle h2 h) ∧
    ∃ p q B, qle (qadd (f4 (qmul (qnat p) ρh)) (f4 (qeps B))) (qadd lu (f4 (qmul (qnat q) ρl))) ∧
      qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (f4 (qadd (qeps B) (qeps B)))) (qadd (f4 (qmul (qnat p) ρl)) (f4 ρl))

/-- The kernel's bottom: `−1`, or the smaller certified end when no minimum can be inside. -/
def CosLo (lu hu l : QExpr) : Prop :=
  qle l (qneg qone) ∨ ∃ ρl ρh, PiBr ρl ρh ∧ (∃ l1 h1, CosCert lu l1 h1 ∧ qle l l1) ∧ (∃ l2 h2, CosCert hu l2 h2 ∧ qle l l2) ∧
    ∃ p q B, qle (qadd (f4 (qmul (qnat p) ρh)) (qadd (f4 (qeps B)) (qadd (qeps B) (qeps B))))
        (qadd (qadd lu (f4 (qmul (qnat q) ρl))) (qadd ρl ρl)) ∧
      qle (qadd (qadd hu (f4 (qmul (qnat q) ρh))) (qadd (f4 (qeps B)) (qadd (qeps B) (qeps B))))
        (qadd (f4 (qmul (qnat p) ρl)) (qadd ρl ρl))

/-- THE KERNEL'S `cos` OVER AN INTERVAL IS SOUND (`zfunc.iv_cos`): a reading eventually in `[lu, hu]` has its
`cos` eventually in `[l, h]`, to every precision. -/
theorem Ev_cos {x : Nat → QExpr} {lu hu l h : QExpr} (hx : Ev x lu hu) (hlh : qle lu hu)
    (hi : CosHi lu hu h) (lo : CosLo lu hu l) : Ev (fun n => Cn (x n) n) l h := by
  refine Ev_of_sides ?_ ?_
  · cases lo with
    | inl h1 => intro k; obtain ⟨N, hN⟩ := cos_pm1 hx k; exact ⟨N, fun n hn => by
        obtain ⟨a, _⟩ := hN n hn; unfold qsub; rat_linarith⟩
    | inr h1 =>
      obtain ⟨ρl, ρh, br, ⟨l1, h1', c1, b1⟩, ⟨l2, h2', c2, b2⟩, p, q, B, L1, L2⟩ := h1
      exact cos_lo hx hlh c1 c2 b1 b2 p q (win_lo_of br.ev p q B L1 L2)
  · cases hi with
    | inl h1 => intro k; obtain ⟨N, hN⟩ := cos_pm1 hx k; exact ⟨N, fun n hn => by
        obtain ⟨_, a⟩ := hN n hn; rat_linarith⟩
    | inr h1 =>
      obtain ⟨ρl, ρh, br, ⟨l1, h1', c1, b1⟩, ⟨l2, h2', c2, b2⟩, p, q, B, U1, U2⟩ := h1
      exact cos_up hx hlh c1 c2 b1 b2 p q (win_up_of br.ev p q B U1 U2)

end ZTrig

#print axioms ZTrig.cert_cos
#print axioms ZTrig.rho_ge
#print axioms ZTrig.rho_le
#print axioms ZTrig.rho_br
#print axioms ZTrig.cos_abs_unif
#print axioms ZTrig.period_pq
#print axioms ZTrig.clamp
#print axioms ZTrig.lip_eps
#print axioms ZTrig.near_shift
#print axioms ZTrig.cos_up
#print axioms ZTrig.cos_lo
#print axioms ZTrig.mult_rho
#print axioms ZTrig.win_up_of
#print axioms ZTrig.win_lo_of
#print axioms ZTrig.cos_pm1
#print axioms ZTrig.Ev_of_sides
#print axioms ZTrig.Ev_cos
