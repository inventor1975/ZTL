import ZRangePin

/-!
# ZLimits — integrals whose limits move with the data (`zintegral.check_limits`, `check_limits_range`). Zero axioms.

`I(p) = ∫_{A(p)}^{B(p)} f(x, p) dx`, the limits `A`, `B` reader nodes. The kernel reads `A` in `[a_lo, a_hi]`, `B` in
`[b_lo, b_hi]` (`a_hi ≤ b_lo`), splits `I = ∫_{a_hi}^{b_lo} f + ∫_A^{a_hi} f + ∫_{b_lo}^B f`, encloses the core by an
ordinary certificate and each tail by `hull{0, w·f}`, `w` the limit's spread, `f` read over the spread × the box.

C1, THE TAIL RULE (`tail_rule`, `limits_enclosure`): for EVERY rational end `a' ∈ [a_lo, a_hi]` (and `b'`), every
tagged sum over `[a', a_hi]` lies in the tail's hull, so every sum over `[a', a_hi] ∪ core ∪ [b_lo, b']` whose core
part is enclosed (by the core's leaves) lies in the kernel's `[L, U]` up to `ε`. The limit `A(p)` itself is an
operational real inside `[a_lo, a_hi]`; the claim holds for each rational end it admits (no real-ended integral is
formed here).
-/

namespace ZLimits

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZIntegral ZIntegralR

/-- `flo·W ≥ Tl` for `W ∈ [0, w]`, `Tl ≤ 0`, `Tl ≤ w·flo` (the hull's lower end). -/
theorem hull_lo {flo W w Tl : QExpr} (W0 : qle qzero W) (Ww : qle W w) (h1 : qle Tl qzero) (h2 : qle Tl (qmul w flo)) :
    qle Tl (qmul flo W) := by
  cases qle_total qzero flo with
  | inl hf => have := qmul_nonneg hf W0; rat_linarith
  | inr hf =>
      have s := scale_l Ww (by rat_linarith : qle qzero (qneg flo))
      have e1 : qEq (qmul (qneg flo) W) (qneg (qmul flo W)) := by rat_ring
      have e2 : qEq (qmul (qneg flo) w) (qneg (qmul w flo)) := by rat_ring
      generalize qmul (qneg flo) W = X at *; generalize qmul (qneg flo) w = Y at *
      rat_linarith

theorem hull_hi {fhi W w Th : QExpr} (W0 : qle qzero W) (Ww : qle W w) (h1 : qle qzero Th) (h2 : qle (qmul w fhi) Th) :
    qle (qmul fhi W) Th := by
  cases qle_total qzero fhi with
  | inl hf =>
      have s := scale_l Ww hf
      have c := qmul_comm w fhi
      rat_linarith
  | inr hf =>
      have := qmul_nonneg (by rat_linarith : qle qzero (qneg fhi)) W0
      have e : qEq (qmul (qneg fhi) W) (qneg (qmul fhi W)) := by rat_ring
      rat_linarith

/-- THE TAIL RULE: a tagged sum over `[s, t] ⊆ [lo, hi]` of `f` read in `[flo, fhi]` there lies in
`[Tl, Th] ⊇ hull{0, (hi − lo)·[flo, fhi]}`, up to `ε_k·(hi − lo)`. -/
theorem tail_rule {e : G} {p : Point QExpr} {i : Nat} {lo hi s t flo fhi Tl Th : QExpr}
    (h1 : qle lo s) (h2 : qle s t) (h3 : qle t hi) (hf : LeafEv e p i lo hi flo fhi)
    {fine : List (QExpr × QExpr)} (hw : ∀ wt, List.Mem wt fine → qle qzero wt.1 ∧ qle s wt.2 ∧ qle wt.2 t)
    (hW : qEq (wtotal qSum fine) (qsub t s))
    (hTl : qle Tl qzero) (hTl2 : qle Tl (qmul (qsub hi lo) flo))
    (hTh : qle qzero Th) (hTh2 : qle (qmul (qsub hi lo) fhi) Th) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub Tl (qmul (qeps k) (qsub hi lo))) (rsum qSum (fun x => evalN n (upd p i x) e) fine) ∧
      qle (rsum qSum (fun x => evalN n (upd p i x) e) fine) (qadd Th (qmul (qeps k) (qsub hi lo))) := by
  intro k
  obtain ⟨N, hN⟩ := ev_list (fun (wt : QExpr × QExpr) n =>
      qle (qsub flo (qeps k)) (evalN n (upd p i wt.2) e) ∧ qle (evalN n (upd p i wt.2) e) (qadd fhi (qeps k))) fine
    (fun wt hm => by
      obtain ⟨_, a, b⟩ := hw wt hm
      exact hf wt.2 (qle_trans h1 a) (qle_trans b h3) k)
  refine ⟨N, fun n hn => ?_⟩
  have W0 : qle qzero (qsub t s) := by unfold qsub; rat_linarith
  have Ww : qle (qsub t s) (qsub hi lo) := by unfold qsub; rat_linarith
  have lo' := piece_lower qSum (fun x => evalN n (upd p i x) e) (qsub flo (qeps k)) fine
    (fun wt hm => ⟨(hw wt hm).1, (hN n hn wt hm).1⟩)
  have hi' := piece_upper qSum (fun x => evalN n (upd p i x) e) (qadd fhi (qeps k)) fine
    (fun wt hm => ⟨(hw wt hm).1, (hN n hn wt hm).2⟩)
  have lo2 : qle (qmul (qsub flo (qeps k)) (wtotal qSum fine)) (rsum qSum (fun x => evalN n (upd p i x) e) fine) := lo'
  have hi2 : qle (rsum qSum (fun x => evalN n (upd p i x) e) fine) (qmul (qadd fhi (qeps k)) (wtotal qSum fine)) := hi'
  clear lo' hi'
  have m1 := qmul_respects (qEq_refl (qsub flo (qeps k))) hW
  have m2 := qmul_respects (qEq_refl (qadd fhi (qeps k))) hW
  have hl := hull_lo W0 Ww hTl hTl2
  have hh := hull_hi W0 Ww hTh hTh2
  have ew := scale_l Ww (qeps_nonneg k)
  have e1 : qEq (qmul (qsub flo (qeps k)) (qsub t s)) (qsub (qmul flo (qsub t s)) (qmul (qeps k) (qsub t s))) := by
    unfold qsub; rat_ring
  have e2 : qEq (qmul (qadd fhi (qeps k)) (qsub t s)) (qadd (qmul fhi (qsub t s)) (qmul (qeps k) (qsub t s))) := by
    rat_ring
  show qle (qsub Tl (qmul (qeps k) (qsub hi lo))) (rsum qSum (fun x => evalN n (upd p i x) e) fine) ∧
    qle (rsum qSum (fun x => evalN n (upd p i x) e) fine) (qadd Th (qmul (qeps k) (qsub hi lo)))
  generalize rsum qSum (fun x => evalN n (upd p i x) e) fine = R at *
  generalize wtotal qSum fine = Wt at *
  generalize qmul (qsub flo (qeps k)) Wt = A1 at *
  generalize qmul (qadd fhi (qeps k)) Wt = A2 at *
  generalize qmul (qsub flo (qeps k)) (qsub t s) = B1 at *
  generalize qmul (qadd fhi (qeps k)) (qsub t s) = B2 at *
  generalize qmul flo (qsub t s) = C1 at *
  generalize qmul fhi (qsub t s) = C2 at *
  generalize qmul (qeps k) (qsub t s) = D1 at *
  generalize qmul (qeps k) (qsub hi lo) = D2 at *
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

/-- C1 ASSEMBLED: a sum = tail A + core + tail B, the core enclosed in `[Cl, Ch]` (by its leaves), each tail by the
tail rule: the whole in `[Cl + Tal + Tbl, Ch + Tah + Tbh]` up to `ε`. -/
theorem limits_enclosure {SA Sc SB : Nat → QExpr} {Cl Ch Tal Tah Tbl Tbh wa wb : QExpr}
    (hA : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub Tal (qmul (qeps k) wa)) (SA n) ∧ qle (SA n) (qadd Tah (qmul (qeps k) wa)))
    (hB : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub Tbl (qmul (qeps k) wb)) (SB n) ∧ qle (SB n) (qadd Tbh (qmul (qeps k) wb)))
    (hC : ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub Cl (qeps k)) (Sc n) ∧ qle (Sc n) (qadd Ch (qeps k)))
    (wa0 : qle qzero wa) (wb0 : qle qzero wb) :
    Ev (fun n => qadd (qadd (SA n) (Sc n)) (SB n)) (qadd (qadd Tal Cl) Tbl) (qadd (qadd Tah Ch) Tbh) := by
  intro k
  obtain ⟨Ba, hBa⟩ := ZAtan.eps_scaledA wa0
  obtain ⟨Bb, hBb⟩ := ZAtan.eps_scaledA wb0
  obtain ⟨N1, h1⟩ := hA (k + 2 + Ba)
  obtain ⟨N2, h2⟩ := hB (k + 2 + Bb)
  obtain ⟨N3, h3⟩ := hC (k + 2)
  refine ⟨N1 + (N2 + N3), fun n hn => ?_⟩
  obtain ⟨a1, a2⟩ := h1 n (Nat.le_trans (Nat.le_add_right _ _) hn)
  obtain ⟨b1, b2⟩ := h2 n (Nat.le_trans (Nat.le_trans (Nat.le_add_right N2 N3) (Nat.le_add_left _ N1)) hn)
  obtain ⟨c1, c2⟩ := h3 n (Nat.le_trans (Nat.le_trans (Nat.le_add_left N3 N2) (Nat.le_add_left _ N1)) hn)
  have ea := hBa (k + 2); have eb := hBb (k + 2)
  have ca := qmul_comm (qeps (k + 2 + Ba)) wa; have cb := qmul_comm (qeps (k + 2 + Bb)) wb
  have s1 := qeps_succ_add k; have s2 := qeps_succ_add (k + 1)
  have z := qeps_nonneg (k + 2)
  -- each part within ε_{k+2} of its interval
  have pa : qle (qsub Tal (qeps (k + 2))) (SA n) ∧ qle (SA n) (qadd Tah (qeps (k + 2))) := by
    generalize qmul (qeps (k + 2 + Ba)) wa = X1 at *; generalize qmul wa (qeps (k + 2 + Ba)) = Y1 at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  have pb : qle (qsub Tbl (qeps (k + 2))) (SB n) ∧ qle (SB n) (qadd Tbh (qeps (k + 2))) := by
    generalize qmul (qeps (k + 2 + Bb)) wb = X2 at *; generalize qmul wb (qeps (k + 2 + Bb)) = Y2 at *
    unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩
  clear a1 a2 b1 b2 ea eb ca cb h1 h2 h3 hA hB hC hBa hBb
  show qle (qsub (qadd (qadd Tal Cl) Tbl) (qeps k)) (qadd (qadd (SA n) (Sc n)) (SB n)) ∧
    qle (qadd (qadd (SA n) (Sc n)) (SB n)) (qadd (qadd (qadd Tah Ch) Tbh) (qeps k))
  obtain ⟨p1, p2⟩ := pa; obtain ⟨q1, q2⟩ := pb
  have s2' : qEq (qadd (qeps (k + 2)) (qeps (k + 2))) (qeps (k + 1)) := s2
  clear s2
  generalize qeps (k + 2) = e2 at *; generalize qeps (k + 1) = e1 at *; generalize qeps k = e0 at *
  generalize SA n = a at *; generalize SB n = b at *; generalize Sc n = c at *
  clear hn
  have u1 : qle (qadd (qadd a c) b) (qadd (qadd (qadd Tah e2) (qadd Ch e2)) (qadd Tbh e2)) :=
    qSum.add_le_add (qSum.add_le_add p2 c2) q2
  have l1 : qle (qadd (qadd (qsub Tal e2) (qsub Cl e2)) (qsub Tbl e2)) (qadd (qadd a c) b) :=
    qSum.add_le_add (qSum.add_le_add p1 c1) q1
  clear p1 p2 q1 q2 c1 c2
  unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith⟩

end ZLimits

#print axioms ZLimits.hull_lo
#print axioms ZLimits.hull_hi
#print axioms ZLimits.tail_rule
#print axioms ZLimits.limits_enclosure
