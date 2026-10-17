import ZMonoStep

/-!
# ZRangePin — the range of an integral over a parameter box, by pins (`zintegral.check_range`). Zero axioms.

The kernel pins a parameter `p_j` whose `∂f/∂p_j` keeps its sign over `[a, b] × box` and reads the integral at two
corners: the low one (each pinned parameter at the end where `f` is smallest) for `L`, the high one for `U`. Here:
  * the sign, as in the run (`zmonocert.sign_covered` along `p_j`): a step reading of `f` along `p_j` and a box bound
    of the grammar's `D_j f` with `L ≥ 0` (rising) or `U ≤ 0` (falling) — `ZMonoStep.slope_step` makes `f` at any
    point of the box at least `f` at the low end of `p_j` (`pin_low`), at most `f` at the high end (`pin_high`);
  * chained over the pins (`corner_low`, `ZSlopeSqrt.corner_bound_S`), with the integration variable `x_i` not pinned
    (the corner commutes with moving `x_i`: `corner_upd`);
  * every tagged sum over a refinement of the LOW corner's certificate, at ANY point `p` of the box, lies above
    `L − ε` (`range_low`); over a refinement of the HIGH corner's, below `U + ε` (`range_high`) — the two corners'
    leaves are the ordinary ones (`PieceR`, `ZIntegralR`).
The two partitions may differ: each bound holds for the sums of its own refinements (both families tend to the one
integral; no limit is taken here).
-/

namespace ZRangePin

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZIntegral ZIntegralR ZMonoStep

/-- `f` is monotone along `x_j` over the box: rising (`up`) with `D_j f ≥ L ≥ 0`, or falling with `D_j f ≤ U ≤ 0`. -/
def Mono (B : Box QExpr) (e : G) (j : Nat) (up : Bool) : Prop :=
  StepRead B j e ∧ ∃ L U, BoxEv B (D j e) L U ∧ (up = true → qle qzero L) ∧ (up = false → qle U qzero)

theorem upd_same_pt (p : Point QExpr) (j : Nat) : ∀ m, upd p j (p j) m = p m := fun m => by
  unfold upd
  cases Nat.decEq m j with
  | isTrue h => subst h; rfl
  | isFalse _ => rfl

theorem eval_upd_same (n : Nat) (p : Point QExpr) (j : Nat) (e : G) : evalN n (upd p j (p j)) e = evalN n p e :=
  evalN_dep n _ _ e (fun m _ => upd_same_pt p j m)

/-- From the low end of `x_j`: `f(low) ≤ f(p) + ε`. -/
theorem pin_low {B : Box QExpr} {e : G} {j : Nat} {up : Bool} (h : Mono B e j up) {p : Point QExpr}
    (hp : InBox qOrd B p) : SLe (fun n => evalN n (upd p j (endOf B (!up) j)) e) (fun n => evalN n p e) := by
  obtain ⟨hS, L, U, hV, hu, hd⟩ := h
  have hpj : qle (B j).1 (p j) ∧ qle (p j) (B j).2 := hp j
  obtain ⟨hj1, hj2⟩ := hpj
  intro k
  cases up with
  | true =>
      -- the low end is (B j).1; the slope from it to p_j is ≥ L·(…) ≥ 0
      have hs : InBox qOrd B (upd p j (B j).1) := upd_end_inbox qOrd j false hp
      have ht : InBox qOrd B (upd p j (p j)) := fun m => by rw [upd_same_pt]; exact hp m
      obtain ⟨N, hN⟩ := slope_step hS hV hs ht hj1 k
      refine ⟨N, fun n hn => ?_⟩
      have a : qle (qsub (qmul L (qsub (p j) (B j).1)) (qeps k)) (qsub (evalN n (upd p j (p j)) e) (evalN n (upd p j (B j).1) e)) := (hN n hn).1
      have f := qmul_nonneg (hu rfl) (by unfold qsub; rat_linarith : qle qzero (qsub (p j) (B j).1))
      have e1 := eval_upd_same n p j e
      show qle (qsub (evalN n (upd p j (B j).1) e) (evalN n p e)) (qeps k)
      rw [← e1]; unfold qsub at *; rat_linarith
  | false =>
      -- the low end is (B j).2; from p_j to it the step is ≤ U·(…) ≤ 0
      have ht : InBox qOrd B (upd p j (B j).2) := upd_end_inbox qOrd j true hp
      have hs : InBox qOrd B (upd p j (p j)) := fun m => by rw [upd_same_pt]; exact hp m
      obtain ⟨N, hN⟩ := slope_step hS hV hs ht hj2 k
      refine ⟨N, fun n hn => ?_⟩
      have b : qle (qsub (evalN n (upd p j (B j).2) e) (evalN n (upd p j (p j)) e)) (qadd (qmul U (qsub (B j).2 (p j))) (qeps k)) := (hN n hn).2
      have d0 : qle qzero (qsub (B j).2 (p j)) := by unfold qsub; rat_linarith
      have f := scale_l (hd rfl) d0
      have z : qEq (qmul (qsub (B j).2 (p j)) qzero) qzero := qmul_zero _
      have c : qEq (qmul U (qsub (B j).2 (p j))) (qmul (qsub (B j).2 (p j)) U) := qmul_comm _ _
      have e1 := eval_upd_same n p j e
      show qle (qsub (evalN n (upd p j (B j).2) e) (evalN n p e)) (qeps k)
      rw [← e1] at *; unfold qsub at *; rat_linarith

/-- To the high end of `x_j`: `f(p) ≤ f(high) + ε`. -/
theorem pin_high {B : Box QExpr} {e : G} {j : Nat} {up : Bool} (h : Mono B e j up) {p : Point QExpr}
    (hp : InBox qOrd B p) : SLe (fun n => evalN n p e) (fun n => evalN n (upd p j (endOf B up j)) e) := by
  obtain ⟨hS, L, U, hV, hu, hd⟩ := h
  have hpj : qle (B j).1 (p j) ∧ qle (p j) (B j).2 := hp j
  obtain ⟨hj1, hj2⟩ := hpj
  intro k
  cases up with
  | true =>
      have ht : InBox qOrd B (upd p j (B j).2) := upd_end_inbox qOrd j true hp
      have hs : InBox qOrd B (upd p j (p j)) := fun m => by rw [upd_same_pt]; exact hp m
      obtain ⟨N, hN⟩ := slope_step hS hV hs ht hj2 k
      refine ⟨N, fun n hn => ?_⟩
      have a : qle (qsub (qmul L (qsub (B j).2 (p j))) (qeps k)) (qsub (evalN n (upd p j (B j).2) e) (evalN n (upd p j (p j)) e)) := (hN n hn).1
      have f := qmul_nonneg (hu rfl) (by unfold qsub; rat_linarith : qle qzero (qsub (B j).2 (p j)))
      have e1 := eval_upd_same n p j e
      show qle (qsub (evalN n p e) (evalN n (upd p j (B j).2) e)) (qeps k)
      rw [← e1]; unfold qsub at *; rat_linarith
  | false =>
      have hs : InBox qOrd B (upd p j (B j).1) := upd_end_inbox qOrd j false hp
      have ht : InBox qOrd B (upd p j (p j)) := fun m => by rw [upd_same_pt]; exact hp m
      obtain ⟨N, hN⟩ := slope_step hS hV hs ht hj1 k
      refine ⟨N, fun n hn => ?_⟩
      have b : qle (qsub (evalN n (upd p j (p j)) e) (evalN n (upd p j (B j).1) e)) (qadd (qmul U (qsub (p j) (B j).1)) (qeps k)) := (hN n hn).2
      have d0 : qle qzero (qsub (p j) (B j).1) := by unfold qsub; rat_linarith
      have f := scale_l (hd rfl) d0
      have z : qEq (qmul (qsub (p j) (B j).1) qzero) qzero := qmul_zero _
      have c : qEq (qmul U (qsub (p j) (B j).1)) (qmul (qsub (p j) (B j).1) U) := qmul_comm _ _
      have e1 := eval_upd_same n p j e
      show qle (qsub (evalN n p e) (evalN n (upd p j (B j).1) e)) (qeps k)
      rw [← e1] at *; unfold qsub at *; rat_linarith

/-- THE LOW CORNER, chained over the pins. -/
theorem corner_low (e : G) (B : Box QExpr) (sg : Nat → Bool) :
    ∀ (ns : List Nat), (∀ j, List.Mem j ns → ∀ p, InBox qOrd B p →
        SLe (fun n => evalN n (upd p j (endOf B (sg j) j)) e) (fun n => evalN n p e)) →
      ∀ p, InBox qOrd B p → SLe (fun n => evalN n (cornerOn B sg ns p) e) (fun n => evalN n p e) := by
  intro ns
  induction ns with
  | nil => intro _ p _; exact SLe_refl _
  | cons j ns ih =>
      intro hm p hp
      exact SLe_trans (ih (fun m hm' => hm m (List.Mem.tail j hm')) _ (upd_end_inbox qOrd j (sg j) hp))
        (hm j (List.Mem.head ns) p hp)

theorem corner_inbox (B : Box QExpr) (sg : Nat → Bool) :
    ∀ (ns : List Nat) (p : Point QExpr), InBox qOrd B p → InBox qOrd B (cornerOn B sg ns p)
  | [], _, hp => hp
  | j :: ns, p, hp => corner_inbox B sg ns _ (upd_end_inbox qOrd j (sg j) hp)

theorem corner_congr (B : Box QExpr) (sg : Nat → Bool) :
    ∀ (ns : List Nat) (p q : Point QExpr), (∀ m, p m = q m) → ∀ m, cornerOn B sg ns p m = cornerOn B sg ns q m
  | [], _, _, h => h
  | j :: ns, p, q, h => corner_congr B sg ns _ _ (fun m => by
      unfold upd
      cases Nat.decEq m j with
      | isTrue _ => rfl
      | isFalse _ => exact h m)

/-- The corner commutes with moving the integration variable `x_i` (not a pin). -/
theorem corner_upd (B : Box QExpr) (sg : Nat → Bool) (i : Nat) (t : QExpr) :
    ∀ (ns : List Nat) (p : Point QExpr), (∀ j, List.Mem j ns → j ≠ i) →
      ∀ m, cornerOn B sg ns (upd p i t) m = upd (cornerOn B sg ns p) i t m
  | [], _, _, _ => rfl
  | j :: ns, p, hns, m => by
      have hj : j ≠ i := hns j (List.Mem.head ns)
      have sw : ∀ m', upd (upd p i t) j (endOf B (sg j) j) m' = upd (upd p j (endOf B (sg j) j)) i t m' := fun m' => by
        unfold upd
        cases Nat.decEq m' j with
        | isTrue h1 =>
            cases Nat.decEq m' i with
            | isTrue h2 => exact absurd (h1.symm.trans h2) hj
            | isFalse _ => rfl
        | isFalse _ => rfl
      show cornerOn B sg ns (upd (upd p i t) j (endOf B (sg j) j)) m = upd (cornerOn B sg ns (upd p j (endOf B (sg j) j))) i t m
      rw [corner_congr B sg ns _ _ sw m]
      exact corner_upd B sg i t ns _ (fun j' h' => hns j' (List.Mem.tail j h')) m

/-- One-sided enclosures (`ZIntegral.enclosure_sound`'s halves). -/
theorem lower_only (f : QExpr → QExpr) :
    ∀ ps : List (Piece QExpr), (∀ p, List.Mem p ps → WeightsOK qSum p ∧ ∀ wt, List.Mem wt p.fine → qle p.lo (f wt.2)) →
      qle (lower qSum ps) (total qSum f ps)
  | [], _ => qle_refl _
  | p :: rest, h => by
      have ⟨⟨hw0, hwle, hwge⟩, htag⟩ := h p (List.Mem.head rest)
      have hr := lower_only f rest (fun z hz => h z (List.Mem.tail _ hz))
      have hlo : qSum.le (qSum.mul p.lo (qSum.add p.b (qSum.neg p.a))) (rsum qSum f p.fine) :=
        qSum.le_trans (qSum.mul_congr p.lo hwge hwle)
          (piece_lower qSum f p.lo p.fine (fun wt hm => ⟨hw0 wt hm, htag wt hm⟩))
      exact qSum.add_le_add hlo hr

theorem upper_only (f : QExpr → QExpr) :
    ∀ ps : List (Piece QExpr), (∀ p, List.Mem p ps → WeightsOK qSum p ∧ ∀ wt, List.Mem wt p.fine → qle (f wt.2) p.hi) →
      qle (total qSum f ps) (upper qSum ps)
  | [], _ => qle_refl _
  | p :: rest, h => by
      have ⟨⟨hw0, hwle, hwge⟩, htag⟩ := h p (List.Mem.head rest)
      have hr := upper_only f rest (fun z hz => h z (List.Mem.tail _ hz))
      have hhi : qSum.le (rsum qSum f p.fine) (qSum.mul p.hi (qSum.add p.b (qSum.neg p.a))) :=
        qSum.le_trans (piece_upper qSum f p.hi p.fine (fun wt hm => ⟨hw0 wt hm, htag wt hm⟩))
          (qSum.mul_congr p.hi hwle hwge)
      exact qSum.add_le_add hhi hr

/-- THE RANGE, FROM BELOW: at any point `p` of the box, every tagged sum over a refinement of the LOW corner's
certificate is at least `L − ε_k·W`. -/
theorem range_low {e : G} {B : Box QExpr} {i : Nat} {ns : List Nat} {up : Nat → Bool} {p : Point QExpr}
    (hp : InBox qOrd B p) (hni : ∀ j, List.Mem j ns → j ≠ i) (hm : ∀ j, List.Mem j ns → Mono B e j (up j))
    {qs : List (Piece QExpr)} (hq : ∀ q, List.Mem q qs → PieceR e (cornerOn B (fun j => !up j) ns p) i q)
    (hab : ∀ q, List.Mem q qs → qle (B i).1 q.a ∧ qle q.b (B i).2) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (lower qSum qs) (qmul (qeps k) (width qs))) (total qSum (fun t => evalN n (upd p i t) e) qs) := by
  intro k
  have cl := corner_low e B (fun j => !up j) ns (fun j hj p' hp' => pin_low (hm j hj) hp')
  have tag : ∀ q, List.Mem q qs → ∃ N, ∀ n, N ≤ n → ∀ wt, List.Mem wt q.fine →
      qle (qsub q.lo (qeps k)) (evalN n (upd p i wt.2) e) := by
    intro q hqm
    obtain ⟨hleaf, _, htags⟩ := hq q hqm
    refine ev_list (fun (wt : QExpr × QExpr) n => qle (qsub q.lo (qeps k)) (evalN n (upd p i wt.2) e)) q.fine
      (fun wt hw => ?_)
    obtain ⟨t1, t2⟩ := htags wt hw
    obtain ⟨a1, b1⟩ := hab q hqm
    have hpt : InBox qOrd B (upd p i wt.2) := fun m => by
      unfold upd
      cases Nat.decEq m i with
      | isTrue h => subst h; exact ⟨qle_trans a1 t1, qle_trans t2 b1⟩
      | isFalse _ => exact hp m
    obtain ⟨N1, h1⟩ := hleaf wt.2 t1 t2 (k + 1)
    obtain ⟨N2, h2⟩ := cl _ hpt (k + 1)
    refine ⟨N1 + N2, fun n hn => ?_⟩
    obtain ⟨l1, _⟩ := h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
    have s2 : qle (qsub (evalN n (cornerOn B (fun j => !up j) ns (upd p i wt.2)) e) (evalN n (upd p i wt.2) e))
        (qeps (k + 1)) := h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
    have ce : evalN n (cornerOn B (fun j => !up j) ns (upd p i wt.2)) e =
        evalN n (upd (cornerOn B (fun j => !up j) ns p) i wt.2) e :=
      evalN_dep n _ _ e (fun m _ => corner_upd B _ i wt.2 ns p hni m)
    have es := qeps_succ_add k
    show qle (qsub q.lo (qeps k)) (evalN n (upd p i wt.2) e)
    rw [ce] at s2
    unfold qsub at *; rat_linarith
  obtain ⟨N, hN⟩ := ev_list _ qs tag
  refine ⟨N, fun n hn => ?_⟩
  have lo := lower_only (fun t => evalN n (upd p i t) e) (qs.map (ZIntegralR.widen k)) (by
    intro q' hq'
    obtain ⟨q, hqm, he⟩ := mem_widen hq'
    subst he
    exact ⟨(hq q hqm).2.1, fun wt hw => hN n hn q hqm wt hw⟩)
  rw [total_widen] at lo
  exact qle_respects (lower_widen k qs) (qEq_refl _) lo

/-- THE RANGE, FROM ABOVE: every tagged sum over a refinement of the HIGH corner's certificate is at most `U + ε_k·W`. -/
theorem range_high {e : G} {B : Box QExpr} {i : Nat} {ns : List Nat} {up : Nat → Bool} {p : Point QExpr}
    (hp : InBox qOrd B p) (hni : ∀ j, List.Mem j ns → j ≠ i) (hm : ∀ j, List.Mem j ns → Mono B e j (up j))
    {qs : List (Piece QExpr)} (hq : ∀ q, List.Mem q qs → PieceR e (cornerOn B up ns p) i q)
    (hab : ∀ q, List.Mem q qs → qle (B i).1 q.a ∧ qle q.b (B i).2) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (total qSum (fun t => evalN n (upd p i t) e) qs) (qadd (upper qSum qs) (qmul (qeps k) (width qs))) := by
  intro k
  have cl := corner_bound_S e B up ns (fun j hj p' hp' => pin_high (hm j hj) hp')
  have tag : ∀ q, List.Mem q qs → ∃ N, ∀ n, N ≤ n → ∀ wt, List.Mem wt q.fine →
      qle (evalN n (upd p i wt.2) e) (qadd q.hi (qeps k)) := by
    intro q hqm
    obtain ⟨hleaf, _, htags⟩ := hq q hqm
    refine ev_list (fun (wt : QExpr × QExpr) n => qle (evalN n (upd p i wt.2) e) (qadd q.hi (qeps k))) q.fine
      (fun wt hw => ?_)
    obtain ⟨t1, t2⟩ := htags wt hw
    obtain ⟨a1, b1⟩ := hab q hqm
    have hpt : InBox qOrd B (upd p i wt.2) := fun m => by
      unfold upd
      cases Nat.decEq m i with
      | isTrue h => subst h; exact ⟨qle_trans a1 t1, qle_trans t2 b1⟩
      | isFalse _ => exact hp m
    obtain ⟨N1, h1⟩ := hleaf wt.2 t1 t2 (k + 1)
    obtain ⟨N2, h2⟩ := cl _ hpt (k + 1)
    refine ⟨N1 + N2, fun n hn => ?_⟩
    obtain ⟨_, u1⟩ := h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
    have s2 : qle (qsub (evalN n (upd p i wt.2) e) (evalN n (cornerOn B up ns (upd p i wt.2)) e))
        (qeps (k + 1)) := h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn)
    have ce : evalN n (cornerOn B up ns (upd p i wt.2)) e = evalN n (upd (cornerOn B up ns p) i wt.2) e :=
      evalN_dep n _ _ e (fun m _ => corner_upd B _ i wt.2 ns p hni m)
    have es := qeps_succ_add k
    show qle (evalN n (upd p i wt.2) e) (qadd q.hi (qeps k))
    rw [ce] at s2
    unfold qsub at *; rat_linarith
  obtain ⟨N, hN⟩ := ev_list _ qs tag
  refine ⟨N, fun n hn => ?_⟩
  have hi := upper_only (fun t => evalN n (upd p i t) e) (qs.map (ZIntegralR.widen k)) (by
    intro q' hq'
    obtain ⟨q, hqm, he⟩ := mem_widen hq'
    subst he
    exact ⟨(hq q hqm).2.1, fun wt hw => hN n hn q hqm wt hw⟩)
  rw [total_widen] at hi
  exact qle_respects (qEq_refl _) (upper_widen k qs) hi

end ZRangePin

#print axioms ZRangePin.pin_low
#print axioms ZRangePin.pin_high
#print axioms ZRangePin.corner_low
#print axioms ZRangePin.corner_upd
#print axioms ZRangePin.lower_only
#print axioms ZRangePin.upper_only
#print axioms ZRangePin.range_low
#print axioms ZRangePin.range_high
