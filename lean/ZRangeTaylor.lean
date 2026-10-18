import ZRangePin
import ZJetClose

/-!
# ZRangeTaylor — the range by pins when a corner's leaf is a Taylor leaf. Zero axioms.

`ZRangePin` needs a bound of `f` at every tag of the corner's pieces (interval and monotone leaves). A Taylor leaf
bounds the SYMMETRIC tagged sums of its piece (`ZJetClose.taylorN_kernel`: `ssum`, the cells' values at `m ± s`), not
`f` at a tag. The pins compose with that claim all the same: at any point `p` of the box, each symmetric sum's tags are
pointwise at least their low corner's (`ZRangePin.corner_low`, the corner commuting with `x_i`: `corner_upd`), so the
symmetric sum at `p` is at least the corner's — hence at least the corner's Taylor bound, up to `ε` (`range_taylor_low`);
at most the high corner's from above (`range_taylor_high`).
-/

namespace ZRangeTaylor

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZPow ZDeriv ZTaylorN ZIntegral ZIntegralR
  ZIntegralT ZMonoStep ZRangePin

/-- The cells' widths `Σ (b − a)`. -/
def wsum (cs : List Cell) : QExpr := csum (fun _ => qone) cs

theorem tag_inbox' {B : Box QExpr} {q : Point QExpr} {i : Nat} {t : QExpr} (hq : InBox qOrd B q)
    (h1 : qle (B i).1 t) (h2 : qle t (B i).2) : InBox qOrd B (upd q i t) := fun m => by
  unfold upd
  cases Nat.decEq m i with
  | isTrue h => subst h; exact ⟨h1, h2⟩
  | isFalse _ => exact hq m

/-- A cellwise lower bound up to `δ` gives the sum's, up to `δ·Σ(b − a)`. -/
theorem csum_lower {g1 g2 : Cell → QExpr} {δ : QExpr} :
    ∀ cs : List Cell, (∀ c, List.Mem c cs → qle qzero (qsub c.2.1 c.1) ∧ qle (qsub (g1 c) δ) (g2 c)) →
      qle (qsub (csum g1 cs) (qmul δ (wsum cs))) (csum g2 cs)
  | [], _ => by
      show qle (qsub qzero (qmul δ qzero)) qzero
      have : qEq (qsub qzero (qmul δ qzero)) qzero := by unfold qsub; rat_ring
      exact qle_of_qEq this
  | c :: rest, h => by
      obtain ⟨w0, hc⟩ := h c (List.Mem.head rest)
      have ih := csum_lower rest (fun z hz => h z (List.Mem.tail _ hz))
      have f := scale_l hc w0
      show qle (qsub (qadd (qmul (qsub c.2.1 c.1) (g1 c)) (csum g1 rest))
          (qmul δ (qadd (qmul (qsub c.2.1 c.1) qone) (csum (fun _ => qone) rest))))
        (qadd (qmul (qsub c.2.1 c.1) (g2 c)) (csum g2 rest))
      have e1 : qEq (qmul (qsub c.2.1 c.1) (qsub (g1 c) δ)) (qsub (qmul (qsub c.2.1 c.1) (g1 c)) (qmul δ (qsub c.2.1 c.1))) := by
        unfold qsub; rat_ring
      have e2 : qEq (qmul δ (qadd (qmul (qsub c.2.1 c.1) qone) (csum (fun _ => qone) rest)))
          (qadd (qmul δ (qsub c.2.1 c.1)) (qmul δ (wsum rest))) := by unfold wsum; rat_ring
      generalize qmul (qsub c.2.1 c.1) (g1 c) = A1 at *; generalize qmul (qsub c.2.1 c.1) (g2 c) = A2 at *
      generalize qmul (qsub c.2.1 c.1) (qsub (g1 c) δ) = A3 at *
      generalize qmul δ (qsub c.2.1 c.1) = A4 at *; generalize qmul δ (wsum rest) = A5 at *
      generalize csum g1 rest = R1 at *; generalize csum g2 rest = R2 at *
      generalize qmul δ (qadd (qmul (qsub c.2.1 c.1) qone) (csum (fun _ => qone) rest)) = A6 at *
      unfold qsub at *; rat_linarith

/-- THE RANGE WITH A TAYLOR CORNER, FROM BELOW: the symmetric sum at any point `p` of the box is at least its low
corner's, up to `ε_k·Σ(b − a)`; so any eventual lower bound of the corner's (`taylorN_kernel`) holds at `p`. -/
theorem range_taylor_low {e : G} {B : Box QExpr} {i : Nat} {ns : List Nat} {up : Nat → Bool} {p : Point QExpr}
    (hp : InBox qOrd B p) (hni : ∀ j, List.Mem j ns → j ≠ i) (hm : ∀ j, List.Mem j ns → Mono B e j (up j))
    {m : QExpr} {cs : List Cell}
    (hcs : ∀ c, List.Mem c cs → qle qzero (qsub c.2.1 c.1) ∧
      qle (B i).1 (qadd m c.2.2) ∧ qle (qadd m c.2.2) (B i).2 ∧ qle (B i).1 (qsub m c.2.2) ∧ qle (qsub m c.2.2) (B i).2)
    {Lb : Nat → QExpr} (hL : ∀ k, ∃ N, ∀ n, N ≤ n → qle (Lb k) (ssum n e (cornerOn B (fun j => !up j) ns p) i m cs)) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (qsub (Lb k) (qmul (qeps k) (wsum cs))) (ssum n e p i m cs) := by
  intro k
  have cl := corner_low e B (fun j => !up j) ns (fun j hj p' hp' => pin_low (hm j hj) hp')
  have tag : ∀ t, qle (B i).1 t → qle t (B i).2 → ∃ N, ∀ n, N ≤ n →
      qle (qsub (evalN n (upd (cornerOn B (fun j => !up j) ns p) i t) e) (qeps (k + 1))) (evalN n (upd p i t) e) := by
    intro t t1 t2
    have hpt : InBox qOrd B (upd p i t) := tag_inbox' hp t1 t2
    obtain ⟨N, hN⟩ := cl _ hpt (k + 1)
    refine ⟨N, fun n hn => ?_⟩
    have s2 : qle (qsub (evalN n (cornerOn B (fun j => !up j) ns (upd p i t)) e) (evalN n (upd p i t) e)) (qeps (k + 1)) :=
      hN n hn
    have ce : evalN n (cornerOn B (fun j => !up j) ns (upd p i t)) e = evalN n (upd (cornerOn B (fun j => !up j) ns p) i t) e :=
      evalN_dep n _ _ e (fun m' _ => corner_upd B _ i t ns p hni m')
    rw [ce] at s2
    unfold qsub at *; rat_linarith
  obtain ⟨N1, h1⟩ := ev_list (fun (c : Cell) n =>
      qle (qsub (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qadd m c.2.2)) e) (qeps (k + 1)))
        (evalN n (upd p i (qadd m c.2.2)) e) ∧
      qle (qsub (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qsub m c.2.2)) e) (qeps (k + 1)))
        (evalN n (upd p i (qsub m c.2.2)) e)) cs
    (fun c hc => by
      obtain ⟨_, a1, a2, b1, b2⟩ := hcs c hc
      obtain ⟨Na, ha⟩ := tag _ a1 a2
      obtain ⟨Nb, hb⟩ := tag _ b1 b2
      exact ⟨Na + Nb, fun n hn => ⟨ha n (Nat.le_trans (Nat.le_add_right _ _) hn), hb n (Nat.le_trans (Nat.le_add_left _ _) hn)⟩⟩)
  obtain ⟨N2, h2⟩ := hL k
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have lo := csum_lower (δ := qeps k)
    (g1 := fun c => qadd (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qadd m c.2.2)) e)
      (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qsub m c.2.2)) e))
    (g2 := fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs
    (fun c hc => ⟨(hcs c hc).1, by
      obtain ⟨a, b⟩ := h1 n (Nat.le_trans (Nat.le_add_right _ _) hn) c hc
      have s := qeps_succ_add k
      show qle (qsub (qadd (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qadd m c.2.2)) e)
          (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qsub m c.2.2)) e)) (qeps k))
        (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
      unfold qsub at *; rat_linarith⟩)
  have l2 := h2 n (Nat.le_trans (Nat.le_add_left _ _) hn)
  unfold ssum at *
  generalize csum (fun c => qadd (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qadd m c.2.2)) e)
      (evalN n (upd (cornerOn B (fun j => !up j) ns p) i (qsub m c.2.2)) e)) cs = Sc at *
  generalize csum (fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs = Sp at *
  generalize qmul (qeps k) (wsum cs) = W at *
  unfold qsub at *; rat_linarith

theorem csum_upper {g1 g2 : Cell → QExpr} {δ : QExpr} :
    ∀ cs : List Cell, (∀ c, List.Mem c cs → qle qzero (qsub c.2.1 c.1) ∧ qle (g2 c) (qadd (g1 c) δ)) →
      qle (csum g2 cs) (qadd (csum g1 cs) (qmul δ (wsum cs)))
  | [], _ => by
      show qle qzero (qadd qzero (qmul δ qzero))
      have : qEq (qadd qzero (qmul δ qzero)) qzero := by rat_ring
      exact qle_of_qEq (qEq_symm this)
  | c :: rest, h => by
      obtain ⟨w0, hc⟩ := h c (List.Mem.head rest)
      have ih := csum_upper rest (fun z hz => h z (List.Mem.tail _ hz))
      have f := scale_l hc w0
      show qle (qadd (qmul (qsub c.2.1 c.1) (g2 c)) (csum g2 rest))
        (qadd (qadd (qmul (qsub c.2.1 c.1) (g1 c)) (csum g1 rest))
          (qmul δ (qadd (qmul (qsub c.2.1 c.1) qone) (csum (fun _ => qone) rest))))
      have e1 : qEq (qmul (qsub c.2.1 c.1) (qadd (g1 c) δ)) (qadd (qmul (qsub c.2.1 c.1) (g1 c)) (qmul δ (qsub c.2.1 c.1))) := by
        rat_ring
      have e2 : qEq (qmul δ (qadd (qmul (qsub c.2.1 c.1) qone) (csum (fun _ => qone) rest)))
          (qadd (qmul δ (qsub c.2.1 c.1)) (qmul δ (wsum rest))) := by unfold wsum; rat_ring
      generalize qmul (qsub c.2.1 c.1) (g1 c) = A1 at *; generalize qmul (qsub c.2.1 c.1) (g2 c) = A2 at *
      generalize qmul (qsub c.2.1 c.1) (qadd (g1 c) δ) = A3 at *
      generalize qmul δ (qsub c.2.1 c.1) = A4 at *; generalize qmul δ (wsum rest) = A5 at *
      generalize csum g1 rest = R1 at *; generalize csum g2 rest = R2 at *
      generalize qmul δ (qadd (qmul (qsub c.2.1 c.1) qone) (csum (fun _ => qone) rest)) = A6 at *
      rat_linarith

/-- THE RANGE WITH A TAYLOR CORNER, FROM ABOVE: at most the high corner's, up to `ε_k·Σ(b − a)`. -/
theorem range_taylor_high {e : G} {B : Box QExpr} {i : Nat} {ns : List Nat} {up : Nat → Bool} {p : Point QExpr}
    (hp : InBox qOrd B p) (hni : ∀ j, List.Mem j ns → j ≠ i) (hm : ∀ j, List.Mem j ns → Mono B e j (up j))
    {m : QExpr} {cs : List Cell}
    (hcs : ∀ c, List.Mem c cs → qle qzero (qsub c.2.1 c.1) ∧
      qle (B i).1 (qadd m c.2.2) ∧ qle (qadd m c.2.2) (B i).2 ∧ qle (B i).1 (qsub m c.2.2) ∧ qle (qsub m c.2.2) (B i).2)
    {Ub : Nat → QExpr} (hU : ∀ k, ∃ N, ∀ n, N ≤ n → qle (ssum n e (cornerOn B up ns p) i m cs) (Ub k)) :
    ∀ k, ∃ N, ∀ n, N ≤ n → qle (ssum n e p i m cs) (qadd (Ub k) (qmul (qeps k) (wsum cs))) := by
  intro k
  have cl := corner_bound_S e B up ns (fun j hj p' hp' => pin_high (hm j hj) hp')
  have tag : ∀ t, qle (B i).1 t → qle t (B i).2 → ∃ N, ∀ n, N ≤ n →
      qle (evalN n (upd p i t) e) (qadd (evalN n (upd (cornerOn B up ns p) i t) e) (qeps (k + 1))) := by
    intro t t1 t2
    have hpt : InBox qOrd B (upd p i t) := tag_inbox' hp t1 t2
    obtain ⟨N, hN⟩ := cl _ hpt (k + 1)
    refine ⟨N, fun n hn => ?_⟩
    have s2 : qle (qsub (evalN n (upd p i t) e) (evalN n (cornerOn B up ns (upd p i t)) e)) (qeps (k + 1)) := hN n hn
    have ce : evalN n (cornerOn B up ns (upd p i t)) e = evalN n (upd (cornerOn B up ns p) i t) e :=
      evalN_dep n _ _ e (fun m' _ => corner_upd B _ i t ns p hni m')
    rw [ce] at s2
    unfold qsub at *; rat_linarith
  obtain ⟨N1, h1⟩ := ev_list (fun (c : Cell) n =>
      qle (evalN n (upd p i (qadd m c.2.2)) e) (qadd (evalN n (upd (cornerOn B up ns p) i (qadd m c.2.2)) e) (qeps (k + 1))) ∧
      qle (evalN n (upd p i (qsub m c.2.2)) e) (qadd (evalN n (upd (cornerOn B up ns p) i (qsub m c.2.2)) e) (qeps (k + 1)))) cs
    (fun c hc => by
      obtain ⟨_, a1, a2, b1, b2⟩ := hcs c hc
      obtain ⟨Na, ha⟩ := tag _ a1 a2
      obtain ⟨Nb, hb⟩ := tag _ b1 b2
      exact ⟨Na + Nb, fun n hn => ⟨ha n (Nat.le_trans (Nat.le_add_right _ _) hn), hb n (Nat.le_trans (Nat.le_add_left _ _) hn)⟩⟩)
  obtain ⟨N2, h2⟩ := hU k
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have hi := csum_upper (δ := qeps k)
    (g1 := fun c => qadd (evalN n (upd (cornerOn B up ns p) i (qadd m c.2.2)) e)
      (evalN n (upd (cornerOn B up ns p) i (qsub m c.2.2)) e))
    (g2 := fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs
    (fun c hc => ⟨(hcs c hc).1, by
      obtain ⟨a, b⟩ := h1 n (Nat.le_trans (Nat.le_add_right _ _) hn) c hc
      have s := qeps_succ_add k
      show qle (qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e))
        (qadd (qadd (evalN n (upd (cornerOn B up ns p) i (qadd m c.2.2)) e)
          (evalN n (upd (cornerOn B up ns p) i (qsub m c.2.2)) e)) (qeps k))
      rat_linarith⟩)
  have u2 := h2 n (Nat.le_trans (Nat.le_add_left _ _) hn)
  unfold ssum at *
  generalize csum (fun c => qadd (evalN n (upd (cornerOn B up ns p) i (qadd m c.2.2)) e)
      (evalN n (upd (cornerOn B up ns p) i (qsub m c.2.2)) e)) cs = Sc at *
  generalize csum (fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) cs = Sp at *
  generalize qmul (qeps k) (wsum cs) = W at *
  rat_linarith

end ZRangeTaylor

#print axioms ZRangeTaylor.csum_lower
#print axioms ZRangeTaylor.range_taylor_low
#print axioms ZRangeTaylor.csum_upper
#print axioms ZRangeTaylor.range_taylor_high
