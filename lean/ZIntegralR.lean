import ZSlopeSqrt
import ZIntegral

/-!
# ZIntegralR — the integral enclosure on VR's operational reals, premise-free for `+ − × / exp ln sqrt`. Zero axioms.

`ZIntegral` proves the kernel's sum rule for any laws given as inequalities; `ZSlopeSqrt` proves the kernel's
readings for the grammar `+ − × / exp ln sqrt` (a value reading encloses the value, `value_sound`; a derivative reading
bounds the slope, `slope_sound`). This module joins them. For an integrand `e`, the integration quantity `i` and a
point `p` of the other quantities:

  * `interval_leaf`  — a value reading `[lo, hi]` over a box holding the piece gives the leaf at every point of it;
  * `monotone_leaf_up`, `monotone_leaf_down` — a derivative reading with a sign, and the value readings at the
    piece's two ends, give the leaf from the ends (no mean value theorem: `slope_sound` is exact slopes);
  * `enclosure_R`    — every tagged sum over a refinement of the certificate's partition lies, to every
    precision from some index on, in `[L − ε·W, U + ε·W]` (`W` the total width of the pieces): VR's order on
    operational reals, the value at a tag being the sequence `evalN n`.

So for this grammar the interval and monotone leaves of `zintegral.py` need no premise. NOT covered, said rather
than hidden: the other functions the kernel reads (`pow`, `sin`, `cos`, `atan`, `tan`, `log10`); the TAYLOR leaf
(its claim is about the limit of Riemann sums, and its reading — Taylor coefficients along the graph — is not
proved here); that the pieces tile `[a, b]` (the Python check; the bound does not use it).
-/

namespace ZIntegralR

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZIntegral

/-- VR's pre-rationals carry `ZIntegral`'s laws (equality is `qEq`, a setoid — the laws are inequalities). -/
def qSum : OSum QExpr where
  zero := qzero
  add := qadd
  neg := qneg
  mul := qmul
  le := qle
  le_refl := qle_refl
  le_trans := qle_trans
  add_le_add := fun h1 h2 => by rat_linarith
  mul_le_mul_nonneg := fun {c a b} hc h =>
    qle_respects (qmul_comm a c) (qmul_comm b c) (qmul_le_mul_of_nonneg h hc)
  mul_comm_le := fun a b => qle_of_qEq (qmul_comm a b)
  mul_add_le := fun a b c => qle_of_qEq (qmul_add a b c)
  mul_add_ge := fun a b c => qle_of_qEq (qEq_symm (qmul_add a b c))
  mul_zero_le := fun a => qle_of_qEq (qmul_zero a)
  mul_zero_ge := fun a => qle_of_qEq (qEq_symm (qmul_zero a))
  mul_congr := fun c h1 h2 => qle_of_qEq (qmul_respects (qEq_refl c) (qle_antisymm h1 h2))

/-! ## The leaf, at the real level -/

/-- The leaf on `[a, b]`: at every `t` of it (quantity `i` of `p` moved to `t`) the value lies in `[lo, hi]`, to
every precision from some index on (`Ev`). -/
def LeafEv (e : G) (p : Point QExpr) (i : Nat) (a b lo hi : QExpr) : Prop :=
  ∀ t, qle a t → qle t b → Ev (fun n => evalN n (upd p i t) e) lo hi

/-- The points of the piece lie in a box whose quantity `i` spans the piece and whose others hold `p`. -/
theorem inbox_upd {B : Box QExpr} {p : Point QExpr} {i : Nat} {a b : QExpr}
    (hp : ∀ j, j ≠ i → qle (B j).1 (p j) ∧ qle (p j) (B j).2) (ha : qle (B i).1 a) (hb : qle b (B i).2) :
    ∀ t, qle a t → qle t b → InBox qOrd B (upd p i t) := by
  intro t hat htb j
  cases Nat.decEq j i with
  | isTrue hj =>
      subst hj
      show qle (B j).1 (upd p j t j) ∧ qle (upd p j t j) (B j).2
      rw [upd_self]
      exact ⟨qle_trans ha hat, qle_trans htb hb⟩
  | isFalse hj =>
      show qle (B j).1 (upd p i t j) ∧ qle (upd p i t j) (B j).2
      rw [upd_other p i t j hj]
      exact hp j hj

/-- AN INTERVAL LEAF: the kernel's value reading over a box holding the piece. -/
theorem interval_leaf {e : G} {p : Point QExpr} {i : Nat} {a b lo hi : QExpr} {B : Box QExpr}
    (r : VRead B e lo hi) (hB : ∀ t, qle a t → qle t b → InBox qOrd B (upd p i t)) :
    LeafEv e p i a b lo hi :=
  fun t hat htb => value_sound (hB t hat htb) r

/-- Two points of the piece differ in quantity `i` only. -/
theorem upd_fix (p : Point QExpr) (i : Nat) (s t : QExpr) : ∀ j, j ≠ i → upd p i t j = upd p i s j := by
  intro j hj
  rw [upd_other p i t j hj, upd_other p i s j hj]

/-- The slope from `s` to `t` (`s ≤ t`, both in the piece): the derivative reading bounds it. -/
theorem slope_at {e : G} {p : Point QExpr} {i : Nat} {B : Box QExpr} {l h s t : QExpr}
    (r : DRead B i e l h) (hs : InBox qOrd B (upd p i s)) (ht : InBox qOrd B (upd p i t)) (hst : qle s t) :
    Ev (fun n => qsub (evalN n (upd p i t) e) (evalN n (upd p i s) e)) (qmul l (qsub t s)) (qmul h (qsub t s)) := by
  have hd : qle qzero (qsub (upd p i t i) (upd p i s i)) := by
    rw [upd_self, upd_self]; unfold qsub; rat_linarith
  have := slope_sound hs ht (upd_fix p i s t) hd r
  rw [upd_self, upd_self] at this
  exact this

/-- A MONOTONE LEAF, RISING: a derivative reading `[l, h]` with `l ≥ 0` over a box holding the piece, the value
at `a` read from `lo`, at `b` up to `hi` — then `[lo, hi]` holds on the whole piece. -/
theorem monotone_leaf_up {e : G} {p : Point QExpr} {i : Nat} {a b lo hi la hb' l h : QExpr} {B : Box QExpr}
    (r : DRead B i e l h) (hl : qle qzero l) (hB : ∀ t, qle a t → qle t b → InBox qOrd B (upd p i t))
    (hab : qle a b) (ea : Ev (fun n => evalN n (upd p i a) e) lo la) (eb : Ev (fun n => evalN n (upd p i b) e) hb' hi) :
    LeafEv e p i a b lo hi := by
  intro t hat htb k
  have s1 := slope_at r (hB a (qle_refl a) hab) (hB t hat htb) hat (k + 1)
  have s2 := slope_at r (hB t hat htb) (hB b hab (qle_refl b)) htb (k + 1)
  obtain ⟨N1, h1⟩ := s1
  obtain ⟨N2, h2⟩ := s2
  obtain ⟨N3, h3⟩ := ea (k + 1)
  obtain ⟨N4, h4⟩ := eb (k + 1)
  refine ⟨N1 + N2 + N3 + N4, fun n hn => ?_⟩
  have g1 : qle (qsub (qmul l (qsub t a)) (qeps (k + 1)))
      (qsub (evalN n (upd p i t) e) (evalN n (upd p i a) e)) :=
    (h1 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).1
  have g2 : qle (qsub (qmul l (qsub b t)) (qeps (k + 1)))
      (qsub (evalN n (upd p i b) e) (evalN n (upd p i t) e)) :=
    (h2 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).1
  have g3 : qle (qsub lo (qeps (k + 1))) (evalN n (upd p i a) e) :=
    (h3 n (Nat.le_trans (Nat.le_trans (Nat.le_add_left N3 (N1 + N2)) (Nat.le_add_right _ N4)) hn)).1
  have g4 : qle (evalN n (upd p i b) e) (qadd hi (qeps (k + 1))) :=
    (h4 n (Nat.le_trans (Nat.le_add_left N4 (N1 + N2 + N3)) hn)).2
  have f1 : qle qzero (qmul l (qsub t a)) := qmul_nonneg hl (by unfold qsub; rat_linarith)
  have f2 : qle qzero (qmul l (qsub b t)) := qmul_nonneg hl (by unfold qsub; rat_linarith)
  have ee := qeps_succ_add k
  show qle (qsub lo (qeps k)) (evalN n (upd p i t) e) ∧ qle (evalN n (upd p i t) e) (qadd hi (qeps k))
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-- A MONOTONE LEAF, FALLING: `h ≤ 0`; the ends trade places (`lo` from the value at `b`, `hi` at `a`). -/
theorem monotone_leaf_down {e : G} {p : Point QExpr} {i : Nat} {a b lo hi la hb' l h : QExpr} {B : Box QExpr}
    (r : DRead B i e l h) (hh : qle h qzero) (hB : ∀ t, qle a t → qle t b → InBox qOrd B (upd p i t))
    (hab : qle a b) (ea : Ev (fun n => evalN n (upd p i a) e) la hi) (eb : Ev (fun n => evalN n (upd p i b) e) lo hb') :
    LeafEv e p i a b lo hi := by
  intro t hat htb k
  have s1 := slope_at r (hB a (qle_refl a) hab) (hB t hat htb) hat (k + 1)
  have s2 := slope_at r (hB t hat htb) (hB b hab (qle_refl b)) htb (k + 1)
  obtain ⟨N1, h1⟩ := s1
  obtain ⟨N2, h2⟩ := s2
  obtain ⟨N3, h3⟩ := ea (k + 1)
  obtain ⟨N4, h4⟩ := eb (k + 1)
  refine ⟨N1 + N2 + N3 + N4, fun n hn => ?_⟩
  have g1 : qle (qsub (evalN n (upd p i t) e) (evalN n (upd p i a) e))
      (qadd (qmul h (qsub t a)) (qeps (k + 1))) :=
    (h1 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_right N1 N2) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).2
  have g2 : qle (qsub (evalN n (upd p i b) e) (evalN n (upd p i t) e))
      (qadd (qmul h (qsub b t)) (qeps (k + 1))) :=
    (h2 n (Nat.le_trans (Nat.le_trans (Nat.le_trans (Nat.le_add_left N2 N1) (Nat.le_add_right _ N3))
    (Nat.le_add_right _ N4)) hn)).2
  have g3 : qle (evalN n (upd p i a) e) (qadd hi (qeps (k + 1))) :=
    (h3 n (Nat.le_trans (Nat.le_trans (Nat.le_add_left N3 (N1 + N2)) (Nat.le_add_right _ N4)) hn)).2
  have g4 : qle (qsub lo (qeps (k + 1))) (evalN n (upd p i b) e) :=
    (h4 n (Nat.le_trans (Nat.le_add_left N4 (N1 + N2 + N3)) hn)).1
  have f1 : qle (qmul h (qsub t a)) qzero := by
    have := qmul_nonneg (a := qneg h) (b := qsub t a) (by rat_linarith) (by unfold qsub; rat_linarith)
    have e1 : qEq (qmul (qneg h) (qsub t a)) (qneg (qmul h (qsub t a))) := by rat_ring
    rat_linarith
  have f2 : qle (qmul h (qsub b t)) qzero := by
    have := qmul_nonneg (a := qneg h) (b := qsub b t) (by rat_linarith) (by unfold qsub; rat_linarith)
    have e1 : qEq (qmul (qneg h) (qsub b t)) (qneg (qmul h (qsub b t))) := by rat_ring
    rat_linarith
  have ee := qeps_succ_add k
  show qle (qsub lo (qeps k)) (evalN n (upd p i t) e) ∧ qle (evalN n (upd p i t) e) (qadd hi (qeps k))
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The sum -/

/-- A piece at the real level: the leaf on `[a, b]`, the weights, the tags in `[a, b]`. -/
def PieceR (e : G) (p : Point QExpr) (i : Nat) (q : Piece QExpr) : Prop :=
  LeafEv e p i q.a q.b q.lo q.hi ∧ WeightsOK qSum q ∧ (∀ wt, List.Mem wt q.fine → qle q.a wt.2 ∧ qle wt.2 q.b)

/-- The total width `W = Σ (b − a)`. -/
def width : List (Piece QExpr) → QExpr
  | [] => qzero
  | q :: qs => qadd (qsub q.b q.a) (width qs)

/-- The leaf's bounds moved out by `ε_k`. -/
def widen (k : Nat) (q : Piece QExpr) : Piece QExpr :=
  ⟨q.a, q.b, qsub q.lo (qeps k), qadd q.hi (qeps k), q.fine⟩

theorem total_widen (f : QExpr → QExpr) (k : Nat) :
    ∀ qs, total qSum f (qs.map (widen k)) = total qSum f qs
  | [] => rfl
  | q :: qs => by
      show qadd (rsum qSum f q.fine) (total qSum f (qs.map (widen k))) = qadd (rsum qSum f q.fine) (total qSum f qs)
      rw [total_widen f k qs]

theorem lower_widen (k : Nat) :
    ∀ qs, qEq (lower qSum (qs.map (widen k))) (qsub (lower qSum qs) (qmul (qeps k) (width qs)))
  | [] => by show qEq qzero (qsub qzero (qmul (qeps k) qzero)); unfold qsub; rat_ring
  | q :: qs => by
      have ih := lower_widen k qs
      show qEq (qadd (qmul (qsub q.lo (qeps k)) (qadd q.b (qneg q.a))) (lower qSum (qs.map (widen k))))
        (qsub (qadd (qmul q.lo (qadd q.b (qneg q.a))) (lower qSum qs)) (qmul (qeps k) (qadd (qsub q.b q.a) (width qs))))
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (by unfold qsub; rat_ring)

theorem upper_widen (k : Nat) :
    ∀ qs, qEq (upper qSum (qs.map (widen k))) (qadd (upper qSum qs) (qmul (qeps k) (width qs)))
  | [] => by show qEq qzero (qadd qzero (qmul (qeps k) qzero)); rat_ring
  | q :: qs => by
      have ih := upper_widen k qs
      show qEq (qadd (qmul (qadd q.hi (qeps k)) (qadd q.b (qneg q.a))) (upper qSum (qs.map (widen k))))
        (qadd (qadd (qmul q.hi (qadd q.b (qneg q.a))) (upper qSum qs)) (qmul (qeps k) (qadd (qsub q.b q.a) (width qs))))
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (by unfold qsub; rat_ring)

theorem mem_widen {k : Nat} {q' : Piece QExpr} :
    ∀ {qs : List (Piece QExpr)}, List.Mem q' (qs.map (widen k)) → ∃ q, List.Mem q qs ∧ q' = widen k q
  | [], h => by cases h
  | q :: qs, h => by
      cases h with
      | head => exact ⟨q, List.Mem.head qs, rfl⟩
      | tail _ h =>
          obtain ⟨q0, hm, he⟩ := mem_widen h
          exact ⟨q0, List.Mem.tail q hm, he⟩

/-- From some index on, for every element of a finite list (the largest of finitely many indices). -/
theorem ev_list {T : Type} (Q : T → Nat → Prop) :
    ∀ l : List T, (∀ x, List.Mem x l → ∃ N, ∀ n, N ≤ n → Q x n) → ∃ N, ∀ n, N ≤ n → ∀ x, List.Mem x l → Q x n
  | [], _ => ⟨0, fun _ _ x hx => by cases hx⟩
  | y :: ys, h => by
      obtain ⟨N1, h1⟩ := h y (List.Mem.head ys)
      obtain ⟨N2, h2⟩ := ev_list Q ys (fun x hx => h x (List.Mem.tail y hx))
      refine ⟨N1 + N2, fun n hn x hx => ?_⟩
      cases hx with
      | head => exact h1 n (Nat.le_trans (Nat.le_add_right N1 N2) hn)
      | tail _ hx => exact h2 n (Nat.le_trans (Nat.le_add_left N2 N1) hn) x hx

/-- THE ENCLOSURE ON VR'S REALS: every tagged sum over a refinement of the certificate's partition lies, to every
precision `ε_k` from some index on, in `[L − ε_k·W, U + ε_k·W]`. -/
theorem enclosure_R (e : G) (p : Point QExpr) (i : Nat) (qs : List (Piece QExpr))
    (h : ∀ q, List.Mem q qs → PieceR e p i q) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (lower qSum qs) (qmul (qeps k) (width qs))) (total qSum (fun t => evalN n (upd p i t) e) qs) ∧
      qle (total qSum (fun t => evalN n (upd p i t) e) qs) (qadd (upper qSum qs) (qmul (qeps k) (width qs))) := by
  intro k
  have hp : ∀ q, List.Mem q qs → ∃ N, ∀ n, N ≤ n → ∀ wt, List.Mem wt q.fine →
      qle (qsub q.lo (qeps k)) (evalN n (upd p i wt.2) e) ∧ qle (evalN n (upd p i wt.2) e) (qadd q.hi (qeps k)) := by
    intro q hq
    have ⟨hleaf, _, htags⟩ := h q hq
    exact ev_list _ q.fine (fun wt hm => hleaf wt.2 (htags wt hm).1 (htags wt hm).2 k)
  obtain ⟨N, hN⟩ := ev_list _ qs hp
  refine ⟨N, fun n hn => ?_⟩
  have enc := enclosure_sound qSum (fun t => evalN n (upd p i t) e) (qs.map (widen k)) (by
    intro q' hq'
    obtain ⟨q, hq, he⟩ := mem_widen hq'
    subst he
    exact ⟨(h q hq).2.1, fun wt hm => hN n hn q hq wt hm⟩)
  rw [total_widen] at enc
  exact ⟨qle_respects (lower_widen k qs) (qEq_refl _) enc.1, qle_respects (qEq_refl _) (upper_widen k qs) enc.2⟩

/-! ## Nonvacuity -/

/-- `∫_0^1 x dx` with one piece, the value reading `[0, 1]` over the box `[0, 1]`, one tag `1/2` of weight `1`:
the hypotheses of `enclosure_R` are met. -/
example : ∀ q, List.Mem q [(⟨qzero, qone, qzero, qone, [(qone, qeps 1)]⟩ : Piece QExpr)] →
    PieceR (.var 0) (fun _ => qzero) 0 q := by
  intro q hq
  cases hq with
  | head =>
      refine ⟨interval_leaf (B := fun _ => (qzero, qone)) (VRead.var (by decide) (by decide))
        (inbox_upd (fun j _ => ⟨by decide, by decide⟩) (by decide) (by decide)), ⟨?_, by show qle (qadd qone qzero) (qadd qone (qneg qzero)); decide,
          by show qle (qadd qone (qneg qzero)) (qadd qone qzero); decide⟩, ?_⟩
      · intro wt hm
        cases hm with
        | head => show qle qzero qone; decide
        | tail _ hm => cases hm
      · intro wt hm
        cases hm with
        | head => exact ⟨by decide, by decide⟩
        | tail _ hm => cases hm
  | tail _ hq => cases hq

end ZIntegralR

#print axioms ZIntegralR.qSum
#print axioms ZIntegralR.inbox_upd
#print axioms ZIntegralR.interval_leaf
#print axioms ZIntegralR.slope_at
#print axioms ZIntegralR.monotone_leaf_up
#print axioms ZIntegralR.monotone_leaf_down
#print axioms ZIntegralR.lower_widen
#print axioms ZIntegralR.upper_widen
#print axioms ZIntegralR.ev_list
#print axioms ZIntegralR.enclosure_R
