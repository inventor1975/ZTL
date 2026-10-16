import ZIntegralT

/-!
# ZTransfer — from symmetric tagged sums to every tagged sum, for a Lipschitz integrand. Zero axioms.

`ZIntegralT.taylor2_leaf` bounds the SYMMETRIC tagged sums of a piece. `zintegral.py` claims every Riemann sum. The
classical bridge: two tagged sums over partitions of the same interval differ by at most `B·(β − α)` when the
integrand moves by at most `B` between the tags of any two overlapping cells — and a Lipschitz integrand (which the
first-order reading certifies) moves by at most `K·(μ_P + μ_Q)` there. The proof is the common refinement, written
as a double sum over pairs of cells weighted by their overlap `ov(c, d) = |c ∩ d|`:

    Σ_c w_c·f(t_c) − Σ_d w_d·f(t_d) = Σ_c Σ_d ov(c, d)·(f(t_c) − f(t_d))

because the overlaps of one cell with a partition add up to its width (`ov_chain`). The overlap is a difference of
CLIPS, `ov([a, b], [x, y]) = clip(b) − clip(a)`, `clip(t) = min(max(t, x), y)`, so its additivity along a partition
is a pointwise identity (`clip_split`).
-/

namespace ZTransfer

open VR.Numbers ZCertify ZSlope ZExp ZSlopeExp ZRecip ZLn ZSqrt ZSlopeSqrt ZExp2 ZTaylor2 ZIntegralR ZIntegralT

/-! ## `min`, `max`, the clip -/

def qmin (x y : QExpr) : QExpr :=
  match qle.decidable x y with
  | .isTrue _ => x
  | .isFalse _ => y

def qmax (x y : QExpr) : QExpr :=
  match qle.decidable x y with
  | .isTrue _ => y
  | .isFalse _ => x

theorem qmin_spec (x y : QExpr) : (qle x y ∧ qmin x y = x) ∨ (qle y x ∧ qmin x y = y) := by
  unfold qmin
  cases qle.decidable x y with
  | isTrue h => exact Or.inl ⟨h, rfl⟩
  | isFalse h =>
      exact Or.inr ⟨by cases qle_total x y with
        | inl h' => exact absurd h' h
        | inr h' => exact h', rfl⟩

theorem qmax_spec (x y : QExpr) : (qle x y ∧ qmax x y = y) ∨ (qle y x ∧ qmax x y = x) := by
  unfold qmax
  cases qle.decidable x y with
  | isTrue h => exact Or.inl ⟨h, rfl⟩
  | isFalse h =>
      exact Or.inr ⟨by cases qle_total x y with
        | inl h' => exact absurd h' h
        | inr h' => exact h', rfl⟩

theorem eq_qEq {a b : QExpr} (h : a = b) : qEq a b := h ▸ qEq_refl a

theorem qmin_l {x y : QExpr} (h : qle x y) : qEq (qmin x y) x := by
  rcases qmin_spec x y with ⟨_, e⟩ | ⟨h', e⟩
  · exact eq_qEq e
  · have := eq_qEq e; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem qmin_r {x y : QExpr} (h : qle y x) : qEq (qmin x y) y := by
  rcases qmin_spec x y with ⟨h', e⟩ | ⟨_, e⟩
  · have := eq_qEq e; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · exact eq_qEq e

theorem qmax_r {x y : QExpr} (h : qle x y) : qEq (qmax x y) y := by
  rcases qmax_spec x y with ⟨_, e⟩ | ⟨h', e⟩
  · exact eq_qEq e
  · have := eq_qEq e; exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem qmax_l {x y : QExpr} (h : qle y x) : qEq (qmax x y) x := by
  rcases qmax_spec x y with ⟨h', e⟩ | ⟨_, e⟩
  · have := eq_qEq e; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · exact eq_qEq e

/-- `t` clipped into `[x, y]`. -/
def clip (x y t : QExpr) : QExpr := qmin (qmax t x) y

/-- The three outcomes of the clip, `x ≤ y`. -/
theorem clip_cases {x y t : QExpr} (hxy : qle x y) :
    (qle t x ∧ qEq (clip x y t) x) ∨ (qle x t ∧ qle t y ∧ qEq (clip x y t) t) ∨ (qle y t ∧ qEq (clip x y t) y) := by
  unfold clip
  cases qle_total t x with
  | inl h =>
      have e1 := qmax_r h
      have e2 := qmin_l (x := qmax t x) (y := y) (by rat_linarith)
      exact Or.inl ⟨h, qEq_trans e2 e1⟩
  | inr h =>
      have e1 := qmax_l h
      cases qle_total t y with
      | inl h' =>
          have e2 := qmin_l (x := qmax t x) (y := y) (by rat_linarith)
          exact Or.inr (Or.inl ⟨h, h', qEq_trans e2 e1⟩)
      | inr h' =>
          have e2 := qmin_r (x := qmax t x) (y := y) (by rat_linarith)
          exact Or.inr (Or.inr ⟨h', e2⟩)

theorem clip_in {x y t : QExpr} (hxy : qle x y) : qle x (clip x y t) ∧ qle (clip x y t) y := by
  have C := clip_cases (t := t) hxy
  generalize clip x y t = c at *
  rcases C with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;> exact ⟨by rat_linarith, by rat_linarith⟩

theorem clip_mono {x y s t : QExpr} (hxy : qle x y) (hst : qle s t) : qle (clip x y s) (clip x y t) := by
  have C1 := clip_cases (t := s) hxy
  have C2 := clip_cases (t := t) hxy
  generalize clip x y s = c1 at *
  generalize clip x y t = c2 at *
  rcases C1 with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;>
    rcases C2 with ⟨c, f⟩ | ⟨c, d, f⟩ | ⟨c, f⟩ <;> rat_linarith

theorem clip_lo {x y t : QExpr} (hxy : qle x y) (h : qle t x) : qEq (clip x y t) x := by
  have C := clip_cases (t := t) hxy
  generalize clip x y t = c at *
  rcases C with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩
  · exact e
  · exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem clip_mid {x y t : QExpr} (h1 : qle x t) (h2 : qle t y) : qEq (clip x y t) t := by
  have C := clip_cases (t := t) (qle_trans h1 h2)
  generalize clip x y t = c at *
  rcases C with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩
  · exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · exact e
  · exact qle_antisymm (by rat_linarith) (by rat_linarith)

theorem clip_hi {x y t : QExpr} (hxy : qle x y) (h : qle y t) : qEq (clip x y t) y := by
  have C := clip_cases (t := t) hxy
  generalize clip x y t = c at *
  rcases C with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩
  · exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · exact e

/-- THE SPLIT: `x ≤ z ≤ y` — `clip_[x,y](t) = clip_[x,z](t) + clip_[z,y](t) − z`. -/
theorem clip_split {x y z t : QExpr} (hxz : qle x z) (hzy : qle z y) :
    qEq (clip x y t) (qsub (qadd (clip x z t) (clip z y t)) z) := by
  have hxy := qle_trans hxz hzy
  unfold qsub
  cases qle_total t x with
  | inl h =>
      have e1 := clip_lo hxy h; have e2 := clip_lo hxz h; have e3 := clip_lo hzy (qle_trans h hxz)
      generalize clip x y t = c1 at *; generalize clip x z t = c2 at *; generalize clip z y t = c3 at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | inr hx =>
      cases qle_total t z with
      | inl h =>
          have e1 := clip_mid hx (qle_trans h hzy); have e2 := clip_mid hx h; have e3 := clip_lo hzy h
          generalize clip x y t = c1 at *; generalize clip x z t = c2 at *; generalize clip z y t = c3 at *
          exact qle_antisymm (by rat_linarith) (by rat_linarith)
      | inr hz =>
          cases qle_total t y with
          | inl h =>
              have e1 := clip_mid hx h; have e2 := clip_hi hxz hz; have e3 := clip_mid hz h
              generalize clip x y t = c1 at *; generalize clip x z t = c2 at *; generalize clip z y t = c3 at *
              exact qle_antisymm (by rat_linarith) (by rat_linarith)
          | inr hy =>
              have e1 := clip_hi hxy hy; have e2 := clip_hi hxz (qle_trans hzy hy); have e3 := clip_hi hzy hy
              generalize clip x y t = c1 at *; generalize clip x z t = c2 at *; generalize clip z y t = c3 at *
              exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The clip respects equality of its ends. -/
theorem clip_respects {x x' y y' t : QExpr} (hx : qEq x x') (hy : qEq y y') (hxy : qle x y) :
    qEq (clip x y t) (clip x' y' t) := by
  have hxy' : qle x' y' := qle_respects hx hy hxy
  have C1 := clip_cases (t := t) hxy
  have C2 := clip_cases (t := t) hxy'
  generalize clip x y t = c1 at *
  generalize clip x' y' t = c2 at *
  rcases C1 with ⟨a, e⟩ | ⟨a, b, e⟩ | ⟨a, e⟩ <;>
    rcases C2 with ⟨c, f⟩ | ⟨c, d, f⟩ | ⟨c, f⟩ <;>
    exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- Reflection: `clip_[m − b, m − a](t) = m − clip_[a, b](m − t)`. -/
theorem clip_reflect {a b m t : QExpr} (hab : qle a b) :
    qEq (clip (qsub m b) (qsub m a) t) (qsub m (clip a b (qsub m t))) := by
  have h' : qle (qsub m b) (qsub m a) := by unfold qsub; rat_linarith
  have C1 := clip_cases (t := t) h'
  have C2 := clip_cases (t := qsub m t) hab
  generalize clip (qsub m b) (qsub m a) t = c1 at *
  generalize clip a b (qsub m t) = c2 at *
  unfold qsub at *
  rcases C1 with ⟨c, f⟩ | ⟨c, d, f⟩ | ⟨c, f⟩ <;>
    rcases C2 with ⟨g, k⟩ | ⟨g, l, k⟩ | ⟨g, k⟩ <;>
    exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- Shift: `clip_[m + a, m + b](t) = m + clip_[a, b](t − m)`. -/
theorem clip_shift {a b m t : QExpr} (hab : qle a b) :
    qEq (clip (qadd m a) (qadd m b) t) (qadd m (clip a b (qsub t m))) := by
  have h' : qle (qadd m a) (qadd m b) := by rat_linarith
  have C1 := clip_cases (t := t) h'
  have C2 := clip_cases (t := qsub t m) hab
  generalize clip (qadd m a) (qadd m b) t = c1 at *
  generalize clip a b (qsub t m) = c2 at *
  unfold qsub at *
  rcases C1 with ⟨c, f⟩ | ⟨c, d, f⟩ | ⟨c, f⟩ <;>
    rcases C2 with ⟨g, k⟩ | ⟨g, l, k⟩ | ⟨g, k⟩ <;>
    exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## Overlaps and sums over cells -/

/-- `|[a, b] ∩ [x, y]|` (for `a ≤ b`, `x ≤ y`). -/
def ov (a b x y : QExpr) : QExpr := qsub (clip x y b) (clip x y a)

/-- `Σ g(cell)` over a list. -/
def lsum (g : Cell → QExpr) : List Cell → QExpr
  | [] => qzero
  | c :: cs => qadd (g c) (lsum g cs)

theorem lsum_congr {g g' : Cell → QExpr} : ∀ cs : List Cell, (∀ c, List.Mem c cs → qEq (g c) (g' c)) →
    qEq (lsum g cs) (lsum g' cs)
  | [], _ => qEq_refl _
  | c :: cs, h => qadd_respects (h c (List.Mem.head cs)) (lsum_congr cs (fun z hz => h z (List.Mem.tail c hz)))

theorem lsum_mono {g g' : Cell → QExpr} : ∀ cs : List Cell, (∀ c, List.Mem c cs → qle (g c) (g' c)) →
    qle (lsum g cs) (lsum g' cs)
  | [], _ => qle_refl _
  | c :: cs, h => by
      have a := h c (List.Mem.head cs)
      have b := lsum_mono cs (fun z hz => h z (List.Mem.tail c hz))
      show qle (qadd (g c) (lsum g cs)) (qadd (g' c) (lsum g' cs)); rat_linarith

theorem lsum_add (g g' : Cell → QExpr) : ∀ cs : List Cell,
    qEq (lsum (fun c => qadd (g c) (g' c)) cs) (qadd (lsum g cs) (lsum g' cs))
  | [] => by show qEq qzero (qadd qzero qzero); rat_ring
  | c :: cs => by
      have ih := lsum_add g g' cs
      show qEq (qadd (qadd (g c) (g' c)) (lsum (fun c => qadd (g c) (g' c)) cs))
        (qadd (qadd (g c) (lsum g cs)) (qadd (g' c) (lsum g' cs)))
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (by rat_ring)

theorem lsum_scale (k : QExpr) (g : Cell → QExpr) : ∀ cs : List Cell,
    qEq (lsum (fun c => qmul k (g c)) cs) (qmul k (lsum g cs))
  | [] => by show qEq qzero (qmul k qzero); rat_ring
  | c :: cs => by
      have ih := lsum_scale k g cs
      show qEq (qadd (qmul k (g c)) (lsum (fun c => qmul k (g c)) cs)) (qmul k (qadd (g c) (lsum g cs)))
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (by rat_ring)

theorem lsum_zero : ∀ Q : List Cell, qEq (lsum (fun _ => qzero) Q) qzero
  | [] => qEq_refl _
  | d :: Q => by
      have ih := lsum_zero Q
      show qEq (qadd qzero (lsum (fun _ => qzero) Q)) qzero
      exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- The double sum may be taken in either order. -/
theorem lsum_swap (g : Cell → Cell → QExpr) : ∀ P Q : List Cell,
    qEq (lsum (fun c => lsum (fun d => g c d) Q) P) (lsum (fun d => lsum (fun c => g c d) P) Q)
  | [], Q => qEq_symm (lsum_zero Q)
  | c :: P, Q => by
      have ih := lsum_swap g P Q
      have a := lsum_add (fun d => g c d) (fun d => lsum (fun c => g c d) P) Q
      show qEq (qadd (lsum (fun d => g c d) Q) (lsum (fun c => lsum (fun d => g c d) Q) P))
        (lsum (fun d => qadd (g c d) (lsum (fun c => g c d) P)) Q)
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (qEq_symm a)

/-- A chain's cells are ordered: `x ≤ y`. -/
theorem chain_le : ∀ (cs : List Cell) (x y : QExpr), Chain x y cs → (∀ c, List.Mem c cs → qle c.1 c.2.1) → qle x y
  | [], x, y, h, _ => qle_of_qEq h
  | (a, b, s) :: cs, x, y, h, hc => by
      have h1 : qEq a x := h.1
      have ab : qle a b := hc (a, b, s) (List.Mem.head cs)
      have ih := chain_le cs b y h.2 (fun z hz => hc z (List.Mem.tail _ hz))
      rat_linarith

/-- The clip respects equality of the point. -/
theorem clip_respects_t {x y s t : QExpr} (hxy : qle x y) (h : qEq s t) : qEq (clip x y s) (clip x y t) := by
  cases qle_total t x with
  | inl hl =>
      have e1 := clip_lo hxy (by rat_linarith : qle s x); have e2 := clip_lo hxy hl
      generalize clip x y s = u at *; generalize clip x y t = v at *
      exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | inr hx =>
      cases qle_total t y with
      | inl hy =>
          have e1 := clip_mid (by rat_linarith : qle x s) (by rat_linarith : qle s y); have e2 := clip_mid hx hy
          generalize clip x y s = u at *; generalize clip x y t = v at *
          exact qle_antisymm (by rat_linarith) (by rat_linarith)
      | inr hy =>
          have e1 := clip_hi hxy (by rat_linarith : qle y s); have e2 := clip_hi hxy hy
          generalize clip x y s = u at *; generalize clip x y t = v at *
          exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- TELESCOPE: along a chain from `α` to `β`, `Σ_c ov(c, [x, y]) = ov([α, β], [x, y])`. -/
theorem ov_telescope {x y : QExpr} (hxy : qle x y) : ∀ (cs : List Cell) (α β : QExpr), Chain α β cs →
    qEq (lsum (fun c => ov c.1 c.2.1 x y) cs) (ov α β x y)
  | [], α, β, h => by
      have e := clip_respects_t (x := x) (y := y) hxy (h : qEq α β)
      show qEq qzero (qsub (clip x y β) (clip x y α))
      generalize clip x y α = u at *; generalize clip x y β = v at *
      unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | (a, b, s) :: cs, α, β, h => by
      have e := clip_respects_t (x := x) (y := y) hxy (h.1 : qEq a α)
      have ih := ov_telescope hxy cs b β h.2
      show qEq (qadd (ov a b x y) (lsum (fun c => ov c.1 c.2.1 x y) cs)) (ov α β x y)
      unfold ov at *
      generalize lsum (fun c => ov c.1 c.2.1 x y) cs = L at *
      generalize clip x y a = ca at *; generalize clip x y b = cb at *; generalize clip x y α = cα at *
      generalize clip x y β = cβ at *
      unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- ADDITIVITY: over a chain from `x` to `y` (cells ordered), `Σ_d ov([a, b], d) = ov([a, b], [x, y])`. -/
theorem ov_chain {a b : QExpr} : ∀ (cs : List Cell) (x y : QExpr), Chain x y cs → (∀ c, List.Mem c cs → qle c.1 c.2.1) →
    qEq (lsum (fun d => ov a b d.1 d.2.1) cs) (ov a b x y)
  | [], x, y, h, _ => by
      have hxy : qEq x y := h
      show qEq qzero (qsub (clip x y b) (clip x y a))
      have i1 := clip_in (t := a) (qle_of_qEq hxy)
      have i2 := clip_in (t := b) (qle_of_qEq hxy)
      generalize clip x y a = u at *; generalize clip x y b = v at *
      obtain ⟨u1, u2⟩ := i1; obtain ⟨v1, v2⟩ := i2
      unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  | (a1, b1, s1) :: cs, x, y, h, hc => by
      have ha : qEq a1 x := h.1
      have hab : qle a1 b1 := hc (a1, b1, s1) (List.Mem.head cs)
      have hcs := fun z hz => hc z (List.Mem.tail (a1, b1, s1) hz)
      have ih := ov_chain (a := a) (b := b) cs b1 y h.2 hcs
      have hby := chain_le cs b1 y h.2 hcs
      have hxb : qle x b1 := by rat_linarith
      have r1 := clip_respects (t := a) ha (qEq_refl b1) hab
      have r2 := clip_respects (t := b) ha (qEq_refl b1) hab
      have sa := clip_split (t := a) hxb hby
      have sb := clip_split (t := b) hxb hby
      show qEq (qadd (ov a b a1 b1) (lsum (fun d => ov a b d.1 d.2.1) cs)) (ov a b x y)
      unfold ov at *
      generalize lsum (fun d => ov a b d.1 d.2.1) cs = L at *
      generalize clip a1 b1 a = p1 at *; generalize clip a1 b1 b = p2 at *
      generalize clip x b1 a = q1 at *; generalize clip x b1 b = q2 at *
      generalize clip b1 y a = r1' at *; generalize clip b1 y b = r2' at *
      generalize clip x y a = z1 at *; generalize clip x y b = z2 at *
      unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## The transfer, at a fixed index -/

/-- The tagged sum `Σ (b − a)·F(s)`. -/
def tsum (F : QExpr → QExpr) (cs : List Cell) : QExpr := lsum (fun c => qmul (qsub c.2.1 c.1) (F c.2.2)) cs

/-- A cell inside `[α, β]` overlaps it by its own width. -/
theorem ov_inside {a b α β : QExpr} (hab : qle a b) (ha : qle α a) (hb : qle b β) :
    qEq (ov a b α β) (qsub b a) := by
  have e1 := clip_mid ha (qle_trans hab hb)
  have e2 := clip_mid (qle_trans ha hab) hb
  unfold ov; generalize clip α β a = u at *; generalize clip α β b = v at *
  unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- `[α, β]` overlaps a cell inside it by the cell's width. -/
theorem ov_around {a b α β : QExpr} (hab : qle a b) (ha : qle α a) (hb : qle b β) :
    qEq (ov α β a b) (qsub b a) := by
  have e1 := clip_lo hab ha
  have e2 := clip_hi hab hb
  unfold ov; generalize clip a b α = u at *; generalize clip a b β = v at *
  unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- Overlap is never negative; it vanishes for cells apart. -/
theorem ov_facts {a b x y : QExpr} (hab : qle a b) (hxy : qle x y) :
    qle qzero (ov a b x y) ∧ (qle b x → qEq (ov a b x y) qzero) ∧ (qle y a → qEq (ov a b x y) qzero) := by
  have m := clip_mono (s := a) (t := b) hxy hab
  refine ⟨by unfold ov qsub; rat_linarith, fun h => ?_, fun h => ?_⟩
  · have e1 := clip_lo hxy h; have e2 := clip_lo hxy (qle_trans hab h)
    unfold ov; generalize clip x y a = u at *; generalize clip x y b = v at *
    unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  · have e1 := clip_hi hxy h; have e2 := clip_hi hxy (qle_trans h hab)
    unfold ov; generalize clip x y a = u at *; generalize clip x y b = v at *
    unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- One pair of cells: `ov(c, d)·X ≤ ov(c, d)·B` when `X ≤ B` holds for cells that touch. -/
theorem pair_bound {X B : QExpr} (c d : Cell) (hc : qle c.1 c.2.1) (hd : qle d.1 d.2.1)
    (hB : qle d.1 c.2.1 → qle c.1 d.2.1 → qle X B) :
    qle (qmul (ov c.1 c.2.1 d.1 d.2.1) X) (qmul (ov c.1 c.2.1 d.1 d.2.1) B) := by
  obtain ⟨o0, z1, z2⟩ := ov_facts hc hd
  cases qle_total c.2.1 d.1 with
  | inl h =>
      have e := z1 h
      have a1 := mul_qeq_zero (y := X) e
      have a2 := mul_qeq_zero (y := B) e
      rat_linarith
  | inr h =>
      cases qle_total d.2.1 c.1 with
      | inl h' =>
          have e := z2 h'
          have a1 := mul_qeq_zero (y := X) e
          have a2 := mul_qeq_zero (y := B) e
          rat_linarith
      | inr h' => exact scale_l (hB h h') o0

/-- THE TRANSFER, AT A FIXED INDEX. `P` a chain from `α` to `β`, `Q` cells inside `[α, β]` that cover it (each cell of
`P` is overlapped by `Q`'s cells exactly by its width), tags inside their cells; `F` moves by at most `B` between the
tags of touching cells. Then the two tagged sums differ by at most `B·(β − α)`. -/
theorem transfer (F : QExpr → QExpr) {α β B : QExpr} (P Q : List Cell) (hP : Chain α β P)
    (hPo : ∀ c, List.Mem c P → qle c.1 c.2.1) (hPin : ∀ c, List.Mem c P → qle α c.1 ∧ qle c.2.1 β)
    (hQo : ∀ d, List.Mem d Q → qle d.1 d.2.1) (hQin : ∀ d, List.Mem d Q → qle α d.1 ∧ qle d.2.1 β)
    (hQcov : ∀ c, List.Mem c P → qEq (lsum (fun d => ov c.1 c.2.1 d.1 d.2.1) Q) (ov c.1 c.2.1 α β))
    (hB : ∀ c, List.Mem c P → ∀ d, List.Mem d Q → qle d.1 c.2.1 → qle c.1 d.2.1 →
      qle (qsub (F c.2.2) (F d.2.2)) B ∧ qle (qsub (F d.2.2) (F c.2.2)) B) :
    qle (qsub (tsum F P) (tsum F Q)) (qmul B (qsub β α)) ∧ qle (qsub (tsum F Q) (tsum F P)) (qmul B (qsub β α)) := by
  -- Σ_P = Σ_c Σ_d ov(c, d)·F(t_c)
  have SP : qEq (tsum F P) (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q) P) := by
    unfold tsum
    refine lsum_congr P (fun c hc => ?_)
    have w := ov_inside (hPo c hc) (hPin c hc).1 (hPin c hc).2
    have cov := hQcov c hc
    have sc := lsum_scale (F c.2.2) (fun d => ov c.1 c.2.1 d.1 d.2.1) Q
    have e1 : qEq (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q)
        (lsum (fun d => qmul (F c.2.2) (ov c.1 c.2.1 d.1 d.2.1)) Q) := lsum_congr Q (fun d _ => qmul_comm _ _)
    have e2 := qmul_respects (qEq_refl (F c.2.2)) (qEq_trans cov w)
    have e3 := qmul_comm (F c.2.2) (qsub c.2.1 c.1)
    exact qEq_symm (qEq_trans e1 (qEq_trans sc (qEq_trans e2 e3)))
  -- Σ_Q = Σ_d Σ_c ov(c, d)·F(t_d) = Σ_c Σ_d ov(c, d)·F(t_d)
  have SQ : qEq (tsum F Q) (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q) P) := by
    have sw := lsum_swap (fun c d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) P Q
    refine qEq_trans ?_ (qEq_symm sw)
    unfold tsum
    refine lsum_congr Q (fun d hd => ?_)
    have w := ov_around (hQo d hd) (hQin d hd).1 (hQin d hd).2
    have tel := ov_telescope (hQo d hd) P α β hP
    have sc := lsum_scale (F d.2.2) (fun c => ov c.1 c.2.1 d.1 d.2.1) P
    have e1 : qEq (lsum (fun c => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) P)
        (lsum (fun c => qmul (F d.2.2) (ov c.1 c.2.1 d.1 d.2.1)) P) := lsum_congr P (fun c _ => qmul_comm _ _)
    have e2 := qmul_respects (qEq_refl (F d.2.2)) (qEq_trans tel w)
    have e3 := qmul_comm (F d.2.2) (qsub d.2.1 d.1)
    exact qEq_symm (qEq_trans e1 (qEq_trans sc (qEq_trans e2 e3)))
  -- Σ_c Σ_d ov(c, d)·B = B·(β − α)
  have SB : qEq (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) B) Q) P) (qmul B (qsub β α)) := by
    have e1 : qEq (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) B) Q) P)
        (lsum (fun c => qmul B (ov c.1 c.2.1 α β)) P) := lsum_congr P (fun c hc => by
      have e := lsum_congr (g := fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) B) (g' := fun d => qmul B (ov c.1 c.2.1 d.1 d.2.1)) Q
        (fun d _ => qmul_comm _ _)
      exact qEq_trans e (qEq_trans (lsum_scale B _ Q) (qmul_respects (qEq_refl B) (hQcov c hc))))
    have hαβ := chain_le P α β hP hPo
    have tel := ov_telescope hαβ P α β hP
    have e2 := lsum_scale B (fun c => ov c.1 c.2.1 α β) P
    have e3 := qmul_respects (qEq_refl B) (qEq_trans tel (ov_inside hαβ (qle_refl α) (qle_refl β)))
    exact qEq_trans e1 (qEq_trans e2 e3)
  -- the difference, pair by pair
  have D1 : qEq (qsub (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q) P)
      (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q) P))
      (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F c.2.2) (F d.2.2))) Q) P) := by
    have a := lsum_add (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q)
      (fun c => qneg (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q)) P
    have b := lsum_scale (qneg qone) (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q) P
    have c1 : qEq (lsum (fun c => qmul (qneg qone) (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q)) P)
        (lsum (fun c => qneg (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q)) P) :=
      lsum_congr P (fun c _ => by rat_ring)
    have c2 : qEq (lsum (fun c => qadd (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q)
          (qneg (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q))) P)
        (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F c.2.2) (F d.2.2))) Q) P) :=
      lsum_congr P (fun c _ => by
        have a' := lsum_add (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2))
          (fun d => qmul (qneg qone) (qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2))) Q
        have b' := lsum_scale (qneg qone) (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q
        have c' : qEq (lsum (fun d => qadd (qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2))
              (qmul (qneg qone) (qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)))) Q)
            (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F c.2.2) (F d.2.2))) Q) :=
          lsum_congr Q (fun d _ => by unfold qsub; rat_ring)
        generalize lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q = X at *
        generalize lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q = Y at *
        generalize lsum (fun d => qmul (qneg qone) (qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2))) Q = Z at *
        generalize lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F c.2.2) (F d.2.2))) Q = W at *
        generalize lsum (fun d => qadd (qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2))
              (qmul (qneg qone) (qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)))) Q = V at *
        exact qle_antisymm (by rat_linarith) (by rat_linarith))
    generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q) P = X at *
    generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q) P = Y at *
    generalize lsum (fun c => qneg (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q)) P = Z at *
    generalize lsum (fun c => qmul (qneg qone) (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q)) P = Z' at *
    generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F c.2.2) (F d.2.2))) Q) P = W at *
    generalize lsum (fun c => qadd (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q)
          (qneg (lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q))) P = V at *
    unfold qsub; exact qle_antisymm (by rat_linarith) (by rat_linarith)
  have M1 := lsum_mono P (fun c hc => lsum_mono Q (fun d hd =>
    pair_bound (X := qsub (F c.2.2) (F d.2.2)) (B := B) c d (hPo c hc) (hQo d hd) (fun h1 h2 => (hB c hc d hd h1 h2).1)))
  have M2 := lsum_mono P (fun c hc => lsum_mono Q (fun d hd =>
    pair_bound (X := qsub (F d.2.2) (F c.2.2)) (B := B) c d (hPo c hc) (hQo d hd) (fun h1 h2 => (hB c hc d hd h1 h2).2)))
  have N : qEq (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F d.2.2) (F c.2.2))) Q) P)
      (qmul (qneg qone) (lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F c.2.2) (F d.2.2))) Q) P)) := by
    refine qEq_trans (lsum_congr P (fun c _ => ?_)) (lsum_scale (qneg qone) _ P)
    exact qEq_trans (lsum_congr Q (fun d _ => by unfold qsub; rat_ring)) (lsum_scale (qneg qone) _ Q)
  simp only [] at M1 M2
  generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F c.2.2)) Q) P = X at *
  generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (F d.2.2)) Q) P = Y at *
  generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F c.2.2) (F d.2.2))) Q) P = W at *
  generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) (qsub (F d.2.2) (F c.2.2))) Q) P = W' at *
  generalize lsum (fun c => lsum (fun d => qmul (ov c.1 c.2.1 d.1 d.2.1) B) Q) P = Z at *
  generalize tsum F P = TP at *
  generalize tsum F Q = TQ at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

/-! ## The symmetric sum as a tagged sum over two mirrored chains -/

def rcell (m : QExpr) (c : Cell) : Cell := (qadd m c.1, qadd m c.2.1, qadd m c.2.2)
def lcell (m : QExpr) (c : Cell) : Cell := (qsub m c.2.1, qsub m c.1, qsub m c.2.2)

/-- The two mirrored halves of a half-chain. -/
def mirror (m : QExpr) (cs : List Cell) : List Cell := cs.map (rcell m) ++ cs.map (lcell m)

theorem lsum_append (g : Cell → QExpr) : ∀ (xs ys : List Cell),
    qEq (lsum g (xs ++ ys)) (qadd (lsum g xs) (lsum g ys))
  | [], ys => by show qEq (lsum g ys) (qadd qzero (lsum g ys)); rat_ring
  | x :: xs, ys => by
      have ih := lsum_append g xs ys
      show qEq (qadd (g x) (lsum g (xs ++ ys))) (qadd (qadd (g x) (lsum g xs)) (lsum g ys))
      exact qEq_trans (qadd_respects (qEq_refl _) ih) (by rat_ring)

theorem lsum_map (g : Cell → QExpr) (f : Cell → Cell) : ∀ cs : List Cell,
    lsum g (cs.map f) = lsum (fun c => g (f c)) cs
  | [] => rfl
  | c :: cs => by show qadd (g (f c)) (lsum g (cs.map f)) = qadd (g (f c)) (lsum (fun c => g (f c)) cs)
                  rw [lsum_map g f cs]

theorem all_map {P : Cell → Prop} {f : Cell → Cell} : ∀ {cs : List Cell}, (∀ c, List.Mem c cs → P (f c)) →
    ∀ d, List.Mem d (cs.map f) → P d
  | [], _, d, h => by cases h
  | c :: cs, hc, d, h => by
      cases h with
      | head => exact hc c (List.Mem.head cs)
      | tail _ h => exact all_map (fun z hz => hc z (List.Mem.tail c hz)) d h

theorem all_app {P : Cell → Prop} : ∀ {xs ys : List Cell}, (∀ d, List.Mem d xs → P d) → (∀ d, List.Mem d ys → P d) →
    ∀ d, List.Mem d (xs ++ ys) → P d
  | [], ys, _, hy, d, h => hy d h
  | x :: xs, ys, hx, hy, d, h => by
      cases h with
      | head => exact hx x (List.Mem.head xs)
      | tail _ h => exact all_app (fun z hz => hx z (List.Mem.tail x hz)) hy d h

theorem csum_lsum (g : Cell → QExpr) : ∀ cs : List Cell, csum g cs = lsum (fun c => qmul (qsub c.2.1 c.1) (g c)) cs
  | [] => rfl
  | c :: cs => by
      show qadd (qmul (qsub c.2.1 c.1) (g c)) (csum g cs) = qadd (qmul (qsub c.2.1 c.1) (g c)) (lsum _ cs)
      rw [csum_lsum g cs]

/-- The tagged sum over the mirrored chains is the symmetric sum `Σ (b − a)·(F(m + s) + F(m − s))`. -/
theorem tsum_mirror (F : QExpr → QExpr) (m : QExpr) (cs : List Cell) :
    qEq (tsum F (mirror m cs)) (csum (fun c => qadd (F (qadd m c.2.2)) (F (qsub m c.2.2))) cs) := by
  unfold tsum mirror
  have a := lsum_append (fun c => qmul (qsub c.2.1 c.1) (F c.2.2)) (cs.map (rcell m)) (cs.map (lcell m))
  rw [lsum_map, lsum_map] at a
  have b := lsum_add (fun c => qmul (qsub (rcell m c).2.1 (rcell m c).1) (F (rcell m c).2.2))
    (fun c => qmul (qsub (lcell m c).2.1 (lcell m c).1) (F (lcell m c).2.2)) cs
  have c := lsum_congr (g := fun c => qadd (qmul (qsub (rcell m c).2.1 (rcell m c).1) (F (rcell m c).2.2))
      (qmul (qsub (lcell m c).2.1 (lcell m c).1) (F (lcell m c).2.2)))
    (g' := fun c => qmul (qsub c.2.1 c.1) (qadd (F (qadd m c.2.2)) (F (qsub m c.2.2)))) cs
    (fun c _ => by
      show qEq (qadd (qmul (qsub (qadd m c.2.1) (qadd m c.1)) (F (qadd m c.2.2)))
          (qmul (qsub (qsub m c.1) (qsub m c.2.1)) (F (qsub m c.2.2))))
        (qmul (qsub c.2.1 c.1) (qadd (F (qadd m c.2.2)) (F (qsub m c.2.2))))
      unfold qsub; rat_ring)
  rw [csum_lsum]
  exact qEq_trans a (qEq_trans (qEq_symm b) c)

/-- Shifted overlap: `ov(c, [m + a, m + b]) = ov(c − m, [a, b])`. -/
theorem ov_shift {ac bc a b m : QExpr} (hab : qle a b) :
    qEq (ov ac bc (qadd m a) (qadd m b)) (ov (qsub ac m) (qsub bc m) a b) := by
  have e1 := clip_shift (t := ac) (m := m) hab
  have e2 := clip_shift (t := bc) (m := m) hab
  unfold ov
  generalize clip (qadd m a) (qadd m b) ac = u1 at *; generalize clip (qadd m a) (qadd m b) bc = u2 at *
  generalize clip a b (qsub ac m) = v1 at *; generalize clip a b (qsub bc m) = v2 at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- Reflected overlap: `ov(c, [m − b, m − a]) = ov(m − c, [a, b])`. -/
theorem ov_reflect {ac bc a b m : QExpr} (hab : qle a b) :
    qEq (ov ac bc (qsub m b) (qsub m a)) (ov (qsub m bc) (qsub m ac) a b) := by
  have e1 := clip_reflect (t := ac) (m := m) hab
  have e2 := clip_reflect (t := bc) (m := m) hab
  unfold ov
  generalize clip (qsub m b) (qsub m a) ac = u1 at *; generalize clip (qsub m b) (qsub m a) bc = u2 at *
  generalize clip a b (qsub m ac) = v1 at *; generalize clip a b (qsub m bc) = v2 at *
  unfold qsub at *; exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-- THE MIRRORED CHAINS COVER `[m − h, m + h]`: a cell `[ac, bc]` is overlapped by them exactly as by the whole piece. -/
theorem mirror_cover {ac bc m h : QExpr} {cs : List Cell} (hch : Chain qzero h cs) (ho : ∀ c, List.Mem c cs → qle c.1 c.2.1) :
    qEq (lsum (fun d => ov ac bc d.1 d.2.1) (mirror m cs)) (ov ac bc (qsub m h) (qadd m h)) := by
  have h0 : qle qzero h := chain_le cs qzero h hch ho
  unfold mirror
  have a := lsum_append (fun d => ov ac bc d.1 d.2.1) (cs.map (rcell m)) (cs.map (lcell m))
  rw [lsum_map, lsum_map] at a
  -- the right half
  have R1 : qEq (lsum (fun c => ov ac bc (rcell m c).1 (rcell m c).2.1) cs)
      (lsum (fun c => ov (qsub ac m) (qsub bc m) c.1 c.2.1) cs) :=
    lsum_congr cs (fun c hc => ov_shift (ho c hc))
  have R2 := ov_chain (a := qsub ac m) (b := qsub bc m) cs qzero h hch ho
  have R3 := ov_shift (ac := ac) (bc := bc) (m := m) h0
  -- the left half
  have L1 : qEq (lsum (fun c => ov ac bc (lcell m c).1 (lcell m c).2.1) cs)
      (lsum (fun c => ov (qsub m bc) (qsub m ac) c.1 c.2.1) cs) :=
    lsum_congr cs (fun c hc => ov_reflect (ho c hc))
  have L2 := ov_chain (a := qsub m bc) (b := qsub m ac) cs qzero h hch ho
  have L3 := ov_reflect (ac := ac) (bc := bc) (m := m) h0
  -- m + 0 = m = m − 0, and the split at m
  have z1 : qEq (qadd m qzero) m := by rat_ring
  have z2 : qEq (qsub m qzero) m := by unfold qsub; rat_ring
  have hm1 : qle (qsub m h) m := by unfold qsub; rat_linarith
  have hm2 : qle m (qadd m h) := by rat_linarith
  have c1 := clip_respects (t := ac) z1 (qEq_refl (qadd m h)) (by rat_linarith)
  have c2 := clip_respects (t := bc) z1 (qEq_refl (qadd m h)) (by rat_linarith)
  have c3 := clip_respects (t := ac) (qEq_refl (qsub m h)) z2 (by unfold qsub; rat_linarith)
  have c4 := clip_respects (t := bc) (qEq_refl (qsub m h)) z2 (by unfold qsub; rat_linarith)
  have s1 := clip_split (t := ac) hm1 hm2
  have s2 := clip_split (t := bc) hm1 hm2
  unfold ov at *
  generalize lsum (fun d => qsub (clip d.1 d.2.1 bc) (clip d.1 d.2.1 ac)) (List.map (rcell m) cs ++ List.map (lcell m) cs) = S at *
  generalize lsum (fun c => qsub (clip (rcell m c).1 (rcell m c).2.1 bc) (clip (rcell m c).1 (rcell m c).2.1 ac)) cs = SR at *
  generalize lsum (fun c => qsub (clip (lcell m c).1 (lcell m c).2.1 bc) (clip (lcell m c).1 (lcell m c).2.1 ac)) cs = SL at *
  generalize lsum (fun c => qsub (clip c.1 c.2.1 (qsub bc m)) (clip c.1 c.2.1 (qsub ac m))) cs = TR at *
  generalize lsum (fun c => qsub (clip c.1 c.2.1 (qsub m ac)) (clip c.1 c.2.1 (qsub m bc))) cs = TL at *
  generalize clip qzero h (qsub bc m) = a1 at *; generalize clip qzero h (qsub ac m) = a2 at *
  generalize clip qzero h (qsub m ac) = a3 at *; generalize clip qzero h (qsub m bc) = a4 at *
  generalize clip (qadd m qzero) (qadd m h) ac = b1 at *; generalize clip (qadd m qzero) (qadd m h) bc = b2 at *
  generalize clip (qsub m h) (qsub m qzero) ac = b3 at *; generalize clip (qsub m h) (qsub m qzero) bc = b4 at *
  generalize clip m (qadd m h) ac = d1 at *; generalize clip m (qadd m h) bc = d2 at *
  generalize clip (qsub m h) m ac = d3 at *; generalize clip (qsub m h) m bc = d4 at *
  generalize clip (qsub m h) (qadd m h) ac = f1 at *; generalize clip (qsub m h) (qadd m h) bc = f2 at *
  unfold qsub at *
  exact qle_antisymm (by rat_linarith) (by rat_linarith)

/-! ## Every tagged sum of a Taylor piece -/

/-- LIPSCHITZ, FROM THE FIRST-ORDER READING: `−K ≤ l`, `h ≤ K` — from some index on, for every `D ≥ |t − t'|`,
`f(t) − f(t') ≤ K·D + ε_k`. -/
theorem lip_pair {e : G} {p : Point QExpr} {i : Nat} {B : Box QExpr} {l h K t t' : QExpr}
    (r : DRead B i e l h) (hl : qle (qneg K) l) (hh : qle h K) (K0 : qle qzero K)
    (ht : InBox qOrd B (upd p i t)) (ht' : InBox qOrd B (upd p i t')) :
    ∀ k, ∃ N, ∀ n, N ≤ n → ∀ D, qle (qsub t t') D → qle (qsub t' t) D →
      qle (qsub (evalN n (upd p i t) e) (evalN n (upd p i t') e)) (qadd (qmul K D) (qeps k)) := by
  intro k
  cases qle_total t t' with
  | inl h1 =>
      obtain ⟨N, hN⟩ := slope_at r ht ht' h1 k
      refine ⟨N, fun n hn D d1 d2 => ?_⟩
      have g : qle (qsub (qmul l (qsub t' t)) (qeps k)) (qsub (evalN n (upd p i t') e) (evalN n (upd p i t) e)) :=
        (hN n hn).1
      have w0 : qle qzero (qsub t' t) := by unfold qsub; rat_linarith
      have f1 := ZExp.scale (by rat_linarith : qle (qneg K) l) w0
      have f2 := scale_l d2 K0
      have e1 : qEq (qmul (qneg K) (qsub t' t)) (qneg (qmul K (qsub t' t))) := by rat_ring
      unfold qsub at *; rat_linarith
  | inr h1 =>
      obtain ⟨N, hN⟩ := slope_at r ht' ht h1 k
      refine ⟨N, fun n hn D d1 d2 => ?_⟩
      have g : qle (qsub (evalN n (upd p i t) e) (evalN n (upd p i t') e)) (qadd (qmul h (qsub t t')) (qeps k)) :=
        (hN n hn).2
      have w0 : qle qzero (qsub t t') := by unfold qsub; rat_linarith
      have f1 := ZExp.scale hh w0
      have f2 := scale_l d1 K0
      unfold qsub at *; rat_linarith

/-- The cells of an ordered chain lie inside it. -/
theorem chain_within : ∀ (cs : List Cell) (α β : QExpr), Chain α β cs → (∀ c, List.Mem c cs → qle c.1 c.2.1) →
    ∀ c, List.Mem c cs → qle α c.1 ∧ qle c.2.1 β
  | [], _, _, _, _, c, hc => by cases hc
  | (a, b, s) :: cs, α, β, h, ho, c, hc => by
      have ha : qEq a α := h.1
      have hcs := fun z hz => ho z (List.Mem.tail (a, b, s) hz)
      have hby := chain_le cs b β h.2 hcs
      have hab : qle a b := ho (a, b, s) (List.Mem.head cs)
      cases hc with
      | head => exact ⟨by rat_linarith, hby⟩
      | tail _ hc =>
          obtain ⟨u, v⟩ := chain_within cs b β h.2 hcs c hc
          exact ⟨by rat_linarith, v⟩

/-- EVERY TAGGED SUM OF A TAYLOR PIECE. The piece `[m − h, m + h]` with the kernel's readings: second coefficient
`[l, u]` (`|l|, |u| ≤ K`), value at the midpoint `[c0, C0]`, first-order `[l1, h1]` (`|l1|, |h1| ≤ K1`). `P` ANY
tagged chain from `m − h` to `m + h` with mesh `μ`; `Q0` a refinement of `[0, h]` with mesh `μQ` (its mirror is the
symmetric comparison). Then from some index on the tagged sum over `P` lies in
`[L − E, U + E]`, `E = 2K·μQ·h² + 3h·ε_k + (K1·(μ + μQ) + ε_k)·2h` — as the meshes go to `0`, `[L, U]`. -/
theorem taylor2_every {e : G} {p : Point QExpr} {i : Nat} {m h μ μQ t3 K K1 c0 C0 l u l1 h1 : QExpr}
    {B B0 : Box QExpr} {P Q0 : List Cell}
    (hT : T2Read B i e l u) (hD : DRead B i e l1 h1) (hV : VRead B0 e c0 C0) (h0 : InBox qOrd B0 (upd p i m))
    (hB : ∀ t, qle (qsub m h) t → qle t (qadd m h) → InBox qOrd B (upd p i t))
    (hch : Chain qzero h Q0) (hok : ∀ c, List.Mem c Q0 → CellOK μQ c) (hμQ : qle qzero μQ)
    (ht3 : qEq (qmul three t3) (cube h)) (hK0 : qle qzero K)
    (hl1 : qle (qneg K) l) (hl2 : qle l K) (hu1 : qle (qneg K) u) (hu2 : qle u K)
    (hk1 : qle (qneg K1) l1) (hk2 : qle h1 K1) (hk0 : qle qzero K1)
    (hP : Chain (qsub m h) (qadd m h) P) (hPt : ∀ c, List.Mem c P → qle c.1 c.2.2 ∧ qle c.2.2 c.2.1)
    (hPμ : ∀ c, List.Mem c P → qle (qsub c.2.1 c.1) μ) :
    ∀ k, ∃ N, ∀ n, N ≤ n →
      qle (qsub (qsub (qadd (qmul (qadd h h) c0) (qmul (qadd l l) t3))
              (qadd (qmul (qadd K K) (qmul μQ (sq h))) (qmul (qmul three h) (qeps k))))
            (qmul (qadd (qmul K1 (qadd μ μQ)) (qeps k)) (qadd h h)))
          (tsum (fun t => evalN n (upd p i t) e) P) ∧
      qle (tsum (fun t => evalN n (upd p i t) e) P)
          (qadd (qadd (qadd (qmul (qadd h h) C0) (qmul (qadd u u) t3))
              (qadd (qmul (qadd K K) (qmul μQ (sq h))) (qmul (qmul three h) (qeps k))))
            (qmul (qadd (qmul K1 (qadd μ μQ)) (qeps k)) (qadd h h))) := by
  intro k
  have hPo : ∀ c, List.Mem c P → qle c.1 c.2.1 := fun c hc => qle_trans (hPt c hc).1 (hPt c hc).2
  have hPin := chain_within P (qsub m h) (qadd m h) hP hPo
  have hQ0o : ∀ c, List.Mem c Q0 → qle c.1 c.2.1 := fun c hc => qle_trans (hok c hc).2.1 (hok c hc).2.2.1
  obtain ⟨hh0, hQ0in⟩ := cells_within Q0 qzero h hch hok
  -- the mirrored chain's cells: ordered, inside, narrow, tags inside
  have hQo : ∀ d, List.Mem d (mirror m Q0) → qle d.1 d.2.1 :=
    all_app (all_map (fun c hc => by show qle (qadd m c.1) (qadd m c.2.1); have := hQ0o c hc; rat_linarith))
      (all_map (fun c hc => by show qle (qsub m c.2.1) (qsub m c.1); have := hQ0o c hc; unfold qsub; rat_linarith))
  have hQin : ∀ d, List.Mem d (mirror m Q0) → qle (qsub m h) d.1 ∧ qle d.2.1 (qadd m h) :=
    all_app (all_map (fun c hc => by
        show qle (qsub m h) (qadd m c.1) ∧ qle (qadd m c.2.1) (qadd m h)
        have := (hQ0in c hc).1; have := (hQ0in c hc).2; have := hQ0o c hc; unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩))
      (all_map (fun c hc => by
        show qle (qsub m h) (qsub m c.2.1) ∧ qle (qsub m c.1) (qadd m h)
        have := (hQ0in c hc).1; have := (hQ0in c hc).2; have := hQ0o c hc; unfold qsub; exact ⟨by rat_linarith, by rat_linarith⟩))
  have hQμ : ∀ d, List.Mem d (mirror m Q0) → qle d.1 d.2.2 ∧ qle d.2.2 d.2.1 ∧ qle (qsub d.2.1 d.1) μQ :=
    all_app (all_map (fun c hc => by
        show qle (qadd m c.1) (qadd m c.2.2) ∧ qle (qadd m c.2.2) (qadd m c.2.1) ∧ qle (qsub (qadd m c.2.1) (qadd m c.1)) μQ
        obtain ⟨_, a1, a2, a3⟩ := hok c hc; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith, by rat_linarith⟩))
      (all_map (fun c hc => by
        show qle (qsub m c.2.1) (qsub m c.2.2) ∧ qle (qsub m c.2.2) (qsub m c.1) ∧ qle (qsub (qsub m c.1) (qsub m c.2.1)) μQ
        obtain ⟨_, a1, a2, a3⟩ := hok c hc; unfold qsub at *; exact ⟨by rat_linarith, by rat_linarith, by rat_linarith⟩))
  -- the symmetric bound
  obtain ⟨N1, hN1⟩ := taylor2_leaf hT hV h0 hB hch hok hμQ ht3 hK0 hl1 hl2 hu1 hu2 k
  -- Lipschitz for every pair of tags, from some index on
  have tagin : ∀ x, qle (qsub m h) x → qle x (qadd m h) → InBox qOrd B (upd p i x) := hB
  have hpair : ∀ c, List.Mem c P → ∃ N, ∀ n, N ≤ n → ∀ d, List.Mem d (mirror m Q0) →
      ∀ D, qle (qsub c.2.2 d.2.2) D → qle (qsub d.2.2 c.2.2) D →
        qle (qsub (evalN n (upd p i c.2.2) e) (evalN n (upd p i d.2.2) e)) (qadd (qmul K1 D) (qeps k)) ∧
        qle (qsub (evalN n (upd p i d.2.2) e) (evalN n (upd p i c.2.2) e)) (qadd (qmul K1 D) (qeps k)) := by
    intro c hc
    have tc := tagin c.2.2 (qle_trans (hPin c hc).1 (hPt c hc).1) (qle_trans (hPt c hc).2 (hPin c hc).2)
    exact ev_list _ (mirror m Q0) (fun d hd => by
      have td := tagin d.2.2 (qle_trans (hQin d hd).1 (hQμ d hd).1) (qle_trans (hQμ d hd).2.1 (hQin d hd).2)
      obtain ⟨Na, ha⟩ := lip_pair hD hk1 hk2 hk0 tc td k
      obtain ⟨Nb, hb⟩ := lip_pair hD hk1 hk2 hk0 td tc k
      exact ⟨Na + Nb, fun n hn D d1 d2 =>
        ⟨ha n (le_l hn) D d1 d2, hb n (le_r hn) D d2 d1⟩⟩)
  obtain ⟨N2, hN2⟩ := ev_list _ P hpair
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨s1, s2⟩ := hN1 n (le_l hn)
  have lip := hN2 n (le_r hn)
  -- the transfer at index n
  have T := transfer (fun t => evalN n (upd p i t) e) (B := qadd (qmul K1 (qadd μ μQ)) (qeps k)) P (mirror m Q0) hP hPo
    hPin hQo hQin (fun c _ => mirror_cover hch hQ0o)
    (fun c hc d hd t1 t2 => by
      have cμ := hPμ c hc
      have dμ := (hQμ d hd).2.2
      obtain ⟨ct1, ct2⟩ := hPt c hc
      obtain ⟨dt1, dt2, _⟩ := hQμ d hd
      have d1 : qle (qsub c.2.2 d.2.2) (qadd μ μQ) := by unfold qsub at *; rat_linarith
      have d2 : qle (qsub d.2.2 c.2.2) (qadd μ μQ) := by unfold qsub at *; rat_linarith
      exact lip c hc d hd (qadd μ μQ) d1 d2)
  have M := tsum_mirror (fun t => evalN n (upd p i t) e) m Q0
  have W : qEq (qsub (qadd m h) (qsub m h)) (qadd h h) := by unfold qsub; rat_ring
  have W2 := qmul_respects (qEq_refl (qadd (qmul K1 (qadd μ μQ)) (qeps k))) W
  obtain ⟨T1, T2⟩ := T
  simp only [] at T1 T2 M
  unfold ssum at s1 s2
  generalize tsum (fun t => evalN n (upd p i t) e) P = SP at *
  generalize tsum (fun t => evalN n (upd p i t) e) (mirror m Q0) = SQ at *
  generalize csum (fun c => qadd (evalN n (upd p i (qadd m c.2.2)) e) (evalN n (upd p i (qsub m c.2.2)) e)) Q0 = SS at *
  unfold qsub at *
  exact ⟨by rat_linarith, by rat_linarith⟩

end ZTransfer

#print axioms ZTransfer.clip_cases
#print axioms ZTransfer.clip_split
#print axioms ZTransfer.clip_reflect
#print axioms ZTransfer.clip_shift
#print axioms ZTransfer.clip_mono
#print axioms ZTransfer.lsum_swap
#print axioms ZTransfer.ov_telescope
#print axioms ZTransfer.ov_chain
#print axioms ZTransfer.transfer
#print axioms ZTransfer.tsum_mirror
#print axioms ZTransfer.mirror_cover
#print axioms ZTransfer.lip_pair
#print axioms ZTransfer.taylor2_every
