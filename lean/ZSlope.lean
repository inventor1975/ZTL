import ZCertify
import VR.Numbers.RealsOp

/-!
# ZSlope — the derivative sign makes the value monotone, without the mean value theorem. Zero axioms.

`ZCertify` proves the rule the kernel checks a certificate by, GIVEN two premises: the interval reading
encloses the value on a piece (`iv_sound`), and a derivative read with a sign makes the value monotone there
(`deriv_sound`, classically the mean value theorem — real analysis on the top tier of axioms). The curator,
2026-10-10: "без аксиом … на континууме как в VR". This module discharges BOTH premises for the expressions
built from constants, quantities, `+`, `−` and `×`, over VR's operational rationals (`VR.Numbers.QExpr`,
read from VRCycle, not copied), on the empty axiom list.

The route is SLOPES, not the mean value theorem. The kernel reads the derivative of a product as
`U·Dv + V·Du` — value intervals times derivative intervals. The same intervals bound the DIVIDED DIFFERENCE:

    u(p')·v(p') − u(p)·v(p) = u(p')·(v(p') − v(p)) + v(p)·(u(p') − u(p))

exactly, with `u(p') ∈ U` and `v(p) ∈ V`. So, by induction on the expression, a derivative reading `[l, h]` in
quantity `i` gives, for two points of the piece differing only in `i` by `d ≥ 0`,

    l·d ≤ f(p') − f(p) ≤ h·d                                   (`slope_sound`)

— no limit, no intermediate point to choose. `l ≥ 0` then makes `f` non-decreasing in `i` (`mono_up`),
`h ≤ 0` non-increasing (`mono_down`): exactly `ZCertify.Mono`. With `value_sound` (the interval reading
encloses the value) the kernel's certificate rule holds with no premise left (`certificate_sound_E`).

The readings are RELATIONS the kernel's computed intervals must satisfy (each product interval below and
above its four corner products), as in `ZLP`: the kernel brings the numbers, the relation is what it checks.
Functions (`exp`, `ln`) and division are not in this grammar yet — the next steps, on VR's operational reals.
-/

namespace ZSlope

open VR.Numbers ZCertify

/-- VR's operational rationals as a `ZCertify` order (total, decidable — no excluded middle used). -/
def qOrd : ZCertify.Ord QExpr where
  le := qle
  refl := qle_refl
  trans := fun h1 h2 => qle_trans h1 h2
  total := qle_total

/-- Expressions over indexed quantities. -/
inductive E where
  | const : QExpr → E
  | var   : Nat → E
  | add   : E → E → E
  | sub   : E → E → E
  | mul   : E → E → E

def eval (p : Point QExpr) : E → QExpr
  | .const c => c
  | .var i => p i
  | .add u v => qadd (eval p u) (eval p v)
  | .sub u v => qsub (eval p u) (eval p v)
  | .mul u v => qmul (eval p u) (eval p v)

/-- The quantities an expression reads. -/
def Uses : E → Nat → Prop
  | .const _, _ => False
  | .var i, j => j = i
  | .add u v, j => Uses u j ∨ Uses v j
  | .sub u v, j => Uses u j ∨ Uses v j
  | .mul u v, j => Uses u j ∨ Uses v j

/-- The value depends on the quantities it reads only (`ZCertify`'s `dep`). -/
theorem eval_dep (p q : Point QExpr) : ∀ e : E, (∀ j, Uses e j → p j = q j) → eval p e = eval q e
  | .const _, _ => rfl
  | .var i, h => h i rfl
  | .add u v, h => by
      show qadd (eval p u) (eval p v) = qadd (eval q u) (eval q v)
      rw [eval_dep p q u (fun j hj => h j (Or.inl hj)), eval_dep p q v (fun j hj => h j (Or.inr hj))]
  | .sub u v, h => by
      show qsub (eval p u) (eval p v) = qsub (eval q u) (eval q v)
      rw [eval_dep p q u (fun j hj => h j (Or.inl hj)), eval_dep p q v (fun j hj => h j (Or.inr hj))]
  | .mul u v, h => by
      show qmul (eval p u) (eval p v) = qmul (eval q u) (eval q v)
      rw [eval_dep p q u (fun j hj => h j (Or.inl hj)), eval_dep p q v (fun j hj => h j (Or.inr hj))]

/-! ## The four corners bound a product -/

/-- `l` below, `h` above the four corner products of `[a1, a2] × [b1, b2]`. -/
def Corners (l h a1 a2 b1 b2 : QExpr) : Prop :=
  (qle l (qmul a1 b1) ∧ qle l (qmul a1 b2) ∧ qle l (qmul a2 b1) ∧ qle l (qmul a2 b2)) ∧
  (qle (qmul a1 b1) h ∧ qle (qmul a1 b2) h ∧ qle (qmul a2 b1) h ∧ qle (qmul a2 b2) h)

/-- Below the corners is below every product of the box. Cases on given `Or`s (`qle_total`). -/
theorem mul_lo {a1 a2 b1 b2 a b l : QExpr} (ha1 : qle a1 a) (ha2 : qle a a2) (hb1 : qle b1 b)
    (hb2 : qle b b2) (c11 : qle l (qmul a1 b1)) (c12 : qle l (qmul a1 b2)) (c21 : qle l (qmul a2 b1))
    (c22 : qle l (qmul a2 b2)) : qle l (qmul a b) := by
  cases qle_total qzero b with
  | inl hb =>
      -- a1·b ≤ a·b
      have f1 : qle qzero (qmul (qsub a a1) b) := qmul_nonneg (by unfold qsub; rat_linarith) hb
      have e1 : qEq (qmul (qsub a a1) b) (qadd (qmul a b) (qneg (qmul a1 b))) := by unfold qsub; rat_ring
      cases qle_total qzero a1 with
      | inl ha =>
          have f2 : qle qzero (qmul a1 (qsub b b1)) := qmul_nonneg ha (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul a1 (qsub b b1)) (qadd (qmul a1 b) (qneg (qmul a1 b1))) := by
            unfold qsub; rat_ring
          rat_linarith
      | inr ha =>
          have f2 : qle qzero (qmul (qneg a1) (qsub b2 b)) :=
            qmul_nonneg (by rat_linarith) (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul (qneg a1) (qsub b2 b)) (qadd (qmul a1 b) (qneg (qmul a1 b2))) := by
            unfold qsub; rat_ring
          rat_linarith
  | inr hb =>
      -- a2·b ≤ a·b
      have f1 : qle qzero (qmul (qsub a2 a) (qneg b)) :=
        qmul_nonneg (by unfold qsub; rat_linarith) (by rat_linarith)
      have e1 : qEq (qmul (qsub a2 a) (qneg b)) (qadd (qmul a b) (qneg (qmul a2 b))) := by
        unfold qsub; rat_ring
      cases qle_total qzero a2 with
      | inl ha =>
          have f2 : qle qzero (qmul a2 (qsub b b1)) := qmul_nonneg ha (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul a2 (qsub b b1)) (qadd (qmul a2 b) (qneg (qmul a2 b1))) := by
            unfold qsub; rat_ring
          rat_linarith
      | inr ha =>
          have f2 : qle qzero (qmul (qneg a2) (qsub b2 b)) :=
            qmul_nonneg (by rat_linarith) (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul (qneg a2) (qsub b2 b)) (qadd (qmul a2 b) (qneg (qmul a2 b2))) := by
            unfold qsub; rat_ring
          rat_linarith

/-- Above the corners is above every product of the box. -/
theorem mul_hi {a1 a2 b1 b2 a b h : QExpr} (ha1 : qle a1 a) (ha2 : qle a a2) (hb1 : qle b1 b)
    (hb2 : qle b b2) (c11 : qle (qmul a1 b1) h) (c12 : qle (qmul a1 b2) h) (c21 : qle (qmul a2 b1) h)
    (c22 : qle (qmul a2 b2) h) : qle (qmul a b) h := by
  cases qle_total qzero b with
  | inl hb =>
      -- a·b ≤ a2·b
      have f1 : qle qzero (qmul (qsub a2 a) b) := qmul_nonneg (by unfold qsub; rat_linarith) hb
      have e1 : qEq (qmul (qsub a2 a) b) (qadd (qmul a2 b) (qneg (qmul a b))) := by unfold qsub; rat_ring
      cases qle_total qzero a2 with
      | inl ha =>
          have f2 : qle qzero (qmul a2 (qsub b2 b)) := qmul_nonneg ha (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul a2 (qsub b2 b)) (qadd (qmul a2 b2) (qneg (qmul a2 b))) := by
            unfold qsub; rat_ring
          rat_linarith
      | inr ha =>
          have f2 : qle qzero (qmul (qneg a2) (qsub b b1)) :=
            qmul_nonneg (by rat_linarith) (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul (qneg a2) (qsub b b1)) (qadd (qmul a2 b1) (qneg (qmul a2 b))) := by
            unfold qsub; rat_ring
          rat_linarith
  | inr hb =>
      -- a·b ≤ a1·b
      have f1 : qle qzero (qmul (qsub a a1) (qneg b)) :=
        qmul_nonneg (by unfold qsub; rat_linarith) (by rat_linarith)
      have e1 : qEq (qmul (qsub a a1) (qneg b)) (qadd (qmul a1 b) (qneg (qmul a b))) := by
        unfold qsub; rat_ring
      cases qle_total qzero a1 with
      | inl ha =>
          have f2 : qle qzero (qmul a1 (qsub b2 b)) := qmul_nonneg ha (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul a1 (qsub b2 b)) (qadd (qmul a1 b2) (qneg (qmul a1 b))) := by
            unfold qsub; rat_ring
          rat_linarith
      | inr ha =>
          have f2 : qle qzero (qmul (qneg a1) (qsub b b1)) :=
            qmul_nonneg (by rat_linarith) (by unfold qsub; rat_linarith)
          have e2 : qEq (qmul (qneg a1) (qsub b b1)) (qadd (qmul a1 b1) (qneg (qmul a1 b))) := by
            unfold qsub; rat_ring
          rat_linarith

/-! ## The value reading -/

/-- What the kernel checks of an interval reading `[l, h]` of `e` over the piece `B`. -/
inductive VRead (B : Box QExpr) : E → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l c → qle c h → VRead B (.const c) l h
  | var {i : Nat} {l h : QExpr} : qle l (B i).1 → qle (B i).2 h → VRead B (.var i) l h
  | add {u v : E} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → VRead B (.add u v) l h
  | sub {u v : E} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → VRead B (.sub u v) l h
  | mul {u v : E} {l1 h1 l2 h2 l h : QExpr} : VRead B u l1 h1 → VRead B v l2 h2 →
      Corners l h l1 h1 l2 h2 → VRead B (.mul u v) l h

/-- THE INTERVAL READING ENCLOSES THE VALUE (`ZCertify`'s `iv_sound`, for this grammar). -/
theorem value_sound {B : Box QExpr} {p : Point QExpr} (hp : InBox qOrd B p) :
    ∀ {e : E} {l h : QExpr}, VRead B e l h → qle l (eval p e) ∧ qle (eval p e) h := by
  intro e l h r
  induction r with
  | const h1 h2 => exact ⟨h1, h2⟩
  | var h1 h2 => exact ⟨qle_trans h1 (hp _).1, qle_trans (hp _).2 h2⟩
  | add _ _ hl hh ih1 ih2 =>
      obtain ⟨a1, a2⟩ := ih1
      obtain ⟨b1, b2⟩ := ih2
      refine ⟨?_, ?_⟩
      · show qle _ (qadd _ _); rat_linarith
      · show qle (qadd _ _) _; rat_linarith
  | sub _ _ hl hh ih1 ih2 =>
      obtain ⟨a1, a2⟩ := ih1
      obtain ⟨b1, b2⟩ := ih2
      refine ⟨?_, ?_⟩
      · show qle _ (qsub _ _); unfold qsub at hl ⊢; rat_linarith
      · show qle (qsub _ _) _; unfold qsub at hh ⊢; rat_linarith
  | mul _ _ hc ih1 ih2 =>
      obtain ⟨a1, a2⟩ := ih1
      obtain ⟨b1, b2⟩ := ih2
      obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hc
      exact ⟨mul_lo a1 a2 b1 b2 l11 l12 l21 l22, mul_hi a1 a2 b1 b2 h11 h12 h21 h22⟩

/-! ## The derivative reading and the slope -/

/-- What the kernel checks of a derivative reading `[l, h]` of `e` in quantity `i` over `B`: the sum rule,
and the product rule `U·Dv + V·Du` with each product interval checked at its corners. -/
inductive DRead (B : Box QExpr) (i : Nat) : E → QExpr → QExpr → Prop where
  | const {c l h : QExpr} : qle l qzero → qle qzero h → DRead B i (.const c) l h
  | self {l h : QExpr} : qle l qone → qle qone h → DRead B i (.var i) l h
  | other {j : Nat} {l h : QExpr} : j ≠ i → qle l qzero → qle qzero h → DRead B i (.var j) l h
  | add {u v : E} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qadd l1 l2) → qle (qadd h1 h2) h → DRead B i (.add u v) l h
  | sub {u v : E} {l1 h1 l2 h2 l h : QExpr} : DRead B i u l1 h1 → DRead B i v l2 h2 →
      qle l (qsub l1 h2) → qle (qsub h1 l2) h → DRead B i (.sub u v) l h
  | mul {u v : E} {lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h : QExpr} :
      VRead B u lu hu → VRead B v lv hv → DRead B i u du1 du2 → DRead B i v dv1 dv2 →
      Corners m1 M1 lu hu dv1 dv2 → Corners m2 M2 lv hv du1 du2 →
      qle l (qadd m1 m2) → qle (qadd M1 M2) h → DRead B i (.mul u v) l h

/-- `x ≤ y`, `d ≥ 0` give `x·d ≤ y·d`. -/
theorem scale {x y d : QExpr} (h : qle x y) (hd : qle qzero d) : qle (qmul x d) (qmul y d) := by
  have f : qle qzero (qmul (qsub y x) d) := qmul_nonneg (by unfold qsub; rat_linarith) hd
  have e : qEq (qmul (qsub y x) d) (qadd (qmul y d) (qneg (qmul x d))) := by unfold qsub; rat_ring
  rat_linarith

/-- A corner bound, scaled: `m` below the corners of `[a1,a2] × [b1,b2]`, `a` in `[a1, a2]`, `t` in
`[b1·d, b2·d]`, `d ≥ 0`: then `m·d ≤ a·t` (and the dual above). -/
theorem scaled {a1 a2 a b1 b2 t d m M : QExpr} (ha1 : qle a1 a) (ha2 : qle a a2) (hd : qle qzero d)
    (ht1 : qle (qmul b1 d) t) (ht2 : qle t (qmul b2 d)) (hc : Corners m M a1 a2 b1 b2) :
    qle (qmul m d) (qmul a t) ∧ qle (qmul a t) (qmul M d) := by
  obtain ⟨⟨l11, l12, l21, l22⟩, ⟨h11, h12, h21, h22⟩⟩ := hc
  have r : ∀ x y : QExpr, qEq (qmul (qmul x y) d) (qmul x (qmul y d)) := fun x y => by rat_ring
  have lo : ∀ {x y : QExpr}, qle m (qmul x y) → qle (qmul m d) (qmul x (qmul y d)) :=
    fun h => qle_respects (qEq_refl _) (r _ _) (scale h hd)
  have hi : ∀ {x y : QExpr}, qle (qmul x y) M → qle (qmul x (qmul y d)) (qmul M d) :=
    fun h => qle_respects (r _ _) (qEq_refl _) (scale h hd)
  exact ⟨mul_lo ha1 ha2 ht1 ht2 (lo l11) (lo l12) (lo l21) (lo l22),
         mul_hi ha1 ha2 ht1 ht2 (hi h11) (hi h12) (hi h21) (hi h22)⟩

/-- THE SLOPE. Two points of the piece, differing only in quantity `i`, by `d = p' i − p i ≥ 0`; a derivative
reading `[l, h]` in `i`: `l·d ≤ f(p') − f(p) ≤ h·d`. Induction on the reading; the product step is the
exact identity `Δ(uv) = u(p')·Δv + v(p)·Δu` — no intermediate point. -/
theorem slope_sound {B : Box QExpr} {i : Nat} {p p' : Point QExpr} (hp : InBox qOrd B p)
    (hp' : InBox qOrd B p') (hfix : ∀ j, j ≠ i → p' j = p j) (hd : qle qzero (qsub (p' i) (p i))) :
    ∀ {e : E} {l h : QExpr}, DRead B i e l h →
      qle (qmul l (qsub (p' i) (p i))) (qsub (eval p' e) (eval p e)) ∧
      qle (qsub (eval p' e) (eval p e)) (qmul h (qsub (p' i) (p i))) := by
  intro e l h r
  induction r with
  | @const c l h hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub c c) qzero := by unfold qsub; rat_ring
      exact ⟨by show qle _ (qsub c c); rat_linarith, by show qle (qsub c c) _; rat_linarith⟩
  | @self l h hl hh =>
      have f1 : qle qzero (qmul (qsub qone l) (qsub (p' i) (p i))) :=
        qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e1 : qEq (qmul (qsub qone l) (qsub (p' i) (p i)))
          (qadd (qsub (p' i) (p i)) (qneg (qmul l (qsub (p' i) (p i))))) := by unfold qsub; rat_ring
      have f2 : qle qzero (qmul (qsub h qone) (qsub (p' i) (p i))) :=
        qmul_nonneg (by unfold qsub; rat_linarith) hd
      have e2 : qEq (qmul (qsub h qone) (qsub (p' i) (p i)))
          (qadd (qmul h (qsub (p' i) (p i))) (qneg (qsub (p' i) (p i)))) := by unfold qsub; rat_ring
      exact ⟨by show qle _ (qsub (p' i) (p i)); rat_linarith,
             by show qle (qsub (p' i) (p i)) _; rat_linarith⟩
  | @other j l h hj hl hh =>
      have f1 : qle qzero (qmul (qneg l) (qsub (p' i) (p i))) := qmul_nonneg (by rat_linarith) hd
      have e1 : qEq (qmul (qneg l) (qsub (p' i) (p i))) (qneg (qmul l (qsub (p' i) (p i)))) := by rat_ring
      have f2 : qle qzero (qmul h (qsub (p' i) (p i))) := qmul_nonneg hh hd
      have e0 : qEq (qsub (p j) (p j)) qzero := by unfold qsub; rat_ring
      show qle _ (qsub (p' j) (p j)) ∧ qle (qsub (p' j) (p j)) _
      rw [hfix j hj]
      exact ⟨by rat_linarith, by rat_linarith⟩
  | @add u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      obtain ⟨a1, a2⟩ := ih1
      obtain ⟨b1, b2⟩ := ih2
      have s1 := scale hl hd
      have s2 := scale hh hd
      have r1 : qEq (qmul (qadd l1 l2) (qsub (p' i) (p i)))
          (qadd (qmul l1 (qsub (p' i) (p i))) (qmul l2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd h1 h2) (qsub (p' i) (p i)))
          (qadd (qmul h1 (qsub (p' i) (p i))) (qmul h2 (qsub (p' i) (p i)))) := by rat_ring
      have ed : qEq (qsub (qadd (eval p' u) (eval p' v)) (qadd (eval p u) (eval p v)))
          (qadd (qsub (eval p' u) (eval p u)) (qsub (eval p' v) (eval p v))) := by unfold qsub; rat_ring
      exact ⟨by show qle _ (qsub (qadd _ _) (qadd _ _)); rat_linarith,
             by show qle (qsub (qadd _ _) (qadd _ _)) _; rat_linarith⟩
  | @sub u v l1 h1 l2 h2 l h _ _ hl hh ih1 ih2 =>
      obtain ⟨a1, a2⟩ := ih1
      obtain ⟨b1, b2⟩ := ih2
      have s1 := scale hl hd
      have s2 := scale hh hd
      have r1 : qEq (qmul (qsub l1 h2) (qsub (p' i) (p i)))
          (qadd (qmul l1 (qsub (p' i) (p i))) (qneg (qmul h2 (qsub (p' i) (p i))))) := by
        unfold qsub; rat_ring
      have r2 : qEq (qmul (qsub h1 l2) (qsub (p' i) (p i)))
          (qadd (qmul h1 (qsub (p' i) (p i))) (qneg (qmul l2 (qsub (p' i) (p i))))) := by
        unfold qsub; rat_ring
      have ed : qEq (qsub (qsub (eval p' u) (eval p' v)) (qsub (eval p u) (eval p v)))
          (qadd (qsub (eval p' u) (eval p u)) (qneg (qsub (eval p' v) (eval p v)))) := by
        unfold qsub; rat_ring
      exact ⟨by show qle _ (qsub (qsub _ _) (qsub _ _)); rat_linarith,
             by show qle (qsub (qsub _ _) (qsub _ _)) _; rat_linarith⟩
  | @mul u v lu hu lv hv du1 du2 dv1 dv2 m1 M1 m2 M2 l h ru rv _ _ c1 c2 hl hh ih1 ih2 =>
      obtain ⟨a1, a2⟩ := ih1
      obtain ⟨b1, b2⟩ := ih2
      -- u(p') ∈ [lu, hu], v(p) ∈ [lv, hv]
      obtain ⟨u1, u2⟩ := value_sound hp' ru
      obtain ⟨v1, v2⟩ := value_sound hp rv
      -- Δv ∈ [dv1·d, dv2·d], Δu ∈ [du1·d, du2·d]
      obtain ⟨k1, K1⟩ := scaled u1 u2 hd b1 b2 c1
      obtain ⟨k2, K2⟩ := scaled v1 v2 hd a1 a2 c2
      have s1 := scale hl hd
      have s2 := scale hh hd
      have r1 : qEq (qmul (qadd m1 m2) (qsub (p' i) (p i)))
          (qadd (qmul m1 (qsub (p' i) (p i))) (qmul m2 (qsub (p' i) (p i)))) := by rat_ring
      have r2 : qEq (qmul (qadd M1 M2) (qsub (p' i) (p i)))
          (qadd (qmul M1 (qsub (p' i) (p i))) (qmul M2 (qsub (p' i) (p i)))) := by rat_ring
      have ed : qEq (qsub (qmul (eval p' u) (eval p' v)) (qmul (eval p u) (eval p v)))
          (qadd (qmul (eval p' u) (qsub (eval p' v) (eval p v)))
                (qmul (eval p v) (qsub (eval p' u) (eval p u)))) := by unfold qsub; rat_ring
      exact ⟨by show qle _ (qsub (qmul _ _) (qmul _ _)); rat_linarith,
             by show qle (qsub (qmul _ _) (qmul _ _)) _; rat_linarith⟩

/-! ## Monotone: `ZCertify.Mono`, proved -/

theorem upd_other (p : Point QExpr) (i : Nat) (v : QExpr) : ∀ j, j ≠ i → upd p i v j = p j := by
  intro j hj
  unfold upd
  cases Nat.decEq j i with
  | isTrue e => exact absurd e hj
  | isFalse _ => rfl

theorem upd_self (p : Point QExpr) (i : Nat) (v : QExpr) : upd p i v i = v := by
  unfold upd
  cases Nat.decEq i i with
  | isTrue _ => rfl
  | isFalse h => exact absurd rfl h

/-- A derivative read non-negative: moving `i` to the top of its interval never lowers the value. -/
theorem mono_up {B : Box QExpr} {i : Nat} {e : E} {l h : QExpr} (r : DRead B i e l h) (hl : qle qzero l) :
    Mono qOrd qOrd (fun p => eval p e) B i true := by
  intro p hp
  have hp' := upd_end_inbox qOrd i true hp
  have hu : upd p i (endOf B true i) i = (B i).2 := upd_self p i _
  have hd : qle qzero (qsub (upd p i (endOf B true i) i) (p i)) := by
    have h2 : qle (p i) (B i).2 := (hp i).2
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨s, _⟩ := slope_sound hp hp' (upd_other p i _) hd r
  have f := qmul_nonneg hl hd
  have es : qEq (qsub (eval (upd p i (endOf B true i)) e) (eval p e))
      (qadd (eval (upd p i (endOf B true i)) e) (qneg (eval p e))) := qEq_refl _
  show qle (eval p e) (eval (upd p i (endOf B true i)) e)
  rat_linarith

/-- A derivative read non-positive: moving `i` to the bottom of its interval never lowers the value. -/
theorem mono_down {B : Box QExpr} {i : Nat} {e : E} {l h : QExpr} (r : DRead B i e l h) (hh : qle h qzero) :
    Mono qOrd qOrd (fun p => eval p e) B i false := by
  intro p hp
  have hp' := upd_end_inbox qOrd i false hp
  have hu : upd p i (endOf B false i) i = (B i).1 := upd_self p i _
  -- the lower point is the moved one: p differs from it in i only, by p i − (B i).1 ≥ 0
  have hfix : ∀ j, j ≠ i → p j = upd p i (endOf B false i) j := fun j hj => (upd_other p i _ j hj).symm
  have hd : qle qzero (qsub (p i) (upd p i (endOf B false i) i)) := by
    have h1 : qle (B i).1 (p i) := (hp i).1
    rw [hu]; unfold qsub; rat_linarith
  obtain ⟨_, s⟩ := slope_sound hp' hp hfix hd r
  have f : qle qzero (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i))) :=
    qmul_nonneg (by rat_linarith) hd
  have e1 : qEq (qmul (qneg h) (qsub (p i) (upd p i (endOf B false i) i)))
      (qneg (qmul h (qsub (p i) (upd p i (endOf B false i) i)))) := by rat_ring
  have es : qEq (qsub (eval p e) (eval (upd p i (endOf B false i)) e))
      (qadd (eval p e) (qneg (eval (upd p i (endOf B false i)) e))) := qEq_refl _
  show qle (eval p e) (eval (upd p i (endOf B false i)) e)
  rat_linarith

/-! ## The certificate rule, with no premise left -/

/-- The kernel's interval leaf: a value reading of `e` over the piece, its top under the bound. -/
def IvOK (e : E) (c : QExpr) (B : Box QExpr) : Prop := ∃ l h, VRead B e l h ∧ qle h c

/-- The kernel's monotone leaf, per quantity: a derivative reading with the sign the leaf names. -/
def DerivOK (e : E) (B : Box QExpr) (i : Nat) : Bool → Prop
  | true => ∃ l h, DRead B i e l h ∧ qle qzero l
  | false => ∃ l h, DRead B i e l h ∧ qle h qzero

/-- THE CERTIFICATE RULE IS SOUND, PREMISE-FREE, for `+ − ×` over VR's operational rationals: every quantity
the expression reads listed, an accepted certificate shows `e ≤ c` on every point of the box. -/
theorem certificate_sound_E (e : E) (ns : List Nat) (c : QExpr) (hns : ∀ j, Uses e j → List.Mem j ns) :
    ∀ (t : Tree QExpr Leaf) (B : Box QExpr),
      Accepts (LeafOK qOrd (fun p => eval p e) ns c (IvOK e c) (DerivOK e)) B t →
      ∀ p, InBox qOrd B p → qle (eval p e) c :=
  certificate_sound qOrd qOrd (fun p => eval p e) ns c
    (fun p q h => eval_dep p q e (fun j hj => h j (hns j hj)))
    (IvOK e c) (DerivOK e)
    (fun _ ⟨_, _, r, hc⟩ _ hp => qle_trans (value_sound hp r).2 hc)
    (fun _ _ s => match s with
      | true => fun ⟨_, _, r, hl⟩ => mono_up r hl
      | false => fun ⟨_, _, r, hh⟩ => mono_down r hh)

/-! ## Nonvacuity: x² on [1, 2] -/

def q2 : QExpr := qadd qone qone
def q4 : QExpr := qadd q2 q2

/-- The kernel's readings of `x·x` on `[1, 2]`: value `[1, 4]`, derivative `[2, 4]` (`U·Dv + V·Du` with
`U = V = [1, 2]`, `Du = Dv = [1, 1]`) — non-negative, so `x²` rises toward the top of the interval. -/
example : Mono qOrd qOrd (fun p => eval p (.mul (.var 0) (.var 0))) (fun _ => (qone, q2)) 0 true :=
  mono_up (l := q2) (h := q4)
    (DRead.mul (lu := qone) (hu := q2) (lv := qone) (hv := q2) (du1 := qone) (du2 := qone)
      (dv1 := qone) (dv2 := qone) (m1 := qone) (M1 := q2) (m2 := qone) (M2 := q2)
      (VRead.var (by decide) (by decide)) (VRead.var (by decide) (by decide))
      (DRead.self (by decide) (by decide)) (DRead.self (by decide) (by decide))
      (by unfold Corners; decide) (by unfold Corners; decide) (by decide) (by decide))
    (by decide)

end ZSlope

#print axioms ZSlope.eval_dep
#print axioms ZSlope.mul_lo
#print axioms ZSlope.mul_hi
#print axioms ZSlope.value_sound
#print axioms ZSlope.scale
#print axioms ZSlope.scaled
#print axioms ZSlope.slope_sound
#print axioms ZSlope.upd_other
#print axioms ZSlope.upd_self
#print axioms ZSlope.mono_up
#print axioms ZSlope.mono_down
#print axioms ZSlope.certificate_sound_E
