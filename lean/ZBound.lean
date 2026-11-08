import ZRootDiv
/-!
# ZBound — a bound over a whole box, as a THEOREM: `∀ x in the box, F(x) ≤ c` (or `c ≤ F(x)`). Zero axioms.

The curator, 2026-11-08: "важно, если стенд будет давать не только сертификат, но и доказательства". Most of the
stand's verdicts are requirements over a box of tolerances — `Vout ∈ [2.475, 2.525]` for every resistor within ±1 % —
judged by a certificate (zcertify: a tree of cuts, interval and monotone leaves). Here the same kind of certificate is
checked by the Lean kernel and becomes a theorem on VR's continuum:

  * a COVER TREE `BT`: a leaf, or a cut of variable `i` at a dyadic `a` into two halves of its interval;
  * `chkB`: every leaf's interval reading (`ZXE.ivX` — division, exp, ln, atan, sin, cos, min included) lies on the
    right side of `c`, and every cut is inside its interval;
  * `chkB_sound`, over ANY constructive ordered field: a point of the box has its value on that side. The cut needs
    no decision of `x ≤ a`: `≤` is stable (`le_of_not_pos`), and inside the proof of `False` a sign is chosen
    (`sign_case`), so each half's case is the induction hypothesis;
  * `bound_vr`: on VR's continuum, the total law (`ZRootDiv.evR`, every denominator checked positive on the box by
    `posOK`) at EVERY real point of the box.

Monotone leaves (`VT`, `chkV`, `bound_vrM` below): the slope reading's sign takes a point to the corner it points to,
where the reading is exact — a requirement met exactly at a corner stays provable.
-/

namespace ZBound

open VR VR.Numbers VR.CSR ZNumBin ZField ZPoly ZIv ZDivIv ZXE ZRealCF ZRootDiv

inductive BT where
  | leaf : BT
  | cut : Nat → D → BT → BT → BT

/-- The box with variable `i`'s interval replaced. -/
def boxSet (B : Box) (i : Nat) (I : Iv) : Box := fun j => cond (Nat.beq j i) (some I) (B j)

/-- The side of `c` a leaf's reading must lie on: `lo` — `c ≤ F`, otherwise `F ≤ c`. -/
def side (lo : Bool) (c : D) (K : Iv) : Bool := cond lo (dle c K.1) (dle K.2 c)

/-- **THE KERNEL'S CHECK** of a cover tree. -/
def chkB (lo : Bool) (e : XE) (c : D) : BT → Box → Bool
  | .leaf => fun B => match ivX B e with
    | none => false
    | some K => side lo c K
  | .cut i a l r => fun B => match B i with
    | none => false
    | some I => dle I.1 a && dle a I.2 && chkB lo e c l (boxSet B i (I.1, a)) && chkB lo e c r (boxSet B i (a, I.2))

/-! ## The search (a PROPOSAL: printed by `#eval` and pasted as a literal; the kernel checks only `chkB`) -/

/-- The widest variable of `vs` on `B`. -/
def widest (B : Box) : List Nat → Option (Nat × Iv)
  | [] => none
  | i :: vs => match B i with
    | none => widest B vs
    | some I => match widest B vs with
      | none => some (i, I)
      | some (j, J) => cond (dle (dadd J.2 (dneg J.1)) (dadd I.2 (dneg I.1))) (some (i, I)) (some (j, J))

/-- Bisection to depth `n`: a leaf where the reading settles it, else a cut of the widest variable at its middle. -/
def findB (lo : Bool) (e : XE) (c : D) (vs : List Nat) : Nat → Box → Option BT
  | 0 => fun B => cond (chkB lo e c .leaf B) (some .leaf) none
  | n + 1 => fun B => cond (chkB lo e c .leaf B) (some .leaf) (match widest B vs with
    | none => none
    | some (i, I) => match findB lo e c vs n (boxSet B i (I.1, ZAff.mid I)) with
      | none => none
      | some l => match findB lo e c vs n (boxSet B i (ZAff.mid I, I.2)) with
        | none => none
        | some r => some (.cut i (ZAff.mid I) l r))

def dTxt (d : D) : String := s!"(⟨⟨{d.m.p}, {d.m.n}⟩, {d.e}⟩ : D)"

/-- The tree as Lean syntax. -/
def BT.txt : BT → String
  | .leaf => ".leaf"
  | .cut i a l r => s!"(.cut {i} {dTxt a} {l.txt} {r.txt})"

def BT.size : BT → Nat
  | .leaf => 1
  | .cut _ _ l r => l.size + r.size

section Sound
variable {α : Type} {S : CF α}

/-- What the bound says, on the side `lo`. -/
def Holds (S : CF α) (lo : Bool) (c : D) (v : α) : Prop := cond lo (S.le (dv S.toOH c) v) (S.le v (dv S.toOH c))

theorem and4' {a b c d : Bool} (h : (a && b && c && d) = true) : a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> first | exact ⟨rfl, rfl, rfl, rfl⟩ | cases h

/-- A point of the box with `p i ≤ a` (resp. `a ≤ p i`) is in the left (resp. right) half. -/
theorem inbox_set {B : Box} {p : Nat → α} (hp : InBox S B p) {i : Nat} {lo hi : D}
    (h1 : S.le (dv S.toOH lo) (p i)) (h2 : S.le (p i) (dv S.toOH hi)) : InBox S (boxSet B i (lo, hi)) p := by
  intro j J hJ
  unfold boxSet at hJ
  cases hb : Nat.beq j i with
  | true =>
      rw [hb] at hJ; cases hJ
      have := Nat.eq_of_beq_eq_true hb; subst this
      exact ⟨h1, h2⟩
  | false => rw [hb] at hJ; exact hp j J hJ

/-- `≤` is stable: a bound refuted nowhere holds. -/
theorem holds_stable {lo : Bool} {c : D} {v : α} (h : ¬ Holds S lo c v → False) : Holds S lo c v := by
  cases lo with
  | true =>
      show S.le (dv S.toOH c) v
      exact S.le_of_not_pos (fun hp => h (fun hh => by
        have hh' : S.le (dv S.toOH c) v := hh
        exact S.pos_not_le hp (by cr_linarith S.toOCR [hh'])))
  | false =>
      show S.le v (dv S.toOH c)
      exact S.le_of_not_pos (fun hp => h (fun hh => by
        have hh' : S.le v (dv S.toOH c) := hh
        exact S.pos_not_le hp (by cr_linarith S.toOCR [hh'])))

/-- **THE COVER TREE IS SOUND**, over any constructive ordered field. -/
theorem chkB_sound {ex atn sn cs : α → α} {mn : α → α → α} {lo : Bool} {e : XE} {c : D} :
    ∀ (T : BT) (B : Box) (p : Nat → α) (v : α), chkB lo e c T B = true → InBox S B p →
      Val S ex atn sn cs mn p e v → Holds S lo c v
  | .leaf, B, p, v, h, hp, hv => by
      unfold chkB at h
      cases hK : ivX B e with
      | none => rw [hK] at h; cases h
      | some K =>
      rw [hK] at h
      have m := ivX_sound S hp hv K hK
      unfold side at h
      cases lo with
      | true => exact S.le_trans (dle_sound S.toOH h) m.1
      | false => exact S.le_trans m.2 (dle_sound S.toOH h)
  | .cut i a l r, B, p, v, h, hp, hv => by
      unfold chkB at h
      cases hI : B i with
      | none => rw [hI] at h; cases h
      | some I =>
      rw [hI] at h
      obtain ⟨_, _, hl, hr⟩ := and4' h
      have mi := hp i I hI
      apply holds_stable
      intro hn
      apply sign_case S (S.add (p i) (S.neg (dv S.toOH a)))
      · intro hge
        have hge' : S.le (dv S.toOH a) (p i) := by cr_linarith S.toOCR [hge]
        exact hn (chkB_sound r _ p v hr (inbox_set hp hge' mi.2) hv)
      · intro hle
        have hle' : S.le (p i) (dv S.toOH a) := by cr_linarith S.toOCR [hle]
        exact hn (chkB_sound l _ p v hl (inbox_set hp mi.1 hle') hv)

end Sound

/-- **THE BOUND ON VR's CONTINUUM**: every real point of the box (every denominator and `ln` argument read
positive on the box) has its value on the side of `c`. -/
theorem bound_vr {lo : Bool} {e : XE} {c : D} {T : BT} {B : Box} (h : chkB lo e c T B = true)
    (hpos : posOK B e = true) : ∀ x : Nat → RExpr, InBox rCF B x → Holds rCF lo c (evR x e) :=
  fun x hx => chkB_sound T B x (evR x e) h hx (val_evR hx e hpos)

/-! ## Monotone leaves: the slope reading's sign takes the point to a corner, one coordinate at a time -/

open ZRootExp ZRealExp

/-- The unit direction of variable `i`. -/
def unitV (i : Nat) : Nat → Iv := fun j => cond (Nat.beq j i) ZIv.one zI

/-- Which end the corner takes for side `lo` (`true` = the upper end): increasing — the upper end for an upper bound. -/
def dirOf (lo : Bool) (K : Iv) : Option Bool :=
  cond (dle dz0 K.1) (some (!lo)) (cond (dle K.2 dz0) (some lo) none)

/-- The corner box: each variable of `vs` set to the end its slope's sign (read on `B0`) points to. -/
def cornerAux (B0 : Box) (lo : Bool) (e : XE) : List Nat → Box → Option Box
  | [] => fun Bc => some Bc
  | i :: vs => fun Bc => match B0 i with
    | none => none
    | some I => match slX B0 (unitV i) e with
      | none => none
      | some K => match dirOf lo K with
        | none => none
        | some up => cornerAux B0 lo e vs (boxSet Bc i (cond up (I.2, I.2) (I.1, I.1)))

/-- A cover tree with monotone leaves. -/
inductive VT where
  | leaf : VT
  | mono : VT
  | cut : Nat → D → VT → VT → VT

/-- **THE KERNEL'S CHECK** with monotone leaves (`vs`: the variables a corner moves). -/
def chkV (lo : Bool) (e : XE) (c : D) (vs : List Nat) : VT → Box → Bool
  | .leaf => fun B => chkB lo e c .leaf B
  | .mono => fun B => posOK B e && (match cornerAux B lo e vs B with
    | none => false
    | some Bc => chkB lo e c .leaf Bc)
  | .cut i a l r => fun B => match B i with
    | none => false
    | some I => dle I.1 a && dle a I.2 && chkV lo e c vs l (boxSet B i (I.1, a)) && chkV lo e c vs r (boxSet B i (a, I.2))

/-- The variables whose slope reading STRADDLES 0 (they block the corner walk), with the score
`(slope span)·(width)` — the search's choice only: the kernel checks the tree, never how it was found. -/
def straddle (B : Box) (e : XE) : List Nat → Option (Nat × Iv × D)
  | [] => none
  | i :: vs => match B i with
    | none => straddle B e vs
    | some I => match slX B (unitV i) e with
      | none => straddle B e vs
      | some K => cond (dle dz0 K.1 || dle K.2 dz0) (straddle B e vs)
          (match straddle B e vs with
           | none => some (i, I, dmul (dadd K.2 (dneg K.1)) (dadd I.2 (dneg I.1)))
           | some (j, J, t) => cond (dle t (dmul (dadd K.2 (dneg K.1)) (dadd I.2 (dneg I.1))))
               (some (i, I, dmul (dadd K.2 (dneg K.1)) (dadd I.2 (dneg I.1)))) (some (j, J, t)))

/-- The variable to cut: the straddling one with the largest score, else the widest. (2026-11-08, ztl-stand
tasks/t5-divider-tcr: the widest — a resistor 200 Ω wide — was cut 14 times while the temperature's sign `T − 25`
blocked every monotone leaf: no tree.) -/
def pickCut (B : Box) (e : XE) (vs : List Nat) : Option (Nat × Iv) :=
  match straddle B e vs with
  | some (i, I, _) => some (i, I)
  | none => widest B vs

/-- The search with monotone leaves (a PROPOSAL; the kernel checks only `chkV`): a monotone leaf, else an interval
leaf, else a cut of `pickCut`'s variable at its middle. -/
def findV (lo : Bool) (e : XE) (c : D) (vs : List Nat) : Nat → Box → Option VT
  | 0 => fun B => cond (chkV lo e c vs .mono B) (some .mono) (cond (chkV lo e c vs .leaf B) (some .leaf) none)
  | n + 1 => fun B => cond (chkV lo e c vs .mono B) (some .mono) (cond (chkV lo e c vs .leaf B) (some .leaf)
    (match pickCut B e vs with
    | none => none
    | some (i, I) => match findV lo e c vs n (boxSet B i (I.1, ZAff.mid I)) with
      | none => none
      | some l => match findV lo e c vs n (boxSet B i (ZAff.mid I, I.2)) with
        | none => none
        | some r => some (.cut i (ZAff.mid I) l r)))

def VT.txt : VT → String
  | .leaf => ".leaf"
  | .mono => ".mono"
  | .cut i a l r => s!"(.cut {i} {dTxt a} {l.txt} {r.txt})"

def VT.size : VT → Nat
  | .leaf => 1
  | .mono => 1
  | .cut _ _ l r => l.size + r.size

section Mono
variable {α : Type} {S : CF α}

/-- A slope in `K`, `K ≥ 0`, a step `d ≥ 0`: the change is `≥ 0`. -/
theorem sl_ge0 {Δ d : α} {K : Iv} (h : SlIn S Δ d K) (hk : S.le S.zero (dv S.toOH K.1)) (hd : S.le S.zero d) :
    S.le S.zero Δ := by
  apply S.le_of_not_pos
  intro hp
  apply h
  intro ⟨s, hs, he⟩
  have m := S.mul_nonneg (S.le_trans hk hs.1) hd
  exact S.pos_not_le hp (by have := S.le_respects (S.refl _) (S.symm he) m; cr_linarith S.toOCR [this])

theorem sl_ge0' {Δ d : α} {K : Iv} (h : SlIn S Δ d K) (hk : S.le (dv S.toOH K.2) S.zero) (hd : S.le d S.zero) :
    S.le S.zero Δ := by
  apply S.le_of_not_pos
  intro hp
  apply h
  intro ⟨s, hs, he⟩
  have a : S.le S.zero (S.neg s) := by have := S.le_trans hs.2 hk; cr_linarith S.toOCR [this]
  have b : S.le S.zero (S.neg d) := by cr_linarith S.toOCR [hd]
  have m := S.mul_nonneg a b
  have e2 : S.r (S.mul (S.neg s) (S.neg d)) (S.mul s d) := by cr_ring S.toCR
  have m' := S.le_respects (S.refl _) (S.trans e2 (S.symm he)) m
  exact S.pos_not_le hp (by cr_linarith S.toOCR [m'])

theorem sl_le0 {Δ d : α} {K : Iv} (h : SlIn S Δ d K) (hk : S.le S.zero (dv S.toOH K.1)) (hd : S.le d S.zero) :
    S.le Δ S.zero := by
  apply S.le_of_not_pos
  intro hp
  apply h
  intro ⟨s, hs, he⟩
  have b : S.le S.zero (S.neg d) := by cr_linarith S.toOCR [hd]
  have m := S.mul_nonneg (S.le_trans hk hs.1) b
  have e2 : S.r (S.mul s (S.neg d)) (S.neg (S.mul s d)) := by cr_ring S.toCR
  have m' := S.le_respects (S.refl _) (S.trans e2 (S.neg_congr (S.symm he))) m
  exact S.pos_not_le hp (by cr_linarith S.toOCR [m'])

theorem sl_le0' {Δ d : α} {K : Iv} (h : SlIn S Δ d K) (hk : S.le (dv S.toOH K.2) S.zero) (hd : S.le S.zero d) :
    S.le Δ S.zero := by
  apply S.le_of_not_pos
  intro hp
  apply h
  intro ⟨s, hs, he⟩
  have a : S.le S.zero (S.neg s) := by have := S.le_trans hs.2 hk; cr_linarith S.toOCR [this]
  have m := S.mul_nonneg a hd
  have e2 : S.r (S.mul (S.neg s) d) (S.neg (S.mul s d)) := by cr_ring S.toCR
  have m' := S.le_respects (S.refl _) (S.trans e2 (S.neg_congr (S.symm he))) m
  exact S.pos_not_le hp (by cr_linarith S.toOCR [m'])

/-- Signs of a difference (any `CF`: `cr_linarith` does not see through `rCF`'s fields). -/
theorem sub_nonpos_of {a b : α} (h : S.le a b) : S.le (S.add a (S.neg b)) S.zero := by cr_linarith S.toOCR [h]
theorem sub_nonneg_of {a b : α} (h : S.le a b) : S.le S.zero (S.add b (S.neg a)) := by cr_linarith S.toOCR [h]
theorem le_of_sub_nonpos {a b : α} (h : S.le (S.add a (S.neg b)) S.zero) : S.le a b := by cr_linarith S.toOCR [h]
theorem le_of_sub_nonneg {a b : α} (h : S.le S.zero (S.add b (S.neg a))) : S.le a b := by cr_linarith S.toOCR [h]

end Mono

/-- `a` is no better than `b` on the side `lo` (`b` is the corner's value). -/
def Worse (lo : Bool) (a b : RExpr) : Prop := cond lo (rCF.le b a) (rCF.le a b)

/-- The point with coordinate `i` moved to `t`. -/
def upd (x : Nat → RExpr) (i : Nat) (t : RExpr) : Nat → RExpr := fun j => cond (Nat.beq j i) t (x j)

theorem inbox_upd {B : Box} {x : Nat → RExpr} (hx : InBox rCF B x) {i : Nat} {I : Iv} (hI : B i = some I)
    {t : RExpr} (h1 : rCF.le (dv rOH I.1) t) (h2 : rCF.le t (dv rOH I.2)) : InBox rCF B (upd x i t) := by
  intro j J hJ
  show rCF.le _ (cond (Nat.beq j i) t (x j)) ∧ rCF.le (cond (Nat.beq j i) t (x j)) _
  cases hb : Nat.beq j i with
  | true =>
      have := Nat.eq_of_beq_eq_true hb; subst this
      rw [hI] at hJ; cases hJ; exact ⟨h1, h2⟩
  | false => exact hx j J hJ

/-- **ONE STEP TO THE CORNER**: moving coordinate `i` to the end its slope's sign points to makes the value no better. -/
theorem mono_step {B0 : Box} {lo : Bool} {e : XE} {x : Nat → RExpr} (hx : InBox rCF B0 x) (hpos : posOK B0 e = true)
    {i : Nat} {I K : Iv} {up : Bool} (hI : B0 i = some I) (hK : slX B0 (unitV i) e = some K)
    (hu : dirOf lo K = some up) :
    InBox rCF B0 (upd x i (dv rOH (cond up I.2 I.1))) ∧
      Worse lo (evR x e) (evR (upd x i (dv rOH (cond up I.2 I.1))) e) := by
  have mi := hx i I hI
  have he : rCF.le (dv rOH (cond up I.2 I.1)) (dv rOH I.2) ∧ rCF.le (dv rOH I.1) (dv rOH (cond up I.2 I.1)) := by
    cases up with
    | true => exact ⟨rCF.le_refl _, rCF.le_trans mi.1 mi.2⟩
    | false => exact ⟨rCF.le_trans mi.1 mi.2, rCF.le_refl _⟩
  have hx' := inbox_upd hx hI he.2 he.1
  refine ⟨hx', ?_⟩
  -- the slope along coordinate i
  have hd : ∀ j, SlIn rCF (rCF.add (upd x i (dv rOH (cond up I.2 I.1)) j) (rCF.neg (x j)))
      (rCF.add (dv rOH (cond up I.2 I.1)) (rCF.neg (x i))) (unitV i j) := by
    intro j
    show SlIn rCF (rCF.add (cond (Nat.beq j i) (dv rOH (cond up I.2 I.1)) (x j)) (rCF.neg (x j))) _
      (cond (Nat.beq j i) ZIv.one zI)
    cases hb : Nat.beq j i with
    | true =>
        have := Nat.eq_of_beq_eq_true hb; subst this
        exact sl_ret (mem_one rCF) (rCF.symm (rCF.one_mul _))
    | false =>
        exact sl_ret mem_zI (rCF.trans (rCF.add_neg _) (rCF.symm (rCF.zero_mul _)))
  have sl := slX_sound rExpLaws r_slope hx hx' hd e (val_evR hx e hpos) (val_evR hx' e hpos) hK
  generalize evR (upd x i (dv rOH (cond up I.2 I.1))) e = w at sl ⊢
  generalize evR x e = v at sl ⊢
  unfold dirOf at hu
  cases hk1 : dle dz0 K.1 with
  | true =>
      rw [hk1] at hu; cases hu
      have k0 := rCF.le_respects (zv_isZ rOH (c := dz0) rfl) (rCF.refl _) (dle_sound rOH hk1)
      cases lo with
      | true =>
          -- up = false: the lower end, a step d ≤ 0, the value falls: w ≤ v
          have d0 := sub_nonpos_of mi.1
          show rCF.le w v
          exact le_of_sub_nonpos (sl_le0 sl k0 d0)
      | false =>
          have d0 := sub_nonneg_of mi.2
          show rCF.le v w
          exact le_of_sub_nonneg (sl_ge0 sl k0 d0)
  | false =>
      rw [hk1] at hu
      cases hk2 : dle K.2 dz0 with
      | true =>
          rw [hk2] at hu; cases hu
          have k0 := rCF.le_respects (rCF.refl _) (zv_isZ rOH (c := dz0) rfl) (dle_sound rOH hk2)
          cases lo with
          | true =>
              have d0 := sub_nonneg_of mi.2
              show rCF.le w v
              exact le_of_sub_nonpos (sl_le0' sl k0 d0)
          | false =>
              have d0 := sub_nonpos_of mi.1
              show rCF.le v w
              exact le_of_sub_nonneg (sl_ge0' sl k0 d0)
      | false => rw [hk2] at hu; cases hu

theorem worse_trans {lo : Bool} {a b c : RExpr} (h1 : Worse lo a b) (h2 : Worse lo b c) : Worse lo a c := by
  cases lo
  · exact rCF.le_trans h1 h2
  · exact rCF.le_trans h2 h1

/-- **THE WALK TO THE CORNER**. -/
theorem corner_walk {B0 : Box} {lo : Bool} {e : XE} (hpos : posOK B0 e = true) :
    ∀ (vs : List Nat) (Bc Bf : Box) (x : Nat → RExpr), cornerAux B0 lo e vs Bc = some Bf → InBox rCF B0 x →
      InBox rCF Bc x → ∃ xf, InBox rCF B0 xf ∧ InBox rCF Bf xf ∧ Worse lo (evR x e) (evR xf e)
  | [], Bc, Bf, x, h, h0, hc => by
      cases h
      exact ⟨x, h0, hc, by cases lo <;> exact rCF.le_refl _⟩
  | i :: vs, Bc, Bf, x, h, h0, hc => by
      unfold cornerAux at h
      cases hI : B0 i with
      | none => rw [hI] at h; cases h
      | some I =>
      rw [hI] at h; dsimp only at h
      cases hK : slX B0 (unitV i) e with
      | none => rw [hK] at h; cases h
      | some K =>
      rw [hK] at h; dsimp only at h
      cases hu : dirOf lo K with
      | none => rw [hu] at h; cases h
      | some up =>
      rw [hu] at h; dsimp only at h
      obtain ⟨h0', w1⟩ := mono_step h0 hpos hI hK hu
      have hc' : InBox rCF (boxSet Bc i (cond up (I.2, I.2) (I.1, I.1))) (upd x i (dv rOH (cond up I.2 I.1))) := by
        intro j J hJ
        unfold boxSet at hJ
        show rCF.le _ (cond (Nat.beq j i) _ (x j)) ∧ rCF.le (cond (Nat.beq j i) _ (x j)) _
        cases hb : Nat.beq j i with
        | true =>
            rw [hb] at hJ; cases hJ
            cases up <;> exact ⟨rCF.le_refl _, rCF.le_refl _⟩
        | false => rw [hb] at hJ; exact hc j J hJ
      obtain ⟨xf, a, b, w2⟩ := corner_walk hpos vs _ Bf _ h h0' hc'
      exact ⟨xf, a, b, worse_trans w1 w2⟩

theorem holds_of_worse {lo : Bool} {c : D} {v w : RExpr} (h : Holds rCF lo c w) (hw : Worse lo v w) : Holds rCF lo c v := by
  cases lo
  · exact rCF.le_trans hw h
  · exact rCF.le_trans h hw

/-- **THE COVER TREE WITH MONOTONE LEAVES IS SOUND** on VR's continuum. -/
theorem chkV_sound {lo : Bool} {e : XE} {c : D} {vs : List Nat} {Bt : Box} (hposT : posOK Bt e = true) :
    ∀ (T : VT) (B : Box) (x : Nat → RExpr), chkV lo e c vs T B = true → InBox rCF B x → InBox rCF Bt x →
      Holds rCF lo c (evR x e)
  | .leaf, B, x, h, hB, hT => chkB_sound .leaf B x (evR x e) h hB (val_evR hT e hposT)
  | .mono, B, x, h, hB, hT => by
      unfold chkV at h
      cases hp : posOK B e with
      | false => rw [hp] at h; cases h
      | true =>
      rw [hp] at h
      cases hc : cornerAux B lo e vs B with
      | none => rw [hc] at h; cases h
      | some Bc =>
      rw [hc] at h
      obtain ⟨xf, h0, hf, w⟩ := corner_walk hp vs B Bc x hc hB hB
      exact holds_of_worse (chkB_sound .leaf Bc xf (evR xf e) h hf (val_evR h0 e hp)) w
  | .cut i a l r, B, x, h, hB, hT => by
      unfold chkV at h
      cases hI : B i with
      | none => rw [hI] at h; cases h
      | some I =>
      rw [hI] at h
      obtain ⟨_, _, hl, hr⟩ := and4' h
      have mi := hB i I hI
      apply holds_stable
      intro hn
      apply sign_case rCF (rCF.add (x i) (rCF.neg (dv rOH a)))
      · intro hge
        have hge' : rCF.le (dv rOH a) (x i) := le_of_sub_nonneg hge
        exact hn (chkV_sound hposT r _ x hr (inbox_set hB hge' mi.2) hT)
      · intro hle
        have hle' : rCF.le (x i) (dv rOH a) := le_of_sub_nonpos hle
        exact hn (chkV_sound hposT l _ x hl (inbox_set hB mi.1 hle') hT)

/-! ## A quotient's bound from its cleared form (a requirement `N/D ≤ c` read as `c·D − N ≥ 0`, `D > 0`) -/

section Quot
variable {α : Type} {S : CF α}

theorem le_of_quot {Dn N v c : α} (hD : S.pos Dn) (hv : S.r (S.mul Dn v) N)
    (h : S.le S.zero (S.add (S.mul c Dn) (S.neg N))) : S.le v c := by
  apply S.le_of_not_pos
  intro hp
  have m := S.pos_mul hp hD
  have e : S.r (S.mul (S.add v (S.neg c)) Dn) (S.add (S.mul Dn v) (S.neg (S.mul c Dn))) := by cr_ring S.toCR
  have m' := S.pos_congr (S.trans e (S.add_congr hv (S.refl _))) m
  exact S.pos_not_le m' (by cr_linarith S.toOCR [h])

theorem ge_of_quot {Dn N v c : α} (hD : S.pos Dn) (hv : S.r (S.mul Dn v) N)
    (h : S.le S.zero (S.add N (S.neg (S.mul c Dn)))) : S.le c v := by
  apply S.le_of_not_pos
  intro hp
  have m := S.pos_mul hp hD
  have e : S.r (S.mul (S.add c (S.neg v)) Dn) (S.add (S.mul c Dn) (S.neg (S.mul Dn v))) := by cr_ring S.toCR
  have m' := S.pos_congr (S.trans e (S.add_congr (S.refl _) (S.neg_congr hv))) m
  exact S.pos_not_le m' (by cr_linarith S.toOCR [h])

/-- A RATIONAL bound without division: `P·D − R·N ≥ 0`, `D > 0`, `D·v = N` ⟹ `R·v ≤ P` (that is `v ≤ P/R` for
`R > 0`). The stand's requirement `q ≤ 247/100` is proved as `100·q ≤ 247`. -/
theorem le_of_quotR {Dn N v P R : α} (hD : S.pos Dn) (hv : S.r (S.mul Dn v) N)
    (h : S.le S.zero (S.add (S.mul P Dn) (S.neg (S.mul R N)))) : S.le (S.mul R v) P := by
  have e : S.r (S.mul Dn (S.mul R v)) (S.mul R (S.mul Dn v)) := by cr_ring S.toCR
  exact le_of_quot hD (S.trans e (S.mul_congr (S.refl _) hv)) h

/-- `R·N − P·D ≥ 0`, `D > 0`, `D·v = N` ⟹ `P ≤ R·v`. -/
theorem ge_of_quotR {Dn N v P R : α} (hD : S.pos Dn) (hv : S.r (S.mul Dn v) N)
    (h : S.le S.zero (S.add (S.mul R N) (S.neg (S.mul P Dn)))) : S.le P (S.mul R v) := by
  have e : S.r (S.mul Dn (S.mul R v)) (S.mul R (S.mul Dn v)) := by cr_ring S.toCR
  exact ge_of_quot hD (S.trans e (S.mul_congr (S.refl _) hv)) h

end Quot

/-- On a box where the denominator reads `≥ 2⁻⁶⁴`: `evR b · evR (a / b) = evR a`, and `evR b > 0`. -/
theorem div_value {B : Box} {x : Nat → RExpr} (hx : InBox rCF B x) {a b : XE} (h : posOK B (.div a b) = true) :
    rCF.pos (evR x b) ∧ rCF.r (rCF.mul (evR x b) (evR x (.div a b))) (evR x a) := by
  have hv := val_evR hx (.div a b) h
  obtain ⟨h12, h3⟩ := and2 h
  obtain ⟨_, h2⟩ := and2 h12
  have Vb := val_evR hx b h2
  have ceq := rcl_eq (above_clamp hx Vb h3)
  have hpos : rCF.pos (evR x b) := rCF.pos_congr ceq (rcl_pos _)
  refine ⟨hpos, ?_⟩
  have hm := rinvPos_mul (rcl (evR x b)) 64 0 (rcl_pw _)
  show rCF.r (rCF.mul (evR x b) (rCF.mul (evR x a) (rinvT (evR x b)))) (evR x a)
  refine rCF.trans (mul_swap rCF _ _ _) ?_
  refine rCF.trans (rCF.mul_congr (rCF.refl _) (rCF.mul_congr (rCF.symm ceq) (rCF.refl _))) ?_
  exact rCF.trans (rCF.mul_congr (rCF.refl _) hm) (rCF.trans (rCF.mul_comm _ _) (rCF.one_mul _))

/-- **THE BOUND ON VR's CONTINUUM**, interval and monotone leaves. -/
theorem bound_vrM {lo : Bool} {e : XE} {c : D} {vs : List Nat} {T : VT} {B : Box}
    (h : chkV lo e c vs T B = true) (hpos : posOK B e = true) :
    ∀ x : Nat → RExpr, InBox rCF B x → Holds rCF lo c (evR x e) :=
  fun x hx => chkV_sound hpos T B x h hx hx

/-! ## One polynomial, two writings: the kernel's identity test carries a bound across

The cleared form `r·N − p·D` read as two polynomials loses their shared factors (ztl-stand tasks/t5, a resistor
divider with temperature coefficients: the coefficient of `a2` sits in both N and D, and the slope in `a2` straddled
0 on every box). The bound is proved on ONE polynomial `G` (Horner, factors kept), and `ZPoly.ident` — the normal
form of `G − H` is empty — moves it to `H`, the form the requirement's glue reads. -/

/-- Both are polynomials and their normal forms agree. -/
def identX (G H : XE) : Bool := match toPE G with
  | none => false
  | some g => match toPE H with
    | none => false
    | some h => ident g h

/-- **Equal at every point of the box**, VR's continuum. -/
theorem evR_identX {B : Box} {x : Nat → RExpr} (hx : InBox rCF B x) {G H : XE} (hid : identX G H = true)
    (pg : posOK B G = true) (ph : posOK B H = true) : rCF.r (evR x G) (evR x H) := by
  unfold identX at hid
  cases hG : toPE G with
  | none => rw [hG] at hid; exact Bool.noConfusion hid
  | some g =>
    rw [hG] at hid
    cases hH : toPE H with
    | none => rw [hH] at hid; exact Bool.noConfusion hid
    | some h =>
      rw [hH] at hid
      exact rCF.trans (val_toPE rCF hG (val_evR hx G pg))
        (rCF.trans (identity_sound rCF.toOH x hid) (rCF.symm (val_toPE rCF hH (val_evR hx H ph))))

/-- The bound proved on `G` holds for `H`. -/
theorem bound_identX {lo : Bool} {G H : XE} {c : D} {vs : List Nat} {T : VT} {B : Box}
    (h : chkV lo G c vs T B = true) (pg : posOK B G = true) (hid : identX G H = true) (ph : posOK B H = true) :
    ∀ x : Nat → RExpr, InBox rCF B x → Holds rCF lo c (evR x H) := by
  intro x hx
  have hb := bound_vrM h pg x hx
  have e := evR_identX hx hid pg ph
  cases lo with
  | true => exact rCF.le_respects (rCF.refl _) e hb
  | false => exact rCF.le_respects e (rCF.refl _) hb

/-! ## A requirement on the LAWS, not on an expression (B/C, the curator 2026-11-09: "делаем")

The stand's unknowns `u` (variables past the box's parameters, unconstrained by the box) satisfy the laws, read as
polynomial ROWS `R_i = Σ_k A_ik·u_k − b_i`. A cofactor certificate `c` (a row of the adjugate, found by Python) with
the identity `Σ_i c_i·R_i ≡ D·u_j − N_j` — checked by the kernel (`identX`) — gives `D·u_j = N_j` for EVERY `u`
satisfying the laws: the elimination is no longer trusted, and with `D > 0` on the box the solution is unique. -/

section Rows
variable {α : Type} {S : CF α}
theorem mul_zero_of {a b : α} (h : S.r b S.zero) : S.r (S.mul a b) S.zero :=
  S.trans (S.mul_congr (S.refl _) h) (by cr_ring S.toCR)
theorem add_zero_of {a b : α} (ha : S.r a S.zero) (hb : S.r b S.zero) : S.r (S.add a b) S.zero :=
  S.trans (S.add_congr ha hb) (by cr_ring S.toCR)
theorem eq_of_sub_zero {a b : α} (h : S.r (S.add a (S.neg b)) S.zero) : S.r a b := by
  have e : S.r a (S.add (S.add a (S.neg b)) b) := by cr_ring S.toCR
  exact S.trans e (S.trans (S.add_congr h (S.refl _)) (by cr_ring S.toCR))
end Rows

/-- `Σ cᵢ·Rᵢ` as an expression (the certificate `cs`, the rows `rs`). -/
def linC : List XE → List XE → XE
  | [], [] => .cst dz0
  | [], _r :: _rs => .cst dz0
  | _c :: _cs, [] => .cst dz0
  | c :: cs, r :: rs => .add (.mul c r) (linC cs rs)

/-- Every row zero ⟹ any combination of them zero. -/
theorem linC_zero {y : Nat → RExpr} : ∀ cs rs : List XE, (∀ r, List.Mem r rs → rCF.r (evR y r) rCF.zero) →
    rCF.r (evR y (linC cs rs)) rCF.zero
  | [], [], _ => zv_isZ rOH (c := dz0) rfl
  | [], _r :: _rs, _ => zv_isZ rOH (c := dz0) rfl
  | _c :: _cs, [], _ => zv_isZ rOH (c := dz0) rfl
  | c :: cs, r :: rs, h => by
    have h0 : rCF.r (evR y r) rCF.zero := h r (List.Mem.head rs)
    have ht := linC_zero cs rs (fun q hq => h q (List.Mem.tail r hq))
    show rCF.r (rCF.add (rCF.mul (evR y c) (evR y r)) (evR y (linC cs rs))) rCF.zero
    exact add_zero_of (mul_zero_of h0) ht

/-- **The laws give the value**: `D·u = N` for every point of the box and EVERY `u` satisfying the rows. -/
theorem law_value {B : Box} {y : Nat → RExpr} (hy : InBox rCF B y) {cs rs : List XE} {Dx Nx U : XE}
    (hl : ∀ r, List.Mem r rs → rCF.r (evR y r) rCF.zero)
    (hid : identX (linC cs rs) (.sub (.mul Dx U) Nx) = true) (pg : posOK B (linC cs rs) = true)
    (ph : posOK B (.sub (.mul Dx U) Nx) = true) : rCF.r (rCF.mul (evR y Dx) (evR y U)) (evR y Nx) := by
  have e := evR_identX hy hid pg ph
  have z : rCF.r (rCF.add (rCF.mul (evR y Dx) (evR y U)) (rCF.neg (evR y Nx))) rCF.zero :=
    rCF.trans (rCF.symm e) (linC_zero cs rs hl)
  exact eq_of_sub_zero z

end ZBound

#print axioms ZBound.boxSet
#print axioms ZBound.chkB
#print axioms ZBound.inbox_set
#print axioms ZBound.holds_stable
#print axioms ZBound.chkB_sound
#print axioms ZBound.bound_vr
#print axioms ZBound.sl_ge0
#print axioms ZBound.sl_ge0'
#print axioms ZBound.sl_le0
#print axioms ZBound.sl_le0'
#print axioms ZBound.mono_step
#print axioms ZBound.corner_walk
#print axioms ZBound.chkV_sound
#print axioms ZBound.bound_vrM
#print axioms ZBound.le_of_quot
#print axioms ZBound.ge_of_quot
#print axioms ZBound.le_of_quotR
#print axioms ZBound.ge_of_quotR
#print axioms ZBound.identX
#print axioms ZBound.identX.eq_def
#print axioms ZBound.evR_identX
#print axioms ZBound.bound_identX
#print axioms ZBound.mul_zero_of
#print axioms ZBound.add_zero_of
#print axioms ZBound.eq_of_sub_zero
#print axioms ZBound.linC
#print axioms ZBound.linC.eq_def
#print axioms ZBound.linC_zero
#print axioms ZBound.law_value
#print axioms ZBound.div_value
