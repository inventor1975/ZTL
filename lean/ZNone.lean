import ZXE
import ZKron
/-!
# ZNone — `check_none`, executable by the kernel and sound. Zero axioms.

Module 4b of the Lean-checked `check_none` (curator, 2026-11-07: "Б"). A system is a list of equations `E_k = 0`
and a list of conditions `N_j` (to be APART from 0, the constructive `≠`). A certificate is a tree:

  * `nz k`      — over the piece, the interval reading of `E_k` excludes 0;
  * `ex j`      — `N_j` is identically 0 (a polynomial identity), so it is never apart from 0;
  * `split i t δ lo hi` — the piece cut in variable `i` at `t` WITH OVERLAP `δ > 0`: `[lo, t + δ]`, `[t − δ, hi]`
                  (`ZField.split_cover`: the constructive price of a cut);
  * `chart u v a b ρ j …` — a blow-up at the integer centre `(a, b)` in the variables `u, v`: the piece lies in the
                  square of radius `ρ`, `N_j` vanishes identically at the centre, and on each side
                  (X: `u ↦ a + u`, `v ↦ b + u·v`; Y: `u ↦ a + u·v`, `v ↦ b + u`; other variables unchanged)
                  every `E_k(φ) = uᵐ·G_k` and every `N_j(φ) = u^q·H_j` is an identity, and the sub-system
                  `(G, H)` has its own tree over `u ∈ [−ρ, ρ]`, `v ∈ [−2, 2]` (`ZField.chart_cover`).

`chk` is a Boolean the kernel evaluates; `chk_sound`: an accepted certificate leaves NO point of the box where every
`E_k` is 0 and every `N_j` is apart from 0 — in every constructive ordered field `CF`. The proof ends in `False`,
where any case split is constructive (`ZField.nn_case`): the point is apart from the centre, or it IS the centre
(`ap_tight`), where `N_j` vanishes.

Not in this version (curator, 2026-11-07, "не забудь"): the affine reading; functions beyond `+ − ×`;
non-integer chart centres.
-/

namespace ZNone
open VR.CSR ZNumBin ZField ZPoly ZIv ZAff ZXE

structure Sys where
  eqs : List XE
  neqs : List XE

inductive Cert where
  | nz (k : Nat)
  | nzA (k : Nat)
  | ex (j : Nat)
  | split (i : Nat) (t δ : D) (lo hi : Cert)
  | chart (u v : Nat) (a b : D) (ρ : D) (j : Nat)
      (gX : List ZPoly.PE) (mX : List Nat) (hX : List ZPoly.PE) (qX : List Nat) (tX : Cert)
      (gY : List ZPoly.PE) (mY : List Nat) (hY : List ZPoly.PE) (qY : List Nat) (tY : Cert)

/-- An identity: by ONE integer evaluation (`ZKron.identK`, MEASURED 2026-11-08 ~57× cheaper in the kernel on a
KS-23 chart identity), the symbolic normal form (`ZPoly.ident`) when that does not settle it (a non-integer constant). -/
def identX (e₁ e₂ : ZPoly.PE) : Bool := ZKron.identK e₁ e₂ || ident e₁ e₂

theorem identX_sound {α : Type} (S : ZNumBin.OH α) {e₁ e₂ : ZPoly.PE} (h : identX e₁ e₂ = true) (env : Nat → α) :
    S.r (ZPoly.eval S env e₁) (ZPoly.eval S env e₂) := by
  cases hk : ZKron.identK e₁ e₂ with
  | true => exact ZKron.identK_sound S hk env
  | false =>
      have h' : ident e₁ e₂ = true := by
        have : (false || ident e₁ e₂) = true := by rw [← hk]; exact h
        exact this
      exact identity_sound S env h'

/-! ## Lists, by our own recursion -/

def nth {β : Type} : List β → Nat → Option β
  | [], _ => none
  | e :: _, 0 => some e
  | _ :: l, n + 1 => nth l n

theorem nth_mem {β : Type} : ∀ {l : List β} {n : Nat} {e : β}, nth l n = some e → e ∈ l
  | [], _, _, h => by cases h
  | x :: _, 0, e, h => by cases h; exact List.Mem.head _
  | _ :: l, n + 1, _, h => List.Mem.tail _ (nth_mem (l := l) h)

/-- All expressions of a list as polynomials (none if one has a division). -/
def toPEs : List XE → Option (List ZPoly.PE)
  | [] => some []
  | e :: l => match toPE e with
      | none => none
      | some q => match toPEs l with
          | none => none
          | some qs => some (q :: qs)

/-! ## The kernel's checks -/

/-- The value of a dyadic is positive / negative (the kernel compares the two parts). -/
def posD (d : D) : Bool := Nat.blt d.m.n d.m.p
def negD (d : D) : Bool := Nat.blt d.m.p d.m.n

def upd (B : Box) (i : Nat) (I : Iv) : Box := fun j => cond (Nat.beq j i) (some I) (B j)

def dOf (z : BZ) : D := ⟨z, 0⟩
def two : D := ⟨⟨2, 0⟩, 0⟩

/-- The chart box: `u ∈ [−ρ, ρ]`, `v ∈ [−2, 2]`, the rest unchanged. -/
def chartBox (B : Box) (u v : Nat) (ρ : D) : Box := upd (upd B u (dneg ρ, ρ)) v (dneg two, two)

def phiX (u v : Nat) (a b : D) (i : Nat) : ZPoly.PE :=
  cond (Nat.beq i u) (.add (.cst a) (.var u)) (cond (Nat.beq i v) (.add (.cst b) (.mul (.var u) (.var v))) (.var i))
def phiY (u v : Nat) (a b : D) (i : Nat) : ZPoly.PE :=
  cond (Nat.beq i u) (.add (.cst a) (.mul (.var u) (.var v))) (cond (Nat.beq i v) (.add (.cst b) (.var u)) (.var i))
def cen (u v : Nat) (a b : D) (i : Nat) : ZPoly.PE :=
  cond (Nat.beq i u) (.cst a) (cond (Nat.beq i v) (.cst b) (.var i))

/-- `E(φ) = uᵐ·G`, for every pair of the two lists (same lengths). -/
def allId (φ : Nat → ZPoly.PE) (u : Nat) : List ZPoly.PE → List ZPoly.PE → List Nat → Bool
  | [], [], [] => true
  | [], [], _ :: _ => false
  | [], _ :: _, _ => false
  | _ :: _, [], _ => false
  | _ :: _, _ :: _, [] => false
  | e :: es, g :: gs, m :: ms => identX (e.subst φ) (.mul (.pow (.var u) m) g) && allId φ u es gs ms

def inSq (B : Box) (u : Nat) (a : D) (ρ : D) : Bool :=
  match B u with
  | some I => dle (dadd a (dneg ρ)) I.1 && dle I.2 (dadd a ρ)
  | none => false

/-- THE CHECKER. -/
def chk (Sy : Sys) (B : Box) : Cert → Bool
  | .nz k => match nth Sy.eqs k with
      | some e => (match ivX B e with
          | some K => posD K.1 || negD K.2
          | none => false)
      | none => false
  | .nzA k => match nth Sy.eqs k with
      | some e => (match afIvX B e with
          | some K => posD K.1 || negD K.2
          | none => false)
      | none => false
  | .ex j => match nth Sy.neqs j with
      | some n => (match toPE n with
          | some q => identX q (.cst ⟨⟨0, 0⟩, 0⟩)
          | none => false)
      | none => false
  | .split i t δ lo hi => posD δ && (match B i with
      | some I => chk Sy (upd B i (I.1, dadd t δ)) lo && chk Sy (upd B i (dadd t (dneg δ), I.2)) hi
      | none => false)
  | .chart u v a b ρ j gX mX hX qX tX gY mY hY qY tY =>
      match toPEs Sy.eqs with
      | none => false
      | some es => match toPEs Sy.neqs with
      | none => false
      | some ns =>
        !(Nat.beq u v) && posD ρ && inSq B u a ρ && inSq B v b ρ &&
        (match nth ns j with
          | some n => identX (n.subst (cen u v a b)) (.cst ⟨⟨0, 0⟩, 0⟩)
          | none => false) &&
        allId (phiX u v a b) u es gX mX && allId (phiX u v a b) u ns hX qX &&
        chk ⟨gX.map ofPE, hX.map ofPE⟩ (chartBox B u v ρ) tX &&
        allId (phiY u v a b) u es gY mY && allId (phiY u v a b) u ns hY qY &&
        chk ⟨gY.map ofPE, hY.map ofPE⟩ (chartBox B u v ρ) tY

/-! ## Splitting a check into pieces (for a certificate checked in parts, e.g. one kernel run per piece) -/

/-- The two boxes of a cut of `B` at `t` with overlap `δ` on variable `i`. -/
def lowB (B : Box) (i : Nat) (t δ : D) : Box := match B i with
  | some I => upd B i (I.1, dadd t δ)
  | none => B
def highB (B : Box) (i : Nat) (t δ : D) : Box := match B i with
  | some I => upd B i (dadd t (dneg δ), I.2)
  | none => B

/-- A cut is accepted when both halves are: the pieces may be checked separately. -/
theorem chk_split_intro {Sy : Sys} {B : Box} {i : Nat} {t δ : D} {lo hi : Cert} (hδ : posD δ = true)
    (hB : (B i).isSome = true) (h1 : chk Sy (lowB B i t δ) lo = true) (h2 : chk Sy (highB B i t δ) hi = true) :
    chk Sy B (.split i t δ lo hi) = true := by
  cases hI : B i with
  | none => rw [hI] at hB; cases hB
  | some I =>
      have e1 : lowB B i t δ = upd B i (I.1, dadd t δ) := by unfold lowB; rw [hI]
      have e2 : highB B i t δ = upd B i (dadd t (dneg δ), I.2) := by unfold highB; rw [hI]
      rw [e1] at h1; rw [e2] at h2
      show (posD δ && (match B i with
        | some I => chk Sy (upd B i (I.1, dadd t δ)) lo && chk Sy (upd B i (dadd t (dneg δ), I.2)) hi
        | none => false)) = true
      rw [hδ, hI]
      show (chk Sy (upd B i (I.1, dadd t δ)) lo && chk Sy (upd B i (dadd t (dneg δ), I.2)) hi) = true
      rw [h1, h2]; rfl

/-- A chart is accepted when each of its checks is: the identities and the two sub-trees may be checked apart. -/
theorem chk_chart_intro {Sy : Sys} {B : Box} {u v : Nat} {a b ρ : D} {j : Nat}
    {gX : List ZPoly.PE} {mX : List Nat} {hX : List ZPoly.PE} {qX : List Nat} {tX : Cert}
    {gY : List ZPoly.PE} {mY : List Nat} {hY : List ZPoly.PE} {qY : List Nat} {tY : Cert}
    {es ns : List ZPoly.PE} (hes : toPEs Sy.eqs = some es) (hns : toPEs Sy.neqs = some ns)
    (h0 : (!(Nat.beq u v) && posD ρ && inSq B u a ρ && inSq B v b ρ) = true)
    (hc : (match nth ns j with
          | some n => identX (n.subst (cen u v a b)) (.cst ⟨⟨0, 0⟩, 0⟩)
          | none => false) = true)
    (h1 : allId (phiX u v a b) u es gX mX = true) (h2 : allId (phiX u v a b) u ns hX qX = true)
    (h3 : chk ⟨gX.map ofPE, hX.map ofPE⟩ (chartBox B u v ρ) tX = true)
    (h4 : allId (phiY u v a b) u es gY mY = true) (h5 : allId (phiY u v a b) u ns hY qY = true)
    (h6 : chk ⟨gY.map ofPE, hY.map ofPE⟩ (chartBox B u v ρ) tY = true) :
    chk Sy B (.chart u v a b ρ j gX mX hX qX tX gY mY hY qY tY) = true := by
  show (match toPEs Sy.eqs with
      | none => false
      | some es => match toPEs Sy.neqs with
      | none => false
      | some ns =>
        !(Nat.beq u v) && posD ρ && inSq B u a ρ && inSq B v b ρ &&
        (match nth ns j with
          | some n => identX (n.subst (cen u v a b)) (.cst ⟨⟨0, 0⟩, 0⟩)
          | none => false) &&
        allId (phiX u v a b) u es gX mX && allId (phiX u v a b) u ns hX qX &&
        chk ⟨gX.map ofPE, hX.map ofPE⟩ (chartBox B u v ρ) tX &&
        allId (phiY u v a b) u es gY mY && allId (phiY u v a b) u ns hY qY &&
        chk ⟨gY.map ofPE, hY.map ofPE⟩ (chartBox B u v ρ) tY) = true
  rw [hes, hns]
  show (!(Nat.beq u v) && posD ρ && inSq B u a ρ && inSq B v b ρ &&
        (match nth ns j with
          | some n => identX (n.subst (cen u v a b)) (.cst ⟨⟨0, 0⟩, 0⟩)
          | none => false) &&
        allId (phiX u v a b) u es gX mX && allId (phiX u v a b) u ns hX qX &&
        chk ⟨gX.map ofPE, hX.map ofPE⟩ (chartBox B u v ρ) tX &&
        allId (phiY u v a b) u es gY mY && allId (phiY u v a b) u ns hY qY &&
        chk ⟨gY.map ofPE, hY.map ofPE⟩ (chartBox B u v ρ) tY) = true
  rw [h0, hc, h1, h2, h3, h4, h5, h6]; rfl

/-! ## Soundness -/

variable {α : Type} (S : CF α)

theorem eval_congr_env {env env' : Nat → α} (h : ∀ i, S.r (env i) (env' i)) :
    ∀ e : ZPoly.PE, S.r (eval S.toOH env e) (eval S.toOH env' e)
  | .var i => h i
  | .cst _ => S.refl _
  | .add p q => S.add_congr (eval_congr_env h p) (eval_congr_env h q)
  | .sub p q => S.add_congr (eval_congr_env h p) (S.neg_congr (eval_congr_env h q))
  | .mul p q => S.mul_congr (eval_congr_env h p) (eval_congr_env h q)
  | .pow p n => powS_congr S.toOH (eval_congr_env h p) n

theorem pos_hp : ∀ e, S.pos (hp S.toOH e)
  | 0 => pos_one S
  | e + 1 => S.pos_mul S.pos_half (pos_hp e)

theorem pos_of_posD {d : D} (h : posD d = true) : S.pos (dv S.toOH d) := by
  have l := nI_le_of_ble S.toOH (a := d.m.n + 1) (b := d.m.p) h
  have a := nI_add S.toOH d.m.n 1
  have one : S.r (nI S.toOH 1) S.one := by show S.r (S.add S.one S.zero) S.one; cr_ring S.toCR
  have l' := S.le_respects (S.trans a (S.add_congr (S.refl _) one)) (S.refl _) l
  have pz : S.pos (zv S.toOH d.m) := S.pos_mono (pos_one S) (by unfold zv; cr_linarith S.toOCR [l'])
  exact S.pos_mul pz (pos_hp S d.e)

theorem pos_of_negD {d : D} (h : negD d = true) : S.pos (S.neg (dv S.toOH d)) := by
  have l := nI_le_of_ble S.toOH (a := d.m.p + 1) (b := d.m.n) h
  have a := nI_add S.toOH d.m.p 1
  have one : S.r (nI S.toOH 1) S.one := by show S.r (S.add S.one S.zero) S.one; cr_ring S.toCR
  have l' := S.le_respects (S.trans a (S.add_congr (S.refl _) one)) (S.refl _) l
  have pz : S.pos (S.neg (zv S.toOH d.m)) := S.pos_mono (pos_one S) (by unfold zv; cr_linarith S.toOCR [l'])
  exact S.pos_congr (by unfold dv; cr_ring S.toCR) (S.pos_mul pz (pos_hp S d.e))

theorem ap_congr {x y : α} (e : S.r x y) (h : ap S x) : ap S y := by
  cases h with
  | inl p => exact Or.inl (S.pos_congr e p)
  | inr p => exact Or.inr (S.pos_congr (S.neg_congr e) p)

theorem or_true_split {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

/-- The leaf `nz`: a reading that excludes 0 contradicts `E = 0`. -/
theorem nz_sound {x : α} {K : Iv} (hm : Mem S x K) (hx : S.r x S.zero) (h : (posD K.1 || negD K.2) = true) : False := by
  cases or_true_split h with
  | inl hp => exact ap_ne S (Or.inl (S.pos_mono (pos_of_posD S hp) hm.1)) hx
  | inr hn =>
      have pn := pos_of_negD S hn
      exact ap_ne S (Or.inr (S.pos_mono pn (by cr_linarith S.toOCR [hm.2]))) hx

theorem beq_self (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem inBox_upd {B : Box} {p : Nat → α} {i : Nat} {I : Iv} (hp : InBox S B p) (hi : Mem S (p i) I) :
    InBox S (upd B i I) p := by
  intro j J hj
  unfold upd at hj
  cases hb : Nat.beq j i with
  | true =>
      rw [hb] at hj
      have e := Nat.eq_of_beq_eq_true hb
      cases hj; rw [e]; exact hi
  | false => rw [hb] at hj; exact hp j J hj

/-- With `r` apart from 0: `rᵐ · g = 0` gives `g = 0`. -/
theorem cancel_pow {r g : α} (hr : ap S r) : ∀ m, S.r (S.mul (powS S.toOH r m) g) S.zero → S.r g S.zero := by
  obtain ⟨i, hi⟩ := S.inv hr
  intro m
  induction m with
  | zero => intro h; exact S.trans (S.symm (S.one_mul g)) h
  | succ m ih =>
      intro h
      apply ih
      have e1 : S.r (S.mul (powS S.toOH r m) g) (S.mul i (S.mul (S.mul r (powS S.toOH r m)) g)) := by
        have e2 : S.r (S.mul i (S.mul (S.mul r (powS S.toOH r m)) g)) (S.mul (S.mul r i) (S.mul (powS S.toOH r m) g)) := by
          cr_ring S.toCR
        exact S.symm (S.trans e2 (S.trans (S.mul_congr hi (S.refl _)) (S.one_mul _)))
      exact S.trans e1 (S.trans (S.mul_congr (S.refl _) h) (by cr_ring S.toCR))

/-- `ap (rᵍ · h)` gives `ap h`. -/
theorem ap_of_pow_mul {r h : α} (q : Nat) (H : ap S (S.mul (powS S.toOH r q) h)) : ap S h :=
  S.ap_mul (ap_congr S (S.mul_comm _ _) H)

/-- Equations carried through a chart: `E(φ) = uᵐ·G`, `E = 0` at the image point, `u` apart: `G = 0`. -/
theorem allId_eqs {φ : Nat → ZPoly.PE} {u : Nat} {p p' : Nat → α}
    (henv : ∀ i, S.r (eval S.toOH p' (φ i)) (p i)) (hu : ap S (p' u)) :
    ∀ (es gs : List ZPoly.PE) (ms : List Nat), allId φ u es gs ms = true →
      (∀ e ∈ es, S.r (eval S.toOH p e) S.zero) → ∀ g ∈ gs, S.r (eval S.toOH p' g) S.zero
  | [], [], [], _, _, _, hg => by cases hg
  | e :: es, g :: gs, m :: ms, h, he, g', hg' => by
      have hh := and_true_split h
      have hid := identX_sound S.toOH hh.1 p'
      have v1 := eval_subst S.toOH p' φ e
      have v2 := eval_congr_env S henv e
      have e0 := he e (List.Mem.head _)
      cases hg' with
      | head =>
          -- p'^m · G = E(p) = 0
          have z : S.r (S.mul (powS S.toOH (p' u) m) (eval S.toOH p' g)) S.zero :=
            S.trans (S.symm hid) (S.trans v1 (S.trans v2 e0))
          exact cancel_pow S hu m z
      | tail _ hm => exact allId_eqs henv hu es gs ms hh.2 (fun e h => he e (List.Mem.tail _ h)) g' hm
  | [], [], _ :: _, h, _, _, _ => by cases h
  | [], _ :: _, _, h, _, _, _ => by cases h
  | _ :: _, [], _, h, _, _, _ => by cases h
  | _ :: _, _ :: _, [], h, _, _, _ => by cases h

/-- Conditions carried through a chart: `N(φ) = u^q·H`, `N` apart at the image point: `H` apart. -/
theorem allId_neqs {φ : Nat → ZPoly.PE} {u : Nat} {p p' : Nat → α}
    (henv : ∀ i, S.r (eval S.toOH p' (φ i)) (p i)) :
    ∀ (ns hs : List ZPoly.PE) (qs : List Nat), allId φ u ns hs qs = true →
      (∀ n ∈ ns, ap S (eval S.toOH p n)) → ∀ h ∈ hs, ap S (eval S.toOH p' h)
  | [], [], [], _, _, _, hg => by cases hg
  | n :: ns, h :: hs, q :: qs, H, hn, h', hh' => by
      have hh := and_true_split H
      have hid := identX_sound S.toOH hh.1 p'
      have v1 := eval_subst S.toOH p' φ n
      have v2 := eval_congr_env S henv n
      have a0 := hn n (List.Mem.head _)
      cases hh' with
      | head =>
          have a1 := ap_congr S (S.symm (S.trans v1 v2)) a0
          exact ap_of_pow_mul S q (ap_congr S hid a1)
      | tail _ hm => exact allId_neqs henv ns hs qs hh.2 (fun e h => hn e (List.Mem.tail _ h)) h' hm
  | [], [], _ :: _, H, _, _, _ => by cases H
  | [], _ :: _, _, H, _, _, _ => by cases H
  | _ :: _, [], _, H, _, _, _ => by cases H
  | _ :: _, _ :: _, [], H, _, _, _ => by cases H

theorem inSq_sound {B : Box} {p : Nat → α} (hp : InBox S B p) {u : Nat} {a : D} {ρ : D}
    (h : inSq B u a ρ = true) :
    S.le (S.add (dv S.toOH a) (S.neg (dv S.toOH ρ))) (p u) ∧ S.le (p u) (S.add (dv S.toOH a) (dv S.toOH ρ)) := by
  unfold inSq at h
  cases hB : B u with
  | none => rw [hB] at h; cases h
  | some I =>
      rw [hB] at h
      have hh := and_true_split h
      have m := hp u I hB
      have l := dle_sound S.toOH hh.1
      have r := dle_sound S.toOH hh.2
      have e1 := S.trans (dv_add S.toOH a (dneg ρ)) (S.add_congr (S.refl _) (dv_neg S.toOH ρ))
      have e2 := dv_add S.toOH a ρ
      exact ⟨S.le_trans (S.le_respects e1 (S.refl _) l) m.1, S.le_trans m.2 (S.le_respects (S.refl _) e2 r)⟩

theorem beq_false_symm {u v : Nat} (h : Nat.beq u v = false) : Nat.beq v u = false := by
  cases hb : Nat.beq v u with
  | false => rfl
  | true =>
      have e := Nat.eq_of_beq_eq_true hb
      rw [e, beq_self] at h
      cases h

theorem dv_two : S.r (dv S.toOH two) (S.add S.one S.one) := by
  show S.r (S.mul (S.add (S.add S.one (S.add S.one S.zero)) (S.neg S.zero)) S.one) (S.add S.one S.one)
  cr_ring S.toCR

/-- The chart point: `r` at `u`, `s` at `v`, `p` elsewhere. -/
def cpt (p : Nat → α) (u v : Nat) (r s : α) : Nat → α :=
  fun j => cond (Nat.beq j u) r (cond (Nat.beq j v) s (p j))

theorem cpt_u (p : Nat → α) (u v : Nat) (r s : α) : cpt p u v r s u = r := by
  unfold cpt; rw [beq_self]; rfl
theorem cpt_v (p : Nat → α) {u v : Nat} (r s : α) (h : Nat.beq u v = false) : cpt p u v r s v = s := by
  unfold cpt; rw [beq_false_symm h, beq_self]; rfl

theorem inBox_chart {B : Box} {p : Nat → α} (hp : InBox S B p) {u v : Nat} (huv : Nat.beq u v = false)
    {ρ : D} {r s : α} (hr1 : S.le (S.neg (dv S.toOH ρ)) r) (hr2 : S.le r (dv S.toOH ρ))
    (hs1 : S.le (S.neg (S.add S.one S.one)) s) (hs2 : S.le s (S.add S.one S.one)) :
    InBox S (chartBox B u v ρ) (cpt p u v r s) := by
  intro j J hj
  unfold chartBox upd at hj
  cases hjv : Nat.beq j v with
  | true =>
      rw [hjv] at hj
      cases hj
      have e := Nat.eq_of_beq_eq_true hjv
      rw [e, cpt_v p r s huv]
      have t := dv_two S
      have n := dv_neg S.toOH two
      exact ⟨S.le_respects (S.symm (S.trans n (S.neg_congr t))) (S.refl _) hs1, S.le_respects (S.refl _) (S.symm t) hs2⟩
  | false =>
      rw [hjv] at hj
      cases hju : Nat.beq j u with
      | true =>
          rw [hju] at hj
          cases hj
          have e := Nat.eq_of_beq_eq_true hju
          rw [e, cpt_u]
          exact ⟨S.le_respects (S.symm (dv_neg S.toOH ρ)) (S.refl _) hr1, hr2⟩
      | false =>
          rw [hju] at hj
          have m := hp j J hj
          have pe : cpt p u v r s j = p j := by unfold cpt; rw [hju, hjv]; rfl
          rw [pe]; exact m

theorem env_X {p : Nat → α} {u v : Nat} (huv : Nat.beq u v = false) {a b : D} {r s : α}
    (ex : S.r (p u) (S.add (dv S.toOH a) r)) (ey : S.r (p v) (S.add (dv S.toOH b) (S.mul r s))) :
    ∀ i, S.r (eval S.toOH (cpt p u v r s) (phiX u v a b i)) (p i) := by
  intro i
  unfold phiX
  cases hiu : Nat.beq i u with
  | true =>
      have e := Nat.eq_of_beq_eq_true hiu
      show S.r (S.add (dv S.toOH a) (cpt p u v r s u)) (p i)
      rw [cpt_u, e]; exact S.symm ex
  | false =>
      cases hiv : Nat.beq i v with
      | true =>
          have e := Nat.eq_of_beq_eq_true hiv
          show S.r (S.add (dv S.toOH b) (S.mul (cpt p u v r s u) (cpt p u v r s v))) (p i)
          rw [cpt_u, cpt_v p r s huv, e]; exact S.symm ey
      | false =>
          show S.r (cpt p u v r s i) (p i)
          unfold cpt; rw [hiu, hiv]; exact S.refl _

theorem env_Y {p : Nat → α} {u v : Nat} (huv : Nat.beq u v = false) {a b : D} {r s : α}
    (ex : S.r (p u) (S.add (dv S.toOH a) (S.mul r s))) (ey : S.r (p v) (S.add (dv S.toOH b) r)) :
    ∀ i, S.r (eval S.toOH (cpt p u v r s) (phiY u v a b i)) (p i) := by
  intro i
  unfold phiY
  cases hiu : Nat.beq i u with
  | true =>
      have e := Nat.eq_of_beq_eq_true hiu
      show S.r (S.add (dv S.toOH a) (S.mul (cpt p u v r s u) (cpt p u v r s v))) (p i)
      rw [cpt_u, cpt_v p r s huv, e]; exact S.symm ex
  | false =>
      cases hiv : Nat.beq i v with
      | true =>
          have e := Nat.eq_of_beq_eq_true hiv
          show S.r (S.add (dv S.toOH b) (cpt p u v r s u)) (p i)
          rw [cpt_u, e]; exact S.symm ey
      | false =>
          show S.r (cpt p u v r s i) (p i)
          unfold cpt; rw [hiu, hiv]; exact S.refl _

theorem env_cen {p : Nat → α} {u v : Nat} {a b : D}
    (ex : S.r (p u) (dv S.toOH a)) (ey : S.r (p v) (dv S.toOH b)) :
    ∀ i, S.r (eval S.toOH p (cen u v a b i)) (p i) := by
  intro i
  unfold cen
  cases hiu : Nat.beq i u with
  | true => have e := Nat.eq_of_beq_eq_true hiu; show S.r (dv S.toOH a) (p i); rw [e]; exact S.symm ex
  | false =>
      cases hiv : Nat.beq i v with
      | true => have e := Nat.eq_of_beq_eq_true hiv; show S.r (dv S.toOH b) (p i); rw [e]; exact S.symm ey
      | false => show S.r (p i) (p i); exact S.refl _

theorem eval_zero (p : Nat → α) : S.r (eval S.toOH p (.cst ⟨⟨0, 0⟩, 0⟩)) S.zero := by
  show S.r (S.mul (S.add S.zero (S.neg S.zero)) S.one) S.zero; cr_ring S.toCR

theorem toPEs_eqs {ex atn sn cs : α → α} {p : Nat → α} : ∀ {xs : List XE} {qs : List ZPoly.PE}, toPEs xs = some qs →
    (∀ x ∈ xs, ∃ v, Val S ex atn sn cs p x v ∧ S.r v S.zero) → ∀ q ∈ qs, S.r (eval S.toOH p q) S.zero
  | [], qs, h, _, q, hq => by cases h; cases hq
  | x :: xs, qs, h, hx, q, hq => by
      unfold toPEs at h
      cases h1 : toPE x with
      | none => rw [h1] at h; cases h
      | some q1 =>
          rw [h1] at h
          dsimp only at h
          cases h2 : toPEs xs with
          | none => rw [h2] at h; cases h
          | some qs1 =>
              rw [h2] at h
              cases h
              cases hq with
              | head =>
                  obtain ⟨v, hv, h0⟩ := hx x (List.Mem.head _)
                  exact S.trans (S.symm (val_toPE S h1 hv)) h0
              | tail _ hm => exact toPEs_eqs h2 (fun y hy => hx y (List.Mem.tail _ hy)) q hm

theorem toPEs_neqs {ex atn sn cs : α → α} {p : Nat → α} : ∀ {xs : List XE} {qs : List ZPoly.PE}, toPEs xs = some qs →
    (∀ x ∈ xs, ∃ v, Val S ex atn sn cs p x v ∧ ap S v) → ∀ q ∈ qs, ap S (eval S.toOH p q)
  | [], qs, h, _, q, hq => by cases h; cases hq
  | x :: xs, qs, h, hx, q, hq => by
      unfold toPEs at h
      cases h1 : toPE x with
      | none => rw [h1] at h; cases h
      | some q1 =>
          rw [h1] at h
          dsimp only at h
          cases h2 : toPEs xs with
          | none => rw [h2] at h; cases h
          | some qs1 =>
              rw [h2] at h
              cases h
              cases hq with
              | head =>
                  obtain ⟨v, hv, h0⟩ := hx x (List.Mem.head _)
                  exact ap_congr S (val_toPE S h1 hv) h0
              | tail _ hm => exact toPEs_neqs h2 (fun y hy => hx y (List.Mem.tail _ hy)) q hm

theorem mem_map_ofPE : ∀ {gs : List ZPoly.PE} {x : XE}, x ∈ gs.map ofPE → ∃ g, g ∈ gs ∧ x = ofPE g
  | [], _, h => by cases h
  | g :: gs, x, h => by
      cases h with
      | head => exact ⟨g, List.Mem.head _, rfl⟩
      | tail _ hm =>
          obtain ⟨g', hg', e⟩ := mem_map_ofPE hm
          exact ⟨g', List.Mem.tail _ hg', e⟩

theorem sub_eqs {ex atn sn cs : α → α} {p : Nat → α} {gs : List ZPoly.PE} (h : ∀ g ∈ gs, S.r (eval S.toOH p g) S.zero) :
    ∀ x ∈ gs.map ofPE, ∃ v, Val S ex atn sn cs p x v ∧ S.r v S.zero := by
  intro x hx
  obtain ⟨g, hg, e⟩ := mem_map_ofPE hx
  rw [e]; exact ⟨_, val_ofPE S ex atn sn cs p g, h g hg⟩

theorem sub_neqs {ex atn sn cs : α → α} {p : Nat → α} {hs : List ZPoly.PE} (h : ∀ g ∈ hs, ap S (eval S.toOH p g)) :
    ∀ x ∈ hs.map ofPE, ∃ v, Val S ex atn sn cs p x v ∧ ap S v := by
  intro x hx
  obtain ⟨g, hg, e⟩ := mem_map_ofPE hx
  rw [e]; exact ⟨_, val_ofPE S ex atn sn cs p g, h g hg⟩

/-- **`check_none` IS SOUND.** An accepted certificate leaves no point of the box, and no values of the
expressions there (division included: a quotient's value needs its divisor apart from 0), where every equation
is 0 and every condition apart from 0 — in every constructive ordered field. -/
theorem chk_sound (ex atn sn cs : α → α) : ∀ (c : Cert) (Sy : Sys) (B : Box) (p : Nat → α), chk Sy B c = true → InBox S B p →
    (∀ e ∈ Sy.eqs, ∃ v, Val S ex atn sn cs p e v ∧ S.r v S.zero) → (∀ n ∈ Sy.neqs, ∃ v, Val S ex atn sn cs p n v ∧ ap S v) → False
  | .nz k, Sy, B, p, h, hp, hE, _ => by
      unfold chk at h
      cases hk : nth Sy.eqs k with
      | none => rw [hk] at h; cases h
      | some e =>
          rw [hk] at h
          dsimp only at h
          cases hK : ivX B e with
          | none => rw [hK] at h; cases h
          | some K =>
              rw [hK] at h
              obtain ⟨v, hv, h0⟩ := hE e (nth_mem hk)
              exact nz_sound S (ivX_sound S hp hv K hK) h0 h
  | .nzA k, Sy, B, p, h, hp, hE, _ => by
      unfold chk at h
      cases hk : nth Sy.eqs k with
      | none => rw [hk] at h; cases h
      | some e =>
          rw [hk] at h
          dsimp only at h
          cases hK : afIvX B e with
          | none => rw [hK] at h; cases h
          | some K =>
              rw [hK] at h
              obtain ⟨v, hv, h0⟩ := hE e (nth_mem hk)
              exact nz_sound S (afIvX_sound S hp hv K hK) h0 h
  | .ex j, Sy, B, p, h, _, _, hN => by
      unfold chk at h
      cases hj : nth Sy.neqs j with
      | none => rw [hj] at h; cases h
      | some n =>
          rw [hj] at h
          dsimp only at h
          cases hq : toPE n with
          | none => rw [hq] at h; cases h
          | some q =>
              rw [hq] at h
              have hid := identX_sound S.toOH h p
              obtain ⟨v, hv, ha⟩ := hN n (nth_mem hj)
              exact ap_ne S ha (S.trans (val_toPE S hq hv) (S.trans hid (eval_zero S p)))
  | .split i t δ lo hi, Sy, B, p, h, hp, hE, hN => by
      unfold chk at h
      have hh := and_true_split h
      cases hB : B i with
      | none => rw [hB] at hh; exact Bool.noConfusion hh.2
      | some I =>
          have h2 := hh.2
          rw [hB] at h2
          dsimp only at h2
          have hc := and_true_split h2
          have m := hp i I hB
          have pδ := pos_of_posD S hh.1
          have a1 := dv_add S.toOH t δ
          have a2 := S.trans (dv_add S.toOH t (dneg δ)) (S.add_congr (S.refl _) (dv_neg S.toOH δ))
          cases split_cover S (t := dv S.toOH t) pδ m.1 m.2 with
          | inl hl =>
              exact chk_sound ex atn sn cs lo Sy _ p hc.1
                (inBox_upd S hp ⟨hl.1, S.le_respects (S.refl _) (S.symm a1) hl.2⟩) hE hN
          | inr hr =>
              exact chk_sound ex atn sn cs hi Sy _ p hc.2
                (inBox_upd S hp ⟨S.le_respects (S.symm a2) (S.refl _) hr.1, hr.2⟩) hE hN
  | .chart u v a b ρ j gX mX hX qX tX gY mY hY qY tY, Sy, B, p, h, hp, hE, hN => by
      unfold chk at h
      cases hes : toPEs Sy.eqs with
      | none => rw [hes] at h; cases h
      | some es =>
      rw [hes] at h
      dsimp only at h
      cases hns : toPEs Sy.neqs with
      | none => rw [hns] at h; cases h
      | some ns =>
      rw [hns] at h
      dsimp only at h
      have hE' := toPEs_eqs S hes hE
      have hN' := toPEs_neqs S hns hN
      have s1 := and_true_split h
      have s2 := and_true_split s1.1
      have s3 := and_true_split s2.1
      have s4 := and_true_split s3.1
      have s5 := and_true_split s4.1
      have s6 := and_true_split s5.1
      have s7 := and_true_split s6.1
      have s8 := and_true_split s7.1
      have s9 := and_true_split s8.1
      have s10 := and_true_split s9.1
      have huv : Nat.beq u v = false := by
        cases hb : Nat.beq u v with
        | false => rfl
        | true => have t := s10.1; rw [hb] at t; cases t
      have hxs := inSq_sound S hp s9.2
      have hys := inSq_sound S hp s8.2
      have hc := s7.2
      cases hn : nth ns j with
      | none => rw [hn] at hc; cases hc
      | some n =>
          rw [hn] at hc
          dsimp only at hc
          have apn := hN' n (nth_mem hn)
          refine nn_case (ap S (S.add (p u) (S.neg (dv S.toOH a))) ∨ ap S (S.add (p v) (S.neg (dv S.toOH b))))
            (fun hap => ?_) (fun hno => ?_)
          · cases chart_cover S hxs.1 hxs.2 hys.1 hys.2 hap with
            | inl hX' =>
                obtain ⟨r, s, apr, r1, r2, sl, sh, hxe, hye⟩ := hX'
                have henv := env_X S huv hxe hye
                have hu : ap S (cpt p u v r s u) := by rw [cpt_u]; exact apr
                exact chk_sound ex atn sn cs tX ⟨gX.map ofPE, hX.map ofPE⟩ _ (cpt p u v r s) s4.2 (inBox_chart S hp huv r1 r2 sl sh)
                  (sub_eqs S (allId_eqs S henv hu es gX mX s6.2 hE')) (sub_neqs S (allId_neqs S henv ns hX qX s5.2 hN'))
            | inr hY' =>
                obtain ⟨r, s, apr, r1, r2, sl, sh, hxe, hye⟩ := hY'
                have henv := env_Y S huv hxe hye
                have hu : ap S (cpt p u v r s u) := by rw [cpt_u]; exact apr
                exact chk_sound ex atn sn cs tY ⟨gY.map ofPE, hY.map ofPE⟩ _ (cpt p u v r s) s1.2 (inBox_chart S hp huv r1 r2 sl sh)
                  (sub_eqs S (allId_eqs S henv hu es gY mY s3.2 hE')) (sub_neqs S (allId_neqs S henv ns hY qY s2.2 hN'))
          · have hxe := S.ap_tight (fun h' => hno (Or.inl h'))
            have hye := S.ap_tight (fun h' => hno (Or.inr h'))
            have ex' : S.r (p u) (dv S.toOH a) := by
              have t : S.r (p u) (S.add (S.add (p u) (S.neg (dv S.toOH a))) (dv S.toOH a)) := by cr_ring S.toCR
              exact S.trans t (S.trans (S.add_congr hxe (S.refl _)) (S.zero_add _))
            have ey' : S.r (p v) (dv S.toOH b) := by
              have t : S.r (p v) (S.add (S.add (p v) (S.neg (dv S.toOH b))) (dv S.toOH b)) := by cr_ring S.toCR
              exact S.trans t (S.trans (S.add_congr hye (S.refl _)) (S.zero_add _))
            have hid := identX_sound S.toOH hc p
            have v1 := eval_subst S.toOH p (cen u v a b) n
            have v2 := eval_congr_env S (env_cen S ex' ey') n
            exact ap_ne S apn (S.trans (S.symm (S.trans v1 v2)) (S.trans hid (eval_zero S p)))

end ZNone

namespace ZNone
open ZNumBin ZPoly ZIv ZXE
/-! ## The kernel, both ways, on a system that needs a blow-up.
`E = x² + y² = 0` with `N = x² + y²` apart from 0, on `[−½, ½]²`: no solution, but near the centre every reading
of `E` contains 0. A chart at `(0, 0)`: on both sides `E(φ) = r²·(1 + s²)`, and `1 + s²` is read positive after one
cut of `s` at 0 (overlap ⅛). With `N = 1` instead the centre IS a solution — and the same certificate is refused. -/
private def X : ZPoly.PE := .var 0
private def Y : ZPoly.PE := .var 1
private def sq (e : ZPoly.PE) : ZPoly.PE := .pow e 2
private def E0 : ZPoly.PE := .add (sq X) (sq Y)
private def G0 : ZPoly.PE := .add (.cst ⟨⟨1, 0⟩, 0⟩) (sq Y)
private def half : D := ⟨⟨1, 0⟩, 1⟩
private def B0 : Box := fun i => cond (Nat.beq i 0 || Nat.beq i 1) (some (dneg half, half)) none
private def side : Cert := .split 1 ⟨⟨0, 0⟩, 0⟩ ⟨⟨1, 0⟩, 3⟩ (.nz 0) (.nz 0)
private def C0 : Cert :=
  .chart 0 1 ⟨⟨0, 0⟩, 0⟩ ⟨⟨0, 0⟩, 0⟩ half 0 [G0] [2] [G0] [2] side [G0] [2] [G0] [2] side
example : chk ⟨[ofPE E0], [ofPE E0]⟩ B0 C0 = true := by decide +kernel
example : chk ⟨[ofPE E0], [.cst ⟨⟨1, 0⟩, 0⟩]⟩ B0 C0 = false := by decide +kernel
/-! A dyadic centre: `(x − ½)² + y² = 0` with the same condition, on `[0, 1] × [−½, ½]`, chart at `(½, 0)`. -/
private def Xh : ZPoly.PE := .sub X (.cst half)
private def E2 : ZPoly.PE := .add (sq Xh) (sq Y)
private def B2 : Box := fun i => cond (Nat.beq i 0) (some (⟨⟨0, 0⟩, 0⟩, ⟨⟨1, 0⟩, 0⟩))
  (cond (Nat.beq i 1) (some (dneg half, half)) none)
private def C2 : Cert :=
  .chart 0 1 half ⟨⟨0, 0⟩, 0⟩ half 0 [G0] [2] [G0] [2] side [G0] [2] [G0] [2] side
example : chk ⟨[ofPE E2], [ofPE E2]⟩ B2 C2 = true := by decide +kernel
example : chk ⟨[ofPE E2], [.cst ⟨⟨1, 0⟩, 0⟩]⟩ B2 C2 = false := by decide +kernel
/-! The affine leaf: `x − x + 1` on `[−1, 1]` — the interval reading gives `[−1, 3]` (it cannot cancel), the
affine reading gives exactly `1`. -/
private def B1 : Box := fun i => cond (Nat.beq i 0) (some (⟨⟨0, 1⟩, 0⟩, ⟨⟨1, 0⟩, 0⟩)) none
private def E1 : ZPoly.PE := .add (.sub X X) (.cst ⟨⟨1, 0⟩, 0⟩)
example : chk ⟨[ofPE E1], []⟩ B1 (.nz 0) = false := by decide +kernel
example : chk ⟨[ofPE E1], []⟩ B1 (.nzA 0) = true := by decide +kernel
/-! Division: `1/x − 2` on `[¼, ⅓]` reads inside `[1, 2]` (accepted); on `[⅓, 1]` the solution `x = ½` is in the
box (refused); on `[−1, 1]` the divisor's interval contains 0, so there is no reading (refused). -/
private def Ed : XE := .sub (.div (.cst ⟨⟨1, 0⟩, 0⟩) (.var 0)) (.cst ⟨⟨2, 0⟩, 0⟩)
private def Bd1 : Box := fun i => cond (Nat.beq i 0) (some (⟨⟨1, 0⟩, 2⟩, ⟨⟨21, 0⟩, 6⟩)) none
private def Bd2 : Box := fun i => cond (Nat.beq i 0) (some (⟨⟨21, 0⟩, 6⟩, ⟨⟨1, 0⟩, 0⟩)) none
private def Bd3 : Box := fun i => cond (Nat.beq i 0) (some (⟨⟨0, 1⟩, 0⟩, ⟨⟨1, 0⟩, 0⟩)) none
example : chk ⟨[Ed], []⟩ Bd1 (.nz 0) = true := by decide +kernel
example : chk ⟨[Ed], []⟩ Bd2 (.nz 0) = false := by decide +kernel
example : chk ⟨[Ed], []⟩ Bd3 (.nz 0) = false := by decide +kernel
example : chk ⟨[Ed], []⟩ Bd1 (.nzA 0) = true := by decide +kernel
/-! `exp` and `ln`: `eˣ − 2` on `[1, 2]` reads positive (accepted); on `[0, 1]` the solution `ln 2` is in the box
(refused); `ln x − 1` on `[1, 2]` reads negative (accepted). -/
private def Ee : XE := .sub (.exp (.var 0)) (.cst ⟨⟨2, 0⟩, 0⟩)
private def El : XE := .sub (.ln (.var 0)) (.cst ⟨⟨1, 0⟩, 0⟩)
private def Be1 : Box := fun i => cond (Nat.beq i 0) (some (⟨⟨1, 0⟩, 0⟩, ⟨⟨2, 0⟩, 0⟩)) none
private def Be0 : Box := fun i => cond (Nat.beq i 0) (some (⟨⟨0, 0⟩, 0⟩, ⟨⟨1, 0⟩, 0⟩)) none
example : chk ⟨[Ee], []⟩ Be1 (.nz 0) = true := by decide +kernel
example : chk ⟨[Ee], []⟩ Be0 (.nz 0) = false := by decide +kernel
example : chk ⟨[El], []⟩ Be1 (.nz 0) = true := by decide +kernel
end ZNone

#print axioms ZNone.nth_mem
#print axioms ZNone.nz_sound
#print axioms ZNone.chk_split_intro
#print axioms ZNone.chk_chart_intro
#print axioms ZNone.cancel_pow
#print axioms ZNone.allId_eqs
#print axioms ZNone.allId_neqs
#print axioms ZNone.inBox_chart
#print axioms ZNone.chk_sound
#print axioms ZAff.afE_sound
#print axioms ZAff.afIvE_sound
