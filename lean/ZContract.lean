import ZMin
import ZLP

/-!
# ZContract — HC4 contraction is sound: a contracted box keeps every solution; an empty one has none. Zero axioms.

2026-10-19 (the duel with dReal; the curator's "потом HC4"). `zcontract.py` narrows a box by a constraint: a
forward pass reads every node, a backward pass narrows each node to what its parent allows and each quantity to
what every one of its occurrences allows. `zmin` takes a piece as FAILING a requirement when the requirement MET,
so contracted, leaves the box EMPTY (a leaf `{"cert": {"leaf": "hc4"}}`). What is proved here:

  * the frame — a narrowing step that keeps every solution (`Sound`) composes (`sound_comp`) and repeats
    (`sound_iter`); a box with an end past the other holds no point (`empty_no_point`); so a sound contraction
    to an empty box shows no solution in the original (`contract_empty_sound`), and that is a FAILS leaf in the
    sense of `ZMin` (`hc4_fails`);
  * the rules the backward pass applies — for `z = a + b`: `a ∈ [zl − bh, zh − bl]` (`add_proj`); for
    `z = a − b`: `a ∈ [zl + bl, zh + bh]` (`sub_proj_left`) and `b ∈ [al − zh, ah − zl]` (`sub_proj_right`), in
    any ordered ring given by its laws (`ZLP.ORing`); for a node RECOVERED from its value by a monotone map —
    `a = ln z` under `z = exp a`, `a = z²` under `z = √a`, `a = tan z` under `z = atan a`, `a = z^(1/c)` — the
    ends' brackets bound it (`inv_proj`, `inv_proj_anti`); for two arguments, `a = z / b` with `b` away from 0,
    the corners do (`corner2`).

PREMISES, said rather than hidden: that `zcontract.py` applies these rules (and no others) — exactly the code's
cases, checked by the stand `test_zcontract.py` against points (6000 constraints × 300 points, and a 1 %-too-narrow
projection caught); that the functions' inverse brackets are zfunc's outward ones (their own Lean witnesses:
ZExp, ZLn, ZAtan, ZSqrt). The rules here are the arithmetic; the frame is the composition.

VR discipline: `#print axioms` at the end — the empty list, every line. No `simp`, `omega`, `decide`, classical.
-/

namespace ZContract

open ZCertify

/-! ## The frame -/

section Frame

variable {α : Type}

/-- A narrowing step keeps every solution: a solution in the box is in the narrowed box. -/
def Sound (O : ZCertify.Ord α) (Sol : Point α → Prop) (N : Box α → Box α) : Prop :=
  ∀ B p, InBox O B p → Sol p → InBox O (N B) p

theorem sound_comp (O : ZCertify.Ord α) (Sol : Point α → Prop) (N1 N2 : Box α → Box α)
    (h1 : Sound O Sol N1) (h2 : Sound O Sol N2) : Sound O Sol (fun B => N2 (N1 B)) :=
  fun B p hp hs => h2 (N1 B) p (h1 B p hp hs) hs

/-- `k` rounds of the same step. -/
def iter (N : Box α → Box α) : Nat → Box α → Box α
  | 0, B => B
  | k + 1, B => N (iter N k B)

theorem sound_iter (O : ZCertify.Ord α) (Sol : Point α → Prop) (N : Box α → Box α) (h : Sound O Sol N) :
    ∀ k, Sound O Sol (iter N k) := by
  intro k
  induction k with
  | zero => exact fun _ _ hp _ => hp
  | succ k ih => exact fun B p hp hs => h (iter N k B) p (ih B p hp hs) hs

/-- A box with one end past the other holds no point. -/
theorem empty_no_point (O : ZCertify.Ord α) {B : Box α} {j : Nat} (he : ¬ O.le (B j).1 (B j).2) :
    ∀ p, ¬ InBox O B p :=
  fun _ hp => he (O.trans (hp j).1 (hp j).2)

/-- A sound contraction to an empty box: no solution in the original box. -/
theorem contract_empty_sound (O : ZCertify.Ord α) (Sol : Point α → Prop) (N : Box α → Box α) (hN : Sound O Sol N)
    {B : Box α} {j : Nat} (he : ¬ O.le (N B j).1 (N B j).2) : ∀ p, InBox O B p → ¬ Sol p :=
  fun p hp hs => empty_no_point O he p (hN B p hp hs)

/-- THE HC4 LEAF. A contraction sound for "requirement `i` MET at data `d`", empty on the piece: no mix of the
piece meets it there — `ZMin`'s FAILS leaf condition (with `d` in its data box, `ZMin.LeafOK`). -/
theorem hc4_fails {β δ : Type} (O : ZCertify.Ord α) (P : ZMin.Problem α β δ) (i : Nat) (d : δ) (N : Box α → Box α)
    (hN : Sound O (fun x => P.meets i x d) N) {B : Box α} {j : Nat} (he : ¬ O.le (N B j).1 (N B j).2) :
    ∀ x, InBox O B x → ¬ P.meets i x d :=
  contract_empty_sound O (fun x => P.meets i x d) N hN he

end Frame

/-! ## The arithmetic rules (an ordered ring by its laws) -/

section Ring

variable {α : Type} (R : ZLP.ORing α)

/-- Membership in a closed interval. -/
def In (lo hi a : α) : Prop := R.le lo a ∧ R.le a hi

theorem add_le_add' {a b c d : α} (h1 : R.le a b) (h2 : R.le c d) : R.le (R.add a c) (R.add b d) := by
  have s1 : R.le (R.add a c) (R.add a d) := R.add_le_add_left a h2
  have s2 := R.add_le_add_left d h1
  rw [R.add_comm d a, R.add_comm d b] at s2
  exact R.le_trans s1 s2

theorem zero_add' (a : α) : R.add R.zero a = a := by
  rw [R.add_comm]
  exact R.add_zero a

theorem neg_anti {a b : α} (h : R.le a b) : R.le (R.neg b) (R.neg a) := by
  have h1 := R.add_le_add_left (R.add (R.neg a) (R.neg b)) h
  have e1 : R.add (R.add (R.neg a) (R.neg b)) a = R.neg b := by
    rw [R.add_comm (R.add (R.neg a) (R.neg b)) a, ← R.add_assoc, R.add_neg, zero_add' R]
  have e2 : R.add (R.add (R.neg a) (R.neg b)) b = R.neg a := by
    rw [R.add_assoc, R.add_comm (R.neg b) b, R.add_neg, R.add_zero]
  rw [e1, e2] at h1
  exact h1

theorem cancel_add (a b : α) : R.add (R.add a b) (R.neg b) = a := by
  rw [R.add_assoc, R.add_neg, R.add_zero]

theorem cancel_sub (a b : α) : R.add (R.add a (R.neg b)) b = a := by
  rw [R.add_assoc, R.add_comm (R.neg b) b, R.add_neg, R.add_zero]

/-- `z = a + b`: `a ∈ [zl − bh, zh − bl]`. -/
theorem add_proj {a b z zl zh bl bh : α} (hz : z = R.add a b) (hzi : In R zl zh z) (hbi : In R bl bh b) :
    In R (R.add zl (R.neg bh)) (R.add zh (R.neg bl)) a := by
  have ha : a = R.add z (R.neg b) := by rw [hz, cancel_add R]
  rw [ha]
  exact ⟨add_le_add' R hzi.1 (neg_anti R hbi.2), add_le_add' R hzi.2 (neg_anti R hbi.1)⟩

/-- `z = a − b`: `a ∈ [zl + bl, zh + bh]`. -/
theorem sub_proj_left {a b z zl zh bl bh : α} (hz : z = R.add a (R.neg b)) (hzi : In R zl zh z)
    (hbi : In R bl bh b) : In R (R.add zl bl) (R.add zh bh) a := by
  have ha : a = R.add z b := by rw [hz, cancel_sub R]
  rw [ha]
  exact ⟨add_le_add' R hzi.1 hbi.1, add_le_add' R hzi.2 hbi.2⟩

/-- `z = a − b`: `b ∈ [al − zh, ah − zl]` (from `a = b + z`, the sum's rule). -/
theorem sub_proj_right {a b z al ah zl zh : α} (hz : z = R.add a (R.neg b)) (hai : In R al ah a)
    (hzi : In R zl zh z) : In R (R.add al (R.neg zh)) (R.add ah (R.neg zl)) b := by
  have ha : a = R.add b z := by rw [hz, R.add_comm b (R.add a (R.neg b)), cancel_sub R]
  exact add_proj R ha hai hzi

end Ring

/-! ## Monotone inverses and corners -/

section Mono

variable {α β γ : Type}

/-- A node RECOVERED from its value by a map `g` increasing on `[zl, zh]` (`a = ln z` under `z = exp a`, …): the
brackets of `g` at the ends bound it. -/
theorem inv_proj (O : ZCertify.Ord α) (V : ZCertify.Ord β) (g : β → α) {zl zh z : β} {lo hi a : α}
    (mono : ∀ u v, V.le zl u → V.le u v → V.le v zh → O.le (g u) (g v))
    (ha : a = g z) (hz1 : V.le zl z) (hz2 : V.le z zh) (hlo : O.le lo (g zl)) (hhi : O.le (g zh) hi) :
    O.le lo a ∧ O.le a hi := by
  rw [ha]
  exact ⟨O.trans hlo (mono zl z (V.refl zl) hz1 hz2), O.trans (mono z zh hz1 hz2 (V.refl zh)) hhi⟩

/-- The same for a decreasing map (`a = z^(1/c)` with `c < 0`, `a = 1/z`, …). -/
theorem inv_proj_anti (O : ZCertify.Ord α) (V : ZCertify.Ord β) (g : β → α) {zl zh z : β} {lo hi a : α}
    (anti : ∀ u v, V.le zl u → V.le u v → V.le v zh → O.le (g v) (g u))
    (ha : a = g z) (hz1 : V.le zl z) (hz2 : V.le z zh) (hlo : O.le lo (g zh)) (hhi : O.le (g zl) hi) :
    O.le lo a ∧ O.le a hi := by
  rw [ha]
  exact ⟨O.trans hlo (anti z zh hz1 hz2 (V.refl zh)), O.trans (anti zl z (V.refl zl) hz1 hz2) hhi⟩

/-- TWO ARGUMENTS BY CORNERS: `a = g z b`, increasing in `z` on `[zl, zh]` for every `b` of its interval, and in
`b` the least at `bmin` and the greatest at `bmax` (ends of `b`'s interval, chosen by the sign of `g`'s slope —
`z / b` with `b` away from 0). The two corners bound `a`. -/
theorem corner2 (O : ZCertify.Ord α) (V : ZCertify.Ord β) (W : ZCertify.Ord γ) (g : β → γ → α) {zl zh z : β} {bl bh b bmin bmax : γ}
    {lo hi a : α}
    (monoZ : ∀ c, W.le bl c → W.le c bh → ∀ u v, V.le zl u → V.le u v → V.le v zh → O.le (g u c) (g v c))
    (minB : ∀ u, V.le zl u → V.le u zh → ∀ c, W.le bl c → W.le c bh → O.le (g u bmin) (g u c))
    (maxB : ∀ u, V.le zl u → V.le u zh → ∀ c, W.le bl c → W.le c bh → O.le (g u c) (g u bmax))
    (hmin : W.le bl bmin ∧ W.le bmin bh) (hmax : W.le bl bmax ∧ W.le bmax bh)
    (ha : a = g z b) (hz1 : V.le zl z) (hz2 : V.le z zh) (hb1 : W.le bl b) (hb2 : W.le b bh)
    (hlo : O.le lo (g zl bmin)) (hhi : O.le (g zh bmax) hi) :
    O.le lo a ∧ O.le a hi := by
  rw [ha]
  have l1 : O.le (g zl bmin) (g z bmin) := monoZ bmin hmin.1 hmin.2 zl z (V.refl zl) hz1 hz2
  have l2 : O.le (g z bmin) (g z b) := minB z hz1 hz2 b hb1 hb2
  have u1 : O.le (g z b) (g z bmax) := maxB z hz1 hz2 b hb1 hb2
  have u2 : O.le (g z bmax) (g zh bmax) := monoZ bmax hmax.1 hmax.2 z zh hz1 hz2 (V.refl zh)
  exact ⟨O.trans hlo (O.trans l1 l2), O.trans (O.trans u1 u2) hhi⟩

end Mono

end ZContract

#print axioms ZContract.sound_comp
#print axioms ZContract.sound_iter
#print axioms ZContract.empty_no_point
#print axioms ZContract.contract_empty_sound
#print axioms ZContract.hc4_fails
#print axioms ZContract.add_le_add'
#print axioms ZContract.zero_add'
#print axioms ZContract.neg_anti
#print axioms ZContract.cancel_add
#print axioms ZContract.cancel_sub
#print axioms ZContract.add_proj
#print axioms ZContract.sub_proj_left
#print axioms ZContract.sub_proj_right
#print axioms ZContract.inv_proj
#print axioms ZContract.inv_proj_anti
#print axioms ZContract.corner2
