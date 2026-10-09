/-!
# ZCertify — the rule `zcertify.py` checks a brought certificate by. Zero axioms.

The decision of 2026-10-09: the kernel takes no budgets. A search, wherever it
runs, brings a CERTIFICATE — a bisection tree over the box — and the kernel only
checks it: every split cuts a piece at a point, every leaf is either an
INTERVAL leaf (a reading of the expression over the piece lies under the bound)
or a MONOTONE leaf (a sign per quantity, the bound checked at ONE corner).

What is proved here — the logic of the rule, for any orders:

  * `cut_cover`     — a cut piece is covered by its two halves;
  * `accepts_sound` — a tree whose every leaf holds on its piece shows the bound
                      on the whole box (induction over the tree);
  * `corner_bound`  — monotone in each listed quantity, toward its sign, on the
                      piece: every point is below the corner (the quantities moved
                      one at a time, each step staying in the piece);
  * `monotone_leaf` — with the value depending on the listed quantities only, the
                      ONE corner the kernel evaluates bounds the whole piece;
  * `certificate_sound` — the two leaf kinds together: an accepted certificate
                      shows `f p ≤ c` for every point of the box.

What stays a PREMISE, said rather than hidden (the parameters `iv_sound` and
`deriv_sound`): that the interval reading encloses the expression on a piece,
and that a derivative read non-negative on a piece makes the expression monotone
there. The first is interval arithmetic, the second the mean value theorem; on
the rationals the kernel computes over they hold, but neither is proved in this
module — without a real-number library, and on the empty axiom list, the step
from a derivative to monotonicity is not available. What is proved is that,
GIVEN sound readings, the way the kernel combines them — the cuts, the corner,
the dependence — never accepts a false bound.

Orders are parameters (`Ord`), not `Int` or `ℚ`: core `Int.le_total` carries
`propext` on this toolchain (probed 2026-10-10), and the kernel's numbers are
fractions anyway. The same theorem serves `≥ c` through the dual value order.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace ZCertify

/-- A total preorder, given by its laws (no typeclass: nothing is borrowed). -/
structure Ord (α : Type) where
  le    : α → α → Prop
  refl  : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  total : ∀ a b, le a b ∨ le b a

/-- A point gives every quantity (by index) a value; a box gives each an interval. -/
def Point (α : Type) := Nat → α
def Box (α : Type) := Nat → α × α

variable {α β : Type}

def InBox (O : Ord α) (B : Box α) (p : Point α) : Prop :=
  ∀ i, O.le (B i).1 (p i) ∧ O.le (p i) (B i).2

/-- The point with quantity `i` moved to `v`. -/
def upd (p : Point α) (i : Nat) (v : α) : Point α :=
  fun j => match Nat.decEq j i with
    | isTrue _  => v
    | isFalse _ => p j

/-- The lower half of a cut at `i = t` (its top becomes `t`) and the upper half. -/
def cutLo (B : Box α) (i : Nat) (t : α) : Box α :=
  fun j => match Nat.decEq j i with
    | isTrue _  => ((B j).1, t)
    | isFalse _ => B j

def cutHi (B : Box α) (i : Nat) (t : α) : Box α :=
  fun j => match Nat.decEq j i with
    | isTrue _  => (t, (B j).2)
    | isFalse _ => B j

/-- A cut piece is covered by its halves: a point lies in one of them. -/
theorem cut_cover (O : Ord α) {B : Box α} {p : Point α} (i : Nat) (t : α)
    (h : InBox O B p) : InBox O (cutLo B i t) p ∨ InBox O (cutHi B i t) p := by
  cases O.total (p i) t with
  | inl hle =>
      apply Or.inl
      intro j
      unfold cutLo
      cases Nat.decEq j i with
      | isTrue e => subst e; exact ⟨(h j).1, hle⟩
      | isFalse _ => exact h j
  | inr hge =>
      apply Or.inr
      intro j
      unfold cutHi
      cases Nat.decEq j i with
      | isTrue e => subst e; exact ⟨hge, (h j).2⟩
      | isFalse _ => exact h j

/-- A certificate: cuts, and leaves carrying a payload (the leaf's kind and data). -/
inductive Tree (α L : Type) where
  | leaf  : L → Tree α L
  | split : Nat → α → Tree α L → Tree α L → Tree α L

/-- The kernel's walk: every leaf accepted on the piece it is reached at. -/
def Accepts {L : Type} (ok : Box α → L → Prop) : Box α → Tree α L → Prop
  | B, .leaf l => ok B l
  | B, .split i t lo hi => Accepts ok (cutLo B i t) lo ∧ Accepts ok (cutHi B i t) hi

/-- An accepted tree carries any property its leaves carry, over the whole box. -/
theorem accepts_sound (O : Ord α) {L : Type} (ok : Box α → L → Prop) (P : Point α → Prop)
    (hleaf : ∀ B l, ok B l → ∀ p, InBox O B p → P p) :
    ∀ (t : Tree α L) (B : Box α), Accepts ok B t → ∀ p, InBox O B p → P p := by
  intro t
  induction t with
  | leaf l => intro B hacc p hp; exact hleaf B l hacc p hp
  | split i t lo hi ihlo ihhi =>
      intro B hacc p hp
      cases cut_cover O i t hp with
      | inl h1 => exact ihlo _ hacc.1 p h1
      | inr h2 => exact ihhi _ hacc.2 p h2

/-! ## The monotone leaf: one corner bounds the piece -/

/-- The end of quantity `i`'s interval its sign points to (`true`: the top). -/
def endOf (B : Box α) (s : Bool) (i : Nat) : α :=
  match s with
  | true  => (B i).2
  | false => (B i).1

/-- Monotone toward the sign on the piece: moving quantity `i` to its end never
lowers the value (in the value order `V`). This is what `deriv_sound` supplies. -/
def Mono (O : Ord α) (V : Ord β) (f : Point α → β) (B : Box α) (i : Nat) (s : Bool) : Prop :=
  ∀ p, InBox O B p → V.le (f p) (f (upd p i (endOf B s i)))

/-- Moving one quantity to an end of its interval stays in the piece. -/
theorem upd_end_inbox (O : Ord α) {B : Box α} {p : Point α} (i : Nat) (s : Bool)
    (h : InBox O B p) : InBox O B (upd p i (endOf B s i)) := by
  intro j
  unfold upd
  cases Nat.decEq j i with
  | isTrue e =>
      subst e
      cases s with
      | true  => exact ⟨O.trans (h j).1 (h j).2, O.refl _⟩
      | false => exact ⟨O.refl _, O.trans (h j).1 (h j).2⟩
  | isFalse _ => exact h j

/-- The corner reached by moving the listed quantities, one at a time. -/
def cornerOn (B : Box α) (sg : Nat → Bool) : List Nat → Point α → Point α
  | [], p => p
  | i :: ns, p => cornerOn B sg ns (upd p i (endOf B (sg i) i))

/-- Every point of the piece is below the corner its signs point to. -/
theorem corner_bound (O : Ord α) (V : Ord β) (f : Point α → β) (B : Box α) (sg : Nat → Bool) :
    ∀ (ns : List Nat), (∀ i, List.Mem i ns → Mono O V f B i (sg i)) →
      ∀ p, InBox O B p → V.le (f p) (f (cornerOn B sg ns p)) := by
  intro ns
  induction ns with
  | nil => intro _ p _; exact V.refl _
  | cons i ns ih =>
      intro hm p hp
      have step : V.le (f p) (f (upd p i (endOf B (sg i) i))) := hm i (List.Mem.head ns) p hp
      have rest := ih (fun j hj => hm j (List.Mem.tail i hj)) _ (upd_end_inbox O i (sg i) hp)
      exact V.trans step rest

/-- The full corner: every quantity at the end its sign names. -/
def corner (B : Box α) (sg : Nat → Bool) : Point α := fun j => endOf B (sg j) j

/-- `upd` at its own index gives the new value. -/
theorem upd_at (p : Point α) (i : Nat) (v : α) : upd p i v i = v := by
  unfold upd
  cases Nat.decEq i i with
  | isTrue _ => rfl
  | isFalse ne => exact absurd rfl ne

/-- Walking further keeps a quantity already at its corner value there. -/
theorem cornerOn_keeps (B : Box α) (sg : Nat → Bool) :
    ∀ (ns : List Nat) (q : Point α) (j : Nat), q j = endOf B (sg j) j →
      cornerOn B sg ns q j = corner B sg j := by
  intro ns
  induction ns with
  | nil => intro q j h; exact h
  | cons k ns ih =>
      intro q j h
      apply ih
      unfold upd
      cases Nat.decEq j k with
      | isTrue e => subst e; rfl
      | isFalse _ => exact h

/-- On the listed quantities the walked corner IS the full corner, whatever the start. -/
theorem cornerOn_agrees (B : Box α) (sg : Nat → Bool) :
    ∀ (ns : List Nat) (p : Point α) (j : Nat), List.Mem j ns → cornerOn B sg ns p j = corner B sg j := by
  intro ns
  induction ns with
  | nil => intro _ _ hj; cases hj
  | cons i ns ih =>
      intro p j hj
      show cornerOn B sg ns (upd p i (endOf B (sg i) i)) j = corner B sg j
      cases hj with
      | head => exact cornerOn_keeps B sg ns _ i (upd_at p i _)
      | tail _ hj' => exact ih _ j hj'

/-- THE MONOTONE LEAF. The value depends on the listed quantities only; it is
monotone toward each one's sign on the piece; and at the one full corner it is
under the bound. Then it is under the bound on the whole piece. -/
theorem monotone_leaf (O : Ord α) (V : Ord β) (f : Point α → β) (B : Box α) (sg : Nat → Bool)
    (ns : List Nat) (c : β)
    (dep : ∀ p q : Point α, (∀ j, List.Mem j ns → p j = q j) → f p = f q)
    (mono : ∀ i, List.Mem i ns → Mono O V f B i (sg i))
    (at_corner : V.le (f (corner B sg)) c) :
    ∀ p, InBox O B p → V.le (f p) c := by
  intro p hp
  have h1 := corner_bound O V f B sg ns mono p hp
  have h2 : f (cornerOn B sg ns p) = f (corner B sg) :=
    dep _ _ (fun j hj => cornerOn_agrees B sg ns p j hj)
  rw [h2] at h1
  exact V.trans h1 at_corner

/-! ## The certificate, both leaf kinds -/

/-- A leaf: an interval reading, or a sign for every quantity. -/
inductive Leaf where
  | interval : Leaf
  | monotone : (Nat → Bool) → Leaf

/-- What the kernel checks at a leaf. `IvOK B`: the interval reading on the piece
lies under the bound. `DerivOK B i s`: the derivative in `i` is read with sign `s`
on the piece. Both are computed by the kernel; their meaning is the premise. -/
def LeafOK (V : Ord β) (f : Point α → β) (ns : List Nat) (c : β)
    (IvOK : Box α → Prop) (DerivOK : Box α → Nat → Bool → Prop) : Box α → Leaf → Prop
  | B, .interval => IvOK B
  | B, .monotone sg => (∀ i, List.Mem i ns → DerivOK B i (sg i)) ∧ V.le (f (corner B sg)) c

/-- THE RULE IS SOUND. Given sound readings — an interval reading encloses the
value (`iv_sound`), a derivative read with a sign makes the value monotone toward
it (`deriv_sound`) — and a value that depends on the listed quantities only, an
accepted certificate shows the bound on every point of the box. -/
theorem certificate_sound (O : Ord α) (V : Ord β) (f : Point α → β) (ns : List Nat) (c : β)
    (dep : ∀ p q : Point α, (∀ j, List.Mem j ns → p j = q j) → f p = f q)
    (IvOK : Box α → Prop) (DerivOK : Box α → Nat → Bool → Prop)
    (iv_sound : ∀ B, IvOK B → ∀ p, InBox O B p → V.le (f p) c)
    (deriv_sound : ∀ B i s, DerivOK B i s → Mono O V f B i s) :
    ∀ (t : Tree α Leaf) (B : Box α),
      Accepts (LeafOK V f ns c IvOK DerivOK) B t → ∀ p, InBox O B p → V.le (f p) c := by
  apply accepts_sound O _ (fun p => V.le (f p) c)
  intro B l hok p hp
  cases l with
  | interval => exact iv_sound B hok p hp
  | monotone sg =>
      exact monotone_leaf O V f B sg ns c dep
        (fun i hi => deriv_sound B i (sg i) (hok.1 i hi)) hok.2 p hp

/-- The lower bound `f p ≥ c` is the same theorem in the dual value order. -/
def Ord.dual (V : Ord β) : Ord β where
  le a b := V.le b a
  refl a := V.refl a
  trans h1 h2 := V.trans h2 h1
  total a b := V.total b a

/-! ## Nonvacuity: the orders exist, on the naturals, axiom-free -/

def natOrd : Ord Nat where
  le := Nat.le
  refl := Nat.le_refl
  trans := Nat.le_trans
  total := Nat.le_total

/-- The point 7 of `[0, 10]` lies in a half of the cut at 5 — the cover, on numbers. -/
example : InBox natOrd (cutLo (fun _ => (0, 10)) 0 5) (fun _ => 7) ∨
          InBox natOrd (cutHi (fun _ => (0, 10)) 0 5) (fun _ => 7) :=
  cut_cover natOrd 0 5 (fun _ => ⟨(by decide : (0 : Nat) ≤ 7), (by decide : (7 : Nat) ≤ 10)⟩)

end ZCertify

#print axioms ZCertify.cut_cover
#print axioms ZCertify.accepts_sound
#print axioms ZCertify.upd_end_inbox
#print axioms ZCertify.corner_bound
#print axioms ZCertify.upd_at
#print axioms ZCertify.cornerOn_keeps
#print axioms ZCertify.cornerOn_agrees
#print axioms ZCertify.monotone_leaf
#print axioms ZCertify.certificate_sound
#print axioms ZCertify.Ord.dual
#print axioms ZCertify.natOrd
