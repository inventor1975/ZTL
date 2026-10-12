import ZCertify

/-!
# ZMin — the rule `zmin.py` checks a lower bound on a NONLINEAR minimum by. Zero axioms.

2026-10-12 (the universal stand's gap J3, the curator's "да"): continuous amounts that enter the requirements
through a ratio, a log, an exponential — no duality at hand. The claim "every ROBUST mix costs at least L" is
made checkable by a split of the amounts' box (`ZCertify.Tree`) whose every leaf is one of two kinds:

  * COST  — the objective is `≥ L` on the piece;
  * FAILS — requirement `i`, at ONE point `d` of its own data box, is not met by any mix of the piece.

A robust mix meets every requirement for EVERY point of the data, so a FAILS leaf holds none of them; a COST
leaf bounds them all. What is proved here:

  * `fails_not_robust` — a failing point inside the data box excludes every mix of the piece;
  * `min_sound`        — an accepted tree: every robust mix of the box costs at least `L`;
  * `no_mix`           — an accepted tree with FAILS leaves only: no robust mix exists in the box.

PREMISES, said rather than hidden: that the kernel's readings decide its leaves — a COST leaf's `L ≤ f` on the
piece and a FAILS leaf's "not met for every mix of the piece" are `zcertify.check` verdicts, whose own rule is
`ZCertify.certificate_sound` (with its premises `iv_sound`, `deriv_sound`). Here they enter as the leaf
predicate `ok`, exactly as the kernel's walk takes them. The tree's cover is `ZCertify.accepts_sound`.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace ZMin

open ZCertify

variable {α β δ : Type}

/-- A leaf's payload: a cost leaf, or requirement `i` failing at data point `d`. -/
inductive Leaf (δ : Type) where
  | cost  : Leaf δ
  | fails : Nat → δ → Leaf δ

/-- The problem: the objective `f`, the requirements `meets i x d` ("mix `x` meets requirement `i` at data `d`"),
each requirement's data box `inData i d`, and the bound `L` under the value order `V`. -/
structure Problem (α β δ : Type) where
  f      : Point α → β
  meets  : Nat → Point α → δ → Prop
  inData : Nat → δ → Prop

/-- A ROBUST mix: every requirement, at every point of its data box. -/
def Robust (P : Problem α β δ) (x : Point α) : Prop :=
  ∀ i d, P.inData i d → P.meets i x d

/-- What the kernel accepts at a leaf on piece `B` (each conjunct is one of its `zcertify.check` verdicts). -/
def LeafOK (O : ZCertify.Ord α) (V : ZCertify.Ord β) (P : Problem α β δ) (L : β) (B : Box α) : Leaf δ → Prop
  | .cost      => ∀ x, InBox O B x → V.le L (P.f x)
  | .fails i d => P.inData i d ∧ ∀ x, InBox O B x → ¬ P.meets i x d

/-- A failing point inside the data box excludes every mix of the piece from the robust ones. -/
theorem fails_not_robust (O : ZCertify.Ord α) (P : Problem α β δ) {B : Box α} {i : Nat} {d : δ}
    (hd : P.inData i d) (hno : ∀ x, InBox O B x → ¬ P.meets i x d) :
    ∀ x, InBox O B x → ¬ Robust P x := by
  intro x hx hr
  exact hno x hx (hr i d hd)

/-- An accepted tree: every robust mix of the box costs at least `L`. -/
theorem min_sound (O : ZCertify.Ord α) (V : ZCertify.Ord β) (P : Problem α β δ) (L : β) :
    ∀ (t : Tree α (Leaf δ)) (B : Box α), Accepts (LeafOK O V P L) B t →
      ∀ x, InBox O B x → Robust P x → V.le L (P.f x) := by
  intro t B hacc x hx
  apply accepts_sound O (LeafOK O V P L) (fun x => Robust P x → V.le L (P.f x)) _ t B hacc x hx
  intro B' l hl y hy hr
  cases l with
  | cost => exact hl y hy
  | fails i d => exact absurd hr (fails_not_robust O P hl.1 hl.2 y hy)

/-- Only FAILS leaves. -/
def AllFails : Tree α (Leaf δ) → Prop
  | .leaf .cost        => False
  | .leaf (.fails _ _) => True
  | .split _ _ lo hi   => AllFails lo ∧ AllFails hi

/-- With FAILS leaves only, an accepted tree shows no robust mix exists in the box. -/
theorem no_mix (O : ZCertify.Ord α) (V : ZCertify.Ord β) (P : Problem α β δ) (L : β) :
    ∀ (t : Tree α (Leaf δ)) (B : Box α), AllFails t → Accepts (LeafOK O V P L) B t →
      ∀ x, InBox O B x → ¬ Robust P x := by
  intro t
  induction t with
  | leaf l =>
      intro B hall hacc x hx
      cases l with
      | cost => exact absurd hall (by intro h; exact h)
      | fails i d => exact fails_not_robust O P hacc.1 hacc.2 x hx
  | split i t lo hi ihlo ihhi =>
      intro B hall hacc x hx
      cases cut_cover O i t hx with
      | inl h1 => exact ihlo _ hall.1 hacc.1 x h1
      | inr h2 => exact ihhi _ hall.2 hacc.2 x h2

end ZMin

#print axioms ZMin.fails_not_robust
#print axioms ZMin.min_sound
#print axioms ZMin.no_mix
