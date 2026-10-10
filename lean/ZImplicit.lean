import ZCertify

/-!
# ZImplicit — the rule `zimplicit.py` checks an implicit law's certificate by. Zero axioms.

An implicit law fixes a quantity `x` as a root of `g(x, p) = 0` over a box of parameters `p` (blind test 2,
2026-10-10: a fan's operating point, a pump's, an oil cooler's outlet). The search brings a certificate; the
kernel checks it. Two parts are proved here, for any orders:

  * `enclosure_sound` — a tiling of the search range in `x` (a tree of cuts on `x`), each piece either KEPT
    (inside the hull `[hlo, hhi]`) or RULED OUT by a partition of the parameter box (a tree of cuts on the
    parameters) whose every part reads `g` away from zero: then every root, at every parameter point of the
    box, lies in the hull. (The kernel's list of pieces IS such a tree: cut at each piece boundary.)
  * `root_lower_bound` — with `g` strictly increasing in `x` and, at fixed `x`, never above its value at
    ONE parameter corner (what monotone parameter readings give, `ZCertify.corner_bound`): the root at that
    corner is below every root. The upper bound is the same theorem in the dual orders; together they give
    the tight range `[root at the min corner, root at the max corner]` the kernel reports.

PREMISES, said rather than hidden (as in ZCertify): that a reading which excludes zero on a part means no root
there (`excl_sound`: interval arithmetic, here also the affine reading), and the two monotonicity facts
(derivative signs and the mean value theorem). What is proved is that the way the kernel combines them — the
tiling, the partitions, the hull, the corner — never misplaces a root.
-/

namespace ZImplicit

open ZCertify

variable {α β : Type}

/-! ## The enclosure -/

/-- A piece of the search range: kept, or ruled out by a partition of the parameter box. -/
inductive QLeaf (α : Type) where
  | kept : QLeaf α
  | none : Tree α Unit → QLeaf α

/-- What the kernel checks at a piece. `Excl B`: the reading of `g` over the part `B` excludes zero. -/
def QOK (O : ZCertify.Ord α) (q : Nat) (hlo hhi : α) (Excl : Box α → Prop) : Box α → QLeaf α → Prop
  | B, .kept => O.le hlo (B q).1 ∧ O.le (B q).2 hhi
  | B, .none t => Accepts (fun B' (_ : Unit) => Excl B') B t

/-- A ruled-out piece holds no root (its partition covers it; every part excludes one). -/
theorem none_no_root (O : ZCertify.Ord α) (Root : Point α → Prop) (Excl : Box α → Prop)
    (excl_sound : ∀ B, Excl B → ∀ p, InBox O B p → ¬ Root p) :
    ∀ (t : Tree α Unit) (B : Box α), Accepts (fun B' (_ : Unit) => Excl B') B t →
      ∀ p, InBox O B p → ¬ Root p :=
  accepts_sound O (fun B' (_ : Unit) => Excl B') (fun p => ¬ Root p)
    (fun B _ hok p hp => excl_sound B hok p hp)

/-- THE ENCLOSURE IS SOUND: every root in the box lies in the hull of the kept pieces. -/
theorem enclosure_sound (O : ZCertify.Ord α) (q : Nat) (hlo hhi : α) (Root : Point α → Prop)
    (Excl : Box α → Prop) (excl_sound : ∀ B, Excl B → ∀ p, InBox O B p → ¬ Root p) :
    ∀ (T : Tree α (QLeaf α)) (B : Box α), Accepts (QOK O q hlo hhi Excl) B T →
      ∀ p, InBox O B p → Root p → O.le hlo (p q) ∧ O.le (p q) hhi := by
  apply accepts_sound O (QOK O q hlo hhi Excl) (fun p => Root p → O.le hlo (p q) ∧ O.le (p q) hhi)
  intro B l hok p hp hroot
  cases l with
  | kept => exact ⟨O.trans hok.1 (hp q).1, O.trans (hp q).2 hok.2⟩
  | none t => exact absurd hroot (none_no_root O Root Excl excl_sound t B hok p hp)

/-! ## The monotone root: its range spans the corner roots -/

/-- Strictly below, from a total preorder. -/
def Lt (V : ZCertify.Ord β) (a b : β) : Prop := V.le a b ∧ ¬ V.le b a

/-- THE LOWER CORNER. `G x p`: the law's value at `x` and parameters `p`; a root is `G x p = z`.
`strict`: G strictly increasing in `x` at the corner `c`. `param`: at fixed `x`, the value at any parameter point
of the box is at most the value at the corner `c` (monotone readings toward it). `r` is the root at `c`.
Then no root `x` (at any parameter point of the box) lies strictly below `r`. Stated constructively — "not
strictly below", no excluded middle (with a total preorder it reads as `r ≤ x`). -/
theorem root_lower_bound (A : ZCertify.Ord α) (V : ZCertify.Ord β) (G : α → Point α → β) (z : β) (InP : Point α → Prop)
    (c : Point α) (r : α)
    (strict : ∀ x y, Lt A x y → Lt V (G x c) (G y c))
    (param : ∀ x p, InP p → V.le (G x p) (G x c))
    (root_c : G r c = z) :
    ∀ x p, InP p → G x p = z → ¬ Lt A x r := by
  intro x p hp hx hlt
  have hs : Lt V (G x c) (G r c) := strict x r hlt
  have h1 : V.le (G x p) (G x c) := param x p hp
  rw [hx] at h1
  rw [root_c] at hs
  exact hs.2 h1

/-- The upper corner is the same theorem in the dual orders (`ZCertify.Ord.dual` of `A` and of `V`). -/
theorem root_upper_bound (A : ZCertify.Ord α) (V : ZCertify.Ord β) (G : α → Point α → β) (z : β) (InP : Point α → Prop)
    (c : Point α) (r : α)
    (strict : ∀ x y, Lt (ZCertify.Ord.dual A) x y → Lt (ZCertify.Ord.dual V) (G x c) (G y c))
    (param : ∀ x p, InP p → (ZCertify.Ord.dual V).le (G x p) (G x c))
    (root_c : G r c = z) :
    ∀ x p, InP p → G x p = z → ¬ Lt (ZCertify.Ord.dual A) x r :=
  root_lower_bound (ZCertify.Ord.dual A) (ZCertify.Ord.dual V) G z InP c r strict param root_c

/-! ## Nonvacuity, on the naturals -/

/-- A kept piece `[1, 2]` inside the hull `[0, 5]` is accepted. -/
example : QOK natOrd 0 0 5 (fun _ => True) (fun _ => ((1 : Nat), (2 : Nat))) .kept :=
  ⟨Nat.zero_le 1, (by decide : (2 : Nat) ≤ 5)⟩

end ZImplicit

#print axioms ZImplicit.none_no_root
#print axioms ZImplicit.enclosure_sound
#print axioms ZImplicit.root_lower_bound
#print axioms ZImplicit.root_upper_bound
