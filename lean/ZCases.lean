import ZCertify
import ZLP

/-!
# ZCases — the rule `zcertify._case_reading` reads a branched expression by. Zero axioms.

A branch (`min`, `max`, `ifpos`) the plain reading cannot decide on a piece is CHOSEN, both ways, one at a time as a
tree; each choice keeps the condition under which that side is taken, as `g ≤ 0` (closed); every leaf — the
expression with its branches resolved — is read with its conditions, by weak duality; a leaf whose conditions
cannot hold together is skipped; the hull of the leaves' readings is the reading of the expression. An OUTER
`min`/`max` is read through its arguments' readings. Since 2026-10-11 (2a24683), "not proved in Lean" — now:

  * `cases_sound`     — every point of the box is explained by some leaf whose conditions hold there (the
                        branch semantics, `Explains`, a premise below); so if every leaf's reading bounds its
                        resolved expression wherever its conditions hold, the bounds hold for the expression;
  * `impossible_leaf` — a leaf whose conditions hold nowhere needs no reading (it bounds vacuously);
  * `dual_leaf_low`, `dual_leaf_impossible` — a leaf's lower bound under its conditions `g_j ≤ 0`, and its
                        skipping, are `ZLP.lower_bound_sound` / `ZLP.infeasible_sound` with `h_j = −g_j`;
  * `min_enclosure`, `max_enclosure` — an outer `min`/`max` lies between the `min`/`max` of its arguments' ends;
  * `meet_enclosure`  — two sound enclosures meet in a sound one (the kernel intersects with the plain reading).

PREMISES, said rather than hidden: `Explains` — that a choice's condition holds at a point where that side is the
one taken, and the resolved expression then equals the original (the semantics of `min`/`max`/`ifpos`, with the
closed conditions: at `ifpos 0` both conditions hold, the TRUE side is the one explained); the readings of the
leaves (interval and affine arithmetic, as in ZCertify) and the box-minimum of the dual form (as in ZLP).
What is proved is that the tree, the conditions, the skipping, the hull and the outer `min`/`max` never let a
value of the expression fall outside the reported bounds.

Orders and lattices are parameters, nothing borrowed (as in ZCertify, ZLP). `#print axioms` at the end.
-/

namespace ZCases

variable {P β α : Type}

/-- A case tree: a leaf holds the expression its choices resolved to; a node chooses between two sides, each with
the condition under which it is taken. -/
inductive Tree (P β : Type) where
  | leaf : (P → β) → Tree P β
  | node : (P → Prop) → Tree P β → (P → Prop) → Tree P β → Tree P β

/-- `p` is explained by the tree for the expression `E`: at a node, the side taken at `p` has its condition true
there and its subtree explains `p`; at a leaf, the resolved expression equals `E` at `p`. -/
def Explains (E : P → β) : Tree P β → P → Prop
  | .leaf f, p => E p = f p
  | .node c1 t1 c2 t2, p => (c1 p ∧ Explains E t1 p) ∨ (c2 p ∧ Explains E t2 p)

/-- The leaves with the conditions accumulated on the way to them. -/
def leaves : Tree P β → (P → Prop) → List ((P → β) × (P → Prop))
  | .leaf f, acc => [(f, acc)]
  | .node c1 t1 c2 t2, acc => leaves t1 (fun p => acc p ∧ c1 p) ++ leaves t2 (fun p => acc p ∧ c2 p)

/-- Membership in an append and in a map, by induction (the library's `List.mem_append` and `List.mem_map` carry
`propext` / `Quot.sound` on this toolchain — the theorems here stay axiom-free). -/
theorem mem_append_left {γ : Type} {x : γ} : ∀ {l1 : List γ} (l2 : List γ), List.Mem x l1 → List.Mem x (l1 ++ l2)
  | _ :: _, _, .head _ => .head _
  | _ :: _, l2, .tail _ h => .tail _ (mem_append_left l2 h)

theorem mem_append_right {γ : Type} {x : γ} : ∀ (l1 : List γ) {l2 : List γ}, List.Mem x l2 → List.Mem x (l1 ++ l2)
  | [], _, h => h
  | _ :: t, _, h => .tail _ (mem_append_right t h)

theorem mem_map_inv {γ δ : Type} (f : γ → δ) {y : δ} : ∀ {l : List γ}, List.Mem y (l.map f) →
    ∃ x, List.Mem x l ∧ f x = y
  | a :: _, .head _ => ⟨a, .head _, rfl⟩
  | _ :: t, .tail _ h => let ⟨x, hx, e⟩ := mem_map_inv f (l := t) h; ⟨x, .tail _ hx, e⟩

/-- A leaf is BOUNDED by `[lo, hi]` when its resolved expression lies in it wherever its conditions hold. -/
def Bounded (O : ZCertify.Ord β) (lo hi : β) (l : (P → β) × (P → Prop)) : Prop :=
  ∀ p, l.2 p → O.le lo (l.1 p) ∧ O.le (l.1 p) hi

/-- A leaf whose conditions hold nowhere is bounded by anything: the kernel skips it. -/
theorem impossible_leaf (O : ZCertify.Ord β) (lo hi : β) (l : (P → β) × (P → Prop)) (h : ∀ p, ¬ l.2 p) :
    Bounded O lo hi l :=
  fun p hp => absurd hp (h p)

theorem cases_sound_acc (O : ZCertify.Ord β) (E : P → β) (lo hi : β) :
    ∀ (t : Tree P β) (acc : P → Prop), (∀ l, List.Mem l (leaves t acc) → Bounded O lo hi l) →
      ∀ p, acc p → Explains E t p → O.le lo (E p) ∧ O.le (E p) hi
  | .leaf f, acc, hl, p, hacc, hx => by
      have hb := hl (f, acc) (List.Mem.head _) p hacc
      have hx' : E p = f p := hx
      rw [hx']
      exact hb
  | .node c1 t1 c2 t2, acc, hl, p, hacc, hx => by
      cases hx with
      | inl h1 =>
          exact cases_sound_acc O E lo hi t1 (fun p => acc p ∧ c1 p)
            (fun l hm => hl l (mem_append_left _ hm)) p ⟨hacc, h1.1⟩ h1.2
      | inr h2 =>
          exact cases_sound_acc O E lo hi t2 (fun p => acc p ∧ c2 p)
            (fun l hm => hl l (mem_append_right _ hm)) p ⟨hacc, h2.1⟩ h2.2

/-- THE CASE READING IS SOUND. Every point of the box explained by the tree (the branch semantics), every leaf
bounded under its conditions (or impossible): the expression lies in `[lo, hi]` at every point of the box. -/
theorem cases_sound (O : ZCertify.Ord β) (E : P → β) (lo hi : β) (t : Tree P β) (inBox : P → Prop)
    (explained : ∀ p, inBox p → Explains E t p)
    (bounded : ∀ l, List.Mem l (leaves t inBox) → Bounded O lo hi l) :
    ∀ p, inBox p → O.le lo (E p) ∧ O.le (E p) hi :=
  fun p hp => cases_sound_acc O E lo hi t inBox bounded p hp (explained p hp)

/-! ## A leaf's conditions by weak duality: ZLP with `h_j = −g_j` -/

/-- `g ≤ 0` gives `0 ≤ −g`. -/
theorem neg_nonneg (R : ZLP.ORing α) {g : α} (h : R.le g R.zero) : R.le R.zero (R.neg g) := by
  have h2 := R.add_le_add_left (R.neg g) h
  rw [R.add_comm (R.neg g) g, R.add_neg, R.add_zero] at h2
  exact h2

/-- A LEAF'S LOWER BOUND UNDER ITS CONDITIONS. At a point where every condition `g_j ≤ 0` holds, with any
multipliers `λ_j ≥ 0` and the kernel's box-minimum `L` of `f − Σ λ_j·(−g_j)` (= `f + Σ λ_j g_j`): `L ≤ f`. -/
theorem dual_leaf_low (R : ZLP.ORing α) (f L : α) (lg : List (α × α))
    (conds : ∀ x, List.Mem x lg → R.le R.zero x.1 ∧ R.le x.2 R.zero)
    (min_sound : R.le L (R.add f (R.neg (ZLP.wsum R (lg.map (fun x => (x.1, R.neg x.2))))))) :
    R.le L f := by
  apply ZLP.lower_bound_sound R f L _ _ min_sound
  intro yh hm
  have ⟨x, hx, hxe⟩ := mem_map_inv _ hm
  rw [← hxe]
  exact ⟨(conds x hx).1, neg_nonneg R (conds x hx).2⟩

/-- A LEAF SKIPPED. Multipliers `λ_j ≥ 0` whose `Σ λ_j·(−g_j)` has a box-maximum `M` below zero: the conditions
`g_j ≤ 0` do not all hold at the point — no point of the piece lies in this case. -/
theorem dual_leaf_impossible (R : ZLP.ORing α) (M : α) (lg : List (α × α))
    (lam_nonneg : ∀ x, List.Mem x lg → R.le R.zero x.1)
    (max_sound : R.le (ZLP.wsum R (lg.map (fun x => (x.1, R.neg x.2)))) M) (neg : ¬ R.le R.zero M) :
    ¬ (∀ x, List.Mem x lg → R.le x.2 R.zero) := by
  intro hall
  apply ZLP.infeasible_sound R M _ max_sound neg
  intro yh hm
  have ⟨x, hx, hxe⟩ := mem_map_inv _ hm
  rw [← hxe]
  exact ⟨lam_nonneg x hx, neg_nonneg R (hall x hx)⟩

/-! ## An outer `min` / `max`, and the meet with the plain reading -/

/-- A lattice on a preorder, given by its laws: `mn` a greatest lower bound, `mx` a least upper bound. -/
structure Lat (γ : Type) extends ZCertify.Ord γ where
  mn : γ → γ → γ
  mx : γ → γ → γ
  mn_le_l : ∀ a b, le (mn a b) a
  mn_le_r : ∀ a b, le (mn a b) b
  le_mn   : ∀ {x a b}, le x a → le x b → le x (mn a b)
  le_mx_l : ∀ a b, le a (mx a b)
  le_mx_r : ∀ a b, le b (mx a b)
  mx_le   : ∀ {x a b}, le a x → le b x → le (mx a b) x

/-- An outer `min`: its arguments in `[la, ha]` and `[lb, hb]`, it lies in `[mn la lb, mn ha hb]`. -/
theorem min_enclosure (L : Lat β) {a b la ha lb hb : β}
    (h1 : L.le la a) (h2 : L.le a ha) (h3 : L.le lb b) (h4 : L.le b hb) :
    L.le (L.mn la lb) (L.mn a b) ∧ L.le (L.mn a b) (L.mn ha hb) :=
  ⟨L.le_mn (L.trans (L.mn_le_l la lb) h1) (L.trans (L.mn_le_r la lb) h3),
   L.le_mn (L.trans (L.mn_le_l a b) h2) (L.trans (L.mn_le_r a b) h4)⟩

/-- An outer `max`: it lies in `[mx la lb, mx ha hb]`. -/
theorem max_enclosure (L : Lat β) {a b la ha lb hb : β}
    (h1 : L.le la a) (h2 : L.le a ha) (h3 : L.le lb b) (h4 : L.le b hb) :
    L.le (L.mx la lb) (L.mx a b) ∧ L.le (L.mx a b) (L.mx ha hb) :=
  ⟨L.mx_le (L.trans h1 (L.le_mx_l a b)) (L.trans h3 (L.le_mx_r a b)),
   L.mx_le (L.trans h2 (L.le_mx_l ha hb)) (L.trans h4 (L.le_mx_r ha hb))⟩

/-- Two sound enclosures of one value meet in a sound one: `[mx l1 l2, mn h1 h2]`. -/
theorem meet_enclosure (L : Lat β) {x l1 h1 l2 h2 : β}
    (a1 : L.le l1 x) (b1 : L.le x h1) (a2 : L.le l2 x) (b2 : L.le x h2) :
    L.le (L.mx l1 l2) x ∧ L.le x (L.mn h1 h2) :=
  ⟨L.mx_le a1 a2, L.le_mn b1 b2⟩

end ZCases

#print axioms ZCases.mem_append_left
#print axioms ZCases.mem_append_right
#print axioms ZCases.mem_map_inv
#print axioms ZCases.impossible_leaf
#print axioms ZCases.cases_sound_acc
#print axioms ZCases.cases_sound
#print axioms ZCases.neg_nonneg
#print axioms ZCases.dual_leaf_low
#print axioms ZCases.dual_leaf_impossible
#print axioms ZCases.min_enclosure
#print axioms ZCases.max_enclosure
#print axioms ZCases.meet_enclosure
