import ZBound
/-!
# ZBoundIf — a requirement on a TABLE, branch by branch

The curator's word (2026-11-09, «Все да» on "ifpos in the XE core"): ztl-stand's tables whose condition is not one
variable's affine sign — tasks/t22 (Euler / Johnson, `x = Sy·λ²/(2π²E) > 1`, the product of two intervals), r04,
s07's choice bricks — stood "not translated (yet): ifpos".

WHY NOT A CONSTRUCTOR OF `XE`, said: `evR` reads an expression as a FUNCTION on VR's continuum, and
`if c > 0 then a else b` is not one there — choosing the branch decides the sign of a real number, which a
constructive real does not decide (no `Classical.choice`: zero axioms is the floor). A table is read here as what its
requirement MEANS: for every point of the box, WHICHEVER branch applies, the bound holds. One theorem per branch:

    ∀ x ∈ B, (the branch's conditions at x) → bound (evR x e_branch)

The conditions are a list of `(s, g)`: `true` — `g > 0`, `false` — `g ≤ 0` (the stand's `ifpos(g, a, b)`: a where
g > 0, else b). The kernel's tree `GT` has three kinds of node: `bd` — the bound proved on this piece (`chkV`);
`ex` — the piece EXCLUDED, one condition contradicted on all of it (`g ≤ d ≤ 0` against `g > 0`, or `g ≥ d > 0`
against `g ≤ 0`, each by `chkV`); `cut`. Zero axioms.

Said, not hidden: that the branches cover the table (every point has `g > 0` or `g ≤ 0`) is the reading of the
table, not a theorem here — constructively a point need not be placed; the theorems hold for every point that is.
-/

namespace ZBoundIf

open VR VR.Numbers ZNumBin ZField ZPoly ZIv ZDivIv ZXE ZRealCF ZRootDiv ZBound ZAff ZRootExp

/-- A branch's condition at the point `x`: `(true, g)` — `g > 0`; `(false, g)` — `g ≤ 0`. -/
def GuardP (x : Nat → RExpr) (s : Bool) (g : XE) : Prop :=
  cond s (rCF.pos (evR x g)) (rCF.le (evR x g) rCF.zero)

/-- Every condition of the branch holds at `x`. -/
def AllG (x : Nat → RExpr) : List (Bool × XE) → Prop
  | [] => True
  | p :: gs => GuardP x p.1 p.2 ∧ AllG x gs

/-- The `k`-th condition. -/
def nthG : List (Bool × XE) → Nat → Option (Bool × XE)
  | [], _ => none
  | p :: _, 0 => some p
  | _ :: gs, n + 1 => nthG gs n

theorem allG_nth {x : Nat → RExpr} : ∀ {gs : List (Bool × XE)} {k : Nat} {p : Bool × XE},
    AllG x gs → nthG gs k = some p → GuardP x p.1 p.2
  | [], _, _, _, h => by cases h
  | _ :: _, 0, _, hA, h => by cases h; exact hA.1
  | _ :: _, _ + 1, _, hA, h => allG_nth hA.2 h

/-- The kernel's tree over a branch: the bound proved, the piece excluded by condition `k` (separation `d`), a cut. -/
inductive GT where
  | bd : VT → GT
  | ex : Nat → D → VT → GT
  | cut : Nat → D → GT → GT → GT

/-- Condition `g` contradicted on all of `B`: `g ≤ d ≤ 0` against `g > 0`; `g ≥ d > 0` against `g ≤ 0`. -/
def exOK (g : Bool × XE) (d : D) (vs : List Nat) (T : VT) (B : Box) : Bool :=
  cond g.1 (dle d zeroD && posOK B g.2 && chkV false g.2 d vs T B)
           (posX d && posOK B g.2 && chkV true g.2 d vs T B)

/-- **THE KERNEL'S CHECK** of a branch: the target `e`'s bound `c` on side `lo`, under the conditions `gs`. -/
def chkG (lo : Bool) (e : XE) (c : D) (vs : List Nat) (gs : List (Bool × XE)) : GT → Box → Bool
  | .bd T => fun B => posOK B e && chkV lo e c vs T B
  | .ex k d T => fun B => match nthG gs k with
    | none => false
    | some g => exOK g d vs T B
  | .cut i a l r => fun B => match B i with
    | none => false
    | some I => dle I.1 a && dle a I.2 && chkG lo e c vs gs l (boxSet B i (I.1, a)) &&
        chkG lo e c vs gs r (boxSet B i (a, I.2))

section Sep
variable {α : Type} {S : CF α}
theorem excl_hi {v : α} {d : D} (hp : S.pos v) (h : S.le v (dv S.toOH d)) (hd : dle d zeroD = true) : False := by
  have h1 : S.le (dv S.toOH d) S.zero := S.le_respects (S.refl _) (dv_zeroD S) (dle_sound S.toOH hd)
  exact S.pos_not_le hp (by cr_linarith S.toOCR [h, h1])
theorem excl_lo {v : α} {d : D} (hv : S.le v S.zero) (h : S.le (dv S.toOH d) v) (hd : posX d = true) : False :=
  S.pos_not_le (pos_of_posX S hd) (by cr_linarith S.toOCR [hv, h])
end Sep

theorem exOK_false {g : Bool × XE} {d : D} {vs : List Nat} {T : VT} {B : Box} {x : Nat → RExpr}
    (h : exOK g d vs T B = true) (hx : InBox rCF B x) (hg : GuardP x g.1 g.2) : False := by
  cases g with
  | mk s g =>
  cases s with
  | true =>
    have h' : (dle d zeroD && posOK B g && chkV false g d vs T B) = true := h
    obtain ⟨h12, h3⟩ := and_true_split h'
    obtain ⟨h1, h2⟩ := and_true_split h12
    have hb : rCF.le (evR x g) (dv rOH d) := bound_vrM h3 h2 x hx
    have hp : rCF.pos (evR x g) := hg
    exact excl_hi hp hb h1
  | false =>
    have h' : (posX d && posOK B g && chkV true g d vs T B) = true := h
    obtain ⟨h12, h3⟩ := and_true_split h'
    obtain ⟨h1, h2⟩ := and_true_split h12
    have hb : rCF.le (dv rOH d) (evR x g) := bound_vrM h3 h2 x hx
    have hv : rCF.le (evR x g) rCF.zero := hg
    exact excl_lo hv hb h1

/-- **THE BRANCH TREE IS SOUND** on VR's continuum. -/
theorem chkG_sound {lo : Bool} {e : XE} {c : D} {vs : List Nat} {gs : List (Bool × XE)} :
    ∀ (T : GT) (B : Box) (x : Nat → RExpr), chkG lo e c vs gs T B = true → InBox rCF B x → AllG x gs →
      Holds rCF lo c (evR x e)
  | .bd T, B, x, h, hB, _ => by
      have h' : (posOK B e && chkV lo e c vs T B) = true := h
      obtain ⟨hp, hc⟩ := and_true_split h'
      exact bound_vrM hc hp x hB
  | .ex k d T, B, x, h, hB, hA => by
      unfold chkG at h
      cases hn : nthG gs k with
      | none => rw [hn] at h; cases h
      | some g =>
        rw [hn] at h
        exact (exOK_false h hB (allG_nth hA hn)).elim
  | .cut i a l r, B, x, h, hB, hA => by
      unfold chkG at h
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
        exact hn (chkG_sound r _ x hr (inbox_set hB hge' mi.2) hA)
      · intro hle
        have hle' : rCF.le (x i) (dv rOH a) := le_of_sub_nonpos hle
        exact hn (chkG_sound l _ x hl (inbox_set hB mi.1 hle') hA)

/-- **The bound on a branch**: for every point of the box where the branch's conditions hold. -/
theorem bound_if {lo : Bool} {e : XE} {c : D} {vs : List Nat} {gs : List (Bool × XE)} {T : GT} {B : Box}
    (h : chkG lo e c vs gs T B = true) : ∀ x : Nat → RExpr, InBox rCF B x → AllG x gs → Holds rCF lo c (evR x e) :=
  fun x hx hA => chkG_sound T B x h hx hA

/-! ## Many tables in one expression: each table's VALUE a variable (2026-11-09, ztl-stand tasks/t23)

A sum of 25 power curves has 2²⁵ branches — not to be listed. Each table `t` gets a variable `y t.i` of its own and
a proved range `[t.L, t.U]`: every branch of `t`, where its conditions hold, lies in it (`chkBr`). The expression
with the tables replaced by their variables is bounded over the box extended by those ranges (`extB`, `chkV`). The
theorem: for every point of the box and every value of each table's variable that IS one of that table's branch
values there (`TV`), the bound holds. Said, not hidden: the tables' dependence on one another (the same wind speed
in every bin) is not used — the ranges are independent; a requirement with that much margin is provable. -/

/-- A table: its value sits at variable `i`; `[L, U]` its range, proved on every branch; the branches; their trees
(lower, upper). -/
structure Tab where
  i : Nat
  L : D
  U : D
  bs : List (List (Bool × XE) × XE)
  ts : List (GT × GT)

/-- `v` is one of the table's values at `y`: the value of a branch whose conditions hold there. -/
def TV (y : Nat → RExpr) (bs : List (List (Bool × XE) × XE)) (v : RExpr) : Prop :=
  ∃ b, List.Mem b bs ∧ AllG y b.1 ∧ rCF.r v (evR y b.2)

/-- Every branch inside `[L, U]` where its conditions hold (`chkG` both sides). -/
def chkBr (L U : D) (vs : List Nat) (B : Box) : List (List (Bool × XE) × XE) → List (GT × GT) → Bool
  | [], [] => true
  | b :: bs, t :: ts => chkG true b.2 L vs b.1 t.1 B && chkG false b.2 U vs b.1 t.2 B && chkBr L U vs B bs ts
  | [], _ :: _ => false
  | _ :: _, [] => false

theorem chkBr_sound {L U : D} {vs : List Nat} {B : Box} {y : Nat → RExpr} :
    ∀ {bs : List (List (Bool × XE) × XE)} {ts : List (GT × GT)}, chkBr L U vs B bs ts = true → InBox rCF B y →
      ∀ b, List.Mem b bs → AllG y b.1 → Holds rCF true L (evR y b.2) ∧ Holds rCF false U (evR y b.2)
  | [], [], _, _, _, hm, _ => nomatch hm
  | b0 :: bs, t :: ts, h, hy, b, hm, hg => by
      have h' : (chkG true b0.2 L vs b0.1 t.1 B && chkG false b0.2 U vs b0.1 t.2 B && chkBr L U vs B bs ts) = true := h
      obtain ⟨h12, h3⟩ := and_true_split h'
      obtain ⟨h1, h2⟩ := and_true_split h12
      cases hm with
      | head => exact ⟨chkG_sound t.1 B y h1 hy hg, chkG_sound t.2 B y h2 hy hg⟩
      | tail _ hm' => exact chkBr_sound h3 hy b hm' hg
  | [], _ :: _, h, _, _, _, _ => by cases h
  | _ :: _, [], h, _, _, _, _ => by cases h

/-- **A table's value lies in its range.** -/
theorem tv_bounds {L U : D} {vs : List Nat} {B : Box} {bs : List (List (Bool × XE) × XE)} {ts : List (GT × GT)}
    {y : Nat → RExpr} {v : RExpr} (h : chkBr L U vs B bs ts = true) (hy : InBox rCF B y) (hv : TV y bs v) :
    rCF.le (dv rOH L) v ∧ rCF.le v (dv rOH U) := by
  obtain ⟨b, hm, hg, he⟩ := hv
  obtain ⟨h1, h2⟩ := chkBr_sound h hy b hm hg
  have h1' : rCF.le (dv rOH L) (evR y b.2) := h1
  have h2' : rCF.le (evR y b.2) (dv rOH U) := h2
  exact ⟨rCF.le_respects (rCF.refl _) (rCF.symm he) h1', rCF.le_respects (rCF.symm he) (rCF.refl _) h2'⟩

def lookTab (i : Nat) : List Tab → Option Tab
  | [] => none
  | t :: ts => cond (Nat.beq t.i i) (some t) (lookTab i ts)

theorem lookTab_mem {i : Nat} {t : Tab} : ∀ {ts : List Tab}, lookTab i ts = some t → List.Mem t ts ∧ t.i = i
  | [], h => by cases h
  | t0 :: ts, h => by
      cases hb : Nat.beq t0.i i with
      | true =>
        have h' : cond (Nat.beq t0.i i) (some t0) (lookTab i ts) = some t := h
        rw [hb] at h'
        cases h'
        exact ⟨List.Mem.head ts, Nat.eq_of_beq_eq_true hb⟩
      | false =>
        have h' : cond (Nat.beq t0.i i) (some t0) (lookTab i ts) = some t := h
        rw [hb] at h'
        obtain ⟨hm, he⟩ := lookTab_mem h'
        exact ⟨List.Mem.tail t0 hm, he⟩

/-- The box extended by the tables' ranges, each at its variable. -/
def extB (Bx : Box) (ts : List Tab) : Box := fun i => match lookTab i ts with
  | some t => some (t.L, t.U)
  | none => Bx i

theorem inbox_ext {Bx : Box} {ts : List Tab} {y : Nat → RExpr} (hy : InBox rCF Bx y)
    (hb : ∀ t, List.Mem t ts → rCF.le (dv rOH t.L) (y t.i) ∧ rCF.le (y t.i) (dv rOH t.U)) :
    InBox rCF (extB Bx ts) y := by
  intro i I hI
  cases hl : lookTab i ts with
  | none =>
    have hI' : Bx i = some I := by
      have : (match lookTab i ts with
        | some t => some (t.L, t.U)
        | none => Bx i) = some I := hI
      rw [hl] at this; exact this
    exact hy i I hI'
  | some t =>
    have hI' : some (t.L, t.U) = some I := by
      have : (match lookTab i ts with
        | some t => some (t.L, t.U)
        | none => Bx i) = some I := hI
      rw [hl] at this; exact this
    cases hI'
    obtain ⟨hm, he⟩ := lookTab_mem hl
    have hr := hb t hm
    rw [he] at hr
    exact hr

/-- Every table's ranges checked. -/
def chkTabs (vs : List Nat) (B : Box) : List Tab → Bool
  | [] => true
  | t :: ts => chkBr t.L t.U vs B t.bs t.ts && chkTabs vs B ts

theorem chkTabs_mem {vs : List Nat} {B : Box} {t : Tab} : ∀ {ts : List Tab}, chkTabs vs B ts = true →
    List.Mem t ts → chkBr t.L t.U vs B t.bs t.ts = true
  | [], _, hm => nomatch hm
  | t0 :: ts, h, hm => by
      have h' : (chkBr t0.L t0.U vs B t0.bs t0.ts && chkTabs vs B ts) = true := h
      obtain ⟨h1, h2⟩ := and_true_split h'
      cases hm with
      | head => exact h1
      | tail _ hm' => exact chkTabs_mem h2 hm'

/-- Each table's variable holds one of that table's values. -/
def AllTab (y : Nat → RExpr) (ts : List Tab) : Prop := ∀ t, List.Mem t ts → TV y t.bs (y t.i)

/-- **The bound over many tables**: for every point of the box and every value of the tables' variables that is
one of their branch values there. -/
theorem bound_tabs {lo : Bool} {e : XE} {c : D} {vs vsx : List Nat} {T : VT} {Bx : Box} {ts : List Tab}
    (h : chkV lo e c vs T (extB Bx ts) = true) (hp : posOK (extB Bx ts) e = true) (ht : chkTabs vsx Bx ts = true) :
    ∀ y : Nat → RExpr, InBox rCF Bx y → AllTab y ts → Holds rCF lo c (evR y e) :=
  fun y hy hA => bound_vrM h hp y (inbox_ext hy (fun t hm => tv_bounds (chkTabs_mem ht hm) hy (hA t hm)))

/-! ## The search (a PROPOSAL; the kernel checks only `chkG`) -/

/-- Condition `g` contradicted on `B` by one monotone or interval leaf, with its separation. -/
def exOne (vs : List Nat) (B : Box) (g : Bool × XE) : Option (D × VT) :=
  cond (posOK B g.2)
    (cond g.1
      (match findV false g.2 zeroD vs 0 B with
       | some T => some (zeroD, T)
       | none => none)
      (match ivX B g.2 with
       | none => none
       | some I => cond (posX I.1)
           (match findV true g.2 I.1 vs 0 B with
            | some T => some (I.1, T)
            | none => none) none))
    none

def exTry (vs : List Nat) (B : Box) : Nat → List (Bool × XE) → Option GT
  | _, [] => none
  | k, g :: rest => match exOne vs B g with
    | some (d, T) => some (.ex k d T)
    | none => exTry vs B (k + 1) rest

/-- The conditions still open on `B`: their interval reading not yet on the branch's side (`0 ≤ g` for `g > 0`,
`g ≤ 0` for `g ≤ 0`). A condition already on its side is not cut for: the points left are the branch's own.
(2026-11-09: reading "straddles 0" instead, the right half `z ∈ [1, 1.5]` of `z − 1 > 0` stayed open — `z` was cut
to the depth, and the other condition's variable never.) -/
def openG (B : Box) : List (Bool × XE) → List XE
  | [] => []
  | g :: rest => match ivX B g.2 with
    | none => g.2 :: openG B rest
    | some I => cond (cond g.1 (dle zeroD I.1) (dle I.2 zeroD)) (openG B rest) (g.2 :: openG B rest)

/-- The variable moving `g` most on `B`: `|slope|·width`, the largest. -/
def influence (B : Box) (g : XE) : List Nat → Option (Nat × Iv × D)
  | [] => none
  | i :: vs => match B i with
    | none => influence B g vs
    | some I => match slX B (unitV i) g with
      | none => influence B g vs
      | some K =>
        let w := dadd I.2 (dneg I.1)
        let s := cond (dle (dneg K.1) K.2) (dmul K.2 w) (dmul (dneg K.1) w)
        match influence B g vs with
        | none => some (i, I, s)
        | some (j, J, t) => cond (dle t s) (some (i, I, s)) (some (j, J, t))

def candG (B : Box) (vs : List Nat) : List XE → List (Nat × Iv)
  | [] => []
  | g :: rest => match influence B g vs with
    | some (i, I, _) => (i, I) :: candG B vs rest
    | none => candG B vs rest

def pickN : List (Nat × Iv) → Nat → Option (Nat × Iv)
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: cs, n + 1 => pickN cs n

/-- The cut: in turn (by the depth left), the most influential variable of each open condition and `pickCut` of
the target — at a condition's own boundary the branch applies, and only ANOTHER condition's cut separates it
(2026-11-09: `z ≤ 1 ∧ F > 3` on `z ∈ [1, 1+ε]`). -/
def pickG (B : Box) (e : XE) (gs : List (Bool × XE)) (vs : List Nat) (n : Nat) : Option (Nat × Iv) :=
  let cs := candG B vs (openG B gs) ++ (match pickCut B e vs with
    | some c => [c]
    | none => [])
  pickN cs (n % cs.length)

def findG (lo : Bool) (e : XE) (c : D) (vs : List Nat) (gs : List (Bool × XE)) : Nat → Box → Option GT
  | 0 => fun B => match exTry vs B 0 gs with
    | some t => some t
    | none => cond (posOK B e) (match findV lo e c vs 0 B with
        | some T => some (.bd T)
        | none => none) none
  | n + 1 => fun B => match exTry vs B 0 gs with
    | some t => some t
    | none => match cond (posOK B e) (findV lo e c vs 0 B) none with
      | some T => some (.bd T)
      | none => match pickG B e gs vs n with
        | none => none
        | some (i, I) => match findG lo e c vs gs n (boxSet B i (I.1, ZAff.mid I)) with
          | none => none
          | some l => match findG lo e c vs gs n (boxSet B i (ZAff.mid I, I.2)) with
            | none => none
            | some r => some (.cut i (ZAff.mid I) l r)

/-- The tree as Lean text (string formatting, outside the kernel — `[propext]`, like `ZBound.VT.txt`; not printed). -/
def GT.txt : GT → String
  | .bd T => s!"(.bd {T.txt})"
  | .ex k d T => s!"(.ex {k} {dTxt d} {T.txt})"
  | .cut i a l r => s!"(.cut {i} {dTxt a} {l.txt} {r.txt})"

end ZBoundIf

#print axioms ZBoundIf.GuardP
#print axioms ZBoundIf.AllG
#print axioms ZBoundIf.nthG
#print axioms ZBoundIf.allG_nth
#print axioms ZBoundIf.exOK
#print axioms ZBoundIf.chkG
#print axioms ZBoundIf.excl_hi
#print axioms ZBoundIf.excl_lo
#print axioms ZBoundIf.exOK_false
#print axioms ZBoundIf.chkG_sound
#print axioms ZBoundIf.bound_if
#print axioms ZBoundIf.TV
#print axioms ZBoundIf.chkBr
#print axioms ZBoundIf.chkBr_sound
#print axioms ZBoundIf.tv_bounds
#print axioms ZBoundIf.lookTab
#print axioms ZBoundIf.lookTab_mem
#print axioms ZBoundIf.extB
#print axioms ZBoundIf.inbox_ext
#print axioms ZBoundIf.chkTabs
#print axioms ZBoundIf.chkTabs_mem
#print axioms ZBoundIf.AllTab
#print axioms ZBoundIf.bound_tabs
#print axioms ZBoundIf.exOne
#print axioms ZBoundIf.exTry
#print axioms ZBoundIf.openG
#print axioms ZBoundIf.influence
#print axioms ZBoundIf.candG
#print axioms ZBoundIf.pickN
#print axioms ZBoundIf.pickG
#print axioms ZBoundIf.findG
