import ZTL

/-!
# The reachable values of a claim, computed down the tree — sound for every formula. Zero axioms.

`zreach.py` (2026-11-09) answers "which values can this claim still take over the fillings (completions) or the
refinements of its dirty atoms" in one pass: for every node the SET of values, a connective's set the image of its
children's sets under its table, and an atom shared by two children ENUMERATED at its lowest common node. The
curator's observation behind it: going down, every value is two-valued — Z lives only on atoms (Pillar 1, `ZTL.lean`),
so above the first layer of connectives the pass is classical.

WHAT THIS FILE PROVES. The pass, on a formula annotated with enumeration points (`EFm.enum n φ`: read φ once per
value of atom n — exactly where zreach.py enumerates), never MISSES a value: every refinement (and, in completion
mode, every completion) gives a value the pass reports. For EVERY formula and EVERY placement of the enumeration
points — independence of the children is not needed for this direction.

WHY THAT IS THE DIRECTION THAT MATTERS. zreach.py's answers are of two kinds:
  * "value r is reachable" — it carries a WITNESS filling, re-evaluated by the forward judge: checked, no theorem
    needed;
  * "value r is NOT reachable" (a NO for SAT; a HEREDITARY grade: every refinement gives the verdict) — that is
    `reach_sound` below, contraposed (`not_reached`).
The other direction (every value reported is attained) holds when the children share no dirty atom; it is not proved
here, and it is not needed: a reported value is either witnessed or zreach.py says it cannot build the witness (an
AssertionError, never an answer).
-/

namespace V
namespace Reach

/-- "some value satisfies p", written out over the three values (no List: its lemmas carry `propext`). -/
def anyV (p : V → Bool) : Bool := p T || p F || p Z

theorem or_l (a b : Bool) (h : a = true) : (a || b) = true := by rw [h]; rfl
theorem or_r (a b : Bool) (h : b = true) : (a || b) = true := by cases a <;> (rw [h]; rfl)

theorem anyV_of (p : V → Bool) (x : V) (hx : p x = true) : anyV p = true := by
  cases x with
  | T => exact or_l _ _ (or_l _ _ hx)
  | F => exact or_l _ _ (or_r _ _ hx)
  | Z => exact or_r _ _ hx

theorem beq_refl (x : V) : (x == x) = true := by cases x <;> rfl

/-- A formula with ENUMERATION POINTS: `.enum n φ` reads φ once per value of atom n. The judge ignores them. -/
inductive EFm where
  | atom : Nat → EFm
  | top  : EFm
  | bot  : EFm
  | neg  : EFm → EFm
  | conj : EFm → EFm → EFm
  | disj : EFm → EFm → EFm
  | imp  : EFm → EFm → EFm
  | xor  : EFm → EFm → EFm
  | xnor : EFm → EFm → EFm
  | enum : Nat → EFm → EFm

/-- The formula the judge reads: the enumeration points erased. -/
def erase : EFm → Fm
  | .atom n   => .atom n
  | .top      => .top
  | .bot      => .bot
  | .neg a    => .neg (erase a)
  | .conj a b => .conj (erase a) (erase b)
  | .disj a b => .disj (erase a) (erase b)
  | .imp a b  => .imp (erase a) (erase b)
  | .xor a b  => .xor (erase a) (erase b)
  | .xnor a b => .xnor (erase a) (erase b)
  | .enum _ a => erase a

/-- Every formula is an annotated one with no enumeration point. -/
def lift : Fm → EFm
  | .atom n   => .atom n
  | .top      => .top
  | .bot      => .bot
  | .neg a    => .neg (lift a)
  | .conj a b => .conj (lift a) (lift b)
  | .disj a b => .disj (lift a) (lift b)
  | .imp a b  => .imp (lift a) (lift b)
  | .xor a b  => .xor (lift a) (lift b)
  | .xnor a b => .xnor (lift a) (lift b)

theorem erase_lift (φ : Fm) : erase (lift φ) = φ := by
  induction φ with
  | atom n => rfl
  | top => rfl
  | bot => rfl
  | neg a ih => show Fm.neg (erase (lift a)) = _; rw [ih]
  | conj a b iha ihb => show Fm.conj (erase (lift a)) (erase (lift b)) = _; rw [iha, ihb]
  | disj a b iha ihb => show Fm.disj (erase (lift a)) (erase (lift b)) = _; rw [iha, ihb]
  | imp a b iha ihb => show Fm.imp (erase (lift a)) (erase (lift b)) = _; rw [iha, ihb]
  | xor a b iha ihb => show Fm.xor (erase (lift a)) (erase (lift b)) = _; rw [iha, ihb]
  | xnor a b iha ihb => show Fm.xnor (erase (lift a)) (erase (lift b)) = _; rw [iha, ihb]

def upd (v : Nat → V) (n : Nat) (x : V) : Nat → V := fun m => if m = n then x else v m

/-- The values a dirty atom may take: completion mode (`cmp = true`) T and F; refinement mode Z as well. -/
def inLeaf : Bool → V → Bool
  | _, T => true
  | _, F => true
  | true, Z => false
  | false, Z => true

/-- "some value a dirty atom may take satisfies p". -/
def anyL (cmp : Bool) (p : V → Bool) : Bool := if cmp then p T || p F else p T || p F || p Z

def img1 (f : V → V) (ra : V → Bool) (r : V) : Bool := anyV (fun x => ra x && f x == r)

def img2 (f : V → V → V) (ra rb : V → Bool) (r : V) : Bool :=
  anyV (fun x => anyV (fun y => ra x && rb y && f x y == r))

/-- THE PASS: `reach cmp v φ r` — does the pass report value r for φ under the marking v. -/
def reach (cmp : Bool) : (Nat → V) → EFm → V → Bool
  | v, .atom n,   r => if v n = Z then inLeaf cmp r else v n == r
  | _, .top,      r => r == T
  | _, .bot,      r => r == F
  | v, .neg a,    r => img1 znot (reach cmp v a) r
  | v, .conj a b, r => img2 zand (reach cmp v a) (reach cmp v b) r
  | v, .disj a b, r => img2 zor (reach cmp v a) (reach cmp v b) r
  | v, .imp a b,  r => img2 zimp (reach cmp v a) (reach cmp v b) r
  | v, .xor a b,  r => img2 zxor (reach cmp v a) (reach cmp v b) r
  | v, .xnor a b, r => img2 zxnor (reach cmp v a) (reach cmp v b) r
  | v, .enum n a, r => anyL cmp (fun x => reach cmp (upd v n x) a r)

/-- A refinement: every clean atom keeps its value (the same relation as `NoGift.refines`). -/
def Ref (v w : Nat → V) : Prop := ∀ n, v n ≠ Z → w n = v n

/-- In completion mode the refinement fills every atom. -/
def Fills (cmp : Bool) (w : Nat → V) : Prop := cmp = true → ∀ n, w n ≠ Z

theorem leaf_mem (cmp : Bool) (w : Nat → V) (hf : Fills cmp w) (n : Nat) : inLeaf cmp (w n) = true := by
  cases cmp with
  | false => cases w n <;> rfl
  | true =>
    have hz := hf rfl n
    cases h : w n with
    | T => rfl
    | F => rfl
    | Z => exact absurd h hz

theorem anyL_of (cmp : Bool) (p : V → Bool) (x : V) (hl : inLeaf cmp x = true) (hx : p x = true) :
    anyL cmp p = true := by
  cases cmp with
  | true =>
    show (p T || p F) = true
    cases x with
    | T => exact or_l _ _ hx
    | F => exact or_r _ _ hx
    | Z => exact absurd hl (by decide)
  | false =>
    show (p T || p F || p Z) = true
    cases x with
    | T => exact or_l _ _ (or_l _ _ hx)
    | F => exact or_l _ _ (or_r _ _ hx)
    | Z => exact or_r _ _ hx

theorem img1_of (f : V → V) (ra : V → Bool) (x : V) (hx : ra x = true) : img1 f ra (f x) = true :=
  anyV_of _ x (by rw [hx]; exact beq_refl (f x))

theorem img2_of (f : V → V → V) (ra rb : V → Bool) (x y : V) (hx : ra x = true) (hy : rb y = true) :
    img2 f ra rb (f x y) = true :=
  anyV_of _ x (anyV_of _ y (by rw [hx, hy]; exact beq_refl (f x y)))

/-- **The pass never misses a value.** For every annotated formula, every marking v and every refinement w of v
(in completion mode: every completion), the value the judge gives at w is reported by the pass. -/
theorem reach_sound (cmp : Bool) (φ : EFm) :
    ∀ (v w : Nat → V), Ref v w → Fills cmp w → reach cmp v φ (evalF w (erase φ)) = true := by
  induction φ with
  | atom n =>
    intro v w hr hf
    show (if v n = Z then inLeaf cmp (w n) else v n == w n) = true
    by_cases hz : v n = Z
    · rw [if_pos hz]
      exact leaf_mem cmp w hf n
    · rw [if_neg hz, hr n hz]
      exact beq_refl (v n)
  | top => intro v w _ _; rfl
  | bot => intro v w _ _; rfl
  | neg a ih =>
    intro v w hr hf
    exact img1_of znot _ _ (ih v w hr hf)
  | conj a b iha ihb =>
    intro v w hr hf
    exact img2_of zand _ _ _ _ (iha v w hr hf) (ihb v w hr hf)
  | disj a b iha ihb =>
    intro v w hr hf
    exact img2_of zor _ _ _ _ (iha v w hr hf) (ihb v w hr hf)
  | imp a b iha ihb =>
    intro v w hr hf
    exact img2_of zimp _ _ _ _ (iha v w hr hf) (ihb v w hr hf)
  | xor a b iha ihb =>
    intro v w hr hf
    exact img2_of zxor _ _ _ _ (iha v w hr hf) (ihb v w hr hf)
  | xnor a b iha ihb =>
    intro v w hr hf
    exact img2_of zxnor _ _ _ _ (iha v w hr hf) (ihb v w hr hf)
  | enum n a ih =>
    intro v w hr hf
    show anyL cmp (fun x => reach cmp (upd v n x) a (evalF w (erase a))) = true
    refine anyL_of cmp _ (w n) (leaf_mem cmp w hf n) (ih (upd v n (w n)) w ?_ hf)
    intro m hm
    by_cases hmn : m = n
    · subst hmn
      show w m = (if m = m then w m else v m)
      rw [if_pos rfl]
    · have hm' : v m ≠ Z := by
        intro h; apply hm; show (if m = n then w n else v m) = Z; rw [if_neg hmn]; exact h
      show w m = (if m = n then w n else v m)
      rw [if_neg hmn]
      exact hr m hm'

/-- **A value the pass does not report is attained by NO refinement** — zreach.py's NO for SAT. -/
theorem not_reached (cmp : Bool) (φ : EFm) (v : Nat → V) (r : V) (hno : reach cmp v φ r = false) :
    ∀ w, Ref v w → Fills cmp w → evalF w (erase φ) ≠ r := by
  intro w hr hf he
  have := reach_sound cmp φ v w hr hf
  rw [he, hno] at this
  exact Bool.false_ne_true this

/-- **The pass reports only u ⇒ every refinement gives u** — the HEREDITARY grade (refinement mode, `cmp = false`):
the verdict u survives every partial verification of the marks. -/
theorem only_value (cmp : Bool) (φ : EFm) (v : Nat → V) (u : V)
    (honly : ∀ r, reach cmp v φ r = true → r = u) :
    ∀ w, Ref v w → Fills cmp w → evalF w (erase φ) = u :=
  fun w hr hf => honly _ (reach_sound cmp φ v w hr hf)

#print axioms reach_sound
#print axioms not_reached
#print axioms only_value
#print axioms erase_lift

end Reach
end V
