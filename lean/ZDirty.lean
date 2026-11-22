import ZTL
import ZRead
import ZClone
import NoGift
/-! # ZDirty — the hereditary verdict against classical substitutions; the lifts of the negated connectives.
Zero axioms.

Pure branch (curator 2026-11-22: "only ZTL, burn everything else, totally"). Removed here: every table of the
lazy register and every theorem stated through one (`k1`/`k2`/`kev`, `*_is_up_kleene`, `rd_is_kleene`,
`strict_*_iff_kleene`, `kleene_cannot_*`, …). The dirty reading itself (`rd`, `covers_rd`, `never_stricter`)
moved to ZRead.lean, where EARNED / REFUTED / IF STABLE are defined by the readings. What stays:
  * `nand_lift` …      — the lifts of the negated connectives are the argument-side De Morgan forms
                          (the tables ¬(a∘b) are compositions, not lifts — the v2.1.4 correction);
  * `substitution_of_earned`, `default_of_earned` — the hereditary verdict `Earned` (T under every refinement)
    survives every classical substitution of the dirty atoms, uniform or atom by atom;
  * Bochvar's external connectives as the classical default "dirty := false", and the characterisation of the
    ZTL connective as the only decisive, sound and maximal table.
-/
namespace V

-- `ok`, `comb`, `rd`, `covers`, `covers_rd`, `refusal_witnessed`, `never_stricter`, `over_grant` moved to
-- ZRead.lean (pure branch, 2026-11-22).


/-- the assertion operator: T stays T, everything else is F -/
def up (x : V) : V := if x = T then T else F

theorem nand_lift : ∀ a b, znand a b = zor (znot a) (znot b) := by decide
theorem nor_lift  : ∀ a b, znor a b = zand (znot a) (znot b) := by decide
theorem nimp_lift : ∀ a b, znimp a b = zand a (znot b) := by decide
theorem nxor_lift : ∀ a b, lift2 (fun a b => !(a != b)) a b = zxnor a b := by decide

/-- The lift of the identity is the assertion operator, and it is definable as x ∧ x. -/
theorem lift_id_is_up : ∀ x, lift1 (fun a => a) x = up x := by decide
theorem and_self_is_up : ∀ x, zand x x = up x := by decide

/-- The hereditary grade: T now and under every refinement of the marks (the judge's EARNED of 2.1.5; since
2026-10-29 the judge's EARNED is the forced T of ZRead, which implies it). -/
def Earned (v : Nat → V) (φ : Fm) : Prop := ∀ w, refines v w → evalF w φ = T

/-- A uniform default: every dirty atom set to d. -/
def subst (v : Nat → V) (d : V) : Nat → V := fun n => if v n = Z then d else v n

theorem subst_refines (v : Nat → V) (d : V) : refines v (subst v d) := by
  intro n hn; show (if v n = Z then d else v n) = v n; exact if_neg hn

/-- (2) What the hereditary grade grants, every uniform default grants. -/
theorem default_of_earned (v : Nat → V) (φ : Fm) (d : V) (h : Earned v φ) : evalF (subst v d) φ = T :=
  h _ (subst_refines v d)

/-- (2') The same against ANY classical substitution of the dirty atoms, uniform or chosen per atom:
a substitution is a total refinement, so what the hereditary grade grants, it grants. -/
theorem substitution_of_earned (v w : Nat → V) (φ : Fm) (hr : refines v w) (h : Earned v φ) :
    evalF w φ = T := h w hr

def bj (x : V) : Bool := x == T
def bof (b : Bool) : V := if b then T else F

def bev (v : Nat → V) : Fm → V
  | .atom n    => v n
  | .top       => T
  | .bot       => F
  | .neg φ     => bof (!bj (bev v φ))
  | .conj φ ψ  => bof (bj (bev v φ) && bj (bev v ψ))
  | .disj φ ψ  => bof (bj (bev v φ) || bj (bev v ψ))
  | .imp φ ψ   => bof (!bj (bev v φ) || bj (bev v ψ))
  | .xor φ ψ   => bof (bj (bev v φ) != bj (bev v ψ))
  | .xnor φ ψ  => bof (bj (bev v φ) == bj (bev v ψ))

theorem bj_bof : ∀ b : Bool, bj (bof b) = b := by decide
theorem bj_T : ∀ x : V, bj x = true → x = T := by decide
theorem bNot : ∀ y : V, y ≠ Z → bj (znot y) = !bj y := by decide
theorem bAnd : ∀ x y : V, x ≠ Z → y ≠ Z → bj (zand x y) = (bj x && bj y) := by decide
theorem bOr : ∀ x y : V, x ≠ Z → y ≠ Z → bj (zor x y) = (bj x || bj y) := by decide
theorem bImp : ∀ x y : V, x ≠ Z → y ≠ Z → bj (zimp x y) = (!bj x || bj y) := by decide
theorem bXor : ∀ x y : V, x ≠ Z → y ≠ Z → bj (zxor x y) = (bj x != bj y) := by decide
theorem bXnor : ∀ x y : V, x ≠ Z → y ≠ Z → bj (zxnor x y) = (bj x == bj y) := by decide
theorem bAtom : ∀ x : V, bj x = bj (if x = Z then F else x) := by decide

/-- After the default "dirty := false" no formula takes Z. -/
theorem subst_F_ne_Z (v : Nat → V) (φ : Fm) : evalF (subst v F) φ ≠ Z := by
  cases evalF_classical (subst v F) φ with
  | inl h =>
      obtain ⟨n, rfl⟩ := h
      show (if v n = Z then F else v n) ≠ Z
      cases h : v n <;> decide
  | inr h => cases h with
    | inl h => rw [h]; decide
    | inr h => rw [h]; decide

/-- **Bochvar's external logic is classical logic under the default "dirty := false":** at every
valuation, a formula is true in Bochvar's external connectives iff it is true after every dirty atom
is set to false. -/
theorem bochvar_is_default_false (v : Nat → V) : ∀ φ : Fm, bj (bev v φ) = bj (evalF (subst v F) φ)
  | .atom n => bAtom (v n)
  | .top => rfl
  | .bot => rfl
  | .neg φ => by
      show bj (bof (!bj (bev v φ))) = bj (znot (evalF (subst v F) φ))
      rw [bj_bof, bNot _ (subst_F_ne_Z v φ), bochvar_is_default_false v φ]
  | .conj φ ψ => by
      show bj (bof (bj (bev v φ) && bj (bev v ψ))) = bj (zand (evalF (subst v F) φ) (evalF (subst v F) ψ))
      rw [bj_bof, bAnd _ _ (subst_F_ne_Z v φ) (subst_F_ne_Z v ψ),
        bochvar_is_default_false v φ, bochvar_is_default_false v ψ]
  | .disj φ ψ => by
      show bj (bof (bj (bev v φ) || bj (bev v ψ))) = bj (zor (evalF (subst v F) φ) (evalF (subst v F) ψ))
      rw [bj_bof, bOr _ _ (subst_F_ne_Z v φ) (subst_F_ne_Z v ψ),
        bochvar_is_default_false v φ, bochvar_is_default_false v ψ]
  | .imp φ ψ => by
      show bj (bof (!bj (bev v φ) || bj (bev v ψ))) = bj (zimp (evalF (subst v F) φ) (evalF (subst v F) ψ))
      rw [bj_bof, bImp _ _ (subst_F_ne_Z v φ) (subst_F_ne_Z v ψ),
        bochvar_is_default_false v φ, bochvar_is_default_false v ψ]
  | .xor φ ψ => by
      show bj (bof (bj (bev v φ) != bj (bev v ψ))) = bj (zxor (evalF (subst v F) φ) (evalF (subst v F) ψ))
      rw [bj_bof, bXor _ _ (subst_F_ne_Z v φ) (subst_F_ne_Z v ψ),
        bochvar_is_default_false v φ, bochvar_is_default_false v ψ]
  | .xnor φ ψ => by
      show bj (bof (bj (bev v φ) == bj (bev v ψ))) = bj (zxnor (evalF (subst v F) φ) (evalF (subst v F) ψ))
      rw [bj_bof, bXnor _ _ (subst_F_ne_Z v φ) (subst_F_ne_Z v ψ),
        bochvar_is_default_false v φ, bochvar_is_default_false v ψ]

theorem refines_refl (v : Nat → V) : refines v v := fun _ _ => rfl

/-- **The hereditary grade dominates Bochvar.** What it grants, Bochvar grants; and on a dirty p,
Bochvar grants ¬p, which the hereditary grade (and the judge) refuses and the dirty reading does not earn. -/
theorem earned_dominates_bochvar (v : Nat → V) (φ : Fm) (h : Earned v φ) : bev v φ = T :=
  bj_T _ (by rw [bochvar_is_default_false]; have e := default_of_earned v φ F h; rw [e]; rfl)
def total (w : Nat → V) : Prop := ∀ n, w n ≠ Z
def Enum (v : Nat → V) (φ : Fm) : Prop := ∀ w, refines v w → total w → evalF w φ = T

theorem enum_of_earned (v : Nat → V) (φ : Fm) (h : Earned v φ) : Enum v φ := fun w hr _ => h w hr

/-- A compositional semantics: one table per connective, applied at every node. -/
def mev (n : V → V) (c d i x e : V → V → V) (v : Nat → V) : Fm → V
  | .atom k    => v k
  | .top       => T
  | .bot       => F
  | .neg φ     => n (mev n c d i x e v φ)
  | .conj φ ψ  => c (mev n c d i x e v φ) (mev n c d i x e v ψ)
  | .disj φ ψ  => d (mev n c d i x e v φ) (mev n c d i x e v ψ)
  | .imp φ ψ   => i (mev n c d i x e v φ) (mev n c d i x e v ψ)
  | .xor φ ψ   => x (mev n c d i x e v φ) (mev n c d i x e v ψ)
  | .xnor φ ψ  => e (mev n c d i x e v φ) (mev n c d i x e v ψ)

/-- the valuation p ↦ a, every other atom ↦ b -/
def two (a b : V) : Nat → V := fun k => match k with | 0 => a | _ => b

def Refuted (v : Nat → V) (φ : Fm) : Prop := ∀ w, refines v w → evalF w φ = F
theorem covers_false_only : ∀ x : V, covers x (false, true) = true → x = F := by decide
theorem refines_from_Z (w : Nat → V) : refines (fun _ => Z) w := fun _ h => absurd rfl h

def established (x : V) : V := if x = Z then F else T
def isMark (x : V) : V := if x = Z then T else F

/-- **ZTL says all three with its own connectives:** p ∧ p, p ∨ ¬p, ¬(p ↔ p). -/
theorem ztl_says_evidence :
    (∀ x : V, evalF (fun _ => x) (.conj (.atom 0) (.atom 0)) = up x) ∧
    (∀ x : V, evalF (fun _ => x) (.disj (.atom 0) (.neg (.atom 0))) = established x) ∧
    (∀ x : V, evalF (fun _ => x) (.neg (.xnor (.atom 0) (.atom 0))) = isMark x) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! The primitives, not the clone (2026-10-29). A table for a classical connective g is DECISIVE if it
never answers Z, SOUND if its T is forced by every reading of its arguments, MAXIMAL if it answers T
whenever every reading forces it. The ZTL connective is the only table with all three. Bochvar's
external connectives are decisive but not sound (¬Z = T, Z → F = T). The judge and the stand rest on all
three. -/
def forced1 (g : Bool → Bool) (x : V) : Bool := (subs x).all (fun a => g a)
def forced2 (g : Bool → Bool → Bool) (x y : V) : Bool := (subs x).all (fun a => (subs y).all (fun b => g a b))

def Decisive1 (t : V → V) : Prop := ∀ x, t x ≠ Z
def Sound1 (g : Bool → Bool) (t : V → V) : Prop := ∀ x, t x = T → forced1 g x = true
def Maximal1 (g : Bool → Bool) (t : V → V) : Prop := ∀ x, forced1 g x = true → t x = T
def Decisive2 (t : V → V → V) : Prop := ∀ x y, t x y ≠ Z
def Sound2 (g : Bool → Bool → Bool) (t : V → V → V) : Prop := ∀ x y, t x y = T → forced2 g x y = true
def Maximal2 (g : Bool → Bool → Bool) (t : V → V → V) : Prop := ∀ x y, forced2 g x y = true → t x y = T

theorem lift1_eq (g : Bool → Bool) (x : V) : lift1 g x = (if forced1 g x = true then T else F) := rfl
theorem lift2_eq (g : Bool → Bool → Bool) (x y : V) :
    lift2 g x y = (if forced2 g x y = true then T else F) := rfl

/-- **The ZTL connective is the unique decisive, sound and maximal table** (unary). -/
theorem lift1_characterized (g : Bool → Bool) (t : V → V) :
    (Decisive1 t ∧ Sound1 g t ∧ Maximal1 g t) ↔ (∀ x, t x = lift1 g x) := by
  constructor
  · intro ⟨hd, hs, hm⟩ x
    rw [lift1_eq]
    cases hf : forced1 g x with
    | true => exact hm x hf
    | false =>
      cases ht : t x with
      | T => exact absurd (hs x ht) (by rw [hf]; decide)
      | F => rfl
      | Z => exact absurd ht (hd x)
  · intro h
    refine ⟨fun x => ?_, fun x ht => ?_, fun x hf => ?_⟩
    · rw [h, lift1_eq]; cases forced1 g x <;> decide
    · rw [h, lift1_eq] at ht
      revert ht; cases forced1 g x <;> decide
    · rw [h, lift1_eq, hf]; rfl

/-- **The ZTL connective is the unique decisive, sound and maximal table** (binary). -/
theorem lift2_characterized (g : Bool → Bool → Bool) (t : V → V → V) :
    (Decisive2 t ∧ Sound2 g t ∧ Maximal2 g t) ↔ (∀ x y, t x y = lift2 g x y) := by
  constructor
  · intro ⟨hd, hs, hm⟩ x y
    rw [lift2_eq]
    cases hf : forced2 g x y with
    | true => exact hm x y hf
    | false =>
      cases ht : t x y with
      | T => exact absurd (hs x y ht) (by rw [hf]; decide)
      | F => rfl
      | Z => exact absurd ht (hd x y)
  · intro h
    refine ⟨fun x y => ?_, fun x y ht => ?_, fun x y hf => ?_⟩
    · rw [h, lift2_eq]; cases forced2 g x y <;> decide
    · rw [h, lift2_eq] at ht
      revert ht; cases forced2 g x y <;> decide
    · rw [h, lift2_eq, hf]; rfl

/-- Bochvar's external negation and implication are decisive but not sound: ¬Z = T and Z → F = T,
though a reading of Z as true makes each false. The implication fails under either convention for
external negation, since it does not use it. -/
theorem bochvar_not_sound :
    ¬ Sound1 (fun a => !a) (fun x => bof (!bj x)) ∧
    ¬ Sound2 (fun a b => !a || b) (fun x y => bof (!bj x || bj y)) :=
  ⟨fun h => absurd (h Z (by decide)) (by decide), fun h => absurd (h Z F (by decide)) (by decide)⟩

end V

#print axioms V.nor_lift
#print axioms V.nxor_lift
#print axioms V.lift_id_is_up
#print axioms V.and_self_is_up
#print axioms V.default_of_earned
#print axioms V.substitution_of_earned
#print axioms V.bochvar_is_default_false
#print axioms V.earned_dominates_bochvar
#print axioms V.enum_of_earned
#print axioms V.lift1_characterized
#print axioms V.lift2_characterized
#print axioms V.bochvar_not_sound
#print axioms V.ztl_says_evidence
