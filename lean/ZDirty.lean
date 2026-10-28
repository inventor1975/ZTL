import ZTL
import ZClone
import NoGift
/-! # ZDirty — the dirty reading, strong Kleene, and the dominance of the earned verdict. Zero axioms.

Z is a dirty parameter: not ours, its owner may change it between two reads, so each occurrence
is read on its own. What is proved here (2026-10-28):
  * `rd_is_kleene`     — the dirty reading, taken as a semantics, IS strong Kleene logic;
  * `*_is_up_kleene`   — each ZTL connective is strong Kleene followed by the assertion ↑;
  * `covers_rd`, `refusal_witnessed`, `never_stricter` — every F of ZTL is witnessed by a reading;
  * `nand_lift` …      — the lifts of the negated connectives are the argument-side De Morgan forms
                          (the tables ¬(a∘b) are compositions, not lifts — the v2.1.4 correction);
  * `earned_of_kleene`, `substitution_of_earned`, `strict_any` — the judge's EARNED verdict
    (T under every refinement) strictly dominates every classical substitution of the dirty
    atoms, uniform or atom by atom, under the criterion "a grant is right iff the dirty reading
    earns it"; `judge_can_err` — it can still be wrong (¬(p ∧ ¬p)), and then so is every
    substitution.
The matrix ALONE does not dominate (¬¬p); the stable criterion gives no dominance (p ∨ ¬p).

The original header of the working file follows.
The dirty reading: each occurrence of a dirty atom is read on its own. `rd v φ = (t, f)`: under some reading
of its occurrences φ is true (t), resp. false (f). Occurrences in different subformulas are different reads,
so the readings of a compound are the products of the readings of its parts. -/
namespace V

/-- is the classical value a among the reachable ones? -/
def ok (a : Bool) (p : Bool × Bool) : Bool := if a then p.1 else p.2

def comb (g : Bool → Bool → Bool) (p q : Bool × Bool) : Bool × Bool :=
  ([true, false].any (fun a => [true, false].any (fun c => ok a p && ok c q && g a c)),
   [true, false].any (fun a => [true, false].any (fun c => ok a p && ok c q && !(g a c))))

def rd (v : Nat → V) : Fm → Bool × Bool
  | .atom n    => ((subs (v n)).contains true, (subs (v n)).contains false)
  | .top       => (true, false)
  | .bot       => (false, true)
  | .neg φ     => ((rd v φ).2, (rd v φ).1)
  | .conj φ ψ  => comb (fun a b => a && b) (rd v φ) (rd v ψ)
  | .disj φ ψ  => comb (fun a b => a || b) (rd v φ) (rd v ψ)
  | .imp φ ψ   => comb (fun a b => !a || b) (rd v φ) (rd v ψ)
  | .xor φ ψ   => comb (fun a b => a != b) (rd v φ) (rd v ψ)
  | .xnor φ ψ  => comb (fun a b => a == b) (rd v φ) (rd v ψ)

/-- every classical reading of the value x is reachable -/
def covers (x : V) (p : Bool × Bool) : Bool := (subs x).all (fun a => ok a p)

theorem stepNot : ∀ (x : V) (a b : Bool), covers x (a, b) = true → covers (znot x) (b, a) = true := by
  intro x a b; cases x <;> cases a <;> cases b <;> decide

theorem stepBin (g : Bool → Bool → Bool)
    (hg : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
      covers (lift2 g x y) (comb g (a, b) (c, d)) = true)
    (x y : V) (p q : Bool × Bool) (hx : covers x p = true) (hy : covers y q = true) :
    covers (lift2 g x y) (comb g p q) = true := by
  cases p; cases q; exact hg _ _ _ _ _ _ hx hy

theorem hAnd : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a && b) x y) (comb (fun a b => a && b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hOr : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a || b) x y) (comb (fun a b => a || b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hImp : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => !a || b) x y) (comb (fun a b => !a || b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hXor : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a != b) x y) (comb (fun a b => a != b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem hXnor : ∀ (x y : V) (a b c d : Bool), covers x (a, b) = true → covers y (c, d) = true →
    covers (lift2 (fun a b => a == b) x y) (comb (fun a b => a == b) (a, b) (c, d)) = true := by
  intro x y a b c d; cases x <;> cases y <;> cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Every classical reading of the ZTL value is reached by some reading of the occurrences. -/
theorem covers_rd (v : Nat → V) : ∀ φ : Fm, covers (evalF v φ) (rd v φ) = true
  | .atom n => by
      show covers (v n) ((subs (v n)).contains true, (subs (v n)).contains false) = true
      cases v n <;> decide
  | .top => rfl
  | .bot => rfl
  | .neg φ => by
      have h := covers_rd v φ
      show covers (znot (evalF v φ)) ((rd v φ).2, (rd v φ).1) = true
      revert h; cases rd v φ; exact stepNot _ _ _
  | .conj φ ψ => stepBin _ hAnd _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .disj φ ψ => stepBin _ hOr _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .imp φ ψ  => stepBin _ hImp _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .xor φ ψ  => stepBin _ hXor _ _ _ _ (covers_rd v φ) (covers_rd v ψ)
  | .xnor φ ψ => stepBin _ hXnor _ _ _ _ (covers_rd v φ) (covers_rd v ψ)

/-- Every refusal is witnessed by a dirty reading: if ZTL says F, some reading of the occurrences is false. -/
theorem refusal_witnessed (v : Nat → V) (φ : Fm) (h : evalF v φ = F) : (rd v φ).2 = true := by
  have c := covers_rd v φ
  rw [h] at c
  revert c; cases rd v φ with
  | mk t f => cases t <;> cases f <;> decide

/-- Never stricter than the dirty reading: true under every reading of the occurrences ⇒ ZTL grants T. -/
theorem never_stricter (v : Nat → V) (φ : Fm) (h : (rd v φ).2 = false) : evalF v φ = T := by
  have c := covers_rd v φ
  revert c; cases e : evalF v φ with
  | T => intro _; rfl
  | F => intro c; have w := refusal_witnessed v φ e; rw [h] at w; exact absurd w (by decide)
  | Z => revert h; cases rd v φ with
    | mk t f => cases t <;> cases f <;> decide

/-- The converse fails: ¬¬p is granted on a dirty p, though a reading of its one occurrence is false. -/
theorem over_grant : evalF (fun _ => Z) (.neg (.neg (.atom 0))) = T ∧
    (rd (fun _ => Z) (.neg (.neg (.atom 0)))).2 = true := by decide

/-! Strong Kleene followed by the assertion collapse ↑ (u ↦ F), at every connective. -/
/-- strong Kleene as the exact lift: T if every reading is 1, F if every reading is 0, else Z -/
def k1 (f : Bool → Bool) (x : V) : V :=
  if (subs x).all (fun a => f a) then T else if (subs x).all (fun a => !f a) then F else Z
def k2 (f : Bool → Bool → Bool) (x y : V) : V :=
  if (subs x).all (fun a => (subs y).all (fun b => f a b)) then T
  else if (subs x).all (fun a => (subs y).all (fun b => !f a b)) then F else Z
/-- the assertion operator: T stays T, everything else is F -/
def up (x : V) : V := if x = T then T else F

theorem not_is_up_kleene  : ∀ x, znot x = up (k1 (fun a => !a) x) := by decide
theorem and_is_up_kleene  : ∀ x y, zand x y = up (k2 (fun a b => a && b) x y) := by decide
theorem or_is_up_kleene   : ∀ x y, zor x y = up (k2 (fun a b => a || b) x y) := by decide
theorem imp_is_up_kleene  : ∀ x y, zimp x y = up (k2 (fun a b => !a || b) x y) := by decide
theorem xor_is_up_kleene  : ∀ x y, zxor x y = up (k2 (fun a b => a != b) x y) := by decide
theorem xnor_is_up_kleene : ∀ x y, zxnor x y = up (k2 (fun a b => a == b) x y) := by decide
/-- k1/k2 are strong Kleene: on ¬, ∧, ∨ they agree with the core's Kleene tables -/
theorem k_matches_core : (∀ x, k1 (fun a => !a) x = knot x) ∧
    (∀ x y, k2 (fun a b => a && b) x y = kand x y) ∧ (∀ x y, k2 (fun a b => a || b) x y = kor x y) := by decide

/-! The lift of a negated classical connective is the argument-negated (De Morgan) form, not the negated verdict. -/
theorem nand_lift : ∀ a b, znand a b = zor (znot a) (znot b) := by decide
theorem nor_lift  : ∀ a b, znor a b = zand (znot a) (znot b) := by decide
theorem nimp_lift : ∀ a b, znimp a b = zand a (znot b) := by decide
theorem nxor_lift : ∀ a b, lift2 (fun a b => !(a != b)) a b = zxnor a b := by decide

/-- The lift of the identity is the assertion operator, and it is definable as x ∧ x. -/
theorem lift_id_is_up : ∀ x, lift1 (fun a => a) x = up x := by decide
theorem and_self_is_up : ∀ x, zand x x = up x := by decide

/-! The dirty reading IS strong Kleene logic: the set of classical values of φ over all readings of its
occurrences is the strong Kleene value of φ (T ↦ {1}, F ↦ {0}, Z ↦ {1,0}). -/
def enc : V → Bool × Bool
  | T => (true, false)
  | F => (false, true)
  | Z => (true, true)

/-- strong Kleene evaluation (the lazy register), built from the exact lifts k1/k2 -/
def kev (v : Nat → V) : Fm → V
  | .atom n    => v n
  | .top       => T
  | .bot       => F
  | .neg φ     => k1 (fun a => !a) (kev v φ)
  | .conj φ ψ  => k2 (fun a b => a && b) (kev v φ) (kev v ψ)
  | .disj φ ψ  => k2 (fun a b => a || b) (kev v φ) (kev v ψ)
  | .imp φ ψ   => k2 (fun a b => !a || b) (kev v φ) (kev v ψ)
  | .xor φ ψ   => k2 (fun a b => a != b) (kev v φ) (kev v ψ)
  | .xnor φ ψ  => k2 (fun a b => a == b) (kev v φ) (kev v ψ)

theorem kNot : ∀ x, enc (k1 (fun a => !a) x) = ((enc x).2, (enc x).1) := by decide
theorem kAnd : ∀ x y, enc (k2 (fun a b => a && b) x y) = comb (fun a b => a && b) (enc x) (enc y) := by decide
theorem kOr : ∀ x y, enc (k2 (fun a b => a || b) x y) = comb (fun a b => a || b) (enc x) (enc y) := by decide
theorem kImp : ∀ x y, enc (k2 (fun a b => !a || b) x y) = comb (fun a b => !a || b) (enc x) (enc y) := by decide
theorem kXor : ∀ x y, enc (k2 (fun a b => a != b) x y) = comb (fun a b => a != b) (enc x) (enc y) := by decide
theorem kXnor : ∀ x y, enc (k2 (fun a b => a == b) x y) = comb (fun a b => a == b) (enc x) (enc y) := by decide
theorem kAtom : ∀ x, enc x = ((subs x).contains true, (subs x).contains false) := by decide

/-- **The dirty reading is strong Kleene.** -/
theorem rd_is_kleene (v : Nat → V) : ∀ φ : Fm, rd v φ = enc (kev v φ)
  | .atom n => (kAtom (v n)).symm
  | .top => rfl
  | .bot => rfl
  | .neg φ => by
      show ((rd v φ).2, (rd v φ).1) = enc (k1 (fun a => !a) (kev v φ))
      rw [rd_is_kleene v φ, kNot]
  | .conj φ ψ => by
      show comb _ (rd v φ) (rd v ψ) = enc (k2 _ (kev v φ) (kev v ψ))
      rw [rd_is_kleene v φ, rd_is_kleene v ψ, kAnd]
  | .disj φ ψ => by
      show comb _ (rd v φ) (rd v ψ) = enc (k2 _ (kev v φ) (kev v ψ))
      rw [rd_is_kleene v φ, rd_is_kleene v ψ, kOr]
  | .imp φ ψ => by
      show comb _ (rd v φ) (rd v ψ) = enc (k2 _ (kev v φ) (kev v ψ))
      rw [rd_is_kleene v φ, rd_is_kleene v ψ, kImp]
  | .xor φ ψ => by
      show comb _ (rd v φ) (rd v ψ) = enc (k2 _ (kev v φ) (kev v ψ))
      rw [rd_is_kleene v φ, rd_is_kleene v ψ, kXor]
  | .xnor φ ψ => by
      show comb _ (rd v φ) (rd v ψ) = enc (k2 _ (kev v φ) (kev v ψ))
      rw [rd_is_kleene v φ, rd_is_kleene v ψ, kXnor]

/-- Hence earned on the dirty reading ⟺ strong Kleene value T. -/
theorem earned_iff_kleene_T (v : Nat → V) (φ : Fm) : (rd v φ).2 = false ↔ kev v φ = T := by
  rw [rd_is_kleene]; cases kev v φ <;> decide

/-! The judge dominates every uniform classical default (criterion: a grant is right iff the dirty
reading earns it, i.e. strong Kleene T). `Earned` is the judge's EARNED: T now and under every refinement. -/
def kle (x y : V) : Bool := x == Z || x == y          -- information order: Z below everything

theorem kmono1 : ∀ x x' : V, kle x x' = true → kle (k1 (fun a => !a) x) (k1 (fun a => !a) x') = true := by decide
theorem kmonoAnd : ∀ x x' y y' : V, kle x x' = true → kle y y' = true →
    kle (k2 (fun a b => a && b) x y) (k2 (fun a b => a && b) x' y') = true := by decide
theorem kmonoOr : ∀ x x' y y' : V, kle x x' = true → kle y y' = true →
    kle (k2 (fun a b => a || b) x y) (k2 (fun a b => a || b) x' y') = true := by decide
theorem kmonoImp : ∀ x x' y y' : V, kle x x' = true → kle y y' = true →
    kle (k2 (fun a b => !a || b) x y) (k2 (fun a b => !a || b) x' y') = true := by decide
theorem kmonoXor : ∀ x x' y y' : V, kle x x' = true → kle y y' = true →
    kle (k2 (fun a b => a != b) x y) (k2 (fun a b => a != b) x' y') = true := by decide
theorem kmonoXnor : ∀ x x' y y' : V, kle x x' = true → kle y y' = true →
    kle (k2 (fun a b => a == b) x y) (k2 (fun a b => a == b) x' y') = true := by decide
theorem kle_of_refines (a b : V) (h : a ≠ Z → b = a) : kle a b = true := by
  cases a <;> cases b <;> first | rfl | (exact absurd (h (by decide)) (by decide))

/-- Strong Kleene is monotone under refinement. -/
theorem kev_mono (v w : Nat → V) (hr : refines v w) : ∀ φ : Fm, kle (kev v φ) (kev w φ) = true
  | .atom n => kle_of_refines (v n) (w n) (hr n)
  | .top => rfl
  | .bot => rfl
  | .neg φ => kmono1 _ _ (kev_mono v w hr φ)
  | .conj φ ψ => kmonoAnd _ _ _ _ (kev_mono v w hr φ) (kev_mono v w hr ψ)
  | .disj φ ψ => kmonoOr _ _ _ _ (kev_mono v w hr φ) (kev_mono v w hr ψ)
  | .imp φ ψ => kmonoImp _ _ _ _ (kev_mono v w hr φ) (kev_mono v w hr ψ)
  | .xor φ ψ => kmonoXor _ _ _ _ (kev_mono v w hr φ) (kev_mono v w hr ψ)
  | .xnor φ ψ => kmonoXnor _ _ _ _ (kev_mono v w hr φ) (kev_mono v w hr ψ)

theorem kle_T (y : V) (h : kle T y = true) : y = T := by cases y <;> first | rfl | exact absurd h (by decide)

/-- The judge's EARNED: T now and under every refinement of the marks. -/
def Earned (v : Nat → V) (φ : Fm) : Prop := ∀ w, refines v w → evalF w φ = T

/-- (1) What the dirty reading earns, the judge grants. -/
theorem earned_of_kleene (v : Nat → V) (φ : Fm) (h : kev v φ = T) : Earned v φ := by
  intro w hr
  have hw : kev w φ = T := kle_T _ (by have m := kev_mono v w hr φ; rw [h] at m; exact m)
  exact never_stricter w φ ((earned_iff_kleene_T w φ).mpr hw)

/-- A uniform default: every dirty atom set to d. -/
def subst (v : Nat → V) (d : V) : Nat → V := fun n => if v n = Z then d else v n

theorem subst_refines (v : Nat → V) (d : V) : refines v (subst v d) := by
  intro n hn; show (if v n = Z then d else v n) = v n; exact if_neg hn

/-- (2) What the judge grants, every uniform default grants. -/
theorem default_of_earned (v : Nat → V) (φ : Fm) (d : V) (h : Earned v φ) : evalF (subst v d) φ = T :=
  h _ (subst_refines v d)

/-- Strictness, both defaults: ¬p and p with p dirty are not earned, the judge refuses them, a default grants. -/
theorem strict_false : kev (fun _ => Z) (.neg (.atom 0)) ≠ T ∧ evalF (fun _ => Z) (.neg (.atom 0)) ≠ T ∧
    evalF (subst (fun _ => Z) F) (.neg (.atom 0)) = T := by decide
theorem strict_true : kev (fun _ => Z) (.atom 0) ≠ T ∧ evalF (fun _ => Z) (.atom 0) ≠ T ∧
    evalF (subst (fun _ => Z) T) (.atom 0) = T := by decide

/-- (2') The same against ANY classical substitution of the dirty atoms, uniform or chosen per atom:
a substitution is a total refinement, so what the judge earns, it grants. -/
theorem substitution_of_earned (v w : Nat → V) (φ : Fm) (hr : refines v w) (h : Earned v φ) :
    evalF w φ = T := h w hr

/-- Strictness against every substitution: whatever value a substitution gives a dirty p,
one of p, ¬p is granted by it and refused by the judge, and neither is earned on the dirty reading. -/
theorem strict_any (w : Nat → V) (hw : w 0 = T ∨ w 0 = F) :
    (evalF w (.atom 0) = T ∧ evalF (fun _ => Z) (.atom 0) ≠ T ∧ kev (fun _ => Z) (.atom 0) ≠ T) ∨
    (evalF w (.neg (.atom 0)) = T ∧ evalF (fun _ => Z) (.neg (.atom 0)) ≠ T ∧
      kev (fun _ => Z) (.neg (.atom 0)) ≠ T) := by
  cases hw with
  | inl h => exact Or.inl ⟨h, by decide, by decide⟩
  | inr h => exact Or.inr ⟨by show znot (w 0) = T; rw [h]; rfl, by decide, by decide⟩

/-- The judge is not always right: ¬(p ∧ ¬p) is EARNED on a dirty p, yet not earned on the dirty
reading — and there every substitution grants it too. -/
theorem judge_can_err : kev (fun _ => Z) (.neg (.conj (.atom 0) (.neg (.atom 0)))) ≠ T := by decide

/-! Bochvar's external connectives are the classical default "dirty := false" (2026-10-29).
Each external connective of Bochvar (Karpenko–Tomova convention: external negation reads "not true")
applies the assertion J₂ (x ↦ x = T) to its arguments and then the classical connective. -/
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

/-- **The judge dominates Bochvar.** What the judge earns, Bochvar grants; and on a dirty p,
Bochvar grants ¬p, which the judge refuses and the dirty reading does not earn. -/
theorem earned_dominates_bochvar (v : Nat → V) (φ : Fm) (h : Earned v φ) : bev v φ = T :=
  bj_T _ (by rw [bochvar_is_default_false]; have e := default_of_earned v φ F h; rw [e]; rfl)
theorem bochvar_strict : bev (fun _ => Z) (.neg (.atom 0)) = T ∧ ¬ Earned (fun _ => Z) (.neg (.atom 0)) ∧
    kev (fun _ => Z) (.neg (.atom 0)) ≠ T :=
  ⟨by decide, fun h => absurd (h _ (refines_refl _)) (by decide), by decide⟩

/-! Classical logic with enumeration: grant iff the formula is classically true in every completion
(a total refinement; on total valuations ZTL is classical, `evalF_agrees`). Under the criterion of this
module (a grant is right iff the dirty reading earns it, i.e. strong Kleene T) the judge has the same
right grants and its wrong grants are among enumeration's. -/
def total (w : Nat → V) : Prop := ∀ n, w n ≠ Z
def Enum (v : Nat → V) (φ : Fm) : Prop := ∀ w, refines v w → total w → evalF w φ = T

theorem enum_of_earned (v : Nat → V) (φ : Fm) (h : Earned v φ) : Enum v φ := fun w hr _ => h w hr

/-- **The judge dominates enumeration under the dirty reading.** Right grants coincide (both are
exactly the strong Kleene T), and every wrong grant of the judge is a wrong grant of enumeration. -/
theorem earned_dominates_enum (v : Nat → V) (φ : Fm) :
    ((Earned v φ ∧ kev v φ = T) ↔ (Enum v φ ∧ kev v φ = T)) ∧
    ((Earned v φ ∧ kev v φ ≠ T) → (Enum v φ ∧ kev v φ ≠ T)) :=
  ⟨⟨fun ⟨h, k⟩ => ⟨enum_of_earned v φ h, k⟩, fun ⟨_, k⟩ => ⟨earned_of_kleene v φ k, k⟩⟩,
   fun ⟨h, k⟩ => ⟨enum_of_earned v φ h, k⟩⟩

/-- Strictly: on a dirty p, enumeration grants p → p, which the judge refuses and the dirty reading
does not earn (two reads may give 1 and 0). -/
theorem enum_strict : Enum (fun _ => Z) (.imp (.atom 0) (.atom 0)) ∧
    ¬ Earned (fun _ => Z) (.imp (.atom 0) (.atom 0)) ∧ kev (fun _ => Z) (.imp (.atom 0) (.atom 0)) ≠ T := by
  refine ⟨fun w _ ht => ?_, fun h => absurd (h _ (refines_refl _)) (by decide), by decide⟩
  have h0 := ht 0
  show zimp (w 0) (w 0) = T
  revert h0
  cases w 0 <;> decide

end V

#print axioms V.covers_rd
#print axioms V.refusal_witnessed
#print axioms V.never_stricter
#print axioms V.over_grant
#print axioms V.imp_is_up_kleene
#print axioms V.xnor_is_up_kleene
#print axioms V.k_matches_core
#print axioms V.nor_lift
#print axioms V.nxor_lift
#print axioms V.lift_id_is_up
#print axioms V.and_self_is_up
#print axioms V.rd_is_kleene
#print axioms V.earned_iff_kleene_T
#print axioms V.earned_of_kleene
#print axioms V.default_of_earned
#print axioms V.strict_false
#print axioms V.strict_true
#print axioms V.substitution_of_earned
#print axioms V.strict_any
#print axioms V.judge_can_err
#print axioms V.bochvar_is_default_false
#print axioms V.earned_dominates_bochvar
#print axioms V.bochvar_strict
#print axioms V.enum_of_earned
#print axioms V.earned_dominates_enum
#print axioms V.enum_strict
