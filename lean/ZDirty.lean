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

/-! Kleene with one verdict at the end, and ZTL (2026-10-29). Kleene followed by the assertion ↑ once,
for the whole formula, is a verdict for every formula, but not a compositional one: the verdict of ¬φ is
not a function of the verdict of φ. Conversely, any compositional (truth-functional) semantics that gives
Kleene's verdict on every single connective applied to atoms is ZTL, on every formula. -/

/-- **Kleene's end verdict is not compositional.** No table m gives the verdict of ¬φ from the verdict
of φ: p false and ¬p with p dirty both have verdict F, yet ¬p has verdict T and ¬¬p has verdict F. -/
theorem kleene_end_verdict_not_compositional :
    ¬ ∃ m : V → V, ∀ (v : Nat → V) (φ : Fm), up (kev v (.neg φ)) = m (up (kev v φ)) := by
  intro ⟨m, h⟩
  have h1 := h (fun _ => F) (.atom 0)
  have h2 := h (fun _ => Z) (.neg (.atom 0))
  have e1 : up (kev (fun _ => F) (.neg (.atom 0))) = T := by decide
  have e2 : up (kev (fun _ => F) (.atom 0)) = F := by decide
  have e3 : up (kev (fun _ => Z) (.neg (.neg (.atom 0)))) = F := by decide
  have e4 : up (kev (fun _ => Z) (.neg (.atom 0))) = F := by decide
  rw [e1, e2] at h1
  rw [e3, e4, ← h1] at h2
  exact absurd h2 (by decide)

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

/-- **ZTL is the unique compositional extension of Kleene's verdict on one connective.** If a
compositional semantics agrees with Kleene-then-↑ on every connective applied to atoms (¬p and p∘q,
at every valuation), it agrees with ZTL on every formula at every valuation. -/
theorem ztl_unique_compositional (n : V → V) (c d i x e : V → V → V)
    (hn : ∀ v, mev n c d i x e v (.neg (.atom 0)) = up (kev v (.neg (.atom 0))))
    (hc : ∀ v, mev n c d i x e v (.conj (.atom 0) (.atom 1)) = up (kev v (.conj (.atom 0) (.atom 1))))
    (hd : ∀ v, mev n c d i x e v (.disj (.atom 0) (.atom 1)) = up (kev v (.disj (.atom 0) (.atom 1))))
    (hi : ∀ v, mev n c d i x e v (.imp (.atom 0) (.atom 1)) = up (kev v (.imp (.atom 0) (.atom 1))))
    (hx : ∀ v, mev n c d i x e v (.xor (.atom 0) (.atom 1)) = up (kev v (.xor (.atom 0) (.atom 1))))
    (he : ∀ v, mev n c d i x e v (.xnor (.atom 0) (.atom 1)) = up (kev v (.xnor (.atom 0) (.atom 1)))) :
    ∀ (v : Nat → V) (φ : Fm), mev n c d i x e v φ = evalF v φ := by
  have tn : ∀ a, n a = znot a := fun a => (hn (fun _ => a)).trans (not_is_up_kleene a).symm
  have tc : ∀ a b, c a b = zand a b := fun a b => (hc (two a b)).trans (and_is_up_kleene a b).symm
  have td : ∀ a b, d a b = zor a b := fun a b => (hd (two a b)).trans (or_is_up_kleene a b).symm
  have ti : ∀ a b, i a b = zimp a b := fun a b => (hi (two a b)).trans (imp_is_up_kleene a b).symm
  have tx : ∀ a b, x a b = zxor a b := fun a b => (hx (two a b)).trans (xor_is_up_kleene a b).symm
  have te : ∀ a b, e a b = zxnor a b := fun a b => (he (two a b)).trans (xnor_is_up_kleene a b).symm
  intro v φ
  induction φ with
  | atom k => rfl
  | top => rfl
  | bot => rfl
  | neg φ ih => show n _ = znot _; rw [tn, ih]
  | conj φ ψ ih1 ih2 => show c _ _ = zand _ _; rw [tc, ih1, ih2]
  | disj φ ψ ih1 ih2 => show d _ _ = zor _ _; rw [td, ih1, ih2]
  | imp φ ψ ih1 ih2 => show i _ _ = zimp _ _; rw [ti, ih1, ih2]
  | xor φ ψ ih1 ih2 => show x _ _ = zxor _ _; rw [tx, ih1, ih2]
  | xnor φ ψ ih1 ih2 => show e _ _ = zxnor _ _; rw [te, ih1, ih2]

/-- And ZTL itself is such a semantics, so the hypotheses are not empty. -/
theorem ztl_is_compositional_kleene_verdict (v : Nat → V) :
    evalF v (.neg (.atom 0)) = up (kev v (.neg (.atom 0))) ∧
    evalF v (.conj (.atom 0) (.atom 1)) = up (kev v (.conj (.atom 0) (.atom 1))) :=
  ⟨not_is_up_kleene (v 0), and_is_up_kleene (v 0) (v 1)⟩

/-- **A verdict at every connective excludes De Morgan.** No compositional semantics that gives
Kleene's verdict on every single connective satisfies ¬(p ∧ q) = ¬p ∨ ¬q: by uniqueness it is ZTL, and
at p dirty, q true the two sides are T and F. -/
theorem verdict_everywhere_excludes_de_morgan (n : V → V) (c d i x e : V → V → V)
    (hn : ∀ v, mev n c d i x e v (.neg (.atom 0)) = up (kev v (.neg (.atom 0))))
    (hc : ∀ v, mev n c d i x e v (.conj (.atom 0) (.atom 1)) = up (kev v (.conj (.atom 0) (.atom 1))))
    (hd : ∀ v, mev n c d i x e v (.disj (.atom 0) (.atom 1)) = up (kev v (.disj (.atom 0) (.atom 1))))
    (hi : ∀ v, mev n c d i x e v (.imp (.atom 0) (.atom 1)) = up (kev v (.imp (.atom 0) (.atom 1))))
    (hx : ∀ v, mev n c d i x e v (.xor (.atom 0) (.atom 1)) = up (kev v (.xor (.atom 0) (.atom 1))))
    (he : ∀ v, mev n c d i x e v (.xnor (.atom 0) (.atom 1)) = up (kev v (.xnor (.atom 0) (.atom 1)))) :
    ¬ ∀ v, mev n c d i x e v (.neg (.conj (.atom 0) (.atom 1))) =
      mev n c d i x e v (.disj (.neg (.atom 0)) (.neg (.atom 1))) := by
  intro h
  have u := ztl_unique_compositional n c d i x e hn hc hd hi hx he
  have w := h (two Z T)
  rw [u, u] at w
  exact absurd w (by decide)

/-! The judge's strict dispositions are strong Kleene (2026-10-29). Since the IF STABLE split, EARNED means
T under every refinement AND T under every read of every occurrence; REFUTED the same for F. Both are exactly
the strong Kleene value: the whole-formula question is answered by the judge as Kleene answers it, no more and
no less; everything Kleene leaves at U is marked by the other dispositions. -/
def StrictEarned (v : Nat → V) (φ : Fm) : Prop := Earned v φ ∧ kev v φ = T
def Refuted (v : Nat → V) (φ : Fm) : Prop := ∀ w, refines v w → evalF w φ = F
def StrictRefuted (v : Nat → V) (φ : Fm) : Prop := Refuted v φ ∧ kev v φ = F

/-- **Strict EARNED is strong Kleene T.** -/
theorem strict_earned_iff_kleene (v : Nat → V) (φ : Fm) : StrictEarned v φ ↔ kev v φ = T :=
  ⟨fun h => h.2, fun h => ⟨earned_of_kleene v φ h, h⟩⟩

theorem covers_false_only : ∀ x : V, covers x (false, true) = true → x = F := by decide
theorem kle_F (y : V) (h : kle F y = true) : y = F := by cases y <;> first | rfl | exact absurd h (by decide)

/-- What strong Kleene refutes, ZTL refutes: false under every reading ⇒ the verdict is F. -/
theorem never_laxer (v : Nat → V) (φ : Fm) (h : kev v φ = F) : evalF v φ = F := by
  have c := covers_rd v φ
  rw [rd_is_kleene, h] at c
  exact covers_false_only _ c

/-- **Strict REFUTED is strong Kleene F.** -/
theorem strict_refuted_iff_kleene (v : Nat → V) (φ : Fm) : StrictRefuted v φ ↔ kev v φ = F := by
  refine ⟨fun h => h.2, fun h => ⟨fun w hr => ?_, h⟩⟩
  have hw : kev w φ = F := kle_F _ (by have m := kev_mono v w hr φ; rw [h] at m; exact m)
  exact never_laxer w φ hw

/-! The primitives, not the clone (2026-10-29). A table for a classical connective g is DECISIVE if it
never answers Z, SOUND if its T is forced by every reading of its arguments, MAXIMAL if it answers T
whenever every reading forces it. The ZTL connective is the only table with all three. Bochvar's
external connectives are decisive but not sound (¬Z = T, Z → F = T); strong Kleene's are sound and
maximal but not decisive (¬Z = Z). The judge and the stand rest on all three. -/
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

/-- Strong Kleene is sound and maximal at every connective, but not decisive: ¬Z = Z. -/
theorem kleene_sound_maximal2 (g : Bool → Bool → Bool) : Sound2 g (k2 g) ∧ Maximal2 g (k2 g) := by
  refine ⟨fun x y ht => ?_, fun x y hf => ?_⟩
  · revert ht
    show (if forced2 g x y = true then T else if (subs x).all (fun a => (subs y).all (fun b => !g a b)) then F else Z) = T → _
    cases forced2 g x y with
    | true => intro _; rfl
    | false => cases (subs x).all (fun a => (subs y).all (fun b => !g a b)) <;> decide
  · show (if forced2 g x y = true then T else _) = T
    rw [hf]; rfl
theorem kleene_not_decisive : ¬ Decisive1 (k1 (fun a => !a)) ∧ ¬ Decisive2 (k2 (fun a b => !a || b)) :=
  ⟨fun h => h Z (by decide), fun h => h Z Z (by decide)⟩

/-- Bochvar's external negation and implication are decisive but not sound: ¬Z = T and Z → F = T,
though a reading of Z as true makes each false. The implication fails under either convention for
external negation, since it does not use it. -/
theorem bochvar_not_sound :
    ¬ Sound1 (fun a => !a) (fun x => bof (!bj x)) ∧
    ¬ Sound2 (fun a b => !a || b) (fun x y => bof (!bj x || bj y)) :=
  ⟨fun h => absurd (h Z (by decide)) (by decide), fun h => absurd (h Z F (by decide)) (by decide)⟩

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
#print axioms V.kleene_end_verdict_not_compositional
#print axioms V.ztl_unique_compositional
#print axioms V.ztl_is_compositional_kleene_verdict
#print axioms V.lift1_characterized
#print axioms V.lift2_characterized
#print axioms V.kleene_sound_maximal2
#print axioms V.kleene_not_decisive
#print axioms V.bochvar_not_sound
#print axioms V.verdict_everywhere_excludes_de_morgan
#print axioms V.strict_earned_iff_kleene
#print axioms V.never_laxer
#print axioms V.strict_refuted_iff_kleene
