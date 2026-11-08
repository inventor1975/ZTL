import ZTL
/-!
# ZGrade — the judge's GRADE as a kernel decision, with its meaning proved. Zero axioms.

The Python judge (`ztljudge.check` → `zverify.grade`) returns, for a claim `φ` under a marking `m` (each atom
`T`, `F` or a mark `Z`), its VALUE `evalF m φ` and a GRADE built from two bits:

  * HEREDITARY — the value is the same under EVERY refinement of the marks (any subset of them verified to
    any classical values): `Hered m φ`;
  * STABLE — the value is the same under every COMPLETION (every mark verified): `Stable m φ`;

  `hereditary` if `Hered`; `until-verification` if not `Stable`; `sound` if `Stable` but not `Hered`.

Both bits quantify over all valuations `Nat → V` — infinitely many. Here they are decided by walking only the
marked atoms OF THE FORMULA (`heredB`, `stableB`; the value of a formula depends only on its atoms), and the
walk is proved to mean the definition IN BOTH DIRECTIONS (`heredB_iff`, `stableB_iff`). So a grade computed
by `decide` in the kernel IS a theorem about the claim: `grade m φ = .hereditary → Hered m φ`, and
`grade m φ = .untilVerification → ¬ Stable m φ` with the witness completion.

This is the bridge from the paradox stands (`dilemmas/`, 35 of 53 through the judge) to Lean: a stand's
`(formula, marking, verdict)` becomes `grade m φ = g := by decide`.
-/

namespace ZGrade
open V

/-- Claims: atoms, constants, and the kernel's six connectives (as in `ztl.py`). -/
inductive Fm where
  | atom : Nat → Fm
  | cst : V → Fm
  | neg : Fm → Fm
  | conj : Fm → Fm → Fm
  | disj : Fm → Fm → Fm
  | imp : Fm → Fm → Fm
  | xor : Fm → Fm → Fm
  | xnor : Fm → Fm → Fm

def evalF (m : Nat → V) : Fm → V
  | .atom n => m n
  | .cst v => v
  | .neg φ => znot (evalF m φ)
  | .conj φ ψ => zand (evalF m φ) (evalF m ψ)
  | .disj φ ψ => zor (evalF m φ) (evalF m ψ)
  | .imp φ ψ => zimp (evalF m φ) (evalF m ψ)
  | .xor φ ψ => zxor (evalF m φ) (evalF m ψ)
  | .xnor φ ψ => zxnor (evalF m φ) (evalF m ψ)

/-! ## The definitions -/

/-- `w` refines `m`: every verified atom of `m` keeps its value. -/
def refines (m w : Nat → V) : Prop := ∀ n, m n ≠ Z → w n = m n

def Hered (m : Nat → V) (φ : Fm) : Prop := ∀ w, refines m w → evalF w φ = evalF m φ
def Stable (m : Nat → V) (φ : Fm) : Prop := ∀ w, refines m w → (∀ n, w n ≠ Z) → evalF w φ = evalF m φ

/-! ## Decidable pieces, by our own recursion -/

def veq : V → V → Bool
  | T, T => true
  | F, F => true
  | Z, Z => true
  | T, F => false
  | T, Z => false
  | F, T => false
  | F, Z => false
  | Z, T => false
  | Z, F => false

theorem veq_eq : ∀ {a b : V}, veq a b = true → a = b
  | T, T, _ => rfl
  | F, F, _ => rfl
  | Z, Z, _ => rfl
  | T, F, h => by cases h
  | T, Z, h => by cases h
  | F, T, h => by cases h
  | F, Z, h => by cases h
  | Z, T, h => by cases h
  | Z, F, h => by cases h

theorem veq_refl : ∀ a : V, veq a a = true
  | T => rfl
  | F => rfl
  | Z => rfl

theorem veq_ne {a b : V} (h : veq a b = false) : a ≠ b := by
  intro e; rw [e, veq_refl] at h; cases h

def isZ : V → Bool
  | Z => true
  | T => false
  | F => false

theorem isZ_true : ∀ {a : V}, isZ a = true → a = Z
  | Z, _ => rfl
  | T, h => by cases h
  | F, h => by cases h

theorem isZ_false : ∀ {a : V}, isZ a = false → a ≠ Z
  | Z, h => by cases h
  | T, _ => fun e => by cases e
  | F, _ => fun e => by cases e

/-- The atoms of a claim (with repetitions). -/
def atomsL : Fm → List Nat
  | .atom n => [n]
  | .cst _ => []
  | .neg φ => atomsL φ
  | .conj φ ψ => atomsL φ ++ atomsL ψ
  | .disj φ ψ => atomsL φ ++ atomsL ψ
  | .imp φ ψ => atomsL φ ++ atomsL ψ
  | .xor φ ψ => atomsL φ ++ atomsL ψ
  | .xnor φ ψ => atomsL φ ++ atomsL ψ

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

def memB (n : Nat) : List Nat → Bool
  | [] => false
  | a :: l => Nat.beq n a || memB n l

theorem memB_app_l (n : Nat) : ∀ (l r : List Nat), memB n l = true → memB n (l ++ r) = true
  | [], _, h => by cases h
  | a :: l, r, h => by
      show (Nat.beq n a || memB n (l ++ r)) = true
      cases hb : Nat.beq n a with
      | true => rfl
      | false =>
          have h' : memB n l = true := by
            have : (Nat.beq n a || memB n l) = true := h
            rw [hb] at this; exact this
          show (false || memB n (l ++ r)) = true
          exact memB_app_l n l r h'

theorem memB_app_r (n : Nat) : ∀ (l r : List Nat), memB n r = true → memB n (l ++ r) = true
  | [], _, h => h
  | a :: l, r, h => by
      show (Nat.beq n a || memB n (l ++ r)) = true
      cases hb : Nat.beq n a with
      | true => rfl
      | false => exact memB_app_r n l r h

/-- The value depends only on the atoms of the claim. -/
theorem evalF_congr {m w : Nat → V} : ∀ φ : Fm, (∀ n, memB n (atomsL φ) = true → w n = m n) →
    evalF w φ = evalF m φ
  | .atom n, h => h n (by show (Nat.beq n n || false) = true; rw [beq_self]; rfl)
  | .cst _, _ => rfl
  | .neg φ, h => by show znot (evalF w φ) = znot (evalF m φ); rw [evalF_congr φ h]
  | .conj φ ψ, h => by
      show zand (evalF w φ) (evalF w ψ) = zand (evalF m φ) (evalF m ψ)
      rw [evalF_congr φ (fun n hn => h n (memB_app_l n _ _ hn)), evalF_congr ψ (fun n hn => h n (memB_app_r n _ _ hn))]
  | .disj φ ψ, h => by
      show zor (evalF w φ) (evalF w ψ) = zor (evalF m φ) (evalF m ψ)
      rw [evalF_congr φ (fun n hn => h n (memB_app_l n _ _ hn)), evalF_congr ψ (fun n hn => h n (memB_app_r n _ _ hn))]
  | .imp φ ψ, h => by
      show zimp (evalF w φ) (evalF w ψ) = zimp (evalF m φ) (evalF m ψ)
      rw [evalF_congr φ (fun n hn => h n (memB_app_l n _ _ hn)), evalF_congr ψ (fun n hn => h n (memB_app_r n _ _ hn))]
  | .xor φ ψ, h => by
      show zxor (evalF w φ) (evalF w ψ) = zxor (evalF m φ) (evalF m ψ)
      rw [evalF_congr φ (fun n hn => h n (memB_app_l n _ _ hn)), evalF_congr ψ (fun n hn => h n (memB_app_r n _ _ hn))]
  | .xnor φ ψ, h => by
      show zxnor (evalF w φ) (evalF w ψ) = zxnor (evalF m φ) (evalF m ψ)
      rw [evalF_congr φ (fun n hn => h n (memB_app_l n _ _ hn)), evalF_congr ψ (fun n hn => h n (memB_app_r n _ _ hn))]

/-! ## The walks -/

def upd (m : Nat → V) (a : Nat) (x : V) : Nat → V := fun n => cond (Nat.beq n a) x (m n)

/-- Every refinement of `m` on the atoms `L` (each mark → `T`, `F` or kept). -/
def allRef (P : (Nat → V) → Bool) : (Nat → V) → List Nat → Bool
  | m, [] => P m
  | m, a :: L => cond (isZ (m a)) (allRef P (upd m a T) L && allRef P (upd m a F) L && allRef P m L) (allRef P m L)

/-- Every completion of `m` on the atoms `L` (each mark → `T` or `F`). -/
def allCom (P : (Nat → V) → Bool) : (Nat → V) → List Nat → Bool
  | m, [] => P m
  | m, a :: L => cond (isZ (m a)) (allCom P (upd m a T) L && allCom P (upd m a F) L) (allCom P m L)

def heredB (m : Nat → V) (φ : Fm) : Bool := allRef (fun w => veq (evalF w φ) (evalF m φ)) m (atomsL φ)
def stableB (m : Nat → V) (φ : Fm) : Bool := allCom (fun w => veq (evalF w φ) (evalF m φ)) m (atomsL φ)


/-! ## The walks mean the definitions -/

theorem and_true_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem upd_same (m : Nat → V) (a : Nat) (x : V) : upd m a x a = x := by
  show cond (Nat.beq a a) x (m a) = x; rw [beq_self]; rfl

theorem upd_other (m : Nat → V) {a n : Nat} (x : V) (h : Nat.beq n a = false) : upd m a x n = m n := by
  show cond (Nat.beq n a) x (m n) = m n; rw [h]; rfl

theorem memB_cons_false {n a : Nat} {L : List Nat} (h : memB n (a :: L) = false) : Nat.beq n a = false ∧ memB n L = false := by
  have h' : (Nat.beq n a || memB n L) = false := h
  cases hb : Nat.beq n a with
  | true => rw [hb] at h'; cases h'
  | false => rw [hb] at h'; exact ⟨rfl, h'⟩

theorem refines_refl (m : Nat → V) : refines m m := fun _ _ => rfl

theorem refines_trans {m u w : Nat → V} (h1 : refines m u) (h2 : refines u w) : refines m w := by
  intro n hn
  have e := h1 n hn
  rw [h2 n (by rw [e]; exact hn), e]

theorem refines_upd {m : Nat → V} {a : Nat} (ha : m a = Z) (x : V) : refines m (upd m a x) := by
  intro n hn
  cases hb : Nat.beq n a with
  | true => have := Nat.eq_of_beq_eq_true hb; subst this; exact absurd ha hn
  | false => exact upd_other m x hb

/-- A refinement of `m` that agrees with `upd m a x` at `a`, and with `m` outside `L`, refines `upd m a x`. -/
theorem step_ref {m w : Nat → V} {a : Nat} {x : V} (hx : x ≠ Z) (hw : refines m w) (hwa : w a = x) :
    refines (upd m a x) w := by
  intro n hn
  cases hb : Nat.beq n a with
  | true => have := Nat.eq_of_beq_eq_true hb; subst this; rw [upd_same, hwa]
  | false => rw [upd_other m x hb] at hn ⊢; exact hw n hn

theorem step_out {m w : Nat → V} {a : Nat} {L : List Nat} {x : V} (hwa : w a = x)
    (ho : ∀ n, memB n (a :: L) = false → w n = m n) : ∀ n, memB n L = false → w n = upd m a x n := by
  intro n hn
  cases hb : Nat.beq n a with
  | true => have := Nat.eq_of_beq_eq_true hb; subst this; rw [upd_same, hwa]
  | false =>
      rw [upd_other m x hb]
      exact ho n (by show (Nat.beq n a || memB n L) = false; rw [hb, hn]; rfl)

theorem step_out_same {m w : Nat → V} {a : Nat} {L : List Nat} (hwa : w a = m a)
    (ho : ∀ n, memB n (a :: L) = false → w n = m n) : ∀ n, memB n L = false → w n = m n := by
  intro n hn
  cases hb : Nat.beq n a with
  | true => have := Nat.eq_of_beq_eq_true hb; subst this; exact hwa
  | false => exact ho n (by show (Nat.beq n a || memB n L) = false; rw [hb, hn]; rfl)

section
variable (P : (Nat → V) → Bool) (Pext : ∀ u u' : Nat → V, (∀ n, u n = u' n) → P u = P u')
include Pext

theorem allRef_sound : ∀ (L : List Nat) (m : Nat → V), allRef P m L = true →
    ∀ w, refines m w → (∀ n, memB n L = false → w n = m n) → P w = true
  | [], m, h, w, _, ho => by rw [Pext w m (fun n => ho n rfl)]; exact h
  | a :: L, m, h, w, hw, ho => by
      cases hz : isZ (m a) with
      | true =>
          have h' : (allRef P (upd m a T) L && allRef P (upd m a F) L && allRef P m L) = true := by
            have : cond (isZ (m a)) (allRef P (upd m a T) L && allRef P (upd m a F) L && allRef P m L) (allRef P m L) = true := h
            rw [hz] at this; exact this
          have hT := (and_true_split (and_true_split h').1).1
          have hF := (and_true_split (and_true_split h').1).2
          have hM := (and_true_split h').2
          cases hwa : w a with
          | T => exact allRef_sound L _ hT w (step_ref (fun e => by cases e) hw hwa) (step_out hwa ho)
          | F => exact allRef_sound L _ hF w (step_ref (fun e => by cases e) hw hwa) (step_out hwa ho)
          | Z => exact allRef_sound L m hM w hw (step_out_same (by rw [hwa, isZ_true hz]) ho)
      | false =>
          have h' : allRef P m L = true := by
            have : cond (isZ (m a)) (allRef P (upd m a T) L && allRef P (upd m a F) L && allRef P m L) (allRef P m L) = true := h
            rw [hz] at this; exact this
          exact allRef_sound L m h' w hw (step_out_same (hw a (isZ_false hz)) ho)

theorem allCom_sound : ∀ (L : List Nat) (m : Nat → V), allCom P m L = true →
    ∀ w, refines m w → (∀ n, memB n L = true → w n ≠ Z) → (∀ n, memB n L = false → w n = m n) → P w = true
  | [], m, h, w, _, _, ho => by rw [Pext w m (fun n => ho n rfl)]; exact h
  | a :: L, m, h, w, hw, ht, ho => by
      have hta : w a ≠ Z := ht a (by show (Nat.beq a a || memB a L) = true; rw [beq_self]; rfl)
      have htL : ∀ n, memB n L = true → w n ≠ Z := fun n hn => ht n (by
        show (Nat.beq n a || memB n L) = true; rw [hn]; cases Nat.beq n a <;> rfl)
      cases hz : isZ (m a) with
      | true =>
          have h' : (allCom P (upd m a T) L && allCom P (upd m a F) L) = true := by
            have : cond (isZ (m a)) (allCom P (upd m a T) L && allCom P (upd m a F) L) (allCom P m L) = true := h
            rw [hz] at this; exact this
          cases hwa : w a with
          | T => exact allCom_sound L _ (and_true_split h').1 w (step_ref (fun e => by cases e) hw hwa) htL (step_out hwa ho)
          | F => exact allCom_sound L _ (and_true_split h').2 w (step_ref (fun e => by cases e) hw hwa) htL (step_out hwa ho)
          | Z => exact absurd hwa hta
      | false =>
          have h' : allCom P m L = true := by
            have : cond (isZ (m a)) (allCom P (upd m a T) L && allCom P (upd m a F) L) (allCom P m L) = true := h
            rw [hz] at this; exact this
          exact allCom_sound L m h' w hw htL (step_out_same (hw a (isZ_false hz)) ho)
end

theorem allRef_complete (P : (Nat → V) → Bool) : ∀ (L : List Nat) (m : Nat → V), allRef P m L = false →
    ∃ w, refines m w ∧ P w = false
  | [], m, h => ⟨m, refines_refl m, h⟩
  | a :: L, m, h => by
      cases hz : isZ (m a) with
      | true =>
          have h' : (allRef P (upd m a T) L && allRef P (upd m a F) L && allRef P m L) = false := by
            have : cond (isZ (m a)) (allRef P (upd m a T) L && allRef P (upd m a F) L && allRef P m L) (allRef P m L) = false := h
            rw [hz] at this; exact this
          cases h1 : allRef P (upd m a T) L with
          | false =>
              obtain ⟨w, hw, hp⟩ := allRef_complete P L _ h1
              exact ⟨w, refines_trans (refines_upd (isZ_true hz) T) hw, hp⟩
          | true =>
          cases h2 : allRef P (upd m a F) L with
          | false =>
              obtain ⟨w, hw, hp⟩ := allRef_complete P L _ h2
              exact ⟨w, refines_trans (refines_upd (isZ_true hz) F) hw, hp⟩
          | true =>
          cases h3 : allRef P m L with
          | false => exact allRef_complete P L m h3
          | true => rw [h1, h2, h3] at h'; cases h'
      | false =>
          have h' : allRef P m L = false := by
            have : cond (isZ (m a)) (allRef P (upd m a T) L && allRef P (upd m a F) L && allRef P m L) (allRef P m L) = false := h
            rw [hz] at this; exact this
          exact allRef_complete P L m h'

theorem allCom_complete (P : (Nat → V) → Bool) : ∀ (L : List Nat) (m : Nat → V), allCom P m L = false →
    ∃ w, refines m w ∧ (∀ n, memB n L = true → w n ≠ Z) ∧ P w = false
  | [], m, h => ⟨m, refines_refl m, (fun n (h' : memB n [] = true) => by cases h'), h⟩
  | a :: L, m, h => by
      have ext : ∀ {u w : Nat → V}, refines u w → u a ≠ Z → (∀ n, memB n L = true → w n ≠ Z) →
          ∀ n, memB n (a :: L) = true → w n ≠ Z := by
        intro u w hw hua hL n hn
        cases hb : Nat.beq n a with
        | true => have := Nat.eq_of_beq_eq_true hb; subst this; rw [hw n hua]; exact hua
        | false =>
            have : (Nat.beq n a || memB n L) = true := hn
            rw [hb] at this; exact hL n this
      cases hz : isZ (m a) with
      | true =>
          have h' : (allCom P (upd m a T) L && allCom P (upd m a F) L) = false := by
            have : cond (isZ (m a)) (allCom P (upd m a T) L && allCom P (upd m a F) L) (allCom P m L) = false := h
            rw [hz] at this; exact this
          cases h1 : allCom P (upd m a T) L with
          | false =>
              obtain ⟨w, hw, hL, hp⟩ := allCom_complete P L _ h1
              exact ⟨w, refines_trans (refines_upd (isZ_true hz) T) hw,
                ext hw (by rw [upd_same]; exact fun e => by cases e) hL, hp⟩
          | true =>
          cases h2 : allCom P (upd m a F) L with
          | false =>
              obtain ⟨w, hw, hL, hp⟩ := allCom_complete P L _ h2
              exact ⟨w, refines_trans (refines_upd (isZ_true hz) F) hw,
                ext hw (by rw [upd_same]; exact fun e => by cases e) hL, hp⟩
          | true => rw [h1, h2] at h'; cases h'
      | false =>
          have h' : allCom P m L = false := by
            have : cond (isZ (m a)) (allCom P (upd m a T) L && allCom P (upd m a F) L) (allCom P m L) = false := h
            rw [hz] at this; exact this
          obtain ⟨w, hw, hL, hp⟩ := allCom_complete P L m h'
          exact ⟨w, hw, ext hw (isZ_false hz) hL, hp⟩

/-! ## The two bits are the definitions -/

theorem pext (φ : Fm) (v : V) : ∀ u u' : Nat → V, (∀ n, u n = u' n) →
    veq (evalF u φ) v = veq (evalF u' φ) v := fun u u' h => by rw [evalF_congr φ (fun n _ => h n)]

/-- The restriction of `w` to the atoms `L`, `m` elsewhere. -/
def restr (m w : Nat → V) (L : List Nat) : Nat → V := fun n => cond (memB n L) (w n) (m n)

theorem restr_refines {m w : Nat → V} (hw : refines m w) (L : List Nat) : refines m (restr m w L) := by
  intro n hn; show cond (memB n L) (w n) (m n) = m n
  cases memB n L with
  | true => exact hw n hn
  | false => rfl

theorem restr_out (m w : Nat → V) (L : List Nat) : ∀ n, memB n L = false → restr m w L n = m n := by
  intro n hn; show cond (memB n L) (w n) (m n) = m n; rw [hn]; rfl

theorem restr_on (m w : Nat → V) (L : List Nat) : ∀ n, memB n L = true → restr m w L n = w n := by
  intro n hn; show cond (memB n L) (w n) (m n) = w n; rw [hn]; rfl

theorem heredB_sound {m : Nat → V} {φ : Fm} (h : heredB m φ = true) : Hered m φ := by
  intro w hw
  have p := allRef_sound _ (pext φ (evalF m φ)) (atomsL φ) m h (restr m w (atomsL φ))
    (restr_refines hw _) (restr_out m w _)
  have e := evalF_congr (m := w) (w := restr m w (atomsL φ)) φ (restr_on m w _)
  rw [← e]; exact veq_eq p

theorem heredB_complete {m : Nat → V} {φ : Fm} (h : heredB m φ = false) : ¬ Hered m φ := by
  intro H
  obtain ⟨w, hw, hp⟩ := allRef_complete _ (atomsL φ) m h
  rw [H w hw, veq_refl] at hp; cases hp

theorem stableB_sound {m : Nat → V} {φ : Fm} (h : stableB m φ = true) : Stable m φ := by
  intro w hw ht
  have p := allCom_sound _ (pext φ (evalF m φ)) (atomsL φ) m h (restr m w (atomsL φ))
    (restr_refines hw _) (fun n hn => by rw [restr_on m w _ n hn]; exact ht n) (restr_out m w _)
  have e := evalF_congr (m := w) (w := restr m w (atomsL φ)) φ (restr_on m w _)
  rw [← e]; exact veq_eq p

/-- Total from non-`Z` on the atoms: the other marks to `T`. -/
def total (w : Nat → V) : Nat → V := fun n => cond (isZ (w n)) T (w n)

theorem stableB_complete {m : Nat → V} {φ : Fm} (h : stableB m φ = false) : ¬ Stable m φ := by
  intro H
  obtain ⟨w, hw, hL, hp⟩ := allCom_complete _ (atomsL φ) m h
  have tw : refines m (total w) := by
    intro n hn; show cond (isZ (w n)) T (w n) = m n
    have e := hw n hn
    cases hz : isZ (w n) with
    | true => rw [isZ_true hz] at e; exact absurd e.symm hn
    | false => exact e
  have tt : ∀ n, total w n ≠ Z := by
    intro n; show cond (isZ (w n)) T (w n) ≠ Z
    cases hz : isZ (w n) with
    | true => exact fun e => by cases e
    | false => exact isZ_false hz
  have ee : evalF (total w) φ = evalF w φ := evalF_congr φ (fun n hn => by
    show cond (isZ (w n)) T (w n) = w n
    cases hz : isZ (w n) with
    | true => exact absurd (isZ_true hz) (hL n hn)
    | false => rfl)
  have := H (total w) tw tt
  rw [ee] at this
  rw [this, veq_refl] at hp; cases hp


/-! ## A witness instead of the walk (for claims with many marks)

`grade` walks `2ᵏ`/`3ᵏ` readings of the `k` marks — fine for a few, not for fourteen. A NEGATIVE bit needs
no walk: one completion that changes the value is a proof. The completion is named by the list `S` of marks
read `F` (every other mark reads `T`), so it is total and refines `m` by construction. -/

def wS (m : Nat → V) (S : List Nat) : Nat → V := fun n => cond (isZ (m n)) (cond (memB n S) F T) (m n)

theorem wS_refines (m : Nat → V) (S : List Nat) : refines m (wS m S) := by
  intro n hn; show cond (isZ (m n)) (cond (memB n S) F T) (m n) = m n
  cases hz : isZ (m n) with
  | true => exact absurd (isZ_true hz) hn
  | false => rfl

theorem wS_total (m : Nat → V) (S : List Nat) : ∀ n, wS m S n ≠ Z := by
  intro n; show cond (isZ (m n)) (cond (memB n S) F T) (m n) ≠ Z
  cases hz : isZ (m n) with
  | true => cases memB n S <;> exact fun e => by cases e
  | false => exact isZ_false hz

/-- **One completion that changes the value: the claim is not stable (so not hereditary either).** -/
theorem notStable_witness {m : Nat → V} {φ : Fm} (S : List Nat)
    (h : veq (evalF (wS m S) φ) (evalF m φ) = false) : ¬ Stable m φ ∧ ¬ Hered m φ := by
  refine ⟨fun H => veq_ne h (H _ (wS_refines m S) (wS_total m S)), fun H => veq_ne h (H _ (wS_refines m S))⟩

/-! ## The grade -/

inductive Grade where
  | hereditary
  | sound
  | untilVerification
deriving DecidableEq

def grade (m : Nat → V) (φ : Fm) : Grade :=
  cond (heredB m φ) .hereditary (cond (stableB m φ) .sound .untilVerification)

/-- **What a computed grade MEANS.** -/
theorem grade_hereditary {m : Nat → V} {φ : Fm} (h : grade m φ = .hereditary) : Hered m φ := by
  cases hh : heredB m φ with
  | true => exact heredB_sound hh
  | false =>
      unfold grade at h; rw [hh] at h
      cases hs : stableB m φ <;> (rw [hs] at h; cases h)

theorem grade_sound {m : Nat → V} {φ : Fm} (h : grade m φ = .sound) : Stable m φ ∧ ¬ Hered m φ := by
  cases hh : heredB m φ with
  | true => unfold grade at h; rw [hh] at h; cases h
  | false =>
      unfold grade at h; rw [hh] at h
      cases hs : stableB m φ with
      | true => exact ⟨stableB_sound hs, heredB_complete hh⟩
      | false => rw [hs] at h; cases h

theorem grade_until {m : Nat → V} {φ : Fm} (h : grade m φ = .untilVerification) : ¬ Stable m φ := by
  cases hs : stableB m φ with
  | false => exact stableB_complete hs
  | true =>
      unfold grade at h
      cases hh : heredB m φ <;> (rw [hh, hs] at h; cases h)

end ZGrade

#print axioms ZGrade.heredB_sound
#print axioms ZGrade.heredB_complete
#print axioms ZGrade.stableB_sound
#print axioms ZGrade.stableB_complete
#print axioms ZGrade.grade_hereditary
#print axioms ZGrade.grade_sound
#print axioms ZGrade.grade_until
#print axioms ZGrade.notStable_witness

#print axioms ZGrade.evalF_congr
