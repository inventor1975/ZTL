import ZTL
import ZAlgebra
import NoGift
/-! # ZComplete — every two-valued function of the atoms is a ZTL formula. Zero axioms.

`ZAlgebra.unary_complete` proved it for one atom; the binary case (514 = 2 + 512) was measured in Python.
Here it is for any finite list of atoms (2026-10-29): a function `g` of a valuation that depends only on the
atoms `xs` and answers T or F is the value of the J-DNF built over `xs`. Hence every judgement the judge makes
about a fixed formula — "is it earned", "does it survive every verification", "is it settled" — is itself the
value of a ZTL formula: the judge is not code over ZTL but ZTL speaking about itself. Strong Kleene cannot do
this even for one atom (`ZDirty.kleene_cannot_jump`). Expressible is not cheap: the J-DNF has 3^|xs| leaves.
-/

namespace V
namespace Cpl

def toV (b : Bool) : V := match b with | true => T | false => F
def constF (b : Bool) : Fm := match b with | true => .top | false => .bot

theorem evalF_constF (v : Nat → V) : ∀ b : Bool, evalF v (constF b) = toV b
  | true => rfl
  | false => rfl

/-- v with the atom x set to c -/
def upd (v : Nat → V) (x : Nat) (c : V) : Nat → V := fun n => if n = x then c else v n

/-- v and w agree on the atoms xs -/
def agree : List Nat → (Nat → V) → (Nat → V) → Prop
  | [], _, _ => True
  | y :: ys, v, w => v y = w y ∧ agree ys v w

/-- g depends only on the atoms xs -/
def Dep (xs : List Nat) (g : (Nat → V) → Bool) : Prop := ∀ v w, agree xs v w → g v = g w

theorem upd_at (v : Nat → V) (x : Nat) (c : V) : upd v x c x = c := if_pos rfl

theorem agree_upd (x : Nat) (c : V) : ∀ (ys : List Nat) (v w : Nat → V),
    agree ys v w → agree ys (upd v x c) (upd w x c)
  | [], _, _, _ => trivial
  | y :: ys, v, w, ⟨hy, hys⟩ => by
      refine ⟨?_, agree_upd x c ys v w hys⟩
      show (if y = x then c else v y) = (if y = x then c else w y)
      match Nat.decEq y x with
      | isTrue h => rw [if_pos h, if_pos h]
      | isFalse h => rw [if_neg h, if_neg h]; exact hy

theorem agree_upd_self (x : Nat) (v : Nat → V) : ∀ ys : List Nat, agree ys (upd v x (v x)) v
  | [] => trivial
  | y :: ys => by
      refine ⟨?_, agree_upd_self x v ys⟩
      show (if y = x then v x else v y) = v y
      match Nat.decEq y x with
      | isTrue h => rw [if_pos h, h]
      | isFalse h => rw [if_neg h]

/-- the three indicator formulas: x is T, x is F, x is Z -/
def jTF (x : Nat) : Fm := .conj (.atom x) (.atom x)
def jFF (x : Nat) : Fm := .conj (.neg (.atom x)) (.neg (.atom x))
def jZF (x : Nat) : Fm := .neg (.xnor (.atom x) (.atom x))

/-- The J-DNF of g over xs. -/
def dnf : List Nat → ((Nat → V) → Bool) → Fm
  | [], g => constF (g (fun _ => Z))
  | x :: xs, g =>
      .disj (.disj (.conj (jTF x) (dnf xs (fun v => g (upd v x T))))
                   (.conj (jFF x) (dnf xs (fun v => g (upd v x F)))))
            (.conj (jZF x) (dnf xs (fun v => g (upd v x Z))))

theorem select : ∀ (x : V) (a b c : Bool),
    zor (zor (zand (zand x x) (toV a)) (zand (zand (znot x) (znot x)) (toV b))) (zand (znot (zxnor x x)) (toV c))
      = (match x with | T => toV a | F => toV b | Z => toV c) := by decide

theorem dep_upd (x : Nat) (c : V) (xs : List Nat) (g : (Nat → V) → Bool) (h : Dep (x :: xs) g) :
    Dep xs (fun v => g (upd v x c)) := fun v w hvw =>
  h _ _ ⟨by rw [upd_at, upd_at], agree_upd x c xs v w hvw⟩

theorem dep_self (x : Nat) (xs : List Nat) (g : (Nat → V) → Bool) (h : Dep (x :: xs) g) (v : Nat → V) :
    g (upd v x (v x)) = g v :=
  h _ _ ⟨upd_at v x (v x), agree_upd_self x v xs⟩

/-- **Every two-valued function of finitely many atoms is the value of a ZTL formula** (its J-DNF). -/
theorem dnf_spec : ∀ (xs : List Nat) (g : (Nat → V) → Bool), Dep xs g →
    ∀ v, evalF v (dnf xs g) = toV (g v)
  | [], g, h, v => by
      show evalF v (constF (g (fun _ => Z))) = toV (g v)
      rw [evalF_constF, h (fun _ => Z) v trivial]
  | x :: xs, g, h, v => by
      have eT := dnf_spec xs (fun w => g (upd w x T)) (dep_upd x T xs g h) v
      have eF := dnf_spec xs (fun w => g (upd w x F)) (dep_upd x F xs g h) v
      have eZ := dnf_spec xs (fun w => g (upd w x Z)) (dep_upd x Z xs g h) v
      show zor (zor (zand (zand (v x) (v x)) (evalF v (dnf xs (fun w => g (upd w x T)))))
                    (zand (zand (znot (v x)) (znot (v x))) (evalF v (dnf xs (fun w => g (upd w x F))))))
               (zand (znot (zxnor (v x) (v x))) (evalF v (dnf xs (fun w => g (upd w x Z))))) = toV (g v)
      rw [eT, eF, eZ, select]
      have hs := dep_self x xs g h v
      revert hs
      cases v x <;> intro hs <;> rw [hs]

theorem ztl_expressively_complete (xs : List Nat) (g : (Nat → V) → Bool) (h : Dep xs g) :
    ∃ φ : Fm, ∀ v, evalF v φ = toV (g v) :=
  ⟨dnf xs g, dnf_spec xs g h⟩

/-! ## Craig interpolation (2026-10-29)
If φ ⊨ ψ, there is χ whose atoms all occur in both, with φ ⊨ χ and χ ⊨ ψ. The interpolant is the J-DNF, over
the shared atoms, of "some value of φ's private atoms makes φ true" — expressible because ZTL expresses every
two-valued function (`dnf_spec`). With no shared atom it is a constant, ⊤ or ⊥. -/

def memB (n : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => decide (n = y) || memB n ys

def atomsL : Fm → List Nat
  | .atom n => [n]
  | .top => []
  | .bot => []
  | .neg φ => atomsL φ
  | .conj φ ψ => atomsL φ ++ atomsL ψ
  | .disj φ ψ => atomsL φ ++ atomsL ψ
  | .imp φ ψ => atomsL φ ++ atomsL ψ
  | .xor φ ψ => atomsL φ ++ atomsL ψ
  | .xnor φ ψ => atomsL φ ++ atomsL ψ

def filterB (p : Nat → Bool) : List Nat → List Nat
  | [] => []
  | y :: ys => match p y with | true => y :: filterB p ys | false => filterB p ys

theorem or3 : ∀ a b c : Bool, (a || b || c) = true → a = true ∨ b = true ∨ c = true := by decide
theorem or_left' : ∀ a b : Bool, a = true → (a || b) = true := by decide
theorem or_right' : ∀ a b : Bool, b = true → (a || b) = true := by decide

theorem memB_append (n : Nat) : ∀ (l m : List Nat), memB n l = true ∨ memB n m = true → memB n (l ++ m) = true
  | [], m, h => by
      cases h with
      | inl h => exact nomatch h
      | inr h => exact h
  | y :: ys, m, h => by
      show (decide (n = y) || memB n (ys ++ m)) = true
      cases h with
      | inl h =>
          have h' : (decide (n = y) || memB n ys) = true := h
          cases hd : decide (n = y) with
          | true => rfl
          | false =>
              rw [hd] at h'
              exact or_right' _ _ (memB_append n ys m (Or.inl h'))
      | inr h => exact or_right' _ _ (memB_append n ys m (Or.inr h))

theorem bin_to_memB (n : Nat) (φ ψ : Fm) (ihφ : occurs n φ = true → memB n (atomsL φ) = true)
    (ihψ : occurs n ψ = true → memB n (atomsL ψ) = true) (h : (occurs n φ || occurs n ψ) = true) :
    memB n (atomsL φ ++ atomsL ψ) = true := by
  apply memB_append
  cases hφ : occurs n φ with
  | true => exact Or.inl (ihφ hφ)
  | false => rw [hφ] at h; exact Or.inr (ihψ h)

theorem occurs_memB (n : Nat) (φ : Fm) : occurs n φ = true → memB n (atomsL φ) = true := by
  induction φ with
  | atom m =>
      intro h
      have e : m = n := of_decide_eq_true h
      show (decide (n = m) || false) = true
      rw [e]; exact or_left' _ _ (decide_eq_true rfl)
  | top => intro h; exact nomatch h
  | bot => intro h; exact nomatch h
  | neg φ ih => exact ih
  | conj φ ψ ih1 ih2 => exact bin_to_memB n φ ψ ih1 ih2
  | disj φ ψ ih1 ih2 => exact bin_to_memB n φ ψ ih1 ih2
  | imp φ ψ ih1 ih2 => exact bin_to_memB n φ ψ ih1 ih2
  | xor φ ψ ih1 ih2 => exact bin_to_memB n φ ψ ih1 ih2
  | xnor φ ψ ih1 ih2 => exact bin_to_memB n φ ψ ih1 ih2

theorem memB_split (n : Nat) : ∀ (l m : List Nat), memB n (l ++ m) = true → memB n l = true ∨ memB n m = true
  | [], m, h => Or.inr h
  | y :: ys, m, h => by
      have h' : (decide (n = y) || memB n (ys ++ m)) = true := h
      cases hd : decide (n = y) with
      | true => exact Or.inl (by show (decide (n = y) || memB n ys) = true; rw [hd]; rfl)
      | false =>
          rw [hd] at h'
          cases memB_split n ys m h' with
          | inl h => exact Or.inl (by show (decide (n = y) || memB n ys) = true; rw [hd]; exact h)
          | inr h => exact Or.inr h

theorem memB_to_bin (n : Nat) (φ ψ : Fm) (ihφ : memB n (atomsL φ) = true → occurs n φ = true)
    (ihψ : memB n (atomsL ψ) = true → occurs n ψ = true) (h : memB n (atomsL φ ++ atomsL ψ) = true) :
    (occurs n φ || occurs n ψ) = true := by
  cases memB_split n (atomsL φ) (atomsL ψ) h with
  | inl h => exact or_left' _ _ (ihφ h)
  | inr h => exact or_right' _ _ (ihψ h)

theorem atomsL_occurs (n : Nat) (φ : Fm) : memB n (atomsL φ) = true → occurs n φ = true := by
  induction φ with
  | atom m =>
      intro h
      have h' : (decide (n = m) || false) = true := h
      cases hd : decide (n = m) with
      | true => have e : n = m := of_decide_eq_true hd; rw [e]; exact decide_eq_true rfl
      | false => rw [hd] at h'; exact nomatch h'
  | top => intro h; exact nomatch h
  | bot => intro h; exact nomatch h
  | neg φ ih => exact ih
  | conj φ ψ ih1 ih2 => exact memB_to_bin n φ ψ ih1 ih2
  | disj φ ψ ih1 ih2 => exact memB_to_bin n φ ψ ih1 ih2
  | imp φ ψ ih1 ih2 => exact memB_to_bin n φ ψ ih1 ih2
  | xor φ ψ ih1 ih2 => exact memB_to_bin n φ ψ ih1 ih2
  | xnor φ ψ ih1 ih2 => exact memB_to_bin n φ ψ ih1 ih2

theorem filter_sub (n : Nat) (p : Nat → Bool) : ∀ l : List Nat, memB n (filterB p l) = true → memB n l = true
  | [], h => h
  | y :: ys, h => by
      revert h
      show memB n (match p y with | true => y :: filterB p ys | false => filterB p ys) = true → memB n (y :: ys) = true
      cases p y with
      | true =>
          intro h
          have h' : (decide (n = y) || memB n (filterB p ys)) = true := h
          show (decide (n = y) || memB n ys) = true
          cases hd : decide (n = y) with
          | true => rfl
          | false => rw [hd] at h'; exact filter_sub n p ys h'
      | false =>
          intro h
          show (decide (n = y) || memB n ys) = true
          exact or_right' _ _ (filter_sub n p ys h)

theorem memB_filter (n : Nat) (p : Nat → Bool) : ∀ l : List Nat,
    memB n l = true → p n = true → memB n (filterB p l) = true
  | [], h, _ => nomatch h
  | y :: ys, h, hp => by
      have h' : (decide (n = y) || memB n ys) = true := h
      cases hd : decide (n = y) with
      | true =>
          have e : n = y := of_decide_eq_true hd
          show memB n (match p y with | true => y :: filterB p ys | false => filterB p ys) = true
          rw [← e, hp]
          show (decide (n = n) || memB n (filterB p ys)) = true
          exact or_left' _ _ (decide_eq_true rfl)
      | false =>
          rw [hd] at h'
          have ih := memB_filter n p ys h' hp
          show memB n (match p y with | true => y :: filterB p ys | false => filterB p ys) = true
          cases p y with
          | true => exact or_right' _ _ ih
          | false => exact ih

theorem filter_sound (n : Nat) (p : Nat → Bool) : ∀ l : List Nat, memB n (filterB p l) = true → p n = true
  | [], h => nomatch h
  | y :: ys, h => by
      revert h
      show memB n (match p y with | true => y :: filterB p ys | false => filterB p ys) = true → p n = true
      cases hy : p y with
      | true =>
          intro h
          have h' : (decide (n = y) || memB n (filterB p ys)) = true := h
          cases hd : decide (n = y) with
          | true => have e : n = y := of_decide_eq_true hd; rw [e]; exact hy
          | false => rw [hd] at h'; exact filter_sound n p ys h'
      | false => exact filter_sound n p ys

theorem agree_mem (n : Nat) : ∀ (zs : List Nat) (v w : Nat → V), agree zs v w → memB n zs = true → v n = w n
  | [], _, _, _, h => nomatch h
  | z :: zs, v, w, ⟨hz, hzs⟩, h => by
      have h' : (decide (n = z) || memB n zs) = true := h
      cases hd : decide (n = z) with
      | true => have e : n = z := of_decide_eq_true hd; rw [e]; exact hz
      | false => rw [hd] at h'; exact agree_mem n zs v w hzs h'

/-- try every value of the atoms ys, starting from v -/
def exE : List Nat → (Nat → V) → ((Nat → V) → Bool) → Bool
  | [], v, P => P v
  | y :: ys, v, P => exE ys (upd v y T) P || exE ys (upd v y F) P || exE ys (upd v y Z) P

theorem exE_out (P : (Nat → V) → Bool) : ∀ (ys : List Nat) (v : Nat → V), exE ys v P = true →
    ∃ w, P w = true ∧ ∀ n, memB n ys = false → w n = v n
  | [], v, h => ⟨v, h, fun _ _ => rfl⟩
  | y :: ys, v, h => by
      have pick : ∀ c : V, exE ys (upd v y c) P = true → ∃ w, P w = true ∧ ∀ n, memB n (y :: ys) = false → w n = v n := by
        intro c hc
        obtain ⟨w, hw, hagree⟩ := exE_out P ys (upd v y c) hc
        refine ⟨w, hw, fun n hn => ?_⟩
        have hn' : (decide (n = y) || memB n ys) = false := hn
        cases hd : decide (n = y) with
        | true => rw [hd] at hn'; exact nomatch hn'
        | false =>
            rw [hd] at hn'
            have ne : ¬ n = y := of_decide_eq_false hd
            rw [hagree n hn']
            show (if n = y then c else v n) = v n
            rw [if_neg ne]
      cases or3 _ _ _ h with
      | inl h => exact pick T h
      | inr h => cases h with
        | inl h => exact pick F h
        | inr h => exact pick Z h

theorem exE_in (P : (Nat → V) → Bool) (hP : ∀ v w, (∀ n, v n = w n) → P v = P w) :
    ∀ (ys : List Nat) (v : Nat → V), P v = true → exE ys v P = true
  | [], _, h => h
  | y :: ys, v, h => by
      have hself : P (upd v y (v y)) = true := by
        rw [hP (upd v y (v y)) v (fun n => by
          show (if n = y then v y else v n) = v n
          match Nat.decEq n y with
          | isTrue e => rw [if_pos e, e]
          | isFalse e => rw [if_neg e])]
        exact h
      have ih := exE_in P hP ys _ hself
      show (exE ys (upd v y T) P || exE ys (upd v y F) P || exE ys (upd v y Z) P) = true
      revert ih
      cases v y with
      | T => intro ih; exact or_left' _ _ (or_left' _ _ ih)
      | F => intro ih; exact or_left' _ _ (or_right' _ _ ih)
      | Z => intro ih; exact or_right' _ _ ih

theorem exE_dep (P : (Nat → V) → Bool) (S : Nat → Bool)
    (hP : ∀ v w, (∀ n, S n = true → v n = w n) → P v = P w) :
    ∀ (ys : List Nat) (v w : Nat → V), (∀ n, S n = true → memB n ys = false → v n = w n) →
      exE ys v P = exE ys w P
  | [], v, w, h => hP v w (fun n hn => h n hn rfl)
  | y :: ys, v, w, h => by
      have step : ∀ c : V, exE ys (upd v y c) P = exE ys (upd w y c) P := by
        intro c
        apply exE_dep P S hP ys
        intro n hn hm
        show (if n = y then c else v n) = (if n = y then c else w n)
        match Nat.decEq n y with
        | isTrue e => rw [if_pos e, if_pos e]
        | isFalse e =>
            rw [if_neg e, if_neg e]
            apply h n hn
            show (decide (n = y) || memB n ys) = false
            rw [decide_eq_false e, hm]; rfl
      show (exE ys (upd v y T) P || exE ys (upd v y F) P || exE ys (upd v y Z) P) =
           (exE ys (upd w y T) P || exE ys (upd w y F) P || exE ys (upd w y Z) P)
      rw [step T, step F, step Z]

theorem dnf_atoms (n : Nat) : ∀ (zs : List Nat) (g : (Nat → V) → Bool), occurs n (dnf zs g) = true → memB n zs = true
  | [], g, h => by
      revert h
      show occurs n (constF (g (fun _ => Z))) = true → _
      cases g (fun _ => Z) <;> intro h <;> exact nomatch h
  | x :: xs, g, h => by
      have hx : ∀ f : Fm, (occurs n f || occurs n f) = true → occurs n f = true := by
        intro f hf; cases hof : occurs n f with
        | true => rfl
        | false => rw [hof] at hf; exact nomatch hf
      have atx : occurs n (.atom x) = true → memB n (x :: xs) = true := by
        intro ha
        have e : x = n := of_decide_eq_true ha
        show (decide (n = x) || memB n xs) = true
        rw [e]; exact or_left' _ _ (decide_eq_true rfl)
      have tail : ∀ c : V, occurs n (dnf xs (fun v => g (upd v x c))) = true → memB n (x :: xs) = true := by
        intro c hc
        exact or_right' _ _ (dnf_atoms n xs _ hc)
      have h' : ((((occurs n (.atom x) || occurs n (.atom x)) || occurs n (dnf xs (fun v => g (upd v x T)))) ||
                 ((occurs n (.atom x) || occurs n (.atom x)) || occurs n (dnf xs (fun v => g (upd v x F))))) ||
                ((occurs n (.atom x) || occurs n (.atom x)) || occurs n (dnf xs (fun v => g (upd v x Z))))) = true := h
      cases ha : occurs n (.atom x) with
      | true => exact atx ha
      | false =>
          rw [ha] at h'
          revert h'
          cases h1 : occurs n (dnf xs (fun v => g (upd v x T))) with
          | true => intro _; exact tail T h1
          | false =>
            cases h2 : occurs n (dnf xs (fun v => g (upd v x F))) with
            | true => intro _; exact tail F h2
            | false =>
              cases h3 : occurs n (dnf xs (fun v => g (upd v x Z))) with
              | true => intro _; exact tail Z h3
              | false => intro h'; exact nomatch h'

def isTB (x : V) : Bool := match x with | T => true | F => false | Z => false
theorem isTB_true : ∀ x : V, isTB x = true → x = T := by decide
theorem isTB_of_T : ∀ x : V, x = T → isTB x = true := by decide
theorem toV_T : ∀ b : Bool, toV b = T → b = true := by decide

/-- **Craig interpolation for ZTL.** -/
theorem ztl_interpolation (φ ψ : Fm) (hent : ∀ v, evalF v φ = T → evalF v ψ = T) :
    ∃ χ : Fm, (∀ n, occurs n χ = true → occurs n φ = true ∧ occurs n ψ = true) ∧
      (∀ v, evalF v φ = T → evalF v χ = T) ∧ (∀ v, evalF v χ = T → evalF v ψ = T) := by
  let ys := filterB (fun n => !occurs n ψ) (atomsL φ)
  let zs := filterB (fun n => occurs n ψ) (atomsL φ)
  let P : (Nat → V) → Bool := fun w => isTB (evalF w φ)
  let g : (Nat → V) → Bool := fun v => exE ys v P
  have hPdep : ∀ v w, (∀ n, occurs n φ = true → v n = w n) → P v = P w := fun v w h => by
    show isTB (evalF v φ) = isTB (evalF w φ)
    rw [evalF_congr v w φ h]
  have hdep : Dep zs g := by
    intro v w hvw
    apply exE_dep P (fun n => occurs n φ) hPdep ys v w
    intro n hn hm
    apply agree_mem n zs v w hvw
    apply memB_filter n _ _ (occurs_memB n φ hn)
    cases hq : occurs n ψ with
    | true => rfl
    | false =>
        have : memB n ys = true := memB_filter n _ _ (occurs_memB n φ hn) (by show (!occurs n ψ) = true; rw [hq]; rfl)
        rw [hm] at this; exact nomatch this
  refine ⟨dnf zs g, fun n hn => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have hz := dnf_atoms n zs g hn
    have hq : occurs n ψ = true := filter_sound n _ _ hz
    refine ⟨?_, hq⟩
    -- an atom of zs is an atom of φ: zs is filtered from atomsL φ, and atomsL lists only occurring atoms
    exact atomsL_occurs n φ (filter_sub n _ _ hz)
  · rw [dnf_spec zs g hdep v]
    have : g v = true := exE_in P (fun v w h => by
        show isTB (evalF v φ) = isTB (evalF w φ)
        rw [evalF_congr v w φ (fun n _ => h n)]) ys v (isTB_of_T _ hv)
    rw [this]; rfl
  · rw [dnf_spec zs g hdep v] at hv
    obtain ⟨w, hw, hoff⟩ := exE_out P ys v (toV_T _ hv)
    have hψw := hent w (isTB_true _ hw)
    rw [evalF_congr v w ψ (fun n hn => by
      have hm : memB n ys = false := by
        cases hmy : memB n ys with
        | false => rfl
        | true =>
            have := filter_sound n _ _ hmy
            have h2 : (!occurs n ψ) = true := this
            rw [hn] at h2; exact nomatch h2
      exact (hoff n hm).symm)]
    exact hψw

end Cpl
end V

#print axioms V.Cpl.evalF_constF
#print axioms V.Cpl.upd_at
#print axioms V.Cpl.agree_upd
#print axioms V.Cpl.agree_upd_self
#print axioms V.Cpl.select
#print axioms V.Cpl.dep_upd
#print axioms V.Cpl.dep_self
#print axioms V.Cpl.dnf_spec
#print axioms V.Cpl.ztl_expressively_complete
#print axioms V.Cpl.exE_out
#print axioms V.Cpl.exE_in
#print axioms V.Cpl.exE_dep
#print axioms V.Cpl.dnf_atoms
#print axioms V.Cpl.ztl_interpolation
