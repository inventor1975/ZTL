import ContextClosure

/-!
# The gift-free fragment: where a greedy T cannot be unearned. Zero axioms.

`Linear.linear_no_loss` bounds the LOSS: at multiplicity ≤ 1 no truth is lost.
This file bounds the GIFT, which is the dangerous half. The collapse `¬Z = F`
hands out verdicts that were never earned — measured, 2744 of them against 1446
honest verdicts killed — and an unearned T is indistinguishable from an earned
one, where a refusal at least announces itself.

WHAT IS PROVED. If every unverified atom of a claim stands under no negation,
then a greedy T survives every refinement of the marks — every subset of them
verified to any classical values. The machine cannot grant on that fragment.

    posMarks v φ  :  ∀ n, v n = Z → negFree n φ = true
    refines v w   :  ∀ n, v n ≠ Z → w n = v n        (marks may be filled, or not)

    no_gift       :  posMarks v φ → refines v w → evalF v φ = T → evalF w φ = T

`ContextClosure.closure_coincides` is the one-atom case of this and was proved
first; what is added is that the property survives all marks at once and all
PARTIAL refinements, which is what the warranty grade of §19 actually asks for.

ONLY `T` IS PROTECTED, and that is not an oversight — `p ∧ p` with `p` marked is
greedily F, sits inside the fragment, and revives at `p := T`. Measured: 950 of
1700 in-fragment F cells are revocable. The asymmetry is the point. An unearned
verdict is the danger; a refusal that later turns into a verdict is inquiry
working.

THE FRAGMENT IS SUFFICIENT AND NARROW, and the second half must be said as
loudly as the first. Measured over 323,530 cells (exhaustive depth 2 over two
atoms, plus random depth 5 over three and depth 6 over four): zero gifts inside
the fragment, and **66% / 97% / 99%** of the honest hereditary verdicts sit
OUTSIDE it, the share rising with depth. So this is a guarantee one can build
on, not a classification of safety: outside the fragment a verdict may still be
perfectly sound, and usually is. `outside_fragment_fails` and
`no_syntactic_characterisation` in `ContextClosure` say why no purely syntactic
test can be exact here.

MEASURED FIRST, predictions frozen in `lab/nogift/PREDICTIONS.md` before the
bench existed; all five held, including the deliberately weak P5.
-/

namespace V

theorem evalF_congr (v w : Nat → V) :
    ∀ φ : Fm, (∀ n, occurs n φ = true → v n = w n) → evalF v φ = evalF w φ := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      exact h n (by show decide (n = n) = true; exact decide_eq_true rfl)
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih =>
      intro h
      show znot (evalF v φ) = znot (evalF w φ)
      rw [ih (fun n hn => h n hn)]
  | conj φ ψ ihφ ihψ =>
      intro h
      show zand (evalF v φ) (evalF v ψ) = zand (evalF w φ) (evalF w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | disj φ ψ ihφ ihψ =>
      intro h
      show zor (evalF v φ) (evalF v ψ) = zor (evalF w φ) (evalF w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | imp φ ψ ihφ ihψ =>
      intro h
      show zimp (evalF v φ) (evalF v ψ) = zimp (evalF w φ) (evalF w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | xor φ ψ ihφ ihψ =>
      intro h
      show zxor (evalF v φ) (evalF v ψ) = zxor (evalF w φ) (evalF w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]
  | xnor φ ψ ihφ ihψ =>
      intro h
      show zxnor (evalF v φ) (evalF v ψ) = zxnor (evalF w φ) (evalF w ψ)
      rw [ihφ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn]; rfl)),
          ihψ (fun n hn => h n (by show (occurs n φ || occurs n ψ) = true; rw [hn];
                                   cases occurs n φ <;> rfl))]

/-- Atoms nobody marked cross a refinement unchanged, so a subformula holding no
marked atom keeps its value. -/
theorem frozen (v w : Nat → V) (φ : Fm) (hr : ∀ n, v n ≠ Z → w n = v n)
    (hno : ∀ n, v n = Z → occurs n φ = false) : evalF w φ = evalF v φ := by
  apply evalF_congr
  intro n hn
  have key : v n = Z ∨ v n ≠ Z := by
    cases hd : decide (v n = Z) with
    | true => exact Or.inl (of_decide_eq_true hd)
    | false => exact Or.inr (of_decide_eq_false hd)
  cases key with
  | inl hz => exact absurd hn (by rw [hno n hz]; intro k; exact Bool.noConfusion k)
  | inr hnz => exact hr n hnz

/-! ## When a greedy connective answers `T`, which branches had to -/

theorem zand_T {a b : V} (h : zand a b = T) : a = T ∧ b = T := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem zor_T {a b : V} (h : zor a b = T) : a = T ∨ b = T := by
  cases a <;> cases b <;> first
    | exact Or.inl rfl | exact Or.inr rfl | exact absurd h (by decide)

theorem zimp_T {a b : V} (h : zimp a b = T) : a = F ∨ b = T := by
  cases a <;> cases b <;> first
    | exact Or.inl rfl | exact Or.inr rfl | exact absurd h (by decide)

def posMarks (v : Nat → V) (φ : Fm) : Prop := ∀ n, v n = Z → negFree n φ = true

def refines (v w : Nat → V) : Prop := ∀ n, v n ≠ Z → w n = v n

/-- **No gift.** Where every unverified atom stands under no negation, a greedy
`T` survives every refinement of the marks. -/
theorem no_gift (v w : Nat → V) (hr : refines v w) :
    ∀ φ : Fm, posMarks v φ → evalF v φ = T → evalF w φ = T := by
  intro φ
  induction φ with
  | atom n =>
      intro _ hT
      have hv : v n = T := hT
      have hnz : v n ≠ Z := by rw [hv]; intro k; exact V.noConfusion k
      show w n = T
      rw [hr n hnz]; exact hv
  | top => intro _ _; rfl
  | bot => intro _ hT; exact absurd hT (by intro k; exact V.noConfusion k)
  | neg φ _ =>
      intro hp hT
      have hno : ∀ n, v n = Z → occurs n φ = false := fun n hn => notT (hp n hn)
      show znot (evalF w φ) = T
      rw [frozen v w φ hr hno]; exact hT
  | conj φ ψ ihφ ihψ =>
      intro hp hT
      obtain ⟨h1, h2⟩ := zand_T hT
      show zand (evalF w φ) (evalF w ψ) = T
      rw [ihφ (fun n hn => (andT (hp n hn)).1) h1,
          ihψ (fun n hn => (andT (hp n hn)).2) h2]
      rfl
  | disj φ ψ ihφ ihψ =>
      intro hp hT
      show zor (evalF w φ) (evalF w ψ) = T
      cases zor_T hT with
      | inl h1 =>
          rw [ihφ (fun n hn => (andT (hp n hn)).1) h1]
          cases evalF w ψ <;> rfl
      | inr h2 =>
          rw [ihψ (fun n hn => (andT (hp n hn)).2) h2]
          cases evalF w φ <;> rfl
  | imp φ ψ _ ihψ =>
      intro hp hT
      have hfr : evalF w φ = evalF v φ :=
        frozen v w φ hr (fun n hn => notT (andT (hp n hn)).1)
      show zimp (evalF w φ) (evalF w ψ) = T
      rw [hfr]
      cases zimp_T hT with
      | inl h1 => rw [h1]; cases evalF w ψ <;> rfl
      | inr h2 =>
          rw [ihψ (fun n hn => (andT (hp n hn)).2) h2]
          cases evalF v φ <;> rfl
  | xor φ ψ _ _ =>
      intro hp hT
      have hno : ∀ n, v n = Z → occurs n (Fm.xor φ ψ) = false := fun n hn => notT (hp n hn)
      rw [frozen v w (Fm.xor φ ψ) hr hno]; exact hT
  | xnor φ ψ _ _ =>
      intro hp hT
      have hno : ∀ n, v n = Z → occurs n (Fm.xnor φ ψ) = false := fun n hn => notT (hp n hn)
      rw [frozen v w (Fm.xnor φ ψ) hr hno]; exact hT

/-! ## Two boundaries, so that "sufficient" is not read as "necessary"

Both are proved rather than asserted, because a one-sided guarantee invites
exactly the two misreadings below. -/

/-- **Only `T` is protected.** `p ∧ p` sits inside the fragment, is greedily `F`,
and revives on verification. A refusal that later becomes a verdict is inquiry
working; an unearned verdict is the danger, and only that one is fenced. -/
theorem F_is_not_protected :
    posMarks (fun _ => Z) (Fm.conj (Fm.atom 0) (Fm.atom 0))
  ∧ evalF (fun _ => Z) (Fm.conj (Fm.atom 0) (Fm.atom 0)) = F
  ∧ refines (fun _ => Z) (fun _ => T)
  ∧ evalF (fun _ => T) (Fm.conj (Fm.atom 0) (Fm.atom 0)) = T :=
  ⟨fun _ _ => rfl, rfl, fun _ h => absurd rfl h, rfl⟩

/-- The valuation of the witness below: atom 0 unverified, everything else
verified true. -/
def vGap : Nat → V
  | 0 => Z
  | _ => T

/-- **The fragment is sufficient, not necessary.** `p → q` with `p` unverified
and `q` verified true is OUTSIDE the fragment — the mark stands in an antecedent
— and yet no refinement can move it. Measured, this is the common case, not the
exception: 66% of hereditary verdicts at depth 2 lie outside the fragment, 97%
at depth 5, 99% at depth 6. Outside is not unsafe; it is merely unguaranteed. -/
theorem fragment_is_not_necessary :
    ¬ posMarks vGap (Fm.imp (Fm.atom 0) (Fm.atom 1))
  ∧ evalF vGap (Fm.imp (Fm.atom 0) (Fm.atom 1)) = T
  ∧ ∀ w, refines vGap w → evalF w (Fm.imp (Fm.atom 0) (Fm.atom 1)) = T := by
  refine ⟨?_, rfl, ?_⟩
  · intro h
    exact absurd (h 0 rfl) (by decide)
  · intro w hr
    have h1 : w 1 = T := hr 1 (by intro k; exact V.noConfusion k)
    show zimp (w 0) (w 1) = T
    rw [h1]; cases w 0 <;> rfl

#print axioms F_is_not_protected
#print axioms fragment_is_not_necessary

#print axioms evalF_congr
#print axioms frozen
#print axioms zand_T
#print axioms no_gift

end V
