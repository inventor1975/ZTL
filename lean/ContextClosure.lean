import ZTL

/-!
# Context closure on the positive fragment — the bench's regularity, proved

`veraxis/context-closure-001/` measured, over an enumeration, that the kernel's
verdict under partial disclosure and completion-based context closure are NOT
the same property — `¬¬b` with `b` withheld is the minimal counterexample — but
that they coincide exactly where the withheld atom occurs under no negation.
That was 818 pairs of a finite census. This file proves the general statement
for the whole formula language.

THE TWO QUANTIFIERS, and why they differ. An undisclosed ground carries the
mark `Z`, and the kernel lifts each CONNECTIVE separately: `znot (znot Z) = T`.
Context closure instead substitutes a value for the ATOM and asks whether every
completion still yields `T`. Composition of lifts is not the lift of the
composition, so the two can part ways — and where a negation stands over the
withheld atom, they do.

WHAT IS PROVED HERE: for a formula in which the withheld atom occurs under no
negation, no antecedent and no exclusive-or, the two agree in both directions,
for every valuation and every formula — not on a sample.

    evalF v φ = T   ↔   (evalF v[a := T] φ = T  ∧  evalF v[a := F] φ = F → …)

read as: the kernel warrants the claim exactly when EVERY completion of the
withheld atom warrants it.

The proof runs through a monotonicity lemma, which is where the syntactic
condition does its work: on this fragment, replacing the withheld atom's `F`
reading by `T` can only preserve a warrant, never destroy one.

NOT A DISCOVERY OF NON-MONOTONICITY. The greedy register's non-monotonicity is
already a theorem of this corpus (`eager_and_not_monotone`,
`eager_not_not_monotone`), and the lazy register is already proved monotone
(`kleene_*_monotone`) — ZTL carries both and separates them by role: verdicts
greedy, self-reference lazy. What is new below is where that known
non-monotonicity damages context closure and where it provably does not.

BOUNDARY, restated so the theorem is not over-read: this is the UNRESTRICTED
completion boundary `B_⊤`. A declared boundary that admits fewer completions is
a separate object, and the kernel does not take it as an input — see the
bench's case 4. Nothing here decides which boundary is admissible.
-/

namespace V

/-- Does the atom occur anywhere in the formula? -/
def occurs (a : Nat) : Fm → Bool
  | .atom n => decide (n = a)
  | .top => false
  | .bot => false
  | .neg φ => occurs a φ
  | .conj φ ψ => occurs a φ || occurs a ψ
  | .disj φ ψ => occurs a φ || occurs a ψ
  | .imp φ ψ => occurs a φ || occurs a ψ
  | .xor φ ψ => occurs a φ || occurs a ψ
  | .xnor φ ψ => occurs a φ || occurs a ψ

/-- The syntactic fragment measured in the bench: the atom sits under no
negation, in no antecedent, and inside no xor/xnor. Those three positions are
exactly where a negation reaches the atom — in `xor`/`xnor` it does so through
the connective's own definition. -/
def negFree (a : Nat) : Fm → Bool
  | .atom _ => true
  | .top => true
  | .bot => true
  | .neg φ => !occurs a φ
  | .conj φ ψ => negFree a φ && negFree a ψ
  | .disj φ ψ => negFree a φ && negFree a ψ
  | .imp φ ψ => !occurs a φ && negFree a ψ
  | .xor φ ψ => !(occurs a φ || occurs a ψ)
  | .xnor φ ψ => !(occurs a φ || occurs a ψ)


/-! ## Boolean plumbing, proved by case split rather than by `simp`

`simp` and `by_cases` pull `propext` and `Classical.choice` into the term — a
known pit in this corpus. Everything below is `cases` + `noConfusion`, so the
whole file stands on the empty axiom list, like the rest of the kernel. -/

theorem orF {x y : Bool} (h : (x || y) = false) : x = false ∧ y = false := by
  cases x with
  | true => exact Bool.noConfusion h
  | false =>
      cases y with
      | true => exact Bool.noConfusion h
      | false => exact ⟨rfl, rfl⟩

theorem andT {x y : Bool} (h : (x && y) = true) : x = true ∧ y = true := by
  cases x with
  | false => exact Bool.noConfusion h
  | true =>
      cases y with
      | false => exact Bool.noConfusion h
      | true => exact ⟨rfl, rfl⟩

theorem notT {x : Bool} (h : (!x) = true) : x = false := by
  cases x with
  | true => exact Bool.noConfusion h
  | false => rfl

/-- Disclose one atom: the completion that reads the withheld ground as `x`. -/
def setA (a : Nat) (x : V) (v : Nat → V) : Nat → V :=
  fun n => if n = a then x else v n

theorem setA_self (a : Nat) (x : V) (v : Nat → V) : setA a x v a = x :=
  if_pos rfl

theorem setA_other {a n : Nat} (x : V) (v : Nat → V) (h : n ≠ a) :
    setA a x v n = v n :=
  if_neg h

/-! ## A formula that does not mention the atom cannot notice the completion -/

theorem eval_indep (a : Nat) (x : V) (v : Nat → V) :
    ∀ φ : Fm, occurs a φ = false → evalF (setA a x v) φ = evalF v φ := by
  intro φ
  induction φ with
  | atom n =>
      intro h
      have h' : decide (n = a) = false := h
      rw [evalF, evalF]
      exact setA_other x v (of_decide_eq_false h')
  | top => intro _; rfl
  | bot => intro _; rfl
  | neg φ ih => intro h; rw [evalF, evalF, ih h]
  | conj φ ψ ihφ ihψ =>
      intro h; rw [evalF, evalF, ihφ (orF h).1, ihψ (orF h).2]
  | disj φ ψ ihφ ihψ =>
      intro h; rw [evalF, evalF, ihφ (orF h).1, ihψ (orF h).2]
  | imp φ ψ ihφ ihψ =>
      intro h; rw [evalF, evalF, ihφ (orF h).1, ihψ (orF h).2]
  | xor φ ψ ihφ ihψ =>
      intro h; rw [evalF, evalF, ihφ (orF h).1, ihψ (orF h).2]
  | xnor φ ψ ihφ ihψ =>
      intro h; rw [evalF, evalF, ihφ (orF h).1, ihψ (orF h).2]

/-! ## Monotonicity — where the syntactic condition earns its keep

On the positive fragment, reading the withheld ground as `T` instead of `F`
can only preserve a warrant. This is the half that fails outside the fragment,
and it is why `¬¬b` breaks the coincidence. -/

theorem mono (a : Nat) (v : Nat → V) :
    ∀ φ : Fm, negFree a φ = true →
      evalF (setA a F v) φ = T → evalF (setA a T v) φ = T := by
  intro φ
  induction φ with
  | atom n =>
      intro _ h
      cases hd : decide (n = a) with
      | true =>
          have hn : n = a := of_decide_eq_true hd
          subst hn
          rw [evalF, setA_self] at h
          exact V.noConfusion h
      | false =>
          have hne := of_decide_eq_false hd
          rw [evalF, setA_other _ _ hne] at h
          rw [evalF, setA_other _ _ hne]
          exact h
  | top => intro _ h; exact h
  | bot => intro _ h; exact h
  | neg φ _ =>
      intro hnf h
      have ho : occurs a φ = false := notT hnf
      rw [evalF] at h ⊢
      rw [eval_indep a F v φ ho] at h
      rw [eval_indep a T v φ ho]
      exact h
  | conj φ ψ ihφ ihψ =>
      intro hnf h
      have hs := andT hnf
      rw [evalF] at h ⊢
      have hc := (cover_and_T _ _).mp h
      exact (cover_and_T _ _).mpr ⟨ihφ hs.1 hc.1, ihψ hs.2 hc.2⟩
  | disj φ ψ ihφ ihψ =>
      intro hnf h
      have hs := andT hnf
      rw [evalF] at h ⊢
      match (cover_or_T _ _).mp h with
      | Or.inl hl => exact (cover_or_T _ _).mpr (Or.inl (ihφ hs.1 hl))
      | Or.inr hr => exact (cover_or_T _ _).mpr (Or.inr (ihψ hs.2 hr))
  | imp φ ψ _ ihψ =>
      intro hnf h
      have hs := andT hnf
      have ho : occurs a φ = false := notT hs.1
      rw [evalF] at h ⊢
      match (cover_imp_T _ _).mp h with
      | Or.inl hl =>
          refine (cover_imp_T _ _).mpr (Or.inl ?_)
          rw [eval_indep a T v φ ho]
          rw [eval_indep a F v φ ho] at hl
          exact hl
      | Or.inr hr => exact (cover_imp_T _ _).mpr (Or.inr (ihψ hs.2 hr))
  | xor φ ψ _ _ =>
      intro hnf h
      have hs := orF (notT hnf)
      rw [evalF] at h ⊢
      rw [eval_indep a F v φ hs.1, eval_indep a F v ψ hs.2] at h
      rw [eval_indep a T v φ hs.1, eval_indep a T v ψ hs.2]
      exact h
  | xnor φ ψ _ _ =>
      intro hnf h
      have hs := orF (notT hnf)
      rw [evalF] at h ⊢
      rw [eval_indep a F v φ hs.1, eval_indep a F v ψ hs.2] at h
      rw [eval_indep a T v φ hs.1, eval_indep a T v ψ hs.2]
      exact h

/-! ## The theorem

For a withheld atom (`v a = Z`) occurring only positively, the kernel's verdict
and completion-based context closure decide the same question. -/

theorem closure_coincides (a : Nat) (v : Nat → V) (hv : v a = Z) :
    ∀ φ : Fm, negFree a φ = true →
      (evalF v φ = T ↔
        (evalF (setA a T v) φ = T ∧ evalF (setA a F v) φ = T)) := by
  intro φ
  induction φ with
  | atom n =>
      intro _
      cases hd : decide (n = a) with
      | true =>
          have hn : n = a := of_decide_eq_true hd
          subst hn
          rw [evalF, evalF, evalF, hv, setA_self, setA_self]
          exact ⟨fun h => V.noConfusion h, fun h => V.noConfusion h.2⟩
      | false =>
          have hne := of_decide_eq_false hd
          rw [evalF, evalF, evalF, setA_other _ _ hne, setA_other _ _ hne]
          exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | top => intro _; exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | bot => intro _; exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | neg φ _ =>
      intro hnf
      have ho : occurs a φ = false := notT hnf
      rw [evalF, evalF, evalF]
      rw [eval_indep a T v φ ho, eval_indep a F v φ ho]
      exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | conj φ ψ ihφ ihψ =>
      intro hnf
      have hs := andT hnf
      rw [evalF, evalF, evalF]
      constructor
      · intro h
        have hc := (cover_and_T _ _).mp h
        have hφ := (ihφ hs.1).mp hc.1
        have hψ := (ihψ hs.2).mp hc.2
        exact ⟨(cover_and_T _ _).mpr ⟨hφ.1, hψ.1⟩,
               (cover_and_T _ _).mpr ⟨hφ.2, hψ.2⟩⟩
      · intro h
        have hT := (cover_and_T _ _).mp h.1
        have hF := (cover_and_T _ _).mp h.2
        exact (cover_and_T _ _).mpr
          ⟨(ihφ hs.1).mpr ⟨hT.1, hF.1⟩, (ihψ hs.2).mpr ⟨hT.2, hF.2⟩⟩
  | disj φ ψ ihφ ihψ =>
      intro hnf
      have hs := andT hnf
      rw [evalF, evalF, evalF]
      constructor
      · intro h
        match (cover_or_T _ _).mp h with
        | Or.inl hl =>
            have hφ := (ihφ hs.1).mp hl
            exact ⟨(cover_or_T _ _).mpr (Or.inl hφ.1),
                   (cover_or_T _ _).mpr (Or.inl hφ.2)⟩
        | Or.inr hr =>
            have hψ := (ihψ hs.2).mp hr
            exact ⟨(cover_or_T _ _).mpr (Or.inr hψ.1),
                   (cover_or_T _ _).mpr (Or.inr hψ.2)⟩
      · intro h
        -- The F-completion binds; monotonicity carries it up to the T-one.
        match (cover_or_T _ _).mp h.2 with
        | Or.inl hl =>
            exact (cover_or_T _ _).mpr
              (Or.inl ((ihφ hs.1).mpr ⟨mono a v φ hs.1 hl, hl⟩))
        | Or.inr hr =>
            exact (cover_or_T _ _).mpr
              (Or.inr ((ihψ hs.2).mpr ⟨mono a v ψ hs.2 hr, hr⟩))
  | imp φ ψ _ ihψ =>
      intro hnf
      have hs := andT hnf
      have ho : occurs a φ = false := notT hs.1
      rw [evalF, evalF, evalF]
      rw [eval_indep a T v φ ho, eval_indep a F v φ ho]
      constructor
      · intro h
        match (cover_imp_T _ _).mp h with
        | Or.inl hl =>
            exact ⟨(cover_imp_T _ _).mpr (Or.inl hl),
                   (cover_imp_T _ _).mpr (Or.inl hl)⟩
        | Or.inr hr =>
            have hψ := (ihψ hs.2).mp hr
            exact ⟨(cover_imp_T _ _).mpr (Or.inr hψ.1),
                   (cover_imp_T _ _).mpr (Or.inr hψ.2)⟩
      · intro h
        match (cover_imp_T _ _).mp h.2 with
        | Or.inl hl => exact (cover_imp_T _ _).mpr (Or.inl hl)
        | Or.inr hr =>
            exact (cover_imp_T _ _).mpr
              (Or.inr ((ihψ hs.2).mpr ⟨mono a v ψ hs.2 hr, hr⟩))
  | xor φ ψ _ _ =>
      intro hnf
      have hs := orF (notT hnf)
      rw [evalF, evalF, evalF]
      rw [eval_indep a T v φ hs.1, eval_indep a T v ψ hs.2,
          eval_indep a F v φ hs.1, eval_indep a F v ψ hs.2]
      exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | xnor φ ψ _ _ =>
      intro hnf
      have hs := orF (notT hnf)
      rw [evalF, evalF, evalF]
      rw [eval_indep a T v φ hs.1, eval_indep a T v ψ hs.2,
          eval_indep a F v φ hs.1, eval_indep a F v ψ hs.2]
      exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

/-! ## The boundary of the theorem, as a theorem

Outside the fragment the coincidence fails, and the bench's minimal
counterexample is exactly this: `¬¬b` with `b` withheld. The kernel warrants
it; the completion `b := F` does not. -/

theorem outside_fragment_fails :
    ∃ (a : Nat) (v : Nat → V) (φ : Fm),
      v a = Z ∧ negFree a φ = false ∧
      evalF v φ = T ∧ evalF (setA a F v) φ ≠ T := by
  refine ⟨0, (fun _ => Z), .neg (.neg (.atom 0)), rfl, by decide, by decide, ?_⟩
  intro h
  rw [evalF, evalF, evalF, setA_self] at h
  exact V.noConfusion h

#print axioms eval_indep
#print axioms mono
#print axioms closure_coincides
#print axioms outside_fragment_fails

end V
