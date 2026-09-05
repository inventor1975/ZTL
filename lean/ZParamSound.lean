/-
  ZParamSound.lean — E38: THE γ/δ RULES, AND WHERE THEIR SOUNDNESS SPLITS.

  WHY THIS FILE EXISTS. §27 asks for a Lean port of the parameter tableaux of
  §6, where soundness is MEASURED (re-checked by total enumeration over finite
  domains) and completeness is "argued, not measured". Before attempting the
  port I predicted that its completeness half would land on the classical
  tier. A prediction is not a fact, and the curator said so. This file
  therefore does not predict: it MEASURES the part that can be measured
  today — the soundness of the four quantifier rules themselves — and reports
  where the axiom list breaks.

  THE FOUR RULES (§6):

      γ (reusable, every parameter):   T:∀xφ → T:φ(c)     F:∃xφ → N:φ(c)
      δ (fresh parameter, once):       T:∃xφ → T:φ(c*)    F:∀xφ → N:φ(c*)

  WHAT IS MEASURED. Three of the four are sound on the EMPTY axiom list.
  The fourth — `F:∀xφ → N:φ(c*)` — is not proved here without `Classical`,
  and the reason is exact: from "not every instance is strictly T" one must
  produce an instance that is not strictly T, which is `¬∀ → ∃¬`.

  AND THAT IS NOT AN ACCIDENT OF THE PROOF. It is the same bridge §6 reports
  as a FALLEN RULE inside ZTL: `¬∀yP ⊭ ∃y¬P`, the second fallen quantifier
  bridge. The calculus's own metatheory needs, at exactly one rule, the step
  the object logic refuses. That is worth more than the port's timetable.

  AND PER-POINT DECIDABILITY DOES NOT RESCUE IT, which is the detail worth
  keeping. `V` has decidable equality, so `φ d = T` is decidable at EVERY
  point. The quantifier still is not: the domain is arbitrary, and deciding
  `∀ d, φ d = T` over it is not an act. So the obstruction is not a missing
  decision procedure for the atom — it is the survey of the domain, which is
  the same thing this logic refuses to call an act everywhere else.

  WHAT IS NOT CLAIMED. That no choice-free proof of the fourth rule exists.
  It is not proved here and the standard argument does not give one; whether
  another route exists is OPEN, and saying otherwise would be the prediction
  this file was written to avoid.

  THE UNIVERSAL IS A SPECIFICATION, NOT A COMPUTATION, and that is forced.
  ZTL's greedy `∀` is "T if every instance is strictly T, else F". Over an
  arbitrary domain that "else" is a decision about an undecidable
  proposition, so it cannot be a definition without importing one. It is
  written here as a predicate the value must satisfy — the same move as
  `GreedyAdmissible` in `ZYablo` — which keeps every theorem below free of
  that import.
-/
import ZTL

namespace ZParamSound

open V

variable {α : Type}

/-- The greedy universal, as a specification: T exactly when every instance
is strictly T, F otherwise, and never Z (greediness, §6). -/
def IsAll (φ : α → V) (v : V) : Prop :=
  (v = T ↔ ∀ d, φ d = T) ∧ (v = T ∨ v = F)

/-- The greedy existential: T exactly when some instance is strictly T. -/
def IsEx (φ : α → V) (v : V) : Prop :=
  (v = T ↔ ∃ d, φ d = T) ∧ (v = T ∨ v = F)

/-! ### γ: reusable, every parameter -/

/-- **γ₁ sound.** `T:∀xφ → T:φ(c)`, for every parameter c. -/
theorem gamma_all (φ : α → V) (v : V) (h : IsAll φ v) (hv : v = T) (c : α) :
    φ c = T := h.1.mp hv c

/-- **γ₂ sound.** `F:∃xφ → N:φ(c)` — the weak sign, for every parameter.
`¬∃ → ∀¬` is constructive, so this costs nothing. -/
theorem gamma_ex (φ : α → V) (v : V) (h : IsEx φ v) (hv : v = F) (c : α) :
    φ c ≠ T := by
  intro hc
  have : v = T := h.1.mpr ⟨c, hc⟩
  rw [hv] at this
  exact V.noConfusion this

/-! ### δ: a fresh parameter, once -/

/-- **δ₁ sound.** `T:∃xφ → T:φ(c*)` — the fresh parameter is interpreted as
the witness. Elimination of an existential into a proposition is
constructive; nothing is chosen. -/
theorem delta_ex (φ : α → V) (v : V) (h : IsEx φ v) (hv : v = T) :
    ∃ d, φ d = T := h.1.mp hv

/-! ### δ₂ — the one that does not go through here

**δ₂** `F:∀xφ → N:φ(c*)` would
need a parameter to interpret, i.e. an instance that is not strictly T. What
the premise gives is only that NOT every instance is strictly T:

    from   ¬ (∀ d, φ d = T)
    to     ∃ d, φ d ≠ T

is `¬∀ → ∃¬`, and it is NOT proved in this module.

THE CLASSICAL PROOF IS DELIBERATELY NOT HERE. It exists and it is measured —
`inventory/ПАРАМЕТР-ЯРУС.py` runs it and reports its axiom list — but it is
kept OUT of the built corpus, because the corpus carries one invariant that
the paper leads with: every theorem in it is on the empty axiom list. A
theorem that breaks the invariant does not get an exemption in the audit;
this corpus already learned that an exemption added to silence a false alarm
is where a real one hides. It gets a stand of its own instead. -/

/-- What δ₂ gives WITHOUT the classical step, and it is strictly weaker: the
premise refutes the universal, and that is all. Whether the calculus can run
on this weaker form is exactly the open question of the port. -/
theorem delta_all_constructive (φ : α → V) (v : V) (h : IsAll φ v) (hv : v = F) :
    ¬ ∀ d, φ d = T := by
  intro hall
  have : v = T := h.1.mpr hall
  rw [hv] at this
  exact V.noConfusion this

/-! ### The split, stated as one theorem -/

/-- **THREE OF THE FOUR RULES ARE SOUND ON THE EMPTY AXIOM LIST.** The fourth
is not proved here without `Classical`, and the axiom prints below say which
is which. -/
theorem gamma_delta_sound_three (φ : α → V) (v : V) (c : α) :
    (IsAll φ v → v = T → φ c = T)
  ∧ (IsEx φ v → v = F → φ c ≠ T)
  ∧ (IsEx φ v → v = T → ∃ d, φ d = T)
  ∧ (IsAll φ v → v = F → ¬ ∀ d, φ d = T) :=
  ⟨fun h hv => gamma_all φ v h hv c,
   fun h hv => gamma_ex φ v h hv c,
   fun h hv => delta_ex φ v h hv,
   fun h hv => delta_all_constructive φ v h hv⟩

end ZParamSound

#print axioms ZParamSound.gamma_all
#print axioms ZParamSound.gamma_ex
#print axioms ZParamSound.delta_ex
#print axioms ZParamSound.delta_all_constructive
#print axioms ZParamSound.gamma_delta_sound_three
