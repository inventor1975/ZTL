import Agrippa
import ZTime

/-!
# AgrippaZ — the count of readings, read in ZTL's own terms: futures and grades. Zero axioms.

2026-10-25 (the curator: "how will you check it, if ZTL's output is always true or false and Z is only on the
input?"). Exactly so: Z lives on atoms; a verdict is T or F. The count of readings shows up not in the verdict but in
its FUTURE. A statement x of a justification chain (Agrippa.lean) is an atom ZTL has not settled. Its ADMISSIBLE
futures are the completions of the marks that respect every support on x's chain — exactly the readings, carried
into ZTL's values (`Admissible`). The verdict on x (the formula `x ∧ ⊤`, T or F today) is then read the way ZTL
reads grades — does any admissible future change it (`AdmHereditary`)?

  `two_readings_on_credit`  two readings that disagree ⇒ today's verdict is NOT hereditary over the admissible
                            futures: one of them reverses it — until-verification, ON CREDIT;
  `forced_settles`          one forced value (the chain reaches a ground: `Agrippa.forced_one`) ⇒ one verification tick
                            settles x, and from then on the verdict is the same in every admissible future —
                            hereditary, EARNED;
  `paradox_no_future`       no reading ⇒ no admissible future at all — the paradox passport.

Honest size: this is mostly a translation (Bool readings ↔ mark-free completions); its value is that "two readings =
on credit" stops being a sentence. Plain `ZTime.Hereditary` ranges over EVERY refinement, and an unsettled atom is
never hereditary under it; admissibility — the chain's own supports — is what the count adds.

VR discipline: `#print axioms` at the end — the empty list, every line.
-/

namespace AgrippaZ

/-- A classical value as a ZTL value. -/
def emb : Bool → ZTime.V
  | true => ZTime.V.T
  | false => ZTime.V.F

/-- An admissible future of x: a mark-free marking that IS a reading of x's chain, carried into ZTL's values. -/
def Admissible (J : Agrippa.Sys) (x : Nat) (c : ZTime.Marking) : Prop :=
  ∃ v : Nat → Bool, Agrippa.Reading J x v ∧ ∀ n, c n = emb (v n)

/-- The verdict on x as a formula: `x ∧ ⊤` — T or F, never Z. -/
def verdictOn (x : Nat) : ZTime.Fm := .conj (.atom x) .top

/-- Hereditary over the admissible futures: no admissible completion of m changes the verdict. -/
def AdmHereditary (J : Agrippa.Sys) (x : Nat) (φ : ZTime.Fm) (m : ZTime.Marking) : Prop :=
  ∀ c, ZTime.Refines c m → Admissible J x c → ZTime.evalF c φ = ZTime.evalF m φ

/-- Nothing settled yet. -/
def unsettled : ZTime.Marking := fun _ => ZTime.V.Z

theorem verdict_emb (c : ZTime.Marking) (x : Nat) (b : Bool) (h : c x = emb b) :
    ZTime.evalF c (verdictOn x) = emb b := by
  show ZTime.V.zand (c x) ZTime.V.T = emb b
  rw [h]; cases b <;> rfl

theorem refines_unsettled (c : ZTime.Marking) : ZTime.Refines c unsettled :=
  fun _ hn => absurd rfl hn

/-- TWO READINGS = ON CREDIT. Today, with x unsettled, the verdict is F; an admissible future makes it T. -/
theorem two_readings_on_credit (J : Agrippa.Sys) (x : Nat) {v w : Nat → Bool}
    (hv : Agrippa.Reading J x v) (hw : Agrippa.Reading J x w) (hne : v x ≠ w x) :
    ¬ AdmHereditary J x (verdictOn x) unsettled := by
  intro h
  have today : ZTime.evalF unsettled (verdictOn x) = ZTime.V.F := rfl
  have fv := h (fun n => emb (v n)) (refines_unsettled _) ⟨v, hv, fun _ => rfl⟩
  have fw := h (fun n => emb (w n)) (refines_unsettled _) ⟨w, hw, fun _ => rfl⟩
  rw [verdict_emb _ x (v x) rfl, today] at fv
  rw [verdict_emb _ x (w x) rfl, today] at fw
  cases hvx : v x with
  | true => rw [hvx] at fv; exact ZTime.V.noConfusion fv
  | false =>
      cases hwx : w x with
      | true => rw [hwx] at fw; exact ZTime.V.noConfusion fw
      | false => exact hne (hvx.trans hwx.symm)

/-- ONE FORCED VALUE = EARNED. The chain reaches a ground: one verification tick settles x to the value every reading
gives, and from then on no admissible future changes the verdict. -/
theorem forced_settles (J : Agrippa.Sys) (x a : Nat) (b : Bool) (hg : J (Agrippa.path J x a) = .ground b) :
    ∃ c : Bool, (∀ v, Agrippa.Reading J x v → v x = c) ∧
      AdmHereditary J x (verdictOn x) (ZTime.verify unsettled x (emb c)) := by
  obtain ⟨⟨v₀, hv₀⟩, huniq⟩ := Agrippa.forced_one J x a b hg
  refine ⟨v₀ x, fun v hv => huniq v v₀ hv hv₀, ?_⟩
  intro c _ hadm
  obtain ⟨v, hv, hc⟩ := hadm
  have hcx : c x = emb (v₀ x) := by rw [hc x, huniq v v₀ hv hv₀]
  have now : ZTime.verify unsettled x (emb (v₀ x)) x = emb (v₀ x) := if_pos rfl
  rw [verdict_emb c x (v₀ x) hcx, verdict_emb _ x (v₀ x) now]

/-- NO READING = NO FUTURE. The paradox has no admissible completion at all. -/
theorem paradox_no_future (J : Agrippa.Sys) (x : Nat) (h : ¬ ∃ v, Agrippa.Reading J x v) :
    ∀ c, ¬ Admissible J x c := by
  intro c ⟨v, hv, _⟩
  exact h ⟨v, hv⟩

/-- The three, on the file's own examples: the dogma is on credit, the nullary settles, the liar has no future. -/
theorem dogma_on_credit : ¬ AdmHereditary Agrippa.dogma 1 (verdictOn 1) unsettled := by
  obtain ⟨v, w, hv, hw, hne⟩ := Agrippa.dogma_two
  exact two_readings_on_credit Agrippa.dogma 1 hv hw hne

theorem liar_no_future : ∀ c, ¬ Admissible Agrippa.liar 0 c :=
  paradox_no_future Agrippa.liar 0 Agrippa.liar_zero

end AgrippaZ

#print axioms AgrippaZ.verdict_emb
#print axioms AgrippaZ.refines_unsettled
#print axioms AgrippaZ.two_readings_on_credit
#print axioms AgrippaZ.forced_settles
#print axioms AgrippaZ.paradox_no_future
#print axioms AgrippaZ.dogma_on_credit
#print axioms AgrippaZ.liar_no_future
