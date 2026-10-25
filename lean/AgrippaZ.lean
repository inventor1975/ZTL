import Agrippa
import ZTime

/-!
# AgrippaZ — the count of readings, read in ZTL's own terms: the futures of a verdict. Zero axioms.

2026-10-25 (the curator: "how will you check it, if ZTL's output is always true or false and Z is only on the
input?"). Exactly so: Z lives on atoms — a dirty parameter, not ours, free to change between two reads — and a verdict
is T or F. The count of readings shows not in the verdict but in its FUTURE. A statement x of a justification chain
(Agrippa.lean) is an atom not yet cleaned. Its ADMISSIBLE futures are the cleanings of the marks that respect every
support on x's chain — exactly the readings, carried into ZTL's values (`Admissible`). The verdict on x is the formula
`x ∧ ⊤`, T or F.

Both sides are compared in ONE state — before anything is cleaned (corrected 2026-10-25 after a cloud review: an
earlier pair compared the unsettled state with the state after verification, and after verification EVERY system,
the dogma included, is trivially stable, so it did not separate earned from credit):

  `forced_futures_agree`        the chain reaches a ground ⇒ an admissible future exists, and every admissible future
                                gives the same verdict — earned;
  `two_readings_futures_split`  two readings that disagree ⇒ two admissible futures give opposite verdicts — on credit;
  `paradox_no_future`           no reading ⇒ no admissible future at all.

Honest size: a translation (Bool readings ↔ mark-free markings) of `Agrippa.forced_one`, `Agrippa.even_two` and
`Agrippa.odd_zero`; its value is that "two readings = on credit" stops being a sentence.

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

theorem verdict_emb (c : ZTime.Marking) (x : Nat) (b : Bool) (h : c x = emb b) :
    ZTime.evalF c (verdictOn x) = emb b := by
  show ZTime.V.zand (c x) ZTime.V.T = emb b
  rw [h]; cases b <;> rfl

theorem emb_inj {a b : Bool} (h : emb a = emb b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact ZTime.V.noConfusion h
  · exact ZTime.V.noConfusion h
  · rfl

/-- EARNED. The chain reaches a ground: an admissible future exists, and every admissible future gives x's verdict the
same value. -/
theorem forced_futures_agree (J : Agrippa.Sys) (x a : Nat) (b : Bool) (hg : J (Agrippa.path J x a) = .ground b) :
    (∃ c, Admissible J x c) ∧
      ∀ c c', Admissible J x c → Admissible J x c' →
        ZTime.evalF c (verdictOn x) = ZTime.evalF c' (verdictOn x) := by
  obtain ⟨⟨v₀, hv₀⟩, huniq⟩ := Agrippa.forced_one J x a b hg
  refine ⟨⟨fun n => emb (v₀ n), v₀, hv₀, fun _ => rfl⟩, ?_⟩
  intro c c' ⟨v, hv, hc⟩ ⟨w, hw, hc'⟩
  rw [verdict_emb c x (v x) (hc x), verdict_emb c' x (w x) (hc' x), huniq v w hv hw]

/-- ON CREDIT. Two readings that disagree: two admissible futures give x's verdict opposite values. -/
theorem two_readings_futures_split (J : Agrippa.Sys) (x : Nat) {v w : Nat → Bool}
    (hv : Agrippa.Reading J x v) (hw : Agrippa.Reading J x w) (hne : v x ≠ w x) :
    ∃ c c', Admissible J x c ∧ Admissible J x c' ∧
      ZTime.evalF c (verdictOn x) ≠ ZTime.evalF c' (verdictOn x) := by
  refine ⟨fun n => emb (v n), fun n => emb (w n), ⟨v, hv, fun _ => rfl⟩, ⟨w, hw, fun _ => rfl⟩, ?_⟩
  rw [verdict_emb _ x (v x) rfl, verdict_emb _ x (w x) rfl]
  exact fun h => hne (emb_inj h)

/-- NO READING = NO FUTURE. The paradox has no admissible future at all. -/
theorem paradox_no_future (J : Agrippa.Sys) (x : Nat) (h : ¬ ∃ v, Agrippa.Reading J x v) :
    ∀ c, ¬ Admissible J x c := by
  intro c ⟨v, hv, _⟩
  exact h ⟨v, hv⟩

/-- The three, on Agrippa.lean's own examples: the nullary is earned, the dogma is on credit, the liar has no future. -/
theorem nullary_earned :
    (∃ c, Admissible Agrippa.nullary 1 c) ∧
      ∀ c c', Admissible Agrippa.nullary 1 c → Admissible Agrippa.nullary 1 c' →
        ZTime.evalF c (verdictOn 1) = ZTime.evalF c' (verdictOn 1) :=
  forced_futures_agree Agrippa.nullary 1 1 true rfl

theorem dogma_on_credit : ∃ c c', Admissible Agrippa.dogma 1 c ∧ Admissible Agrippa.dogma 1 c' ∧
    ZTime.evalF c (verdictOn 1) ≠ ZTime.evalF c' (verdictOn 1) := by
  obtain ⟨v, w, hv, hw, hne⟩ := Agrippa.dogma_two
  exact two_readings_futures_split Agrippa.dogma 1 hv hw hne

theorem liar_no_future : ∀ c, ¬ Admissible Agrippa.liar 0 c :=
  paradox_no_future Agrippa.liar 0 Agrippa.liar_zero

end AgrippaZ

#print axioms AgrippaZ.verdict_emb
#print axioms AgrippaZ.emb_inj
#print axioms AgrippaZ.forced_futures_agree
#print axioms AgrippaZ.two_readings_futures_split
#print axioms AgrippaZ.paradox_no_future
#print axioms AgrippaZ.nullary_earned
#print axioms AgrippaZ.dogma_on_credit
#print axioms AgrippaZ.liar_no_future
