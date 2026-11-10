/-
  Trolley.lean  —  ZTL / dilemmas
  ---------------------------------------------------------------------------
  The trolley problem (Foot 1967; Thomson 1976, 1985): the two bridges are a
  refuted pair, and the count alone cannot split SWITCH from FOOTBRIDGE.

  Companion of dilemmas/trolley.py (the measured grades). Here, the shapes as
  theorems over ANY model:

    THE MODEL, fixed in words first.
      Act        a type of acts (pull the lever, push the man, do nothing, ...)
      deaths a   the number of deaths the act ends in (a fact of the case)
      Fewer a    the act ends in fewer deaths than its alternative (a fact)
      Kills a    the act itself kills someone (a fact)
      Means a    a death is the MEANS of the rescue (a fact about the causal structure)
      Ought a    the act ought to be done (the norm)

    THE BRIDGES (norms: they MENTION Ought).
      counting   ∀ a, Fewer a → Ought a
      doing      ∀ a, Kills a → ¬ Ought a

  Results:
    bridges_refuted_pair     both bridges + an act that is Fewer and Kills  ⊢ False
    counting_alone_holds     a model of the counting bridge on that act exists
    doing_alone_holds        a model of the doing bridge on that act exists
    count_cannot_split       if Ought reads only the count, equal counts ⇒ equal verdicts:
                             "pull in SWITCH, don't push in FOOTBRIDGE" is impossible
    means_splits             a norm reading Means (same counts) does split them
    means_norm_not_counting  and that norm is not a function of the count
    tragic_no_permitted      if doing nothing ALSO kills (lets die counted as killing),
                             the doing bridge leaves no permitted option

  Scope, honestly: the model is ours; "Ought reads only the count" is the
  formal content of a purely counting ethics, nothing more. Self-contained: no
  imports, no mathlib. All public objects must print "does not depend on any
  axioms".

  AI participation: written by Claude (Anthropic) at the curator's request
  (Vitaly Reznik), 2026-11-10.
-/

namespace Trolley

/-- A case: acts, their facts, and a norm. -/
structure Case where
  Act : Type
  deaths : Act → Nat
  Fewer : Act → Prop
  Kills : Act → Prop
  Means : Act → Prop
  Ought : Act → Prop

/-- THE REFUTED PAIR. The counting bridge and the doing bridge cannot both hold
of a case with an act that ends in fewer deaths AND kills (the lever in SWITCH). -/
theorem bridges_refuted_pair (C : Case)
    (counting : ∀ a, C.Fewer a → C.Ought a)
    (doing : ∀ a, C.Kills a → ¬ C.Ought a)
    (a : C.Act) (hf : C.Fewer a) (hk : C.Kills a) : False :=
  doing a hk (counting a hf)

/-- The SWITCH case, one act (the lever): fewer deaths, and it kills. -/
def switchWith (o : Prop) : Case where
  Act := Unit
  deaths := fun _ => 1
  Fewer := fun _ => True
  Kills := fun _ => True
  Means := fun _ => False
  Ought := fun _ => o

/-- Each bridge ALONE is satisfiable on the same facts: the impossibility is
in the PAIR, not in either principle. -/
theorem counting_alone_holds :
    (∀ a, (switchWith True).Fewer a → (switchWith True).Ought a)
    ∧ (switchWith True).Fewer () ∧ (switchWith True).Kills () :=
  ⟨fun _ _ => trivial, trivial, trivial⟩

theorem doing_alone_holds :
    (∀ a, (switchWith False).Kills a → ¬ (switchWith False).Ought a)
    ∧ (switchWith False).Fewer () ∧ (switchWith False).Kills () :=
  ⟨fun _ _ h => h, trivial, trivial⟩

/-- THE COUNT CANNOT SPLIT. If the norm reads only the count (acts with equal
deaths get equal verdicts), then an act in SWITCH and an act in FOOTBRIDGE with
the same count cannot get "ought" and "ought not". -/
theorem count_cannot_split (Act : Type) (deaths : Act → Nat) (Ought : Act → Prop)
    (counting_only : ∀ a b, deaths a = deaths b → (Ought a ↔ Ought b))
    (sw fb : Act) (same : deaths sw = deaths fb) :
    ¬ (Ought sw ∧ ¬ Ought fb) :=
  fun ⟨hs, hn⟩ => hn ((counting_only sw fb same).mp hs)

/-- Two acts with the same count: the lever (SWITCH) and the push (FOOTBRIDGE). -/
def leverOrPush (b : Bool) : Nat := match b with | _ => 1

/-- The push uses the death as the MEANS; the lever does not. -/
def usesMeans (b : Bool) : Prop := b = true

/-- The norm that reads Means: "fewer deaths (both acts), but never a death used
as a means". -/
def meansNorm (b : Bool) : Prop := ¬ usesMeans b

/-- THE MEANS SPLITS. Same counts, and the means-reading norm says: pull
(false = lever), don't push (true = push). -/
theorem means_splits :
    leverOrPush false = leverOrPush true ∧ meansNorm false ∧ ¬ meansNorm true :=
  ⟨rfl, fun h => Bool.noConfusion h, fun h => h rfl⟩

/-- And so that norm does NOT read only the count: the split needs an atom the
count does not contain. -/
theorem means_norm_not_counting :
    ¬ (∀ a b, leverOrPush a = leverOrPush b → (meansNorm a ↔ meansNorm b)) :=
  fun h => (h false true rfl).mp means_splits.2.1 rfl

/-- TRAGIC: if letting die counts as killing too (every option kills), the
doing bridge forbids every option — no permitted act exists, and nobody
declared the conflict: the world offers it. -/
theorem tragic_no_permitted (C : Case)
    (doing : ∀ a, C.Kills a → ¬ C.Ought a)
    (every_option_kills : ∀ a, C.Kills a) :
    ¬ ∃ a, C.Ought a :=
  fun ⟨a, h⟩ => doing a (every_option_kills a) h

end Trolley

#print axioms Trolley.bridges_refuted_pair
#print axioms Trolley.switchWith
#print axioms Trolley.counting_alone_holds
#print axioms Trolley.doing_alone_holds
#print axioms Trolley.count_cannot_split
#print axioms Trolley.leverOrPush
#print axioms Trolley.usesMeans
#print axioms Trolley.meansNorm
#print axioms Trolley.means_splits
#print axioms Trolley.means_norm_not_counting
#print axioms Trolley.tragic_no_permitted
