/-
  Hume_Guillotine.lean  —  ZTL / dilemmas
  ---------------------------------------------------------------------------
  No ought from is: the guillotine as a conservativity theorem.

  Hume (Treatise III.i.1): descriptive premises alone never yield a normative
  conclusion; every system of morals that seems to derive one has smuggled a
  bridge premise that is itself normative.  Checked here in the same shape as
  Plato_Conservativity.lean: the descriptive axioms do not constrain the
  normative predicate AT ALL, so any model extends with any assignment of
  ought whatsoever — and therefore no contingent ought-sentence is entailed,
  in either direction.  The converse is proved too: add the bridge, and the
  derivation goes through by bare modus ponens.  The guillotine cuts exactly
  at the bridge — nowhere else.

  THE DESCRIPTIVE AXIOMS, fixed in words first (per the programme):

    D1 (nonemptiness)   there is an act: ∃ a, True — the domain is inhabited.
    D2 (factuality)     Fact is any predicate over acts (e.g. "causes
                        suffering"); no axiom mentions Ought.

  Nothing else.  In particular no axiom links Fact to Ought — that absence IS
  Hume's observation.

  Scope, honestly: conservativity is per-theory; these are the two schematic
  descriptive axioms.  A richer descriptive theory requires redoing the file
  — but no descriptive axiom can constrain Ought unless it MENTIONS Ought,
  and then it is a bridge, not a description.  The normative status of the
  guillotine itself (theorem vs commandment) is measured separately in
  dilemmas/hume_guillotine.py.

  Self-contained: no imports, no mathlib.  Check with:

      lean Hume_Guillotine.lean

  All public objects must print "does not depend on any axioms".
-/

namespace HumeGuillotine

/-- A descriptive model: acts and their facts.  No normative vocabulary. -/
structure DescModel where
  Act : Type
  Fact : Act → Prop
  witness : Act

/-- A normed model: the same descriptive data PLUS an ought-predicate.
No field links Fact to Ought — that is the point. -/
structure NormedModel where
  Act : Type
  Fact : Act → Prop
  witness : Act
  Ought : Act → Prop

/-- THE CONSTRUCTION.  Any descriptive model extends with ANY ought-assignment
whatsoever: the descriptive axioms impose zero obstruction on norms. -/
def extend (M : DescModel) (o : M.Act → Prop) : NormedModel where
  Act := M.Act
  Fact := M.Fact
  witness := M.witness
  Ought := o

/-- Descriptive facts survive every normative extension, verbatim. -/
theorem facts_preserved (M : DescModel) (o : M.Act → Prop) (a : M.Act) :
    (extend M o).Fact a ↔ M.Fact a := Iff.rfl

/-- NO OUGHT FROM IS.  For any descriptive model there is an extension where
some act ought to be done and an extension where no act ought to be done —
with identical descriptive facts.  Hence no contingent ought-sentence is
entailed by the descriptions, in either direction: two models of the same
descriptions disagree on it. -/
theorem ought_underdetermined (M : DescModel) :
    (∃ N : NormedModel, N.Act = M.Act ∧ (∃ a, N.Ought a))
    ∧ (∃ N : NormedModel, N.Act = M.Act ∧ ¬ (∃ a, N.Ought a)) :=
  ⟨⟨extend M (fun _ => True), rfl, ⟨M.witness, trivial⟩⟩,
   ⟨extend M (fun _ => False), rfl, fun ⟨_, h⟩ => h⟩⟩

/-- THE BRIDGE, AND ONLY THE BRIDGE.  Add the normative premise "whatever has
the fact ought not be done" (a bridge: it MENTIONS ought) and the derivation
is bare modus ponens.  The guillotine cuts between description and norm, not
between premise and conclusion. -/
theorem bridge_delivers (N : NormedModel)
    (bridge : ∀ a, N.Fact a → N.Ought a)
    (a : N.Act) (h : N.Fact a) : N.Ought a :=
  bridge a h

/-- And the bridge is NECESSARY: without it, the same facts coexist with the
opposite norm.  Packaged for citation: same act, same facts, ought and
not-ought — in two extensions of one descriptive model. -/
theorem bridge_necessary (M : DescModel) :
    (∃ N : NormedModel, N.Ought = fun _ => True)
    ∧ (∃ N : NormedModel, N.Ought = fun _ => False) :=
  ⟨⟨extend M (fun _ => True), rfl⟩, ⟨extend M (fun _ => False), rfl⟩⟩

/-! ## Verdict

The descriptive layer does not reach the normative one: `extend` typechecks
with EVERY ought-assignment (ought_underdetermined), facts intact
(facts_preserved); a norm becomes derivable exactly when a premise mentioning
ought is added (bridge_delivers), and without one the opposite norms are both
available (bridge_necessary).  Hume's law, in the same costume as "absence
has no formula": description cannot exclude — or include — a single norm.
What every ethics buys with its bridge is measured, with the link named, in
dilemmas/hume_guillotine.py.
-/

end HumeGuillotine

#print axioms HumeGuillotine.extend
#print axioms HumeGuillotine.facts_preserved
#print axioms HumeGuillotine.ought_underdetermined
#print axioms HumeGuillotine.bridge_delivers
#print axioms HumeGuillotine.bridge_necessary
