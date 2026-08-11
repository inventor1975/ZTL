/-
  Cogito_Conservativity.lean  —  ZTL / dilemmas
  ---------------------------------------------------------------------------
  No subject from thinking: Lichtenberg's objection as a conservativity
  theorem.

  Descartes (Med. II): "cogito, ergo sum" — from the occurrence of thinking
  to the existence of a thinking SUBJECT.  Lichtenberg (Sudelbücher K 76):
  one is entitled only to "es denkt" — "there is thinking" — as one says
  "it rains"; the step to an owner is an addition, not an observation.
  Checked here in the same shape as Hume_Guillotine.lean and
  Plato_Conservativity.lean: the thinking-facts impose ZERO obstruction on
  ownership, so any model of occurring thinking extends with any
  bearer-assignment whatsoever — including the assignment where NOTHING is
  owned.  The subjectless world is a model.  Conversely, add the bridge
  premise "all thinking has a bearer" and the derivation is bare modus
  ponens.  The cut lies exactly at the bridge — nowhere else.

  THE THINKING AXIOMS, fixed in words first (per the programme):

    T1 (occurrence)   there is an event, and it is a thinking event:
                      the witness — this is what the act of doubt itself
                      certifies, and it is carried as a FIELD, not assumed
                      classically.
    T2 (factuality)   Thinking is a predicate over events; no axiom
                      mentions bearers or ownership.

  Nothing else.  In particular no axiom links Thinking to Owned — that
  absence IS Lichtenberg's observation.

  Scope, honestly: conservativity is per-theory; a richer theory of mind
  requires redoing the file — but no thinking-axiom can constrain Owned
  unless it MENTIONS ownership, and then it is a bridge (Descartes' "what
  thinks, is"), not an observation.  The warrant grades of the whole
  package, and the performative reading (Hintikka), are measured
  separately in dilemmas/cogito.py.

  Self-contained: no imports, no mathlib.  Check with:

      lean Cogito_Conservativity.lean

  All public objects must print "does not depend on any axioms".
-/

namespace CogitoConservativity

/-- A thinking model: events, which of them are thinkings, and one witnessed
occurrence.  No ownership vocabulary. -/
structure ThoughtModel where
  Event : Type
  Thinking : Event → Prop
  witness : Event
  witness_thinks : Thinking witness

/-- A bearer model: the same thinking data PLUS an ownership predicate
("this thinking has a bearer").  No field links Thinking to Owned —
that is the point. -/
structure BearerModel where
  Event : Type
  Thinking : Event → Prop
  witness : Event
  witness_thinks : Thinking witness
  Owned : Event → Prop

/-- THE CONSTRUCTION.  Any thinking model extends with ANY ownership
assignment whatsoever: the thinking-facts impose zero obstruction on
subjects. -/
def extend (M : ThoughtModel) (o : M.Event → Prop) : BearerModel where
  Event := M.Event
  Thinking := M.Thinking
  witness := M.witness
  witness_thinks := M.witness_thinks
  Owned := o

/-- The thinking-facts survive every ownership extension, verbatim. -/
theorem thinking_preserved (M : ThoughtModel) (o : M.Event → Prop)
    (e : M.Event) : (extend M o).Thinking e ↔ M.Thinking e := Iff.rfl

/-- NO SUBJECT FROM THINKING.  For any thinking model there is an extension
where the witnessed thinking is owned and an extension where NOTHING is
owned — with identical thinking-facts, the witnessed occurrence included.
The second is Lichtenberg's world: es denkt, and nobody is home.  Hence no
ownership claim is entailed by the thinking-facts, in either direction. -/
theorem bearer_underdetermined (M : ThoughtModel) :
    (∃ N : BearerModel, N.Event = M.Event ∧ (∃ e, N.Owned e))
    ∧ (∃ N : BearerModel, N.Event = M.Event ∧ ¬ (∃ e, N.Owned e)) :=
  ⟨⟨extend M (fun _ => True), rfl, ⟨M.witness, trivial⟩⟩,
   ⟨extend M (fun _ => False), rfl, fun ⟨_, h⟩ => h⟩⟩

/-- SENSUS EST, ERGO EST — the curator's emendation (V. Reznik, 2026-05,
measured 2026-08-08).  From a witnessed occurrence the existence of
SOMETHING follows internally: the witness itself delivers it.  No bridge,
no subject, no axioms — the one metaphysical sentence of the series that
is a theorem of the occurrence model rather than a purchase against it.
(Contrast bearer_underdetermined: "ergo sum" is not available; "ergo est"
is free.) -/
theorem occurrence_exists (M : ThoughtModel) : ∃ e, M.Thinking e :=
  ⟨M.witness, M.witness_thinks⟩

/-- THE BRIDGE, AND ONLY THE BRIDGE.  Add the premise "all thinking has a
bearer" (a bridge: it MENTIONS ownership — Descartes' background principle
"what thinks, is") and the sum follows by bare modus ponens from the
witnessed occurrence. -/
theorem bridge_delivers (N : BearerModel)
    (bridge : ∀ e, N.Thinking e → N.Owned e) : N.Owned N.witness :=
  bridge N.witness N.witness_thinks

/-- And the bridge is NECESSARY: without it the same witnessed thinking
coexists with total ownerlessness.  Packaged for citation: same events,
same thinkings, everything owned and nothing owned — two extensions of one
thinking model. -/
theorem bridge_necessary (M : ThoughtModel) :
    (∃ N : BearerModel, N.Owned = fun _ => True)
    ∧ (∃ N : BearerModel, N.Owned = fun _ => False) :=
  ⟨⟨extend M (fun _ => True), rfl⟩, ⟨extend M (fun _ => False), rfl⟩⟩

/-! ## Verdict

The thinking layer does not reach the subject layer: `extend` typechecks
with EVERY ownership assignment (bearer_underdetermined), the witnessed
occurrence intact (thinking_preserved); the sum becomes derivable exactly
when a premise mentioning ownership is added (bridge_delivers), and without
one the ownerless world is a model (bridge_necessary).  Lichtenberg's "es
denkt", in the same costume as "absence has no formula" and Hume's
guillotine: occurrence cannot exclude — or include — a single owner.  What
the cogito buys with its bridge, and what the performative reading earns
without one, is measured with the links named in dilemmas/cogito.py.
-/

end CogitoConservativity

#print axioms CogitoConservativity.extend
#print axioms CogitoConservativity.thinking_preserved
#print axioms CogitoConservativity.bearer_underdetermined
#print axioms CogitoConservativity.occurrence_exists
#print axioms CogitoConservativity.bridge_delivers
#print axioms CogitoConservativity.bridge_necessary
