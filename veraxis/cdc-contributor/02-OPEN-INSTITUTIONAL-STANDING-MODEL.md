# 02 — OPEN Institutional-Standing Model (Part C)

Contributor artifact — standing: `CORE_RESEARCH_AND_ARCHITECTURE_CONTRIBUTOR`. Feeds submission
sections: 1, 6, 10, 11, 13. This file states the **structural** model for CDC; it does not include
any internal personal example.

**The question the system must answer.** Not *"who is this actor?"* but:

> **In what institutional standing is this actor acting — relative to this object, under what
> authority basis, within what scope, for what permitted consequence, at what time?**

Identity answers *who*. It does not answer *is this actor institutionally entitled to perform this
consequential transition, relative to this object, now?*

---

## Standing as a bounded relation

A **standing** is not a field and not a property of the actor. It is the **resulting bounded relation
/ status** computed from the input dimensions below — `role` is one input; `standing` is what the whole
set yields. (So an actor may carry the label `role = reviewer` yet have **no standing** to approve this
exact object now.)

| Dimension | Meaning |
|---|---|
| `actor` | the entity acting |
| `identity` | authenticated identity (necessary, not sufficient) |
| `role` | the institutional role being exercised now (one input dimension) |
| `authority_basis` | the mandate/appointment that grounds this role (externally grounded; standing does not self-issue) |
| `scope` | mission / population / boundary the role covers |
| `object` | the exact artifact or transition acted upon |
| `action` | the permitted operation |
| `consequence` | the institutional effect the action may produce |
| `effective_time` | when the standing holds |
| `revocation / currentness` | whether the standing is still current (not expired/withdrawn/superseded) |
| `separation_constraints` | roles this actor may **not** simultaneously hold on this object |

A consequential disposition is valid only if all of these are recorded and current at the moment of
the act — not merely that the actor authenticated.

## Canonical principles

1. **Capability does not confer standing.** Knowing how to do a thing is not being entitled to do it.
2. **Standing is bounded, contextual and non-transitive.** Authority in one standing does not flow to
   another — even for the same actor.
3. **OPEN makes institutional standing computable without making it transferable by implication.**

## Separation of powers (the non-transitivity rule)

The same person is, at different moments, *analyst / reviewer / methodology owner / supervisor /
signatory / external expert*. Authority must not leak between these roles because identity coincides.

Concretely: one actor may hold two legitimate standings — e.g. **contributor** and **independent
reviewer** — but **never relative to the same object in the same institutional context**. If an actor
materially shaped an artifact, a later check by the same actor is peer-review-as-contributor, not
independent assurance; independent assurance of that object requires a different actor, or a genuine
separation established for a later bounded review.

> `CONTRIBUTOR ≠ INDEPENDENT REVIEWER ON THE SAME OBJECT`

This is a separation-of-powers property, not an organizational formality. It prevents authority from
being derived from identity, competence, or a prior state.

## How CDC expresses it (without overcomplication)

- **Standing stamp.** Every material institutional act carries
  ⟨ actor/identity, role, authority_basis, scope, object, action, permitted_consequence,
  effective_time, currentness/status, separation_constraints ⟩ under which it was taken — enough bounded
  context to replay the standing determination. The UI need not display all of it; the computational
  object must retain it (actor and currentness included).
- **The reviewer→deliverable seam** (see 05, SEAM-3) is exactly this check: reviewer identity is
  necessary but insufficient; the disposition record must cite valid, current standing for *this*
  action on *this* object, connected to the exact candidate/evidence/rule.
- **Currentness caveat.** Standing-currentness (a signing standing that is still valid at signing
  time) is *design-required*; the executable rollback-resistant currentness runtime is not yet
  operationalized (see 03 and CDC-CLAIM-13). We claim the standing model at the level actually
  established.

**Why this matters for public-sector audit.** In a controller's office the difference between
"authenticated" and "in valid standing to sign *this* finding *now*" is the difference between a
defensible institutional act and a leaked one. A system that computes standing — not just identity —
is auditable in exactly the way a public auditor requires.
