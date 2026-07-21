# VERAXIS–ZTL semantic-review package — candidate subset v0.1

Upstream input for `VERAXIS-ZTL-CONFORMANCE-v0.1`. Every declaration below is `evidence_status: PROVED` on the empty axiom list at the pinned repository snapshot. Mechanical fields are extracted; the semantic fields are authored (ZTL-author semantic review). Four are fully authored as the format sample; the rest carry mechanical fields and an explicit TODO pending format approval.

## Core value and register semantics

### `V.ax_not_Z`
- **canonical name**: `V.ax_not_Z`
- **statement**: `theorem ax_not_Z : znot Z = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: znot
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: Negating the mark computes F: ¬Z = F — the default-deny cell of the negation table.
- **prohibited interpretation**: F here is default-deny (no ground was offered), NOT a grounded negative fact about the atom; the atom stays Z.
- **claim ceiling**: Fixes one cell (¬ of Z is F). Nothing about ¬p for grounded p.
- **positive test vector**: atom Z → ¬(atom) = F (a default-deny verdict).
- **adversarial test vector**: consumer reports ¬(atom)=F as a grounded false fact → FAILS.
- **expected Veraxis conformance**: Veraxis exposes ¬(atom)=F as default-deny, never as a grounded negative world-fact.

### `V.ax_notnot_Z`
- **canonical name**: `V.ax_notnot_Z`
- **statement**: `theorem ax_notnot_Z : znot (znot Z) = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: znot
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: Under this negation, double-negating the mark computes the verdict T: ¬Z = F, then ¬F = T. It is a fact about the CONNECTIVE TABLE.
- **prohibited interpretation**: This T is NOT a grounded truth of the atom. `¬¬Z = T` must not be read as 'the datum is verified' or the atom promoted to grounded-T; the atom's own status stays Z, only the compound computes T (a formula verdict, §10).
- **claim ceiling**: Fixes exactly one cell (¬¬ applied to Z is T). Says nothing about ¬¬p for grounded p, nor about whether the atom denotes.
- **positive test vector**: atom marked Z; compute ¬¬(atom) → expect T (formula verdict).
- **adversarial test vector**: atom marked Z; a consumer reads ¬¬(atom)=T and reports the atom's ground-state as T → CONFORMANCE FAILS (prohibited promotion).
- **expected Veraxis conformance**: Veraxis exposes the compound verdict T but keeps the atom's grounding at Z; it never serialises the atom as grounded-true.

### `V.lift1_classical`
- **canonical name**: `V.lift1_classical`
- **statement**: `theorem lift1_classical (f : Bool → Bool) (x : V) : lift1 f x = T ∨ lift1 f x = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: V, lift1
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Every UNARY compound is classical: for any lifted unary connective and any value (Z included), the result is T or F — the mark never survives an operator.
- **prohibited interpretation**: About COMPOUNDS, not atoms; it does not say the input is classical. The mark lives on atoms and evaporates at the first operator.
- **claim ceiling**: Universal over unary connectives and values. Does not touch atoms/nullary, which may be Z.
- **positive test vector**: any f, x=Z → lift1 f Z ∈ {T,F}.
- **adversarial test vector**: consumer expects a compound to carry Z downstream → it is always T/F.
- **expected Veraxis conformance**: Veraxis may rely on every unary compound being two-valued; only atoms carry Z.

### `V.lift2_classical`
- **canonical name**: `V.lift2_classical`
- **statement**: `theorem lift2_classical (f : Bool → Bool → Bool) (x y : V) : lift2 f x y = T ∨ lift2 f x y = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: V, lift2
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Every BINARY compound is classical: any lifted binary connective on any values (Z included) returns T or F.
- **prohibited interpretation**: About compounds, not the atomic operands; a marked operand does not make the compound carry Z.
- **claim ceiling**: Universal over binary connectives and value pairs. Atoms excluded.
- **positive test vector**: any f, x=Z, y=T → lift2 f Z T ∈ {T,F}.
- **adversarial test vector**: consumer expects a Z operand to propagate as Z through a connective → it collapses to T/F.
- **expected Veraxis conformance**: Veraxis may rely on every binary compound being two-valued.

### `V.evalF_classical`
- **canonical name**: `V.evalF_classical`
- **statement**: `theorem evalF_classical (v : Nat → V) : ∀ φ : Fm, (∃ n, φ = .atom n) ∨ evalF v φ = T ∨ evalF v φ = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: Fm, V, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Greediness, general: every formula is an ATOM or evaluates to T or F. Z appears only on atoms; no compound takes the mark — the structural guarantee behind two-valued verdicts.
- **prohibited interpretation**: Does NOT say atoms are classical (they may be Z); it says compounds are. A compound value can never serialize as Z.
- **claim ceiling**: General over formulas and valuations; the atomic case is set aside (atoms may be Z). No denotation claim.
- **positive test vector**: any non-atomic φ, any marked valuation → evalF ∈ {T,F}.
- **adversarial test vector**: consumer reserves a Z code point for a compound's value → compounds are strictly {T,F}.
- **expected Veraxis conformance**: Veraxis serializes compound verdicts as {T,F}; only atom slots may hold Z.

### `V.isZ_detects`
- **canonical name**: `V.isZ_detects`
- **statement**: `theorem isZ_detects : isZ Z = T ∧ isZ T = F ∧ isZ F = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: isZ
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: The quarantine detector isZ (= ¬(x↔x), expressible inside the logic) flags the mark: T on Z, F on the verdicts. The system detects its own marks from within.
- **prohibited interpretation**: isZ is a META-predicate about the register (is this a mark?), NOT a truth about the world: isZ Z = T means 'this slot is unverified', not 'the atom is true'.
- **claim ceiling**: Fixes the three cells of isZ. It is the ONLY sanctioned mark-detector; a generic predicate returns Z on a mark, not T.
- **positive test vector**: slot Z → isZ = T; slot T/F → isZ = F.
- **adversarial test vector**: consumer reads isZ=T as the atom being true → FAILS (detector, not assertion).
- **expected Veraxis conformance**: Veraxis may use isZ to route/quarantine unverified slots; never as grounded truth.

### `V.no_gluts`
- **canonical name**: `V.no_gluts`
- **statement**: `theorem no_gluts : ∀ p, ¬(p = T ∧ znot p = T)`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: znot
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: No gluts: no value makes both p and ¬p true. Paracomplete (a gap at Z) but NOT paraconsistent — a contradiction is never jointly asserted.
- **prohibited interpretation**: Does NOT give excluded middle (p∨¬p FALLS at Z). Absence of gluts ≠ presence of the middle.
- **claim ceiling**: Universal over values; the no-glut direction only. The companion gap (paracompleteness) is separate.
- **positive test vector**: any p → not (p=T and ¬p=T).
- **adversarial test vector**: consumer relies on explosion (p,¬p ⊨ anything) as if gluts existed → gluts are absent, explosion is vacuous.
- **expected Veraxis conformance**: Veraxis may rely on no-glut (never both affirmed and denied); it must not assume excluded middle.

## Warrant-preserving and credit-rejecting inference

### `V.modus_ponens`
- **canonical name**: `V.modus_ponens`
- **statement**: `theorem modus_ponens : ∀ p q : V, p = T → zimp p q = T → q = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: V, zimp
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Modus ponens holds: an earned p and an earned p→q yield an earned q. The forward inference is warrant-preserving.
- **prohibited interpretation**: The earned q is a formula verdict transported from the premises, NOT a grounded world-fact about q's atom (§10). MP moves warrant, does not mint ground.
- **claim ceiling**: General over p, q. MP as a valid rule; nothing about the converse or q's denotation.
- **positive test vector**: p=T, p→q=T → q=T.
- **adversarial test vector**: consumer applies MP with p unverified (Z) → premise not T, the rule does not fire; no false promotion.
- **expected Veraxis conformance**: Veraxis may use MP soundly; the earned q stays a formula verdict.

### `V.rule_and_intro`
- **canonical name**: `V.rule_and_intro`
- **statement**: `theorem rule_and_intro : ∀ p q, p = T → q = T → zand p q = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zand
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: ∧-introduction: two earned claims yield their earned conjunction — joint warrant is composable.
- **prohibited interpretation**: p∧q=T means both are jointly EARNED as verdicts, not that the conjoined objects are grounded-true in the world.
- **claim ceiling**: General; the intro direction (elim is separate).
- **positive test vector**: p=T, q=T → p∧q=T.
- **adversarial test vector**: consumer conjoins with a Z side → p∧q ≠ T; the mark blocks, no false joint warrant.
- **expected Veraxis conformance**: Veraxis's join-by-∧ requires BOTH earned; a marked side blocks it.

### `V.rule_and_elim`
- **canonical name**: `V.rule_and_elim`
- **statement**: `theorem rule_and_elim : ∀ p q, zand p q = T → p = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zand
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: ∧-elimination: from an earned conjunction each conjunct is earned — warrant distributes over ∧.
- **prohibited interpretation**: The extracted p=T is a formula verdict, not a grounded fact.
- **claim ceiling**: General; the p-projection (q symmetric by commutativity, separate).
- **positive test vector**: p∧q=T → p=T.
- **adversarial test vector**: consumer extracts p from a conjunction that is not actually T → premise false, no extraction.
- **expected Veraxis conformance**: Veraxis extracts conjuncts only from an earned conjunction.

### `V.rule_transitivity`
- **canonical name**: `V.rule_transitivity`
- **statement**: `theorem rule_transitivity : ∀ p q r, zimp p q = T → zimp q r = T → zimp p r = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zimp
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Transitivity of the arrow: earned p→q and q→r yield earned p→r — implication chains compose.
- **prohibited interpretation**: A formula-level CONSEQUENCE chain, NOT a causal or temporal chain in the world.
- **claim ceiling**: General; transitivity of →-verdicts, not the deduction theorem.
- **positive test vector**: p→q=T, q→r=T → p→r=T.
- **adversarial test vector**: consumer reads the chain as causation → it is entailment structure only.
- **expected Veraxis conformance**: Veraxis may chain earned implications; the chain is logical, not causal.

### `V.dt_one_way`
- **canonical name**: `V.dt_one_way`
- **statement**: `theorem dt_one_way : zimp Z Z = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zimp
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: The deduction theorem is ONE-WAY, witnessed by Z→Z = F: reflexive entailment p⊨p does not internalize to ⊨ p→p — the arrow is stricter than entailment, and even self-implication over the mark is F.
- **prohibited interpretation**: Does NOT mean implication is broken: p→p FALLS at Z (a fallen law), yet the RULE reflexivity holds. The formula-arrow is not the consequence relation.
- **claim ceiling**: One cell (Z→Z=F) witnessing the one-way deduction theorem. Grounded p→p = T; this does not classify all p→p.
- **positive test vector**: p=Z → p→p = F (the arrow does not hold at the mark).
- **adversarial test vector**: consumer treats p→p as a universal tautology (always T) → FAILS at Z.
- **expected Veraxis conformance**: Veraxis must not treat p→p as universally T, nor internalize entailment into the arrow.

### `V.rule_dn_elim_fails`
- **canonical name**: `V.rule_dn_elim_fails`
- **statement**: `theorem rule_dn_elim_fails : ¬ ∀ p, znot (znot p) = T → p = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: znot
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Double-negation ELIMINATION is not universally warrant-preserving: it is not the case that for every p, ¬¬p = T forces p = T. The witness is p = Z (¬¬Z = T yet Z ≠ T).
- **prohibited interpretation**: This does NOT mean any formula with a double negation is rejected, nor that ¬¬p is useless. Only the INFERENCE ¬¬p ⊨ p fails, and exactly at the mark; for grounded p, ¬¬p = T coincides with p = T.
- **claim ceiling**: A universal-negative refuting the rule ∀ p, ¬¬p=T → p=T. It does not classify which p break it, and does not touch ¬¬p as a table value elsewhere.
- **positive test vector**: apply DNE-elim with p = Z: premise ¬¬Z = T holds, conclusion Z = T is false → the rule is correctly seen to fail.
- **adversarial test vector**: a consumer uses DNE-elim as a sound inference to promote an unverified atom to T because its double negation computed T → CONFORMANCE FAILS.
- **expected Veraxis conformance**: Veraxis must not carry ¬¬p ⊨ p as an admissible inference over unverified atoms; grounded atoms are unaffected.

### `V.rule_taut_concl_fails`
- **canonical name**: `V.rule_taut_concl_fails`
- **statement**: `theorem rule_taut_concl_fails : ¬ ∀ p q, p = T → zor q (znot q) = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: znot, zor
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: 'Tautology in the conclusion' fails as a rule: an earned p does NOT license concluding q∨¬q, because excluded middle is not T at q=Z — a fresh unverified atom earns no T.
- **prohibited interpretation**: Does NOT reject q∨¬q wholesale (grounded q → T). What fails is the RULE 'anything ⊨ q∨¬q'; guarded tautologies (¬q→¬q) survive, middle-shaped ones do not.
- **claim ceiling**: Universal-negative refuting the rule; q=Z is the witness. Does not classify which q break it.
- **positive test vector**: p=T, q=Z → q∨¬q = F → the rule correctly fails.
- **adversarial test vector**: consumer injects q∨¬q as an always-available tautology → FAILS at unverified q.
- **expected Veraxis conformance**: Veraxis must not treat excluded middle as a free tautology over unverified atoms.

## Proof-engine correspondence

### `V.closes_iff`
- **canonical name**: `V.closes_iff`
- **statement**: `theorem closes_iff : ∀ (fuel : Nat) (e : Env) (ws : List Node), wsize ws < fuel → (∀ n, sIsEmpty (e n) = false) → (closes fuel e ws = true ↔ ¬ SAT e ws)`
- **module / source hash**: `TableauCert.lean` / `sha256:0a6e13c0e2b35655`
- **dependent definitions**: closes, sIsEmpty
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The tableau engine is correct: a node set CLOSES exactly when it is unsatisfiable (no model), given enough fuel and a non-degenerate environment. Closure ⟺ unsatisfiability.
- **prohibited interpretation**: Closure is FORMULA-level unsatisfiability (no valuation satisfies), NOT a claim that the negated formula is a grounded world-fact.
- **claim ceiling**: General over fuel/environment/nodes with the stated side conditions; the {¬,∧,∨} tableau (heavier connectives via reductions).
- **positive test vector**: an unsatisfiable node set → closes = true.
- **adversarial test vector**: consumer reads a closure as proving a world-fact false → it proves formula-unsatisfiability only.
- **expected Veraxis conformance**: Veraxis maps closure to formula-unsat, not world-falsity.

### `V.tproves_iff`
- **canonical name**: `V.tproves_iff`
- **statement**: `theorem tproves_iff (ps : List Fm) (c : Fm) : tproves ps c = true ↔ ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T`
- **module / source hash**: `TableauCert.lean` / `sha256:0a6e13c0e2b35655`
- **dependent definitions**: Fm, evalF, tproves
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The tableau engine is sound and complete for entailment: `tproves ps c` is true exactly when c follows from ps under every valuation (every classical reading of the marks). Engine YES ⟺ ⊨.
- **prohibited interpretation**: `tproves ps c = true` means c is a semantic CONSEQUENCE — NOT that c is a grounded world-fact, nor that its atoms are verified. A relation between formulas, not an assertion about objects (§10).
- **claim ceiling**: General over premise lists and conclusions on the {¬,∧,∨} basis (heavier connectives reduced by proven identities). Does not extend to arbitrary domains (the FO layer) and makes no denotation claim.
- **positive test vector**: ps = [p, p→q], c = q (modus ponens) → tproves true, and q follows.
- **adversarial test vector**: ps = [], c = ¬q→¬q (a guarded tautology): tproves true, but a consumer must not read the derived c as a grounded world-fact — formula-level consequence only.
- **expected Veraxis conformance**: Veraxis may use `tproves` as the authoritative entailment oracle for the covered fragment, but maps its YES to 'formula-level consequence', never to grounded truth.

### `V.closesN_iff`
- **canonical name**: `V.closesN_iff`
- **statement**: `theorem closesN_iff : ∀ (fuel : Nat) (e : Env) (ws : List Node), wsize ws < fuel → (∀ n, sIsEmpty (e n) = false) → (closesN fuel e ws = true ↔ ¬ SAT e ws)`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c57`
- **dependent definitions**: closes, closesN, sIsEmpty
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Same correctness for the NATIVE engine (→/⊕/↔ handled directly): closesN ⟺ unsatisfiability.
- **prohibited interpretation**: Closure is formula-unsatisfiability, not a grounded world-fact.
- **claim ceiling**: General with the stated side conditions, for the native connective set.
- **positive test vector**: an unsatisfiable node set → closesN = true.
- **adversarial test vector**: as closes_iff: closure ≠ world-falsity.
- **expected Veraxis conformance**: Veraxis maps native closure to formula-unsat only.

### `V.tprovesN_iff`
- **canonical name**: `V.tprovesN_iff`
- **statement**: `theorem tprovesN_iff (ps : List Fm) (c : Fm) : tprovesN ps c = true ↔ ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c57`
- **dependent definitions**: Fm, evalF, tproves, tprovesN
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The NATIVE engine is sound and complete for entailment: tprovesN ps c ⟺ c follows from ps under every valuation.
- **prohibited interpretation**: A YES is formula-level consequence, NOT grounded world-truth (§10).
- **claim ceiling**: General over premise lists and conclusions for the native connectives; no denotation claim, no arbitrary domains.
- **positive test vector**: ps=[p, p→q], c=q → tprovesN true.
- **adversarial test vector**: consumer reads a derived c as a grounded fact → consequence only.
- **expected Veraxis conformance**: Veraxis may use tprovesN as the entailment oracle; YES ↦ consequence, not truth.

### `V.engines_agree`
- **canonical name**: `V.engines_agree`
- **statement**: `theorem engines_agree (ps : List Fm) (c : Fm) : tprovesN ps c = tproves ps c`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c57`
- **dependent definitions**: Fm, tproves, tprovesN
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The two proof engines agree on every input: the {¬,∧,∨}-basis engine and the native →/⊕/↔ engine return the same YES/NO — the reduction is faithful.
- **prohibited interpretation**: Engine equivalence, not a claim about the world.
- **claim ceiling**: General over premise lists and conclusions; both are sound+complete for ⊨ (separate results).
- **positive test vector**: any ps, c → tprovesN ps c = tproves ps c.
- **adversarial test vector**: consumer expects the engines to differ on some input → they never do.
- **expected Veraxis conformance**: Veraxis may use either engine interchangeably as the oracle.

### `V.entails_structural`
- **canonical name**: `V.entails_structural`
- **statement**: `theorem entails_structural (σ : Nat → Fm) (Γ : List Fm) (φ : Fm) (h : ∀ v, allT v Γ → evalF v φ = T) : ∀ v, allT v (substL σ Γ) → evalF v (substF σ φ) = T`
- **module / source hash**: `ZAlgebra.lean` / `sha256:a7c845303ba3d7b4`
- **dependent definitions**: Fm, entails, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Entailment is STRUCTURAL: if Γ ⊨ φ then, substituting formulas for atoms uniformly, σΓ ⊨ σφ — the consequence relation respects substitution (Suszko-structurality).
- **prohibited interpretation**: A property of the CONSEQUENCE relation over formula variables, NOT a licence to substitute grounded objects; the substituends are formulas.
- **claim ceiling**: General over substitutions, premise lists, conclusions. Structurality only; not the deduction theorem or compactness.
- **positive test vector**: Γ ⊨ φ, substitution σ → σΓ ⊨ σφ.
- **adversarial test vector**: consumer substitutes an object for a variable expecting object-identity to carry → only formula structure carries.
- **expected Veraxis conformance**: Veraxis may rely on uniform substitution preserving entailment over formula variables.

## Refinement and warranty structure

### `ZTime.refines_refl`
- **canonical name**: `ZTime.refines_refl`
- **statement**: `theorem refines_refl (m : Marking) : Refines m m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, Refines
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Refinement is reflexive: any marking refines itself — the 'more-verified-than' order has identity.
- **prohibited interpretation**: An order on MARKINGS (verification states), not on world-facts.
- **claim ceiling**: General over markings; reflexivity only.
- **positive test vector**: any m → Refines m m.
- **adversarial test vector**: consumer assumes refinement is strict/irreflexive → it is a preorder.
- **expected Veraxis conformance**: Veraxis's refinement is a preorder; equal states refine each other.

### `ZTime.refines_trans`
- **canonical name**: `ZTime.refines_trans`
- **statement**: `theorem refines_trans {m₂ m₁ m : Marking} (h₂ : Refines m₂ m₁) (h₁ : Refines m₁ m) : Refines m₂ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, Refines
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Refinement is transitive: chained refinements compose — the verification order is a preorder.
- **prohibited interpretation**: A property of the marking order, not of the world.
- **claim ceiling**: General; transitivity only.
- **positive test vector**: Refines m₂ m₁, Refines m₁ m → Refines m₂ m.
- **adversarial test vector**: consumer assumes refinement is not transitive → it is.
- **expected Veraxis conformance**: Veraxis may chain refinement steps.

### `ZTime.verify_refines`
- **canonical name**: `ZTime.verify_refines`
- **statement**: `theorem verify_refines {m : Marking} {a : Nat} {v : V} (h : m a = V.Z) : Refines (verify m a v) m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, Refines, V
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Verifying an unverified slot is a refinement: setting a Z-atom to a verdict yields a marking that refines the original — verification only ever adds ground.
- **prohibited interpretation**: Says verification MOVES along the refinement order (adds ground), NOT that the verified value v is true — v could be F.
- **claim ceiling**: General over markings/atoms/values, given the slot was Z. No claim that v is correct.
- **positive test vector**: m a = Z → verify m a v refines m.
- **adversarial test vector**: consumer reads 'refines' as 'the new value is true' → it is about ground added, not the truth of v.
- **expected Veraxis conformance**: Veraxis models verification as monotone refinement; the verified value's truth is a separate matter.

### `ZTime.evalF_congr`
- **canonical name**: `ZTime.evalF_congr`
- **statement**: `theorem evalF_congr {m' m : Marking} (h : ∀ n, m' n = m n) : ∀ φ, evalF m' φ = evalF m φ`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Evaluation is a congruence on markings: markings agreeing on every atom give every formula the same verdict — the verdict depends only on the marking's content.
- **prohibited interpretation**: A determinism property of evaluation, not a world-fact claim.
- **claim ceiling**: General over markings and formulas; congruence only.
- **positive test vector**: m' = m pointwise → evalF m' φ = evalF m φ for all φ.
- **adversarial test vector**: consumer expects hidden state to move the verdict → evaluation is a pure function of the marking.
- **expected Veraxis conformance**: Veraxis's evaluation is deterministic in the marking; no hidden inputs.

### `ZTime.hereditary_absorbing`
- **canonical name**: `ZTime.hereditary_absorbing`
- **statement**: `theorem hereditary_absorbing {φ : Fm} {m : Marking} {a : Nat} {v : V} (hH : Hereditary φ m) (ha : m a = V.Z) : evalF (verify m a v) φ = evalF m φ ∧ Hereditary φ (verify m a v)`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Fm, Hereditary, Marking, V, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Hereditary is absorbing under verification: if φ is hereditary at m, verifying any unverified atom leaves φ's verdict UNCHANGED and still hereditary — once settled, further verification buys nothing.
- **prohibited interpretation**: About a HEREDITARY verdict; a sound/until verdict CAN change under verification. Absorption is the mark of the permanent grade only.
- **claim ceiling**: General over φ/m/a/v, given Hereditary φ m and the slot was Z. Does not say which φ are hereditary.
- **positive test vector**: φ hereditary at m, verify a Z-atom → same verdict, still hereditary.
- **adversarial test vector**: consumer re-checks a hereditary verdict after each verification expecting change (wasted), or treats an until-verdict as hereditary → FAILS.
- **expected Veraxis conformance**: Veraxis may treat a hereditary verdict as settled, immune to further verification; only non-hereditary verdicts need re-checking.

### `ZTime.grounded_hereditary`
- **canonical name**: `ZTime.grounded_hereditary`
- **statement**: `theorem grounded_hereditary {φ : Fm} {m : Marking} (hg : ∀ n, m n ≠ V.Z) : Hereditary φ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Fm, Hereditary, Marking, V
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: A fully grounded marking makes every formula hereditary: with no atom unverified there is nothing left to refine, so every verdict is permanent — ground buys permanence.
- **prohibited interpretation**: Requires FULL grounding (no Z anywhere). A partially grounded marking does NOT make all formulas hereditary; permanence is bought with ground, not asserted.
- **claim ceiling**: General over φ, given a Z-free marking. Sufficient condition (full grounding ⇒ hereditary), not necessary.
- **positive test vector**: a Z-free marking → every φ hereditary.
- **adversarial test vector**: consumer assumes a partially-verified marking gives permanent verdicts → only full grounding guarantees it.
- **expected Veraxis conformance**: Veraxis may treat verdicts under a fully-grounded marking as permanent; partial grounding does not license it globally.

### `ZTime.hereditary_sound`
- **canonical name**: `ZTime.hereditary_sound`
- **statement**: `theorem hereditary_sound {φ : Fm} {m : Marking} (hH : Hereditary φ m) : Sound φ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Fm, Hereditary, Marking, Sound
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: A hereditary verdict is sound: if φ under marking m is hereditary (its T survives every partial refinement), then it is sound (never lies about the facts at m). The stronger warranty implies the weaker.
- **prohibited interpretation**: Soundness here is 'does not lie under the current marking', NOT 'permanently settled' (that is hereditary). A merely-sound verdict must not be read as hereditary or as revocation-proof.
- **claim ceiling**: General over all φ and m. Establishes hereditary ⇒ sound only; NOT the converse (a sound verdict need not be hereditary — measured separately), and does not characterise which formulas are hereditary.
- **positive test vector**: a formula/marking that is hereditary (grounded atoms, stable T) → it is also sound.
- **adversarial test vector**: a sound-but-not-hereditary T (survives no-lie now, revoked under a later verification): a consumer treating sound as hereditary wrongly marks it settled → CONFORMANCE FAILS.
- **expected Veraxis conformance**: Veraxis's grade ladder respects hereditary ⇒ sound and does NOT collapse the two; a sound-only verdict stays revocable.

### `ZTime.Witness.strict_ladder`
- **canonical name**: `ZTime.Witness.strict_ladder`
- **statement**: `theorem strict_ladder : (sound3 V.Z V.Z V.Z = false ∧ hered3 V.Z V.Z V.Z = false) ∧ (sound3 V.T V.Z V.Z = true ∧ hered3 V.T V.Z V.Z = false) ∧ hered3 V.T V.T V.Z = true`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: V, hered3, sound3
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: The strict warranty ladder U→S→H is REALIZED rung by rung by an exhibited case: a verdict neither sound nor hereditary (Z,Z,Z), one sound-but-not-hereditary (T,Z,Z), and one hereditary (T,T,Z). The three grades are genuinely distinct.
- **prohibited interpretation**: A WITNESS that the grades separate, not a classification of all formulas; it exhibits one instance per rung.
- **claim ceiling**: A concrete finite construction (specific values). Proves the ladder is inhabited at each rung; does not enumerate which formulas sit where.
- **positive test vector**: the exhibited triples realize U, S, H respectively.
- **adversarial test vector**: consumer collapses sound and hereditary into one 'verified' grade → the sound-not-hereditary case would be wrongly settled.
- **expected Veraxis conformance**: Veraxis must carry all three grades distinctly; the sound-not-hereditary rung is real and revocable.

