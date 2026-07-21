# VERAXIS–ZTL semantic-review package — candidate subset v0.1

## Snapshot

This package pins the CORPUS it reviews, not itself. A tracked file cannot stably carry the SHA of the commit it lives in (writing that SHA changes the commit SHA). So:

- **corpus_source_commit** (the reviewed Lean corpus): `905c7fd37851704519c3dd172c02650f0b2e5612`  — the last commit that changed `lean/`; the declarations and their per-module `sha256` (below) are taken from this state.
- **package_commit** and the immutable **tag** (`veraxis-ztl-input-v0.1`) are recorded EXTERNALLY — by the git tag and by the downstream Veraxis manifest — never inside this file.
- **DOI (v1.3 baseline)**: `10.5281/zenodo.21472971`  · concept `10.5281/zenodo.21318981`
- **Lean toolchain**: `leanprover/lean4:v4.29.1`
- **theorem / module count**: 371 theorems across 21 modules
- **axiom-audit result**: ALL CLEAN — every theorem on the EMPTY axiom list (`inventory/axiom_audit.py`, re-run in CI)
- **inventory hash** (`ZTL-theorems.txt`): `sha256:fa0b34378a967c409f3c2afb2414c8b5a4b087200f923521dc035933ae1e303a`
- **semantic-review status**: all 28 declarations authored
- **dependency-closure status**: DEFERRED (native Lean dependency extraction not yet run)
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` (typed by `subject_kind`; no generic defaults)

Upstream input for `VERAXIS-ZTL-CONFORMANCE-v0.1`. Every declaration below is `evidence_status: PROVED` on the empty axiom list at the pinned snapshot. Mechanical fields are extracted; the semantic fields are authored (ZTL-author semantic review). No semantic transition is hidden inside a convenient phrasing.

## Core value and register semantics

### `V.ax_not_Z`
- **canonical name**: `V.ax_not_Z`
- **statement**: `theorem ax_not_Z : znot Z = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: znot  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: Negating the mark computes the formula verdict F: ¬Z = F — one cell of the negation table.
- **prohibited interpretation**: F here is the FORMULA VERDICT F, nothing more. 'default-deny' is a possible DOWNSTREAM mapping of that verdict, not the universal meaning of F; and it is not a grounded negative fact about the atom (the atom stays Z).
- **claim ceiling**: Fixes one cell (¬ of Z is F). Nothing about ¬p for grounded p, and no downstream semantics of F is implied.
- **positive test vector** (human): atom Z → ¬(atom) = F (formula verdict).
- **adversarial test vector** (human): consumer reports ¬(atom)=F as a grounded false fact about the atom → FAILS.
- **expected Veraxis conformance**: Veraxis exposes ¬(atom)=F as a formula verdict; any 'default-deny' reading is an explicit downstream mapping, never a grounded negative world-fact.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.ax_not_Z"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.ax_notnot_Z`
- **canonical name**: `V.ax_notnot_Z`
- **statement**: `theorem ax_notnot_Z : znot (znot Z) = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: znot  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: Under this negation, double-negating the mark computes the verdict T: ¬Z = F, then ¬F = T. It is a fact about the CONNECTIVE TABLE.
- **prohibited interpretation**: This T is NOT a grounded truth of the atom. `¬¬Z = T` must not be read as 'the datum is verified' or the atom promoted to grounded-T; the atom's own status stays Z, only the compound computes T (a formula verdict, §10).
- **claim ceiling**: Fixes exactly one cell (¬¬ applied to Z is T). Says nothing about ¬¬p for grounded p, nor about whether the atom denotes.
- **positive test vector** (human): atom marked Z; compute ¬¬(atom) → expect T (formula verdict).
- **adversarial test vector** (human): atom marked Z; a consumer reads ¬¬(atom)=T and reports the atom's ground-state as T → CONFORMANCE FAILS (prohibited promotion).
- **expected Veraxis conformance**: Veraxis exposes the compound verdict T but keeps the atom's grounding at Z; it never serialises the atom as grounded-true.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.ax_notnot_Z"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.lift1_classical`
- **canonical name**: `V.lift1_classical`
- **statement**: `theorem lift1_classical (f : Bool → Bool) (x : V) : lift1 f x = T ∨ lift1 f x = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: V, lift1  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Every UNARY compound is classical: for any lifted unary connective and any value (Z included), the result is T or F — the mark never survives an operator.
- **prohibited interpretation**: About COMPOUNDS, not atoms; it does not say the input is classical. The mark lives on atoms and evaporates at the first operator.
- **claim ceiling**: Universal over unary connectives and values. Does not touch atoms/nullary, which may be Z.
- **positive test vector** (human): any f, x=Z → lift1 f Z ∈ {T,F}.
- **adversarial test vector** (human): consumer expects a compound to carry Z downstream → it is always T/F.
- **expected Veraxis conformance**: Veraxis may rely on every unary compound being two-valued; only atoms carry Z.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.lift1_classical"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.lift2_classical`
- **canonical name**: `V.lift2_classical`
- **statement**: `theorem lift2_classical (f : Bool → Bool → Bool) (x y : V) : lift2 f x y = T ∨ lift2 f x y = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: V, lift2  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Every BINARY compound is classical: any lifted binary connective on any values (Z included) returns T or F.
- **prohibited interpretation**: About compounds, not the atomic operands; a marked operand does not make the compound carry Z.
- **claim ceiling**: Universal over binary connectives and value pairs. Atoms excluded.
- **positive test vector** (human): any f, x=Z, y=T → lift2 f Z T ∈ {T,F}.
- **adversarial test vector** (human): consumer expects a Z operand to propagate as Z through a connective → it collapses to T/F.
- **expected Veraxis conformance**: Veraxis may rely on every binary compound being two-valued.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.lift2_classical"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.evalF_classical`
- **canonical name**: `V.evalF_classical`
- **statement**: `theorem evalF_classical (v : Nat → V) : ∀ φ : Fm, (∃ n, φ = .atom n) ∨ evalF v φ = T ∨ evalF v φ = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: Fm, V, evalF  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Greediness, general: every formula is an ATOM or evaluates to T or F. Z appears only on atoms; no compound takes the mark — the structural guarantee behind two-valued verdicts.
- **prohibited interpretation**: Does NOT say atoms are classical (they may be Z); it says compounds are. A compound value can never serialize as Z.
- **claim ceiling**: General over formulas and valuations; the atomic case is set aside (atoms may be Z). No denotation claim.
- **positive test vector** (human): any non-atomic φ, any marked valuation → evalF ∈ {T,F}.
- **adversarial test vector** (human): consumer reserves a Z code point for a compound's value → compounds are strictly {T,F}.
- **expected Veraxis conformance**: Veraxis serializes compound verdicts as {T,F}; only atom slots may hold Z.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.evalF_classical"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.isZ_detects`
- **canonical name**: `V.isZ_detects`
- **statement**: `theorem isZ_detects : isZ Z = T ∧ isZ T = F ∧ isZ F = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: isZ  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: The quarantine detector isZ (= ¬(x↔x), expressible inside the logic) flags the mark: T on Z, F on the verdicts. The system detects its own marks from within.
- **prohibited interpretation**: isZ is a META-predicate about the register (is this a mark?), NOT a truth about the world: isZ Z = T means 'this slot is unverified', not 'the atom is true'.
- **claim ceiling**: Fixes the three cells of isZ — it proves the detector WORKS (T on Z, F on verdicts). It does NOT prove uniqueness (that no other predicate detects the mark); a generic predicate happens to return Z on a mark, but that is a separate observation.
- **positive test vector** (human): slot Z → isZ = T; slot T/F → isZ = F.
- **adversarial test vector** (human): consumer reads isZ=T as the atom being true → FAILS (detector, not assertion).
- **expected Veraxis conformance**: Veraxis may use isZ to route/quarantine unverified slots; never as grounded truth.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.isZ_detects"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.no_gluts`
- **canonical name**: `V.no_gluts`
- **statement**: `theorem no_gluts : ∀ p, ¬(p = T ∧ znot p = T)`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: znot  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: No gluts at the VALUE level: no single value makes both p and ¬p equal T. (Paracomplete — a gap at Z — but no value is both T and not-T.)
- **prohibited interpretation**: This is a fact about the connective tables, NOT a general paraconsistency claim and NOT a statement about external source conflicts (two parties asserting p and ¬p is a different, institutional matter). It also does not give excluded middle (p∨¬p FALLS at Z).
- **claim ceiling**: Universal over the three values; the no-glut direction only. Says nothing about conflicts between distinct sources or about the middle.
- **positive test vector** (human): any single value v → not (v=T and ¬v=T).
- **adversarial test vector** (human): consumer reads no_gluts as 'the system reconciles conflicting external sources' → it says nothing about source conflict.
- **expected Veraxis conformance**: Veraxis may rely on no single value being both T and not-T; cross-source conflict is handled by the institutional layer, not by this theorem.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.no_gluts"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

## Warrant-preserving and credit-rejecting inference

### `V.modus_ponens`
- **canonical name**: `V.modus_ponens`
- **statement**: `theorem modus_ponens : ∀ p q : V, p = T → zimp p q = T → q = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: V, zimp  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Modus ponens holds: an earned p and an earned p→q yield an earned q. The forward inference is warrant-preserving.
- **prohibited interpretation**: The earned q is a formula verdict transported from the premises, NOT a grounded world-fact about q's atom (§10). MP moves warrant, does not mint ground.
- **claim ceiling**: General over p, q. MP as a valid rule; nothing about the converse or q's denotation.
- **positive test vector** (human): p=T, p→q=T → q=T.
- **adversarial test vector** (human): consumer applies MP with p unverified (Z) → premise not T, the rule does not fire; no false promotion.
- **expected Veraxis conformance**: Veraxis may use MP soundly; the earned q stays a formula verdict.
- **subject_kind**: `inference_rule`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.modus_ponens"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.rule_and_intro`
- **canonical name**: `V.rule_and_intro`
- **statement**: `theorem rule_and_intro : ∀ p q, p = T → q = T → zand p q = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: zand  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: ∧-introduction: two earned claims yield their earned conjunction — joint LOGICAL warrant is composable at the formula level.
- **prohibited interpretation**: p∧q=T establishes joint logical warrant only. It is NOT sufficient for a legal/institutional Seam: certificate admissibility, schema/namespace agreement, provenance and the interface conditions are separate and live in the institutional layer, not in this theorem.
- **claim ceiling**: General; the intro direction (elim is separate). Logical joint warrant, not institutional seam-legality.
- **positive test vector** (human): p=T, q=T → p∧q=T.
- **adversarial test vector** (human): consumer treats p∧q=T as a legally sewn institutional claim → it is only logical joint warrant; seam-legality needs the interface layer.
- **expected Veraxis conformance**: Veraxis's logical join-by-∧ requires BOTH earned; institutional seam-legality adds admissibility/provenance on top, out of scope here.
- **subject_kind**: `inference_rule`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.rule_and_intro"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.rule_and_elim`
- **canonical name**: `V.rule_and_elim`
- **statement**: `theorem rule_and_elim : ∀ p q, zand p q = T → p = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: zand  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: ∧-elimination: from an earned conjunction each conjunct is earned — warrant distributes over ∧.
- **prohibited interpretation**: The extracted p=T is a formula verdict, not a grounded fact.
- **claim ceiling**: General; the p-projection (q symmetric by commutativity, separate).
- **positive test vector** (human): p∧q=T → p=T.
- **adversarial test vector** (human): consumer extracts p from a conjunction that is not actually T → premise false, no extraction.
- **expected Veraxis conformance**: Veraxis extracts conjuncts only from an earned conjunction.
- **subject_kind**: `inference_rule`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.rule_and_elim"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.rule_transitivity`
- **canonical name**: `V.rule_transitivity`
- **statement**: `theorem rule_transitivity : ∀ p q r, zimp p q = T → zimp q r = T → zimp p r = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: zimp  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Transitivity of the arrow: earned p→q and q→r yield earned p→r — implication chains compose.
- **prohibited interpretation**: A formula-level CONSEQUENCE chain, NOT a causal or temporal chain in the world.
- **claim ceiling**: General; transitivity of →-verdicts, not the deduction theorem.
- **positive test vector** (human): p→q=T, q→r=T → p→r=T.
- **adversarial test vector** (human): consumer reads the chain as causation → it is entailment structure only.
- **expected Veraxis conformance**: Veraxis may chain earned implications; the chain is logical, not causal.
- **subject_kind**: `inference_rule`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.rule_transitivity"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.dt_one_way`
- **canonical name**: `V.dt_one_way`
- **statement**: `theorem dt_one_way : zimp Z Z = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: zimp  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: The deduction theorem is ONE-WAY, witnessed by Z→Z = F: reflexive entailment p⊨p does not internalize to ⊨ p→p — the arrow is stricter than entailment, and even self-implication over the mark is F.
- **prohibited interpretation**: Does NOT mean implication is broken: p→p FALLS at Z (a fallen law), yet the RULE reflexivity holds. The formula-arrow is not the consequence relation.
- **claim ceiling**: One cell (Z→Z=F) witnessing the one-way deduction theorem. Grounded p→p = T; this does not classify all p→p.
- **positive test vector** (human): p=Z → p→p = F (the arrow does not hold at the mark).
- **adversarial test vector** (human): consumer treats p→p as a universal tautology (always T) → FAILS at Z.
- **expected Veraxis conformance**: Veraxis must not treat p→p as universally T, nor internalize entailment into the arrow.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.dt_one_way"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.rule_dn_elim_fails`
- **canonical name**: `V.rule_dn_elim_fails`
- **statement**: `theorem rule_dn_elim_fails : ¬ ∀ p, znot (znot p) = T → p = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: znot  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Double-negation ELIMINATION is not universally warrant-preserving: it is not the case that for every p, ¬¬p = T forces p = T. The witness is p = Z (¬¬Z = T yet Z ≠ T).
- **prohibited interpretation**: This does NOT mean any formula with a double negation is rejected, nor that ¬¬p is useless. Only the INFERENCE ¬¬p ⊨ p fails, and exactly at the mark; for grounded p, ¬¬p = T coincides with p = T.
- **claim ceiling**: A universal-negative refuting the rule ∀ p, ¬¬p=T → p=T. It does not classify which p break it, and does not touch ¬¬p as a table value elsewhere.
- **positive test vector** (human): apply DNE-elim with p = Z: premise ¬¬Z = T holds, conclusion Z = T is false → the rule is correctly seen to fail.
- **adversarial test vector** (human): a consumer uses DNE-elim as a sound inference to promote an unverified atom to T because its double negation computed T → CONFORMANCE FAILS.
- **expected Veraxis conformance**: Veraxis must not carry ¬¬p ⊨ p as an admissible inference over unverified atoms; grounded atoms are unaffected.
- **subject_kind**: `inference_rule`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.rule_dn_elim_fails"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.rule_taut_concl_fails`
- **canonical name**: `V.rule_taut_concl_fails`
- **statement**: `theorem rule_taut_concl_fails : ¬ ∀ p q, p = T → zor q (znot q) = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9fdcef5c60f8cc903980fa2db104ac867fd99ca3f409b32d6b`
- **surface definitions referenced in statement**: znot, zor  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: 'Tautology in the conclusion' fails as a rule: an earned p does NOT license concluding q∨¬q, because excluded middle is not T at q=Z — a fresh unverified atom earns no T.
- **prohibited interpretation**: Does NOT reject q∨¬q wholesale (grounded q → T). What fails is the RULE 'anything ⊨ q∨¬q'; guarded tautologies (¬q→¬q) survive, middle-shaped ones do not.
- **claim ceiling**: Universal-negative refuting the rule; q=Z is the witness. Does not classify which q break it.
- **positive test vector** (human): p=T, q=Z → q∨¬q = F → the rule correctly fails.
- **adversarial test vector** (human): consumer injects q∨¬q as an always-available tautology → FAILS at unverified q.
- **expected Veraxis conformance**: Veraxis must not treat excluded middle as a free tautology over unverified atoms.
- **subject_kind**: `inference_rule`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.rule_taut_concl_fails"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

## Proof-engine correspondence

### `V.closes_iff`
- **canonical name**: `V.closes_iff`
- **statement**: `theorem closes_iff : ∀ (fuel : Nat) (e : Env) (ws : List Node), wsize ws < fuel → (∀ n, sIsEmpty (e n) = false) → (closes fuel e ws = true ↔ ¬ SAT e ws)`
- **module / source hash**: `TableauCert.lean` / `sha256:0a6e13c0e2b35655f9a2a04c788e7c3049467b8d3144230a009c5b0d09d8df1b`
- **surface definitions referenced in statement**: Env, Node, SAT, closes, sIsEmpty, wsize  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The tableau engine is correct: a node set CLOSES exactly when it is unsatisfiable (no model), given enough fuel and a non-degenerate environment. Closure ⟺ unsatisfiability.
- **prohibited interpretation**: Closure is FORMULA-level unsatisfiability (no valuation satisfies), NOT a claim that the negated formula is a grounded world-fact.
- **claim ceiling**: General over fuel/environment/nodes with the stated side conditions; the {¬,∧,∨} tableau (heavier connectives via reductions).
- **positive test vector** (human): an unsatisfiable node set → closes = true.
- **adversarial test vector** (human): consumer reads a closure as proving a world-fact false → it proves formula-unsatisfiability only.
- **expected Veraxis conformance**: Veraxis maps closure to formula-unsat, not world-falsity.
- **subject_kind**: `tableau_closure`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.closes_iff"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.tproves_iff`
- **canonical name**: `V.tproves_iff`
- **statement**: `theorem tproves_iff (ps : List Fm) (c : Fm) : tproves ps c = true ↔ ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T`
- **module / source hash**: `TableauCert.lean` / `sha256:0a6e13c0e2b35655f9a2a04c788e7c3049467b8d3144230a009c5b0d09d8df1b`
- **surface definitions referenced in statement**: Fm, evalF, tproves  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The tableau engine is sound and complete for entailment: `tproves ps c` is true exactly when c follows from ps under every valuation (every classical reading of the marks). Engine YES ⟺ ⊨.
- **prohibited interpretation**: `tproves ps c = true` means c is a semantic CONSEQUENCE — NOT that c is a grounded world-fact, nor that its atoms are verified. A relation between formulas, not an assertion about objects (§10).
- **claim ceiling**: General over premise lists and conclusions on the {¬,∧,∨} basis (heavier connectives reduced by proven identities). Does not extend to arbitrary domains (the FO layer) and makes no denotation claim.
- **positive test vector** (human): ps = [p, p→q], c = q (modus ponens) → tproves true, and q follows.
- **adversarial test vector** (human): ps = [], c = ¬q→¬q (a guarded tautology): tproves true, but a consumer must not read the derived c as a grounded world-fact — formula-level consequence only.
- **expected Veraxis conformance**: Veraxis may use `tproves` as the authoritative entailment oracle for the covered fragment, but maps its YES to 'formula-level consequence', never to grounded truth.
- **subject_kind**: `entailment`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.tproves_iff"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.closesN_iff`
- **canonical name**: `V.closesN_iff`
- **statement**: `theorem closesN_iff : ∀ (fuel : Nat) (e : Env) (ws : List Node), wsize ws < fuel → (∀ n, sIsEmpty (e n) = false) → (closesN fuel e ws = true ↔ ¬ SAT e ws)`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c5744a090e3c4796e3e885a30a7130189bf473c9b61530fe7dc`
- **surface definitions referenced in statement**: Env, Node, SAT, closes, closesN, sIsEmpty, wsize  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Same correctness for the NATIVE engine (→/⊕/↔ handled directly): closesN ⟺ unsatisfiability.
- **prohibited interpretation**: Closure is formula-unsatisfiability, not a grounded world-fact.
- **claim ceiling**: General with the stated side conditions, for the native connective set.
- **positive test vector** (human): an unsatisfiable node set → closesN = true.
- **adversarial test vector** (human): as closes_iff: closure ≠ world-falsity.
- **expected Veraxis conformance**: Veraxis maps native closure to formula-unsat only.
- **subject_kind**: `tableau_closure`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.closesN_iff"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.tprovesN_iff`
- **canonical name**: `V.tprovesN_iff`
- **statement**: `theorem tprovesN_iff (ps : List Fm) (c : Fm) : tprovesN ps c = true ↔ ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c5744a090e3c4796e3e885a30a7130189bf473c9b61530fe7dc`
- **surface definitions referenced in statement**: Fm, evalF, tproves, tprovesN  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The NATIVE engine is sound and complete for entailment: tprovesN ps c ⟺ c follows from ps under every valuation.
- **prohibited interpretation**: A YES is formula-level consequence, NOT grounded world-truth (§10).
- **claim ceiling**: General over premise lists and conclusions for the native connectives; no denotation claim, no arbitrary domains.
- **positive test vector** (human): ps=[p, p→q], c=q → tprovesN true.
- **adversarial test vector** (human): consumer reads a derived c as a grounded fact → consequence only.
- **expected Veraxis conformance**: Veraxis may use tprovesN as the entailment oracle; YES ↦ consequence, not truth.
- **subject_kind**: `entailment`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.tprovesN_iff"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.engines_agree`
- **canonical name**: `V.engines_agree`
- **statement**: `theorem engines_agree (ps : List Fm) (c : Fm) : tprovesN ps c = tproves ps c`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c5744a090e3c4796e3e885a30a7130189bf473c9b61530fe7dc`
- **surface definitions referenced in statement**: Fm, tproves, tprovesN  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: The two proof engines agree on every input: the {¬,∧,∨}-basis engine and the native →/⊕/↔ engine return the same YES/NO — the reduction is faithful.
- **prohibited interpretation**: Engine equivalence, not a claim about the world.
- **claim ceiling**: General over premise lists and conclusions; both are sound+complete for ⊨ (separate results).
- **positive test vector** (human): any ps, c → tprovesN ps c = tproves ps c.
- **adversarial test vector** (human): consumer expects the engines to differ on some input → they never do.
- **expected Veraxis conformance**: Veraxis may use either engine interchangeably as the oracle.
- **subject_kind**: `engine_equivalence`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.engines_agree"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `V.entails_structural`
- **canonical name**: `V.entails_structural`
- **statement**: `theorem entails_structural (σ : Nat → Fm) (Γ : List Fm) (φ : Fm) (h : ∀ v, allT v Γ → evalF v φ = T) : ∀ v, allT v (substL σ Γ) → evalF v (substF σ φ) = T`
- **module / source hash**: `ZAlgebra.lean` / `sha256:a7c845303ba3d7b4fbbf8f0b5d5bdac51f7b93f80d1b83d20a22da630f979f68`
- **surface definitions referenced in statement**: Fm, allT, entails, evalF, substF, substL  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Entailment is STRUCTURAL: if Γ ⊨ φ then, substituting formulas for atoms uniformly, σΓ ⊨ σφ — the consequence relation respects substitution (Suszko-structurality).
- **prohibited interpretation**: A property of the CONSEQUENCE relation over formula variables, NOT a licence to substitute grounded objects; the substituends are formulas.
- **claim ceiling**: General over substitutions, premise lists, conclusions. Structurality only; not the deduction theorem or compactness.
- **positive test vector** (human): Γ ⊨ φ, substitution σ → σΓ ⊨ σφ.
- **adversarial test vector** (human): consumer substitutes an object for a variable expecting object-identity to carry → only formula structure carries.
- **expected Veraxis conformance**: Veraxis may rely on uniform substitution preserving entailment over formula variables.
- **subject_kind**: `entailment`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"V.entails_structural"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

## Refinement and warranty structure

### `ZTime.refines_refl`
- **canonical name**: `ZTime.refines_refl`
- **statement**: `theorem refines_refl (m : Marking) : Refines m m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: Marking, Refines  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Refinement is reflexive: any marking refines itself — the 'more-verified-than' order has identity.
- **prohibited interpretation**: An order on MARKINGS (verification states), not on world-facts.
- **claim ceiling**: General over markings; reflexivity only.
- **positive test vector** (human): any m → Refines m m.
- **adversarial test vector** (human): consumer assumes refinement is strict/irreflexive → it is a preorder.
- **expected Veraxis conformance**: Veraxis's refinement is a preorder; equal states refine each other.
- **subject_kind**: `refinement_relation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.refines_refl"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `ZTime.refines_trans`
- **canonical name**: `ZTime.refines_trans`
- **statement**: `theorem refines_trans {m₂ m₁ m : Marking} (h₂ : Refines m₂ m₁) (h₁ : Refines m₁ m) : Refines m₂ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: Marking, Refines  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Refinement is transitive: chained refinements compose — the verification order is a preorder.
- **prohibited interpretation**: A property of the marking order, not of the world.
- **claim ceiling**: General; transitivity only.
- **positive test vector** (human): Refines m₂ m₁, Refines m₁ m → Refines m₂ m.
- **adversarial test vector** (human): consumer assumes refinement is not transitive → it is.
- **expected Veraxis conformance**: Veraxis may chain refinement steps.
- **subject_kind**: `refinement_relation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.refines_trans"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `ZTime.verify_refines`
- **canonical name**: `ZTime.verify_refines`
- **statement**: `theorem verify_refines {m : Marking} {a : Nat} {v : V} (h : m a = V.Z) : Refines (verify m a v) m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: Marking, Refines, V, verify  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Setting a previously-unverified slot yields a refinement: it PRESERVES all the earlier non-Z assignments and is comparable in the refinement order. It is the monotonicity of the operation, not an assertion that ground was added.
- **prohibited interpretation**: This does NOT itself prove that ground was ADDED: the written value v may even be Z, so the theorem alone does not establish a grounding. A Veraxis 'verification' requires the ADDITIONAL conditions v ≠ Z AND an external grounded event; the refinement relation does not supply them.
- **claim ceiling**: General over markings/atoms/values, given the slot was Z. Proves refinement (earlier non-Z preserved), NOT that v is correct, NOT that v is non-Z, NOT that a real-world verification occurred.
- **positive test vector** (human): m a = Z, v = T → verify m a v refines m, and every earlier non-Z assignment is preserved.
- **adversarial test vector** (human): consumer treats any `verify` call as a grounding event (even with v = Z) → FAILS; grounding needs v ≠ Z plus an external event, not just this refinement.
- **expected Veraxis conformance**: Veraxis models the write as monotone refinement; it counts a slot as GROUNDED only on v ≠ Z together with an external grounded event, never from the refinement relation alone.
- **subject_kind**: `refinement_relation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.verify_refines"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `ZTime.evalF_congr`
- **canonical name**: `ZTime.evalF_congr`
- **statement**: `theorem evalF_congr {m' m : Marking} (h : ∀ n, m' n = m n) : ∀ φ, evalF m' φ = evalF m φ`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: Marking, evalF  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Evaluation is a congruence on markings: markings agreeing on every atom give every formula the same verdict — the verdict depends only on the marking's content.
- **prohibited interpretation**: A determinism property of evaluation, not a world-fact claim.
- **claim ceiling**: General over markings and formulas; congruence only.
- **positive test vector** (human): m' = m pointwise → evalF m' φ = evalF m φ for all φ.
- **adversarial test vector** (human): consumer expects hidden state to move the verdict → evaluation is a pure function of the marking.
- **expected Veraxis conformance**: Veraxis's evaluation is deterministic in the marking; no hidden inputs.
- **subject_kind**: `formula_evaluation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.evalF_congr"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `ZTime.hereditary_absorbing`
- **canonical name**: `ZTime.hereditary_absorbing`
- **statement**: `theorem hereditary_absorbing {φ : Fm} {m : Marking} {a : Nat} {v : V} (hH : Hereditary φ m) (ha : m a = V.Z) : evalF (verify m a v) φ = evalF m φ ∧ Hereditary φ (verify m a v)`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: Fm, Hereditary, Marking, V, evalF, verify  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: For a HEREDITARY φ at m, monotonically resolving ANOTHER unverified atom (Z→T/F) within the SAME fixed formula, marking model and semantics leaves φ's verdict invariant and still hereditary. It is closure of a hereditary verdict under the allowed monotone resolution of a mark — nothing wider.
- **prohibited interpretation**: This is NARROW. It does NOT say a hereditary verdict is 'permanent', 'settled', or 'immune to further verification' in general. It does NOT remove the obligation to re-evaluate under expiry, revocation, correction, source invalidation, schema change, formula change, semantic-version change, or institutional admissibility — none of those is a monotone Z→T/F step in the same fixed model.
- **claim ceiling**: General over φ/m/a/v, given Hereditary φ m and the slot was Z. Invariance under one allowed monotone mark-resolution ONLY; not over any external event.
- **positive test vector** (human): φ hereditary at m; resolve some OTHER Z atom to T/F in the same marking → φ's verdict is unchanged and still hereditary.
- **adversarial test vector** (human): consumer treats a hereditary verdict as needing no re-check after an expiry / revocation / schema or semantic-version change → FAILS; those are outside this theorem's monotone-resolution scope.
- **expected Veraxis conformance**: A hereditary verdict does not require logical recomputation solely because another Z in the same fixed marking is monotonically resolved. It does NOT remove the obligation to re-evaluate external grounds, validity, admissibility, schema, or semantic version.
- **subject_kind**: `warranty_relation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.hereditary_absorbing"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `ZTime.grounded_hereditary`
- **canonical name**: `ZTime.grounded_hereditary`
- **statement**: `theorem grounded_hereditary {φ : Fm} {m : Marking} (hg : ∀ n, m n ≠ V.Z) : Hereditary φ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: Fm, Hereditary, Marking, V  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: Under the GLOBAL premise that no atom is unverified (∀ n, m n ≠ Z), every formula is hereditary: there is nothing left to refine, so the verdict is invariant under (the now-empty set of) monotone refinements.
- **prohibited interpretation**: This is a STRONG global SUFFICIENT condition on the whole marking, NOT a formula-local production rule: a partially grounded marking does not make a formula hereditary just because that formula's own atoms are set. Hereditary is still only monotone-refinement invariance, not expiry/revocation/correction-proof.
- **claim ceiling**: General over φ, given the whole marking is Z-free. Sufficient (full grounding ⇒ hereditary), not necessary, and not localisable to a formula's atoms.
- **positive test vector** (human): a globally Z-free marking → every φ hereditary.
- **adversarial test vector** (human): consumer applies this formula-locally ('φ's atoms are grounded, so φ is hereditary') under a marking with other Z atoms → FAILS; the premise is global.
- **expected Veraxis conformance**: Veraxis may treat verdicts hereditary only under a globally Z-free marking; partial grounding does not license it, even for formulas whose own atoms are set.
- **subject_kind**: `warranty_relation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.grounded_hereditary"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `ZTime.hereditary_sound`
- **canonical name**: `ZTime.hereditary_sound`
- **statement**: `theorem hereditary_sound {φ : Fm} {m : Marking} (hH : Hereditary φ m) : Sound φ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: Fm, Hereditary, Marking, Sound  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational interpretation**: A hereditary verdict is sound: if φ at m is HEREDITARY (its T is invariant under every allowed monotone refinement Z→T/F), then it is SOUND — it agrees with the verdict on ALL completions of the marking. The stronger scope implies the weaker.
- **prohibited interpretation**: SOUND means 'agrees with all completions', NOT 'truth about the facts of the world'. HEREDITARY means invariance under the allowed monotone refinements Z→T/F ONLY — it is NOT proof against expiry, revocation, correction, or schema change. A sound verdict must not be read as hereditary, nor either as world-truth.
- **claim ceiling**: General over all φ and m. hereditary ⇒ sound only; NOT the converse (sound need not be hereditary — measured separately). Both scopes are over monotone refinements/completions of the marking, not over world events.
- **positive test vector** (human): a formula/marking hereditary (its T invariant under every Z→T/F refinement) → it agrees with the verdict on all completions (sound).
- **adversarial test vector** (human): a consumer treats a sound (or even hereditary) verdict as proof against expiry/revocation/correction → FAILS; those are outside the refinement lattice this theorem ranges over.
- **expected Veraxis conformance**: Veraxis's grade ladder respects hereditary ⇒ sound and does not collapse them; neither grade is read as world-truth or as expiry/revocation-proof.
- **subject_kind**: `warranty_relation`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.hereditary_sound"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

### `ZTime.Witness.strict_ladder`
- **canonical name**: `ZTime.Witness.strict_ladder`
- **statement**: `theorem strict_ladder : (sound3 V.Z V.Z V.Z = false ∧ hered3 V.Z V.Z V.Z = false) ∧ (sound3 V.T V.Z V.Z = true ∧ hered3 V.T V.Z V.Z = false) ∧ hered3 V.T V.T V.Z = true`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd849973fdbda3d0a3f02b673983c4b3728064cd4842721b416307`
- **surface definitions referenced in statement**: V, hered3, sound3  _(substring scan, not a dependency graph)_
- **transitive theorem/definition closure**: DEFERRED (native Lean dependency extraction; supplied on request)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational interpretation**: The strict warranty ladder U→S→H is REALIZED rung by rung by an exhibited case: a verdict neither sound nor hereditary (Z,Z,Z), one sound-but-not-hereditary (T,Z,Z), and one hereditary (T,T,Z). The three grades are genuinely distinct.
- **prohibited interpretation**: A WITNESS that the grades separate, not a classification of all formulas; it exhibits one instance per rung.
- **claim ceiling**: A concrete finite construction (specific values). Proves the ladder is inhabited at each rung; does not enumerate which formulas sit where.
- **positive test vector** (human): the exhibited triples realize U, S, H respectively.
- **adversarial test vector** (human): consumer collapses sound and hereditary into one 'verified' grade → the sound-not-hereditary case would be wrongly settled.
- **expected Veraxis conformance**: Veraxis must carry all three grades distinctly; the sound-not-hereditary rung is real and revocable.
- **subject_kind**: `bounded_witness`
- **machine-readable fixtures**: `VERAXIS-ZTL-fixtures-v0.1.json` → `"ZTime.Witness.strict_ladder"` (`positive` / `adversarial`, typed by `subject_kind`; only the fields applicable to that kind are present)

