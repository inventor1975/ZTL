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
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

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
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.lift2_classical`
- **canonical name**: `V.lift2_classical`
- **statement**: `theorem lift2_classical (f : Bool → Bool → Bool) (x y : V) : lift2 f x y = T ∨ lift2 f x y = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: V, lift2
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.evalF_classical`
- **canonical name**: `V.evalF_classical`
- **statement**: `theorem evalF_classical (v : Nat → V) : ∀ φ : Fm, (∃ n, φ = .atom n) ∨ evalF v φ = T ∨ evalF v φ = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: Fm, V, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.isZ_detects`
- **canonical name**: `V.isZ_detects`
- **statement**: `theorem isZ_detects : isZ Z = T ∧ isZ T = F ∧ isZ F = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: isZ
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.no_gluts`
- **canonical name**: `V.no_gluts`
- **statement**: `theorem no_gluts : ∀ p, ¬(p = T ∧ znot p = T)`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: znot
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

## Warrant-preserving and credit-rejecting inference

### `V.modus_ponens`
- **canonical name**: `V.modus_ponens`
- **statement**: `theorem modus_ponens : ∀ p q : V, p = T → zimp p q = T → q = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: V, zimp
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.rule_and_intro`
- **canonical name**: `V.rule_and_intro`
- **statement**: `theorem rule_and_intro : ∀ p q, p = T → q = T → zand p q = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zand
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.rule_and_elim`
- **canonical name**: `V.rule_and_elim`
- **statement**: `theorem rule_and_elim : ∀ p q, zand p q = T → p = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zand
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.rule_transitivity`
- **canonical name**: `V.rule_transitivity`
- **statement**: `theorem rule_transitivity : ∀ p q r, zimp p q = T → zimp q r = T → zimp p r = T`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zimp
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.dt_one_way`
- **canonical name**: `V.dt_one_way`
- **statement**: `theorem dt_one_way : zimp Z Z = F`
- **module / source hash**: `ZTL.lean` / `sha256:9bdb2d8e7f6dfd9f`
- **dependent definitions**: zimp
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: CONCRETE_CELL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

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
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

## Proof-engine correspondence

### `V.closes_iff`
- **canonical name**: `V.closes_iff`
- **statement**: `theorem closes_iff : ∀ (fuel : Nat) (e : Env) (ws : List Node), wsize ws < fuel → (∀ n, sIsEmpty (e n) = false) → (closes fuel e ws = true ↔ ¬ SAT e ws)`
- **module / source hash**: `TableauCert.lean` / `sha256:0a6e13c0e2b35655`
- **dependent definitions**: closes, sIsEmpty
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

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
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.tprovesN_iff`
- **canonical name**: `V.tprovesN_iff`
- **statement**: `theorem tprovesN_iff (ps : List Fm) (c : Fm) : tprovesN ps c = true ↔ ∀ v, (∀ p ∈ ps, evalF v p = T) → evalF v c = T`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c57`
- **dependent definitions**: Fm, evalF, tproves, tprovesN
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.engines_agree`
- **canonical name**: `V.engines_agree`
- **statement**: `theorem engines_agree (ps : List Fm) (c : Fm) : tprovesN ps c = tproves ps c`
- **module / source hash**: `TableauCertN.lean` / `sha256:2445af9c6e8e5c57`
- **dependent definitions**: Fm, tproves, tprovesN
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `V.entails_structural`
- **canonical name**: `V.entails_structural`
- **statement**: `theorem entails_structural (σ : Nat → Fm) (Γ : List Fm) (φ : Fm) (h : ∀ v, allT v Γ → evalF v φ = T) : ∀ v, allT v (substL σ Γ) → evalF v (substF σ φ) = T`
- **module / source hash**: `ZAlgebra.lean` / `sha256:a7c845303ba3d7b4`
- **dependent definitions**: Fm, entails, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

## Refinement and warranty structure

### `ZTime.refines_refl`
- **canonical name**: `ZTime.refines_refl`
- **statement**: `theorem refines_refl (m : Marking) : Refines m m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, Refines
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `ZTime.refines_trans`
- **canonical name**: `ZTime.refines_trans`
- **statement**: `theorem refines_trans {m₂ m₁ m : Marking} (h₂ : Refines m₂ m₁) (h₁ : Refines m₁ m) : Refines m₂ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, Refines
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `ZTime.verify_refines`
- **canonical name**: `ZTime.verify_refines`
- **statement**: `theorem verify_refines {m : Marking} {a : Nat} {v : V} (h : m a = V.Z) : Refines (verify m a v) m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, Refines, V
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `ZTime.evalF_congr`
- **canonical name**: `ZTime.evalF_congr`
- **statement**: `theorem evalF_congr {m' m : Marking} (h : ∀ n, m' n = m n) : ∀ φ, evalF m' φ = evalF m φ`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Marking, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `ZTime.hereditary_absorbing`
- **canonical name**: `ZTime.hereditary_absorbing`
- **statement**: `theorem hereditary_absorbing {φ : Fm} {m : Marking} {a : Nat} {v : V} (hH : Hereditary φ m) (ha : m a = V.Z) : evalF (verify m a v) φ = evalF m φ ∧ Hereditary φ (verify m a v)`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Fm, Hereditary, Marking, V, evalF
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

### `ZTime.grounded_hereditary`
- **canonical name**: `ZTime.grounded_hereditary`
- **statement**: `theorem grounded_hereditary {φ : Fm} {m : Marking} (hg : ∀ n, m n ≠ V.Z) : Hereditary φ m`
- **module / source hash**: `ZTime.lean` / `sha256:6e26d7ea75cd8499`
- **dependent definitions**: Fm, Hereditary, Marking, V
- **transitive theorem deps**: (via Lean `#print`; supplied on request — not hard-coded here)
- **evidence_status**: PROVED  ·  **proof_scope**: GENERAL
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

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
- **operational / prohibited / ceiling / test vectors / conformance**: _TODO — author on format approval_

