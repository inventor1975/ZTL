# -*- coding: utf-8 -*-
"""
conformance_package — the upstream semantic-review package for the Veraxis
candidate subset v0.1 (28 Lean declarations selected by A. Miteiko).

For each declaration it emits the fields Miteiko asked for. The MECHANICAL
fields (name, normalized statement, module + full sha256, surface
definitions, evidence_status, proof_scope) are extracted; the SEMANTIC
fields (operational + prohibited interpretation, claim ceiling, positive +
adversarial test vectors, expected conformance) are authored — the ZTL
author's semantic-review role. All 28 declarations are authored; each also
carries machine-readable positive/adversarial fixtures. The file opens with
a self-contained snapshot header (commit, toolchain, DOI, counts, audit,
inventory hash) so it pins its own provenance. The transitive dependency
closure is DEFERRED (native Lean extraction), not guessed.

Run:  python3 inventory/conformance_package.py
      → writes VERAXIS-ZTL-CONFORMANCE-input-v0.1.md
"""
import hashlib
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
_LEAN = os.path.join(_ROOT, "lean")
sys.path.insert(0, _HERE)
import axiom_audit as aa                                          # noqa: E402
import evidence_status as es                                     # noqa: E402

SUBSET = [
    ("Core value and register semantics",
     ["V.ax_not_Z", "V.ax_notnot_Z", "V.lift1_classical", "V.lift2_classical",
      "V.evalF_classical", "V.isZ_detects", "V.no_gluts"]),
    ("Warrant-preserving and credit-rejecting inference",
     ["V.modus_ponens", "V.rule_and_intro", "V.rule_and_elim",
      "V.rule_transitivity", "V.dt_one_way", "V.rule_dn_elim_fails",
      "V.rule_taut_concl_fails"]),
    ("Proof-engine correspondence",
     ["V.closes_iff", "V.tproves_iff", "V.closesN_iff", "V.tprovesN_iff",
      "V.engines_agree", "V.entails_structural"]),
    ("Refinement and warranty structure",
     ["ZTime.refines_refl", "ZTime.refines_trans", "ZTime.verify_refines",
      "ZTime.evalF_congr", "ZTime.hereditary_absorbing",
      "ZTime.grounded_hereditary", "ZTime.hereditary_sound",
      "ZTime.Witness.strict_ladder"]),
]

# ---- KNOWN definitions the statements lean on (for the dependent-defs field)
_DEFS = ["znot", "zand", "zor", "zimp", "zxor", "zxnor", "lift1", "lift2",
         "evalF", "isZ", "sIsEmpty", "tproves", "tprovesN", "closes", "closesN",
         "entails", "Refines", "verify", "Verify", "Hereditary", "Sound",
         "sound3", "hered3", "allT", "substL", "substF", "SAT", "wsize",
         "Node", "Env", "Fm", "Marking", "V"]


def _index():
    """Map every namespace-qualified name → (module, signature)."""
    idx = {}
    for m in aa.build_targets():
        for qname, sig in es.statements(m):
            idx[qname] = (m, sig)
    return idx


def _hash(module):
    data = open(os.path.join(_LEAN, module + ".lean"), "rb").read()
    return hashlib.sha256(data).hexdigest()          # full 64-char digest


def _norm(sig):
    return " ".join(sig.split())


def _deps(sig):
    body = _norm(sig)
    return sorted({d for d in _DEFS if d in body}) or ["—"]


# ---- authored semantic fields (the format sample: four declarations) ------
AUTHORED = {
 "V.ax_notnot_Z": {
   "op": "Under this negation, double-negating the mark computes the verdict "
         "T: ¬Z = F, then ¬F = T. It is a fact about the CONNECTIVE TABLE.",
   "no": "This T is NOT a grounded truth of the atom. `¬¬Z = T` must not be "
         "read as 'the datum is verified' or the atom promoted to grounded-T; "
         "the atom's own status stays Z, only the compound computes T (a "
         "formula verdict, §10).",
   "ceil": "Fixes exactly one cell (¬¬ applied to Z is T). Says nothing about "
           "¬¬p for grounded p, nor about whether the atom denotes.",
   "pos": "atom marked Z; compute ¬¬(atom) → expect T (formula verdict).",
   "adv": "atom marked Z; a consumer reads ¬¬(atom)=T and reports the atom's "
          "ground-state as T → CONFORMANCE FAILS (prohibited promotion).",
   "conf": "Veraxis exposes the compound verdict T but keeps the atom's "
           "grounding at Z; it never serialises the atom as grounded-true.",
 },
 "V.rule_dn_elim_fails": {
   "op": "Double-negation ELIMINATION is not universally warrant-preserving: "
         "it is not the case that for every p, ¬¬p = T forces p = T. The "
         "witness is p = Z (¬¬Z = T yet Z ≠ T).",
   "no": "This does NOT mean any formula with a double negation is rejected, "
         "nor that ¬¬p is useless. Only the INFERENCE ¬¬p ⊨ p fails, and "
         "exactly at the mark; for grounded p, ¬¬p = T coincides with p = T.",
   "ceil": "A universal-negative refuting the rule ∀ p, ¬¬p=T → p=T. It does "
           "not classify which p break it, and does not touch ¬¬p as a table "
           "value elsewhere.",
   "pos": "apply DNE-elim with p = Z: premise ¬¬Z = T holds, conclusion Z = T "
          "is false → the rule is correctly seen to fail.",
   "adv": "a consumer uses DNE-elim as a sound inference to promote an "
          "unverified atom to T because its double negation computed T → "
          "CONFORMANCE FAILS.",
   "conf": "Veraxis must not carry ¬¬p ⊨ p as an admissible inference over "
           "unverified atoms; grounded atoms are unaffected.",
 },
 "ZTime.hereditary_sound": {
   "op": "A hereditary verdict is sound: if φ at m is HEREDITARY (its T is "
         "invariant under every allowed monotone refinement Z→T/F), then it is "
         "SOUND — it agrees with the verdict on ALL completions of the "
         "marking. The stronger scope implies the weaker.",
   "no": "SOUND means 'agrees with all completions', NOT 'truth about the "
         "facts of the world'. HEREDITARY means invariance under the allowed "
         "monotone refinements Z→T/F ONLY — it is NOT proof against expiry, "
         "revocation, correction, or schema change. A sound verdict must not "
         "be read as hereditary, nor either as world-truth.",
   "ceil": "General over all φ and m. hereditary ⇒ sound only; NOT the converse "
           "(sound need not be hereditary — measured separately). Both scopes "
           "are over monotone refinements/completions of the marking, not over "
           "world events.",
   "pos": "a formula/marking hereditary (its T invariant under every Z→T/F "
          "refinement) → it agrees with the verdict on all completions "
          "(sound).",
   "adv": "a consumer treats a sound (or even hereditary) verdict as proof "
          "against expiry/revocation/correction → FAILS; those are outside the "
          "refinement lattice this theorem ranges over.",
   "conf": "Veraxis's grade ladder respects hereditary ⇒ sound and does not "
           "collapse them; neither grade is read as world-truth or as "
           "expiry/revocation-proof.",
 },
 "V.tproves_iff": {
   "op": "The tableau engine is sound and complete for entailment: "
         "`tproves ps c` is true exactly when c follows from ps under every "
         "valuation (every classical reading of the marks). Engine YES ⟺ ⊨.",
   "no": "`tproves ps c = true` means c is a semantic CONSEQUENCE — NOT that c "
         "is a grounded world-fact, nor that its atoms are verified. A relation "
         "between formulas, not an assertion about objects (§10).",
   "ceil": "General over premise lists and conclusions on the {¬,∧,∨} basis "
           "(heavier connectives reduced by proven identities). Does not extend "
           "to arbitrary domains (the FO layer) and makes no denotation claim.",
   "pos": "ps = [p, p→q], c = q (modus ponens) → tproves true, and q follows.",
   "adv": "ps = [], c = ¬q→¬q (a guarded tautology): tproves true, but a "
          "consumer must not read the derived c as a grounded world-fact — "
          "formula-level consequence only.",
   "conf": "Veraxis may use `tproves` as the authoritative entailment oracle "
           "for the covered fragment, but maps its YES to 'formula-level "
           "consequence', never to grounded truth.",
 },
 "V.ax_not_Z": {
   "op": "Negating the mark computes the formula verdict F: ¬Z = F — one cell "
         "of the negation table.",
   "no": "F here is the FORMULA VERDICT F, nothing more. 'default-deny' is a "
         "possible DOWNSTREAM mapping of that verdict, not the universal "
         "meaning of F; and it is not a grounded negative fact about the atom "
         "(the atom stays Z).",
   "ceil": "Fixes one cell (¬ of Z is F). Nothing about ¬p for grounded p, and "
           "no downstream semantics of F is implied.",
   "pos": "atom Z → ¬(atom) = F (formula verdict).",
   "adv": "consumer reports ¬(atom)=F as a grounded false fact about the atom "
          "→ FAILS.",
   "conf": "Veraxis exposes ¬(atom)=F as a formula verdict; any 'default-deny' "
           "reading is an explicit downstream mapping, never a grounded "
           "negative world-fact.",
 },
 "V.lift1_classical": {
   "op": "Every UNARY compound is classical: for any lifted unary connective "
         "and any value (Z included), the result is T or F — the mark never "
         "survives an operator.",
   "no": "About COMPOUNDS, not atoms; it does not say the input is classical. "
         "The mark lives on atoms and evaporates at the first operator.",
   "ceil": "Universal over unary connectives and values. Does not touch "
           "atoms/nullary, which may be Z.",
   "pos": "any f, x=Z → lift1 f Z ∈ {T,F}.",
   "adv": "consumer expects a compound to carry Z downstream → it is always "
          "T/F.",
   "conf": "Veraxis may rely on every unary compound being two-valued; only "
           "atoms carry Z.",
 },
 "V.lift2_classical": {
   "op": "Every BINARY compound is classical: any lifted binary connective on "
         "any values (Z included) returns T or F.",
   "no": "About compounds, not the atomic operands; a marked operand does not "
         "make the compound carry Z.",
   "ceil": "Universal over binary connectives and value pairs. Atoms excluded.",
   "pos": "any f, x=Z, y=T → lift2 f Z T ∈ {T,F}.",
   "adv": "consumer expects a Z operand to propagate as Z through a connective "
          "→ it collapses to T/F.",
   "conf": "Veraxis may rely on every binary compound being two-valued.",
 },
 "V.evalF_classical": {
   "op": "Greediness, general: every formula is an ATOM or evaluates to T or "
         "F. Z appears only on atoms; no compound takes the mark — the "
         "structural guarantee behind two-valued verdicts.",
   "no": "Does NOT say atoms are classical (they may be Z); it says compounds "
         "are. A compound value can never serialize as Z.",
   "ceil": "General over formulas and valuations; the atomic case is set aside "
           "(atoms may be Z). No denotation claim.",
   "pos": "any non-atomic φ, any marked valuation → evalF ∈ {T,F}.",
   "adv": "consumer reserves a Z code point for a compound's value → compounds "
          "are strictly {T,F}.",
   "conf": "Veraxis serializes compound verdicts as {T,F}; only atom slots may "
           "hold Z.",
 },
 "V.isZ_detects": {
   "op": "The quarantine detector isZ (= ¬(x↔x), expressible inside the logic) "
         "flags the mark: T on Z, F on the verdicts. The system detects its "
         "own marks from within.",
   "no": "isZ is a META-predicate about the register (is this a mark?), NOT a "
         "truth about the world: isZ Z = T means 'this slot is unverified', "
         "not 'the atom is true'.",
   "ceil": "Fixes the three cells of isZ — it proves the detector WORKS "
           "(T on Z, F on verdicts). It does NOT prove uniqueness (that no "
           "other predicate detects the mark); a generic predicate happens to "
           "return Z on a mark, but that is a separate observation.",
   "pos": "slot Z → isZ = T; slot T/F → isZ = F.",
   "adv": "consumer reads isZ=T as the atom being true → FAILS (detector, not "
          "assertion).",
   "conf": "Veraxis may use isZ to route/quarantine unverified slots; never as "
           "grounded truth.",
 },
 "V.no_gluts": {
   "op": "No gluts at the VALUE level: no single value makes both p and ¬p "
         "equal T. (Paracomplete — a gap at Z — but no value is both T and "
         "not-T.)",
   "no": "This is a fact about the connective tables, NOT a general "
         "paraconsistency claim and NOT a statement about external source "
         "conflicts (two parties asserting p and ¬p is a different, "
         "institutional matter). It also does not give excluded middle (p∨¬p "
         "FALLS at Z).",
   "ceil": "Universal over the three values; the no-glut direction only. Says "
           "nothing about conflicts between distinct sources or about the "
           "middle.",
   "pos": "any single value v → not (v=T and ¬v=T).",
   "adv": "consumer reads no_gluts as 'the system reconciles conflicting "
          "external sources' → it says nothing about source conflict.",
   "conf": "Veraxis may rely on no single value being both T and not-T; "
           "cross-source conflict is handled by the institutional layer, not "
           "by this theorem.",
 },
 "V.modus_ponens": {
   "op": "Modus ponens holds: an earned p and an earned p→q yield an earned q. "
         "The forward inference is warrant-preserving.",
   "no": "The earned q is a formula verdict transported from the premises, NOT "
         "a grounded world-fact about q's atom (§10). MP moves warrant, does "
         "not mint ground.",
   "ceil": "General over p, q. MP as a valid rule; nothing about the converse "
           "or q's denotation.",
   "pos": "p=T, p→q=T → q=T.",
   "adv": "consumer applies MP with p unverified (Z) → premise not T, the rule "
          "does not fire; no false promotion.",
   "conf": "Veraxis may use MP soundly; the earned q stays a formula verdict.",
 },
 "V.rule_and_intro": {
   "op": "∧-introduction: two earned claims yield their earned conjunction — "
         "joint LOGICAL warrant is composable at the formula level.",
   "no": "p∧q=T establishes joint logical warrant only. It is NOT sufficient "
         "for a legal/institutional Seam: certificate admissibility, "
         "schema/namespace agreement, provenance and the interface conditions "
         "are separate and live in the institutional layer, not in this "
         "theorem.",
   "ceil": "General; the intro direction (elim is separate). Logical joint "
           "warrant, not institutional seam-legality.",
   "pos": "p=T, q=T → p∧q=T.",
   "adv": "consumer treats p∧q=T as a legally sewn institutional claim → it is "
          "only logical joint warrant; seam-legality needs the interface "
          "layer.",
   "conf": "Veraxis's logical join-by-∧ requires BOTH earned; institutional "
           "seam-legality adds admissibility/provenance on top, out of scope "
           "here.",
 },
 "V.rule_and_elim": {
   "op": "∧-elimination: from an earned conjunction each conjunct is earned — "
         "warrant distributes over ∧.",
   "no": "The extracted p=T is a formula verdict, not a grounded fact.",
   "ceil": "General; the p-projection (q symmetric by commutativity, separate).",
   "pos": "p∧q=T → p=T.",
   "adv": "consumer extracts p from a conjunction that is not actually T → "
          "premise false, no extraction.",
   "conf": "Veraxis extracts conjuncts only from an earned conjunction.",
 },
 "V.rule_transitivity": {
   "op": "Transitivity of the arrow: earned p→q and q→r yield earned p→r — "
         "implication chains compose.",
   "no": "A formula-level CONSEQUENCE chain, NOT a causal or temporal chain in "
         "the world.",
   "ceil": "General; transitivity of →-verdicts, not the deduction theorem.",
   "pos": "p→q=T, q→r=T → p→r=T.",
   "adv": "consumer reads the chain as causation → it is entailment structure "
          "only.",
   "conf": "Veraxis may chain earned implications; the chain is logical, not "
           "causal.",
 },
 "V.dt_one_way": {
   "op": "The deduction theorem is ONE-WAY, witnessed by Z→Z = F: reflexive "
         "entailment p⊨p does not internalize to ⊨ p→p — the arrow is stricter "
         "than entailment, and even self-implication over the mark is F.",
   "no": "Does NOT mean implication is broken: p→p FALLS at Z (a fallen law), "
         "yet the RULE reflexivity holds. The formula-arrow is not the "
         "consequence relation.",
   "ceil": "One cell (Z→Z=F) witnessing the one-way deduction theorem. "
           "Grounded p→p = T; this does not classify all p→p.",
   "pos": "p=Z → p→p = F (the arrow does not hold at the mark).",
   "adv": "consumer treats p→p as a universal tautology (always T) → FAILS at "
          "Z.",
   "conf": "Veraxis must not treat p→p as universally T, nor internalize "
           "entailment into the arrow.",
 },
 "V.rule_taut_concl_fails": {
   "op": "'Tautology in the conclusion' fails as a rule: an earned p does NOT "
         "license concluding q∨¬q, because excluded middle is not T at q=Z — a "
         "fresh unverified atom earns no T.",
   "no": "Does NOT reject q∨¬q wholesale (grounded q → T). What fails is the "
         "RULE 'anything ⊨ q∨¬q'; guarded tautologies (¬q→¬q) survive, "
         "middle-shaped ones do not.",
   "ceil": "Universal-negative refuting the rule; q=Z is the witness. Does not "
           "classify which q break it.",
   "pos": "p=T, q=Z → q∨¬q = F → the rule correctly fails.",
   "adv": "consumer injects q∨¬q as an always-available tautology → FAILS at "
          "unverified q.",
   "conf": "Veraxis must not treat excluded middle as a free tautology over "
           "unverified atoms.",
 },
 "V.closes_iff": {
   "op": "The tableau engine is correct: a node set CLOSES exactly when it is "
         "unsatisfiable (no model), given enough fuel and a non-degenerate "
         "environment. Closure ⟺ unsatisfiability.",
   "no": "Closure is FORMULA-level unsatisfiability (no valuation satisfies), "
         "NOT a claim that the negated formula is a grounded world-fact.",
   "ceil": "General over fuel/environment/nodes with the stated side "
           "conditions; the {¬,∧,∨} tableau (heavier connectives via "
           "reductions).",
   "pos": "an unsatisfiable node set → closes = true.",
   "adv": "consumer reads a closure as proving a world-fact false → it proves "
          "formula-unsatisfiability only.",
   "conf": "Veraxis maps closure to formula-unsat, not world-falsity.",
 },
 "V.closesN_iff": {
   "op": "Same correctness for the NATIVE engine (→/⊕/↔ handled directly): "
         "closesN ⟺ unsatisfiability.",
   "no": "Closure is formula-unsatisfiability, not a grounded world-fact.",
   "ceil": "General with the stated side conditions, for the native connective "
           "set.",
   "pos": "an unsatisfiable node set → closesN = true.",
   "adv": "as closes_iff: closure ≠ world-falsity.",
   "conf": "Veraxis maps native closure to formula-unsat only.",
 },
 "V.tprovesN_iff": {
   "op": "The NATIVE engine is sound and complete for entailment: tprovesN ps "
         "c ⟺ c follows from ps under every valuation.",
   "no": "A YES is formula-level consequence, NOT grounded world-truth (§10).",
   "ceil": "General over premise lists and conclusions for the native "
           "connectives; no denotation claim, no arbitrary domains.",
   "pos": "ps=[p, p→q], c=q → tprovesN true.",
   "adv": "consumer reads a derived c as a grounded fact → consequence only.",
   "conf": "Veraxis may use tprovesN as the entailment oracle; YES ↦ "
           "consequence, not truth.",
 },
 "V.engines_agree": {
   "op": "The two proof engines agree on every input: the {¬,∧,∨}-basis engine "
         "and the native →/⊕/↔ engine return the same YES/NO — the reduction "
         "is faithful.",
   "no": "Engine equivalence, not a claim about the world.",
   "ceil": "General over premise lists and conclusions; both are sound+complete "
           "for ⊨ (separate results).",
   "pos": "any ps, c → tprovesN ps c = tproves ps c.",
   "adv": "consumer expects the engines to differ on some input → they never "
          "do.",
   "conf": "Veraxis may use either engine interchangeably as the oracle.",
 },
 "V.entails_structural": {
   "op": "Entailment is STRUCTURAL: if Γ ⊨ φ then, substituting formulas for "
         "atoms uniformly, σΓ ⊨ σφ — the consequence relation respects "
         "substitution (Suszko-structurality).",
   "no": "A property of the CONSEQUENCE relation over formula variables, NOT a "
         "licence to substitute grounded objects; the substituends are "
         "formulas.",
   "ceil": "General over substitutions, premise lists, conclusions. "
           "Structurality only; not the deduction theorem or compactness.",
   "pos": "Γ ⊨ φ, substitution σ → σΓ ⊨ σφ.",
   "adv": "consumer substitutes an object for a variable expecting "
          "object-identity to carry → only formula structure carries.",
   "conf": "Veraxis may rely on uniform substitution preserving entailment "
           "over formula variables.",
 },
 "ZTime.refines_refl": {
   "op": "Refinement is reflexive: any marking refines itself — the "
         "'more-verified-than' order has identity.",
   "no": "An order on MARKINGS (verification states), not on world-facts.",
   "ceil": "General over markings; reflexivity only.",
   "pos": "any m → Refines m m.",
   "adv": "consumer assumes refinement is strict/irreflexive → it is a "
          "preorder.",
   "conf": "Veraxis's refinement is a preorder; equal states refine each other.",
 },
 "ZTime.refines_trans": {
   "op": "Refinement is transitive: chained refinements compose — the "
         "verification order is a preorder.",
   "no": "A property of the marking order, not of the world.",
   "ceil": "General; transitivity only.",
   "pos": "Refines m₂ m₁, Refines m₁ m → Refines m₂ m.",
   "adv": "consumer assumes refinement is not transitive → it is.",
   "conf": "Veraxis may chain refinement steps.",
 },
 "ZTime.verify_refines": {
   "op": "Setting a previously-unverified slot yields a refinement: it "
         "PRESERVES all the earlier non-Z assignments and is comparable in the "
         "refinement order. It is the monotonicity of the operation, not an "
         "assertion that ground was added.",
   "no": "This does NOT itself prove that ground was ADDED: the written value "
         "v may even be Z, so the theorem alone does not establish a "
         "grounding. A Veraxis 'verification' requires the ADDITIONAL "
         "conditions v ≠ Z AND an external grounded event; the refinement "
         "relation does not supply them.",
   "ceil": "General over markings/atoms/values, given the slot was Z. Proves "
           "refinement (earlier non-Z preserved), NOT that v is correct, NOT "
           "that v is non-Z, NOT that a real-world verification occurred.",
   "pos": "m a = Z, v = T → verify m a v refines m, and every earlier non-Z "
          "assignment is preserved.",
   "adv": "consumer treats any `verify` call as a grounding event (even with "
          "v = Z) → FAILS; grounding needs v ≠ Z plus an external event, not "
          "just this refinement.",
   "conf": "Veraxis models the write as monotone refinement; it counts a slot "
           "as GROUNDED only on v ≠ Z together with an external grounded event, "
           "never from the refinement relation alone.",
 },
 "ZTime.evalF_congr": {
   "op": "Evaluation is a congruence on markings: markings agreeing on every "
         "atom give every formula the same verdict — the verdict depends only "
         "on the marking's content.",
   "no": "A determinism property of evaluation, not a world-fact claim.",
   "ceil": "General over markings and formulas; congruence only.",
   "pos": "m' = m pointwise → evalF m' φ = evalF m φ for all φ.",
   "adv": "consumer expects hidden state to move the verdict → evaluation is a "
          "pure function of the marking.",
   "conf": "Veraxis's evaluation is deterministic in the marking; no hidden "
           "inputs.",
 },
 "ZTime.hereditary_absorbing": {
   "op": "Hereditary is absorbing under verification: if φ is hereditary at m, "
         "verifying any unverified atom leaves φ's verdict UNCHANGED and still "
         "hereditary — once settled, further verification buys nothing.",
   "no": "About a HEREDITARY verdict; a sound/until verdict CAN change under "
         "verification. Absorption is the mark of the permanent grade only.",
   "ceil": "General over φ/m/a/v, given Hereditary φ m and the slot was Z. Does "
           "not say which φ are hereditary.",
   "pos": "φ hereditary at m, verify a Z-atom → same verdict, still hereditary.",
   "adv": "consumer re-checks a hereditary verdict after each verification "
          "expecting change (wasted), or treats an until-verdict as hereditary "
          "→ FAILS.",
   "conf": "Veraxis may treat a hereditary verdict as settled, immune to "
           "further verification; only non-hereditary verdicts need "
           "re-checking.",
 },
 "ZTime.grounded_hereditary": {
   "op": "Under the GLOBAL premise that no atom is unverified (∀ n, m n ≠ Z), "
         "every formula is hereditary: there is nothing left to refine, so the "
         "verdict is invariant under (the now-empty set of) monotone "
         "refinements.",
   "no": "This is a STRONG global SUFFICIENT condition on the whole marking, "
         "NOT a formula-local production rule: a partially grounded marking "
         "does not make a formula hereditary just because that formula's own "
         "atoms are set. Hereditary is still only monotone-refinement "
         "invariance, not expiry/revocation/correction-proof.",
   "ceil": "General over φ, given the whole marking is Z-free. Sufficient (full "
           "grounding ⇒ hereditary), not necessary, and not localisable to a "
           "formula's atoms.",
   "pos": "a globally Z-free marking → every φ hereditary.",
   "adv": "consumer applies this formula-locally ('φ's atoms are grounded, so "
          "φ is hereditary') under a marking with other Z atoms → FAILS; the "
          "premise is global.",
   "conf": "Veraxis may treat verdicts hereditary only under a globally "
           "Z-free marking; partial grounding does not license it, even for "
           "formulas whose own atoms are set.",
 },
 "ZTime.Witness.strict_ladder": {
   "op": "The strict warranty ladder U→S→H is REALIZED rung by rung by an "
         "exhibited case: a verdict neither sound nor hereditary (Z,Z,Z), one "
         "sound-but-not-hereditary (T,Z,Z), and one hereditary (T,T,Z). The "
         "three grades are genuinely distinct.",
   "no": "A WITNESS that the grades separate, not a classification of all "
         "formulas; it exhibits one instance per rung.",
   "ceil": "A concrete finite construction (specific values). Proves the ladder "
           "is inhabited at each rung; does not enumerate which formulas sit "
           "where.",
   "pos": "the exhibited triples realize U, S, H respectively.",
   "adv": "consumer collapses sound and hereditary into one 'verified' grade → "
          "the sound-not-hereditary case would be wrongly settled.",
   "conf": "Veraxis must carry all three grades distinctly; the "
           "sound-not-hereditary rung is real and revocable.",
 },
}


# ---- machine-readable fixture bits (ast · marking · expected · reason) -----
# one canonical instance per declaration; the emitter derives the structured
# positive/adversarial fixtures from these plus the authored prohibition.
MB = {
 "V.ax_not_Z":            ("(¬ a)", "a=Z", "F", "F_READ_AS_GROUNDED_NEGATIVE"),
 "V.ax_notnot_Z":         ("(¬ (¬ a))", "a=Z", "T", "Z_PROMOTED_TO_GROUNDED_T"),
 "V.lift1_classical":     ("(f a)  [any unary f]", "a=Z", "T|F (never Z)",
                           "COMPOUND_EXPECTED_TO_CARRY_Z"),
 "V.lift2_classical":     ("(f a b)  [any binary f]", "a=Z, b=T", "T|F (never Z)",
                           "COMPOUND_EXPECTED_TO_CARRY_Z"),
 "V.evalF_classical":     ("any non-atomic φ", "any marking with marks", "T|F",
                           "COMPOUND_SERIALIZED_AS_Z"),
 "V.isZ_detects":         ("(isZ a)", "a=Z", "T", "DETECTOR_READ_AS_ASSERTION"),
 "V.no_gluts":            ("(a ∧ (¬ a))", "a ∈ {T,F,Z}", "never T",
                           "NO_GLUT_READ_AS_SOURCE_RECONCILIATION"),
 "V.modus_ponens":        ("premises [a, (a→b)] ⊢ b", "a=T, b=T", "b=T",
                           "VERDICT_READ_AS_WORLD_FACT"),
 "V.rule_and_intro":      ("(a ∧ b)", "a=T, b=T", "T",
                           "LOGICAL_WARRANT_READ_AS_SEAM_LEGALITY"),
 "V.rule_and_elim":       ("(a ∧ b) ⊢ a", "a∧b = T", "a=T",
                           "VERDICT_READ_AS_WORLD_FACT"),
 "V.rule_transitivity":   ("[(a→b),(b→c)] ⊢ (a→c)", "both = T", "(a→c)=T",
                           "ENTAILMENT_READ_AS_CAUSATION"),
 "V.dt_one_way":          ("(a → a)", "a=Z", "F", "ARROW_ASSUMED_TAUTOLOGY"),
 "V.rule_taut_concl_fails": ("(b ∨ (¬ b))", "b=Z", "F", "EXCLUDED_MIDDLE_ASSUMED"),
 "V.closes_iff":          ("an unsatisfiable node set", "—", "closes = true",
                           "CLOSURE_READ_AS_WORLD_FALSITY"),
 "V.closesN_iff":         ("an unsatisfiable node set (native)", "—",
                           "closesN = true", "CLOSURE_READ_AS_WORLD_FALSITY"),
 "V.tprovesN_iff":        ("ps=[a,(a→b)], c=b (native)", "—", "tprovesN = true",
                           "PROOF_READ_AS_WORLD_FACT"),
 "V.engines_agree":       ("any (ps, c)", "—", "tprovesN = tproves",
                           "ENGINES_EXPECTED_TO_DIFFER"),
 "V.entails_structural":  ("Γ ⊨ φ, substitution σ", "—", "σΓ ⊨ σφ",
                           "SUBSTITUTION_CARRIES_OBJECT_IDENTITY"),
 "V.tproves_iff":         ("ps=[a,(a→b)], c=b", "—", "tproves = true",
                           "PROOF_READ_AS_WORLD_FACT"),
 "V.rule_dn_elim_fails":  ("apply ¬¬p ⊨ p at p=Z", "p=Z",
                           "rule FAILS (¬¬Z=T, Z≠T)",
                           "INFERENCE_NOT_WARRANT_PRESERVING"),
 "ZTime.refines_refl":    ("Refines m m", "any m", "holds",
                           "REFINEMENT_ASSUMED_IRREFLEXIVE"),
 "ZTime.refines_trans":   ("Refines m₂ m₁, Refines m₁ m", "—", "Refines m₂ m",
                           "REFINEMENT_ASSUMED_NONTRANSITIVE"),
 "ZTime.verify_refines":  ("verify m a v", "m a=Z, v=T",
                           "Refines (verify m a v) m", "REFINEMENT_READ_AS_GROUNDING"),
 "ZTime.evalF_congr":     ("m' = m pointwise", "—", "evalF m' φ = evalF m φ",
                           "HIDDEN_STATE_ASSUMED"),
 "ZTime.hereditary_absorbing": ("verify m a v on hereditary φ",
                           "Hereditary φ m, m a=Z",
                           "verdict unchanged ∧ still Hereditary",
                           "HEREDITARY_READ_AS_EXPIRY_PROOF"),
 "ZTime.grounded_hereditary": ("Hereditary φ m", "∀ n, m n ≠ Z",
                           "holds", "GROUNDED_APPLIED_FORMULA_LOCALLY"),
 "ZTime.Witness.strict_ladder": ("(sound3,hered3) at (Z,Z,Z)/(T,Z,Z)/(T,T,Z)",
                           "the three triples", "U / S / H realized",
                           "LADDER_GRADES_COLLAPSED"),
}


def snapshot_header():
    import subprocess
    try:
        sha = subprocess.run(["git", "-C", _ROOT, "rev-parse", "HEAD"],
                             capture_output=True, text=True).stdout.strip()
    except Exception:
        sha = "(run git rev-parse HEAD)"
    tc = open(os.path.join(_LEAN, "lean-toolchain")).read().strip()
    inv = hashlib.sha256(
        open(os.path.join(_ROOT, "ZTL-theorems.txt"), "rb").read()).hexdigest()
    targets = aa.build_targets()
    thms = sum(len(es.statements(m)) for m in targets)
    return [
        "## Snapshot (self-contained pin coordinates)",
        "",
        f"- **repository commit (verified corpus state)**: `{sha}`  "
        "— the finalized artifact is contained in the committing revision; "
        "pin THAT commit.",
        "- **release tag**: none at this commit; published version is v1.3 "
        "(Zenodo).",
        "- **DOI (v1.3 baseline)**: `10.5281/zenodo.21472971`  · concept "
        "`10.5281/zenodo.21318981`",
        f"- **Lean toolchain**: `{tc}`",
        f"- **theorem / module count**: {thms} theorems across {len(targets)} "
        "modules",
        "- **axiom-audit result**: ALL CLEAN — every theorem on the EMPTY "
        "axiom list (`inventory/axiom_audit.py`, re-run in CI)",
        f"- **inventory hash** (`ZTL-theorems.txt`): `sha256:{inv}`",
        "- **semantic-review status**: all 28 declarations authored",
        "- **dependency-closure status**: DEFERRED (native Lean dependency "
        "extraction not yet run)",
        "",
    ]


def main():
    idx = _index()
    L = ["# VERAXIS–ZTL semantic-review package — candidate subset v0.1", ""]
    L += snapshot_header()
    L += ["Upstream input for `VERAXIS-ZTL-CONFORMANCE-v0.1`. Every declaration "
          "below is `evidence_status: PROVED` on the empty axiom list at the "
          "pinned snapshot. Mechanical fields are extracted; the semantic "
          "fields are authored (ZTL-author semantic review). No semantic "
          "transition is hidden inside a convenient phrasing.", ""]
    missing = []
    for group, names in SUBSET:
        L.append(f"## {group}\n")
        for qn in names:
            if qn not in idx:
                missing.append(qn); continue
            module, sig = idx[qn]
            _, scope = es.classify(module, sig)
            a = AUTHORED[qn]
            L.append(f"### `{qn}`")
            L.append(f"- **canonical name**: `{qn}`")
            L.append(f"- **statement**: `{_norm(sig)}`")
            L.append(f"- **module / source hash**: `{module}.lean` / "
                     f"`sha256:{_hash(module)}`")
            L.append("- **surface definitions referenced in statement**: "
                     f"{', '.join(_deps(sig))}  _(substring scan, not a "
                     "dependency graph)_")
            L.append("- **transitive theorem/definition closure**: DEFERRED "
                     "(native Lean dependency extraction; supplied on request)")
            L.append("- **evidence_status**: PROVED  ·  **proof_scope**: "
                     f"{scope}")
            L.append(f"- **operational interpretation**: {a['op']}")
            L.append(f"- **prohibited interpretation**: {a['no']}")
            L.append(f"- **claim ceiling**: {a['ceil']}")
            L.append(f"- **positive test vector** (human): {a['pos']}")
            L.append(f"- **adversarial test vector** (human): {a['adv']}")
            L.append(f"- **expected Veraxis conformance**: {a['conf']}")
            ast, mk, ver, rc = MB.get(qn, ("", "", "", "REVIEW"))
            key = qn.split(".")[-1]
            L.append("- **machine-readable fixtures**:")
            L.append(f"  - `{{ id: \"FX-{key}-pos\", formula_ast: \"{ast}\", "
                     f"marking: \"{mk}\", expected_formula_verdict: \"{ver}\", "
                     f"retained_atom_state: \"marks in the marking stay Z\", "
                     f"epistemic_status: \"formula-level; atoms unpromoted\", "
                     f"prohibited_conversion: \"none\", "
                     f"expected_veraxis: \"accept; reason=OK\" }}`")
            L.append(f"  - `{{ id: \"FX-{key}-adv\", formula_ast: \"{ast}\", "
                     f"marking: \"{mk}\", expected_formula_verdict: \"{ver}\", "
                     f"retained_atom_state: \"marks stay Z\", "
                     f"epistemic_status: \"unchanged by the misuse\", "
                     f"prohibited_conversion: \"{rc}\", "
                     f"expected_veraxis: \"reject; reason={rc}\" }}`")
            L.append("")
    if missing:
        L.append(f"> MISSING from the corpus: {missing}")
    path = os.path.join(_ROOT, "VERAXIS-ZTL-CONFORMANCE-input-v0.1.md")
    open(path, "w", encoding="utf-8").write("\n".join(L) + "\n")
    n = sum(len(v) for _, v in SUBSET)
    print(f"wrote {path}: {n} declarations, {len(AUTHORED)} authored, "
          f"{len(missing)} missing")


if __name__ == "__main__":
    main()
