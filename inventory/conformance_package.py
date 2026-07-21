# -*- coding: utf-8 -*-
"""
conformance_package — the upstream semantic-review package for the Veraxis
candidate subset v0.1 (28 Lean declarations selected by A. Miteiko).

For each declaration it emits the thirteen fields Miteiko asked for. The
MECHANICAL fields (name, normalized statement, module + source hash, proof
scope, immediate dependent definitions, evidence status) are extracted; the
SEMANTIC fields (operational interpretation, prohibited interpretation,
claim ceiling, positive / adversarial test vectors, expected conformance
behaviour) are authored — that is the ZTL author's semantic-review role.

This first pass ships four fully-authored declarations as the format
sample — chosen to hit Miteiko's own concerns (¬¬Z must not be read as
grounded truth; DNE-elim's failure does not reject all double negations) —
with the remaining declarations carrying the mechanical fields and an
explicit TODO for the authored ones, pending format approval.

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
         "entails", "Refines", "Verify", "Hereditary", "Sound", "sound3",
         "hered3", "Fm", "Marking", "V"]


def _index():
    """Map every namespace-qualified name → (module, signature)."""
    idx = {}
    for m in aa.build_targets():
        for qname, sig in es.statements(m):
            idx[qname] = (m, sig)
    return idx


def _hash(module):
    data = open(os.path.join(_LEAN, module + ".lean"), "rb").read()
    return hashlib.sha256(data).hexdigest()[:16]


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
   "op": "A hereditary verdict is sound: if φ under marking m is hereditary "
         "(its T survives every partial refinement), then it is sound (never "
         "lies about the facts at m). The stronger warranty implies the weaker.",
   "no": "Soundness here is 'does not lie under the current marking', NOT "
         "'permanently settled' (that is hereditary). A merely-sound verdict "
         "must not be read as hereditary or as revocation-proof.",
   "ceil": "General over all φ and m. Establishes hereditary ⇒ sound only; NOT "
           "the converse (a sound verdict need not be hereditary — measured "
           "separately), and does not characterise which formulas are "
           "hereditary.",
   "pos": "a formula/marking that is hereditary (grounded atoms, stable T) → "
          "it is also sound.",
   "adv": "a sound-but-not-hereditary T (survives no-lie now, revoked under a "
          "later verification): a consumer treating sound as hereditary wrongly "
          "marks it settled → CONFORMANCE FAILS.",
   "conf": "Veraxis's grade ladder respects hereditary ⇒ sound and does NOT "
           "collapse the two; a sound-only verdict stays revocable.",
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
   "op": "Negating the mark computes F: ¬Z = F — the default-deny cell of the "
         "negation table.",
   "no": "F here is default-deny (no ground was offered), NOT a grounded "
         "negative fact about the atom; the atom stays Z.",
   "ceil": "Fixes one cell (¬ of Z is F). Nothing about ¬p for grounded p.",
   "pos": "atom Z → ¬(atom) = F (a default-deny verdict).",
   "adv": "consumer reports ¬(atom)=F as a grounded false fact → FAILS.",
   "conf": "Veraxis exposes ¬(atom)=F as default-deny, never as a grounded "
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
   "ceil": "Fixes the three cells of isZ. It is the ONLY sanctioned "
           "mark-detector; a generic predicate returns Z on a mark, not T.",
   "pos": "slot Z → isZ = T; slot T/F → isZ = F.",
   "adv": "consumer reads isZ=T as the atom being true → FAILS (detector, not "
          "assertion).",
   "conf": "Veraxis may use isZ to route/quarantine unverified slots; never as "
           "grounded truth.",
 },
 "V.no_gluts": {
   "op": "No gluts: no value makes both p and ¬p true. Paracomplete (a gap at "
         "Z) but NOT paraconsistent — a contradiction is never jointly "
         "asserted.",
   "no": "Does NOT give excluded middle (p∨¬p FALLS at Z). Absence of gluts ≠ "
         "presence of the middle.",
   "ceil": "Universal over values; the no-glut direction only. The companion "
           "gap (paracompleteness) is separate.",
   "pos": "any p → not (p=T and ¬p=T).",
   "adv": "consumer relies on explosion (p,¬p ⊨ anything) as if gluts existed "
          "→ gluts are absent, explosion is vacuous.",
   "conf": "Veraxis may rely on no-glut (never both affirmed and denied); it "
           "must not assume excluded middle.",
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
         "joint warrant is composable.",
   "no": "p∧q=T means both are jointly EARNED as verdicts, not that the "
         "conjoined objects are grounded-true in the world.",
   "ceil": "General; the intro direction (elim is separate).",
   "pos": "p=T, q=T → p∧q=T.",
   "adv": "consumer conjoins with a Z side → p∧q ≠ T; the mark blocks, no false "
          "joint warrant.",
   "conf": "Veraxis's join-by-∧ requires BOTH earned; a marked side blocks it.",
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
   "op": "Verifying an unverified slot is a refinement: setting a Z-atom to a "
         "verdict yields a marking that refines the original — verification "
         "only ever adds ground.",
   "no": "Says verification MOVES along the refinement order (adds ground), NOT "
         "that the verified value v is true — v could be F.",
   "ceil": "General over markings/atoms/values, given the slot was Z. No claim "
           "that v is correct.",
   "pos": "m a = Z → verify m a v refines m.",
   "adv": "consumer reads 'refines' as 'the new value is true' → it is about "
          "ground added, not the truth of v.",
   "conf": "Veraxis models verification as monotone refinement; the verified "
           "value's truth is a separate matter.",
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
   "op": "A fully grounded marking makes every formula hereditary: with no "
         "atom unverified there is nothing left to refine, so every verdict is "
         "permanent — ground buys permanence.",
   "no": "Requires FULL grounding (no Z anywhere). A partially grounded marking "
         "does NOT make all formulas hereditary; permanence is bought with "
         "ground, not asserted.",
   "ceil": "General over φ, given a Z-free marking. Sufficient condition (full "
           "grounding ⇒ hereditary), not necessary.",
   "pos": "a Z-free marking → every φ hereditary.",
   "adv": "consumer assumes a partially-verified marking gives permanent "
          "verdicts → only full grounding guarantees it.",
   "conf": "Veraxis may treat verdicts under a fully-grounded marking as "
           "permanent; partial grounding does not license it globally.",
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


def main():
    idx = _index()
    L = ["# VERAXIS–ZTL semantic-review package — candidate subset v0.1",
         "",
         "Upstream input for `VERAXIS-ZTL-CONFORMANCE-v0.1`. Every declaration "
         "below is `evidence_status: PROVED` on the empty axiom list at the "
         "pinned repository snapshot. Mechanical fields are extracted; the "
         "semantic fields are authored (ZTL-author semantic review). Four are "
         "fully authored as the format sample; the rest carry mechanical "
         "fields and an explicit TODO pending format approval.", ""]
    missing = []
    for group, names in SUBSET:
        L.append(f"## {group}\n")
        for qn in names:
            if qn not in idx:
                missing.append(qn); continue
            module, sig = idx[qn]
            _, scope = es.classify(module, sig)
            a = AUTHORED.get(qn)
            L.append(f"### `{qn}`")
            L.append(f"- **canonical name**: `{qn}`")
            L.append(f"- **statement**: `{_norm(sig)}`")
            L.append(f"- **module / source hash**: `{module}.lean` / "
                     f"`sha256:{_hash(module)}`")
            L.append(f"- **dependent definitions**: {', '.join(_deps(sig))}")
            L.append("- **transitive theorem deps**: (via Lean `#print`; "
                     "supplied on request — not hard-coded here)")
            L.append("- **evidence_status**: PROVED  ·  **proof_scope**: "
                     f"{scope}")
            if a:
                L.append(f"- **operational interpretation**: {a['op']}")
                L.append(f"- **prohibited interpretation**: {a['no']}")
                L.append(f"- **claim ceiling**: {a['ceil']}")
                L.append(f"- **positive test vector**: {a['pos']}")
                L.append(f"- **adversarial test vector**: {a['adv']}")
                L.append(f"- **expected Veraxis conformance**: {a['conf']}")
            else:
                L.append("- **operational / prohibited / ceiling / test "
                         "vectors / conformance**: _TODO — author on format "
                         "approval_")
            L.append("")
    if missing:
        L.append(f"> MISSING from the corpus: {missing}")
    path = os.path.join(_ROOT, "VERAXIS-ZTL-CONFORMANCE-input-v0.1.md")
    open(path, "w", encoding="utf-8").write("\n".join(L) + "\n")
    n = sum(len(v) for _, v in SUBSET)
    print(f"wrote {path}: {n} declarations, "
          f"{len(AUTHORED)} fully authored, {len(missing)} missing")


if __name__ == "__main__":
    main()
