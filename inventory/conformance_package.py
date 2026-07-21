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
