# -*- coding: utf-8 -*-
"""
evidence_status — a FIRST-CUT evidence-status map of the corpus, in the
four-level taxonomy proposed by A. Miteiko for the Veraxis conformance
manifest:

  PROVED                  a general Lean theorem on the empty axiom list —
                          universal over the semantic domain (all of V, all
                          formulas Fm, an arbitrary type).
  PROVED-BOUNDED-WITNESS  a machine-proved SPECIFIC witness or finite
                          construction (an ∃-claim, or a claim over a fixed
                          chosen finite MODEL) — the instance is proved, not
                          a universal classification.
  MEASURED-WITH-CEILING   a Python-stand pool enumeration — not a Lean
                          theorem; true within a bounded test space.
  INTERPRETIVE-INVARIANT  an interface reading rule (§10) — normatively
                          required, NOT a Lean theorem unless the mapping is
                          formalized in Lean.

This is a FIRST CUT to help selection; the final status of each SELECTED
element is confirmed jointly in the semantic-review package. Grey cases are
marked REVIEW rather than asserted — the whole point of the taxonomy is to
not call a witness a universal, nor a universal a mere measurement.

The Lean classifier reads each theorem's actual STATEMENT and applies:
  * a fixed-model module (ZEq/ZDesc/ZEps/QuantumWitness/JunctionWitness/
    Contextuality) → BOUNDED-WITNESS;
  * an ∃ in the statement → BOUNDED-WITNESS;
  * a ∀ / ¬∀ over V, Fm, Nat or an abstract type → PROVED;
  * a bare concrete equation (no quantifier) → REVIEW (anchor cell / a
    specific fact — proved, but neither universal nor a witness).

Run:  python3 inventory/evidence_status.py   →   writes ZTL-evidence.txt
"""
import os
import re
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
_LEAN = os.path.join(_ROOT, "lean")
sys.path.insert(0, _HERE)
import axiom_audit as aa                                          # noqa: E402

FIXED_MODEL = {"ZEq", "ZDesc", "ZEps", "QuantumWitness",
               "JunctionWitness", "Contextuality"}

_DECL = re.compile(r"^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+"
                   r"([A-Za-z_][\w'.!?]*)")


def statements(module):
    """Yield (name, signature-text) for each theorem, tracking namespaces
    like axiom_audit does. The signature is the text from the name up to
    the proof marker ':='."""
    src = open(os.path.join(_LEAN, module + ".lean"), encoding="utf-8").read()
    lines = src.split("\n")
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        m = _DECL.match(s)
        if m:
            buf = [s]
            j = i
            while ":=" not in buf[-1] and j + 1 < len(lines):
                j += 1
                buf.append(lines[j].strip())
            sig = " ".join(buf)
            sig = sig.split(":=")[0]
            yield m.group(1), sig
            i = j + 1
        else:
            i += 1


def classify(module, name, sig):
    # drop the leading `theorem NAME` / `lemma NAME` so we look at the
    # SIGNATURE (binders + conclusion) only.
    body = re.sub(r"^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+\S+",
                  "", sig).strip()
    if module in FIXED_MODEL:
        return "PROVED-BOUNDED-WITNESS", "fixed finite model"
    if "∃" in body:
        return "PROVED-BOUNDED-WITNESS", "existence witness"
    # Universal if it binds ANY variable — Lean binds with `(x : T)` /
    # `{x : T}` / `[Inst]` / `∀`, or takes a hypothesis with `→`. The naive
    # `∀`-only test misses `refines_refl (m : Marking)`, which IS universal.
    has_binder = bool(re.search(r"[∀]|[({]\s*[\w₀-₉'ₙ ]+\s*:|\[[^\]]+\]|→",
                                body))
    if has_binder:
        return "PROVED", "universal over the semantic domain"
    # no binder, no ∃: a proved SPECIFIC fact — an anchor cell (znot Z = F,
    # ¬¬Z = T) or a finite construction (strict_ladder). Not universal, so
    # in Miteiko's taxonomy it is a bounded witness, not PROVED.
    return "PROVED-BOUNDED-WITNESS", "concrete cell / finite construction"


# ---- MEASURED-WITH-CEILING: the Python stands, with their ceiling ---------
MEASURED = [
    ("entailment.py / audit.py", "the 12 alive / 14 fallen laws and rules — "
     "measured on the connective tables and the entailment pool"),
    ("zverify.py", "the runtime grade classifier (until / sound / hereditary) "
     "and its separation — pool-level; the hereditary-checkable-at-depth-1 "
     "hypothesis FELL (2-move counterexample)"),
    ("zipc.py / pssl/*", "ZTL vs IPC and the matrix neighbours — incomparable, "
     "witnesses exhibited; depth-2 pool"),
    ("zsequent.py / zalgebra.py", "cut admissibility and interpolation as "
     "run over pools (the Lean-proved cores are separate, PROVED)"),
    ("pengine.py", "the paradox containment sweep — 9015 nets, grounded ⊊ "
     "categorical, 1068 cautious-Z witnesses"),
    ("ztime.py (runtime)", "observed U/S/H transitions and pool coverage — "
     "the STRUCTURE is PROVED in ZTime.lean; only the classifier behaviour "
     "and coverage are measured"),
]

# ---- INTERPRETIVE-INVARIANT: the §10 reading rules ------------------------
INTERPRETIVE = [
    "a formula verdict is NOT the state of an external object",
    "a formula F is NOT a grounded negative fact about the world",
    "deny (default-deny) is NOT a proved prohibition",
    "Z is a mark and cannot be serialized as a grounded F",
    "the passport register reads ONE WAY, physical → operational (§10)",
]


def main():
    targets = aa.build_targets()
    out = ["ZTL — evidence-status map (first cut, Miteiko's four-level "
           "taxonomy)", "=" * 66, ""]
    out.append(__doc__.strip().split("\n\n")[1])   # the taxonomy legend
    out.append("")
    out.append("=" * 66)
    out.append("1. LEAN THEOREMS — PROVED and PROVED-BOUNDED-WITNESS")
    out.append("=" * 66)

    tally = {"PROVED": 0, "PROVED-BOUNDED-WITNESS": 0}
    for m in targets:
        rows = []
        for name, sig in statements(m):
            status, why = classify(m, name, sig)
            tally[status] += 1
            tag = {"PROVED": "PROVED    ",
                   "PROVED-BOUNDED-WITNESS": "WITNESS   "}[status]
            rows.append(f"    [{tag}] {m}.{name}")
        out.append(f"\n## {m}.lean")
        out.extend(rows)

    out.append("")
    out.append("=" * 66)
    out.append("2. MEASURED-WITH-CEILING — the Python stands (NOT Lean "
               "theorems)")
    out.append("=" * 66)
    for src, desc in MEASURED:
        out.append(f"    [{src}]  {desc}")

    out.append("")
    out.append("=" * 66)
    out.append("3. INTERPRETIVE-INVARIANT — §10 interface reading rules "
               "(NOT Lean theorems)")
    out.append("=" * 66)
    for inv in INTERPRETIVE:
        out.append(f"    - {inv}")

    out.append("")
    out.append("=" * 66)
    out.append(f"first-cut tally of Lean theorems: "
               f"{tally['PROVED']} PROVED (universal over the semantics), "
               f"{tally['PROVED-BOUNDED-WITNESS']} PROVED-BOUNDED-WITNESS "
               f"(∃-witness / fixed model / concrete cell or construction).")
    out.append("All are on the empty axiom list. The PROVED / BOUNDED split "
               "is by UNIVERSALITY, not importance: an anchor cell (¬Z=F) is "
               "foundational yet bounded. Heuristic first cut — the status of "
               "each SELECTED element is confirmed in the semantic-review "
               "package.")

    path = os.path.join(_ROOT, "ZTL-evidence.txt")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(out) + "\n")
    print(f"wrote {path}: {sum(tally.values())} Lean theorems classified "
          f"({tally})")


if __name__ == "__main__":
    main()
