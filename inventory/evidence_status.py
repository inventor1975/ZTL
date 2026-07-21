# -*- coding: utf-8 -*-
"""
evidence_status — a FIRST-CUT status map of the corpus in TWO coordinates,
as refined by A. Miteiko for the Veraxis conformance manifest.

Every Lean declaration in this corpus IS proved on the empty axiom list, so
"proved-vs-witness" is not a status difference — it is a difference of
SCOPE. Two orthogonal coordinates keep that honest:

  evidence_status:
    PROVED                  a Lean theorem, kernel-checked, empty axiom list
    MEASURED_WITH_CEILING   a Python-stand pool enumeration (not a theorem)
    INTERPRETIVE_INVARIANT  a §10 interface reading rule (not a theorem)

  proof_scope (for PROVED):
    GENERAL           universal over the semantic domain (all of V, all
                      formulas Fm, an arbitrary type) — a binder or ∀ or a
                      hypothesis arrow. An ∃ INSIDE the conclusion does not
                      demote it (e.g. V.evalF_classical is GENERAL).
    BOUNDED_MODEL     proved over a fixed chosen finite model (the five-
                      individual identity model, MO2, the GHZ/Mermin frame).
    EXISTENCE_WITNESS a top-level ∃ — the instance is exhibited.
    CONCRETE_CELL     a specific proved equation or finite construction (an
                      anchor cell znot Z = F; the realized ladder).
  proof_scope (for the others): POOL_BOUNDED / INTERFACE_NORMATIVE.

A bounded scope is not "less proved"; its claim scope is simply narrower.

Names are namespace-qualified via the SAME mechanism axiom_audit uses
(V.ax_not_Z, V.tproves_iff — not the module/file name). This is a heuristic
FIRST CUT for selection; the scope of each SELECTED element is confirmed by
semantic review in the package, not by this syntactic scan alone.

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


def statements(module):
    """Yield (namespace-qualified name, signature-text) per theorem, tracking
    namespaces exactly as axiom_audit.theorem_names does, so the identifier
    is the real Lean-qualified name."""
    src = open(os.path.join(_LEAN, module + ".lean"), encoding="utf-8").read()
    lines = src.split("\n")
    stack, out, i = [], [], 0
    while i < len(lines):
        s = lines[i].strip()
        m = aa._NS.match(s)
        if m:
            stack.append(m.group(1)); i += 1; continue
        m = aa._END.match(s)
        if m and stack and m.group(1) == stack[-1]:
            stack.pop(); i += 1; continue
        m = aa._DECL.match(s)
        if m:
            qname = ".".join(stack + [m.group(1)])
            buf, j = [s], i
            while ":=" not in buf[-1] and j + 1 < len(lines):
                j += 1
                buf.append(lines[j].strip())
            sig = " ".join(buf).split(":=")[0]
            out.append((qname, sig))
            i = j + 1
            continue
        i += 1
    return out


def classify(module, sig):
    """Return (evidence_status, proof_scope). Every declaration here is
    PROVED; the coordinate that varies is scope."""
    body = re.sub(r"^(?:private\s+|protected\s+)?(?:theorem|lemma)\s+\S+",
                  "", sig).strip()
    if module in FIXED_MODEL:
        return "PROVED", "BOUNDED_MODEL"
    # A universal binder / ∀ / hypothesis arrow / instance binder makes it
    # GENERAL and TAKES PRECEDENCE over an ∃ that sits inside the conclusion.
    universal = bool(re.search(
        r"∀|[({]\s*[\w₀-₉'ₙ]+[\w₀-₉'ₙ ]*:|\[[^\]]+\]|→", body))
    if universal:
        return "PROVED", "GENERAL"
    if "∃" in body:
        return "PROVED", "EXISTENCE_WITNESS"
    return "PROVED", "CONCRETE_CELL"


# ---- MEASURED_WITH_CEILING: the Python stands (proof_scope POOL_BOUNDED) ---
MEASURED = [
    ("entailment.py / audit.py", "the 12 alive / 14 fallen laws and rules, "
     "measured on the connective tables and the entailment pool"),
    ("zverify.py", "the runtime grade classifier (until / sound / hereditary) "
     "and its separation; the depth-1-checkability hypothesis FELL (2-move "
     "counterexample)"),
    ("zipc.py / pssl/*", "ZTL vs IPC and the matrix neighbours — incomparable, "
     "witnesses exhibited; depth-2 pool"),
    ("pengine.py", "the paradox containment sweep — 9015 nets, grounded ⊊ "
     "categorical, 1068 cautious-Z"),
    ("ztime.py (runtime)", "observed U/S/H transitions and pool coverage — the "
     "STRUCTURE is PROVED/GENERAL in ZTime.lean; only the classifier "
     "behaviour and coverage are measured"),
]

# ---- INTERPRETIVE_INVARIANT: §10 (proof_scope INTERFACE_NORMATIVE) ---------
INTERPRETIVE = [
    "a formula verdict is NOT the state of an external object",
    "a formula F is NOT a grounded negative fact about the world",
    "deny (default-deny) is NOT a proved prohibition",
    "Z is a mark and cannot be serialized as a grounded F",
    "the passport register reads ONE WAY, physical → operational (§10)",
]


def main():
    targets = aa.build_targets()
    out = ["ZTL — evidence-status × proof-scope map (first cut)", "=" * 66, ""]
    out.append(__doc__.strip().split("\n\n", 1)[1].split(
        "\n\nNames are")[0])
    out.append("")
    out.append("=" * 66)
    out.append("1. LEAN DECLARATIONS — evidence_status = PROVED (empty axiom "
               "list); proof_scope varies")
    out.append("=" * 66)

    tally = {"GENERAL": 0, "BOUNDED_MODEL": 0,
             "EXISTENCE_WITNESS": 0, "CONCRETE_CELL": 0}
    for m in targets:
        rows = []
        for qname, sig in statements(m):
            _, scope = classify(m, sig)
            tally[scope] += 1
            rows.append(f"    [PROVED · {scope:<17}] {qname}")
        out.append(f"\n## {m}.lean")
        out.extend(rows)

    out.append("")
    out.append("=" * 66)
    out.append("2. evidence_status = MEASURED_WITH_CEILING · proof_scope = "
               "POOL_BOUNDED  (Python stands, not Lean theorems)")
    out.append("=" * 66)
    for src, desc in MEASURED:
        out.append(f"    [{src}]  {desc}")

    out.append("")
    out.append("=" * 66)
    out.append("3. evidence_status = INTERPRETIVE_INVARIANT · proof_scope = "
               "INTERFACE_NORMATIVE  (§10, not Lean theorems)")
    out.append("=" * 66)
    for inv in INTERPRETIVE:
        out.append(f"    - {inv}")

    out.append("")
    out.append("=" * 66)
    out.append(f"proof_scope tally over {sum(tally.values())} PROVED Lean "
               f"declarations: {tally['GENERAL']} GENERAL, "
               f"{tally['BOUNDED_MODEL']} BOUNDED_MODEL, "
               f"{tally['EXISTENCE_WITNESS']} EXISTENCE_WITNESS, "
               f"{tally['CONCRETE_CELL']} CONCRETE_CELL.")
    out.append("Heuristic first cut (syntactic scan); the scope of each "
               "SELECTED element is confirmed by semantic review.")

    path = os.path.join(_ROOT, "ZTL-evidence.txt")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(out) + "\n")
    print(f"wrote {path}: {sum(tally.values())} PROVED Lean declarations "
          f"({tally})")


if __name__ == "__main__":
    main()
