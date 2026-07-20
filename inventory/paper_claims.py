# -*- coding: utf-8 -*-
"""
paper_claims — the papers' numbers, measured instead of trusted.

The code in this repository is guarded: `axiom_audit.py` checks every
theorem, `run_all.py` checks every stand, and both run in CI. The PAPERS
were guarded by nothing. Their numbers — object counts, module counts,
stand counts, page counts — lived on whoever last remembered to update
them, which is exactly the arrangement the stands were in until the
morning of 2026-07-20.

It cost twice the same day. The PSSL note shipped a verify-from-zero
listing saying `QuantumWitness.lean` prints 5 objects when it prints 11
— a wrong number in the one instruction a reader of THAT paper is meant
to run. And its closing paragraph still offered "its two poles" as proof
while the masthead promised five components. Both were caught by a
reviewer reading, not by any machine.

A paper is a set of claims. Claims get measured. This stand measures the
numeric ones and fails on a mismatch.

WHAT IT CANNOT DO, stated plainly: it checks numbers, not meanings. A
paper can be arithmetically consistent and still describe its own results
wrongly. Nothing here relieves the author of reading.

Run:  python3 inventory/paper_claims.py
"""
import os
import re
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
_LEAN = os.path.join(_ROOT, "lean")
_PAPER = os.path.join(_ROOT, "paper")

# LIVE documents are checked against reality. FROZEN ones describe a
# record already published and must NOT be "corrected" — paper/ZENODO.md
# says 40 stands because v1.2 was published with 40, and rewriting it
# would misdescribe the public record. Distinguishing the two is the
# whole reason this list is explicit rather than a glob.
FROZEN = {"paper/ZENODO.md": "the published v1.2 record (DOI 21440066)"}

WORDS = {"twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
         "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
         "twenty": 20}

failures = []


def text(rel):
    with open(os.path.join(_ROOT, rel), encoding="utf-8") as fh:
        return fh.read()


def check(label, claimed, actual, where):
    ok = claimed == actual
    print(f"  [{'OK ' if ok else 'FAIL'}] {label:46s} paper {str(claimed):>6s}"
          f"   measured {str(actual):>6s}")
    if not ok:
        failures.append(f"{where}: says {claimed}, measured {actual}")
    return ok


# ---------------------------------------------------------------------------
# Measurements — every one taken now, none carried over
# ---------------------------------------------------------------------------
def lean_objects(module):
    """Objects printing 'does not depend on any axioms' for one module,
    compiled standalone exactly as a reader of the paper would."""
    env = dict(os.environ,
               LEAN_PATH=os.path.join(_LEAN, ".lake/build/lib/lean"))
    r = subprocess.run(["lean", module + ".lean"], cwd=_LEAN, env=env,
                       capture_output=True, text=True, timeout=600)
    return (r.stdout + r.stderr).count("does not depend on any axioms")


def corpus_totals():
    """Theorems and modules, from the per-theorem audit itself."""
    r = subprocess.run([sys.executable,
                        os.path.join(_HERE, "axiom_audit.py")],
                       cwd=_ROOT, capture_output=True, text=True, timeout=2400)
    m = re.search(r"ALL CLEAN: (\d+) theorems across (\d+) modules", r.stdout)
    if not m:
        return None, None
    return int(m.group(1)), int(m.group(2))


def stand_count():
    src = text("run_all.py")
    block = src[src.index("STANDS = ["):src.index("]\n\n\ndef main")]
    return len(re.findall(r'^\s{4}\("', block, re.M))


def pdf_pages(rel):
    r = subprocess.run(["pdfinfo", os.path.join(_ROOT, rel)],
                       capture_output=True, text=True, timeout=120)
    m = re.search(r"Pages:\s+(\d+)", r.stdout)
    return int(m.group(1)) if m else None


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    print("=" * 78)
    print("PAPER CLAIMS — the numbers in the papers, measured")
    print("=" * 78)

    # --- 1. the ZTL preprint's corpus figures ---------------------------
    print("\n### ZTL preprint (paper/ZTL-draft.md)")
    thms, mods = corpus_totals()
    d = text("paper/ZTL-draft.md")
    for claimed in set(re.findall(r"(\d+) theorems", d)):
        check("theorems in the corpus", claimed, str(thms), "ZTL-draft.md")
    words = set(re.findall(r"(\w+) modules in all|(\w+) modules", d))
    for w in {a or b for a, b in words}:
        if w.lower() in WORDS:
            check(f"modules ('{w}')", str(WORDS[w.lower()]), str(mods),
                  "ZTL-draft.md")
    for claimed in set(re.findall(r"(\d+) (?:test )?stands", d)):
        check("test stands", claimed, str(stand_count()), "ZTL-draft.md")
    lake = subprocess.run(["lake", "build"], cwd=_LEAN, capture_output=True,
                          text=True, timeout=1800)
    prints = (lake.stdout + lake.stderr).count("does not depend on any axioms")
    for claimed in set(re.findall(r"(\d+) hand-placed prints", d)):
        check("hand-placed #print axioms", claimed, str(prints),
              "ZTL-draft.md")
    ci = text(".github/workflows/lean.yml")
    m = re.search(r'test "\$clean" -ge (\d+)', ci)
    if m:
        check("CI floor tracks the corpus", m.group(1), str(prints),
              "lean.yml")

    # --- 2. PSSL's verify-from-zero listing -----------------------------
    print("\n### PSSL note (paper/PSSL_EN_v1_0_0.tex) — the listing a")
    print("    reader of THIS paper is instructed to run")
    tex = text("paper/PSSL_EN_v1_0_0.tex")
    cited = re.findall(r"lean lean/(\w+)\.lean\s*#\s*(\d+) objects", tex)
    assert cited, "the verify-from-zero listing was not found — did it move?"
    for module, claimed in cited:
        check(f"{module}.lean objects", claimed, str(lean_objects(module)),
              "PSSL tex listing")

    # --- 3. PSSL's internal component count ------------------------------
    print("\n### PSSL note — does it agree with itself about how many")
    print("    machine-checked components it has?")
    counts = re.findall(r"(two|three|four|five|six) machine-checked", tex)
    uniq = sorted(set(counts))
    ok = len(uniq) == 1
    print(f"  [{'OK ' if ok else 'FAIL'}] component word used in the tex"
          f"{'':<18s} {uniq}")
    if not ok:
        failures.append(f"PSSL tex disagrees with itself: {uniq}")
    # the closing must not offer fewer components as proof than the masthead
    poles_only = "its two poles are offered as proof" in tex
    print(f"  [{'OK ' if not poles_only else 'FAIL'}] closing does not "
          f"under-count the proof")
    if poles_only:
        failures.append("PSSL closing offers 'two poles' as the proof")

    # --- 4. the Zenodo sheet vs the actual artefact ----------------------
    print("\n### Frozen records — deliberately NOT checked")
    for rel, why in FROZEN.items():
        print(f"  [skip] {rel:42s} {why}")

    print("\n### Zenodo sheet (paper/PSSL-ZENODO.md) vs the PDF it ships")
    sheet = text("paper/PSSL-ZENODO.md")
    pages = pdf_pages("paper/PSSL_EN_v1_0_0.pdf")
    for claimed in set(re.findall(r"\((\d+) pages", sheet)):
        check("pages of the uploaded PDF", claimed, str(pages), "sheet")
    m = re.search(r"(\d+) \+ (\d+) \+ (\d+) \+ (\d+) = (\d+) objects", sheet)
    if m:
        parts = [int(x) for x in m.groups()[:4]]
        check("object sum adds up", str(sum(parts)), m.group(5), "sheet")
        for mod, claimed in zip(["ZTL", "QuantumWitness", "Contextuality",
                                 "JunctionWitness"], parts):
            check(f"sheet: {mod}", str(claimed), str(lean_objects(mod)),
                  "sheet")

    # --- verdict ---------------------------------------------------------
    print("\n" + "=" * 78)
    if failures:
        print(f"RED — {len(failures)} claim(s) in the papers are not true:")
        for f in failures:
            print(f"    {f}")
        print("\n  A paper is a set of claims. These ones do not measure up.")
        sys.exit(1)
    print("PAPER CLAIMS GREEN — every numeric claim checked matches a")
    print("measurement taken now.")
    print("\n  CEILING: numbers only. A paper can be arithmetically")
    print("  consistent and still describe its results wrongly; this")
    print("  stand does not relieve the author of reading.")
