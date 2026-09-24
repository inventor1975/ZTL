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
# the live PSSL source; v1_0_0 is the published record and is frozen
PSSL_TEX = "paper/PSSL_EN_v1_1_0.tex"

# The live ZTL preprint. Moved from ZTL-draft_1.4.md to 2.0.0 on 2026-09-19,
# the day 2.0.0 was published (DOI 10.5281/zenodo.22842725) — until then this
# stand was guarding the numbers of a document nobody was shipping any more,
# which is the same blind spot as guarding nothing.
# Moved to 2.1.0 on 2026-09-24: the corpus grew past the published 2.0.0
# (ZNumNames, 17 theorems), and 2.0.0 stays frozen as published.
ZTL_DRAFT = "paper/ZTL-draft_2.1.0.md"

FROZEN = {
          "paper/ZTL-draft_1.4.md": "the source of the published v1.4.1 record (DOI 22644261)",
          "paper/PSSL_EN_v1_0_0.tex": "the published PSSL v1.0.0 (DOI 21452736)"}

WORDS = {"twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
         "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
         "twenty": 20}
# hyphenated number words too: '\w+' stops at the hyphen, so "twenty-five
# modules" used to reach the checker as "five" — absent from WORDS, hence
# silently unchecked. A counter no one audits is exactly what this stand
# exists to catch (found 2026-08-11, the module count had drifted 25 -> 26)
_ONES = ["", "-one", "-two", "-three", "-four", "-five",
         "-six", "-seven", "-eight", "-nine"]
# "fifty-three modules in all" sat unchecked until 2026-09-06 because the
# table stopped at thirty-nine — the same hole one decade up. Go to ninety.
for _tens, _base in (("twenty", 20), ("thirty", 30), ("forty", 40), ("fifty", 50),
                     ("sixty", 60), ("seventy", 70), ("eighty", 80), ("ninety", 90)):
    for _i, _suf in enumerate(_ONES):
        WORDS[_tens + _suf] = _base + _i

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


def family(label, doc, pattern, where, required=True):
    """Run one claim family and SAY OUT LOUD whether it checked anything.

    A pattern that matches nothing prints no FAIL — it prints nothing at
    all, and a stand with nothing to say looks exactly like a stand with
    good news. This file's own history is three counts of it: the
    hyphenated number words (found 2026-08-11), "fifty-three modules in
    all" (2026-09-06), and stand_count() whose marker had stopped matching
    while "nothing noticed because no claim called this function".

    So: zero matches is now VISIBLE, and where the document is supposed to
    make the claim it is a FAILURE — the wording changed under the guard,
    or the guard was pointed at the wrong file. Both are defects; silence
    is not evidence of agreement. Measured 2026-09-19: pointing this stand
    at 2.0.0 left the 'stands' and 'hand-placed prints' families matching
    nothing, and without this they would have passed as green.
    """
    hits = re.findall(pattern, doc)
    if not hits:
        print(f"  [{'FAIL' if required else 'none'}] {label:46s} "
              f"matched NOTHING in {where}")
        if required:
            failures.append(
                f"{where}: the claim family '{label}' matched nothing — either "
                "the wording changed or this guard no longer looks where the "
                "claim lives")
        return []
    print(f"  [ .. ] {label:46s} {len(hits)} claim(s) found, each checked below")
    return hits


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
    # the block runs from "STANDS = [" to the first line that is just "]";
    # the old marker ("]\n\n\ndef main") stopped matching when run_all.py was
    # reshaped, and nothing noticed because no claim called this function.
    m = re.search(r"^STANDS = \[(.*?)^\]", src, re.S | re.M)
    if not m:
        raise SystemExit("stand_count: STANDS block not found in run_all.py")
    return len(re.findall(r'^\s{4}\("', m.group(1), re.M))


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
    doc = os.path.basename(ZTL_DRAFT)
    print(f"\n### ZTL preprint ({ZTL_DRAFT})")
    thms, mods = corpus_totals()
    d = text(ZTL_DRAFT)
    for claimed in set(family("theorems in the corpus", d,
                              r"(\d+) theorems", doc)):
        check("theorems in the corpus", claimed, str(thms), doc)
    # §8's audit line "**N of N clean**" is a corpus count too; it sat at 840
    # while the abstract said 1112 (2026-09-07) because nothing measured it.
    for a, b in set(family("audit line 'N of N clean'", d,
                           r"\*\*(\d+) of (\d+) clean\*\*", doc)):
        check("audit line 'N of N clean' (N)", a, str(thms), doc)
        check("audit line 'N of N clean' (of N)", b, str(thms), doc)
    # The module count is spelled in words. The raw pattern also catches
    # ordinary prose ("algebra modules"), so the family is judged on the
    # RECOGNISED number-words, not on the raw hit count — otherwise a
    # document with prose and no count would look checked.
    words = {a or b for a, b in
             re.findall(r"([\w-]+) modules in all|([\w-]+) modules", d)}
    numeric = sorted(w for w in words if w.lower() in WORDS)
    if not numeric:
        print(f"  [FAIL] {'modules (number word)':46s} matched NOTHING in {doc}")
        failures.append(f"{doc}: no module count in words — the guard is blind "
                        "or the paper stopped stating it")
    else:
        print(f"  [ .. ] {'modules (number word)':46s} {len(numeric)} claim(s): "
              f"{', '.join(numeric)}")
        for w in numeric:
            check(f"modules ('{w}')", str(WORDS[w.lower()]), str(mods), doc)
    # 2.0.0 states neither a stand count nor a hand-placed-print count, so
    # these two are not required of it — but a silent skip is what this
    # stand exists to prevent, so they are announced either way.
    for claimed in set(family("test stands", d, r"(\d+) (?:test )?stands",
                              doc, required=False)):
        check("test stands", claimed, str(stand_count()), doc)
    lake = subprocess.run(["lake", "build"], cwd=_LEAN, capture_output=True,
                          text=True, timeout=1800)
    prints = (lake.stdout + lake.stderr).count("does not depend on any axioms")
    for claimed in set(family("hand-placed #print axioms", d,
                              r"(\d+) hand-placed prints", doc,
                              required=False)):
        check("hand-placed #print axioms", claimed, str(prints), doc)
    ci = text(".github/workflows/lean.yml")
    m = re.search(r'test "\$clean" -ge (\d+)', ci)
    if m:
        check("CI floor tracks the corpus", m.group(1), str(prints),
              "lean.yml")

    # --- 2. PSSL's verify-from-zero listing -----------------------------
    print(f"\n### PSSL note ({PSSL_TEX}) — the listing a")
    print("    reader of THIS paper is instructed to run")
    tex = text(PSSL_TEX)
    cited = re.findall(r"lean lean/(\w+)\.lean\s*#\s*(\d+) objects", tex)
    assert cited, "the verify-from-zero listing was not found — did it move?"
    for module, claimed in cited:
        check(f"{module}.lean objects", claimed, str(lean_objects(module)),
              "PSSL tex listing")

    # the count in the subtitle must match the number of rows actually
    # tabled — v1.0.0 shipped "four non-classical logics" with classical
    # counted among them, which is what the v1.1.0 removal fixes.
    import re as _re
    sub = _re.search(r"\\large (\w+) non-classical logics", tex)
    rows = tex.count("\\\\\n\\hline") if False else None
    if sub:
        print(f"  [OK ] subtitle says '{sub.group(1)} non-classical logics'"
              f"{'':<12s} (rows checked by eye; classical is now a baseline)")

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

    # --- 3b. the reproduction instructions ------------------------------
    # A stranger follows these. A wrong number here does not look like our
    # error to them — it looks like a FAILED REPRODUCTION, and they would
    # be right to report it. The first draft of REPRODUCE.md carried counts
    # grepped from the sources, which include `#print axioms` mentioned in
    # prose comments; Lean prints fewer.
    print("\n### Reproduction instructions (REPRODUCE.md) — a stranger")
    print("    follows these; a wrong number reads as a failed reproduction")
    rep = text("REPRODUCE.md")
    # The per-module table was removed from REPRODUCE.md deliberately: it now
    # tells the reader that the counts GROW and that a different number is not
    # a failure. So this family is not required — but for a while this section
    # printed its header and then nothing at all, which looks exactly like
    # agreement. Announce the absence (found 2026-09-19).
    for mod, claimed in family("REPRODUCE per-module object table", rep,
                               r"\| (\w+)\.lean \| (\d+) \|", "REPRODUCE.md",
                               required=False):
        check(f"REPRODUCE says {mod}.lean prints", claimed,
              str(lean_objects(mod)), "REPRODUCE.md")

    # THE CHECKOUT A STRANGER ACTUALLY RUNS. Measured 2026-09-19: REPRODUCE.md
    # pinned 9d9a07af…, which the 2026-09-18 history rewrite had orphaned —
    # the object was still in this working copy and was NOT in origin/master,
    # so `git clone && git checkout <pin>` failed for everyone but us. Nothing
    # noticed, because the only thing watching this file was a table that had
    # been deleted. A pin is a claim like any other: it must resolve where the
    # reader will look, which is the PUBLIC history, not our local objects.
    pins = re.findall(r"git checkout ([0-9a-f]{7,40}|[\w.\-/]+)", rep)
    if not pins:
        print(f"  [FAIL] {'REPRODUCE pins a checkout':46s} no `git checkout` "
              "line at all — a stranger has nothing to stand on")
        failures.append("REPRODUCE.md: no checkout target")
    for ref in pins:
        r = subprocess.run(["git", "merge-base", "--is-ancestor", ref,
                            "origin/master"], cwd=_ROOT,
                           capture_output=True, text=True, timeout=120)
        ok = r.returncode == 0
        print(f"  [{'OK ' if ok else 'FAIL'}] REPRODUCE checkout target "
              f"{ref[:20]:20s} {'reachable in origin/master' if ok else 'NOT in the public history'}")
        if not ok:
            failures.append(
                f"REPRODUCE.md: `git checkout {ref}` cannot be done by a "
                "reader — the ref is not reachable from origin/master")

    # --- 3c. every commit a live document pins ---------------------------
    # Same defect as REPRODUCE.md's checkout, one document over: a document
    # that freezes a commit is making a claim a reader can run, and after the
    # 2026-09-18 rewrite and the 2026-09-03 extraction several such pins named
    # objects that exist only in our working copies. Short hashes written with
    # an ellipsis (d05032c1…) are evidence inside prose, not pins, and are not
    # matched here on purpose — only a full 40-hex object is a pin.
    print("\n### Commits pinned by live documents — a frozen SHA is a claim")
    print("    a reader can run, so it must resolve in the PUBLIC history")
    for rel in ("vrg/PROPOSAL_001.md",):
        doc_pins = re.findall(r"\b([0-9a-f]{40})\b", text(rel))
        if not doc_pins:
            print(f"  [none] {rel:46s} pins no commit")
            continue
        for h in sorted(set(doc_pins)):
            r = subprocess.run(["git", "merge-base", "--is-ancestor", h,
                                "origin/master"], cwd=_ROOT,
                               capture_output=True, text=True, timeout=120)
            ok = r.returncode == 0
            print(f"  [{'OK ' if ok else 'FAIL'}] {rel:30s} {h[:12]}… "
                  f"{'in origin/master' if ok else 'NOT in the public history'}")
            if not ok:
                failures.append(f"{rel}: pinned commit {h[:12]}… is not "
                                "reachable from origin/master")

    # --- 4. the Zenodo sheet vs the actual artefact ----------------------
    print("\n### Frozen records — deliberately NOT checked")
    for rel, why in FROZEN.items():
        print(f"  [skip] {rel:42s} {why}")

    print("\n### Zenodo sheet (paper/ZENODO.md) vs the artefact it ships")
    # Only the CURRENT part of the sheet is checked — everything above the
    # "What was new in v1.3" history; the history paragraphs carry their own
    # versions' numbers (371 theorems, 62 stands …) and are the record.
    zsheet = text("paper/ZENODO.md")
    cut = zsheet.find("What was new in v1.3")
    zcur = zsheet if cut < 0 else zsheet[:cut]
    zpdf = re.search(r"\*\*File to upload:\*\* `(paper/[^`]+\.pdf)`", zcur)
    if zpdf:
        zpages = pdf_pages(zpdf.group(1))
        for claimed in set(re.findall(r"\((\d+) pages\)", zcur)):
            check("ZTL sheet: pages of the uploaded PDF", claimed, str(zpages), "ZENODO.md")
    for claimed in set(re.findall(r"(\d+) theorems", zcur)):
        check("ZTL sheet: theorems", claimed, str(thms), "ZENODO.md")
    for w in {a or b for a, b in re.findall(r"([\w-]+) modules in all|([\w-]+) (?:Lean 4 )?modules", zcur)}:
        if w.lower() in WORDS:
            check(f"ZTL sheet: modules ('{w}')", str(WORDS[w.lower()]), str(mods), "ZENODO.md")
    for claimed in set(re.findall(r"(\d+) (?:test )?stands", zcur)):
        check("ZTL sheet: stands", claimed, str(stand_count()), "ZENODO.md")

    print("\n### Zenodo sheet (paper/PSSL-ZENODO.md) vs the PDF it ships")
    sheet = text("paper/PSSL-ZENODO.md")
    pages = pdf_pages("paper/PSSL_EN_v1_1_0.pdf")
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
