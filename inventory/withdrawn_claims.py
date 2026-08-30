# -*- coding: utf-8 -*-
"""
A withdrawn claim must not still be standing somewhere else in the corpus.

WHY THIS FILE EXISTS. On 2026-08-17, hours before a deposit, an adversarial
review found ten blocking defects in one note. They were four defects, and
THREE OF THE FOUR were the same mistake: a claim had been withdrawn — properly,
with a correction written and a refuted-prediction entry filed — and left
standing verbatim somewhere else in the same document.

  * "the error from incompleteness is one-directional" was withdrawn in the
    abstract, in §3.6 and in the refuted-predictions list, and survived in §4
    and in §6 Limits, where it had been promoted to a stated limitation.
  * "Debian's `|` is this corpus's `|` ... transfers without qualification"
    was withdrawn in db/probe_real.py and in the other note. The commit
    message announcing it said "in the probe and in both notes". It was not in
    both notes, and the paragraph stood for another seven hours.

Neither was caught by anything. `inventory/note_claims.py` matches figures
against program output, and no figure was wrong: the numbers were right and the
sentences were false. A previous adversarial review had even PRESCRIBED one of
these fixes and it was applied to three sites out of four.

WHAT THIS CHECKS. Each withdrawn claim gets a signature — a distinctive phrase
from its wording. The corpus is scanned for that phrase. A hit is allowed only
where the surrounding text marks it as withdrawn; a hit in plain assertive
prose is RED.

ITS CEILING, stated because a checker that oversells itself is worse than
none — the same lesson as note_claims.py. This matches WORDING, not meaning. A
withdrawn claim restated in fresh words passes here untouched. It closes the
case where a correction was applied in one place and forgotten in another,
which is the case that actually happened three times in one day, and it closes
nothing else.

Run:  python3 inventory/withdrawn_claims.py
"""
import os
import re
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Text that marks a nearby hit as a WITHDRAWAL rather than an assertion.
MARKERS = (
    "withdraw", "refut", "was wrong", "no longer", "too strong",
    "did not survive", "an earlier draft", "an earlier version",
    "an earlier paragraph", "an earlier version of this", "used to",
    "struck", "retract", "no program produces", "was invented",
    "corrected after review", "this was wrong", "this file claimed",
    "objection is correct", "declared impossible", "claimed the error",
    # ПО-РУССКИ — добавлено 2026-08-31. Сторож считал корпус английским, а он
    # двуязычен давно: русский отзыв рядом с русским вхождением НЕ опознавался,
    # и файл кричал RED там, где отзыв был прямо в соседней строке. Список
    # маркеров, слепой к языку половины корпуса, — тот же зелёный без лампы,
    # только наоборот.
    "отозван", "ОТОЗВАНО", "снято", "снят как", "прежняя строка",
    "было неверно", "не было", "переклад", "устарел", "происшеств",
)
# `earlier` and `correct` were markers until 2026-08-17 and were removed: both
# are near-ubiquitous in this corpus, so over a ±6-line window almost any
# assertion sitting near any correction was auto-allowed. A marker list that
# forgives everything is a green light with no lamp behind it.

# (signature, the withdrawn claim it belongs to). Signatures are literal and
# lowercased; keep them long enough to be distinctive and short enough to
# survive rewrapping.
WITHDRAWN = [
    # ASSURANCE-INCIDENT-001, 2026-08-31. Утверждение стояло в докстринге
    # verify(), в зелёном заголовке стенда И в моём разборе, поданном
    # внешнему рецензенту как ДОВОД. Кода за ним не было: verify() сверяет объект сам с
    # собой, подделка с пересчётом отпечатка проходит (промерено в
    # inventory/assurance_incident_001.py, пункт 3). Отзыв ФОРМАЛЬНЫЙ:
    # новый зелёный не «поправка» старого, он начинается с нуля свидетельств.
    ("проверяется на той стороне",
     "квитанция защищена от подделки (ASSURANCE-INCIDENT-001)"),
    ("verified on the far side",
     "квитанция защищена от подделки (ASSURANCE-INCIDENT-001)"),
    ("защищено от подделки",
     "квитанция защищена от подделки (ASSURANCE-INCIDENT-001)"),
    ("меняет отпечаток и валит сверку",
     "квитанция защищена от подделки (ASSURANCE-INCIDENT-001)"),
    ("understated and never overstated",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    ("error from incompleteness is one-directional",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    # The canonical §5 wording was absent from this list — the claim's own
    # name, missed. Added with the phrasings a re-read found still standing.
    ("error from incompleteness runs one way only",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    ("no symmetric case where an incomplete map flatters",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    ("a one-directional error is the kind you cannot average",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    ("the error runs one way, and it is the dangerous way",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    ("understated blast radius, never an overstated",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    # Added after the control round found this one live in TWO places while
    # this file reported GREEN — the checker only sees what it was told, and
    # it had not been told. Third instance of the same class in one day.
    ("column does not move anywhere",
     "the chosen-target column does not move (floor is 0.791 at density 2)"),
    ("at any density and any redundancy",
     "the chosen-target column does not move (floor is 0.791 at density 2)"),
    ("transfers without qualification",
     "Debian's `|` is this corpus's `|` (withdrawn 2026-08-17)"),
    ("debian's `|` is this corpus's `|`",
     "Debian's `|` is this corpus's `|` (withdrawn 2026-08-17)"),
    ("r*` holds exactly",
     "1 - q* = r* exactly (refuted 2026-08-17: coincides only at step 0.05)"),
    ("holds exactly — arithmetic",
     "1 - q* = r* exactly (refuted 2026-08-17: coincides only at step 0.05)"),
    ("c = 0.789",
     "C = 0.789 is invented — the ACCUSATION was false; the probe prints 0.7891 at the mirror configuration (2026-08-17)"),
    ("lag zero is not safe",
     "lag zero is not safe (refuted pred. 3: at zero lag the window is zero)"),
    ("nobody has written this one",
     "the earned/credit grade is an unwritten semiring (sr_maxmin ships)"),
    ("semiring nobody has written",
     "the earned/credit grade is an unwritten semiring (sr_maxmin ships)"),
]

SCAN_EXT = (".md", ".py", ".sql")
SKIP = ("withdrawn_claims.py", "NOTE-REVIEW-FINDINGS.md",
        "PROVSQL-REVIEW-FINDINGS.md", "LEDGER-NOTE-REVIEW.md")
# Directories with no claims of our own in them.
SKIP_DIRS = (".git", "_attic", "archive", "OLD", ".lake", "node_modules",
             "__pycache__", ".claude",
             # `lab/` holds copies of PRE-FIX text on purpose — it is the
             # experimental record of what the defects looked like. Scanning
             # it flags the specimens as if they were live claims.
             "lab")


def files():
    """RECURSIVE. The first version listed four directories non-recursively,
    so `essays/`, `downstream/`, `tool/`, `conformance/`, `dilemmas/` and the
    blueprint were never scanned at all — and a re-read found live withdrawn
    claims in files it could not reach. A checker that reports GREEN over a
    fraction of the corpus reports nothing."""
    out = []
    for base, dirs, names in os.walk(_ROOT):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for name in names:
            if name in SKIP or not name.endswith(SCAN_EXT):
                continue
            out.append(os.path.join(base, name))
    return sorted(set(out))


def joined(text):
    """Whitespace-collapsed text, so a signature broken across a line break
    is still found. The first version matched per line and promised in its own
    comment that signatures were `short enough to survive rewrapping'; they
    were not, and the claim standing in KNOWN-LIMITS.md was missed for exactly
    that reason — `...UNDERSTATED and never' / `overstated.'"""
    text = re.sub(r'"\s*\)\s*\n?\s*print\(\s*f?"', " ", text)
    return re.sub(r"\s+", " ", text).lower()


def line_of(text, char_index):
    return text.count("\n", 0, char_index) + 1


def main():
    print("=" * 78)
    print("WITHDRAWN CLAIMS — still standing anywhere?")
    print("=" * 78)
    print("\n  Three of four blocking defects found before the 2026-08-17")
    print("  deposit were one mistake: a claim withdrawn in one place and")
    print("  left standing in another. Figures were right; sentences were")
    print("  false, so the figure scan passed. This is the other direction.\n")

    bad, checked = [], 0
    scanned = files()
    for path in scanned:
        try:
            raw = open(path, encoding="utf-8").read()
        except (OSError, UnicodeDecodeError):
            continue
        flat = joined(raw)
        if not any(sig in flat for sig, _c in WITHDRAWN):
            continue
        # Only files with a hit pay for the expensive per-offset work.
        for sig, claim in WITHDRAWN:
            start = 0
            while True:
                j = flat.find(sig, start)
                if j < 0:
                    break
                start = j + 1
                checked += 1
                # Context measured in CHARACTERS of collapsed text, so it is
                # the same amount of prose either side regardless of wrapping.
                ctx = flat[max(0, j - 420):j + len(sig) + 420]
                if not any(m in ctx for m in MARKERS):
                    rel = os.path.relpath(path, _ROOT)
                    # map back to a line number in the original text
                    words = sig.split()[0]
                    k = raw.lower().find(words)
                    bad.append((rel, line_of(raw, k if k >= 0 else 0),
                                sig, claim))

    print(f"  signatures tracked      {len(WITHDRAWN):>4}")
    print(f"  files scanned           {len(scanned):>4}")
    print(f"  occurrences examined    {checked:>4}")

    if bad:
        print("\n  RED — a withdrawn claim stands as an assertion:\n")
        for rel, n, sig, claim in bad:
            print(f"     {rel}:{n}")
            print(f"       phrase   {sig!r}")
            print(f"       withdrew {claim}")
        print(f"\nWITHDRAWN CLAIMS RED — {len(bad)} live occurrence(s).")
        return 1

    print("\n  Every occurrence sits beside its withdrawal. None stands as an")
    print("  assertion.")
    print("\n  WHAT THIS DOES NOT CHECK: meaning. A withdrawn claim restated")
    print("  in fresh words passes here untouched, and the reviewer that")
    print("  found these four defects would still have been needed. This")
    print("  closes the repeat, not the original.")
    print(f"\nWITHDRAWN CLAIMS GREEN — {len(WITHDRAWN)} signatures, "
          f"{checked} occurrences, none live.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
