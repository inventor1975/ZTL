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
    "earlier", "withdraw", "refut", "was wrong", "correct", "no longer",
    "too strong", "did not survive", "an earlier draft", "an earlier version",
    "struck", "retract", "no program produces", "invented",
)

# (signature, the withdrawn claim it belongs to). Signatures are literal and
# lowercased; keep them long enough to be distinctive and short enough to
# survive rewrapping.
WITHDRAWN = [
    ("understated and never overstated",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    ("error from incompleteness is one-directional",
     "the error from incompleteness runs one way only (refuted pred. 12)"),
    ("transfers without qualification",
     "Debian's `|` is this corpus's `|` (withdrawn 2026-08-17)"),
    ("debian's `|` is this corpus's `|`",
     "Debian's `|` is this corpus's `|` (withdrawn 2026-08-17)"),
    ("r*` holds exactly",
     "1 - q* = r* exactly (refuted 2026-08-17: coincides only at step 0.05)"),
    ("holds exactly — arithmetic",
     "1 - q* = r* exactly (refuted 2026-08-17: coincides only at step 0.05)"),
    ("c = 0.789",
     "C = 0.789 — a figure no program produces (refuted pred. 11)"),
    ("lag zero is not safe",
     "lag zero is not safe (refuted pred. 3: at zero lag the window is zero)"),
    ("nobody has written this one",
     "the earned/credit grade is an unwritten semiring (sr_maxmin ships)"),
    ("semiring nobody has written",
     "the earned/credit grade is an unwritten semiring (sr_maxmin ships)"),
]

SCAN_DIRS = ("paper", "db", "inventory", ".")
SCAN_EXT = (".md", ".py", ".sql")
SKIP = ("withdrawn_claims.py", "NOTE-REVIEW-FINDINGS.md",
        "PROVSQL-REVIEW-FINDINGS.md", "LEDGER-NOTE-REVIEW.md")


def files():
    out = []
    for d in SCAN_DIRS:
        p = os.path.join(_ROOT, d)
        if not os.path.isdir(p):
            continue
        for name in sorted(os.listdir(p)):
            if name in SKIP or not name.endswith(SCAN_EXT):
                continue
            out.append(os.path.join(p, name))
    return sorted(set(out))


def window(lines, i, span=6):
    lo, hi = max(0, i - span), min(len(lines), i + span + 1)
    return " ".join(lines[lo:hi]).lower()


def main():
    print("=" * 78)
    print("WITHDRAWN CLAIMS — still standing anywhere?")
    print("=" * 78)
    print("\n  Three of four blocking defects found before the 2026-08-17")
    print("  deposit were one mistake: a claim withdrawn in one place and")
    print("  left standing in another. Figures were right; sentences were")
    print("  false, so the figure scan passed. This is the other direction.\n")

    bad, checked = [], 0
    for path in files():
        try:
            lines = open(path, encoding="utf-8").read().splitlines()
        except (OSError, UnicodeDecodeError):
            continue
        low = [ln.lower() for ln in lines]
        for i, ln in enumerate(low):
            for sig, claim in WITHDRAWN:
                if sig not in ln:
                    continue
                checked += 1
                ctx = window(low, i)
                if not any(m in ctx for m in MARKERS):
                    rel = os.path.relpath(path, _ROOT)
                    bad.append((rel, i + 1, sig, claim))

    print(f"  signatures tracked      {len(WITHDRAWN):>4}")
    print(f"  files scanned           {len(files()):>4}")
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
