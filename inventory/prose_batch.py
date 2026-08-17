# -*- coding: utf-8 -*-
"""
Every formalised sentence in a paper, judged in one pass.

THE CURATOR'S DESIGN, 2026-08-17. `inventory/prose_warrant.py` showed that the
corpus's own judge diagnoses its prose failures exactly as `dilemmas/cogito.py`
diagnoses Descartes — the sentence rides an atom no run delivered. But it cost
twenty minutes a sentence, because each one was written out as Python.

His fix: the expensive part is the FORMALISATION and nothing else, so make that
one terse line and let the core answer the whole batch. Then it is twenty
minutes for a paper, not twenty minutes for a sentence.

INPUT FORMAT — `paper/prose-atoms.txt`, one sentence per line:

    LOCATION | FORMULA | WITNESSED | SENTENCE

  LOCATION   where it lives, e.g. `note §3.6` or `probe_real:172`
  FORMULA    ZTL formula over named atoms: `&  |  ->  ~  ( )`
  WITNESSED  comma-separated atoms a run actually delivered; blank means none.
             Prefix an atom with `!` to mark it REFUTED rather than unverified.
  SENTENCE   the prose itself, for the report

Everything not listed in WITNESSED is Z — unverified — which is the default a
zero-trust reading requires: an atom is unpaid until a run pays it.

Append ` | !` to require the line to come out EARNED. Those are the pins: a
sentence that was corrected once should not quietly drift back, and this stand
goes RED if it does. Lines without the pin are surveyed, not enforced —
reporting ON CREDIT is the diagnosis, not a failure.

WHAT IT DOES NOT DO, unchanged from prose_warrant: it does not read prose. The
split into atoms is done by hand and a self-serving split gives a self-serving
verdict. What it buys is that the split is written down, public, cheap to add
to, and re-run on every commit.

Run:  python3 inventory/prose_batch.py [path]
"""
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from ztljudge import judge                                     # noqa: E402

DEFAULT = os.path.join(_ROOT, "paper", "prose-atoms.txt")


def parse(path):
    """-> list of (lineno, location, formula, marking, sentence, pinned)"""
    out, bad = [], []
    with open(path, encoding="utf-8") as fh:
        for n, raw in enumerate(fh, 1):
            line = raw.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            parts = [p.strip() for p in line.split("|")]
            pinned = len(parts) > 4 and parts[4] == "!"
            if len(parts) < 4:
                bad.append((n, line, "needs 4 fields separated by |"))
                continue
            loc, formula, witnessed, sentence = parts[:4]
            marking = {}
            for a in (x.strip() for x in witnessed.split(",")):
                if not a:
                    continue
                if a.startswith("!"):
                    marking[a[1:]] = "F"
                else:
                    marking[a] = "T"
            if not formula:
                bad.append((n, line, "empty formula"))
                continue
            out.append((n, loc, formula, marking, sentence, pinned))
    return out, bad


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT
    print("=" * 78)
    print("PROSE BATCH — a paper's sentences, judged in one pass")
    print("=" * 78)
    if not os.path.exists(path):
        print(f"\n  no batch file at {os.path.relpath(path, _ROOT)}; "
              f"nothing claimed.")
        print("\nPROSE BATCH SKIPPED — no batch file.")
        return 0

    rows, bad = parse(path)
    if bad:
        print("\n  MALFORMED LINES — a batch that silently drops a sentence is")
        print("  worse than no batch:\n")
        for n, line, why in bad:
            print(f"     {n}: {why}\n        {line[:90]}")
        print(f"\nPROSE BATCH RED — {len(bad)} malformed line(s).")
        return 1

    judged = []
    for n, loc, formula, marking, sentence, pinned in rows:
        try:
            r = judge(formula, dict(marking))
        except Exception as exc:                      # a bad formula is data
            print(f"\n  line {n}: formula rejected by the judge — {exc}")
            print(f"     {formula}")
            print("\nPROSE BATCH RED — a formula the core will not parse.")
            return 1
        judged.append((n, loc, sentence, pinned, r))

    order = {"EARNED": 0, "REFUTED": 1, "OPEN": 2, "ON CREDIT": 3}
    judged.sort(key=lambda t: (-order.get(t[4]["disposition"], 9), t[0]))

    print(f"\n  {len(judged)} sentences from "
          f"{os.path.relpath(path, _ROOT)}\n")
    print(f"  {'':>4} {'where':22} {'verdict':<10} {'rides'}")
    for n, loc, sentence, pinned, r in judged:
        weak = ", ".join(r["unverified"]) or "—"
        pin = "!" if pinned else " "
        print(f"  {pin}{n:>3} {loc[:22]:22} {r['disposition']:<10} {weak}")
        print(f"       {sentence[:88]}")

    counts = {}
    for _n, _l, _s, _p, r in judged:
        counts[r["disposition"]] = counts.get(r["disposition"], 0) + 1
    print("\n  " + "   ".join(f"{k} {v}" for k, v in sorted(counts.items())))

    broken = [(n, loc, r) for n, loc, _s, p, r in judged
              if p and r["disposition"] != "EARNED"]
    if broken:
        print("\n  RED — pinned sentences that no longer come out EARNED:\n")
        for n, loc, r in broken:
            print(f"     line {n}, {loc}: {r['disposition']}, "
                  f"rides {r['unverified']}")
        print(f"\nPROSE BATCH RED — {len(broken)} pinned sentence(s) drifted.")
        return 1

    unpaid = counts.get("ON CREDIT", 0) + counts.get("OPEN", 0)
    print(f"""
  HOW TO READ THIS. A line marked `!` is PINNED: it was corrected once and
  must stay EARNED, and this stand goes red if it drifts. The rest are
  surveyed — ON CREDIT is a diagnosis, not a failure, and the `rides` column
  names the atom to go and pay for. {unpaid} of {len(judged)} sentences here
  still ride an unpaid atom, which is a fact about the paper and not about
  the checker.

  The ceiling is the same one prose_warrant states: the atoms are the
  author's, by hand. This makes the split cheap and public. It does not make
  it honest — that is still on whoever writes the line.""")
    print(f"\nPROSE BATCH GREEN — {len(judged)} sentences judged, "
          f"{sum(1 for _n, _l, _s, p, _r in judged if p)} pinned, none drifted.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
