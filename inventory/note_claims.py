# -*- coding: utf-8 -*-
"""
Every number in the warrant-containment note, checked against the code.

The note is a document; the probes are the measurement. Between them sits the
oldest hole in this corpus, named in KNOWN-LIMITS: numbers can be re-measured
and match while the sentence interpreting them is false. This file closes the
half that can be closed — it takes each figure quoted in the note and demands
that a program still print it.

It does NOT read the prose around the figures. A note whose numbers are right
and whose claims are wrong would pass here, and that ceiling is exactly where
Frege's mistake lived.

Run:  python3 inventory/note_claims.py
"""
import concurrent.futures
import os
import time
import pathlib
import re
import subprocess
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NOTE = os.path.join(_ROOT, "paper", "warrant-containment-note.md")

# (probe, what the note says, the substring that must appear in the output)
CLAIMS = [
    ("probe_ledger.py", "plain SQL answers 2", "ANSWERS          2"),
    ("probe_ledger.py", "answers 3 wrongly", "ANSWERS WRONGLY  3"),
    ("probe_ledger.py", "cannot express 3", "CANNOT EXPRESS   3"),
    ("probe_assertions.py", "5 of 20 need a warrant", "5 of 20"),
    ("probe_assertions.py", "completeness reaches no ledger", "NEITHER 2   of 12"),
    ("probe_failures.py", "2 touches of eight", "TOUCHES   2 of 8"),
    ("probe_failures.py", "4 out of eight", "OUT       4 of 8"),
    ("probe_failures.py", "Wirecard would print EARNED",
     "Wirecard would have printed EARNED"),
    ("probe_system_errors.py", "1 caught, 1 only if declared, 1 not",
     "CAUGHT 1 of 3   CAUGHT ONLY IF DECLARED 1"),
    ("probe_system_errors.py", "Mars is a reconstruction, not a catch",
     "SO THE CATCH IS A RECONSTRUCTION, NOT A CATCH"),
    ("probe_system_errors.py", "no unit on the source returns EARNED",
     "disposition : EARNED   <- the wrong answer"),
    ("probe_system_errors.py", "the Mars units refusal",
     "cannot compare 'lbf' with 'N'"),
    ("probe_system_errors.py", "the Whale formula earns",
     "the formula as WRITTEN   -> EARNED"),
    ("probe_topology.py", "random-local threshold 90%", "random-local"),
    ("probe_topology.py", "hierarchy threshold 75%", "hierarchy"),
    ("probe_containment.py", "the commander costs everything",
     "THE COMMANDER    -> 100,000 of 100,000 fall"),
    ("probe_variance.py", "r* median 0.725 across ten seeds",
     "median 0.725"),
    ("probe_variance.py", "q* median 0.35 across ten seeds",
     "q*  hidden correlation tolerated       median 0.35"),
    ("probe_variance.py", "A_crit constant across seeds",
     "A_crit, 1 root                         median 1        constant"),
    ("probe_criterion.py", "r and q are one crossing", "ONE NUMBER, NOT TWO"),
    ("probe_topology.py", "no threshold against a chosen target",
     "THE THRESHOLD IS AN ARTEFACT OF WHERE YOU AIM"),
    ("probe_roots.py", "closed forms, not measurements",
     "READ THESE AS ARITHMETIC, NOT AS MEASUREMENTS"),
    ("probe_criterion.py", "the minimum does not govern",
     "The minimum does not determine C"),
    ("probe_classes.py", "four dimensions raise r* to 0.75",
     "four (plus shared model and sensor)    r* = 0.75"),
    ("probe_classes.py", "A_crit is the authority root",
     "A_crit = 1.000, from authority root"),
    ("probe_roots.py", "one root costs everything",
     "1 authority root                   A_crit = 1.000"),
    ("probe_roots.py", "shared upstream costs everything",
     "3 roots, SHARED upstream           A_crit = 1.000"),
    ("probe_blindspot.py", "the direction holds",
     "THE DIRECTION HOLDS EXACTLY"),
    ("probe_blindspot.py", "the magnitude did not",
     "THE MAGNITUDE DID NOT REPRODUCE"),
    ("probe_currentness.py", "the window is the lag",
     "blind steps == update lag, exactly"),
    ("probe_currentness.py", "a prediction refuted",
     "A PREDICTION OF MINE, REFUTED BY ITS OWN TABLE"),
    ("probe_gate.py", "the gate leaks", "CONTAINS A FAILURE OF MY OWN"),
    ("probe_gate.py", "reliance, not permission",
     "may continue to TREAT its current warrant as satisfying the"),
]

# Figures the note prints in prose or tables, each of which must appear
# somewhere in the named probe's output exactly as written.
FIGURES = [
    ("probe_topology.py", ["95,041", "20,840", "95,081", "194", "33,943"]),
    ("probe_containment.py", ["4,102", "29,391", "3,793", "20,099", "99,992"]),
    ("probe_roots.py", ["0.117"]),
    ("probe_blindspot.py", ["0.089", "0.086", "0.064", "+0.004", "+0.025"]),
    ("probe_gate.py", ["66.0%", "270", "170"]),
    ("probe_variance.py", ["0.725", "0.117"]),
]


def out(probe):
    return _OUTPUTS[probe]


def _run(probe):
    r = subprocess.run([sys.executable, os.path.join(_ROOT, "db", probe)],
                       capture_output=True, text=True, timeout=1800)
    return probe, r.stdout + r.stderr


def _run_all_probes():
    """EVERY probe, ONCE, IN PARALLEL. This file used to shell out per claim
    and per figure, sequentially, so its wall time was the SUM of fifteen
    probes — about eight minutes, most of it spent re-running the same
    programs. They are independent processes; the wait is not.

    The cache also matters for correctness, not only speed: a checker that
    ran a probe twice could in principle compare a claim against one run and
    a figure against another."""
    names = sorted(f.name for f in pathlib.Path(_ROOT, "db").glob("probe_*.py"))
    with concurrent.futures.ThreadPoolExecutor(
            max_workers=min(8, len(names))) as ex:
        return dict(ex.map(_run, names))


_OUTPUTS = {}


def main():
    print("=" * 72)
    print("NOTE CLAIMS — every figure in the note, demanded back from the code")
    print("=" * 72)
    global _OUTPUTS
    t0 = time.perf_counter()
    _OUTPUTS = _run_all_probes()
    text = open(NOTE, encoding="utf-8").read()
    bad = []
    print(f"\n  {len(_OUTPUTS)} probes run in parallel, "
          f"{time.perf_counter() - t0:.0f}s wall")

    print(f"\n  the note: {len(text):,} characters, "
          f"{len(text.splitlines())} lines")

    print("\n  1. CLAIMS")
    for probe, said, marker in CLAIMS:
        ok = marker in out(probe)
        print(f"     [{'OK ' if ok else 'BAD'}] {said}")
        if not ok:
            bad.append((probe, said, marker))

    print("\n  2. FIGURES PRINTED IN THE NOTE")
    for probe, figs in FIGURES:
        for f in figs:
            in_note, in_code = f in text, f in out(probe)
            ok = (not in_note) or in_code
            print(f"     [{'OK ' if ok else 'BAD'}] {f:>10}  "
                  f"note={'y' if in_note else 'n'} "
                  f"code={'y' if in_code else 'n'}  ({probe})")
            if not ok:
                bad.append((probe, f, "figure in note, absent from output"))

    print("\n  3. ORPHAN FIGURES — numbers in the note that no probe prints")
    print("     Added after an adversarial review found `C = 0.789`, a figure")
    print("     no program produces, and `52,000` where the probe prints")
    print("     59,716. The checker above could not catch either: it looks")
    print("     for figures it was TOLD about. This scan goes the other way,")
    print("     from the note outward, and needs no list.")
    # EVERY probe, not only the cited ones. The first version scanned the
    # probes named in the lists above, so a figure taken from an uncited run
    # looked like a fabrication — which is the same class of false alarm as
    # the false assurance this scan was added to remove.
    every = "\n".join(_OUTPUTS.values())
    # numbers as a reader meets them: 0.789, 59,716, 95,041, 66.0%
    nums = set(re.findall(r"(?<![\w.])\d{1,3}(?:,\d{3})+(?![\w.])|"
                          r"(?<![\w,])\d+\.\d+(?![\w])", text))
    # figures that belong to the prose rather than to a run
    # section references, standard numbers and figures the note explicitly
    # marks as DERIVED rather than run. Every entry here is a decision to
    # exempt something, so the set is short and each addition is deliberate.
    PROSE_OK = {"61508", "1.4"} | {f"{a}.{b}" for a in range(1, 8)
                                   for b in range(0, 10)}
    orphans = sorted(n for n in nums
                     if n not in PROSE_OK and n not in every
                     and n.replace(",", "") not in every)
    for n in orphans:
        print(f"     [ORPHAN] {n}")
    if not orphans:
        print("     none — every figure in the note appears in some run")
    else:
        bad.append(("(note)", f"{len(orphans)} orphan figure(s)", str(orphans)))

    print("\n  4. WHAT THIS DOES NOT CHECK")
    print("     The prose, and whether a figure MEANS in the note what it")
    print("     meant in the run. `0.117` passed for a day while the note")
    print("     called it a measurement and the model was deterministic.")
    print("     A number can be present, correct, and still misdescribed.")
    print("     Beyond that: a note whose figures are right and whose claims")
    print("     are wrong passes here — the ceiling named in KNOWN-LIMITS,")
    print("     and the place Frege's mistake lived. This file closes the")
    print("     half that can be closed by machine and says so rather than")
    print("     letting a green line imply the other half.")

    if bad:
        print(f"\n  RED: {len(bad)} claim(s) no longer supported:")
        for p, s, m in bad:
            print(f"     {p}: {s}  (missing: {m!r})")
        return 1
    print(f"\nNOTE CLAIMS GREEN — {len(CLAIMS)} claims and "
          f"{sum(len(f) for _p, f in FIGURES)} figures still printed by the "
          f"code.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
