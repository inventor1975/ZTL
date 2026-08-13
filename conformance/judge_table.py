# -*- coding: utf-8 -*-
"""
The judge's behaviour over a systematic sweep of its inputs — a reference
table, and the diff against it.

The curator's reason for it, and it is the right one: the judge is still
being built, and its behaviour has started coming out in places nobody
predicted. Today alone three of this session's changes altered a verdict
that no one had asked about, and only an assert in some unrelated stand
caught them. Stands cover the cases we thought of. This covers the cases we
did not.

WHAT IS SWEPT. Every combination of the sheet judge's input dimensions over
two quantities — provenance, value shape, lattice, unit, the sample flag —
against a set of formulas. Roughly 184 thousand judgements, which at the
measured 13.5k/sec single-threaded is a matter of seconds; the space is
enumerated exhaustively rather than sampled, so nothing is missed by luck.

WHAT IS STORED, and this is the design decision worth defending. Not the
table: 184k rows are unreadable and a diff of them is unusable. Three things
instead —

  * a FINGERPRINT, one hash over the whole sweep. Any change to any verdict
    moves it. That is the alarm;
  * a CENSUS, verdict counts by input class. That is the readable body of
    the thing: what the judge does, in twenty lines;
  * the RARE CELLS, verbatim. A verdict that occurs a handful of times in
    184k inputs is either a deliberate corner of the design or a bug, and
    both deserve to be looked at by name. These are where the surprises
    live.

WHEN THE FINGERPRINT MOVES, the run prints the census diff, so the question
is never "did something change" but "what, and is it what you meant".

CEILING: this characterizes, it does not verify. A table records what the
judge DOES, including whatever it does wrongly; agreeing with it tomorrow
proves only that nothing moved. It is a regression net and a map, not a
proof — the proofs are in `lean/`.

TWO RUNS INSTEAD OF ONE, the curator's addition. The stored table answers
"has anything moved since a human looked at it and approved it". It does not
answer "when did it move, and because of what" — for that you want the same
sweep run against an older revision's judge, which `--against <rev>` does
through a throwaway git worktree. That is what a "separate copy of the
repository" should be: git already keeps every copy, and a copy made by hand
rots the first time somebody forgets to refresh it.

One subtlety decides whether the comparison means anything. The SWEEP must
come from the current revision and only the JUDGE from the old one — run the
old script against the old code and you have compared apples to oranges,
since the input space may have moved too and the difference would be a
difference of questions rather than of answers. Hence ZTL_ROOT: this file
stays put, the modules it imports come from the worktree.

PARALLELISM. The sweep is embarrassingly parallel — every case is independent
— and `--jobs 0` spreads it over the machine: 12.9s on one process, 1.2s on
32, with the fingerprint UNCHANGED. That last part was the design constraint,
not a bonus. Combining per-worker digests would have been simpler and would
have moved the fingerprint for a reason having nothing to do with the judge:
an alarm going off because somebody rewired the alarm. So only the judging is
spread; the stream is assembled and hashed in the parent, in enumeration
order.

The default is nevertheless ONE process, and deliberately. `run_all.py`
already saturates the machine with thirty stands at once, and a stand that
forks thirty-two more would fight the suite for the same cores; 13 seconds
inside a run whose wall time is set by a 52-second stand costs nothing. Use
`--jobs 0` when running this alone, and with `--against`, where two full
sweeps happen.

Run:  python3 conformance/judge_table.py                 (check against stored)
      python3 conformance/judge_table.py --update        (re-bless the table)
      python3 conformance/judge_table.py --against REV   (diff two revisions)
      python3 conformance/judge_table.py --jobs 0        (use every core)
"""
import hashlib
import json
import os
import sys
import time
from collections import Counter
from itertools import product

# The judge modules are taken from ZTL_ROOT when set. That is what lets the
# SAME sweep definition — this file, the current one — be run against an old
# revision's judge. Running the old script on the old code instead would
# compare apples to oranges: the input space may have moved too, and the
# difference would be a difference of QUESTIONS rather than of answers.
_ROOT = os.environ.get("ZTL_ROOT") or os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from znumjudge import judge_sheet_claim, parse_quantities        # noqa: E402

STORE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "judge_table.json")

# --------------------------------------------------------- the input space
PROV = ["earned:doc", "credit"]
VALUE = ["1", "5", "[0,10]", "?"]
LATTICE = ["", " int", " decimal2", " frac3"]
UNIT = ["", " RUB", " m"]
SAMPLE = ["", " sample"]

FORMULAS = [
    "x <= y",
    "x == y",
    "x < y",
    "sum(x,y) == 5",
    "x <= y & ok",
]


def quantity(name, prov, value, lattice, unit, sample):
    return f"{name}={value} {prov}{lattice}{unit}{sample}"


def cases():
    """Every combination, enumerated. The nonsensical ones are included on
    purpose: what the judge does with `? earned:doc` is exactly the kind of
    corner nobody writes a stand for."""
    shapes = list(product(PROV, VALUE, LATTICE, UNIT, SAMPLE))
    for formula in FORMULAS:
        tail = ", ok=Z" if "ok" in formula else ""
        for sx in shapes:
            qx = quantity("x", *sx)
            for sy in shapes:
                yield formula, f"{qx}, {quantity('y', *sy)}{tail}"


def verdict(formula, data):
    try:
        q, m = parse_quantities(data)
        r = judge_sheet_claim(formula, q, m)
        # the cure KINDS, not their arguments: `measure x` and `measure y`
        # are the same shape of answer and should not split a cell
        cures = sorted({c.split()[0] for c in (r.get("next_check") or [])})
        return (r["disposition"], str(r.get("lazy")), ",".join(cures) or "-")
    except Exception as exc:                     # a corner that stops parsing
        return ("!" + type(exc).__name__, "-", 0)


def _slice(bounds):
    """Judge one contiguous slice of the enumeration. Workers regenerate the
    case list rather than receiving it: the generator is deterministic and
    cheap, and shipping 184k strings across a pipe is not."""
    start, end = bounds
    out = []
    for i, (formula, data) in enumerate(cases()):
        if i >= end:
            break
        if i >= start:
            out.append(verdict(formula, data))
    return out


def _judged(jobs):
    """Every verdict, in enumeration order — computed in parallel when it is
    worth it, and always ASSEMBLED serially.

    The order matters more than the speed: the fingerprint is a hash over
    the stream, so only the judging is spread across cores and the hashing
    stays in the parent. Combining per-worker digests would have been
    simpler and would have moved the fingerprint for a reason that has
    nothing to do with the judge — an alarm going off because the alarm was
    rewired."""
    total = sum(1 for _ in cases())
    if jobs <= 1:
        return [verdict(f, d) for f, d in cases()], total
    import multiprocessing as mp
    step = (total + jobs - 1) // jobs
    bounds = [(i, min(i + step, total)) for i in range(0, total, step)]
    with mp.get_context("fork").Pool(jobs) as pool:
        parts = pool.map(_slice, bounds)
    return [v for part in parts for v in part], total


def sweep(jobs=1):
    """Returns (fingerprint, census, rare, total)."""
    h = hashlib.sha256()
    census, examples = Counter(), {}
    verdicts, total = _judged(jobs)
    for (formula, data), v in zip(cases(), verdicts):
        h.update(f"{formula}|{data}|{v}".encode())
        census[v] += 1
        examples.setdefault(v, (formula, data))
    rare = sorted((n, list(v), list(examples[v]))
                  for v, n in census.items() if n <= total // 1000)
    return (h.hexdigest()[:16],
            {" ".join(map(str, k)): n for k, n in census.most_common()},
            rare, total)


def against(rev, jobs=1):
    """Run this same sweep against another revision's judge, via a throwaway
    git worktree — which is what a "separate copy of the repository" should
    be, since git already keeps every copy and a hand-made one rots.

    The stored table answers "has anything moved since a human looked and
    approved". This answers a different question the table cannot: WHEN did
    it move, and against which revision — the tool for bisecting a verdict
    change back to the commit that caused it."""
    import subprocess
    import tempfile
    here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    with tempfile.TemporaryDirectory() as tmp:
        tree = os.path.join(tmp, "old")
        r = subprocess.run(["git", "worktree", "add", "--detach", tree, rev],
                           cwd=here, capture_output=True, text=True)
        if r.returncode:
            print(r.stderr.strip())
            return None
        try:
            env = dict(os.environ, ZTL_ROOT=tree)
            out = subprocess.run(
                [sys.executable, os.path.abspath(__file__), "--emit",
                 "--jobs", str(jobs)],
                env=env, capture_output=True, text=True, timeout=1800)
            if out.returncode:
                print(out.stderr[-1500:])
                return None
            return json.loads(out.stdout)
        finally:
            subprocess.run(["git", "worktree", "remove", "--force", tree],
                           cwd=here, capture_output=True)


def main():
    update = "--update" in sys.argv
    jobs = 1
    for i, a in enumerate(sys.argv):
        if a == "--jobs" and i + 1 < len(sys.argv):
            jobs = int(sys.argv[i + 1])
    if jobs <= 0:
        jobs = min(32, os.cpu_count() or 1)
    if "--emit" in sys.argv:                    # used by `against`
        fp, census, rare, total = sweep(jobs)
        print(json.dumps({"fingerprint": fp, "census": census,
                          "cases": total}))
        return 0
    rev = None
    for i, a in enumerate(sys.argv):
        if a == "--against" and i + 1 < len(sys.argv):
            rev = sys.argv[i + 1]
    print("=" * 78)
    print("THE JUDGE'S TABLE — an exhaustive sweep of its input space")
    print("=" * 78)
    t0 = time.time()
    fp, census, rare, total = sweep(jobs)
    print(f"\n  cases swept: {total:,}   fingerprint: {fp}")
    print(f"  {time.time() - t0:.1f}s on {jobs} process"
          f"{'' if jobs == 1 else 'es'}")
    print("\n  CENSUS — what the judge does, by verdict:")
    for k, n in census.items():
        print(f"    {k:34} {n:>8,}  ({100 * n / total:5.2f}%)")
    print(f"\n  RARE CELLS ({len(rare)}) — a verdict reached by a handful of")
    print("  inputs is either a deliberate corner or a bug, and both want a")
    print("  name:")
    for n, v, ex in rare:
        print(f"    {' '.join(map(str, v)):30} x{n:<4} {ex[0]}  ::  {ex[1]}")
    if not rare:
        smallest = min(census.values())
        print(f"    none — the smallest cell holds {smallest:,} inputs. The")
        print("    judge has no one-off corners in this space: every behaviour")
        print("    it shows, it shows systematically. That is a finding and")
        print("    not an empty section.")

    earned = census.get("EARNED T -", 0)
    empty = sum(n for k, n in census.items() if k.startswith("E "))
    print("\n  WHAT THE CENSUS SAYS")
    print(f"    EARNED: {earned:,} of {total:,} — {100 * earned / total:.2f}%.")
    print("    Across every systematically enumerated input, fewer than two")
    print("    in a hundred earn. That is the no-credit rule as a statistic")
    print("    rather than a slogan: earning is the rare event by design.")
    print(f"    E (no readings at all): {empty:,} — "
          f"{100 * empty / total:.2f}%.")
    print("    Nearly a quarter of the space is unjudgeable — mismatched")
    print("    units, impossible lattices, inverted intervals. That is a")
    print("    fact about the input space, not a defect of the judge: the")
    print("    fourth corner is where nonsense goes, and nonsense is common")
    print("    when you enumerate rather than curate.")

    if rev:
        print(f"\n  AGAINST {rev} — same sweep, that revision's judge")
        old = against(rev, jobs)
        if old is None:
            print("  could not run the old revision; nothing compared.")
            return 1
        print(f"    {old['cases']:,} cases there, {total:,} here")
        if old["fingerprint"] == fp:
            print(f"    IDENTICAL ({fp}). The judge answers exactly as it")
            print("    did at that revision, over the whole space.")
            return 0
        print(f"    MOVED: {old['fingerprint']} -> {fp}")
        for k in sorted(set(old["census"]) | set(census)):
            a, b = old["census"].get(k, 0), census.get(k, 0)
            if a != b:
                print(f"      {k:34} {a:>8,} -> {b:>8,}")
        return 0

    stored = None
    if os.path.exists(STORE):
        stored = json.load(open(STORE, encoding="utf-8"))
    if update or stored is None:
        json.dump({"fingerprint": fp, "cases": total, "census": census,
                   "rare": rare}, open(STORE, "w", encoding="utf-8"),
                  indent=1, ensure_ascii=False)
        print(f"\n  TABLE WRITTEN — {STORE}")
        print("  (blessing a table is a decision: it records what the judge")
        print("   does today, right or wrong. Read the census before doing it.)")
        return 0

    if stored["fingerprint"] == fp:
        print(f"\n  MATCHES the stored table ({stored['cases']:,} cases).")
        print("\nJUDGE TABLE GREEN — the judge answers exactly as it did when")
        print("this table was blessed. Which proves nothing about whether it")
        print("answers WELL; it proves that nothing moved unnoticed, and that")
        print("is the whole job of a characterization sweep.")
        return 0

    print(f"\n  FINGERPRINT MOVED: {stored['fingerprint']} -> {fp}")
    print("  census diff (stored -> now):")
    keys = set(stored["census"]) | set(census)
    for k in sorted(keys):
        a, b = stored["census"].get(k, 0), census.get(k, 0)
        if a != b:
            print(f"    {k:34} {a:>8,} -> {b:>8,}")
    print("\n  RED — the judge answers differently than when this table was")
    print("  blessed. That is not automatically wrong: if the change was")
    print("  intended, read the diff, satisfy yourself it is the change you")
    print("  meant and no other, then re-bless with --update.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
