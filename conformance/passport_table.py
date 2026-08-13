# -*- coding: utf-8 -*-
"""
The passport office over every three-sentence system — the net over the
instrument with published verdicts behind it.

Of the three instruments still unswept this one was taken first, and not
alphabetically. `zpassport` is what issues the passports in *The Paradox
Docket* (v1.1, DOI 10.5281/zenodo.21916017): twenty-one published rows, each
a claim about how many classical solutions a self-referential system has. A
silent change here does not produce a red stand — it produces a false
sentence in an issued paper. `inventory/docket_claims.py` re-measures those
twenty-one rows every run, which pins what we published; this pins the
INSTRUMENT, including the thousand systems nobody thought to publish.

WHAT IS SWEPT. Every system of three sentences, each defined by one of a
vocabulary that reaches every shape the office distinguishes: a constant, a
plain reference, a negated reference, a conjunction, a disjunction, and the
self-forcing `xnor` that gives INTRINSIC its single model. 12^3 = 1,728
systems, exhaustively, and for each the whole answer — every component, its
passport, its solution count, its oscillation period, plus the stipulation
theorem's own tallies.

THE COUNT IS THE POINT here in a way it is not elsewhere. The docket's
central claim is arithmetical: zero solutions, one, or many exhaust a finite
system, and each maps to a fate. If that map ever changed, this fingerprint
moves and the paper needs a correction.

CEILING: characterizes, does not verify — the same bargain as the other
tables. Three sentences is a bounded family, not the space of all systems;
Yablo lives in an actual infinity and no sweep reaches him.

Run:  python3 conformance/passport_table.py            (check against stored)
      python3 conformance/passport_table.py --update   (re-bless)
"""
import hashlib
import json
import os
import sys
from collections import Counter
from itertools import product

_ROOT = os.environ.get("ZTL_ROOT") or os.path.dirname(
    os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

from zpassport import (passports, component_models, deps,         # noqa: E402
                       oscillation_period, stipulation_theorem)

STORE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     "passport_table.json")

NAMES = ["s0", "s1", "s2"]

# Every shape the office distinguishes, reachable from one sentence.
DEFS = [
    "T", "F", "Z",
    "s0", "s1", "s2",
    ("not", "s0"), ("not", "s1"), ("not", "s2"),
    ("and", "s0", "s1"), ("or", "s1", "s2"), ("xnor", "s0", "s0"),
]


def systems():
    for combo in product(DEFS, repeat=len(NAMES)):
        yield dict(zip(NAMES, combo))


def read(system):
    """The whole answer: every component's passport, model count and period,
    plus the stipulation theorem's tallies for the system."""
    try:
        lfp, reports, _ = passports(system)
        rows = []
        for comp, kind, _why in reports:
            env_names = set()
            for s in comp:
                env_names |= deps(system[s]) - set(comp)
            env = {n: lfp[n] for n in env_names}
            models = len(list(component_models(comp, system, env)))
            period = oscillation_period(comp, system, env)
            rows.append((tuple(comp), kind, models, period))
        return tuple(sorted(rows)), stipulation_theorem(system)
    except Exception as exc:
        return ("!" + type(exc).__name__,), ()


def sweep():
    h = hashlib.sha256()
    census, examples, total = Counter(), {}, 0
    kinds, violations = Counter(), []
    for system in systems():
        rows, stip = read(system)
        h.update(f"{sorted(system.items())}|{rows}|{stip}".encode())
        if not rows:                       # every sentence grounded outright
            key = ("GROUNDED-ALL",)
        elif isinstance(rows[0], str):
            key = (rows[0],)
        else:
            key = tuple(sorted({(r[1], r[2]) for r in rows}))
            for r in rows:
                kinds[r[1]] += 1
                # The docket's arithmetic governs the LOOP passports only.
                # INPUT and DOWNSTREAM are the off-loop ones and the paper
                # lists them apart; applying the count to them was this
                # file's first draft, and it reported 797 violations of a
                # rule it had invented. The sweep screaming at a check
                # rather than at the instrument is the check's job too.
                if r[1] not in ("PARADOX", "INTRINSIC", "UNDERDETERMINED"):
                    continue
                if (r[1] == "PARADOX") != (r[2] == 0):
                    violations.append((system, r))
                if r[1] == "INTRINSIC" and r[2] != 1:
                    violations.append((system, r))
                if r[1] == "UNDERDETERMINED" and r[2] < 2:
                    violations.append((system, r))
        census[key] += 1
        examples.setdefault(key, dict(system))
        total += 1
    rare = sorted((n, str(list(k)), str(examples[k]))
                  for k, n in census.items() if n <= max(2, total // 100))
    return (h.hexdigest()[:16],
            {str(list(k)): n for k, n in census.most_common()},
            rare, total, dict(kinds.most_common()), violations)


def main():
    print("=" * 78)
    print("THE PASSPORT TABLE — every three-sentence system, exhaustively")
    print("=" * 78)
    fp, census, rare, total, kinds, violations = sweep()
    print(f"\n  systems swept: {total:,}   fingerprint: {fp}")
    print(f"  components by passport: {kinds}")
    loops = sum(n for k, n in kinds.items()
                if k in ("PARADOX", "INTRINSIC", "UNDERDETERMINED"))
    print(f"\n  THE DOCKET'S ARITHMETIC — 0 solutions is PARADOX, 1 is")
    print("  INTRINSIC, 2+ is UNDERDETERMINED — checked on every LOOP")
    print(f"  component of every system ({loops:,} of them, the off-loop")
    print(f"  INPUT and DOWNSTREAM being governed by a different rule):")
    print(f"  {len(violations)} violations")
    for system, row in violations[:5]:
        print(f"    {system}  ->  {row}")
    if violations:
        print("  RED — the published docket rests on this map. A violation")
        print("  here is a correction to an issued paper, not a failing test.")
        return 1
    print("  None. The map the paper publishes holds over the whole family,")
    print("  not only over the twenty-one rows that were written down.")
    print(f"\n  CENSUS ({len(census)} shapes), the ten commonest:")
    for k, n in list(census.items())[:10]:
        print(f"    {k[:64]:64} {n:>5}")
    print(f"\n  RARE SHAPES ({len(rare)}), the first five:")
    for n, k, ex in rare[:5]:
        print(f"    {k[:60]:60} x{n}")
        print(f"      e.g. {ex}")

    stored = json.load(open(STORE, encoding="utf-8")) \
        if os.path.exists(STORE) else None
    if "--update" in sys.argv or stored is None:
        json.dump({"fingerprint": fp, "systems": total, "census": census,
                   "kinds": kinds, "rare": rare},
                  open(STORE, "w", encoding="utf-8"), indent=1,
                  ensure_ascii=False)
        print(f"\n  TABLE WRITTEN — {STORE}")
        return 0
    if stored["fingerprint"] == fp:
        print(f"\n  MATCHES the stored table ({stored['systems']:,} systems).")
        print("\nPASSPORT TABLE GREEN — the office answers exactly as it did")
        print("when this table was blessed, over every three-sentence system")
        print("and not only over the ones a paper happened to quote.")
        return 0
    print(f"\n  FINGERPRINT MOVED: {stored['fingerprint']} -> {fp}")
    for k in sorted(set(stored["census"]) | set(census)):
        a, b = stored["census"].get(k, 0), census.get(k, 0)
        if a != b:
            print(f"    {k[:64]:64} {a:>5} -> {b:>5}")
    print("\n  RED — and this one has a published paper behind it. Before")
    print("  re-blessing, check whether any docket row moved.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
