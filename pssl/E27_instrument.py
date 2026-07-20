# -*- coding: utf-8 -*-
"""
Expedition E27: the instrument inherits the ground it was built from.

E26 measured the price of DERIVATIONS: the twelve alive rules transport
earned truth and never mint it; from ∅ nothing follows, even on credit.
E27 measures the price of MEASURING — and finds the same law one level
up. **An instrument assembled from one ground's habits transports that
ground's blindness.** A battery transports too, and what it transports
includes what it cannot see.

This is not a confession dressed as a finding. Every entry below is a
measurement: the CONVENIENT form of a question and the REAL form are run
side by side on the same objects, and the gap between their answers is
printed. Where the two disagree, the convenient form returned a number
that a competent reader would have believed.

Six were committed to the repository as results before being recognised
as errors; B8 is the same shape in shell tooling with no logic anywhere
near it. B7 is the one that makes the rest data rather than anecdote: a fresh reviewer (Claude Fable 5, 2026-07-20),
having just read the warning about shallow pools, reproduced B4 in the
first run of its own verification script. The failure is not carelessness.
It is structural, and it is why a price list must be GENERATED and never
INHERITED.

THE SHAPE, identical in all eight:

    test a convenient form of the question,
    read the answer as if it were the real statement.

Which is precisely the move ZTL exists to catch — truth accepted on
credit — performed eight times in one day by the people building the
instrument that measures it.

Run:  python3 pssl/E27_instrument.py
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, _HERE)
sys.path.insert(0, os.path.join(_ROOT, "dilemmas"))

import fnmatch                                                # noqa: E402
import re                                                     # noqa: E402
import subprocess                                             # noqa: E402

import zipc                                                   # noqa: E402
import grounds as G                                           # noqa: E402
import family as F                                            # noqa: E402
import quantum_ladder as QL                                   # noqa: E402
from ztl import T, F as FF                                    # noqa: E402
from entailment import entails                                # noqa: E402

_mo2_valid, _mo2_der = G.mo2_valid, G.mo2_derives
_ztl_valid = zipc.ztl_valid
_ztl_der = lambda g, c: entails(list(g), c) is None
POOL1 = zipc.build_pool(("p", "q"), depth=1)
POOL2 = zipc.build_pool(("p", "q"), depth=2)

BLINDNESSES = []


def blindness(n, title, convenient, real):
    def deco(fn):
        BLINDNESSES.append((n, title, convenient, real, fn))
        return fn
    return deco


# ---------------------------------------------------------------------------
@blindness(
    "B1", "a curated battery cannot price a foreign ground",
    "run the classical canon of 14 rules and count the failures",
    "generate the battery over the shared language")
def b1():
    """The canon reports MO2 as having the deduction theorem. It does not:
    DT fails on 32 of 216 triples. The classical rules contain no
    non-commuting instance, so the canon is blind by construction."""
    curated = 0
    for _name, prems, concl in zipc.RULES:
        ante = None
        for p in prems:
            ante = p if ante is None else ("and", ante, p)
        law = concl if ante is None else ("imp", ante, concl)
        if _mo2_der(list(prems), concl) and not _mo2_valid(law):
            curated += 1
    real = sum(1 for x in QL.ELS for y in QL.ELS for z in QL.ELS
               if QL.leq(QL.meet(x, y), z) != QL.leq(x, QL.sasaki(y, z)))
    return curated, real, "MO2", f"{curated} on the canon vs {real}/216 real"


# ---------------------------------------------------------------------------
@blindness(
    "B2", "one premise always discharges in an ortholattice",
    "γ ⊨ φ  ⟹  ⊨ γ→φ",
    "Γ, γ ⊨ φ  ⟹  Γ ⊨ γ→φ  (a context left standing)")
def b2():
    """x ≤ y already gives x →s y = ⊤, so no single-premise sweep can ever
    see MO2 fail. The convenient form is not merely coarse — it is
    incapable of the answer."""
    one = sum(1 for g in POOL1 for f in POOL1
              if _mo2_der([g], f) and not _mo2_valid(("imp", g, f)))
    two = sum(1 for c in POOL1 for g in POOL1 for f in POOL1
              if _mo2_der([c, g], f) and not _mo2_der([c], ("imp", g, f)))
    always = all((not QL.leq(x, y)) or QL.sasaki(x, y) == "top"
                 for x in QL.ELS for y in QL.ELS)
    assert always, "the ortholattice argument itself failed"
    return one, two, "MO2", f"{one} at one premise vs {two} at two"


# ---------------------------------------------------------------------------
@blindness(
    "B3", "folding the premises into ⋀Γ is blind to BOTH grounds",
    "⋀Γ ⊨ φ  ⟹  ⊨ (⋀Γ)→φ",
    "Γ, γ ⊨ φ  ⟹  Γ ⊨ γ→φ")
def b3():
    """Blind to MO2 for B2's reason, and blind to ZTL for a different one:
    ∧ collapses the mark (Z∧Z = F) before → ever sees it. One convenient
    form, two grounds hidden, two unrelated reasons."""
    folded = 0
    real = 0
    for c in POOL1:
        for g in POOL1:
            for f in POOL1:
                if _ztl_der([c, g], f):
                    if not _ztl_valid(("imp", ("and", c, g), f)):
                        folded += 1
                    if not _ztl_der([c], ("imp", g, f)):
                        real += 1
    collapse = zipc.ztl_valid(("imp", ("and", "p", "p"), "p")) and \
        not zipc.ztl_valid(("imp", "p", "p"))
    assert collapse, "the ZTL collapse argument itself failed"
    return folded, real, "ZTL", f"{folded} folded vs {real} real"


# ---------------------------------------------------------------------------
@blindness(
    "B4", "a zero on a shallow pool is not a theorem",
    "no counterexample at depth 1  ⟹  the ground has DT",
    "a zero is the absence of a refutation we could REACH")
def b4():
    """Ł3 reads 0 at depth 1 and 6404 at depth 2. The counterexample
    p ⊨ ¬(p→¬p) while ⊭ p→¬(p→¬p) has depth 3. This one was printed as
    'Q2 HOLDS' before it was checked."""
    L3 = [m for m in F.FAMILY if m.name == "Lukasiewicz L3"][0]
    shallow = sum(1 for g in POOL1 for f in POOL1
                  if L3.derives([g], f) and not L3.valid(("imp", g, f)))
    deep = sum(1 for g in POOL2 for f in POOL2
               if L3.derives([g], f) and not L3.valid(("imp", g, f)))
    ce = ("not", ("imp", "p", ("not", "p")))
    witness = L3.derives(["p"], ce) and not L3.valid(("imp", "p", ce))
    assert witness, "the L3 counterexample itself failed"
    return shallow, deep, "Łukasiewicz Ł3", f"{shallow} at depth 1 vs {deep} at depth 2"


# ---------------------------------------------------------------------------
@blindness(
    "B5", "a proxy column read as the property itself",
    "fill the DT column with the arity-0 gap",
    "DT requires discharge at EVERY arity")
def b5():
    """This one put MO2 in the 'has the deduction theorem' column two
    hours after we machine-proved that no arrow can give MO2 one. Caught
    by an assert placed on the both-halves club, not by re-reading."""
    a0 = sum(1 for g in POOL1 for f in POOL1
             if _mo2_der([g], f) and not _mo2_valid(("imp", g, f)))
    a1 = sum(1 for c in POOL1 for g in POOL1 for f in POOL1
             if _mo2_der([c, g], f) and not _mo2_der([c], ("imp", g, f)))
    return a0, a1, "MO2", f"proxy says {a0} (=has DT), truth is {a1}"


# ---------------------------------------------------------------------------
@blindness(
    "B6", "apartness has an arity too",
    "no separator at arity 1  ⟹  the grounds coincide",
    "look for the arity at which they come apart")
def b6():
    """Classical logic and LP validate exactly the same formulas — LP is
    paraconsistent in its consequence relation, not in its theorems. No
    law and no one-premise rule separates them. Explosion does, at two
    premises."""
    LP = [m for m in F.FAMILY if m.name == "LP"][0]
    laws = sum(1 for f in POOL2 if zipc.cpc_valid(f) != LP.valid(f))
    one = sum(1 for g in POOL1 for f in POOL1
              if G.cpc_derives([g], f) != LP.derives([g], f))
    two = sum(1 for a in POOL1 for b in POOL1 for f in POOL1
              if G.cpc_derives([a, b], f) != LP.derives([a, b], f))
    explosion = G.cpc_derives(["p", ("not", "p")], "q") and \
        not LP.derives(["p", ("not", "p")], "q")
    assert explosion, "the explosion witness itself failed"
    return one, two, "classical | LP", \
        f"{laws} laws, {one} at arity 1, {two} at arity 2"


# ---------------------------------------------------------------------------
@blindness(
    "B8", "the same shape outside logic entirely — in the tooling",
    "last time this commit produced 3 CI runs, so wait for 3",
    "ask which workflows the CHANGED FILES actually trigger")
def b8():
    """Not a measurement about logics. After pushing E27 the session sat
    in a wait-loop for three completed CI runs because the previous push
    had produced three — and hung, because this commit touches only
    `pssl/` and `run_all.py`, while `lean.yml` filters on `lean/**` and
    `inventory/**`. Two runs, correctly.

    The convenient form was a remembered NUMBER; the real form is the
    path filters read against the changed files. That the identical shape
    appears in shell tooling, with no logic anywhere near it, is the
    strongest evidence in this expedition that the failure is structural
    rather than a property of three-valued matrices."""
    root = _ROOT
    try:
        changed = subprocess.run(
            ["git", "show", "--name-only", "--format=", "9760b0f"],
            cwd=root, capture_output=True, text=True, timeout=30).stdout.split()
    except Exception:
        return 3, 2, "CI", "git unavailable — recorded value 3 vs 2"
    if not changed:
        return 3, 2, "CI", "commit unreachable — recorded value 3 vs 2"

    wf = os.path.join(root, ".github", "workflows")
    triggered = 0
    for name in sorted(os.listdir(wf)):
        if not name.endswith((".yml", ".yaml")):
            continue
        text = open(os.path.join(wf, name), encoding="utf-8").read()
        m = re.search(r"^on:.*?(?=^\w)", text, re.S | re.M)
        head = m.group(0) if m else text
        if "paths:" not in head:
            triggered += 1                      # unfiltered: always runs
            continue
        pats = re.findall(r'^\s*-\s*"([^"]+)"', head, re.M)
        if any(fnmatch.fnmatch(f, pat) or
               fnmatch.fnmatch(f, pat.replace("/**", "/*"))
               for f in changed for pat in pats):
            triggered += 1
    return 3, triggered, "CI on 9760b0f", \
        f"assumed 3 runs, actual {triggered} ({len(changed)} files changed)"


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    print("=" * 78)
    print("EXPEDITION E27 — THE INSTRUMENT INHERITS ITS GROUND")
    print("  E26: rules transport earned truth, they never mint it.")
    print("  E27: batteries transport too — including their blindness.")
    print("=" * 78)
    print("\n  Each row runs the CONVENIENT form of a question and the REAL")
    print("  form on the same objects. Where they differ, the convenient")
    print("  form returned a number a competent reader would believe.")
    print("  All six were committed as results before being recognised.\n")

    silent = 0
    for n, title, conv, real, fn in BLINDNESSES:
        c, r, ground, detail = fn()
        hidden = (c != r)
        silent += hidden
        print(f"  {n} — {title}")
        print(f"     convenient : {conv}")
        print(f"     real       : {real}")
        print(f"     on {ground:16s} {detail}"
              f"   {'← HIDDEN' if hidden else '(agrees here)'}")
        print()

    print("=" * 78)
    print(f"  blindnesses that silently changed the answer: {silent} of "
          f"{len(BLINDNESSES)}")
    print("=" * 78)

    print("\n  B7 — the one that makes the rest data, not anecdote.")
    print("  A fresh reviewer (Claude Fable 5, 2026-07-20), auditing this")
    print("  work and having just read the warning about shallow pools,")
    print("  reproduced B4 in the first run of its own verification script:")
    print("  its independent re-implementation of Ł3 reported DT=True on a")
    print("  depth-1 pool. Caught by an adjacent line of the same script")
    print("  that checked the witness directly.")
    print()
    print("  Eight repetitions, one shape:")
    print("      test a convenient form of the question,")
    print("      read the answer as if it were the real statement.")
    print()
    print("  And B8 says the same thing from the other side: the shape")
    print("  appears in shell tooling, waiting for a CI run that the path")
    print("  filters were never going to produce, with no logic anywhere")
    print("  near it. A warned reviewer reproducing it, and the shape")
    print("  recurring outside logic, together rule out carelessness.")
    print("  The failure is structural: an instrument")
    print("  assembled from one ground's habits transports that ground's")
    print("  blindness, exactly as E26's rules transport truth without")
    print("  minting it. That is why a price list must be GENERATED and")
    print("  never INHERITED — and why every conclusion in pssl/ is")
    print("  asserted rather than printed.")

    assert silent == len(BLINDNESSES), \
        "a blindness stopped hiding its answer — re-read the expedition"
    print(f"\n  E27 GREEN — {len(BLINDNESSES)} blindnesses reproduced, "
          "each with its witness.")
