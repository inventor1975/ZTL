# -*- coding: utf-8 -*-
"""
grounds — PSSL leg 1: one generator, four grounds, comparable columns.

PSSL §2 arranges four logics as four resolutions of one diagonal, each
"classical logic minus exactly one structural principle". That sentence
is written as a description of four cases. Here it is read as a
PARAMETER, which turns the arrangement into a generator:

    a GROUND is what you refuse to grant;
    its WITNESS is the price list of what still transports.

So four grounds are put through ONE procedure on ONE battery and each is
asked exactly one question — does Γ ⊨ φ. Nothing is re-derived by hand
from four literatures; the columns are comparable by construction.

DESIGN, settled in words before code (pssl/PREREGISTRATION.md):

  D1  A ground is given by an ORACLE, not by a matrix. One matrix for all
      four is impossible: IPC has no finite characteristic matrix (Gödel
      1932). The generator asks `entails` and does not care how the
      answer is produced — no corner is forced into another's vocabulary.
  D2  The quantum corner DECLARES its implication. MO2 has no canonical
      →; we take the Sasaki hook, already measured in this repository
      (dilemmas/quantum_ladder.py: Sasaki MP, 216/216 triples). Which →
      you use is part of the ground, not neutral plumbing.
  D3  The price list is DOUBLE — laws and rules, for every ground. The
      central finding of ZTL is that these come apart; a single-number
      column would lie. The gap between them is the measured quantity.

THE GAP, defined precisely. For each rule Γ ⊨ φ that HOLDS in a ground,
ask whether the corresponding law ⋀Γ → φ is valid there. A ground with
the deduction theorem answers yes every time; the gap counts the rules
that survive as rules but fall as laws. It is the deduction theorem's
failure, counted.

Oracles reused, not rewritten: `zipc.py` (cpc/ipc/ztl) and the MO2
lattice of `dilemmas/quantum_ladder.py`.

Run:  python3 pssl/grounds.py
"""
import itertools
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)
sys.path.insert(0, os.path.join(_ROOT, "dilemmas"))

import zipc                                                   # noqa: E402
import quantum_ladder as QL                                   # noqa: E402
from ztl import T, F, ev                                      # noqa: E402
from entailment import entails                                # noqa: E402


# ---------------------------------------------------------------------------
# Syntax helpers — the battery is shared, so the language must be too
# ---------------------------------------------------------------------------
def atoms_of(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        acc.add(phi)
    else:
        for sub in phi[1:]:
            atoms_of(sub, acc)
    return acc


def conj(fs):
    """⋀Γ as a formula; the empty conjunction is the trivial premise."""
    if not fs:
        return None
    out = fs[0]
    for f in fs[1:]:
        out = ("and", out, f)
    return out


# ---------------------------------------------------------------------------
# Ground 4 — MO2, the quantum corner (lattice from quantum_ladder.py)
# ---------------------------------------------------------------------------
def mo2_eval(phi, asg):
    """Evaluate into MO2. Implication is the SASAKI HOOK, by declaration."""
    if isinstance(phi, str):
        return asg[phi]
    op = phi[0]
    if op == "not":
        return QL.NEG[mo2_eval(phi[1], asg)]
    a = mo2_eval(phi[1], asg)
    b = mo2_eval(phi[2], asg)
    if op == "and":
        return QL.meet(a, b)
    if op == "or":
        return QL.join(a, b)
    if op == "imp":
        return QL.sasaki(a, b)
    raise ValueError(f"MO2: no reading for {op}")


def mo2_assignments(phi_list):
    names = sorted(set().union(*(atoms_of(f) for f in phi_list if f is not None)))
    for combo in itertools.product(QL.ELS, repeat=len(names)):
        yield dict(zip(names, combo))


def mo2_valid(phi):
    """φ is a LAW of MO2 iff it takes the top element under every reading."""
    return all(mo2_eval(phi, a) == "top" for a in mo2_assignments([phi]))


def mo2_derives(premises, conclusion):
    """Γ ⊨ φ in an ortholattice: ⋀Γ ≤ φ under every reading."""
    fs = list(premises) + [conclusion]
    for a in mo2_assignments(fs):
        c = mo2_eval(conclusion, a)
        if not premises:
            if c != "top":
                return False
            continue
        m = mo2_eval(premises[0], a)
        for p in premises[1:]:
            m = QL.meet(m, mo2_eval(p, a))
        if not QL.leq(m, c):
            return False
    return True


# ---------------------------------------------------------------------------
# The four grounds, each a pair of oracles. THIS is the parameter PSSL §2
# describes: what the ground refuses, and what it still transports.
# ---------------------------------------------------------------------------
def cpc_derives(premises, conclusion):
    fs = list(premises) + [conclusion]
    names = sorted(set().union(*(atoms_of(f) for f in fs)))
    for combo in itertools.product((T, F), repeat=len(names)):
        asg = dict(zip(names, combo))
        if all(ev(p, asg) == T for p in premises) and ev(conclusion, asg) != T:
            return False
    return True


GROUNDS = [
    ("classical", "nothing refused",
     zipc.cpc_valid, cpc_derives),
    ("intuitionistic", "excluded middle refused",
     zipc.ipc_valid, zipc.ipc_derives),
    ("quantum MO2", "distributivity refused (→ = Sasaki hook)",
     mo2_valid, mo2_derives),
    ("ZTL", "identity p→p, LEM, DNE refused at the mark",
     zipc.ztl_valid, lambda g, c: entails(list(g), c) is None),
]


# ---------------------------------------------------------------------------
# The two price lists and the gap between them
# ---------------------------------------------------------------------------
def price_list_laws():
    rows = []
    for name, formula, _canon in zipc.LAWS:
        rows.append((name, [valid(formula) for _, _, valid, _ in GROUNDS]))
    return rows


def price_list_rules():
    rows = []
    for name, prems, concl in zipc.RULES:
        rows.append((name, [der(list(prems), concl)
                            for _, _, _, der in GROUNDS]))
    return rows


def deduction_gap():
    """Rules that hold as RULES but fall as LAWS — the deduction theorem's
    failure, counted per ground. Zero iff the ground exports every rule
    into its own object language."""
    gaps = [[] for _ in GROUNDS]
    for name, prems, concl in zipc.RULES:
        antecedent = conj(list(prems))
        law = concl if antecedent is None else ("imp", antecedent, concl)
        for i, (_, _, valid, der) in enumerate(GROUNDS):
            if der(list(prems), concl) and not valid(law):
                gaps[i].append(name)
    return gaps


def deduction_theorem_gap(pool, ctx_sizes=(0, 1)):
    """The deduction theorem, in its ACTUAL form, swept over a generated
    battery:

        Γ, γ ⊨ φ   ⟹   Γ ⊨ γ → φ

    The discharged premise moves right across the arrow; the REST of Γ
    stays on the left. Getting this wrong cost three passes in leg 1, and
    the way it was wrong is worth recording because it is the exact
    failure mode ZTL exists to catch — testing a convenient form and
    reading the answer as if it were the real statement:

      * the curated 14-rule battery reported gap 0 for MO2. False: the
        deduction theorem fails there on 32/216 triples. The classical
        canon contains no non-commuting instance — you cannot price a
        ground with another ground's battery.
      * a one-premise sweep cannot see MO2 either: a ≤ b already gives
        a →s b = top in any ortholattice.
      * folding all premises into one conjoined antecedent is blind to
        BOTH: in MO2 because ⋀Γ ≤ φ again exports for free, and in ZTL
        because ∧ collapses the mark (Z∧Z = F) before → ever sees it.

    Only the real statement, with a context left standing, sees either.
    """
    gaps = [0] * len(GROUNDS)
    firsts = [None] * len(GROUNDS)
    holds = [0] * len(GROUNDS)
    for k in ctx_sizes:
        ctxs = [[]] if k == 0 else [[c] for c in pool]
        for ctx in ctxs:
            for gamma in pool:
                for phi in pool:
                    disch = ("imp", gamma, phi)
                    for i, (_, _, valid, der) in enumerate(GROUNDS):
                        if not der(ctx + [gamma], phi):
                            continue
                        holds[i] += 1
                        ok = valid(disch) if not ctx else der(ctx, disch)
                        if not ok:
                            gaps[i] += 1
                            if firsts[i] is None:
                                firsts[i] = (ctx, gamma, phi)
    return gaps, holds, firsts


def show(title, rows):
    print(f"\n{'=' * 78}\n{title}\n{'=' * 78}")
    head = "".join(f"{g[0][:13]:>15s}" for g in GROUNDS)
    print(f"  {'':44s}{head}")
    tally = [0] * len(GROUNDS)
    for name, cols in rows:
        cells = "".join(f"{'  ✓' if c else '  ✗':>15s}" for c in cols)
        print(f"  {name[:44]:44s}{cells}")
        for i, c in enumerate(cols):
            tally[i] += bool(c)
    print(f"  {'ALIVE':44s}" + "".join(f"{t:>15d}" for t in tally))
    return tally


if __name__ == "__main__":
    print("=" * 78)
    print("PSSL LEG 1 — four grounds, one generator")
    print("  a ground is what you refuse to grant;")
    print("  its witness is the price list of what still transports.")
    print("=" * 78)
    for nm, refuses, _, _ in GROUNDS:
        print(f"  {nm:16s} {refuses}")

    laws = show("PRICE LIST — LAWS (⊨ φ)", price_list_laws())
    rules = show("PRICE LIST — RULES (Γ ⊨ φ)", price_list_rules())

    print(f"\n{'=' * 78}\nTHE GAP — rules that hold, whose law falls\n{'=' * 78}")
    print("  Zero iff the ground exports every rule into its object")
    print("  language, i.e. iff it has the deduction theorem.\n")
    gaps = deduction_gap()
    for (nm, _, _, _), g in zip(GROUNDS, gaps):
        print(f"  {nm:16s} gap {len(g):2d}"
              + (f"   {', '.join(x.split()[0] for x in g[:6])}" if g else ""))

    print(f"\n{'=' * 78}\nTHE DEDUCTION THEOREM — real statement, generated battery")
    print(f"{'=' * 78}")
    print("  The curated battery above reports gap 0 for MO2. That is FALSE")
    print("  about MO2: the deduction theorem fails there on 32 of 216")
    print("  triples (non-commuting pairs). The fourteen classical rules")
    print("  contain no such instance — the canon is blind to a ground that")
    print("  is not classical. So: generate the pairs instead.\n")
    print("  Nor a one-premise sweep (a ≤ b already gives a →s b = top),")
    print("  nor a conjoined antecedent (∧ collapses the ZTL mark first).")
    print("  Only the real statement:  Γ, γ ⊨ φ  ⟹  Γ ⊨ γ → φ.\n")
    pool = zipc.build_pool(("p", "q"), depth=1)
    print(f"  pool: {len(pool)} formulas, contexts of size 0 and 1")
    ggaps, gholds, gfirst = deduction_theorem_gap(pool)
    for (nm, _, _, _), gp, hd, fw in zip(GROUNDS, ggaps, gholds, gfirst):
        w = (f"   first: {fw[0]}, {fw[1]} ⊨ {fw[2]}" if fw else "")
        print(f"  {nm:16s} holding {hd:6d}   gap {gp:6d}{w}")

    print(f"\n{'=' * 78}\nPREDICTION P1 (pre-registered, pssl/PREREGISTRATION.md)")
    print("  gap = 0 for classical and intuitionistic;")
    print("  gap > 0 for ZTL and quantum.")
    print("  Judged on the deduction theorem in its real form — the curated")
    print("  14-rule battery is not an instrument that can decide this.")
    got = ggaps   # the REAL statement, not the curated battery
    p1 = (got[0] == 0 and got[1] == 0 and got[2] > 0 and got[3] > 0)
    print(f"  measured gaps: {dict(zip([g[0] for g in GROUNDS], got))}")
    print(f"  P1 {'HOLDS' if p1 else 'FAILS'} — "
          + ("the family splits 2/2 on an axis PSSL does not use:"
             if p1 else "read the columns before reading a meaning into them."))
    if p1:
        print("    grounds WITH the deduction theorem : classical, intuitionistic")
        print("    grounds WITHOUT it                 : quantum MO2, ZTL")
        print("  PSSL cuts by WHICH PRINCIPLE IS DROPPED. This cuts by whether")
        print("  the ground can export a rule into its own object language —")
        print("  and the two cuts do not coincide.")

    nc = [name for name, _, _ in zipc.LAWS if "non-contradiction" in name]
    print(f"\nPREDICTION P2 — non-contradiction (the PSSL floor) in all four:")
    for nm, cols in price_list_laws():
        if "non-contradiction" in nm:
            print(f"  {nm.strip()}: "
                  + ", ".join(f"{g[0]}={'✓' if c else '✗'}"
                              for g, c in zip(GROUNDS, cols)))
            print(f"  P2 {'HOLDS' if all(cols) else 'FAILS'}")
