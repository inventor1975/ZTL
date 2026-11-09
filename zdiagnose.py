# -*- coding: utf-8 -*-
"""
WHICH PREMISE IS SUSPECT — a measurement against a stated law with stated inputs (2026-11-09).

The curator, after ztl-stand's physics round 2 (six stated laws refuted by their measurements): «Ты говоришь, мы
физику не учли. Но она же входящая, по входу всё верно посчитано?» — yes: the arithmetic is right; what fails is the
SET OF PREMISES the case gives as input. Which one? This module answers what logic can answer: the minimal sets of
premises that are jointly INCOMPATIBLE with the measurement (conflicts), and the minimal sets of premises to re-read so
that the measurement can fit (diagnoses). Which diagnosis is the true one is not logic's to say — a check is.

PREMISES. Each input is a premise with a STATED range (as the source gives it) and a RELAXED range (what is physically
admissible if the source's value is wrong — a premise of the diagnosis itself, said by whoever writes it). The law is a
premise too: the quantity is read as g · law, g = 1 stated, g in `law_relaxed` relaxed ("the law may be off").

CONFLICT. A set S of premises kept STATED (all others relaxed) is in conflict with the measurement [m_lo, m_hi] iff
ZTL's numeric judge REFUTES `q >= m_lo` (q < m_lo at every point) or REFUTES `q <= m_hi`. A judge that says OPEN does
not make a conflict: every conflict reported is PROVED, none is presumed. Conflicts are monotone (keeping more premises
stated narrows q), so the minimal ones are found by size.

DIAGNOSIS. "Every conflict has a false premise" — the measurement makes it so — is a formula over premise atoms, each
DIRTY (the source's word, not verified by us): AND over conflicts C of OR over i in C of NOT p_i. zbackward's
POSSIBILITY family for the target EARNED is the minimal sets of premises whose reading can earn it — the minimal
hitting sets of the conflicts (Reiter's diagnoses). Cross-checked by direct enumeration in `diagnose`.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import zbackward as ZBK                    # noqa: E402
import znumjudge as ZJ                     # noqa: E402
from ztl import Z                          # noqa: E402

LAW = "law"


def _num(x):
    """An exact fraction for the sheet (its reader takes no scientific notation): the value as written."""
    from fractions import Fraction
    f = Fraction(str(x)) if not isinstance(x, Fraction) else x
    return str(f.numerator) if f.denominator == 1 else f"{f.numerator}/{f.denominator}"


def _sheet(premises, kept, law_relaxed):
    parts = []
    for n, (st, rx) in premises.items():
        lo, hi = st if n in kept else rx
        parts.append(f"{n}=[{_num(lo)},{_num(hi)}] earned")
    g = (1, 1) if LAW in kept else law_relaxed
    parts.append(f"g_law=[{_num(g[0])},{_num(g[1])}] earned")
    return ", ".join(parts)


def _conflict(expr, premises, kept, measured, law_relaxed):
    qs = ZJ.parse_quantities(_sheet(premises, kept, law_relaxed))[0]
    q = f"g_law*({expr})"
    lo = ZJ.judge_sheet_claim(f"{q} >= {_num(measured[0])}", dict(qs), {})["disposition"]
    hi = ZJ.judge_sheet_claim(f"{q} <= {_num(measured[1])}", dict(qs), {})["disposition"]
    return lo == "REFUTED" or hi == "REFUTED"


def _formula(conflicts):
    """AND over conflicts of OR over NOT p — as zbackward's tuples."""
    def big(op, xs):
        out = xs[0]
        for x in xs[1:]:
            out = (op, out, x)
        return out
    return big("and", [big("or", [("not", p) for p in sorted(c)]) for c in conflicts])


def diagnose(expr, premises, measured, law_relaxed=(0.5, 2)):
    """premises: {name: ((stated_lo, stated_hi), (relaxed_lo, relaxed_hi))}; measured: (lo, hi).
    -> {"conflicts": [...], "diagnoses": [...], "consistent_as_stated": bool, "check": "..."}"""
    names = list(premises) + [LAW]
    conflicts = []
    for k in range(1, len(names) + 1):
        for S in itertools.combinations(names, k):
            if any(set(c) <= set(S) for c in conflicts):
                continue                                   # a superset of a conflict: not minimal
            if _conflict(expr, premises, set(S), measured, law_relaxed):
                conflicts.append(tuple(S))
    out = {"conflicts": conflicts, "consistent_as_stated": not conflicts}
    if not conflicts:
        out["diagnoses"] = []
        return out
    phi = _formula(conflicts)
    atoms = sorted({p for c in conflicts for p in c})
    r = ZBK.backward(phi, {p: Z for p in atoms}, "EARNED")
    diag = sorted(tuple(sorted(s)) for s in r["possible"])
    # cross-check: the minimal hitting sets by enumeration
    hits = []
    for k in range(1, len(atoms) + 1):
        for H in itertools.combinations(atoms, k):
            if all(set(H) & set(c) for c in conflicts) and not any(set(h) <= set(H) for h in hits):
                hits.append(H)
    out["diagnoses"] = diag
    out["check"] = "zbackward == the minimal hitting sets" if diag == sorted(tuple(sorted(h)) for h in hits) else \
        f"MISMATCH: zbackward {diag} vs hitting sets {hits}"
    return out
