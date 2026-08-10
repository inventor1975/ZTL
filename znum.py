# -*- coding: utf-8 -*-
"""
Expedition E37: znum — the numeric floor of ZTL (probe).

Design: ZNUM-DESIGN-draft.md (stage 1, curator-accepted forks F1-F3):
  F1  occurrences read DECORRELATED, as in the propositional lift (m-m != 0);
  F2  a bare number is a number ON CREDIT: [x,x] with unearned bounds;
  F3  the two credit axes stay SEPARATE and both are reported:
        interval axis   — is the verdict forced by the current intervals?
        provenance axis — are the bounds themselves earned by witnesses?

The floor is an ATOM SUPPLIER: comparisons over quantities yield T/F/Z
atoms; formulas over those atoms are judged by the UNCHANGED core
(ztljudge) — demonstrated in section 4 below.

The measured bet of this expedition (design §4): interval narrowing is
monotone, therefore on purely numeric atoms a FORCED verdict can never be
revoked by any further narrowing — hereditary in ONE PASS, against the
m-1-deep enumeration the propositional grade costs. Section 3 hunts for a
counterexample over an exhaustive grid, correlated occurrences included.

Run:  python3 znum.py
"""
import itertools
import math
import os
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztljudge import judge                              # noqa: E402

INF = math.inf
EARNED, CREDIT = "earned", "credit"


# ------------------------------------------------------------- quantities
def qty(lo, hi, provenance=CREDIT, witness=None, discrete=None, unit=None):
    """A quantity: interval [lo, hi] + provenance of its bounds + TYPE.

    The type is a FORMALIZATION commitment, not knowledge: it filters the
    READING SET (readings = lattice(discrete) ∩ [lo, hi]) and needs no
    witness; expire never touches it. `discrete`: None (continuous
    rationals), "int", or ("decimal", k) — the lattice of multiples of
    10^-k. `unit`: a name ("candies", "RUB") or None (dimensionless).
    The declared bounds are tightened to the lattice at construction; an
    EMPTY reading set is a formalization error (E_EMPTY_DOMAIN), never a
    vacuous verdict."""
    assert lo <= hi
    assert provenance in (EARNED, CREDIT)
    step = _step(discrete)
    if step is not None:
        tlo = lo if lo == -INF else math.ceil(lo / step - 1e-12) * step
        thi = hi if hi == INF else math.floor(hi / step + 1e-12) * step
        if tlo > thi:
            raise ValueError(
                f"E_EMPTY_DOMAIN: no {discrete} reading in [{lo}, {hi}]")
        lo, hi = tlo, thi
    return {"lo": lo, "hi": hi, "prov": provenance, "witness": witness,
            "discrete": discrete, "unit": unit}


def _step(discrete):
    """Lattice step of a discreteness type; None = continuous."""
    if discrete == "int":
        return 1
    if isinstance(discrete, tuple) and discrete[0] == "decimal":
        return 10 ** (-discrete[1])
    return None


def _on_lattice(value, step):
    return abs(value / step - round(value / step)) < 1e-9


def bare(x):
    """F2: a bare number = [x, x] on credit — usable, never load-bearing
    above ON CREDIT."""
    return qty(x, x, CREDIT)


# ------------------------------------------- the lift: interval arithmetic
def _iv_add(a, b): return (a[0] + b[0], a[1] + b[1])
def _iv_sub(a, b): return (a[0] - b[1], a[1] - b[0])


def _iv_mul(a, b):
    ps = [x * y for x in a for y in b]
    return (min(ps), max(ps))


def _iv_div(a, b):
    if b[0] <= 0 <= b[1]:
        return None                       # divisor may be 0: undefined (§25 echo)
    inv = (1 / b[1], 1 / b[0])
    return _iv_mul(a, inv)


def _unify_units(u1, u2, ctx):
    """Dimensionless (None) unifies with anything; named units must match
    for additive/comparative contexts — a mismatch is a FORMALIZATION
    error (E_UNIT), caught before any verdict."""
    if u1 is None:
        return u2
    if u2 is None or u1 == u2:
        return u1
    raise ValueError(f"E_UNIT: cannot {ctx} '{u1}' with '{u2}'")


def _ev(expr, quantities):
    """Rich evaluator: (interval|None, pedigree, used, lattice_step, unit).
    Discreteness is tracked exactly through +, -, *, sum (integer lattices
    are closed there) and is dropped at division — a conservative
    over-approximation: derived-expression verdicts may stay Z where a
    finer analysis could refute, but a forced verdict is never wrong."""
    if isinstance(expr, (int, float)):
        step = 1 if float(expr).is_integer() else None
        return (expr, expr), set(), set(), step, None
    if isinstance(expr, str):
        q = quantities[expr]
        pedigree = {expr} if q["prov"] == CREDIT else set()
        return ((q["lo"], q["hi"]), pedigree, {expr},
                _step(q.get("discrete")), q.get("unit"))
    op, *args = expr
    if op == "sum":
        iv, ped, used, step, unit = (0, 0), set(), set(), 1, None
        for a in args[0]:
            r, p, u, st, un = _ev(a, quantities)
            unit = _unify_units(unit, un, "add")
            if r is None:
                return None, ped | p, used | u, None, unit
            step = st if step is None or st is None else (
                st if st == step else None)
            iv, ped, used = _iv_add(iv, r), ped | p, used | u
        return iv, ped, used, step, unit
    ra, pa, ua, sa, una = _ev(args[0], quantities)
    rb, pb, ub, sb, unb = _ev(args[1], quantities)
    ped, used = pa | pb, ua | ub
    if op in ("add", "sub"):
        unit = _unify_units(una, unb, "add")
        step = sa if sa == sb else None
    elif op == "mul":
        unit = una if unb is None else (unb if una is None else f"{una}·{unb}")
        step = 1 if sa == 1 and sb == 1 else None
    else:  # div
        unit = (None if una == unb else
                una if unb is None else
                f"{una or '1'}/{unb}")
        step = None
    if ra is None or rb is None:
        return None, ped, used, step, unit
    f = {"add": _iv_add, "sub": _iv_sub, "mul": _iv_mul, "div": _iv_div}[op]
    return f(ra, rb), ped, used, step, unit


def ev(expr, quantities):
    """Public 3-tuple view (interval | None, credit_pedigree, atoms) —
    unchanged contract; see _ev for types. Occurrences decorrelated (F1);
    credit pedigree flows pessimistically."""
    iv, ped, used, _, _ = _ev(expr, quantities)
    return iv, ped, used


# ---------------------------------------------------- comparisons -> atoms
def compare(kind, e1, e2, quantities):
    """A numeric atom. Verdict by the generating principle over intervals:
    T if forced under every reading, F if the negation is forced, else Z.
    Returns (verdict, credit_pedigree, quantities_read)."""
    r1, p1, u1, s1, un1 = _ev(e1, quantities)
    r2, p2, u2, s2, un2 = _ev(e2, quantities)
    _unify_units(un1, un2, "compare")     # unit mismatch = E_UNIT, pre-verdict
    ped, used = p1 | p2, u1 | u2
    if r1 is None or r2 is None:
        return "Z", ped, used             # undefined subterm: mark, not verdict
    if kind == "le":
        v = "T" if r1[1] <= r2[0] else ("F" if r1[0] > r2[1] else "Z")
    elif kind == "lt":
        v = "T" if r1[1] < r2[0] else ("F" if r1[0] >= r2[1] else "Z")
    elif kind == "eq":                     # equality within exactness (§13:
        d = _iv_sub(r1, r2)                # only forced equality is earned)
        v = "T" if d == (0, 0) else ("F" if d[0] > 0 or d[1] < 0 else "Z")
        if v == "Z":                       # lattice miss: an int-typed side
            for sa, rb in ((s1, r2), (s2, r1)):   # can never equal a point
                if sa is not None and rb[0] == rb[1] \
                        and not _on_lattice(rb[0], sa):
                    v = "F"                # off the lattice: forced false
    else:
        raise ValueError(kind)
    return v, ped, used


# --------------------------------------- the two axes (F3) + the numeric judge
def judge_claim(kind, e1, e2, quantities):
    """Judge one numeric claim on BOTH axes, kept separate (F3):

      interval axis:    FORCED (T/F) or NOT_FORCED (Z) — cured by narrowing;
      provenance axis:  EARNED or ON_CREDIT — cured by a witness.

    Disposition = the meet of the axes; carriers name what holds it up."""
    v, ped, used = compare(kind, e1, e2, quantities)
    interval_axis = "FORCED" if v in ("T", "F") else "NOT_FORCED"
    prov_axis = "ON_CREDIT" if ped else "EARNED"
    if v == "Z":
        disp = "OPEN"
    elif ped:
        disp = "ON CREDIT"
    else:
        disp = "EARNED" if v == "T" else "REFUTED"
    # carriers, SPLIT BY AXIS (F3 continued): each axis degrades separately,
    # so next_check can say WHICH cure the quantity needs.
    #   interval carrier:   widening the interval to full ignorance (its own
    #                       provenance kept) changes the verdict -> MEASURE it;
    #   provenance carrier: the verdict is forced and stays forced, but this
    #                       quantity's CREDIT bounds are what the claim rides
    #                       on -> DOCUMENT it (witness converts the claim
    #                       from ON CREDIT toward EARNED).
    interval_carriers = []
    for name in sorted(used):
        degraded = dict(quantities)
        degraded[name] = qty(-INF, INF, quantities[name]["prov"])
        if compare(kind, e1, e2, degraded)[0] != v:
            interval_carriers.append(name)
    provenance_carriers = []
    if v in ("T", "F"):
        # a credit quantity is a provenance carrier iff witnessing it (alone)
        # removes it from the pedigree the forced verdict rides on
        for name in sorted(ped):
            healed = dict(quantities)
            healed[name] = dict(quantities[name], prov=EARNED)
            _, ped2, _ = compare(kind, e1, e2, healed)
            if ped2 == ped - {name}:
                provenance_carriers.append(name)
    return {"verdict": v, "interval_axis": interval_axis,
            "provenance_axis": prov_axis, "credit_pedigree": sorted(ped),
            "disposition": disp, "interval_carriers": interval_carriers,
            "provenance_carriers": provenance_carriers,
            "next_check": (
                [f"measure {n}" for n in interval_carriers if v == "Z"]
                + [f"document {n}" for n in provenance_carriers])}


# ============================================================== the bench
def sec1_lift_and_axes():
    print("-" * 72)
    print("1. THE LIFT AND THE TWO AXES")
    m = {"m": qty(0, 9, EARNED, "sensor-a")}
    iv, _, _ = ev(("sub", "m", "m"), m)
    print(f"   decorrelation (F1): m - m over m=[0,9]  ->  {iv}")
    assert iv == (-9, 9)                       # not 0: occurrences independent
    d = {"x": qty(1, 2, EARNED), "z": qty(-1, 1, EARNED)}
    r, _, _ = ev(("div", "x", "z"), d)
    assert r is None                           # divisor spans 0: undefined
    print("   x / z with 0 in z  ->  undefined  ->  any atom reading it is Z")
    # two axes separate (F3):
    a = judge_claim("le", "p", 10, {"p": qty(3, 5, EARNED, "doc-1")})
    assert a["disposition"] == "EARNED" and a["interval_axis"] == "FORCED"
    b = judge_claim("le", "p", 10, {"p": bare(4)})
    assert b["disposition"] == "ON CREDIT" and b["interval_axis"] == "FORCED"
    assert b["credit_pedigree"] == ["p"]       # F2: bare number infects
    c = judge_claim("le", "p", 4, {"p": qty(3, 5, EARNED)})
    assert c["disposition"] == "OPEN" and c["interval_axis"] == "NOT_FORCED"
    print("   same claim, three fates:")
    print(f"     earned [3,5]  <= 10 : {a['disposition']} (forced, earned)")
    print(f"     bare 4        <= 10 : {b['disposition']} (forced, bounds unearned)")
    print(f"     earned [3,5]  <= 4  : {c['disposition']} (overlap: cure = narrow)")
    print("   the cures differ: ON CREDIT needs a WITNESS, OPEN needs a MEASUREMENT")


def sec2_claims_sheet():
    print("-" * 72)
    print("2. THE CLAIMS SHEET (the riding task, in miniature)")
    q = {"line1": qty(1000, 1000, EARNED, "invoice-17"),
         "line2": qty(2000, 2000, EARNED, "invoice-18"),
         "line3": bare(1800),                          # unverified line
         "budget": qty(5000, 5000, EARNED, "order-o4")}
    smeta = judge_claim("le", ("sum", ["line1", "line2", "line3"]), "budget", q)
    print(f"   smeta: sum(lines) <= budget -> {smeta['disposition']}, "
          f"weak link {smeta['credit_pedigree']}")
    print(f"     next_check: {smeta['next_check']}")
    assert smeta["disposition"] == "ON CREDIT"
    assert smeta["credit_pedigree"] == ["line3"]
    assert smeta["provenance_carriers"] == ["line3"]   # cure: DOCUMENT line3
    assert smeta["next_check"] == ["document line3"]   # not "measure" anything
    # the same claim after the witness arrives:
    q2 = dict(q); q2["line3"] = qty(1800, 1800, EARNED, "invoice-19")
    assert judge_claim("le", ("sum", ["line1", "line2", "line3"]),
                       "budget", q2)["disposition"] == "EARNED"
    print("   after invoice-19 arrives: EARNED — the cure was a document")
    # denominator discipline: a rate without an earned denominator
    r = {"detected": qty(50, 50, EARNED, "run-log"),
         "attempted": bare(50)}
    rate = judge_claim("eq", "detected", "attempted", r)
    print(f"   '100% detection' (detected = attempted): {rate['disposition']}, "
          f"weak link {rate['credit_pedigree']}")
    assert rate["disposition"] == "ON CREDIT"
    assert rate["credit_pedigree"] == ["attempted"]
    print("   the rate is true-on-credit until the denominator is witnessed —")
    print("   the claim-discipline we enforce by hand, now a button")


def sec3_theorem_hunt():
    print("-" * 72)
    print("3. THE BET, MEASURED: forced verdicts survive every narrowing")
    grid = range(-2, 3)
    intervals = [(lo, hi) for lo in grid for hi in grid if lo <= hi]

    def subintervals(iv):
        return [(a, b) for a in grid for b in grid
                if iv[0] <= a <= b <= iv[1]]

    pool = [("le", "a", "b"), ("lt", "a", "b"), ("eq", "a", "b"),
            ("le", ("add", "a", "b"), 2), ("le", ("mul", "a", "b"), "b"),
            ("eq", ("sub", "a", "a"), 0),          # correlated occurrences
            ("le", ("mul", "a", "a"), 4),          # correlated, nonlinear
            ("le", ("div", "b", "a"), 2),          # division: undefined cells
            ("lt", ("sub", ("mul", "a", "b"), "a"), 3)]
    checks = revocations = forced_seen = 0
    for kind, e1, e2 in pool:
        for ia in intervals:
            for ib in intervals:
                qs = {"a": qty(*ia, EARNED), "b": qty(*ib, EARNED)}
                v0 = compare(kind, e1 if isinstance(e1, tuple) else e1,
                             e2, qs)[0]
                if v0 == "Z":
                    continue
                forced_seen += 1
                for na in subintervals(ia):
                    for nb in subintervals(ib):
                        qn = {"a": qty(*na, EARNED), "b": qty(*nb, EARNED)}
                        v1 = compare(kind, e1, e2, qn)[0]
                        checks += 1
                        if v1 != v0:
                            revocations += 1
                            print(f"   COUNTEREXAMPLE: {kind} {e1} {e2} "
                                  f"a={ia}->{na} b={ib}->{nb}: {v0}->{v1}")
    print(f"   9 comparison shapes (correlated + division included), "
          f"{forced_seen} forced start cells,")
    print(f"   {checks} narrowing pairs checked: {revocations} revocations")
    assert revocations == 0, "the bet is DEAD — record the counterexample"
    print("   THE BET STANDS on this grid: narrowing is monotone, a forced")
    print("   verdict is hereditary BY ONE PASS — no m-1 enumeration needed.")
    print("   (Kernel half: lean/ZNum.lean proves it STRUCTURALLY for every")
    print("   expression, marking and narrowing chain — readings semantics,")
    print("   empty axiom list; division excluded there by the grammar and")
    print("   measured here instead.)")


def sec4_seam_with_the_judge():
    print("-" * 72)
    print("4. THE SEAM: numeric atoms feed the UNCHANGED core")
    q = {"total": qty(4800, 4800, EARNED, "ledger"),
         "budget": qty(5000, 5000, EARNED, "order-o4"),
         "deadline_ok": None}  # non-numeric atom left to the core as Z
    under = compare("le", "total", "budget", q)[0]
    marking = {"under_budget": under}          # numeric floor supplies the atom
    r = judge("under_budget & deadline_ok", marking)
    print(f"   under_budget := {under} (from znum), deadline_ok := Z (unknown)")
    print(f"   core verdict on 'under_budget & deadline_ok': "
          f"{r['disposition']} — {r['why']}")
    assert under == "T" and r["disposition"] == "OPEN"
    assert r["unverified"] == ["deadline_ok"]
    print("   ztljudge untouched: znum is an atom supplier, not a new logic")


if __name__ == "__main__":
    print("=" * 72)
    print("E37: ZNUM — the numeric floor of ZTL (probe)")
    print("=" * 72)
    sec1_lift_and_axes()
    sec2_claims_sheet()
    sec3_theorem_hunt()
    sec4_seam_with_the_judge()
    print("=" * 72)
    print("E37 GREEN — the lift extends to numbers (decorrelated, F1); bare")
    print("numbers are credit (F2); the two credit axes stay separate and")
    print("name their different cures (F3); forced numeric verdicts survived")
    print("every narrowing on the measured grid (the one-pass hereditary bet")
    print("stands, boundary stated); and the core judges numeric atoms")
    print("without changing a single line.")
