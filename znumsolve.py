# -*- coding: utf-8 -*-
"""
znumsolve — the judge learns to narrow: a solver that issues receipts.

Stage 2 of the plan settled in words with the curator. Until now the
numeric floor computed FORWARDS: given the quantities, judge the claim.
That made it a checker and not a solver — "x + x == 10" came back OPEN
with the cure "measure x", which is true and useless, since the sheet
already says everything needed to pin x.

Backward narrowing closes that. Each comparison is read as a CONSTRAINT
and pushed back onto the quantities it mentions; the pass repeats to a
fixed point. The rule per variable is hull consistency: drop exactly
those values of x for which NO choice of the other quantities inside
their own boxes satisfies the constraint. That is sound by construction —
a value is removed only when it is refuted whatever the others do — and
section 3 measures it anyway, on an exhaustive grid, because "sound by
construction" is the kind of sentence this project does not accept from
others.

Two properties make this ours rather than a small interval solver:

  * the TYPE does the last mile. x + x == 10 over the rationals gives
    x = 5 outright; k == 8/3 with k an integer gives the EMPTY box, which
    is a refutation and not a failure to converge. The lattice is what
    turns narrowing into an answer.
  * the answer carries its RECEIPT. A pinned value inherits the
    provenance of every bound that pinned it, so the solver says not just
    "x = 5" but "x = 5, ON CREDIT, because line3's bound is undocumented"
    — with the cure attached.

Honest boundaries, stated before the examples: propagation runs over
CONJUNCTIONS of comparisons only (a disjunction constrains nothing on its
own); it is exact on the linear fragment and silently skipped outside it,
never guessed; `sample` quantities are not narrowed at all, since each
occurrence is a separate act and the constraint speaks about occurrences,
not about the name; and an interval solver returns a BOX, so a
non-degenerate answer is the normal case, not a bug.

Run:  python3 znumsolve.py
"""
import os
import re
import sys
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from znum import (INF, EARNED, CREDIT, qty, num, fmt, _linear,   # noqa: E402
                  _NotLinear, _step, typename, _poly, _rat_sqrt, _NoReadings)
from znumjudge import (parse_quantities, extract_comparisons,     # noqa: E402
                       judge_sheet_claim, _closes_last)

MAX_ROUNDS = 32


def _hull(kind, form_c, terms, name, quantities):
    """The values of `name` that survive the constraint, given the others.

    `form_c + Σ k·x  ⋈  0` with ⋈ from the comparison. Isolate the
    variable, evaluate the rest over its current box, and keep exactly the
    values for which SOME choice of the rest satisfies the constraint."""
    k = sum(coef for key, (coef, nm) in terms.items() if nm == name)
    if k == 0:
        return None
    rlo = rhi = form_c
    for key, (coef, nm) in terms.items():
        if nm == name:
            continue
        q = quantities[nm]
        ends = (coef * q["lo"], coef * q["hi"])
        rlo, rhi = rlo + min(ends), rhi + max(ends)
    # k·x ⋈ -rest, with rest ranging over [rlo, rhi]
    strict_lo = strict_hi = False
    if kind == "eq":
        lo, hi = -rhi, -rlo
    elif kind == "le":
        lo, hi = -INF, -rlo
    else:                                    # lt: the upper bound is STRICT
        lo, hi = -INF, -rlo
        strict_hi = True
    if k < 0:
        lo, hi = (-hi if hi != INF else -INF), (-lo if lo != -INF else INF)
        strict_lo, strict_hi = strict_hi, strict_lo
        k = -k
    lo = lo if lo == -INF else lo / k
    hi = hi if hi == INF else hi / k
    return lo, hi, strict_lo, strict_hi


def _parabola_pieces(kind, p, q, c, box):
    """The parts of `box` where  q·x² + p·x + c ⋈ 0  can hold, from the
    discriminant (a line, q = 0, is taken for `eq` too). Roots are enclosed by
    the square root's rational clamp, exact when D is a rational square; each
    piece is a SUPERSET of the true solutions in it (strictness is not used to
    tighten), so narrowing to the pieces is sound, and none is a refutation."""
    if q == 0:
        if kind != "eq" or p == 0:
            return None
        r = -c / p
        sets = [(r, r)]
    else:
        d = p * p - 4 * q * c
        roots = []
        if d >= 0:
            s_lo, s_hi = _rat_sqrt(d)
            for sg in (-1, 1):
                ends = ((-p + sg * s_lo) / (2 * q), (-p + sg * s_hi) / (2 * q))
                roots.append((min(ends), max(ends)))
            roots.sort()
            if d == 0:
                roots = roots[:1]
        if kind == "eq":
            sets = roots
        elif q > 0:                  # q·x² + p·x + c <= 0 between the roots
            sets = [(roots[0][0], roots[-1][1])] if roots else []
        else:                        # ... and outside them when q < 0
            sets = ([(-INF, roots[0][1]), (roots[1][0], INF)] if len(roots) == 2
                    else [(-INF, INF)])
    pieces = []
    for lo, hi in sets:
        lo, hi = max(lo, box["lo"]), min(hi, box["hi"])
        if lo <= hi:
            pieces.append((lo, hi))
    return pieces


def _quadratic(kind, e1, e2, qs):
    """ONE unknown under a quadratic constraint: the parts of its box that
    can satisfy  q·x² + p·x + c ⋈ 0, found from the discriminant.

    The curator's X*X-2X+5=0 (2026-09-24): D = p² - 4qc < 0 means no real x
    makes the equation true, which is a refutation, not a stall; D = 0 gives
    one root, D > 0 two, and both are kept («корня-то два»). Returns
    (name, pieces, seen) or None when the constraint is not one parabola in
    one non-sample unknown."""
    seen = set()
    try:
        c, terms, _, _ = _poly(("sub", e1, e2), qs, [0], seen)
    except (_NotLinear, KeyError, _NoReadings):
        return None
    live = [(k, t) for k, t in terms.items() if t[0] != 0 or t[1] != 0]
    if len(live) != 1:
        return None
    key, (p, q, name) = live[0]
    if q == 0 or key != name:
        return None                  # linear (the linear rule's), or a sample
    return name, _parabola_pieces(kind, p, q, c, qs[name]), seen


def _solve_monomial_system(qs, atoms):
    """Exact elimination over the equalities, x and x² as SEPARATE columns.

    The curator's plot (2026-09-24): `area == s*s & area - 2*s + 5 == 0`. No
    equality alone is one parabola in one unknown, and the linear system has
    one usable row in two unknowns. With each power of each name its own
    column, elimination is still exact linear algebra over Fractions, and
    every row it derives is a CONSEQUENCE of the equalities: a row left in
    ONE name is solved outright (a line pins it, a parabola goes to the
    discriminant), and 0 = c != 0 refutes. Names that never appear squared
    are eliminated first, so what is left speaks of the rest.
    Returns (rows in one name as (name, p, q, c), inconsistent, contributors)."""
    eqs, contributors = [], set()
    for kind, e1, e2, chunk in atoms.values():
        if kind != "eq":
            continue
        seen = set()
        try:
            c, terms, _, _ = _poly(("sub", e1, e2), qs, [0], seen)
        except (_NotLinear, KeyError, _NoReadings):
            continue
        row = {}
        for key, (p, q, nm) in terms.items():
            if key != nm:                    # a sample's occurrence
                row = None
                break
            for deg, coef in ((1, p), (2, q)):
                if coef:
                    row[(nm, deg)] = row.get((nm, deg), Fraction(0)) + coef
        if row is None:
            continue
        row = {k: v for k, v in row.items() if v != 0}
        if not row:
            # A ROW OF CONSTANTS is the judge's, not the system's: 4 + 4 == 10
            # with 10 on credit is ON CREDIT (false, on a ground not yet
            # earned), and deciding it here as "inconsistent" laundered that
            # into REFUTED. Caught by conformance/solver_table.py, 2026-09-24:
            # 24 of 336 cases moved; the linear system has always skipped them.
            continue
        contributors |= seen
        eqs.append((row, -c))
    if not eqs:
        return [], False, set()
    squared = {nm for row, _ in eqs for (nm, deg) in row if deg == 2}
    cols = sorted({k for row, _ in eqs for k in row},
                  key=lambda k: (k[0] in squared, k[0], k[1]))
    mat = [[Fraction(row.get(k, 0)) for k in cols] + [Fraction(rhs)]
           for row, rhs in eqs]
    r = 0
    for col in range(len(cols)):
        piv = next((i for i in range(r, len(mat)) if mat[i][col] != 0), None)
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        f = mat[r][col]
        mat[r] = [x / f for x in mat[r]]
        for i in range(len(mat)):
            if i != r and mat[i][col] != 0:
                k = mat[i][col]
                mat[i] = [a - k * b for a, b in zip(mat[i], mat[r])]
        r += 1
    single = []
    for row in mat:
        nz = [cols[i] for i, x in enumerate(row[:-1]) if x != 0]
        if not nz:
            if row[-1] != 0:
                return [], True, contributors
            continue
        names = {nm for nm, _ in nz}
        if len(names) == 1:
            nm = names.pop()
            coef = {deg: row[i] for i, (n2, deg) in enumerate(cols) if n2 == nm}
            single.append((nm, coef.get(1, Fraction(0)), coef.get(2, Fraction(0)),
                           -row[-1]))
    return single, False, contributors


def _solve_linear_system(qs, atoms):
    """Exact rational elimination over the EQUALITY constraints.

    Interval propagation alone cannot do simultaneous equations: to narrow
    a you need b's box finite and vice versa, so two unbounded unknowns
    sit there forever (measured, before this was written). On the linear
    fragment we do not have to propagate at all — we can solve. Gaussian
    elimination over Fractions, exact, and it also detects an inconsistent
    system, which is a refutation rather than a stall."""
    eqs, contributors = [], set()
    for kind, e1, e2, chunk in atoms.values():
        if kind != "eq":
            continue
        seen = set()
        try:
            c, terms, _, _ = _linear(("sub", e1, e2), qs, [0], seen)
        except (_NotLinear, KeyError):
            continue
        contributors |= seen
        row = {}
        for _, (coef, nm) in terms.items():
            if qs[nm].get("sample"):
                row = None
                break
            row[nm] = row.get(nm, Fraction(0)) + coef
        if row:
            eqs.append((row, -c, chunk))
    if not eqs:
        return {}, None, set()
    names = sorted({n for row, _, _ in eqs for n in row})
    mat = [[Fraction(row.get(n, 0)) for n in names] + [Fraction(rhs)]
           for row, rhs, _ in eqs]
    r = 0
    for col in range(len(names)):
        piv = next((i for i in range(r, len(mat)) if mat[i][col] != 0), None)
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        f = mat[r][col]
        mat[r] = [x / f for x in mat[r]]
        for i in range(len(mat)):
            if i != r and mat[i][col] != 0:
                k = mat[i][col]
                mat[i] = [a - k * b for a, b in zip(mat[i], mat[r])]
        r += 1
    pinned = {}
    for row in mat:
        nz = [i for i, x in enumerate(row[:-1]) if x != 0]
        if not nz and row[-1] != 0:
            return {}, "inconsistent", contributors
        if len(nz) == 1:
            pinned[names[nz[0]]] = row[-1] / row[nz[0]]
    return pinned, None, contributors


def _is_ground(q):
    """A quantity CARRIES A GROUND when it bounds something: a pinned value or
    a finite end. An unknown asked for with `?` spans the whole line and
    grounds nothing: its `credit` is the absence of a ground, not a bad one.
    The curator's word, 2026-09-24: an unknown is the question, not a source."""
    return not (q["lo"] == -INF and q["hi"] == INF)


def _grounds_of(names, qs, orig):
    """The ORIGINAL grounds these quantities rest on, through every derivation
    that produced them (a derived quantity records its own `grounds`)."""
    out = set()
    for n in names:
        if qs[n].get("grounds") is not None:
            out |= set(qs[n]["grounds"])
        elif _is_ground(orig[n]):
            out.add(n)
    return out


def _prov_of(grounds, orig):
    """Earned exactly when every ground is: the provenance invariant, now
    over grounds rather than over every name a derivation touched."""
    return EARNED if all(orig[g]["prov"] == EARNED for g in grounds) else CREDIT


def _own(name, qs, orig):
    """The grounds of `name`'s own current box (its bounds enter a narrowing)."""
    return _grounds_of([name], qs, orig)


def _narrow_quadratic(kind, e1, e2, chunk, qs, log, orig=None):
    """Apply `_quadratic` to the ledger: 'empty', 'moved' or None.

    A piece that is one exact point is a DERIVED value and takes the
    provenance of the derivation, as exact elimination does; a piece that
    is still a box keeps the unknown's own. Pieces off the unknown's
    lattice are dropped (an integer x with x*x == 2 has no reading). Two
    root points are kept as `roots` on the hull, for the judge to try each."""
    got = _quadratic(kind, e1, e2, qs)
    if got is None:
        return None
    name, pieces, seen = got
    return _apply_pieces(kind, name, pieces, seen, chunk, qs, log, orig or qs)


def _apply_pieces(kind, name, pieces, seen, chunk, qs, log, orig=None):
    """Narrow `name` to `pieces` (from `_parabola_pieces`): 'empty', 'moved'
    or None. An exact root is a DERIVED value: its grounds are the grounds of
    the equation's other quantities. A piece that is still a box is also
    bounded by `name`'s own box, so those grounds join. Pieces off the
    lattice are dropped (an integer x with x*x == 2 has no reading); two root
    points are kept as `roots` on the hull, for the judge to try each."""
    orig = orig or qs
    q = qs[name]
    grounds = _grounds_of(sorted(seen - {name}), qs, orig)
    own = _own(name, qs, orig)
    kept = []
    for lo, hi in pieces:
        point = lo == hi
        g = grounds if point else grounds | own
        pq = qty(lo, hi, _prov_of(g, orig),
                 ("derived:" + ",".join(sorted(g))) if g else None,
                 discrete=q["discrete"], unit=q["unit"], sample=False)
        if pq.get("no_readings"):
            continue
        pq["root"] = kind == "eq"    # an answer to show, not a box to narrow
        pq["grounds"] = pq["derived_from"] = sorted(g)
        kept.append(pq)
    if not kept:
        log.append(f"{name}: no {typename(q['discrete'])} value in its box "
                   f"makes [{chunk}] true (from the discriminant)")
        qs[name] = dict(q, empty=True, empty_grounds=sorted(grounds | own))
        return "empty"
    if len(kept) == 1:
        new = kept[0]
    else:
        g = set().union(*(k["grounds"] for k in kept))
        new = qty(kept[0]["lo"], kept[-1]["hi"], _prov_of(g, orig),
                  ("derived:" + ",".join(sorted(g))) if g else None,
                  discrete=q["discrete"], unit=q["unit"], sample=False)
        new["grounds"] = new["derived_from"] = sorted(g)
        if kind == "eq":
            new["roots"] = kept
    if (new["lo"], new["hi"]) == (q["lo"], q["hi"]) and \
            len(new.get("roots") or []) == len(q.get("roots") or []):
        return None
    qs[name] = new
    shown = (" or ".join(f"{fmt(k['lo'])}" if k["lo"] == k["hi"]
                         else f"[{fmt(k['lo'])}, {fmt(k['hi'])}]" for k in kept))
    log.append(f"{name} -> {shown} by [{chunk}] (from the discriminant)")
    return "moved"


def _committed_atoms(core):
    """The comparisons the claim COMMITS to: those joined by `&` at the top
    level, through parentheses that only wrap. Under | ~ -> ^ <-> a
    comparison is one possibility, not a constraint.

    MEASURED 2026-09-24: every equality was taken as a constraint wherever
    it stood, so with x = ? `x == 2 | x == 3`, `~(x == 2)` and
    `x == 2 -> x == 3` came back REFUTED, and 71 of 336 claims built from
    atoms with every connective were refuted though an integer made them
    true (126 after the same day's quadratic path, which inherited it).
    The docstring above always said "conjunctions only"; the code did not."""
    out = set()

    def walk(t):
        t = t.strip()
        while t.startswith("(") and _closes_last(t, 0):
            t = t[1:-1].strip()
        parts, depth, cur = [], 0, []
        for ch in t:
            depth += (ch == "(") - (ch == ")")
            if ch == "&" and depth == 0:
                parts.append("".join(cur))
                cur = []
            else:
                cur.append(ch)
        parts.append("".join(cur))
        if len(parts) > 1:
            for part in parts:
                walk(part)
        elif re.fullmatch(r"nc\d+", t):
            out.add(t)

    walk(core)
    return out


def _committed_disjunctions(core):
    """The top-level conjuncts that are a disjunction of comparisons alone:
    `nc1 | nc2 | nc3`, through parentheses that only wrap. Each is a set of
    alternatives the claim commits to: one of them holds."""
    groups = []

    def split(t, sep):
        parts, depth, cur = [], 0, []
        for ch in t:
            depth += (ch == "(") - (ch == ")")
            if ch == sep and depth == 0:
                parts.append("".join(cur))
                cur = []
            else:
                cur.append(ch)
        parts.append("".join(cur))
        return parts

    def unwrap(t):
        t = t.strip()
        while t.startswith("(") and _closes_last(t, 0):
            t = t[1:-1].strip()
        return t

    def walk(t):
        t = unwrap(t)
        conj = split(t, "&")
        if len(conj) > 1:
            for part in conj:
                walk(part)
            return
        alts = [unwrap(a) for a in split(t, "|")]
        if len(alts) > 1 and all(re.fullmatch(r"nc\d+", a) for a in alts):
            groups.append(alts)

    walk(core)
    return groups


def _disjunction_pieces(group, atoms, qs):
    """ONE OF SEVERAL EQUALITIES OF ONE UNKNOWN (the curator's word,
    2026-09-24: read "x == 2 | x == 3" as the set of its roots). Each
    alternative must be an equality that pins the same non-sample unknown to
    points — a line to one, a parabola to its roots — and the unknown lies in
    the union. Returns (name, pieces, seen), or None when any alternative is
    something else: then the disjunction narrows nothing, as before."""
    name, pieces, seen = None, [], set()
    for atom in group:
        kind, e1, e2, _chunk = atoms[atom]
        if kind != "eq":
            return None
        try:
            c, terms, _, _ = _poly(("sub", e1, e2), qs, [0], seen)
        except (_NotLinear, KeyError, _NoReadings):
            return None
        live = [(k, t) for k, t in terms.items() if t[0] != 0 or t[1] != 0]
        if len(live) != 1:
            return None
        key, (p, q, nm) = live[0]
        if key != nm or (name is not None and nm != name):
            return None
        name = nm
        got = _parabola_pieces("eq", p, q, c, qs[nm])
        if got is None:
            return None
        pieces.extend(got)
    pieces = sorted(set(pieces))
    return name, pieces, seen


def narrow(quantities, formula, rounds=MAX_ROUNDS, orig=None):
    """Push every comparison of the formula back onto its quantities until
    nothing moves. Returns (quantities, log) — the log names each step, so
    a narrowed value can always say who narrowed it."""
    qs = {n: dict(q) for n, q in quantities.items()}
    orig = dict(orig or quantities)    # the sheet as given: where grounds live
    core, atoms = extract_comparisons(formula, qs)
    for k, v in qs.items():            # a literal interval in the claim is a
        orig.setdefault(k, v)          # declared quantity too (`_lit`, credit)
    committed = _committed_atoms(core)
    alternatives = _committed_disjunctions(core)
    all_atoms = atoms
    atoms = {k: v for k, v in atoms.items() if k in committed}
    log = []
    pinned, bad, contributors = _solve_linear_system(qs, atoms)
    if bad == "inconsistent":
        first = sorted(qs)[0]
        log.append("the equalities are inconsistent as a system")
        qs[first] = dict(qs[first], empty=True,
                         empty_grounds=sorted(_grounds_of(contributors, qs, orig)))
        return qs, log
    for name, value in sorted(pinned.items()):
        q = qs[name]
        grounds = _grounds_of(sorted(contributors - {name}), qs, orig)
        if not (q["lo"] <= value <= q["hi"]):
            log.append(f"{name}: forced to {fmt(value)}, outside its box")
            qs[name] = dict(q, empty=True, empty_grounds=sorted(
                grounds | _own(name, qs, orig)))
            return qs, log
        # a DERIVED value takes its provenance from the derivation, not
        # from whatever the unknown was declared to be. An unknown is
        # `credit` because its bounds were unwitnessed; once the equations
        # force it out of earned quantities, the value IS earned — and if
        # any contributor rides credit, so does the answer.
        # ... and its grounds are the grounds of the equations' other
        # quantities; another UNKNOWN is the question, not a source, so a
        # value derived from constants and earned rows is earned (the
        # curator's word, 2026-09-24: x + y = 10, x - y = 2 came out credit)
        derived_prov = _prov_of(grounds, orig)
        pinned_q = qty(value, value, derived_prov,
                       "derived:" + ",".join(sorted(grounds)) if grounds else None,
                       discrete=q["discrete"], unit=q["unit"], sample=False)
        pinned_q["grounds"] = pinned_q["derived_from"] = sorted(grounds)
        # KEEP THE TWO EMPTINESSES APART (2026-08-12). A quantity DECLARED
        # with no reading is E: the sheet cannot be judged at all. A value
        # DERIVED onto a point the lattice does not contain is something
        # else entirely — the judging succeeded and found no solution, so
        # the claim is REFUTED. Same empty set, opposite meanings: one is a
        # broken description, the other is an answer.
        if pinned_q.get("no_readings"):
            log.append(f"{name}: {fmt(value)} is off the "
                       f"{typename(q['discrete'])} lattice — no solution")
            qs[name] = dict(q, empty=True, empty_grounds=sorted(grounds))
            return qs, log
        qs[name] = pinned_q
        log.append(f"{name} = {fmt(value)} by exact elimination"
                   f" ({derived_prov})")
    single, bad, contributors = _solve_monomial_system(qs, atoms)
    if bad:
        first = sorted(qs)[0]
        log.append("the equalities are inconsistent as a system "
                   "(each power of a name its own column)")
        qs[first] = dict(qs[first], empty=True,
                         empty_grounds=sorted(_grounds_of(contributors, qs, orig)))
        return qs, log
    for name, p, q2, c in single:
        if qs[name].get("sample") or qs[name]["lo"] == qs[name]["hi"]:
            continue
        pieces = _parabola_pieces("eq", p, q2, c, qs[name])
        if pieces is None:
            continue
        if _apply_pieces("eq", name, pieces, contributors, "the system",
                         qs, log, orig) == "empty":
            return qs, log
    for _ in range(rounds):
        moved = False
        for atom, (kind, e1, e2, chunk) in atoms.items():
            seen = set()   # every name READ, pinned ones too: a pinned t is a
            try:           # constant to the arithmetic but still a ground
                c, terms, _, _ = _linear(("sub", e1, e2), qs, [0], seen)
            except (_NotLinear, KeyError):
                step = _narrow_quadratic(kind, e1, e2, chunk, qs, log, orig)
                if step == "empty":
                    return qs, log
                moved = moved or step == "moved"
                continue                     # outside the linear fragment
            names = {nm for _, (_, nm) in terms.items()}
            for name in sorted(names):
                q = qs[name]
                if q.get("sample"):
                    continue                 # occurrences, not one thing
                got = _hull(kind, c, terms, name, qs)
                if got is None:
                    continue
                glo, ghi, slo, shi = got
                # a STRICT bound on a lattice is one step tighter: age > 10
                # over the integers means age >= 11, and saying [10, 14] for
                # "older than 10, younger than 14" would be an answer nobody
                # asked for (measured: it was the first thing this got wrong)
                step = _step(q["discrete"])
                if step is not None:
                    if shi and ghi != INF and (ghi / step).denominator == 1:
                        ghi = ghi - step
                    if slo and glo != -INF and (glo / step).denominator == 1:
                        glo = glo + step
                lo, hi = max(q["lo"], glo), min(q["hi"], ghi)
                if lo == q["lo"] and hi == q["hi"]:
                    continue
                # its grounds: the other quantities' and its own box's (an
                # unknown's `?` box grounds nothing; see `_is_ground`)
                # (MEASURED 2026-09-24: reading only `names`, the varying ones,
                # x <= t with t on credit gave x an EARNED bound from nothing)
                g = (_grounds_of(sorted((names | seen) - {name}), qs, orig)
                     | _own(name, qs, orig))
                if lo > hi:
                    log.append(f"{name}: emptied by [{chunk}]")
                    qs[name] = dict(q, lo=lo, hi=hi, empty=True,
                                    empty_grounds=sorted(g))
                    return qs, log
                # the type has the last word: round to the lattice
                narrowed = qty(lo, hi, _prov_of(g, orig),
                               ("derived:" + ",".join(sorted(g))) if g else None,
                               discrete=q["discrete"], unit=q["unit"],
                               sample=q.get("sample", False))
                # WHO PAID FOR THIS BOUND — recorded here, where it is
                # known, instead of being reconstructed downstream from
                # the witness text. Reconstructing it was a real bug
                # (found by conformance/solver_table.py on its first run):
                # a narrowed quantity keeps its ORIGINAL witness, so
                # `earned:doc` was read as the source quantity `doc` and
                # crashed on lookup — and would silently have attributed
                # the value to the wrong source had a document ever been
                # named like a quantity.
                narrowed["grounds"] = narrowed["derived_from"] = sorted(g)
                qs[name] = narrowed
                log.append(f"{name} -> [{fmt(narrowed['lo'])}, "
                           f"{fmt(narrowed['hi'])}] by [{chunk}]")
                moved = True
        for group in alternatives:
            got = _disjunction_pieces(group, all_atoms, qs)
            if got is None or qs[got[0]].get("sample"):
                continue
            name, pieces, seen = got
            chunk = " | ".join(all_atoms[a][3] for a in group)
            step = _apply_pieces("eq", name, pieces, seen, chunk, qs, log, orig)
            if step == "empty":
                return qs, log
            moved = moved or step == "moved"
        if not moved:
            break
    return qs, log


def _no_solution(qs, log, empty, sheet):
    """No value makes the claim true. Resting only on earned grounds (and
    constants, and types) that is a refutation; resting on a ground that is
    still on credit it is not one yet: ON CREDIT, toward F, with the cure
    named. The curator's word, 2026-09-24: `x == k & x == j` with k on
    credit came back REFUTED, which the judge itself would never say."""
    grounds = sorted({g for n in empty for g in (qs[n].get("empty_grounds") or [])})
    weak = [g for g in grounds if sheet[g]["prov"] == CREDIT]
    if weak:
        return {"disposition": "ON CREDIT", "polarity": "toward F",
                "narrowed": qs, "log": log, "empty": empty,
                "next_check": [f"document {g}" for g in weak
                               if not g.startswith("_lit")], "solved": {}}
    return {"disposition": "REFUTED", "narrowed": qs, "log": log,
            "empty": empty, "next_check": [], "solved": {}}


def solve_claim(formula, quantities, marks):
    """Narrow first, then judge on the narrowed ledger — and say, for every
    answer the narrowing produced, what it is worth and what would fix it.

    A solved value is not a number: it is a number with a warranty and a
    cure. `x = 5 ON CREDIT, document total` is a different object from
    `x = 5 EARNED`, and the difference is the only thing an auditor is
    paid to look at."""
    qs, log = narrow(quantities, formula)
    sheet = dict(quantities)
    for k, v in qs.items():            # with the claim's literal intervals
        sheet.setdefault(k, v)
    empty = [n for n, q in qs.items() if q.get("empty")]
    if empty:
        return _no_solution(qs, log, empty, sheet)
    # TWO ROOTS ARE TWO ANSWERS («корня-то два», 2026-09-24). Judge the claim
    # once per root: a root that makes it false is not an answer and goes;
    # if none is left the claim is refuted; the disposition of the rest is
    # the weakest of theirs, so EARNED means earned for every root kept.
    kept_roots = {}
    multi = [n for n, q in qs.items() if len(q.get("roots") or []) > 1]
    if len(multi) == 1:
        name = multi[0]
        worlds = []
        for rq in qs[name]["roots"]:
            qs1 = dict(qs)
            qs1[name] = rq
            # a name that DEPENDS on the root (area = s*s) follows it: narrow
            # again inside the world, or it stays a box and the claim OPEN
            qs1, _ = narrow(qs1, formula, orig=sheet)
            e1 = [n for n, q1 in qs1.items() if q1.get("empty")]
            if e1:
                worlds.append((rq, _no_solution(qs1, [], e1, sheet), qs1))
                continue
            worlds.append((rq, judge_sheet_claim(formula, qs1, marks), qs1))
        alive_w = [w3 for w3 in worlds if w3[1]["disposition"] != "REFUTED"]
        alive = [(rq, w) for rq, w, _ in alive_w]
        if not alive:
            log.append(f"{name}: no root makes the whole claim true")
            return {"disposition": "REFUTED", "narrowed": qs, "log": log,
                    "empty": [name], "next_check": [], "solved": {}}
        if len(alive) == 1:
            qs[name] = alive[0][0]
            for other, q1 in alive_w[0][2].items():
                if other != name and q1["lo"] == q1["hi"] != qs[other]["lo"]:
                    qs[other] = q1           # it followed the one root left
        else:
            # a name pinned in every world follows its root: area = 4 or 9,
            # never the box [4, 9] that would say 6 is possible
            for other in qs:
                if other == name:
                    continue
                vals = [w3[2][other] for w3 in alive_w]
                if all(v["lo"] == v["hi"] for v in vals):
                    if len({v["lo"] for v in vals}) == 1:
                        qs[other] = vals[0]
                    else:
                        kept_roots[other] = vals
                        g = set().union(*(set(v.get("grounds") or []) for v in vals))
                        qs[other] = qty(min(v["lo"] for v in vals),
                                        max(v["hi"] for v in vals),
                                        _prov_of(g, sheet),
                                        ("derived:" + ",".join(sorted(g))) if g else None,
                                        discrete=qs[other]["discrete"],
                                        unit=qs[other]["unit"], sample=False)
                        qs[other]["grounds"] = sorted(g)
            rank = {"EARNED": 3, "ON CREDIT": 2, "OPEN": 1}
            odd = [w for _, w in alive if w["disposition"] not in rank]
            r = odd[0] if odd else min(
                (w for _, w in alive), key=lambda w: rank[w["disposition"]])
            kept_roots[name] = [rq for rq, _ in alive]
    if not kept_roots:
        r = judge_sheet_claim(formula, qs, marks)
    r["narrowed"], r["log"] = qs, log
    solved, cures = {}, list(r["next_check"])
    # a literal of the claim (`_lit`, which the judge's own reading may add
    # again as `_lit2`) is not an answer: until 2026-09-24 looking it up here
    # crashed every claim with an interval literal and x = ?, E_UNREADABLE
    derived = {n for n, q in qs.items() if n in quantities
               and (quantities[n]["lo"], quantities[n]["hi"]) != (q["lo"], q["hi"])}
    # a cure must be addressed to someone who can act on it. Nobody can
    # document or measure the ANSWER: line3 is what the sheet is asking
    # for, not a source. Cures naming a derived quantity are dropped, and
    # the one thing worth saying about it — that it is still a box — is
    # said once, below.
    cures = [c for c in cures
             if c.split(" ", 1)[-1] not in derived
             and not c.split(" ", 1)[-1].startswith("_lit")]
    for name, q in sorted(qs.items()):
        if name not in quantities:
            continue                          # a literal of the claim, not asked for
        before = quantities[name]
        if (before["lo"], before["hi"]) == (q["lo"], q["hi"]):
            continue                          # this one was not narrowed
        pinned = q["lo"] == q["hi"]
        # who paid for it: the grounds the derivation recorded, transitively
        sources = sorted(q.get("grounds") or [])
        # a literal is declared, so it rides credit, but nobody can document
        # it: the cure is addressed only to rows of the sheet
        weak = [c for c in sources if c in quantities and sheet[c]["prov"] == CREDIT]
        solved[name] = {"lo": q["lo"], "hi": q["hi"], "pinned": pinned,
                        "prov": q["prov"], "from": sources, "weak": weak}
        roots = kept_roots.get(name) or ([q] if q.get("root") else [])
        if roots:
            solved[name]["roots"] = [(k["lo"], k["hi"]) for k in roots]
        for c in weak:
            if f"document {c}" not in cures:
                cures.append(f"document {c}")
        if not pinned and not roots:
            # an irrational root is an enclosure of one exact number: no
            # measurement narrows it further, so no such cure is offered
            cures.append(f"narrow {name} further (still a box)")
    seen = set()
    r["solved"] = solved
    # nobody can document a value the equations derived, nor an unknown the
    # question asks for: a cure must name a source someone can act on
    r["next_check"] = [c for c in cures
                       if not (c.startswith("document ")
                               and c.split(" ", 1)[1] in derived)
                       and not (c in seen or seen.add(c))]
    return r


# ================================================================ the bench
def _show(qs, names):
    return ", ".join(f"{n} in [{fmt(qs[n]['lo'])}, {fmt(qs[n]['hi'])}]"
                     for n in names)


def sec1_the_school_problems():
    print("-" * 72)
    print("1. THE THINGS A CHILD IS ASKED (and the judge could not do)")
    cases = [
        ("x + x == 10", "x=? int", ["x"]),
        ("apples - 7 == 5", "apples=? int", ["apples"]),
        ("3 * k == 12", "k=? int", ["k"]),
        ("sum(a,b) == 10 & a - b == 2", "a=? int, b=? int", ["a", "b"]),
    ]
    for formula, data, names in cases:
        quantities, marks = parse_quantities(data)
        r = solve_claim(formula, quantities, marks)
        print(f"   {formula:34} -> {_show(r['narrowed'], names)}"
              f"   [{r['disposition']}]")
    q, m = parse_quantities("x=? int")
    assert narrow(q, "x + x == 10")[0]["x"]["lo"] == 5
    q, m = parse_quantities("a=? int, b=? int")
    out, _ = narrow(q, "sum(a,b) == 10 & a - b == 2")
    assert (out["a"]["lo"], out["a"]["hi"]) == (6, 6)
    assert (out["b"]["lo"], out["b"]["hi"]) == (4, 4)
    print("   two unknowns and two constraints: solved by narrowing alone,")
    print("   no algebra, no symbol pushing — the boxes squeeze each other.")


def sec2_the_type_finishes_it():
    print("-" * 72)
    print("2. THE TYPE DOES THE LAST MILE")
    q, m = parse_quantities("k=? int, sweets=8 earned:cheque, kids=3 earned:cheque")
    r = solve_claim("k * kids == sweets", q, m)
    print(f"   'she shared 8 sweets equally among 3': {r['disposition']}"
          f"   {r.get('empty') and 'empty box for ' + str(r['empty']) or ''}")
    assert r["disposition"] == "REFUTED" and r["empty"] == ["k"]
    q2, m2 = parse_quantities("k=? frac3, sweets=8 earned:cheque, "
                              "kids=3 earned:cheque")
    r2 = solve_claim("k * kids == sweets", q2, m2)
    print(f"   the same with thirds allowed: "
          f"k in [{fmt(r2['narrowed']['k']['lo'])}, "
          f"{fmt(r2['narrowed']['k']['hi'])}]   [{r2['disposition']}]")
    assert r2["narrowed"]["k"]["lo"] == Fraction(8, 3)
    print("   an EMPTY box is a refutation, not a failure to converge — and")
    print("   the cure is the one the corpus already names: contest the type.")


def sec3_soundness_measured():
    print("-" * 72)
    print("3. SOUNDNESS, MEASURED RATHER THAN ASSERTED")
    # exhaustive grid: every true solution must survive the narrowing
    grid = range(-4, 5)
    checks = lost = narrowed_cells = 0
    for c in grid:
        for kind, formula in (("eq", f"a + b == {c}"),
                              ("le", f"a + b <= {c}"),
                              ("eq", f"a - b == {c}"),
                              ("eq", f"a + a == {c}")):
            q = {"a": qty(-4, 4, EARNED, "grid", discrete="int"),
                 "b": qty(-4, 4, EARNED, "grid", discrete="int")}
            out, _ = narrow(q, formula)
            for av in grid:
                for bv in grid:
                    ok = {"eq": (lambda: (av + bv == c) if "b" in formula
                                 else (av + av == c)),
                          "le": (lambda: av + bv <= c)}[kind]()
                    if "a - b" in formula:
                        ok = (av - bv == c)
                    if not ok:
                        continue
                    checks += 1
                    inside = (out["a"].get("empty") is None
                              and out["a"]["lo"] <= av <= out["a"]["hi"])
                    if "b" in formula.replace("a + a", ""):
                        inside = inside and (
                            out["b"]["lo"] <= bv <= out["b"]["hi"])
                    if not inside:
                        lost += 1
            narrowed_cells += 1
    print(f"   {narrowed_cells} constraint systems, {checks} true solutions")
    print(f"   solutions dropped by narrowing: {lost}")
    assert lost == 0
    print("   none. The failure mode is the safe one: a box may stay wider")
    print("   than the truth (we lose completeness, and the claim stays")
    print("   OPEN) but a real solution is never thrown away, so a verdict")
    print("   forced after narrowing is as good as one forced before.")


def sec4_the_receipt():
    print("-" * 72)
    print("4. THE ANSWER COMES WITH ITS RECEIPT")
    # the audit case: the total is documented, one line is not
    q, m = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=4500 earned:contract")
    r = solve_claim("sum(line1,line2,line3) == total", q, m)
    l3 = r["narrowed"]["line3"]
    print(f"   the missing line is forced: line3 = {fmt(l3['lo'])}"
          f"   provenance: {l3['prov']}")
    assert l3["lo"] == l3["hi"] == 1500 and l3["prov"] == EARNED
    print(f"   log: {r['log']}")
    # and now with a total nobody documented
    q2, m2 = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=4500 credit")
    r2 = solve_claim("sum(line1,line2,line3) == total", q2, m2)
    l3b = r2["narrowed"]["line3"]
    print(f"   same arithmetic, undocumented total: line3 = "
          f"{fmt(l3b['lo'])}   provenance: {l3b['prov']}")
    assert l3b["lo"] == 1500 and l3b["prov"] == CREDIT
    print("   the value is the same and the warranty is not. A solver that")
    print("   returned only the number would have hidden exactly the thing")
    print("   an auditor is paid to see.")


def sec5_word_problems():
    print("-" * 72)
    print("5. A SHEET OF WORD PROBLEMS, INCLUDING ONES THAT MUST NOT SOLVE")
    sheet = [
        ("Masha had apples, gave 7 away, 5 left",
         "had - 7 == 5", "had=? int"),
        ("three equal boxes hold 12",
         "3 * box == 12", "box=? int"),
        ("two numbers, sum 10, difference 2",
         "sum(a,b) == 10 & a - b == 2", "a=? int, b=? int"),
        ("the change from 1000 for a 743 purchase",
         "paid - price == change",
         "paid=1000 earned:till, price=743 earned:till, change=? int"),
        ("8 sweets shared equally among 3 children",
         "k * kids == sweets",
         "k=? int, sweets=8 earned:cheque, kids=3 earned:cheque"),
        ("a number whose double is odd",
         "2 * n == 7", "n=? int"),
        ("she is older than 10 and younger than 14",
         "age > 10 & age < 14", "age=? int"),
    ]
    for title, formula, data in sheet:
        q, m = parse_quantities(data)
        r = solve_claim(formula, q, m)
        answers = ", ".join(
            f"{n} = {fmt(v['lo'])}" if v["pinned"]
            else f"{n} in [{fmt(v['lo'])}, {fmt(v['hi'])}]"
            for n, v in sorted(r["solved"].items())) or "—"
        print(f"   {title:44} {answers:26} [{r['disposition']}]")
    # the ones that must solve
    q, m = parse_quantities("had=? int")
    assert solve_claim("had - 7 == 5", q, m)["solved"]["had"]["lo"] == 12
    # the one that must NOT: an odd double has no integer solution
    q, m = parse_quantities("n=? int")
    assert solve_claim("2 * n == 7", q, m)["disposition"] == "REFUTED"
    # and the one that must stay a box, honestly
    q, m = parse_quantities("age=? int")
    r = solve_claim("age > 10 & age < 14", q, m)
    assert (r["solved"]["age"]["lo"], r["solved"]["age"]["hi"]) == (11, 13)
    assert not r["solved"]["age"]["pinned"]
    print("   the last three are the point: a double that is odd gets an")
    print("   EMPTY box (refuted, not 'no idea'), and 'older than 10,")
    print("   younger than 14' answers [11, 13] and says so — a box is an")
    print("   answer when a box is the truth.")


def sec6_the_audit_sheet():
    print("-" * 72)
    print("6. THE SAME MACHINE ON AN AUDIT SHEET")
    rows = [
        ("total documented, one line missing",
         "sum(line1,line2,line3) == total",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=4500 earned:contract"),
        ("same, but the total is nobody's",
         "sum(line1,line2,line3) == total",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=4500 credit"),
        ("the claimed line contradicts the total",
         "sum(line1,line2,line3) == total & line3 == 1600",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=4500 earned:contract"),
        ("bounds only: the total is a range",
         "sum(line1,line2,line3) == total",
         "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
         "line3=? int, total=[4200,4400] earned:contract"),
    ]
    for title, formula, data in rows:
        q, m = parse_quantities(data)
        r = solve_claim(formula, q, m)
        got = r["solved"].get("line3")
        if got is None:
            answer = "— (refuted)"
        elif got["pinned"]:
            answer = f"line3 = {fmt(got['lo'])} [{got['prov']}]"
        else:
            answer = f"line3 in [{fmt(got['lo'])}, {fmt(got['hi'])}]"
        print(f"   {title:38} {answer:34} cure {r['next_check']}")
    q, m = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=4500 credit")
    r = solve_claim("sum(line1,line2,line3) == total", q, m)
    assert r["solved"]["line3"]["prov"] == CREDIT
    assert r["next_check"] == ["document total"]      # not "document line3"
    q2, m2 = parse_quantities(
        "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
        "line3=? int, total=[4200,4400] earned:contract")
    r2 = solve_claim("sum(line1,line2,line3) == total", q2, m2)
    assert (r2["solved"]["line3"]["lo"], r2["solved"]["line3"]["hi"]) == (1200, 1400)
    print("   the cure is not 'measure line3' — nobody can measure a line")
    print("   that does not exist yet. It is 'document total', naming the")
    print("   quantity whose credit the answer rides on. That is the whole")
    print("   difference between a solver and an auditor.")


if __name__ == "__main__":
    print("=" * 72)
    print("ZNUMSOLVE — narrowing backwards, with receipts")
    print("=" * 72)
    sec1_the_school_problems()
    sec2_the_type_finishes_it()
    sec3_soundness_measured()
    sec4_the_receipt()
    sec5_word_problems()
    sec6_the_audit_sheet()
    print("=" * 72)
    print("ZNUMSOLVE GREEN — the floor now runs backwards as well as")
    print("forwards: constraints narrow their quantities to a fixed point,")
    print("the type finishes the job (an empty box is a refutation), and no")
    print("true solution was dropped on the measured grid. The answer")
    print("carries its provenance, so 'line3 = 1500' and 'line3 = 1500 on")
    print("credit' never look alike.")
