# -*- coding: utf-8 -*-
"""
Expedition E37: znum — the numeric floor of ZTL (probe).

Design: ZNUM-DESIGN-draft.md (stage 1, curator-accepted forks F1-F3), with F1
superseded by the curator's word in two steps:
  F1  a NAME is ONE NUMBER across the whole claim: m - m = 0 and m == m
      (2026-08-11 within a term; 2026-09-24 across a comparison). Occurrences
      read independently only for a `sample` — separate acts of measurement;
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
import re
import os
import sys
from fractions import Fraction

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztljudge import judge                              # noqa: E402

INF = math.inf
EARNED, CREDIT = "earned", "credit"

# The four corners of ONE construction. A formula's meaning here is its SET
# OF READINGS, and every status is a fact about that set:
#     T   readings exist and all of them make it true
#     F   readings exist and all of them make it false
#     Z   readings exist and they disagree
#     E   THERE ARE NO READINGS AT ALL — the set is empty
# E was raised as a Python exception until 2026-08-12, which put it OUTSIDE
# the logic: a breakage of the implementation. It is not a breakage — and it
# is not a value either (settled 2026-08-19; the curator, 2026-09-24:
# «внутренняя метка, стоп-машина»): E enters no connective, it is the judge's
# STOP, nothing to judge here. It is the fourth corner, and the corpus had already
# stumbled over it twice — as the two ValueErrors below, and as the vacuity
# trap measured in zprove.py, where "all readings are true" comes for free
# when there are no readings to check. Emptiness must be SEPARATED, not
# quantified over.
#
# Note what this answers, since the question came from the ethics thread:
# the norm behind E is not imposed from outside (Augustine had to hang it
# on a Creator). Judging IS quantification over readings; E is what happens
# when there is nothing to quantify over. The judge halts because it has
# nothing to inspect, not because it broke somebody's design.
E = "E"


def num(x):
    """Every finite value is an EXACT rational; ±INF stays the float
    sentinel. A float is read as the decimal it prints (0.7 means 7/10,
    not its binary neighbour) — the floor judges the number the claim
    says, not the one the machine stores. MEASURED 2026-08-11: on floats
    the lattice tightening turned 0.7 into 0.7000000000000001 and forced
    two FALSE refutations ('p == r' with both sides 0.7, and
    '29.7 + 0.3 == 30'); exact rationals are what makes eq trustworthy."""
    if isinstance(x, Fraction):
        return x
    if isinstance(x, float):
        return x if math.isinf(x) else Fraction(str(x))
    return Fraction(x)                       # int, or a string like "8/3"


def fmt(x):
    """Display form: ∞, an integer, or a/b — never a float artefact."""
    if isinstance(x, float):
        return "∞" if x > 0 else "-∞"
    return (str(x.numerator) if x.denominator == 1
            else f"{x.numerator}/{x.denominator}")


# ------------------------------------------------------------- quantities
def qty(lo, hi, provenance=CREDIT, witness=None, discrete=None, unit=None,
        sample=False):
    """A quantity: interval [lo, hi] + provenance of its bounds + TYPE.

    The type is a FORMALIZATION commitment, not knowledge: it filters the
    READING SET (readings = lattice(discrete) ∩ [lo, hi]) and needs no
    witness; expire never touches it. `discrete`: None (continuous
    rationals), "int", ("decimal", k) — multiples of 10^-k — or
    ("frac", m) — multiples of 1/m, the lattice a decimal one cannot
    express (thirds, eighths: "she shared it out in thirds" is a sayable
    claim, not a refuted one). `unit`: a name ("candies", "RUB") or None
    (dimensionless). The declared bounds are tightened to the lattice at
    construction; if nothing survives, the quantity carries `no_readings`
    and every comparison touching it comes back E — never a vacuous
    verdict, and never an exception either.

    `sample`: what a repeated NAME means. Default False — the quantity is
    ONE THING IN THE WORLD, so every occurrence co-refers and m - m is 0.
    True — each occurrence is a separate ACT of measurement (the same rod
    measured twice), so the occurrences are read independently and
    m - m is not 0. This is a formalization commitment like the type, not
    knowledge: it says what the symbol denotes, needs no witness, and is
    contestable as an encoding. Until 2026-08-11 the floor read EVERY
    quantity as a sample, decorrelated — inherited by analogy from the
    propositional lift, where decorrelation is FORCED because a connective
    sees values and not names. Down here the names are right there, so it
    was a choice, and the default was the wrong way round."""
    lo, hi = num(lo), num(hi)
    assert provenance in (EARNED, CREDIT)
    if lo > hi:
        # An INVERTED interval is the purest empty reading set there is,
        # and until 2026-08-12 it was an `assert` — the same mistake as the
        # lattice case, caught the same day by the curator's Vasya/Petya
        # story: emptiness kept leaking out of the logic through a
        # different hole. There is one emptiness and it has one status.
        return {"lo": lo, "hi": hi, "prov": provenance, "witness": witness,
                "discrete": discrete, "unit": _unit_str(_unit_map(unit)),
                "sample": sample,
                "no_readings": f"empty interval [{fmt(lo)}, {fmt(hi)}]"}
    step = _step(discrete)
    if step is not None:
        tlo = lo if lo == -INF else Fraction(math.ceil(lo / step)) * step
        thi = hi if hi == INF else Fraction(math.floor(hi / step)) * step
        if tlo > thi:
            # no lattice point inside the bounds: the reading set is EMPTY.
            # Not an exception any more — a status the floor computes and
            # carries, with the offending declaration kept for the report.
            return {"lo": lo, "hi": hi, "prov": provenance,
                    "witness": witness, "discrete": discrete,
                    "unit": _unit_str(_unit_map(unit)), "sample": sample,
                    "no_readings":
                        f"no {typename(discrete)} reading in "
                        f"[{fmt(lo)}, {fmt(hi)}]"}
        lo, hi = tlo, thi
    return {"lo": lo, "hi": hi, "prov": provenance, "witness": witness,
            "discrete": discrete, "unit": _unit_str(_unit_map(unit)),
            "sample": sample, "no_readings": None}


def _step(discrete):
    """Lattice step of a discreteness type; None = continuous."""
    if discrete == "int":
        return Fraction(1)
    if isinstance(discrete, tuple) and discrete[0] == "decimal":
        # ПОТОЛОК НА РАЗРЯДНОСТЬ. `10 ** k` с большим k — целое на миллионы цифр:
        # одно поле запроса вешало публичный сервер (промерено 2026-08-25:
        # decimal5000000 = 1,33 с только на возведение, дальше арифметика хуже).
        # Больше 30 знаков после запятой не бывает у величин, которые мы судим.
        if not (0 <= discrete[1] <= 30):
            raise ValueError(f"недопустимая разрядность decimal{discrete[1]}: "
                             f"допустимо 0..30")
        return Fraction(1, 10 ** discrete[1])
    if isinstance(discrete, tuple) and discrete[0] == "frac":
        assert discrete[1] >= 1
        return Fraction(1, discrete[1])
    return None


def typename(discrete):
    """The type as the sheet writes it — the name a cure must quote."""
    if discrete is None:
        return "continuous"
    if discrete == "int":
        return "int"
    return f"{discrete[0]}{discrete[1]}"


def _on_lattice(value, step):
    """Exactly on the lattice — no tolerance window: with rationals the
    question has an answer, and a tolerance would silently earn equality
    the claim never bought (§13)."""
    if isinstance(value, float):             # ±INF lies on no lattice
        return False
    return (value / step).denominator == 1


def bare(x):
    """F2: a bare number = [x, x] on credit — usable, never load-bearing
    above ON CREDIT."""
    return qty(x, x, CREDIT)


# ------------------------------------------- the lift: interval arithmetic
def _iv_add(a, b): return (a[0] + b[0], a[1] + b[1])
def _iv_sub(a, b): return (a[0] - b[1], a[1] - b[0])


def _iv_mul(a, b):
    # 0 TIMES AN INFINITE END IS 0: the ends are limits, never attained, and 0
    # times any real is 0 (IEEE 1788 takes the same convention for bounds).
    # Python's 0 * inf is nan, and min/max over a list holding nan depend on
    # its order: MEASURED 2026-09-24, [-inf,0]·[0,1] came out (nan, nan), so
    # a*b <= 0 was Z where it is T, and [0,0]·[-inf,inf] was (nan, nan). No
    # verdict was ever false (nan made every comparison Z), but forced ones
    # were lost.
    ps = [Fraction(0) if (x == 0 or y == 0) else x * y for x in a for y in b]
    return (min(ps), max(ps))


def _iv_div(a, b):
    if b[0] <= 0 <= b[1]:
        return None                       # divisor may be 0: undefined (§25 echo)
    # 1/±inf is an EXACT zero, not the float 0.0. A finite float passed for
    # an infinity downstream — `fmt` printed it as -∞ and `_on_lattice` put
    # it off every lattice — and the live service refuted `k == 0/d` for an
    # int k that can be 0: a false verdict, found 2026-09-24 in the audit.
    inv = (Fraction(0) if b[1] in (INF, -INF) else 1 / b[1],
           Fraction(0) if b[0] in (INF, -INF) else 1 / b[0])
    return _iv_mul(a, inv)


# SQRT_DIGITS — ОБЪЯВЛЕННАЯ точность зажима, а не молчаливая. Потолок стоит
# по той же причине, что и у decimal(k) в zfl: `decimal5000000` однажды дошёл
# до 10**k и повесил службу. Точность, которую никто не объявил и никто не
# ограничил, — это решение, спрятанное внутри прибора.
SQRT_DIGITS = 12
SQRT_DIGITS_CAP = 30


def _rat_sqrt(x, k=None):
    """Рациональный ЗАЖИМ корня: (lo, hi), lo <= sqrt(x) <= hi.

    Не приближение, а доказанная вилка. Корень из рационального почти всегда
    иррационален и точкой на этой решётке не представим — но представим
    зажатым, и зажим честнее округления: он ГОВОРИТ, чего не знает.

    Когда корень точен (4, 9/4), возвращается точка: вилка шириной ноль —
    это не особый случай, а тот же зажим, сошедшийся.
    """
    k = SQRT_DIGITS if k is None else min(int(k), SQRT_DIGITS_CAP)
    if x < 0:
        return None
    if x == 0:
        return (Fraction(0), Fraction(0))
    p, q = x.numerator, x.denominator
    rp, rq = math.isqrt(p), math.isqrt(q)
    if rp * rp == p and rq * rq == q:          # корень точен — вилка сходится
        e = Fraction(rp, rq)
        return (e, e)
    s = 10 ** k
    n2 = p * s * s
    lo = Fraction(math.isqrt(n2 // q), s)      # isqrt(floor(x s^2)) <= s*sqrt(x)
    hi = Fraction(math.isqrt((n2 + q - 1) // q) + 1, s)   # > s*sqrt(x)
    return (lo, hi)


def _iv_sqrt(a, k=None):
    """Корень над интервалом. Три исхода, и они разные:

        весь интервал < 0   -> НЕТ ЧТЕНИЙ вовсе (четвёртый угол, E)
        интервал задевает 0 -> None: часть чтений не определена, это МЕТКА,
                               а не вердикт — ровно как деление на возможный ноль
        интервал >= 0       -> зажим [sqrt(lo), sqrt(hi)]
    """
    if a[1] < 0:
        raise _NoReadings("sqrt of a strictly negative quantity")
    if a[0] < 0:
        return None
    lo, hi = _rat_sqrt(a[0], k), _rat_sqrt(a[1], k)
    return (lo[0], hi[1])


def _unit_sqrt(u):
    """Единица под корнем: степени делятся пополам. Нечётная степень —
    ОТКАЗ, а не приближение: sqrt(m3) в целых степенях не выражается, и
    сказать об этом честнее, чем выдать m1.5."""
    m = _unit_map(u)
    if not m:
        return None
    if any(e % 2 for e in m.values()):
        raise _NoReadings(f"cannot take the root of '{u}': odd exponent")
    return _unit_str({k: e // 2 for k, e in m.items() if e})


def _unit_map(u):
    """A unit read as EXPONENTS: 'm2' -> {m: 2}, 'RUB/m2' -> {RUB: 1, m: -2},
    None -> {} (dimensionless). '·' (or '*') makes the next factor positive,
    '/' makes it negative — so 'km/h' is km·h^-1. No conversion factors live
    here and none ever will silently: km and m are DIFFERENT units, and
    turning one into the other is a claim about the world, not arithmetic."""
    if not u:
        return {}
    out, sign = {}, 1
    for part in re.split(r"([·*/])", u):
        if part in ("·", "*"):
            sign = 1
            continue
        if part == "/":
            sign = -1
            continue
        part = part.strip()
        if not part:
            continue
        # LETTERS, not Latin letters. Nothing in this floor cares which
        # alphabet a unit is written in — the whole content of a unit is
        # that DIFFERENT symbols never meet, and `конфеты` are as
        # incomparable with roubles as metres are. Found 2026-08-13, when a
        # word problem about sweets crashed on its own unit.
        m = re.fullmatch(r"((?:[^\W\d]|_)+)(-?\d+)?", part)
        if not m:
            raise ValueError(f"E_UNIT: cannot read the unit {u!r}")
        out[m.group(1)] = out.get(m.group(1), 0) + sign * int(m.group(2) or 1)
        sign = 1
    return {k: v for k, v in out.items() if v}


def _unit_str(m):
    """The canonical spelling: 'm2', 'km/h', 'RUB/m2' — dimensionless is
    None, so a ratio of like units (m/m) comes back a bare number."""
    if not m:
        return None
    top = "·".join(k if m[k] == 1 else f"{k}{m[k]}"
                   for k in sorted(k for k in m if m[k] > 0)) or "1"
    bot = "·".join(k if m[k] == -1 else f"{k}{-m[k]}"
                   for k in sorted(k for k in m if m[k] < 0))
    return top if not bot else f"{top}/{bot}"


def _unit_combine(u1, u2, power):
    """Multiply (power=+1) or divide (power=-1) two units."""
    m = dict(_unit_map(u1))
    for k, e in _unit_map(u2).items():
        m[k] = m.get(k, 0) + power * e
    return _unit_str({k: e for k, e in m.items() if e})


def _unify_units(u1, u2, ctx):
    """Dimensionless (None) unifies with anything; named units must match
    for additive/comparative contexts — a mismatch is a FORMALIZATION
    error (E_UNIT), caught before any verdict."""
    if u1 is None:
        return u2
    if u2 is None or u1 == u2:
        return u1
    raise _NoReadings(f"cannot {ctx} '{u1}' with '{u2}'")


class _NoReadings(Exception):
    """Raised inside the evaluator, caught at the verdict boundary, turned
    into the value E. Units that do not unify leave the comparison with no
    admissible reading at all — the same emptiness as a type with no
    lattice point, arrived at from the other side."""


# ------------------------------------ the linear fragment, read coherently
class _NotLinear(Exception):
    pass


def _linear(expr, quantities, counter, seen=None):
    """Read the expression as  c + Σ k·x  over KEYS, or give up.

    A correlated quantity contributes its own name as the key, so repeated
    occurrences ADD UP and cancel — this is what makes m - m zero and
    x + x equal to 2x. A `sample` quantity contributes a fresh key per
    occurrence, which reproduces the old decorrelated reading exactly.
    On the linear fragment the resulting interval is EXACT (each key is
    counted once), which is the whole gain; outside it we raise and the
    caller falls back to plain interval arithmetic, wide but sound."""
    if isinstance(expr, (int, float, Fraction)):
        return num(expr), {}, None, Fraction(1) if num(expr).denominator == 1 else None
    if isinstance(expr, str):
        q = quantities[expr]
        if q.get("no_readings"):
            raise _NoReadings(f"{expr}: {q['no_readings']}")
        if seen is not None:
            seen.add(expr)
        counter[0] += 1
        if q["lo"] == q["hi"] and not isinstance(q["lo"], float):
            # a pinned quantity IS a constant, and saying so keeps whole
            # expressions inside the linear fragment (k * kids with kids
            # known). Its provenance still travels, via `seen`.
            return q["lo"], {}, q.get("unit"), _step(q.get("discrete"))
        key = (expr, counter[0]) if q.get("sample") else expr
        return Fraction(0), {key: (Fraction(1), expr)}, q.get("unit"), \
            _step(q.get("discrete"))
    op, *args = expr
    if op == "sqrt":
        # THE ROOT OF A KNOWN NUMBER is a constant when it is exact: sqrt(disc)
        # with disc pinned at 1 is 1 (MEASURED 2026-09-24: a model's table
        # computing the discriminant stopped at OPEN, sqrtD unread). A root
        # the rational floor cannot hold exactly is not a constant of it.
        c1, t1, u1, _ = _linear(args[0], quantities, counter, seen)
        r = _rat_sqrt(c1) if not t1 and c1 >= 0 else None
        if r is None or r[0] != r[1]:
            raise _NotLinear()
        return r[0], {}, _unit_sqrt(u1), None
    if op == "sum":
        c, terms, unit, step = Fraction(0), {}, None, Fraction(1)
        for a in args[0]:
            c2, t2, u2, s2 = _linear(a, quantities, counter, seen)
            unit = _unify_units(unit, u2, "add")
            step = s2 if step is None or s2 is None else (
                s2 if s2 == step else None)
            c += c2
            for k, (coef, nm) in t2.items():
                old = terms.get(k, (Fraction(0), nm))
                terms[k] = (old[0] + coef, nm)
        return c, terms, unit, step
    if op in ("add", "sub"):
        c1, t1, u1, s1 = _linear(args[0], quantities, counter, seen)
        c2, t2, u2, s2 = _linear(args[1], quantities, counter, seen)
        unit = _unify_units(u1, u2, "add")
        sign = Fraction(1) if op == "add" else Fraction(-1)
        terms = dict(t1)
        for k, (coef, nm) in t2.items():
            old = terms.get(k, (Fraction(0), nm))
            terms[k] = (old[0] + sign * coef, nm)
        step = s1 if s1 == s2 else None
        return c1 + sign * c2, terms, unit, step
    if op in ("mul", "div"):
        c1, t1, u1, s1 = _linear(args[0], quantities, counter, seen)
        c2, t2, u2, s2 = _linear(args[1], quantities, counter, seen)
        if op == "mul" and not t2:                 # variable times constant
            k = c2
            return (c1 * k, {kk: (co * k, nm) for kk, (co, nm) in t1.items()},
                    _unit_combine(u1, u2, +1),
                    Fraction(1) if (s1 == Fraction(1) and k.denominator == 1
                                    and s2 == Fraction(1)) else None)
        if op == "mul" and not t1:
            k = c1
            return (k * c2, {kk: (k * co, nm) for kk, (co, nm) in t2.items()},
                    _unit_combine(u1, u2, +1),
                    Fraction(1) if (s2 == Fraction(1) and k.denominator == 1
                                    and s1 == Fraction(1)) else None)
        if op == "div" and not t2 and c2 != 0:     # divided by a constant
            return (c1 / c2,
                    {kk: (co / c2, nm) for kk, (co, nm) in t1.items()},
                    _unit_combine(u1, u2, -1), None)
        raise _NotLinear()
    raise _NotLinear()


def _ev_linear(expr, quantities):
    """(interval, pedigree, used, step, unit) via the coherent linear read,
    or None when the expression is not linear."""
    seen = set()
    try:
        c, terms, unit, step = _linear(expr, quantities, [0], seen)
    except (_NotLinear, KeyError):
        return None
    lo = hi = c
    used = set(seen)
    ped = {n for n in seen if quantities[n]["prov"] == CREDIT}
    for _, (coef, name) in terms.items():
        q = quantities[name]
        a, b = q["lo"], q["hi"]
        if coef == 0 and not (a == b and isinstance(a, float)):
            # A name that cancelled (m - m) contributes exactly 0 for every
            # FINITE reading, however wide the bounds; 0 * inf would be nan
            # (2026-09-24). A quantity pinned AT an infinity has no finite
            # reading, inf - inf is undefined, and it keeps the old path.
            continue
        ends = sorted((coef * a, coef * b), key=lambda x: (x == -INF and -1)
                      or (x == INF and 1) or 0) if isinstance(a, float) \
            or isinstance(b, float) else sorted((coef * a, coef * b))
        lo, hi = lo + ends[0], hi + ends[1]
    return (lo, hi), ped, used, step, unit


# ---------------------------------- the quadratic fragment, read coherently
def _poly_add(t1, t2, sign):
    terms = dict(t1)
    for k, (p, q, nm) in t2.items():
        op_, oq, _ = terms.get(k, (Fraction(0), Fraction(0), nm))
        terms[k] = (op_ + sign * p, oq + sign * q, nm)
    return terms


def _poly_scale(t, k):
    return {kk: (p * k, q * k, nm) for kk, (p, q, nm) in t.items()}


def _poly(expr, quantities, counter, seen=None):
    """Read the expression as  c + Σ (p·x + q·x²)  over KEYS, or give up.

    The linear reading one degree up (the curator's X*X-2X+5=0, 2026-09-24).
    A name that multiplies ITSELF is still one number, so x*x - 2*x + 5 is one
    parabola in x, and its range over x's box is exact: the two ends and, when
    it lies inside, the vertex. Different names never multiply here: x*y is
    not separable, while a SUM of separate parabolas ranges over exactly the
    sum of their ranges, each name varying alone. A `sample` gets a key per
    occurrence, so s*s is two keys and gives up, as it must: two acts of
    measurement are two numbers. Anything else raises, and the caller keeps
    the separate interval arithmetic. No lattice step is carried: the
    lattice-miss rule reads the sides separately, as before."""
    if isinstance(expr, (int, float, Fraction)):
        return num(expr), {}, None, None
    if isinstance(expr, str):
        q = quantities[expr]
        if q.get("no_readings"):
            raise _NoReadings(f"{expr}: {q['no_readings']}")
        if seen is not None:
            seen.add(expr)
        counter[0] += 1
        if q["lo"] == q["hi"] and not isinstance(q["lo"], float):
            return q["lo"], {}, q.get("unit"), None
        key = (expr, counter[0]) if q.get("sample") else expr
        return (Fraction(0), {key: (Fraction(1), Fraction(0), expr)},
                q.get("unit"), None)
    op, *args = expr
    if op == "sqrt":                     # as in `_linear`: exact roots of constants only
        c1, t1, u1, _ = _poly(args[0], quantities, counter, seen)
        r = _rat_sqrt(c1) if not t1 and c1 >= 0 else None
        if r is None or r[0] != r[1]:
            raise _NotLinear()
        return r[0], {}, _unit_sqrt(u1), None
    if op == "sum":
        c, terms, unit = Fraction(0), {}, None
        for a in args[0]:
            c2, t2, u2, _ = _poly(a, quantities, counter, seen)
            unit = _unify_units(unit, u2, "add")
            c, terms = c + c2, _poly_add(terms, t2, 1)
        return c, terms, unit, None
    if op in ("add", "sub"):
        c1, t1, u1, _ = _poly(args[0], quantities, counter, seen)
        c2, t2, u2, _ = _poly(args[1], quantities, counter, seen)
        unit = _unify_units(u1, u2, "add")
        sign = 1 if op == "add" else -1
        return c1 + sign * c2, _poly_add(t1, t2, sign), unit, None
    if op in ("mul", "div"):
        c1, t1, u1, _ = _poly(args[0], quantities, counter, seen)
        c2, t2, u2, _ = _poly(args[1], quantities, counter, seen)
        if op == "div":
            if t2 or c2 == 0:
                raise _NotLinear()
            return (c1 / c2, _poly_scale(t1, 1 / c2),
                    _unit_combine(u1, u2, -1), None)
        unit = _unit_combine(u1, u2, +1)
        if not t2:
            return c1 * c2, _poly_scale(t1, c2), unit, None
        if not t1:
            return c1 * c2, _poly_scale(t2, c1), unit, None
        if len(t1) == 1 and len(t2) == 1 and t1.keys() == t2.keys():
            (k, (p1, q1, nm)), = t1.items()
            (_, (p2, q2, _)), = t2.items()
            if q1 == 0 and q2 == 0:          # (c1 + p1·x)(c2 + p2·x)
                return (c1 * c2, {k: (c1 * p2 + c2 * p1, p1 * p2, nm)},
                        unit, None)
        raise _NotLinear()
    raise _NotLinear()


def _at(p, q, x):
    """p·x + q·x² at a point; at an infinite end, the leading term decides."""
    if x == INF or x == -INF:
        if q != 0:
            return INF if q > 0 else -INF
        return INF if (p > 0) == (x > 0) else -INF
    return p * x + q * x * x


def _parabola_range(p, q, a, b):
    """The exact range of p·x + q·x² over x in [a, b], ends possibly infinite:
    the two ends and, if it lies strictly inside, the vertex -p/2q."""
    cands = [_at(p, q, a), _at(p, q, b)]
    if q != 0:
        v = -p / (2 * q)
        if a < v < b:
            cands.append(_at(p, q, v))
    return min(cands), max(cands)


def _ev_poly(expr, quantities):
    """(interval, pedigree, used, step, unit) via the quadratic reading, or
    None outside it. Asked only where the linear reading gave up."""
    seen = set()
    try:
        c, terms, unit, _ = _poly(expr, quantities, [0], seen)
    except (_NotLinear, KeyError):
        return None
    lo = hi = c
    for _, (p, q, name) in terms.items():
        a, b = quantities[name]["lo"], quantities[name]["hi"]
        if a == b and isinstance(a, float):
            return None          # pinned AT an infinity: no finite reading
        if p == 0 and q == 0:
            continue             # cancelled: 0 for every finite reading
        r = _parabola_range(p, q, a, b)
        lo, hi = lo + r[0], hi + r[1]
    ped = {n for n in seen if quantities[n]["prov"] == CREDIT}
    return (lo, hi), ped, set(seen), None, unit


# ------------------------------------------- exact quadratic irrationals
class QSqrt:
    """p + q·√d EXACTLY: p, q rational, d a positive integer that is not a
    square. The roots of a parabola with a non-square discriminant live here,
    (−b ± √D)/2a, and so does everything the claim computes from them and from
    rational constants: + − × ÷ stay inside, and the SIGN is decided without
    approximation (compare p² with q²d). MEASURED 2026-09-24: x*x == 2 with x
    solved came back OPEN, the root held only as a 12-digit clamp."""
    __slots__ = ("p", "q", "d")

    def __init__(self, p, q, d):
        self.p, self.q, self.d = Fraction(p), Fraction(q), int(d)

    def _pair(self, o):
        if isinstance(o, QSqrt):
            if o.q != 0 and self.q != 0 and o.d != self.d:
                raise _NotLinear()          # two different radicands: give up
            return o if o.q != 0 else QSqrt(o.p, 0, self.d)
        return QSqrt(o, 0, self.d)

    def __add__(self, o):
        o = self._pair(o)
        d = self.d if self.q != 0 else o.d
        return QSqrt(self.p + o.p, self.q + o.q, d)

    __radd__ = __add__

    def __neg__(self):
        return QSqrt(-self.p, -self.q, self.d)

    def __sub__(self, o):
        return self + (-self._pair(o))

    def __rsub__(self, o):
        return self._pair(o) - self

    def __mul__(self, o):
        o = self._pair(o)
        d = self.d if self.q != 0 else o.d
        return QSqrt(self.p * o.p + self.q * o.q * d, self.p * o.q + self.q * o.p, d)

    __rmul__ = __mul__

    def inverse(self):
        n = self.p * self.p - self.q * self.q * self.d    # never 0: d is not a square
        if n == 0:
            raise _NotLinear()
        return QSqrt(self.p / n, -self.q / n, self.d)

    def __truediv__(self, o):
        o = self._pair(o)
        return self * o.inverse()

    def __rtruediv__(self, o):
        return self._pair(o) * self.inverse()

    def sign(self):
        p, q, d = self.p, self.q, self.d
        if q == 0:
            return (p > 0) - (p < 0)
        if p == 0 or (p > 0) == (q > 0):
            return 1 if (q > 0 if p == 0 else p > 0) else -1
        # opposite signs: the larger of |p| and |q|√d wins
        big = p * p - q * q * d
        return ((p > 0) if big > 0 else (q > 0)) * 2 - 1

    def approx(self):
        return float(self.p) + float(self.q) * math.sqrt(self.d)

    def __str__(self):
        def f(x):
            x = abs(x)
            return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"
        if self.q == 0:
            return ("-" if self.p < 0 else "") + f(self.p)
        root = f"√{self.d}" if abs(self.q) == 1 else f"{f(self.q)}·√{self.d}"
        if self.p == 0:
            return ("-" if self.q < 0 else "") + root
        return f"{'-' if self.p < 0 else ''}{f(self.p)}{'-' if self.q < 0 else '+'}{root}"

    def enclose(self):
        """Rational bounds lo <= value <= hi, from the square root's clamp."""
        s_lo, s_hi = _rat_sqrt(Fraction(self.d))
        a, b = self.p + self.q * s_lo, self.p + self.q * s_hi
        return (min(a, b), max(a, b))


def qsqrt_of(r):
    """√r for a positive rational r as an exact value: a Fraction when r is a
    rational square, else a QSqrt with small square factors taken out."""
    r = Fraction(r)
    n = r.numerator * r.denominator          # √(a/b) = √(a·b)/b
    rn, sq = math.isqrt(n), Fraction(1, r.denominator)
    if rn * rn == n:
        return Fraction(rn) * sq
    k = 2
    while k * k <= n and k <= 1000:
        while n % (k * k) == 0:
            n //= k * k
            sq *= k
        k += 1
    return QSqrt(0, sq, n)


def _ev_exact(expr, quantities):
    """The expression's exact value where every name it reads is pinned or
    carries an `exact` value (a solved root): a Fraction or a QSqrt; raises
    `_NotLinear` otherwise."""
    if isinstance(expr, (int, float, Fraction)):
        return num(expr)
    if isinstance(expr, str):
        q = quantities[expr]
        if q.get("exact") is not None:
            return q["exact"]
        if q["lo"] == q["hi"] and not isinstance(q["lo"], float):
            return q["lo"]
        raise _NotLinear()
    op, *args = expr
    if op == "sqrt":
        v = _ev_exact(args[0], quantities)
        if isinstance(v, QSqrt) or v < 0:
            raise _NotLinear()
        return qsqrt_of(v) if v > 0 else Fraction(0)
    if op == "sum":
        out = Fraction(0)
        for a in args[0]:
            out = _ev_exact(a, quantities) + out
        return out
    a, b = _ev_exact(args[0], quantities), _ev_exact(args[1], quantities)
    if op == "add":
        return a + b
    if op == "sub":
        return a - b
    if op == "mul":
        return a * b
    if op == "div":
        if (b.sign() if isinstance(b, QSqrt) else (b > 0) - (b < 0)) == 0:
            raise _NotLinear()
        return a / b
    raise _NotLinear()


# ---------------------------------- one name to any degree: Sturm and Horner
UPOLY_MAX_DEGREE = 8
ROOT_WIDTH = Fraction(1, 10 ** 12)      # the clamp width of an isolated root


def _ptrim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def _padd(a, b, sign=1):
    n = max(len(a), len(b))
    return _ptrim([(a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0)
                   for i in range(n)])


def _pmul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return _ptrim(out)


def _peval(a, x):
    v = Fraction(0)
    for c in reversed(a):
        v = v * x + c
    return v


def _pderiv(a):
    return _ptrim([i * a[i] for i in range(1, len(a))]) or [Fraction(0)]


def _pdivmod(a, b):
    a, b = _ptrim(a), _ptrim(b)
    q = [Fraction(0)] * max(1, len(a) - len(b) + 1)
    r = list(a)
    while len(r) >= len(b) and any(r):
        k = len(r) - len(b)
        f = r[-1] / b[-1]
        q[k] = f
        for i, c in enumerate(b):
            r[i + k] -= f * c
        r = _ptrim(r[:-1]) if len(r) > 1 else [Fraction(0)]
        if len(r) < len(b):
            break
    return _ptrim(q), _ptrim(r)


def _pgcd(a, b):
    while any(_ptrim(b)):
        a, b = b, _pdivmod(a, b)[1]
    a = _ptrim(a)
    return [c / a[-1] for c in a]


def _sturm(a):
    """The Sturm sequence of the square-free part of `a`."""
    g = _pgcd(a, _pderiv(a))
    sq = _pdivmod(a, g)[0] if len(g) > 1 else _ptrim(a)
    seq = [sq, _pderiv(sq)]
    while len(seq[-1]) > 1 or seq[-1][0] != 0:
        r = _pdivmod(seq[-2], seq[-1])[1]
        if not any(r):
            break
        seq.append([-c for c in r])
    return seq


def _changes(seq, x):
    signs = [(v > 0) - (v < 0) for v in (_peval(p, x) for p in seq)]
    signs = [t for t in signs if t != 0]
    return sum(1 for u, v in zip(signs, signs[1:]) if u != v)


def _cauchy(a):
    a = _ptrim(a)
    return 1 + max((abs(c / a[-1]) for c in a[:-1]), default=Fraction(0))


def _simplest_between(l, h):
    """The fraction with the smallest denominator in [l, h] (Stern–Brocot).
    A rational root of a polynomial with a small leading coefficient has a
    small denominator, so in its clamp it is this one — and it is TESTED, not
    assumed: the polynomial must vanish on it exactly."""
    if l <= 0 <= h:
        return Fraction(0)
    if h < 0:
        return -_simplest_between(-h, -l)
    fl = math.floor(l)
    if fl == l or math.ceil(l) <= h:
        return Fraction(math.ceil(l))
    # l and h share an integer part: recurse on the reciprocals of the fractional parts
    return fl + 1 / _simplest_between(1 / (h - fl), 1 / (l - fl))


def _real_roots(a, lo=None, hi=None):
    """The distinct real roots of `a` in [lo, hi] (the Cauchy bound if not
    given), each as (l, h) with l <= root <= h: an exact rational root as
    (r, r), an irrational one clamped to ROOT_WIDTH. Exact rational arithmetic
    throughout; nothing is guessed."""
    a = _ptrim(a)
    if len(a) < 2:
        return []
    b = _cauchy(a)
    lo = -b if lo is None or lo == -INF else max(Fraction(lo), -b)
    hi = b if hi is None or hi == INF else min(Fraction(hi), b)
    if lo > hi:
        return []
    seq = _sturm(a)
    sq = seq[0]
    out = []

    def count(l, h):                     # roots in (l, h]
        return _changes(seq, l) - _changes(seq, h)

    def solve(l, h):                      # roots in (l, h], l not a root
        n = count(l, h)
        if n == 0:
            return
        if n == 1 and h - l <= ROOT_WIDTH:
            if _peval(sq, h) == 0:
                out.append((h, h))
                return
            r = _simplest_between(l, h)
            out.append((r, r) if l < r <= h and _peval(sq, r) == 0 else (l, h))
            return
        m = (l + h) / 2
        if _peval(sq, m) == 0:
            solve(l, m - ROOT_WIDTH / 4) if count(l, m - ROOT_WIDTH / 4) else None
            out.append((m, m))
            solve(m, h)
            return
        solve(l, m)
        solve(m, h)

    if _peval(sq, lo) == 0:
        out.append((lo, lo))
    solve(lo, hi)
    return sorted(set(out))


def _peval_iv(a, box):
    """Bounds of the polynomial over [l, h] by interval Horner — sound, and
    tight on the narrow clamps it is used on."""
    lo = hi = Fraction(0)
    for c in reversed(a):
        lo, hi = _iv_mul((lo, hi), box)
        lo, hi = lo + c, hi + c
    return lo, hi


def _one_name(n1, n2):
    if n1 is not None and n2 is not None and n1 != n2:
        raise _NotLinear()
    return n1 if n1 is not None else n2


def _upoly(expr, quantities, seen=None):
    """(coefficients from degree 0 up, name): the expression as a polynomial in
    ONE non-sample name, every other name pinned, unit-free; or `_NotLinear`.
    The parabola reading stops at degree 2; this one goes to UPOLY_MAX_DEGREE."""
    if isinstance(expr, (int, float, Fraction)):
        return [num(expr)], None
    if isinstance(expr, str):
        q = quantities[expr]
        if q.get("no_readings"):
            raise _NoReadings(f"{expr}: {q['no_readings']}")
        if seen is not None:
            seen.add(expr)
        if q.get("unit"):
            raise _NotLinear()
        if q["lo"] == q["hi"] and not isinstance(q["lo"], float):
            return [q["lo"]], None
        if q.get("sample"):
            raise _NotLinear()
        return [Fraction(0), Fraction(1)], expr
    op, *args = expr
    if op == "sqrt":
        a, n = _upoly(args[0], quantities, seen)
        r = _rat_sqrt(a[0]) if n is None and len(_ptrim(a)) == 1 and a[0] >= 0 else None
        if r is None or r[0] != r[1]:
            raise _NotLinear()
        return [r[0]], None
    if op == "sum":
        acc, name = [Fraction(0)], None
        for x in args[0]:
            a, n = _upoly(x, quantities, seen)
            name = _one_name(name, n)
            acc = _padd(acc, a)
        return acc, name
    a, n1 = _upoly(args[0], quantities, seen)
    b, n2 = _upoly(args[1], quantities, seen)
    name = _one_name(n1, n2)
    if op == "add":
        return _padd(a, b), name
    if op == "sub":
        return _padd(a, b, -1), name
    if op == "mul":
        out = _pmul(a, b)
        if len(out) - 1 > UPOLY_MAX_DEGREE:
            raise _NotLinear()
        return out, name
    if op == "div":
        b = _ptrim(b)
        if len(b) != 1 or b[0] == 0:
            raise _NotLinear()
        return [c / b[0] for c in a], name
    raise _NotLinear()


def _ev_upoly(expr, quantities):
    """(interval, pedigree, used, step, unit): the range of a polynomial of
    degree >= 3 in one name over its box — the ends (or the leading term's
    limit at an infinite end) and every critical point, a root of the
    derivative isolated by Sturm; an irrational one is bounded by interval
    Horner over its clamp. Sound, and tight to the clamp. None outside."""
    seen = set()
    try:
        coeffs, name = _upoly(expr, quantities, seen)
    except (_NotLinear, KeyError):
        return None
    coeffs = _ptrim(coeffs)
    if name is None or len(coeffs) <= 3:
        return None
    q = quantities[name]
    lo, hi = q["lo"], q["hi"]
    if lo == hi and isinstance(lo, float):
        return None
    deg, lead = len(coeffs) - 1, coeffs[-1]

    def at(x):
        if x == INF:
            return INF if lead > 0 else -INF
        if x == -INF:
            up = (lead > 0) == (deg % 2 == 0)
            return INF if up else -INF
        return _peval(coeffs, x)

    lows, highs = [at(lo), at(hi)], [at(lo), at(hi)]
    for l, h in _real_roots(_pderiv(coeffs), lo, hi):
        if l == h:
            v = _peval(coeffs, l)
            lows.append(v)
            highs.append(v)
        else:
            a, b = _peval_iv(coeffs, (l, h))
            lows.append(a)
            highs.append(b)
    ped = {n for n in seen if quantities[n]["prov"] == CREDIT}
    return (min(lows), max(highs)), ped, set(seen), None, None


# ------------------------------ the multilinear fragment, read at the corners
MLIN_MAX_KEYS = 10       # 2**10 corners; the studio caps a formula at 10 atoms anyway


def _mlin(expr, quantities, counter, keys, seen=None):
    """Read the expression as  Σ k·(a product of distinct keys) — MULTILINEAR,
    every key at most to the first power — or give up (`_NotLinear`).

    Where names multiply each other (x*y - x), neither the linear nor the
    parabola reading applies, and the separate interval arithmetic reads x
    twice: x*y - x over x in [0,1], y in [0,2] came out [-1, 2], where it is
    x·(y - 1), in [-1, 1]. A multilinear polynomial is linear in each key with
    the others fixed, so over a box its extremes sit at the CORNERS, and the
    range is exact from them. A `sample` gets a key per occurrence, so s*s is
    two keys — exactly its old decorrelated reading. `keys` maps each key to
    its name, for the bounds."""
    if isinstance(expr, (int, float, Fraction)):
        return {frozenset(): num(expr)}, None
    if isinstance(expr, str):
        q = quantities[expr]
        if q.get("no_readings"):
            raise _NoReadings(f"{expr}: {q['no_readings']}")
        if seen is not None:
            seen.add(expr)
        counter[0] += 1
        if q["lo"] == q["hi"] and not isinstance(q["lo"], float):
            return {frozenset(): q["lo"]}, q.get("unit")
        key = (expr, counter[0]) if q.get("sample") else expr
        keys[key] = expr
        return {frozenset([key]): Fraction(1)}, q.get("unit")
    op, *args = expr
    if op == "sqrt":
        t1, u1 = _mlin(args[0], quantities, counter, keys, seen)
        c1 = t1.get(frozenset(), Fraction(0))
        r = _rat_sqrt(c1) if set(t1) <= {frozenset()} and c1 >= 0 else None
        if r is None or r[0] != r[1]:
            raise _NotLinear()
        return {frozenset(): r[0]}, _unit_sqrt(u1)
    if op == "sum":
        out, unit = {}, None
        for a in args[0]:
            t, u = _mlin(a, quantities, counter, keys, seen)
            unit = _unify_units(unit, u, "add")
            for m, k in t.items():
                out[m] = out.get(m, Fraction(0)) + k
        return out, unit
    if op in ("add", "sub"):
        t1, u1 = _mlin(args[0], quantities, counter, keys, seen)
        t2, u2 = _mlin(args[1], quantities, counter, keys, seen)
        unit = _unify_units(u1, u2, "add")
        sign = 1 if op == "add" else -1
        out = dict(t1)
        for m, k in t2.items():
            out[m] = out.get(m, Fraction(0)) + sign * k
        return out, unit
    if op in ("mul", "div"):
        t1, u1 = _mlin(args[0], quantities, counter, keys, seen)
        t2, u2 = _mlin(args[1], quantities, counter, keys, seen)
        if op == "div":
            c2 = t2.get(frozenset(), Fraction(0))
            if set(t2) != {frozenset()} or c2 == 0:
                raise _NotLinear()
            return ({m: k / c2 for m, k in t1.items()},
                    _unit_combine(u1, u2, -1))
        out = {}
        for m1, k1 in t1.items():
            for m2, k2 in t2.items():
                if m1 & m2:
                    raise _NotLinear()      # a key squared: not multilinear
                m = m1 | m2
                out[m] = out.get(m, Fraction(0)) + k1 * k2
        return out, _unit_combine(u1, u2, +1)
    raise _NotLinear()


def _ev_mlin(expr, quantities):
    """(interval, pedigree, used, step, unit) from the corners, or None: when
    the expression is not multilinear, has more than MLIN_MAX_KEYS keys, or a
    key with an infinite end (a corner at infinity makes ∞ - ∞; that box keeps
    the separate reading, wide and sound)."""
    seen, keys = set(), {}
    try:
        terms, unit = _mlin(expr, quantities, [0], keys, seen)
    except (_NotLinear, KeyError):
        return None
    live = sorted({k for m, c in terms.items() if c != 0 for k in m}, key=repr)
    if len(live) > MLIN_MAX_KEYS:
        return None
    bounds = []
    for k in live:
        q = quantities[keys[k]]
        if isinstance(q["lo"], float) or isinstance(q["hi"], float):
            return None
        bounds.append((q["lo"], q["hi"]))
    lo = hi = None
    for corner in itertools.product(*bounds):
        at = dict(zip(live, corner))
        v = Fraction(0)
        for m, c in terms.items():
            if c == 0:
                continue
            t = c
            for k in m:
                t *= at[k]
            v += t
        lo = v if lo is None or v < lo else lo
        hi = v if hi is None or v > hi else hi
    if lo is None:
        lo = hi = Fraction(0)
    ped = {n for n in seen if quantities[n]["prov"] == CREDIT}
    return (lo, hi), ped, set(seen), None, unit


def _ev(expr, quantities):
    """Rich evaluator: (interval|None, pedigree, used, lattice_step, unit).
    Discreteness is tracked exactly through +, -, *, sum (integer lattices
    are closed there) and is dropped at division — a conservative
    over-approximation: derived-expression verdicts may stay Z where a
    finer analysis could refute, but a forced verdict is never wrong."""
    lin = _ev_linear(expr, quantities)
    if lin is not None:
        return lin
    if isinstance(expr, (int, float, Fraction)):
        v = num(expr)
        step = Fraction(1) if v.denominator == 1 else None
        return (v, v), set(), set(), step, None
    if isinstance(expr, str):
        q = quantities[expr]
        if q.get("no_readings"):
            raise _NoReadings(f"{expr}: {q['no_readings']}")
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
    if op == "sqrt":                       # УНАРНАЯ — до распаковки двух
        ra, pa, ua, sa, una = _ev(args[0], quantities)
        unit = _unit_sqrt(una)             # бросит _NoReadings на нечётной
        if ra is None:
            return None, pa, ua, None, unit
        # Решётка НЕ наследуется: корень из целого целым не бывает вообще.
        # Это то же консервативное огрубление, что и на делении.
        return _iv_sqrt(ra), pa, ua, None, unit
    ra, pa, ua, sa, una = _ev(args[0], quantities)
    rb, pb, ub, sb, unb = _ev(args[1], quantities)
    ped, used = pa | pb, ua | ub
    if op in ("add", "sub"):
        unit = _unify_units(una, unb, "add")
        step = sa if sa == sb else None
    elif op == "mul":
        unit = _unit_combine(una, unb, +1)
        step = 1 if sa == 1 and sb == 1 else None
    else:  # div
        unit = _unit_combine(una, unb, -1)
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
def names_in(expr, acc=None):
    """Every quantity name occurring in an expression — needed on the E
    path, where the evaluator aborts before it can collect them."""
    acc = set() if acc is None else acc
    if isinstance(expr, str):
        acc.add(expr)
    elif isinstance(expr, tuple):
        op, *args = expr
        for a in (args[0] if op == "sum" else args):
            names_in(a, acc)
    return acc


def compare(kind, e1, e2, quantities):
    """A numeric atom. Verdict by the generating principle over intervals:
    T if forced under every reading, F if the negation is forced, else Z.
    Returns (verdict, credit_pedigree, quantities_read)."""
    try:
        r1, p1, u1, s1, un1 = _ev(e1, quantities)
        r2, p2, u2, s2, un2 = _ev(e2, quantities)
        _unify_units(un1, un2, "compare")
    except _NoReadings as why:
        touched = {n for n in names_in(e1) | names_in(e2) if n in quantities}
        # THE FOURTH CORNER: no admissible reading, so there is nothing to
        # quantify over and no verdict to give. E is returned with the reason
        # attached — not a value but the judge's STOP on this atom, and on
        # nothing else.
        return E, set(), touched, str(why)
    ped, used = p1 | p2, u1 | u2
    if kind not in ("le", "lt", "eq"):
        raise ValueError(kind)
    if any(quantities[n].get("exact") is not None for n in used if n in quantities):
        # AN EXACT ROOT IS READ EXACTLY: where every name the atom reads is
        # pinned or a solved root p + q√d, the difference of the sides is an
        # exact number and its sign decides the atom (see QSqrt).
        try:
            dv = _ev_exact(("sub", e1, e2), quantities)
            sg = dv.sign() if isinstance(dv, QSqrt) else (dv > 0) - (dv < 0)
            if kind == "le":
                return ("T" if sg <= 0 else "F"), ped, used, None
            if kind == "lt":
                return ("T" if sg < 0 else "F"), ped, used, None
            return ("T" if sg == 0 else "F"), ped, used, None
        except (_NotLinear, ZeroDivisionError, KeyError):
            pass                            # something is still a box: as before
    if r1 is None or r2 is None:
        return "Z", ped, used, None       # undefined subterm: mark, not verdict
    # A NAME IS ONE NUMBER ACROSS THE WHOLE CLAIM (the curator's word,
    # 2026-09-24, in two steps): (1) for numbers m - m = 0, and m - m != 0
    # only for a `sample`, where each occurrence is a separate act of
    # measurement; (2) `==` over numbers is arithmetic, so `m == m` is true.
    # The ZTL table (Z <-> Z = F) belongs to the logical connective, not to
    # numbers: «в логике не бывает m==m, а бывает m nxor m». The judge used
    # to bound each side SEPARATELY, so a name on both sides lost its
    # identity (`m == m` Z while `m - m == 0` T), and the solver, which reads
    # the difference of the sides, disagreed with the judge. On the linear
    # fragment the difference is now read in ONE pass, each name counted
    # once (a `sample` still gets a key per occurrence): exact, hence sound,
    # and it never overturns a verdict the separate bounds gave. Outside the
    # fragment the separate bounds run unchanged — wider, and honest.
    try:
        joint = _ev_linear(("sub", e1, e2), quantities)
    except _NoReadings:
        joint = None
    if joint is None:
        # ONE DEGREE UP (2026-09-24, the curator's X*X-2X+5=0): where the
        # difference is a sum of parabolas, one per name, its range is read
        # exactly. MEASURED before this: x*x - 2*x + 5 == 0 over the reals,
        # and even (x-1)*(x-1) + 4 == 0, came back OPEN, x in x*x being read
        # as two independent numbers; the truth is REFUTED, (x-1)² + 4 >= 4.
        try:
            joint = _ev_poly(("sub", e1, e2), quantities)
        except _NoReadings:
            joint = None
    if joint is None:
        # ... and where names multiply each other, at the corners (`_mlin`)
        try:
            joint = _ev_mlin(("sub", e1, e2), quantities)
        except _NoReadings:
            joint = None
    if joint is None:
        # ... and one name to a higher degree, by its critical points (`_upoly`)
        try:
            joint = _ev_upoly(("sub", e1, e2), quantities)
        except _NoReadings:
            joint = None
    if joint is not None and (joint[0][0] != joint[0][0] or joint[0][1] != joint[0][1]):
        # nan: a quantity pinned AT +inf met an unbounded one (inf + -inf).
        # Found by the full regression, dilemmas/omnipotence.py: the stone
        # against an unlimited capacity came back OPEN instead of REFUTED.
        # The difference is undefined there; the separate bounds still decide.
        joint = None
    if joint is not None:
        d = joint[0]
        if kind == "le":
            v = "T" if d[1] <= 0 else ("F" if d[0] > 0 else "Z")
        elif kind == "lt":
            v = "T" if d[1] < 0 else ("F" if d[0] >= 0 else "Z")
        else:
            v = "T" if d == (0, 0) else ("F" if d[0] > 0 or d[1] < 0 else "Z")
    elif kind == "le":
        v = "T" if r1[1] <= r2[0] else ("F" if r1[0] > r2[1] else "Z")
    elif kind == "lt":
        v = "T" if r1[1] < r2[0] else ("F" if r1[0] >= r2[1] else "Z")
    else:                                  # equality within exactness (§13:
        d = _iv_sub(r1, r2)                # only forced equality is earned)
        v = "T" if d == (0, 0) else ("F" if d[0] > 0 or d[1] < 0 else "Z")
    if kind == "eq" and v == "Z":          # lattice miss: an int-typed side
        for sa, rb in ((s1, r2), (s2, r1)):   # can never equal a point
            if sa is not None and rb[0] == rb[1] \
                    and not _on_lattice(rb[0], sa):
                v = "F"                    # off the lattice: forced false
    return v, ped, used, None


# ------------------------------------------------- what holds a verdict up
def _degrade(q):
    """Full ignorance about the VALUE, the TYPE kept. Credit means the
    bounds may be wrong — the honest probe is therefore WIDENING, not
    narrowing: narrowing can never revoke a forced verdict (that is the
    hereditary theorem, lean/ZNum.lean), so it can never tell us what the
    verdict rides on. The lattice is not a bound and does not drop here."""
    return qty(-INF, INF, q["prov"], None,
               discrete=q["discrete"], unit=q["unit"])


def bounds_bearing(kind, e1, e2, quantities, name):
    """Does the verdict ride on THIS quantity's bounds? (Widen it to full
    ignorance and see whether the verdict survives.)"""
    v = compare(kind, e1, e2, quantities)[0]
    wide = dict(quantities)
    wide[name] = _degrade(quantities[name])
    return compare(kind, e1, e2, wide)[0] != v


def type_bearing(kind, e1, e2, quantities, name):
    """Does the verdict ride on this quantity's TYPE? A type is a
    formalization commitment, not knowledge, so its appeal is a different
    one: no document can cure it, only contesting the encoding."""
    if quantities[name]["discrete"] is None:
        return False
    v = compare(kind, e1, e2, quantities)[0]
    loose = dict(quantities)
    loose[name] = dict(quantities[name], discrete=None)
    return compare(kind, e1, e2, loose)[0] != v


# --------------------------------------- the two axes (F3) + the numeric judge
def judge_claim(kind, e1, e2, quantities):
    """Judge one numeric claim on BOTH axes, kept separate (F3):

      interval axis:    FORCED (T/F) or NOT_FORCED (Z) — cured by narrowing;
      provenance axis:  EARNED or ON_CREDIT — cured by a witness.

    Disposition = the meet of the axes; carriers name what holds it up."""
    v, ped, used, why = compare(kind, e1, e2, quantities)
    if v == E:
        # nothing to judge: the atom halts here and says why
        return {"verdict": E, "interval_axis": "NO_READINGS",
                "provenance_axis": "NO_READINGS", "credit_pedigree": [],
                "disposition": "E", "why": why, "riding_credit": False,
                "interval_carriers": [], "provenance_carriers": [],
                "type_carriers": [], "next_check": [f"repair the claim: {why}"]}
    interval_axis = "FORCED" if v in ("T", "F") else "NOT_FORCED"
    prov_axis = "ON_CREDIT" if ped else "EARNED"
    # carriers, SPLIT BY AXIS (F3 continued): each axis degrades separately,
    # so next_check can say WHICH cure the quantity needs.
    #   interval carrier:   widening the interval to full ignorance (its own
    #                       provenance and type kept) changes the verdict
    #                       -> MEASURE it;
    #   provenance carrier: the verdict is forced, this quantity's CREDIT
    #                       bounds are what it rides on -> DOCUMENT it;
    #   type carrier:       the verdict is forced by the LATTICE, and no
    #                       document can touch that -> CONTEST THE TYPE.
    # A quantity that is merely present is no carrier: MEASURED 2026-08-11
    # on 'share == 8/3' with share:int — share is in the pedigree, yet the
    # refutation stands under any bounds whatsoever, so 'document share'
    # was a cure that cures nothing. The bounds probe below removes it and
    # the type probe names the appeal that is actually open.
    interval_carriers = [n for n in sorted(used)
                         if bounds_bearing(kind, e1, e2, quantities, n)]
    provenance_carriers, type_carriers = [], []
    if v in ("T", "F"):
        # a credit quantity is a provenance carrier iff witnessing it (alone)
        # removes it from the pedigree the forced verdict rides on AND its
        # bounds are load-bearing at all
        for name in sorted(ped):
            healed = dict(quantities)
            healed[name] = dict(quantities[name], prov=EARNED)
            _, ped2, _, _ = compare(kind, e1, e2, healed)
            if ped2 == ped - {name} \
                    and bounds_bearing(kind, e1, e2, quantities, name):
                provenance_carriers.append(name)
        type_carriers = [n for n in sorted(used)
                         if type_bearing(kind, e1, e2, quantities, n)]
    # DOES the forced verdict ride on credit at all? Probe the credit
    # quantities JOINTLY (two bounds can bear together what neither bears
    # alone). Presence in the pedigree is not bearing: a claim refuted by
    # the lattice alone is refuted outright, not refuted-on-credit.
    if v == "Z":
        # nothing is forced yet, so nothing can be shown non-bearing; a
        # credit quantity whose interval already bears the openness will
        # owe a witness the moment it is measured — name that cure now
        provenance_carriers = [n for n in sorted(ped)
                               if n in interval_carriers]
    riding_credit = False
    if v in ("T", "F") and ped:
        wide = dict(quantities)
        for name in ped:
            wide[name] = _degrade(quantities[name])
        riding_credit = compare(kind, e1, e2, wide)[0] != v
        if riding_credit and not provenance_carriers:
            provenance_carriers = sorted(ped)      # jointly borne: name all
    if v == "Z":
        disp = "OPEN"
    elif riding_credit:
        disp = "ON CREDIT"
    else:
        disp = "EARNED" if v == "T" else "REFUTED"
    return {"verdict": v, "interval_axis": interval_axis,
            "provenance_axis": prov_axis, "credit_pedigree": sorted(ped),
            "disposition": disp, "riding_credit": riding_credit,
            "interval_carriers": interval_carriers,
            "provenance_carriers": provenance_carriers,
            "type_carriers": type_carriers,
            "next_check": (
                [f"measure {n}" for n in interval_carriers if v == "Z"]
                + [f"document {n}" for n in provenance_carriers]
                + [f"contest type {n}:{typename(quantities[n]['discrete'])}"
                   for n in type_carriers])}


# ============================================================== the bench
def sec1_lift_and_axes():
    print("-" * 72)
    print("1. THE LIFT AND THE TWO AXES")
    # WHAT A REPEATED NAME MEANS (settled 2026-08-11, replacing F1's global
    # decorrelation): by default a quantity is ONE THING IN THE WORLD, so
    # occurrences co-refer and cancel; `sample` says each occurrence is a
    # separate act of measurement, and then they do not.
    m = {"m": qty(0, 9, EARNED, "sensor-a")}
    iv, _, _ = ev(("sub", "m", "m"), m)
    ms = {"m": qty(0, 9, EARNED, "sensor-a", sample=True)}
    ivs, _, _ = ev(("sub", "m", "m"), ms)
    print(f"   one thing in the world: m - m over m=[0,9]  ->  "
          f"({fmt(iv[0])}, {fmt(iv[1])})")
    print(f"   two acts of measuring : m - m over m=[0,9]  ->  "
          f"({fmt(ivs[0])}, {fmt(ivs[1])})")
    assert iv == (0, 0) and ivs == (-9, 9)
    x = {"x": qty(0, 10, EARNED, "doc")}
    assert ev(("add", "x", "x"), x)[0] == (0, 20)      # x + x is 2x, not 2 boxes
    print("   and x + x is 2x, not two independent boxes — which is what")
    print("   makes an unknown solvable at all. Outside the linear fragment")
    print("   (a variable times a variable, a variable in a divisor) the")
    print("   floor falls back to plain interval arithmetic: wider, still")
    print("   sound, and the fallback is reported rather than hidden.")
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


def sec6_the_fourth_corner():
    print("-" * 72)
    print("6. THE FOURTH CORNER: E, computed rather than raised")
    print("   A formula's meaning here is its SET OF READINGS, and every")
    print("   status is one fact about that set:")
    ok = {"x": qty(1, 3, EARNED, "doc", discrete="int")}
    empty = {"k": qty(0.2, 0.9, EARNED, "doc", discrete="int")}
    units = {"a": qty(5, 5, EARNED, "doc", unit="m"),
             "b": qty(3, 3, EARNED, "doc", unit="RUB")}
    wide = {"x": qty(1, 9, EARNED, "doc", discrete="int")}
    print(f"     all readings true      x in [1,3] <= 5 : "
          f"{compare('le', 'x', 5, ok)[0]}")
    print(f"     all readings false     x in [1,3] >= 9 : "
          f"{compare('le', 9, 'x', ok)[0]}")
    print(f"     readings disagree      x in [1,9] <= 5 : "
          f"{compare('le', 'x', 5, wide)[0]}")
    print(f"     NO readings at all     k int in [.2,.9]: "
          f"{compare('le', 'k', 5, empty)[0]}   "
          f"({compare('le', 'k', 5, empty)[3]})")
    print(f"     NO readings, units     5 m == 3 RUB    : "
          f"{compare('eq', 'a', 'b', units)[0]}   "
          f"({compare('eq', 'a', 'b', units)[3]})")
    assert compare("le", "x", 5, ok)[0] == "T"
    assert compare("le", 9, "x", ok)[0] == "F"
    assert compare("le", "x", 5, wide)[0] == "Z"
    assert compare("le", "k", 5, empty)[0] == E
    assert compare("eq", "a", "b", units)[0] == E
    # and the judge stops on that atom, with the repair named
    r = judge_claim("le", "k", 5, empty)
    assert r["disposition"] == "E" and r["next_check"][0].startswith("repair")
    print(f"   the atom's disposition: {r['disposition']}, "
          f"cure {r['next_check']}")
    print("   Two things this fixes. First, E was a Python exception until")
    print("   2026-08-12 — an accident of the implementation sitting")
    print("   OUTSIDE the logic; now the floor computes it as a STOP, so")
    print("   one broken claim halts itself and not the sheet. Second, the")
    print("   empty set is exactly where 'all readings are true' comes for")
    print("   free — the vacuity trap measured in zprove.py. Separating E")
    print("   is what stops emptiness from being read as truth.")


def sec5_exact_lattices_and_carriers():
    print("-" * 72)
    print("5. EXACT LATTICES, AND WHAT A VERDICT REALLY RIDES ON")
    # (a) the two false refutations floats produced, now gone
    p = {"p": qty(0.7, 0.7, EARNED, "price-tag", discrete=("decimal", 1)),
         "r": qty(0.7, 0.7, EARNED, "price-tag")}
    assert p["p"]["lo"] == Fraction(7, 10)     # not 0.7000000000000001
    assert compare("eq", "p", "r", p)[0] == "T"
    s = {"a": qty(29.7, 29.7, EARNED, "inv-1", discrete=("decimal", 1)),
         "b": qty(0.3, 0.3, EARNED, "inv-2", discrete=("decimal", 1))}
    assert compare("eq", ("add", "a", "b"), 30, s)[0] == "T"
    print("   0.7 == 0.7 (typed vs untyped) -> T;  29.7 + 0.3 == 30 -> T")
    print("   (both were REFUTED on floats — MEASURED 2026-08-11)")
    # (b) the lattice a decimal type cannot say: thirds
    eaters, slices = qty(3, 3, EARNED, "cheque"), qty(8, 8, EARNED, "cheque")
    div = ("div", "slices", "eaters")
    ints = {"share": qty(-INF, INF, CREDIT, None, discrete="int"),
            "slices": slices, "eaters": eaters}
    thirds = dict(ints, share=qty(-INF, INF, CREDIT, None,
                                  discrete=("frac", 3)))
    dec = dict(ints, share=qty(-INF, INF, CREDIT, None,
                               discrete=("decimal", 2)))
    assert compare("eq", "share", div, ints)[0] == "F"      # whole pieces: no
    assert compare("eq", "share", div, dec)[0] == "F"       # hundredths: no
    assert compare("eq", "share", div, thirds)[0] == "Z"    # thirds: sayable
    print("   share == 8/3 :  int -> F,  decimal2 -> F,  frac3 -> Z")
    print("   'she shared it out in thirds' is now a claim, not a refutation")
    # (c) carriers: presence is not bearing
    r = judge_claim("eq", "share", div, ints)
    assert r["disposition"] == "REFUTED"
    assert r["credit_pedigree"] == ["share"]           # still on the pedigree
    assert r["provenance_carriers"] == []              # but bounds bear nothing
    assert r["type_carriers"] == ["share"]
    assert r["next_check"] == ["contest type share:int"]
    print(f"   8/3 into whole pieces: {r['disposition']}, "
          f"cure {r['next_check']} — not 'document share'")
    # the genuine document-carrier still reports itself — and here the
    # falsity really is bought on credit, so it stays ON CREDIT
    g = judge_claim("eq", "x", 5, {"x": qty(7, 9, CREDIT)})
    assert g["verdict"] == "F" and g["riding_credit"]
    assert g["disposition"] == "ON CREDIT"
    assert g["provenance_carriers"] == ["x"] and g["type_carriers"] == []
    print(f"   x == 5 with x=[7,9] on credit: {g['disposition']}, "
          f"cure {g['next_check']} — the bounds DO bear it")
    print("   so the two refutations no longer wear one face: the lattice")
    print("   one is REFUTED outright, the borrowed one stays ON CREDIT")
    print("   probe = WIDENING (narrowing cannot revoke a forced verdict —")
    print("   that is the hereditary theorem, so it can never test a carrier)")


if __name__ == "__main__":
    print("=" * 72)
    print("E37: ZNUM — the numeric floor of ZTL (probe)")
    print("=" * 72)
    sec1_lift_and_axes()
    sec2_claims_sheet()
    sec3_theorem_hunt()
    sec4_seam_with_the_judge()
    sec5_exact_lattices_and_carriers()
    sec6_the_fourth_corner()
    print("=" * 72)
    print("E37 GREEN — the lift extends to numbers (decorrelated, F1); bare")
    print("numbers are credit (F2); the two credit axes stay separate and")
    print("name their different cures (F3); forced numeric verdicts survived")
    print("every narrowing on the measured grid (the one-pass hereditary bet")
    print("stands, boundary stated); and the core judges numeric atoms")
    print("without changing a single line. Values are EXACT rationals, so")
    print("kopecks no longer refute honest sums and frac(m) lets a claim say")
    print("'in thirds'; and a carrier is what the verdict RIDES on, probed by")
    print("widening — presence in the pedigree buys no cure.")
