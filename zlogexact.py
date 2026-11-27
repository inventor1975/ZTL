# -*- coding: utf-8 -*-
"""
zlogexact — EXACT LOGARITHMS OF RATIONALS on the numeric floor (2026-11-24, the curator: "Надо, делаем").

WHY. The floor reads ln as a proved bracket of rationals, so an EQUALITY with logarithms is never forced: ln 64 / ln 8
is a narrow interval around 2, never 2, and `log_8 64 + log_4 64 = 5` stays OPEN (MEASURED on aime_1984_p5's
hypotheses at a = -64, b = 8 in Lean's reading). Inequalities were decided; equalities were not.

WHAT. At a point where every quantity is pinned to a rational, an expression built from + - * / ln log10 (and ifpos,
integer powers, min, max) is read EXACTLY as

        c + Σ r_p · ln p        (c and every r_p rational, p prime)

ln(a/b) = Σ e_p ln p by unique factorisation, so ln 64 = 6 ln 2 and ln 64 / ln 8 = 2 — as an equality, not a bracket.
A quotient of two such values is exact when they are proportional (both constants 0, coefficient vectors parallel);
otherwise the reading gives up and the interval path decides as before.

WHEN IS IT ZERO — decided exactly:
    c + Σ r_p ln p = 0   iff   c = 0 and every r_p = 0.
    * c = 0: Σ r_p ln p = 0 means Π p^(N r_p) = 1 for a common denominator N; by unique factorisation every r_p = 0.
    * c ≠ 0, some r_p ≠ 0: e^(-c) = Π p^(r_p) is algebraic, while e^q is transcendental for rational q ≠ 0
      (Hermite 1873; Lindemann–Weierstrass) — never equal.
    * c ≠ 0, every r_p = 0: the value is c.
The SIGN of a non-zero value is read from the floor's own proved brackets of ln p (zfunc.ln_pt); a bracket that
straddles 0 leaves the sign undecided (None), never guessed.

SOUNDNESS, 2026-11-27: Hermite–Lindemann is used by no verdict — sign() is 0 only for the formal zero and otherwise
reads the proved brackets (straddling 0: no verdict). What every verdict DOES use is ln(xy) = ln x + ln y: PROVED on
VR's continuum, lean/ZLnMul.lean `rln_mul` (from exp's addition law, lean/ZExpAdd5.lean `rexpR_add`), zero axioms;
the factorisations are checked by the kernel in inventory/zlogexact_lean_bridge.py. Primality and the uniqueness of
the factorisation matter only for completeness (the zero test), not for soundness.
"""
from fractions import Fraction

FACTOR_CAP = 10 ** 12          # a numerator or denominator past this is not factorised (NotExact)


class NotExact(Exception):
    pass


def _factor(n):
    """the prime factorisation of a positive integer n <= FACTOR_CAP, as {p: e}"""
    if n > FACTOR_CAP:
        raise NotExact(f"{n} is past the factorisation cap")
    out, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


class LogLin:
    """c + Σ r[p] ln p — c a Fraction, r {prime: Fraction}, no zero coefficients kept"""

    def __init__(self, c=Fraction(0), r=None):
        self.c = Fraction(c)
        self.r = {p: Fraction(v) for p, v in (r or {}).items() if v != 0}

    @staticmethod
    def of(x):
        return x if isinstance(x, LogLin) else LogLin(x)

    @staticmethod
    def ln(q):
        """ln of a positive rational, exactly"""
        q = Fraction(q)
        if q <= 0:
            raise NotExact("ln of a non-positive value")
        r = {}
        for p, e in _factor(q.numerator).items():
            r[p] = r.get(p, 0) + e
        for p, e in _factor(q.denominator).items():
            r[p] = r.get(p, 0) - e
        return LogLin(0, r)

    def is_rational(self):
        return not self.r

    def __add__(self, o):
        o = LogLin.of(o)
        r = dict(self.r)
        for p, v in o.r.items():
            r[p] = r.get(p, 0) + v
        return LogLin(self.c + o.c, r)

    def __neg__(self):
        return LogLin(-self.c, {p: -v for p, v in self.r.items()})

    def __sub__(self, o):
        return self + (-LogLin.of(o))

    def scale(self, k):
        k = Fraction(k)
        return LogLin(self.c * k, {p: v * k for p, v in self.r.items()})

    def is_zero(self):
        """exact: c + Σ r_p ln p = 0 iff c = 0 and every r_p = 0 (unique factorisation; Hermite for c ≠ 0)"""
        return self.c == 0 and not self.r

    def bracket(self):
        """a proved enclosure of the value, from the floor's brackets of ln p"""
        import zfunc
        lo = hi = self.c
        for p, v in self.r.items():
            a, b = zfunc.ln_pt(Fraction(p))
            ends = (v * a, v * b)
            lo, hi = lo + min(ends), hi + max(ends)
        return lo, hi

    def sign(self):
        """-1, 0 or +1, exactly for 0; from the brackets otherwise (None when they straddle 0)"""
        if self.is_zero():
            return 0
        if self.is_rational():
            return (self.c > 0) - (self.c < 0)
        lo, hi = self.bracket()
        if lo > 0:
            return 1
        if hi < 0:
            return -1
        return None


def _div(a, b):
    a, b = LogLin.of(a), LogLin.of(b)
    if b.is_zero():
        raise NotExact("a division by an exact 0: the interval path says what that is")
    if b.is_rational():
        return a.scale(1 / b.c)
    # proportional: a = k b  with both constants 0 and parallel vectors
    if a.is_zero():
        return LogLin(0)
    if a.c != 0 or b.c != 0 or set(a.r) != set(b.r):
        raise NotExact("a quotient of logarithms that is not a rational multiple")
    ks = {a.r[p] / b.r[p] for p in a.r}
    if len(ks) != 1:
        raise NotExact("a quotient of logarithms that is not a rational multiple")
    return LogLin(ks.pop())


def _mul(a, b):
    a, b = LogLin.of(a), LogLin.of(b)
    if a.is_rational():
        return b.scale(a.c)
    if b.is_rational():
        return a.scale(b.c)
    raise NotExact("a product of two logarithms")


def _rat(x):
    x = LogLin.of(x)
    if not x.is_rational():
        raise NotExact("a logarithm where a rational is needed")
    return x.c


def ev(expr, quantities):
    """the exact value (LogLin) of an expression at a point where every name is pinned to a rational, or NotExact"""
    if isinstance(expr, (int, Fraction)):
        return LogLin(Fraction(expr))
    if isinstance(expr, float):
        raise NotExact("an infinity")
    if isinstance(expr, str):
        q = quantities.get(expr)
        if q is None or q.get("no_readings"):
            raise NotExact(f"{expr}: no pinned reading")
        if q.get("exact") is not None and isinstance(q["exact"], Fraction):
            return LogLin(q["exact"])
        lo, hi = q["lo"], q["hi"]
        if lo != hi or isinstance(lo, float):
            raise NotExact(f"{expr} is not pinned")
        return LogLin(Fraction(lo))
    op, *args = expr
    if op == "sum":
        out = LogLin(0)
        for a in args[0]:
            out = out + ev(a, quantities)
        return out
    if op in ("ln", "log10"):
        v = _rat(ev(args[0], quantities))
        out = LogLin.ln(v)
        return _div(out, LogLin.ln(10)) if op == "log10" else out
    if op == "ifpos":
        s = ev(args[0], quantities).sign()
        if s is None:
            raise NotExact("an undecided branch")
        return ev(args[1] if s == 1 else args[2], quantities)
    if op in ("min", "max"):
        a, b = ev(args[0], quantities), ev(args[1], quantities)
        s = (a - b).sign()
        if s is None:
            raise NotExact("an undecided min/max")
        return (a if s <= 0 else b) if op == "min" else (a if s >= 0 else b)
    if op == "pow":
        base, ex = ev(args[0], quantities), _rat(ev(args[1], quantities))
        if ex.denominator != 1:
            raise NotExact("a non-integer power")
        b = _rat(base)
        if b == 0 and ex < 0:
            raise NotExact("0 to a negative power")
        return LogLin(b ** int(ex))
    if op in ("add", "sub", "mul", "div"):
        a, b = ev(args[0], quantities), ev(args[1], quantities)
        if op == "add":
            return a + b
        if op == "sub":
            return a - b
        if op == "mul":
            return _mul(a, b)
        return _div(a, b)
    raise NotExact(f"{op}: no exact logarithmic reading")


def has_log(expr):
    if isinstance(expr, tuple):
        if expr[0] in ("ln", "log10"):
            return True
        return any(has_log(a) for a in (expr[1] if expr[0] == "sum" else expr[1:]))
    return False
