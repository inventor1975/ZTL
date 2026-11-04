# -*- coding: utf-8 -*-
"""
zsteps — THE PRICE OF AN ALGEBRA STEP: a chain of equations in one unknown, checked step by step (2026-11-05, the
curator: "при решении уравнений часто перемещают переменные под знаменателем… Делаем").

    python3 zsteps.py "x^2 = x" "x = 1"                       (the whole real line)
    python3 zsteps.py "x*(x-5) = 3*(x-5)" "x = 3" --domain 0,4 [--credit]

The algebraic twin of zderive (E26, the price of a LOGIC step). Moving a denominator, cancelling a factor, dividing
both sides: each is valid only where the thing divided by (or multiplied away) is not zero, and that condition is
usually not written. Here every step is judged by its SOLUTION SETS, exactly:

    EARNED     the two equations have the same solutions on the domain (the domain verified);
    ON CREDIT  the same, but the domain is not verified (dirty): the step holds as far as the domain does;
    REFUTED    a solution is LOST (e.g. dividing by x loses x = 0) or GAINED (multiplying a denominator away gains
               the point where the original was undefined) — with the witness and the cause named;
    E          the step divides by an expression that is 0 for EVERY x (the "1 = 2" proofs): it has no subject
               (ZTL 2.1 §25, as on the numeric floor since f0c71f8).

EXACT, standard library only: an equation L = R becomes the rational function f = L - R over Fractions, and the
evaluator keeps EVERY denominator it met (the original is undefined there even if the fraction cancels: (x^2-1)/(x-1)
= 2 has no solution, x + 1 = 2 has x = 1). The solution set is {x in domain: numerator(f) = 0, no denominator 0};
lost and gained roots are the real roots of exact polynomial quotients, counted and isolated by znum's Sturm
sequences — nothing is sampled. A rational witness is exact; an irrational one is clamped to 1e-12.
Scope v1: one unknown; + - * / and integer powers; numbers are exact decimals. Roots, logarithms, several unknowns:
not yet (refused with the reason, never guessed).
"""
from __future__ import annotations

import re
import sys
from fractions import Fraction

import znum as ZN

MUTANT = {}       # TEST-ONLY sabotage switches; empty = the real check
MAX_DEGREE = 24


# ------------------------------------------------------------------ polynomials (coefficients low -> high, Fractions)
P0, P1 = [Fraction(0)], [Fraction(1)]


def _deg(p):
    p = ZN._ptrim(p)
    return -1 if (len(p) == 1 and p[0] == 0) else len(p) - 1


def _is_zero(p):
    return _deg(p) == -1


def _sqfree(p):
    p = ZN._ptrim(p)
    if _deg(p) <= 0:
        return p
    g = ZN._pgcd(p, ZN._pderiv(p))
    return ZN._pdivmod(p, g)[0] if _deg(g) > 0 else p


def _strip_common(a, b):
    """a with every root it shares with b removed (a square-free)."""
    a = _sqfree(a)
    if _deg(a) <= 0 or _is_zero(b):
        return a
    g = ZN._pgcd(a, b)
    return ZN._pdivmod(a, g)[0] if _deg(g) > 0 else a


class StepError(ValueError):
    pass


# ------------------------------------------------------------------ parsing to rational functions
_TOK = re.compile(r"\s*(?:(\d+(?:\.\d*)?|\.\d+)|([A-Za-z_][A-Za-z_0-9]*)|(\*\*|\^|[-+*/()]))")


def _tokens(s):
    out, i = [], 0
    s = s.strip()
    while i < len(s):
        m = _TOK.match(s, i)
        if not m or m.end() == i:
            raise StepError(f"cannot read {s[i:]!r}")
        num, name, op = m.groups()
        out.append(("num", num) if num else ("name", name) if name else ("op", "^" if op == "**" else op))
        i = m.end()
    return out


class _RF:
    """A rational function N/D in one unknown, with the denominators met on the way (where it is undefined)."""
    __slots__ = ("n", "d", "dens")

    def __init__(self, n, d, dens):
        g = ZN._pgcd(n, d) if not _is_zero(n) else d
        if _deg(g) > 0:
            n, d = ZN._pdivmod(n, g)[0], ZN._pdivmod(d, g)[0]
        if _is_zero(n):
            d = P1
        lead = ZN._ptrim(d)[-1]
        self.n = [c / lead for c in ZN._ptrim(n)]
        self.d = [c / lead for c in ZN._ptrim(d)]
        self.dens = dens
        if max(_deg(self.n), _deg(self.d)) > MAX_DEGREE:
            raise StepError(f"degree above {MAX_DEGREE}")


def _const(c):
    return _RF([Fraction(c)], P1, [])


def _add(a, b, sign=1):
    return _RF(ZN._padd(ZN._pmul(a.n, b.d), ZN._pmul(b.n, a.d), sign), ZN._pmul(a.d, b.d), a.dens + b.dens)


def _mul(a, b):
    return _RF(ZN._pmul(a.n, b.n), ZN._pmul(a.d, b.d), a.dens + b.dens)


def _div(a, b, text):
    if _is_zero(b.n):
        # divided by an expression that is 0 for every x: there is no reading at all
        raise _NoSubject(f"divides by {text}, which is 0 for every x")
    return _RF(ZN._pmul(a.n, b.d), ZN._pmul(a.d, b.n), a.dens + b.dens + [(b.n, text)])


class _NoSubject(Exception):
    pass


def _parse(s, var, consts):
    toks = _tokens(s)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else (None, None)

    def take():
        t = peek()
        pos[0] += 1
        return t

    def text(i, j):
        return "".join(v for _k, v in toks[i:j])

    def atom():
        k, v = peek()
        if k == "num":
            take()
            return _const(Fraction(v))
        if k == "name":
            take()
            if v == var:
                return _RF([Fraction(0), Fraction(1)], P1, [])
            if v in consts:
                return _const(Fraction(consts[v]))
            raise StepError(f"unknown name {v!r} (v1: one unknown, other names need values)")
        if v == "(":
            take()
            r = expr()
            if take() != ("op", ")"):
                raise StepError("a ')' is missing")
            return r
        if v == "-":
            take()
            return _mul(_const(-1), power())
        raise StepError(f"unexpected {v!r}")

    def power():
        base = atom()
        if peek() == ("op", "^"):
            take()
            neg = False
            if peek() == ("op", "-"):
                take()
                neg = True
            k, v = take()
            if k != "num" or "." in v:
                raise StepError("v1: only integer powers")
            n = int(v)
            r = _const(1)
            for _ in range(n):
                r = _mul(r, base)
            if neg:
                r = _div(_const(1), r, "a negative power")
            return r
        return base

    def term():
        start = pos[0]
        r = power()
        while peek() in (("op", "*"), ("op", "/")):
            op = take()[1]
            i = pos[0]
            rhs = power()
            r = _mul(r, rhs) if op == "*" else _div(r, rhs, text(i, pos[0]))
        return r

    def expr():
        r = term()
        while peek() in (("op", "+"), ("op", "-")):
            op = take()[1]
            rhs = term()
            r = _add(r, rhs, 1 if op == "+" else -1)
        return r

    r = expr()
    if pos[0] != len(toks):
        raise StepError(f"cannot read the end of {s!r}")
    return r


def equation(s, var="x", consts=None):
    """'L = R' -> the rational function L - R with every denominator met (or _NoSubject)."""
    parts = re.split(r"==|=", s)
    if len(parts) != 2:
        raise StepError(f"one '=' per equation: {s!r}")
    L, R = (_parse(p, var, consts or {}) for p in parts)
    return _add(L, R, -1)


# ------------------------------------------------------------------ solution sets, exactly
def _undef(f):
    """the polynomial whose real roots are the points where the equation is undefined"""
    if MUTANT.get("no_definedness"):        # sabotage (tests only): forget where the original was undefined
        return P1
    p = P1
    for q, _t in f.dens:
        p = ZN._pmul(p, _sqfree(q))
    return p


def _sols(f):
    """(polynomial whose roots are the solutions, everywhere?) — 'everywhere' when the equation is an identity"""
    if _is_zero(f.n):
        return None, True
    return _strip_common(f.n, _undef(f)), False


def _roots(p, lo, hi):
    p = ZN._ptrim(p)
    if _deg(p) <= 0:
        return []
    lo_ = lo if lo is not None else -ZN._cauchy(p)
    hi_ = hi if hi is not None else ZN._cauchy(p)
    return ZN._real_roots(p, lo_, hi_)


def _show(iv):
    l, h = iv
    return str(l) if l == h else f"~{float((l + h) / 2):.12g}"


def _ptext(p, var="x"):
    """a polynomial as a person writes it"""
    p = ZN._ptrim(p)
    terms = []
    for k in range(len(p) - 1, -1, -1):
        c = p[k]
        if c == 0:
            continue
        mag = abs(c)
        cs = "" if (mag == 1 and k > 0) else str(mag)
        mon = "" if k == 0 else (var if k == 1 else f"{var}^{k}")
        t = cs + ("*" if cs and mon else "") + mon
        terms.append(("- " if c < 0 else "+ ") + t)
    out = " ".join(terms) or "0"
    return out[2:] if out.startswith("+ ") else "-" + out[2:]


def _cause_lost(r, f, g, var="x"):
    for q, t in g.dens:
        if _vanishes(q, r):
            return f"the step divides by {t}, which is 0 there"
    # a factor cancelled from both sides without being written: the quotient of the two numerators
    if not _is_zero(g.n) and _deg(g.n) >= 0:
        q, rem = ZN._pdivmod(f.n, g.n)
        if _is_zero(rem) and _deg(q) > 0 and _vanishes(q, r):
            return f"the step cancelled the factor {_ptext(q, var)} from both sides, which is 0 there"
    return "the new equation has no solution there"


def _vanishes(q, iv):
    l, h = iv
    if l == h:
        return ZN._peval(q, l) == 0
    # an irrational root: q vanishes on it iff q shares the root's minimal factor — test by sign change on the clamp
    return any(r[0] <= l and h <= r[1] or (l <= r[0] and r[1] <= h) for r in _roots(q, l - (h - l), h + (h - l)))


def _cause_gained(r, f):
    for q, t in f.dens:
        if _vanishes(q, r):
            return f"the original is undefined there ({t} is 0) — the step multiplied that denominator away"
    return "the new equation has a solution the original does not"


def check_step(s1, s2, var="x", consts=None, domain=(None, None)):
    lo, hi = domain
    try:
        f = equation(s1, var, consts)
    except _NoSubject as e:
        return {"verdict": "E", "why": f"the first equation {e}"}
    try:
        g = equation(s2, var, consts)
    except _NoSubject as e:
        return {"verdict": "E", "why": f"the step {e} — there is nothing to check, ever: repair the derivation"}
    A, allA = _sols(f)
    B, allB = _sols(g)
    lost, gained = [], []
    if allA and allB:
        # both identities: compare where each is undefined
        lost = [(r, f"the step makes the equation undefined there") for r in _roots(_strip_common(_undef(g), _undef(f)), lo, hi)]
        gained = [(r, "the step defines the equation where the original was undefined") for r in _roots(_strip_common(_undef(f), _undef(g)), lo, hi)]
    elif allA or allB:
        # an identity against an equation: everything but finitely many points is lost (or gained); a witness point
        p = B if allA else A
        bad = ZN._pmul(_undef(f), _undef(g))
        cand = [Fraction(k) for k in range(-50, 51)] + [Fraction(k, 7) for k in range(-50, 51)]
        w = next((x for x in cand if (lo is None or x >= lo) and (hi is None or x <= hi)
                  and ZN._peval(p, x) != 0 and ZN._peval(bad, x) != 0), None)
        if w is not None:
            (lost if allA else gained).append(((w, w), "every x solves one equation and not the other"))
    else:
        for r in _roots(_strip_common(A, B), lo, hi):
            lost.append((r, _cause_lost(r, f, g, var)))
        for r in _roots(_strip_common(B, A), lo, hi):
            gained.append((r, _cause_gained(r, f)))
    out = {"lost": [(_show(r), c) for r, c in lost], "gained": [(_show(r), c) for r, c in gained]}
    out["verdict"] = "REFUTED" if (lost or gained) else "EARNED"
    return out


def check_chain(eqs, var="x", consts=None, domain=(None, None), domain_earned=True):
    """Every step of a chain; the chain's verdict is its weakest step's."""
    steps = []
    for s1, s2 in zip(eqs, eqs[1:]):
        r = check_step(s1, s2, var, consts, domain)
        if not domain_earned and r["verdict"] in ("EARNED", "REFUTED"):
            r["verdict"] = "ON CREDIT" if r["verdict"] == "EARNED" else "REFUTED (on credit)"
            r["domain"] = "the domain is not verified: the step holds only as far as the domain does"
        steps.append({"from": s1, "to": s2, **r})
    order = ["E", "REFUTED", "REFUTED (on credit)", "ON CREDIT", "EARNED"]
    worst = min((s["verdict"] for s in steps), key=order.index) if steps else "EARNED"
    return {"verdict": worst, "steps": steps}


# ------------------------------------------------------------------ self-test (both sides + a sabotage)
def _selftest():
    H = Fraction
    def v(eqs, **k):
        return check_chain(eqs, **k)
    r = v(["x^2 = x", "x = 1"])
    assert r["verdict"] == "REFUTED" and r["steps"][0]["lost"] == [
        ("0", "the step cancelled the factor x from both sides, which is 0 there")], r
    r2 = v(["(x^2-1)/(x-1) = 2", "x^2-1 = 2*(x-1)"])
    assert r2["verdict"] == "REFUTED" and r2["steps"][0]["gained"][0][0] == "1" \
        and "undefined" in r2["steps"][0]["gained"][0][1], r2
    r3 = v(["2*x + 3 = 7", "2*x = 4", "x = 2"])
    assert r3["verdict"] == "EARNED", r3
    r4 = v(["x*(x^2+1) = 2*(x^2+1)", "x = 2"])
    assert r4["verdict"] == "EARNED", r4                      # divided by x^2+1: never 0
    r5a = v(["x*(x-5) = 3*(x-5)", "x = 3"], domain=(H(0), H(4)))
    r5b = v(["x*(x-5) = 3*(x-5)", "x = 3"])
    assert r5a["verdict"] == "EARNED" and r5b["verdict"] == "REFUTED" and r5b["steps"][0]["lost"] == [
        ("5", "the step cancelled the factor x - 5 from both sides, which is 0 there")], (r5a, r5b)
    r9 = v(["x^2 = x", "x^2/x = x/x"])                       # the division WRITTEN on both sides: named as such
    assert r9["verdict"] == "REFUTED" and r9["steps"][0]["lost"] == [("0", "the step divides by x, which is 0 there")], r9
    r6 = v(["(x+x)*(x-x) = x*(x-x)", "x+x = x*(x-x)/(x-x)"])
    assert r6["verdict"] == "E", r6                          # the "1 = 2" proofs: dividing by x - x
    r7 = v(["x^2 = 2", "x = 0"])
    assert r7["verdict"] == "REFUTED" and len(r7["steps"][0]["lost"]) == 2 and r7["steps"][0]["lost"][0][0].startswith("~"), r7
    r8 = v(["x*(x-5) = 3*(x-5)", "x = 3"], domain=(H(0), H(4)), domain_earned=False)
    assert r8["verdict"] == "ON CREDIT", r8
    MUTANT["no_definedness"] = True                           # forget where the original was undefined
    try:
        assert v(["(x^2-1)/(x-1) = 2", "x^2-1 = 2*(x-1)"])["verdict"] == "EARNED"
    finally:
        MUTANT.clear()
    print("  x^2 = x -> x = 1: REFUTED, x = 0 lost (the step cancelled the factor x from both sides, which is 0 there)")
    print("  (x^2-1)/(x-1) = 2 -> x^2-1 = 2(x-1): REFUTED, x = 1 gained (the original is undefined there)")
    print("  2x+3 = 7 -> 2x = 4 -> x = 2: EARNED;  x(x^2+1) = 2(x^2+1) -> x = 2: EARNED (x^2+1 is never 0)")
    print("  x(x-5) = 3(x-5) -> x = 3: EARNED on [0, 4], REFUTED on the line (x = 5 lost); ON CREDIT on a dirty domain")
    print("  dividing by x - x (the '1 = 2' proofs): E;  x^2 = 2 -> x = 0: both irrational roots lost, clamped")
    print("  the sabotage (forget where the original was undefined) turns the gained root into a false EARNED: caught")
    print("ZSTEPS GREEN")


def main(argv):
    if not argv or argv[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    if argv == ["--selftest"]:
        _selftest()
        return 0
    dom, earned, eqs = (None, None), True, []
    i = 0
    while i < len(argv):
        if argv[i] == "--domain":
            a, b = argv[i + 1].split(",")
            dom = (None if a in ("", "-inf") else Fraction(a), None if b in ("", "inf") else Fraction(b))
            i += 2
        elif argv[i] == "--credit":
            earned = False
            i += 1
        else:
            eqs.append(argv[i])
            i += 1
    r = check_chain(eqs, domain=dom, domain_earned=earned)
    print(f"chain: {r['verdict']}")
    for s in r["steps"]:
        print(f"  {s['from']}  ->  {s['to']}:  {s['verdict']}" + (f"  ({s['why']})" if s.get("why") else ""))
        for w, c in s.get("lost", []):
            print(f"      LOST    x = {w}: {c}")
        for w, c in s.get("gained", []):
            print(f"      GAINED  x = {w}: {c}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]) if sys.argv[1:] else (_selftest() or 0))
