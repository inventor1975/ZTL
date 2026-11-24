# -*- coding: utf-8 -*-
"""
zsummation — THE SUMMATION METHOD IS A DIRTY PARAMETER (2026-11-25, the curator: "Надо делать как я понял… будет
ровненько"; the article https://ztljudge.com/articles/mathematics/minus-one-twelfth/).

"1 + 2 + 3 + … = −1/12" names no method. ZTL reads the method M as a dirty parameter of the claim and judges it
under every reading of M. This module gives, EXACTLY, the value a series takes under each method, for the class on
which the famous derivations live:

        Σ_{n ≥ 0} P(n)        and        Σ_{n ≥ 0} (−1)^n P(n),        P a polynomial with rational coefficients,

indexed as Lean's `∑' n : ℕ` is (from n = 0). The methods (names as `METHODS`):

  limit    the limit of the partial sums: a value only when P ≡ 0 (otherwise the terms do not tend to 0)
  mathlib  Mathlib's `tsum`: the unconditional sum when summable (P ≡ 0), and 0 BY CONVENTION otherwise
  abel     lim_{x→1⁻} Σ a_n x^n: alternating series get η-values; a non-alternating P ≢ 0 has none
  cesaro   (C,1), the limit of the means of the partial sums: an alternating constant c gets c/2; otherwise none
  zeta     the article's definition: the series a₁ + a₂ + … (a₁ the FIRST term, here P(0)) gets the value at s = 0 of
           the continuation of Σ a_m m^(−s). With Q(m) = P(m − 1) = Σ q_j m^j: Σ q_j ζ(−j); alternating: Σ q_j η(−j)

        ζ(0) = −1/2, ζ(−j) = −B_{j+1}/(j+1) (j ≥ 1);  η(−j) = (1 − 2^{j+1}) ζ(−j), η(0) = 1/2.

THE ZERO IN FRONT. Under zeta regularisation, 1 + 2 + 3 + … = ζ(−1) = −1/12, while 0 + 1 + 2 + 3 + … (Lean's
∑' n : ℕ, n — the same terms behind one zero) = ζ(−1) − ζ(0) = 5/12: the method is not stable, which is the article's
point, here computed rather than asserted.

`None` means: no value under that method (the reading set is empty — E for that reading). A Python reading; the
article's Lean theorems (ζ(−1) = −1/12, the partial sums unbounded, no stable additive method) are in
inventor1975/ztl-classical, not a twin of this module.
"""
from fractions import Fraction
from math import comb

METHODS = ("limit", "mathlib", "abel", "cesaro", "zeta")


def bernoulli(n):
    """B_n with B_1 = −1/2 (the recursion Σ_{k<m+1} C(m+1, k) B_k = 0)"""
    B = [Fraction(1)]
    for m in range(1, n + 1):
        B.append(-sum(comb(m + 1, k) * B[k] for k in range(m)) / (m + 1))
    return B[n]


def zeta_neg(j):
    """ζ(−j) for j ≥ 0"""
    return Fraction(-1, 2) if j == 0 else -bernoulli(j + 1) / (j + 1)


def eta_neg(j):
    """η(−j) = (1 − 2^{j+1}) ζ(−j): the Dirichlet eta at −j (η(0) = 1/2)"""
    return (1 - 2 ** (j + 1)) * zeta_neg(j)


def _trim(p):
    return {k: Fraction(v) for k, v in p.items() if v != 0}


def shift_to_one(p):
    """P(n) = Σ p_k n^k  ->  Q(m) = P(m − 1) = Σ q_j m^j"""
    q = {}
    for k, c in _trim(p).items():
        for j in range(k + 1):
            q[j] = q.get(j, 0) + c * comb(k, j) * (-1) ** (k - j)
    return _trim(q)


def value(p, alternating, method):
    """the value of Σ_{n ≥ 0} (−1)^{n·alternating} P(n) under `method`, exactly, or None (no value)"""
    p = _trim(p)
    if not p:
        return Fraction(0)                              # every method gives an all-zero series 0
    if method == "limit":
        return None
    if method == "mathlib":
        return Fraction(0)                              # not summable: Mathlib's tsum is 0 by convention
    q = shift_to_one(p)
    deg = max(q) if q else 0
    if method == "cesaro":
        if alternating and deg == 0:
            return q.get(0, Fraction(0)) * eta_neg(0)  # c − c + c − … : (C,1) gives c/2
        return None
    if method == "abel":
        if not alternating:
            return None
        return sum((c * eta_neg(j) for j, c in q.items()), Fraction(0))
    if method == "zeta":
        f = eta_neg if alternating else zeta_neg
        return sum((c * f(j) for j, c in q.items()), Fraction(0))
    raise ValueError(method)


def table(p, alternating):
    return {m: value(p, alternating, m) for m in METHODS}


# ------------------------------------------------ geometric: Σ_{n ≥ 0} P(n) r^n (2026-11-25, Lean Workbook's series)
# MEASURED that day: of 58 translated series statements in Goedel's Lean Workbook proofs, none was a power series
# Σ P(n); almost all were GEOMETRIC — Σ x^n = 1/(1 − x), Σ (1/2)^i = 1, Σ k/3^k, Σ n² x^(2n).
#     Σ_{n ≥ 0} n^k r^n = r A_k(r) / (1 − r)^(k+1)  (k ≥ 1, A_k the Eulerian polynomial),  Σ r^n = 1/(1 − r).
#   |r| < 1: the series converges; every method gives that sum.
#   |r| > 1: the terms grow — no limit, no Abel (Σ r^n x^n diverges near x = 1), no (C,1); Mathlib 0 by convention;
#            zeta (Σ a_m m^(−s) at s = 0, a polylogarithm) gives the continuation of the same rational function
#            (1 + 2 + 4 + 8 + … = −1). For r ≠ 1 a zero in front does not move it (only r = 1 is unstable).
#   r = 1, r = −1: the power-series case above.  |r| = 1 otherwise is not rational.
def eulerian(k):
    """A_k(r) = Σ_{m < k} A(k, m) r^m, A(k, m) = Σ_j (−1)^j C(k+1, j) (m+1−j)^k"""
    return {m: sum((-1) ** j * comb(k + 1, j) * (m + 1 - j) ** k for j in range(m + 2)) for m in range(k)}


def geo_closed(p, r):
    """Σ_{n ≥ 0} P(n) r^n as the rational function's value at a rational r ≠ 1 (the sum when |r| < 1)"""
    r = Fraction(r)
    out = Fraction(0)
    for k, c in _trim(p).items():
        if k == 0:
            out += c / (1 - r)
        else:
            a = sum((Fraction(v) * r ** m for m, v in eulerian(k).items()), Fraction(0))
            out += c * r * a / (1 - r) ** (k + 1)
    return out


def value_geo(p, r, method):
    """the value of Σ_{n ≥ 0} P(n) r^n under `method`, r rational, exactly, or None"""
    r = Fraction(r)
    p = _trim(p)
    if not p or r == 0:
        return Fraction(p.get(0, 0)) if r == 0 else Fraction(0)      # 0^0 = 1: only the n = 0 term
    if r == 1:
        return value(p, False, method)
    if r == -1:
        return value(p, True, method)
    if abs(r) < 1:
        return geo_closed(p, r)
    if method == "mathlib":
        return Fraction(0)
    if method == "zeta":
        return geo_closed(p, r)
    return None


def closed_text(p, rt):
    """the rational function Σ P(n) r^n as ZFL text in a ratio given as text (for a ratio that is a variable)"""
    terms = []
    for k, c in sorted(_trim(p).items()):
        cs = f"({c.numerator} / {c.denominator})" if c.denominator != 1 else (f"(0 - {-c})" if c < 0 else str(c))
        if k == 0:
            terms.append(f"({cs} / (1 - {rt}))")
        else:
            a = " + ".join(f"({v} * ({rt})**{m})" for m, v in eulerian(k).items())
            terms.append(f"(({cs} * {rt} * ({a})) / (1 - {rt})**{k + 1})")
    return "(" + " + ".join(terms) + ")" if terms else "0"
