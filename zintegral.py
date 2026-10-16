# -*- coding: utf-8 -*-
"""
A DEFINITE INTEGRAL — ∫_a^b f(x, p) dx enclosed for EVERY p of the box (2026-10-16, the curator's "да, делай интегралы").

ZTL's numbers read an expression over a box as a proved interval; this module reads an integral the same way. The
kernel does not search (the decision of 2026-10-09): a CERTIFICATE — a partition of [a, b] and a leaf per piece — is
found outside (search(), untrusted, below) and the kernel checks every piece with its own readings (zcertify._reading,
znum._ev, zfunc's brackets) and its own derivatives (zcertify.derivative):

    {"points": ["a", "x1", ..., "b"],          fractions, strictly increasing, from a to b
     "leaves": [leaf, ...]}                    one per piece [x_i, x_i+1], width w, middle m:
        "interval"                     w * f read over the piece (and the box)
        {"monotone": "+" | "-"}        df/dx keeps that sign on the piece × box -> the integral lies between
                                       w * f(left end) and w * f(right end)
        {"taylor": n}  (n even, 2..12) f(m + t) = sum_{j<n} f^(j)(m) t^j / j! + f^(n)(xi) t^n / n!  (Lagrange):
                                       the odd terms integrate to 0 over [-w/2, w/2], the even ones exactly to
                                       2 (w/2)^(j+1) / (j+1)!, and as t^n >= 0 the remainder lies in
                                       f^(n)(piece) * 2 (w/2)^(n+1) / (n+1)!   (n = 2: the midpoint rule)
Every piece's enclosure is rounded OUTWARD; their sum encloses the integral for every p of the box.

THE CLAIM, operational (no "real integral" as an object): for every p of the box and every eps > 0 there is a delta
such that EVERY Riemann sum of mesh below delta lies in [L - eps, U + eps] — [L, U] holds the limit of the Riemann
sums. (CORRECTED 2026-10-16, the same day: the first text said every Riemann sum of every refinement lies in [L, U].
That holds for interval and monotone leaves — each tagged sum of such a piece lies between w*inf f and w*sup f, or
between the end values — but NOT for a Taylor leaf, whose enclosure hugs the integral itself: a coarse sum w*f(u)
of that piece may fall outside it.) The premises named, not proved here: the elementary functions are as smooth as
their readings say (a derivative read finite over a piece bounds the derivative there), and Taylor's theorem with the
Lagrange remainder. Lean: not yet.
"""

from fractions import Fraction
import zcertify as ZC

MAX_TAYLOR = 12


def _out(iv):
    return ZC._iv_out(iv)


def _derivs(f, x, n, cache):
    """[f, f', ..., f^(n)] (symbolic, the kernel's own derivative), cached per expression."""
    key = (f, x)
    ds = cache.setdefault(key, [f])
    while len(ds) <= n:
        ds.append(ZC.derivative(ds[-1], x))
    return ds


def _piece_enclosure(f, x, u, v, qs, box, leaf, cache):
    """(lo, hi) of ∫_u^v f dx for every p of the box, or (None, why)."""
    w = v - u
    if w <= 0:
        return None, "a piece of no width"
    piece = dict(box, **{x: (u, v)})
    if leaf == "interval":
        r = ZC._reading(f, qs, piece)
        if r is None:
            return None, "f has no reading on the piece"
        return _out((w * r[0], w * r[1])), None
    if isinstance(leaf, dict) and "monotone" in leaf:
        s = leaf["monotone"]
        if s not in ("+", "-"):
            return None, "a monotone leaf with no sign"
        d = _derivs(f, x, 1, cache)[1]
        r = ZC._reading(d, qs, piece)
        if r is None or (s == "+" and r[0] < 0) or (s == "-" and r[1] > 0):
            return None, (f"df/d{x} on the piece reads [{float(r[0]):.6g}, {float(r[1]):.6g}], not {s}" if r is not None
                          else f"df/d{x} has no reading on the piece")
        fu = ZC._reading(f, qs, dict(box, **{x: (u, u)}))
        fv = ZC._reading(f, qs, dict(box, **{x: (v, v)}))
        if fu is None or fv is None:
            return None, "f has no value at an end"
        lo_end, hi_end = (fu, fv) if s == "+" else (fv, fu)
        return _out((w * lo_end[0], w * hi_end[1])), None
    if isinstance(leaf, dict) and "taylor" in leaf:
        n = leaf["taylor"]
        if not isinstance(n, int) or n < 2 or n > MAX_TAYLOR or n % 2:
            return None, f"taylor order {n!r}: an even number 2..{MAX_TAYLOR}"
        m = (u + v) / 2
        h = w / 2
        at_m = dict(box, **{x: (m, m)})
        # TAYLOR COEFFICIENTS ALONG THE GRAPH first (zcertify.taylor_coeffs: c_j = f^(j)/j!, recurrences over shared
        # nodes): the symbolic derivatives of sqrt to order 6 were trees of nested roots, 228 s for a 1e-6 search
        cm = ZC.taylor_coeffs(f, x, qs, at_m, n)
        cp = ZC.taylor_coeffs(f, x, qs, piece, n) if cm is not None else None
        if cm is not None and cp is not None:
            lo = hi = Fraction(0)
            for j in range(0, n + 1, 2):
                coef = 2 * h ** (j + 1) / (j + 1)
                r = cp[n] if j == n else cm[j]
                lo, hi = lo + coef * r[0], hi + coef * r[1]
            return _out((lo, hi)), None
        ds = _derivs(f, x, n, cache)
        lo = hi = Fraction(0)
        fact = Fraction(1)                       # (j+1)!
        for j in range(n + 1):
            fact *= (j + 1)
            if j % 2:
                continue
            coef = 2 * h ** (j + 1) / fact
            r = ZC._reading(ds[j], qs, piece if j == n else at_m)
            if r is None:
                return None, f"the derivative of order {j} has no reading " + ("on the piece" if j == n else "at the middle")
            lo, hi = lo + coef * r[0], hi + coef * r[1]
        return _out((lo, hi)), None
    return None, f"unknown leaf {leaf!r}"


def check(f, x, a, b, qs, cert):
    """(True, (L, U), pieces) — ∫_a^b f dx lies in [L, U] for every value of the box — or (False, why).
    f: a reader node; x: the variable's name (a quantity of qs; its own box is ignored, the pieces set it);
    a, b: fractions; qs: the quantities (every other name of f at its box)."""
    a, b = Fraction(a), Fraction(b)
    if a >= b:
        return False, f"the limits [{float(a)}, {float(b)}] are not increasing"
    try:
        pts = [Fraction(str(p)) for p in cert["points"]]
        leaves = cert["leaves"]
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False, "the certificate is unreadable"
    if pts[0] != a or pts[-1] != b:
        return False, f"the partition runs {float(pts[0])}..{float(pts[-1])}, not {float(a)}..{float(b)}"
    if any(p2 <= p1 for p1, p2 in zip(pts, pts[1:])):
        return False, "the partition is not strictly increasing (an overlap or an empty piece)"
    if len(leaves) != len(pts) - 1:
        return False, f"{len(pts) - 1} pieces and {len(leaves)} leaves"
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in ZC._names(f) if n in qs and n != x}
    cache = {}
    L = U = Fraction(0)
    for i, (u, v, leaf) in enumerate(zip(pts, pts[1:], leaves)):
        r, why = _piece_enclosure(f, x, u, v, qs, box, leaf, cache)
        if r is None:
            return False, f"piece {i} [{float(u):.9g}, {float(v):.9g}]: {why}"
        L, U = L + r[0], U + r[1]
    L, U = _out((L, U))
    return True, (L, U), len(leaves)


def proves(f, x, a, b, qs, op, bound, cert):
    """Does the certificate show ∫_a^b f dx  op  bound (op "<=" or ">=") for every value of the box?"""
    got = check(f, x, a, b, qs, cert)
    if not got[0]:
        return got
    L, U = got[1]
    ok = U <= bound if op == "<=" else L >= bound if op == ">=" else False
    return (True, got[2]) if ok else (False, f"the integral is proved in [{float(L):.17g}, {float(U):.17g}], "
                                                 f"not {op} {float(bound):.17g}")


# ── THE SEARCH (outside the kernel, trusted for nothing: check() decides) ──────────────────────────────────────────
def search(f, x, a, b, qs, tol, max_pieces=20000, orders=(6, 4, 2)):
    """A certificate whose enclosure is at most `tol` wide (when the readings allow): each piece tries Taylor leaves
    of falling order, then a monotone and an interval leaf, and is halved when none is narrow enough for its share
    tol * w / (b - a). -> {"points", "leaves", "enclosure"} or {"gave_up": why}."""
    a, b = Fraction(a), Fraction(b)
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in ZC._names(f) if n in qs and n != x}
    cache = {}
    out_pts, out_leaves = [a], []
    stack = [(a, b)]
    count = 0
    width_total = b - a
    while stack:
        u, v = stack.pop()
        count += 1
        if count > max_pieces:
            return {"gave_up": f"more than {max_pieces} pieces"}
        share = Fraction(tol) * (v - u) / width_total
        # the PARAMETERS' own spread on this piece (w * f at the middle over the box) no cut in x removes: only the
        # discretisation error is refined (a parameter's range is tightened by pinning it — range_with_pins)
        fm = ZC._reading(f, qs, dict(box, **{x: ((u + v) / 2, (u + v) / 2)}))
        share += (v - u) * (fm[1] - fm[0]) if fm is not None else 0
        best = None
        cands = [{"taylor": n} for n in orders] + [{"monotone": "+"}, {"monotone": "-"}, "interval"]
        for leaf in cands:
            r, _why = _piece_enclosure(f, x, u, v, qs, box, leaf, cache)
            if r is not None and (best is None or r[1] - r[0] < best[1][1] - best[1][0]):
                best = (leaf, r)
                if r[1] - r[0] <= share:
                    break
        if best is not None and best[1][1] - best[1][0] <= share:
            out_pts.append(v)
            out_leaves.append(best[0])
            continue
        mid = (u + v) / 2
        mid = Fraction(round(mid * 2 ** 40), 2 ** 40) if u < Fraction(round(mid * 2 ** 40), 2 ** 40) < v else mid
        stack.append((mid, v))
        stack.append((u, mid))
    cert = {"points": [f"{p.numerator}/{p.denominator}" for p in out_pts], "leaves": out_leaves}
    got = check(f, x, a, b, qs, cert)
    if not got[0]:
        return {"gave_up": f"the kernel refused the search's own certificate: {got[1]}"}
    cert["enclosure"] = got[1]
    return cert


# ── A PARAMETER'S RANGE BY PINS (the kernel checks) ─────────────────────────────────────────────────────────────────
# If df/dp keeps one sign over [a, b] × the box, the integral is monotone in p (for every value of the other data):
# its range over p is spanned by p at its two ends. Pinning every such parameter, the integral's range over the box is
# [∫ at the low corner, ∫ at the high corner] — each a narrow certificate with every pinned parameter a point.
#     {"pins": {p: "+" | "-"}, "low": cert, "high": cert}
#     low: the parameters at the end that makes the integral smallest; high: largest; a parameter not pinned keeps its
#     box in both (its spread stays in the enclosures).
def check_range(f, x, a, b, qs, cert):
    """(True, (L, U)) — ∫_a^b f dx lies in [L, U] for every value of the box, L and U each read at a corner — or
    (False, why)."""
    a, b = Fraction(a), Fraction(b)
    pins = cert.get("pins") if isinstance(cert, dict) else None
    if not isinstance(pins, dict):
        return False, "no pins"
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in ZC._names(f) if n in qs and n != x}
    whole = dict(box, **{x: (a, b)})
    low_q, high_q = dict(qs), dict(qs)
    for p, s in pins.items():
        if p not in box or s not in ("+", "-"):
            return False, f"a pin on {p!r}: not a parameter of the integrand, or no sign"
        r = ZC._reading(ZC.derivative(f, p), qs, whole)
        if r is None or (s == "+" and r[0] < 0) or (s == "-" and r[1] > 0):
            return False, (f"df/d{p} over [a, b] x the box reads "
                           + (f"[{float(r[0]):.6g}, {float(r[1]):.6g}]" if r is not None else "nothing") + f", not {s}")
        lo, hi = box[p]
        lo_end, hi_end = (lo, hi) if s == "+" else (hi, lo)
        low_q[p] = dict(qs[p], lo=lo_end, hi=lo_end)
        high_q[p] = dict(qs[p], lo=hi_end, hi=hi_end)
    gl = check(f, x, a, b, low_q, cert.get("low") or {})
    if not gl[0]:
        return False, f"the low corner: {gl[1]}"
    gh = check(f, x, a, b, high_q, cert.get("high") or {})
    if not gh[0]:
        return False, f"the high corner: {gh[1]}"
    return True, (gl[1][0], gh[1][1])


def search_range(f, x, a, b, qs, tol, **kw):
    """Pins for every parameter whose df/dp sign shows over [a, b] x the box, then a search at each corner."""
    a, b = Fraction(a), Fraction(b)
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in ZC._names(f) if n in qs and n != x}
    whole = dict(box, **{x: (a, b)})
    pins, low_q, high_q = {}, dict(qs), dict(qs)
    for p, (lo, hi) in box.items():
        if lo == hi:
            continue
        try:
            r = ZC._reading(ZC.derivative(f, p), qs, whole)
        except ZC.NoDerivative:
            r = None
        if r is not None and (r[0] >= 0 or r[1] <= 0):
            s = "+" if r[0] >= 0 else "-"
            pins[p] = s
            lo_end, hi_end = (lo, hi) if s == "+" else (hi, lo)
            low_q[p] = dict(qs[p], lo=lo_end, hi=lo_end)
            high_q[p] = dict(qs[p], lo=hi_end, hi=hi_end)
    low = search(f, x, a, b, low_q, tol, **kw)
    high = search(f, x, a, b, high_q, tol, **kw)
    if "gave_up" in low or "gave_up" in high:
        return {"gave_up": (low.get("gave_up") or high.get("gave_up"))}
    cert = {"pins": pins, "low": {k: low[k] for k in ("points", "leaves")},
            "high": {k: high[k] for k in ("points", "leaves")}}
    got = check_range(f, x, a, b, qs, cert)
    if not got[0]:
        return {"gave_up": f"the kernel refused the search's own range certificate: {got[1]}"}
    cert["range"] = got[1]
    return cert
