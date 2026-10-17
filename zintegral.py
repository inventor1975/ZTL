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
Lagrange remainder. Lean, zero axioms: lean/ZIntegral.lean — for interval and monotone leaves, every tagged sum over a
refinement of the partition lies in [L, U] (`enclosure_sound`); lean/ZIntegralR.lean — the same on VR's operational
reals with the leaves discharged by the proved readings (ZSlopeSqrt), for the grammar + - * / exp ln sqrt sin cos
tan (`enclosure_R`; sqrt found on a grid, lean/ZSqrt.lean). The Taylor leaf of ORDER 2 (lean/ZTaylor2.lean,
lean/ZIntegralT.lean, `taylor2_leaf`): the symmetric second difference is bounded by the kernel's second coefficient
along the graph (no mean value theorem), and every SYMMETRIC tagged sum of mesh mu lies in [L, U] widened by
2*K*mu*h^2 — for the grammar const var + - * exp / sqrt sin cos tan (exp's second-order step from its first-order
slopes on a grid, lean/ZExp2.lean; sin's and cos's likewise, lean/ZTrig13.lean; tan as sin/cos, as the kernel reads
it; / and sqrt by exact identities). Integer powers of a base read >= 0 (value, slope) and log10's
value: lean/ZPow.lean, ZSlopeSqrt. sin, cos over intervals (pi's bracket checked by cos at its halves), tan on
|x| <= 1.5, and their slopes (chords on a grid, no mean value theorem): lean/ZTrig10-15.lean; every kernel
reading is checked for the Lean witnesses IN THE RUN (ztrigcert; a side without them widened to +-1, tan: no reading).
Taylor leaves of EVERY even order (2026-10-17): lean/ZJetRead.lean `CRead` mirrors zcertify.taylor_coeffs node by node,
`cread_sound` + ZJetClose `cread_good` give `taylorN_kernel` — every symmetric tagged sum of mesh mu in the leaf's
interval widened by mu-terms, with no hypothesis on the derivatives — for const var + - * / exp sin cos tan sqrt (its
value read > 0) and natural powers of a base read >= 0; every leaf's two series are checked against CRead IN THE RUN
(ztaylorcert): a series failing an inequality is refused, one outside that grammar (ln, log10, atan, other powers, and
the symbolic-derivative fallback when a series has no reading) stays a premise, counted in TAYLOR_PREMISE. Still premises: non-integer pow,
atan, log10's derivative; Taylor of order 2 for ln (the kernel's recurrence needs a same-point argument); the Taylor
leaves above order 2 outside CRead's grammar. Every tagged sum, not only the symmetric ones, for the order-2 leaf:
lean/ZTransfer.lean (`taylor2_every`); for higher orders only the symmetric ones.
"""

from fractions import Fraction
import zcertify as ZC

MAX_TAYLOR = 12
# Taylor leaves checked against the Lean reading in the run: faults (refused) and premises (outside the Lean grammar),
# by reason
TAYLOR_FAULT = [0]
TAYLOR_PREMISE = {}


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
        trm, trp = {}, {}
        cm = ZC.taylor_coeffs(f, x, qs, at_m, n, trace=trm)
        cp = ZC.taylor_coeffs(f, x, qs, piece, n, trace=trp) if cm is not None else None
        if cm is not None and cp is not None:
            # THE LEAN READING, IN THE RUN (ztaylorcert; lean/ZJetRead CRead -> ZJetClose.taylorN_kernel): a series
            # that fails its inequalities is refused; one outside the Lean grammar (sqrt, ln, ...) stays a premise
            import ztaylorcert
            for piece_, cs_, tr_ in ((at_m, cm, trm), (piece, cp, trp)):
                good, why, fault = ztaylorcert.check(f, x, qs, piece_, n, cs_, tr_)
                if fault:
                    TAYLOR_FAULT[0] += 1
                    return None, f"the Taylor coefficients fail the Lean reading: {why}"
                if not good:
                    TAYLOR_PREMISE[why] = TAYLOR_PREMISE.get(why, 0) + 1
                    break
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
        # the kernel's own symbolic derivatives: outside the Lean reading (ZC.derivative is not Lean's D) — a premise
        TAYLOR_PREMISE["symbolic derivatives (no series)"] = TAYLOR_PREMISE.get("symbolic derivatives (no series)", 0) + 1
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


# ── LIMITS THAT MOVE WITH THE DATA (2026-10-16) ───────────────────────────────────────────────────────────────────
# I(p) = ∫_{A(p)}^{B(p)} f(x, p) dx, A and B reader nodes of the box. With A read in [a_lo, a_hi], B in [b_lo, b_hi]
# and a_hi <= b_lo:  I = ∫_{a_hi}^{b_lo} f  +  ∫_A^{a_hi} f  +  ∫_{b_lo}^B f.  The core is an ordinary certificate;
# each tail is (its length in [0, spread]) x f(xi), xi in the spread x the box (mean value) — hull{0, spread*f}.
#     {"core": cert}                                   -> check_limits: an enclosure for every p (sound, may be wide)
#     {"pins": {p: s}, "low": {"core": cert}, "high": {"core": cert}}
#                                                      -> check_limits_range: dI/dp = f(B) dB/dp - f(A) dA/dp
#                                                         + ∫_A^B df/dp keeps the sign s over the box (each term read,
#                                                         the last as (B - A) x df/dp over the hull) -> the range is
#                                                         spanned by the two corners, each with its limits near-points.
def _tail(f, x, qs, box, lo, hi):
    if lo == hi:
        return (Fraction(0), Fraction(0))
    r = ZC._reading(f, qs, dict(box, **{x: (lo, hi)}))
    if r is None:
        raise ArithmeticError("f has no reading where a limit moves")
    w = hi - lo
    return _out((min(Fraction(0), w * r[0]), max(Fraction(0), w * r[1])))


def check_limits(f, x, A, B, qs, cert, box=None):
    """(True, (L, U), pieces) — ∫_{A}^{B} f dx in [L, U] for every value of the box — or (False, why)."""
    box = box if box is not None else {n: (qs[n]["lo"], qs[n]["hi"]) for n in set(ZC._names(f)) | ZC._names(A)
                                         | ZC._names(B) if n in qs and n != x}
    ra = ZC._reading(A, qs, box) if not isinstance(A, Fraction) else (A, A)
    rb = ZC._reading(B, qs, box) if not isinstance(B, Fraction) else (B, B)
    if ra is None or rb is None:
        return False, "a limit has no reading over the box"
    if ra[1] > rb[0]:
        return False, "the limits' ranges overlap (A may exceed B): not read (version 1)"
    core = cert.get("core") if isinstance(cert, dict) else None
    if core is None:
        return False, "no core certificate"
    qb = dict(qs)
    for n, (lo, hi) in box.items():
        qb[n] = dict(qs[n], lo=lo, hi=hi)
    if ra[1] < rb[0]:
        got = check(f, x, ra[1], rb[0], qb, core)
        if not got[0]:
            return False, f"the core [{float(ra[1]):.9g}, {float(rb[0]):.9g}]: {got[1]}"
        C, pieces = got[1], got[2]
    else:
        C, pieces = (Fraction(0), Fraction(0)), 0
    fbox = {n: v for n, v in box.items() if n in ZC._names(f)}
    try:
        ta = _tail(f, x, qb, fbox, ra[0], ra[1])
        tb = _tail(f, x, qb, fbox, rb[0], rb[1])
    except ArithmeticError as e:
        return False, str(e)
    return True, _out((C[0] + ta[0] + tb[0], C[1] + ta[1] + tb[1])), pieces


def _limits_box(qs, names):
    return {n: (qs[n]["lo"], qs[n]["hi"]) for n in names if n in qs}


def _limit_sign(f, x, A, B, qs, box, ra, rb, p, s):
    """dI/dp = f(B) dB/dp - f(A) dA/dp + ∫_A^B df/dp, each term read over the box (the last as (B - A) x df/dp over the
    hull of the limits): (True, None) when it keeps the sign s, else (False, why)."""
    if p not in box or s not in ("+", "-"):
        return False, f"a pin on {p!r}: not a datum here, or no sign"
    try:
        dA, dB, df = ZC.derivative(A, p), ZC.derivative(B, p), ZC.derivative(f, p)
    except ZC.NoDerivative as e:
        return False, f"{p}: {e}"
    fB = ZC._reading(f, qs, dict(box, **{x: rb}))
    fA = ZC._reading(f, qs, dict(box, **{x: ra}))
    rdA, rdB = ZC._reading(dA, qs, box), ZC._reading(dB, qs, box)
    rdf = ZC._reading(df, qs, dict(box, **{x: (ra[0], rb[1])}))
    if None in (fB, fA, rdA, rdB, rdf):
        return False, f"dI/d{p}: a term has no reading"
    span = (rb[0] - ra[1], rb[1] - ra[0])
    t = ZC._iadd(ZC._imul2(fB, rdB), ZC._ineg(ZC._imul2(fA, rdA)))
    t = ZC._iadd(t, ZC._imul2(span, rdf))
    if (s == "+" and t[0] < 0) or (s == "-" and t[1] > 0):
        return False, f"dI/d{p} over the box reads [{float(t[0]):.6g}, {float(t[1]):.6g}], not {s}"
    return True, None


def check_limits_range(f, x, A, B, qs, cert):
    """(True, (L, U)) by pins: each pinned parameter's dI/dp has its sign over the box; L from the low corner, U from
    the high one (each an ordinary check_limits with the pinned parameters points) — or (False, why)."""
    pins = cert.get("pins") if isinstance(cert, dict) else None
    if not isinstance(pins, dict):
        return False, "no pins"
    names = (set(ZC._names(f)) | ZC._names(A) | ZC._names(B)) - {x}
    box = _limits_box(qs, names)
    ra, rb = ZC._reading(A, qs, box), ZC._reading(B, qs, box)
    if ra is None or rb is None or ra[1] > rb[0]:
        return False, "the limits cannot be read apart over the box"
    low_b, high_b = dict(box), dict(box)
    for p, s in pins.items():
        ok, why = _limit_sign(f, x, A, B, qs, box, ra, rb, p, s)
        if not ok:
            return False, why
        lo, hi = box[p]
        lo_end, hi_end = (lo, hi) if s == "+" else (hi, lo)
        low_b[p], high_b[p] = (lo_end, lo_end), (hi_end, hi_end)
    gl = check_limits(f, x, A, B, qs, cert.get("low") or {}, low_b)
    if not gl[0]:
        return False, f"the low corner: {gl[1]}"
    gh = check_limits(f, x, A, B, qs, cert.get("high") or {}, high_b)
    if not gh[0]:
        return False, f"the high corner: {gh[1]}"
    return True, (gl[1][0], gh[1][1])


def search_limits(f, x, A, B, qs, tol, box=None, **kw):
    """The core's certificate for check_limits (the tails are read, not searched)."""
    box = box if box is not None else _limits_box(qs, (set(ZC._names(f)) | ZC._names(A) | ZC._names(B)) - {x})
    ra = ZC._reading(A, qs, box) if not isinstance(A, Fraction) else (A, A)
    rb = ZC._reading(B, qs, box) if not isinstance(B, Fraction) else (B, B)
    if ra is None or rb is None or ra[1] > rb[0]:
        return {"gave_up": "the limits cannot be read apart over the box"}
    qb = dict(qs)
    for n, (lo, hi) in box.items():
        qb[n] = dict(qs[n], lo=lo, hi=hi)
    if ra[1] == rb[0]:
        core = {"points": [], "leaves": []}
    else:
        c = search(f, x, ra[1], rb[0], qb, tol, **kw)
        if "gave_up" in c:
            return c
        core = {k: c[k] for k in ("points", "leaves")}
    got = check_limits(f, x, A, B, qs, {"core": core}, box)
    return {"core": core, "enclosure": got[1]} if got[0] else {"gave_up": got[1]}


def search_limits_range(f, x, A, B, qs, tol, **kw):
    """Pins for every datum whose dI/dp sign shows, then the corners' cores."""
    names = (set(ZC._names(f)) | ZC._names(A) | ZC._names(B)) - {x}
    box = _limits_box(qs, names)
    pins = {}
    for p, (lo, hi) in box.items():
        if lo == hi:
            continue
        ra, rb = ZC._reading(A, qs, box), ZC._reading(B, qs, box)
        if ra is None or rb is None:
            break
        for s in ("+", "-"):
            if _limit_sign(f, x, A, B, qs, box, ra, rb, p, s)[0]:
                pins[p] = s
                break
    low_b, high_b = dict(box), dict(box)
    for p, s in pins.items():
        lo, hi = box[p]
        lo_end, hi_end = (lo, hi) if s == "+" else (hi, lo)
        low_b[p], high_b[p] = (lo_end, lo_end), (hi_end, hi_end)
    lo_c = search_limits(f, x, A, B, qs, tol, box=low_b, **kw)
    hi_c = search_limits(f, x, A, B, qs, tol, box=high_b, **kw)
    if "gave_up" in lo_c or "gave_up" in hi_c:
        return {"gave_up": lo_c.get("gave_up") or hi_c.get("gave_up")}
    cert = {"pins": pins, "low": {"core": lo_c["core"]}, "high": {"core": hi_c["core"]}}
    got = check_limits_range(f, x, A, B, qs, cert)
    if not got[0]:
        return {"gave_up": f"the kernel refused the search's own certificate: {got[1]}"}
    cert["range"] = got[1]
    return cert


# ── A DOUBLE INTEGRAL OVER A RECTANGLE (2026-10-16) ──────────────────────────────────────────────────────────────
# ∫_a^b ∫_c^d f(x, y) dy dx as iterated integrals, a certificate inside a certificate. The outer partition of [a, b];
# per piece [u, v] (width w, middle m):
#     {"interval": inner}           w x ∫_c^d f dy read with x over the whole piece (a parameter box of the inner one)
#     {"taylor": n, "inner": [I_0, I_2, ..., I_{n-2}, I_n]}
#                                    f(m + t, y) = sum_{j<n} c_j(m, y) t^j + c_n(xi, y) t^n,  c_j = (d^j f/dx^j)/j!:
#                                    the even terms integrate over t exactly (2 (w/2)^(j+1)/(j+1)), each ∫_c^d c_j(m, y) dy
#                                    by its inner certificate I_j; the remainder's ∫ c_n(xi, y) dy by I_n with x over the
#                                    piece (for each y, c_n(xi(y), y) lies in c_n's reading over the piece — the inner
#                                    enclosure holds it).
def _coef_nodes(f, x, n, cache):
    ds = _derivs(f, x, n, cache)
    out, fact = [], Fraction(1)
    for j in range(n + 1):
        if j:
            fact *= j
        out.append(ds[j] if j == 0 else ("div", ds[j], fact))
    return out


def check2(f, x, a, b, y, c, d, qs, cert):
    """(True, (L, U), inner pieces) — ∫_a^b ∫_c^d f dy dx in [L, U] for every value of the box — or (False, why)."""
    a, b, c, d = Fraction(a), Fraction(b), Fraction(c), Fraction(d)
    try:
        pts = [Fraction(str(p)) for p in cert["points"]]
        leaves = cert["leaves"]
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False, "the certificate is unreadable"
    if pts[0] != a or pts[-1] != b or any(p2 <= p1 for p1, p2 in zip(pts, pts[1:])) or len(leaves) != len(pts) - 1:
        return False, "the outer partition does not cover [a, b] in order with a leaf per piece"
    cache = {}
    L = U = Fraction(0)
    count = 0

    def inner(node, xbox, icert):
        q2 = dict(qs, **{x: dict(qs[x], lo=xbox[0], hi=xbox[1])})
        return check(node, y, c, d, q2, icert)
    for i, (u, v, leaf) in enumerate(zip(pts, pts[1:], leaves)):
        w, m, h = v - u, (u + v) / 2, (v - u) / 2
        if isinstance(leaf, dict) and "interval" in leaf:
            g = inner(f, (u, v), leaf["interval"])
            if not g[0]:
                return False, f"outer piece {i}: the inner integral: {g[1]}"
            r = _out((w * g[1][0], w * g[1][1]))
            count += g[2]
        elif isinstance(leaf, dict) and "taylor" in leaf:
            n = leaf["taylor"]
            ins = leaf.get("inner")
            if not isinstance(n, int) or n < 2 or n > MAX_TAYLOR or n % 2 or not isinstance(ins, list) \
                    or len(ins) != n // 2 + 1:
                return False, f"outer piece {i}: a taylor leaf needs an even order and n/2 + 1 inner certificates"
            cn = _coef_nodes(f, x, n, cache)
            lo = hi = Fraction(0)
            for k, j in enumerate(range(0, n + 1, 2)):
                g = inner(cn[j], (u, v) if j == n else (m, m), ins[k])
                if not g[0]:
                    return False, f"outer piece {i}: the inner integral of c_{j}: {g[1]}"
                coef = 2 * h ** (j + 1) / (j + 1)
                lo, hi = lo + coef * g[1][0], hi + coef * g[1][1]
                count += g[2]
            r = _out((lo, hi))
        else:
            return False, f"outer piece {i}: unknown leaf"
        L, U = L + r[0], U + r[1]
    return True, _out((L, U)), count


def search2(f, x, a, b, y, c, d, qs, tol, orders=(4, 2), max_pieces=400):
    """An outer partition with inner certificates (untrusted; check2 decides)."""
    a, b = Fraction(a), Fraction(b)
    cache = {}
    stack, pts, leaves, count = [(a, b)], [a], [], 0
    while stack:
        u, v = stack.pop()
        count += 1
        if count > max_pieces:
            return {"gave_up": f"more than {max_pieces} outer pieces"}
        share = Fraction(tol) * (v - u) / (b - a)
        m = (u + v) / 2
        found = None
        for n in orders:
            cn = _coef_nodes(f, x, n, cache)
            ins, lo, hi, ok = [], Fraction(0), Fraction(0), True
            for j in range(0, n + 1, 2):
                xb = (u, v) if j == n else (m, m)
                q2 = dict(qs, **{x: dict(qs[x], lo=xb[0], hi=xb[1])})
                # inner tolerance: the remainder's share scaled by its weight, the exact terms a fraction of tol
                coef = 2 * ((v - u) / 2) ** (j + 1) / (j + 1)
                # the REMAINDER (j == n, x over the piece) is wide by nature — x's own spread — and only weighed by
                # (w/2)^(n+1): read coarsely (a small budget, else one crude piece); if the sum is still too wide the
                # OUTER piece is cut, not the inner one (MEASURED: a 1e-6 inner search of it ran 3000 pieces, 106 s)
                ic = search(cn[j], y, c, d, q2, share / (4 * coef) if coef else share,
                            max_pieces=8 if j == n else 4000)
                if "gave_up" in ic and j == n:
                    ic = search(cn[j], y, c, d, q2, Fraction(10) ** 30, max_pieces=64)
                if "gave_up" in ic:
                    ok = False
                    break
                ins.append({k: ic[k] for k in ("points", "leaves")})
                lo, hi = lo + coef * ic["enclosure"][0], hi + coef * ic["enclosure"][1]
            if ok and hi - lo <= share:
                found = {"taylor": n, "inner": ins}
                break
        if found is not None:
            pts.append(v)
            leaves.append(found)
            continue
        mid = (u + v) / 2
        stack.append((mid, v))
        stack.append((u, mid))
    cert = {"points": [f"{p.numerator}/{p.denominator}" for p in pts], "leaves": leaves}
    got = check2(f, x, a, b, y, c, d, qs, cert)
    if not got[0]:
        return {"gave_up": f"the kernel refused the search's own certificate: {got[1]}"}
    cert["enclosure"] = got[1]
    return cert
