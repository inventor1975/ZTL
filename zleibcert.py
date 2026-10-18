"""THE LEIBNIZ PIN IN THE RUN — the premises of lean/ZLeibniz.leibniz_low / leibniz_high (zero axioms).

zintegral.check_limits_range pins a parameter p_j that moves a limit when the kernel's
t_j = f(B)·dB/dp_j − f(A)·dA/dp_j + (B − A)·df/dp_j keeps a sign over the box. Lean proves the same rule as a finite
difference (no derivative of the integral): from a point of the box to its corner, sums sharing their middle differ by
Σ_j Δ_j·t_j. Its premises, checked here with LEAN'S readings (not the kernel's):
  * a step reading (ZDeriv.StepRead) along p_j of f, A and B over [a_lo, b_hi] × the box, and a box bound of the
    grammar's D_j of each (zmonocert.lean_D_reading: naive VRead meet the affine AffR);
  * f's value read (naive VRead) over each limit's range × the box (the ends' φ);
  * the span [b_lo − a_hi, b_hi − a_lo], b_lo ≥ a_hi;
  * t_j by corners with the readings FOLDED by the pin's direction (DRd: [L, U] for "+", [−U, −L] for "−"):
    cB_lo − cA_hi + cS_lo ≥ 0. (leibniz_high is leibniz_low for 0 − f with the flags flipped: the folded products are
    the same numbers, so one check serves both corners.)
"""
from fractions import Fraction as F

import zmonocert as M
import ztaylorcert as T


def _corners(a, b):
    ps = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(ps), max(ps)


def leibniz_covered(f, x, A, B, qs, box, ra, rb, pins):
    """"" when every pin's t_j keeps its sign with Lean's readings (ZLeibniz's premises), else why not."""
    if ra[1] > rb[0]:
        return "the limits' readings overlap"
    whole = dict(box, **{x: (ra[0], rb[1])})
    fA = T.lean_naive(f, qs, dict(box, **{x: ra}))
    fB = T.lean_naive(f, qs, dict(box, **{x: rb}))
    if fA is None or fB is None:
        return "f at a limit: no Lean reading"
    span = (rb[0] - ra[1], rb[1] - ra[0])
    for p, s in pins.items():
        rd = {}
        for name, g in (("f", f), ("A", A), ("B", B)):
            if isinstance(g, (F, int)):
                rd[name] = (F(0), F(0))
                continue
            r, why = M.lean_D_reading(g, p, qs, whole)
            if r is None:
                return f"d{name}/d{p}: {why}"
            rd[name] = r
        fold = (lambda L, U: (L, U)) if s == "+" else (lambda L, U: (-U, -L))
        df, dA, dB = fold(*rd["f"]), fold(*rd["A"]), fold(*rd["B"])
        cS, cA, cB = _corners(span, df), _corners(fA, dA), _corners(fB, dB)
        if cB[0] - cA[1] + cS[0] < 0:
            return f"pin {p}: t_j with Lean's readings reaches {float(cB[0] - cA[1] + cS[0]):.3g} < 0"
    return ""
