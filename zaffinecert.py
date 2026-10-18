# -*- coding: utf-8 -*-
"""The Lean reading for the kernel's AFFINE reading (lean/ZAffine*.lean `AffR`, `aff_sound`), in exact fractions — the
bridge between zaffine.read and the theorem ZAffine.aff_sound (zero axioms, on VR's operational reals).

The kernel's value readings (zcertify._reading) meet the plain reading with the affine one (zaffine.read), and the
affine one is tighter than any Lean VRead (the red team's F1, measured 2026-10-17: 124 readings of the integral stand).
`read_checked` replays zaffine.read with the kernel's own steps and checks, step by step, the premises of the AffR
constructor that step is:
  * a constant; a point variable; a basis element (a variable of the box: centre and radius of its box; a subtree
    read plainly — `opaque` — whose plain reading must contain Lean's naive reading, ztaylorcert._naive);
  * +, −: exact;  ×: the error |c_x| e_y + |c_y| e_x + (R_x + e_x)(R_y + e_y);  the grid rounding (tidy): widen;
  * the min-range steps: 1/x on a POSITIVE interval, the slope at a (α ≤ −1/a²) or at b (α ≥ −1/b²), the remainder's
    two ends against ζ ± δ (rem_recip_a/b); exp, the slope at a (α ≤ e^a's certified lower bracket, the brackets of e^a
    and e^b certified by ZExp.ExpCert, zexpcert), the ends against ζ ± δ (rem_exp).
  * ln, the slope at b (α·b ≤ 1, the ends' ln brackets certified as zfunc._cert_ln, rem_ln); log10 = ln × 1/ln 10;
    u^c (c not an integer) = exp(c·ln u).
  * atan, not across zero: the slope at the end where ψ = 1/(1 + t²) is smaller, α·(1 + end²) ≤ 1, the ends' brackets
    certified by zatancert (rem_atan_pos / rem_atan_neg, lean/ZAffineAtan.lean).
Not in AffR: sqrt, integer powers, 1/x of a negative interval, the shared form of the case reading. The
replay's interval must equal the kernel's (a mismatch is a FAULT: the mirror lost the kernel).
"""
from fractions import Fraction as F

import zaffine as ZA
import zfunc as ZF
from zexpcert import exp_cert


class Uncovered(Exception):
    """A step outside AffR, or a premise that fails."""


def read_checked(e, qs, piece, rat_sqrt, plain, naive):
    """(interval, "") when zaffine.read's affine reading of e is an AffR derivation, (interval or None, why) when not.
    plain(n) -> the kernel's plain reading of a subtree; naive(n) -> Lean's naive VRead of it (or None)."""

    def leaf(name):
        lo, hi = piece.get(name, (qs[name]["lo"], qs[name]["hi"]))
        if isinstance(lo, float) or isinstance(hi, float):
            raise ZA.Unknown("an infinite end")
        lo, hi = F(lo), F(hi)
        if lo == hi:
            return ZA.Aff(lo)                          # AffR.point
        return ZA.Aff((lo + hi) / 2, {name: (hi - lo) / 2})   # AffR.basis (a variable)

    fresh = [0]

    def opaque(n):
        iv = plain(n)
        if iv is None or any(isinstance(v, float) for v in iv):
            raise ZA.Unknown("no plain reading")
        lo, hi = F(iv[0]), F(iv[1])
        nv = naive(n)
        if nv is None or not (lo <= nv[0] and nv[1] <= hi):
            raise Uncovered(f"an opaque {n[0] if isinstance(n, tuple) else n}: its plain reading is tighter than Lean's")
        fresh[0] += 1
        return ZA.Aff((lo + hi) / 2, {("#", fresh[0]): (hi - lo) / 2} if lo != hi else {})   # AffR.basis

    def rad0(x):
        return sum((abs(v) for v in x.t.values()), F(0))

    def widen_ok(pre, post):
        """AffR.widen: post.e ≥ pre.e + |Δc| + Σ |Δt_j| (t_j = s_j r_j)."""
        keys = set(pre.t) | set(post.t)
        need = pre.e + abs(pre.c - post.c) + sum((abs(pre.t.get(k, 0) - post.t.get(k, 0)) for k in keys), F(0))
        if not post.e >= need:
            raise Uncovered("a grid rounding lost more than its error")

    def mul(x, y):
        t = {}
        for k, v in x.t.items():
            t[k] = t.get(k, 0) + y.c * v
        for k, v in y.t.items():
            t[k] = t.get(k, 0) + x.c * v
        if x.e < 0 or y.e < 0:
            raise Uncovered("a negative error")
        e = abs(x.c) * y.e + abs(y.c) * x.e + (rad0(x) + x.e) * (rad0(y) + y.e)     # AffR.mul, exactly
        pre = ZA.Aff(x.c * y.c, t, e)
        post = ZA.Aff(pre.c, dict(pre.t), pre.e).tidy()
        widen_ok(pre, post)
        out = ZA._mul(x, y)                            # the kernel's own step
        if (out.c, out.t, out.e) != (post.c, post.t, post.e):
            raise RuntimeError("FAULT: the replay of _mul lost the kernel")
        return out

    def nl(x, alpha, zeta, delta):
        """AffR.nl: α·x + ζ, error |α| e + δ, then the rounding (the kernel's _scale)."""
        if x.e < 0:
            raise Uncovered("a negative error")
        pre = ZA.Aff(alpha * x.c + zeta, {k: alpha * v for k, v in x.t.items()}, abs(alpha) * x.e + delta)
        post = ZA.Aff(pre.c, dict(pre.t), pre.e).tidy()
        widen_ok(pre, post)
        return post

    def minrange(x, f, df, convex, end):
        """zaffine._minrange's numbers: (α, ζ, δ, a, b, fa, fb)."""
        a, b = x.iv()
        fa, fb = f(a), f(b)
        if convex and end == "a":
            alpha = ZA._down(df(a)[0])
        elif convex:
            alpha = ZA._up(df(b)[1])
        elif end == "a":
            alpha = ZA._up(df(a)[1])
        else:
            alpha = ZA._down(df(b)[0])
        inc = (convex and end == "a") or (not convex and end != "a")
        ra = (fa[0] - alpha * a, fa[1] - alpha * a)
        rb = (fb[0] - alpha * b, fb[1] - alpha * b)
        rlo, rhi = (ra[0], rb[1]) if inc else (rb[0], ra[1])
        return alpha, (rlo + rhi) / 2, ZA._up((rhi - rlo) / 2), a, b, fa, fb, inc

    def recip(x):
        a, b = x.iv()
        if a <= 0 <= b:
            raise ZA.Unknown("1/x across zero")
        if b < 0:
            raise Uncovered("1/x of a negative interval")
        f = lambda t: (1 / F(t), 1 / F(t))
        df = lambda t: (-1 / (F(t) * t), -1 / (F(t) * t))
        end = ZA._pick_end(df(a), df(b))
        alpha, zeta, delta, a, b, fa, fb, inc = minrange(x, f, df, True, end)
        if end == "a":                                 # rem_recip_a
            ok = alpha <= -1 / (a * a) and zeta - delta <= 1 / a - alpha * a and 1 / b - alpha * b <= zeta + delta
        else:                                          # rem_recip_b
            ok = alpha >= -1 / (b * b) and zeta - delta <= 1 / b - alpha * b and 1 / a - alpha * a <= zeta + delta
        if not ok:
            raise Uncovered(f"1/x: the remainder's premises fail (end {end})")
        out = nl(x, alpha, zeta, delta)
        k = ZA._recip(x)
        if (k.c, k.t, k.e) != (out.c, out.t, out.e):
            raise RuntimeError("FAULT: the replay of _recip lost the kernel")
        return out

    def exp(x):
        f = lambda t: ZF.exp_pt(F(t))
        alpha, zeta, delta, a, b, fa, fb, inc = minrange(x, f, f, True, "a")
        if not (exp_cert(a, fa[0], fa[1])[0] and exp_cert(b, fb[0], fb[1])[0]):
            raise Uncovered("exp: a bracket without its ExpCert")
        if not (alpha <= fa[0] and zeta - delta <= fa[0] - alpha * a and fb[1] - alpha * b <= zeta + delta):
            raise Uncovered("exp: the remainder's premises fail")
        out = nl(x, alpha, zeta, delta)
        k = ZA._exp(x)
        if (k.c, k.t, k.e) != (out.c, out.t, out.e):
            raise RuntimeError("FAULT: the replay of _exp lost the kernel")
        return out

    def atan(x):
        from zatancert import atan_cert
        a, b = x.iv()
        if a < 0 < b:
            raise ZA.Unknown("atan across zero")
        f = lambda t: ZF.atan_pt_cert(F(t))
        df = lambda t: (1 / (1 + F(t) * t), 1 / (1 + F(t) * t))
        end = "a" if b <= 0 else "b"
        alpha, zeta, delta, a, b, fa, fb, inc = minrange(x, f, df, b <= 0, end)
        # rem_atan_pos (0 ≤ a: α·(1 + b²) ≤ 1) / rem_atan_neg (b ≤ 0: α·(1 + a²) ≤ 1); the ends' brackets certified
        # (zatancert: atan a ≥ fa0, atan b ≤ fb1), the ends against ζ ± δ
        slope = alpha * (1 + b * b) <= 1 if a >= 0 else alpha * (1 + a * a) <= 1
        if not (slope and atan_cert(a)[0] >= fa[0] and atan_cert(b)[1] <= fb[1]
                and zeta - delta <= fa[0] - alpha * a and fb[1] - alpha * b <= zeta + delta):
            raise Uncovered("atan: the remainder's premises fail")
        out = nl(x, alpha, zeta, delta)
        k = ZA._atan(x)
        if (k.c, k.t, k.e) != (out.c, out.t, out.e):
            raise RuntimeError("FAULT: the replay of _atan lost the kernel")
        return out

    def ln(x):
        a, b = x.iv()
        if a <= 0:
            raise ZA.Unknown("ln reaching zero")
        f = lambda t: ZF.ln_pt_cert(F(t))
        df = lambda t: (1 / F(t), 1 / F(t))
        alpha, zeta, delta, a, b, fa, fb, inc = minrange(x, f, df, False, "b")
        # rem_ln: α ≥ 0, α·b ≤ 1, e^{fa0} ≤ a and e^{fb1} ≥ b certified (ExpCert), the ends against ζ ± δ
        if not (alpha >= 0 and alpha * b <= 1 and ZF._ln_side(a, F(fa[0]), "lo") and ZF._ln_side(b, F(fb[1]), "hi")
                and zeta - delta <= fa[0] - alpha * a and fb[1] - alpha * b <= zeta + delta):
            raise Uncovered("ln: the remainder's premises fail")
        out = nl(x, alpha, zeta, delta)
        k = ZA._ln(x)
        if (k.c, k.t, k.e) != (out.c, out.t, out.e):
            raise RuntimeError("FAULT: the replay of _ln lost the kernel")
        return out

    def ev(n):
        if isinstance(n, (int, F)):
            return ZA.Aff(F(n))
        if isinstance(n, str):
            return leaf(n)
        op, *args = n
        try:
            if op == "add":
                return ZA._add(ev(args[0]), ev(args[1]))
            if op == "sub":
                return ZA._add(ev(args[0]), ev(args[1]), -1)
            if op == "mul":
                return mul(ev(args[0]), ev(args[1]))
            if op == "div":
                return mul(ev(args[0]), recip(ev(args[1])))
            if op == "exp":
                return exp(ev(args[0]))
            if op == "ln":
                return ln(ev(args[0]))
            if op == "log10":
                l10 = ZF.LN10
                c10 = ZA.Aff((F(l10[0]) + F(l10[1])) / 2, {}, (F(l10[1]) - F(l10[0])) / 2)   # basis ln 10, widened
                return mul(ln(ev(args[0])), recip(c10))
            if op == "pow" and not (isinstance(args[1], (int, F)) and F(args[1]).denominator == 1):
                return exp(mul(ev(args[1]), ln(ev(args[0]))))
            if op == "atan":
                return atan(ev(args[0]))
            if op in ("sqrt", "pow"):
                # the kernel linearises these (or falls back to opaque on Unknown): replay its choice
                k = ZA.read(n, qs, piece, rat_sqrt, plain)
                if k is None:
                    raise ZA.Unknown(op)
                raise Uncovered(f"{op}: not in the Lean affine reading")
        except ZA.Unknown:
            pass
        return opaque(n)

    try:
        out = ev(e)
    except Uncovered as u:
        return None, str(u)
    except (ZA.Unknown, ZeroDivisionError, ZF.NoReadings, ValueError, OverflowError, TypeError) as ex:
        return None, f"no affine reading ({type(ex).__name__})"
    iv = out.iv()
    k = ZA.read(e, qs, piece, rat_sqrt, plain)
    if k is not None and tuple(k) != tuple(iv):
        raise RuntimeError(f"FAULT: the replay {iv} is not the kernel's affine reading {k}")
    return iv, ""


def lean_covered(f, qs, piece, r):
    """"" when the kernel's value reading r of f over the piece contains a reading Lean proves: the naive VRead, the
    checked affine one, or their meet (ZAffine.boxEv_meet); else why not."""
    import zcertify as ZC
    import ztaylorcert as T
    if r is None:
        return ""
    if ZC.CASES and ZC._branch_nodes(f, []):
        return "a branch read by cases (ZCases: its readings are premises)"
    q2 = dict(qs)
    for n_, (lo, hi) in piece.items():
        q2[n_] = dict(qs[n_], lo=lo, hi=hi)
    nv = T.lean_naive(f, qs, piece)
    av, why = (None, "affine off")
    if ZC.AFFINE:
        try:
            av, why = read_checked(f, qs, piece, ZC._rat_sqrt, lambda n: ZC._plain(n, q2), lambda n: T.lean_naive(n, qs, piece))
        except RecursionError:
            av, why = None, "too deep"
    cands = [iv for iv in (nv, av) if iv is not None]
    if not cands:
        return "no Lean reading"
    lo = max(iv[0] for iv in cands)
    hi = min(iv[1] for iv in cands)
    if r[0] <= lo and hi <= r[1]:
        return ""
    return "the kernel's reading is tighter than Lean's" + (f" ({why})" if why else "")
