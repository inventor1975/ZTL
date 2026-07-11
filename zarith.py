# -*- coding: utf-8 -*-
"""
Expedition E8: arithmetic with marks.

Numbers: verified ('V', n) and marks ('M', id, lo, hi) — unverified
with an interval of partial knowledge (None = unbounded). Operations
are computations ⇒ lazy: intervals FLOW (interval arithmetic,
decorrelated — each occurrence of a mark reads independently).
Comparison atoms follow the generating principle: T if forced under
all readings; F if falsehood is forced; else Z.

Twin #4: abstract interpretation (Cousot & Cousot 1977) — interval
value analysis + assertion checking.
"""

from ztl import T, F, Z, OPS2

AND, OR, IMP = OPS2["and"], OPS2["or"], OPS2["imp"]

NEG_INF, POS_INF = float("-inf"), float("inf")


def V_(n):
    return ("V", n, n, n)


def M_(ident, lo=None, hi=None):
    return ("M", ident,
            NEG_INF if lo is None else lo,
            POS_INF if hi is None else hi)


def bounds(x):
    return x[2], x[3]


def is_verified(x):
    return x[0] == "V"


def name(x):
    if is_verified(x):
        return str(x[1])
    lo, hi = bounds(x)
    rng = "" if (lo, hi) == (NEG_INF, POS_INF) else f"∈[{lo},{hi}]"
    return f"{x[1]}{rng}"


# --- operations: intervals flow (lazily), the pedigree grows ---
def add(x, y):
    lo, hi = x[2] + y[2], x[3] + y[3]
    if is_verified(x) and is_verified(y):
        return V_(x[1] + y[1])
    return ("M", f"({name(x)}+{name(y)})", lo, hi)


def sub_(x, y):
    lo, hi = x[2] - y[3], x[3] - y[2]      # decorrelation!
    if is_verified(x) and is_verified(y):
        return V_(x[1] - y[1])
    if lo == hi:                            # a forced value — earned
        return V_(lo)
    return ("M", f"({name(x)}-{name(y)})", lo, hi)


def mul(x, y):
    # over ℤ: 0·x = 0 always (including unbounded marks)
    cands = [0 if (a == 0 or b == 0) else a * b
             for a in (x[2], x[3]) for b in (y[2], y[3])]
    lo, hi = min(cands), max(cands)
    if is_verified(x) and is_verified(y):
        return V_(x[1] * y[1])
    if lo == hi:                            # forced (e.g. 0·m)
        return V_(int(lo))
    return ("M", f"({name(x)}·{name(y)})", lo, hi)


# --- comparison atoms: the generating principle on intervals ---
def lt_atom(x, y):
    if x[3] < y[2]:
        return T                            # forced under all readings
    if x[2] >= y[3]:
        return F                            # falsehood forced
    return Z


def eq_atom(x, y):
    if is_verified(x) and is_verified(y):
        return T if x[1] == y[1] else F
    if x[3] < y[2] or y[3] < x[2]:
        return F                            # apartness EARNED by intervals
    return Z


if __name__ == "__main__":
    print("=" * 72)
    print("E8. ARITHMETIC WITH MARKS (intervals flow, verdicts are earned)")
    print("=" * 72)

    m = M_("m", 0, 9)         # a sensor, partially verified: [0,9]
    w = M_("w")               # a wild mark, nothing known
    five = V_(5)
    zero = V_(0)

    print("\n### Interval flow (the lazy register)")
    s1 = add(five, m)
    print(f"  5 + m∈[0,9] = {name(s1)}")
    s2 = add(five, w)
    print(f"  5 + w(∅ information) = {name(s2)} — bare NaN mode")

    print("\n### Forcedness earns even on marks")
    p = mul(zero, w)
    print(f"  0 · w = {name(p)}  ← an EARNED zero (forced under all")
    print("  readings; IEEE answers NaN here — their domain has inf/nan, ours is ℤ)")
    d = sub_(m, m)
    print(f"  m − m = {name(d)} — NOT zero: decorrelation (two independent")
    print("  readings of one mark; exactly like NaN−NaN and like {Z,Z}≠{Z})")

    print("\n### Comparison atoms: three fates (T earned / F earned / Z)")
    a, b = M_("a", 3, 5), M_("b", 10, 12)
    print(f"  a∈[3,5] < b∈[10,12]: {lt_atom(a, b)} — earned (separated)")
    print(f"  a∈[3,5] = b∈[10,12]: {eq_atom(a, b)} — apartness earned!")
    c = M_("c", 4, 6)
    print(f"  a∈[3,5] < c∈[4,6]: {lt_atom(a, c)} — not forced (overlap)")
    print(f"  a∈[3,5] = a∈[3,5] (the same mark): {eq_atom(a, a)} — identity")
    print("  is not earned by intervals (coinciding bounds ≠ coincidence)")

    print("\n### Verification = interval narrowing: verdicts are earned")
    four = V_(4)
    for lo, hi in [(0, 9), (3, 7), (5, 7), (5, 5)]:
        mm = M_("m", lo, hi)
        atom = lt_atom(four, mm)   # "4 < m"
        note = {T: "T earned", F: "falsehood earned", Z: "not yet forced"}[atom]
        print(f"  m∈[{lo},{hi}]:  atom \"4 < m\" = {atom}  ({note})")
    print("  Narrowing never revokes what is earned — the monotonicity of")
    print("  the lazy register, now in numbers.")

    print("\n### Laws: price-list inheritance")
    x, y = M_("x", 1, 3), M_("y", 2, 4)
    lhs, rhs = add(x, y), add(y, x)
    print(f"  x+y = {name(lhs)};  y+x = {name(rhs)}")
    print(f"  commutativity: intervals coincided ({bounds(lhs) == bounds(rhs)}),")
    print(f"  verdict eq(x+y, y+x): {eq_atom(lhs, rhs)} — two levels, again")
    xz = add(x, zero)
    print(f"  x+0 = {name(xz)}: the interval is the same ({bounds(xz) == bounds(x)}),")
    print(f"  verdict eq(x+0, x): {eq_atom(xz, x)} — the unit fell verdict-wise")

    print("\n### Summary")
    print("  ZTL arithmetic = interval arithmetic (the solver) + verdicts of")
    print("  the generating principle (customs). All inherited, nothing")
    print("  postulated. Twin #4 — abstract interpretation (Cousot): interval")
    print("  value analysis + assertion checking = our lazy register + greedy")
    print("  verdicts. Addendum to E6: apartness of numbers is earned by")
    print("  intervals — as apartness of reals by prefixes; identity is earned")
    print("  by nothing short of full verification ([x,x] — the mark becomes a value).")
