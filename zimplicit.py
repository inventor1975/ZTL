# -*- coding: utf-8 -*-
"""
AN IMPLICIT LAW — a quantity fixed by g(q, p) = 0 that cannot be written as q == expression.

WHY (2026-10-10, the universal stand's blind test, gap G6): a fan's operating point is where its
curve meets the system's (p_max·(1 − Q/Q_max) = K·Q²); a pump's, where its head meets the line's.
The authors bounded those by hand.

THE DECISION OF 2026-10-09 HOLDS: the kernel does not search. The search (splitting q's range,
bracketing roots) lives outside and brings a CERTIFICATE; the kernel checks every statement in it
with its own readings (znum._ev, zfunc's brackets) and its own derivative (zcertify.derivative):

    {"search": [lo, hi],                       q is sought in this range only (the law's domain)
     "pieces": [{"lo", "hi", "kind": "none" | "kept"}, ...],   cover [lo, hi] in order, no gap
     "unique": true | false,                   dg/dq has one strict sign on every kept piece × the box
     "monotone": {param: "+" | "-"} | null,    dq*/dp: from -g_p / g_q, read on the kept hull × box
     "corners": [{"at": {param: value}, "lo", "hi"}, ...] | null}   a root bracketed at every corner

What the kernel concludes, and only from what it checked:
  * every root of g in [lo, hi], for every p in the box, lies in a KEPT piece (the "none" pieces are
    read to exclude 0) — the hull of the kept pieces ENCLOSES the solution set (always);
  * with "unique": each p has at most one root there (g strictly monotone in q on each kept piece,
    and the kept pieces' readings for each p ... the hull is one connected run of kept pieces);
  * with "monotone" and "corners": q*(p) is monotone in each parameter, so its range is spanned by
    the corner roots — each bracketed by a sign change the kernel reads at the bracket's ends —
    and the range is [min corner lo, max corner hi]: tight, not just enclosing.
Anything not proved falls back to the plain enclosure; nothing is assumed.
"""

from fractions import Fraction
import zcertify as ZC


def _reading(e, qs, piece):
    return ZC._reading(e, qs, piece)


def _sign(r):
    if r is None:
        return None
    if r[0] > 0:
        return 1
    if r[1] < 0:
        return -1
    return 0                                   # contains zero: no sign proved


def check_implicit(g, q, qs, cert):
    """(True, (lo, hi), how) — the range of q over the box — or (False, reason).
    g: the law as a reader node, lhs - rhs. qs: the quantities (q itself may be unbounded there)."""
    names = sorted(n for n in ZC._names(g) if n in qs and n != q and qs[n]["lo"] < qs[n]["hi"])
    for n in names:
        if isinstance(qs[n]["lo"], float) or isinstance(qs[n]["hi"], float):
            return False, f"{n} is unbounded"
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    try:
        slo, shi = (Fraction(str(x)) for x in cert["search"])
        pieces = [(Fraction(str(p["lo"])), Fraction(str(p["hi"])), p["kind"]) for p in cert["pieces"]]
    except (KeyError, ValueError, TypeError, ZeroDivisionError):
        return False, "certificate unreadable"
    if not pieces or slo >= shi:
        return False, "no pieces / an empty search range"
    # 1. THE COVER: pieces in order, from lo to hi, no gap, no overlap
    at = slo
    for a, b, kind in pieces:
        if a != at or b <= a or kind not in ("none", "kept"):
            return False, f"the pieces do not tile [{slo}, {shi}] at {at}"
        at = b
    if at != shi:
        return False, f"the pieces stop at {at}, not {shi}"
    # 2. EXCLUSION: on a "none" piece g's reading over the piece × the whole box excludes 0 — or, with a
    #    "split", every part of a partition of the box does (the kernel checks the partition tiles the box)
    splits = {(Fraction(str(p["lo"])), Fraction(str(p["hi"]))): p.get("split") for p in cert["pieces"]
              if isinstance(p, dict) and p.get("split") is not None}
    for a, b, kind in pieces:
        if kind == "none":
            if (a, b) in splits:
                if not _check_tree(g, q, qs, box, (a, b), splits[(a, b)]):
                    return False, f"q in [{a}, {b}] marked rootless by a partition the kernel does not accept"
                continue
            s = _sign(_reading(g, qs, dict(box, **{q: (a, b)})))
            if s in (None, 0):
                return False, f"q in [{a}, {b}] marked rootless, but g's reading there does not exclude 0"
    kept = [(a, b) for a, b, k in pieces if k == "kept"]
    if not kept:
        return True, None, "no root in the search range for any value of the box"
    hull = (min(a for a, _ in kept), max(b for _, b in kept))
    how = "enclosure: every root lies in the kept pieces (their hull)"
    # 3. UNIQUENESS: dg/dq one strict sign over the HULL × box -> g strictly monotone in q there
    if not cert.get("unique"):
        return True, hull, how
    try:
        dq = ZC.derivative(g, q)
    except ZC.NoDerivative as e:            # min/max in g (blind test 2, c11, 2026-10-10: it raised)
        return False, f"unique claimed, but dg/dq has no derivative: {e}"
    sq = _sign(_reading(dq, qs, dict(box, **{q: hull})))
    if sq in (None, 0):
        return False, "unique claimed, but dg/dq's reading over the hull × box does not keep one sign"
    how = "unique root (g strictly monotone in q over the hull); enclosure"
    # 4. MONOTONE ROOT: dq*/dp = -g_p / g_q has one sign per parameter over hull × box
    mono = cert.get("monotone")
    corners = cert.get("corners")
    if not mono or not corners:
        return True, hull, how
    signs = {}
    for n in names:
        try:
            dn = ZC.derivative(g, n)
        except ZC.NoDerivative as e:
            return False, f"monotone claimed, but dg/d{n} has no derivative: {e}"
        sp = _sign(_reading(dn, qs, dict(box, **{q: hull})))
        if sp is None:
            return False, f"monotone claimed, but dg/d{n} has no reading"
        dir_ = 0 if sp == 0 else -sp * sq          # sign of dq*/dn
        if sp == 0:
            r = _reading(dn, qs, dict(box, **{q: hull}))
            if r != (0, 0):
                return False, f"monotone claimed, but dg/d{n} changes sign over the hull × box"
        if mono.get(n) not in ("+", "-", "0") or {"+": 1, "-": -1, "0": 0}[mono[n]] != dir_:
            return False, f"monotone sign of {n} claimed {mono.get(n)!r}, read {dir_}"
        signs[n] = dir_
    # the corners the signs point to: the extremes of q*
    want = {}
    for side in ("min", "max"):
        corner = {}
        for n in names:
            lo_n, hi_n = box[n]
            up = (signs[n] > 0) == (side == "max")
            corner[n] = hi_n if (up and signs[n] != 0) else lo_n
        want[side] = corner
    got = {}
    for c in corners:
        try:
            point = {n: Fraction(str(v)) for n, v in c["at"].items()}
            a, b = Fraction(str(c["lo"])), Fraction(str(c["hi"]))
        except (KeyError, ValueError, TypeError, ZeroDivisionError):
            return False, "a corner bracket unreadable"
        for side, corner in want.items():
            if point == corner:
                got[side] = (a, b)
    if set(got) != {"min", "max"}:
        return False, "the corners the monotone signs point to are not both bracketed"
    for side, (a, b) in got.items():
        if not (hull[0] <= a <= b <= hull[1]):
            return False, f"the {side} corner's bracket leaves the hull"
        env = {n: (v, v) for n, v in want[side].items()}
        s1 = _sign(_reading(g, qs, dict(env, **{q: (a, a)})))
        s2 = _sign(_reading(g, qs, dict(env, **{q: (b, b)})))
        if a == b:
            if _reading(g, qs, dict(env, **{q: (a, a)})) != (0, 0):
                return False, f"the {side} corner's root point is not a root"
        elif s1 in (None, 0) or s2 in (None, 0) or s1 == s2:
            return False, f"the {side} corner's bracket shows no certain sign change"
    return True, (got["min"][0], got["max"][1]), \
        "unique root, monotone in every parameter: its range spans the corner roots (bracketed exactly)"


# ---------------------------------------------------------------- EXISTENCE: the root is BUILT
def _read_or_none(e, qs, piece):
    """A reading that RAISES (a function read outside its domain, e.g. tan beyond 1.5) is no reading: the
    existence check refuses on it and never raises on a brought certificate."""
    try:
        return _reading(e, qs, piece)
    except Exception:                                    # noqa: BLE001 — any failure to read proves nothing
        return None


def check_exists(g, q, qs, cert):
    """A ROOT IS BUILT for every value of the parameter box — the kernel's check of a brought certificate.

    WHY (2026-11-13). `check_implicit` proves an ENCLOSURE: every root lies in the kept pieces. It never said that a
    root is there, and a stand read the enclosure as the quantity's range: a law that jumps across zero, or has a
    pole there, with NO root was reported as an earned range around the jump. "The q such that g(q, p) = 0" is a
    definite description (ZTL v2.1.6, §25): it denotes only a satisfier that exists, and existence is earned.

    THE RULE is the one already proved in Lean with zero axioms, `lean/ZRootPar.lean` — `chkP` / `par_root` for one
    box, `chkT` / `tree_root` for a cover: on a bracket [qa, qb] of the unknown,
      * the law reads strictly negative at one end and strictly positive at the other, over the whole part;
      * its slope in the unknown keeps ONE STRICT SIGN over the bracket x the part (so it is bounded away from zero
        there, and bounded above: the reading is finite) — the root is unique in the bracket;
      * its slope in every parameter of the box has a finite reading (the Lipschitz bound `par_root` asks);
    then for every value of the part the root exists in [qa, qb] and is the only one. A wide box is COVERED by a
    tree of cuts whose two parts OVERLAP (a real parameter is placed in a part by cotransitivity, not by a
    decision — `tree_root`): a cut with no overlap is refused.

    This is the OPERATIONAL ground. A sign change with the law merely continuous (the classical intermediate value
    theorem) builds nothing and is not accepted here.

        {"search": [lo, hi],
         "exists": {"leaf": true, "qa": "...", "qb": "..."}
                 | {"param": name, "at": "...", "overlap": "...", "parts": [tree, tree]}}

    -> (True, number of leaves, how) | (False, reason). The kernel reads everything itself (zcertify._reading,
    zcertify.derivative); the search that proposed the tree is outside (`search_exists`)."""
    names = sorted(n for n in ZC._names(g) if n in qs and n != q and qs[n]["lo"] < qs[n]["hi"])
    for n in names:
        if isinstance(qs[n]["lo"], float) or isinstance(qs[n]["hi"], float):
            return False, f"{n} is unbounded"
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    try:
        slo, shi = (Fraction(str(x)) for x in cert["search"])
        tree = cert["exists"]
    except (KeyError, ValueError, TypeError, ZeroDivisionError):
        return False, "certificate unreadable"
    try:
        dq = ZC.derivative(g, q)
        dps = {n: ZC.derivative(g, n) for n in names}
    except ZC.NoDerivative as e:
        return False, f"the law's slope has no derivative here: {e}"
    leaves = [0]

    def leaf(part, t):
        try:
            qa, qb = Fraction(str(t["qa"])), Fraction(str(t["qb"]))
        except (KeyError, ValueError, TypeError, ZeroDivisionError):
            return "a leaf's bracket is unreadable"
        if not (slo <= qa < qb <= shi):
            return f"the bracket [{qa}, {qb}] is not inside the search range"
        s1 = _sign(_read_or_none(g, qs, dict(part, **{q: (qa, qa)})))
        s2 = _sign(_read_or_none(g, qs, dict(part, **{q: (qb, qb)})))
        if s1 not in (1, -1) or s2 not in (1, -1) or s1 == s2:
            return f"no strict sign change of the law across [{qa}, {qb}] over the part"
        sd = _sign(_read_or_none(dq, qs, dict(part, **{q: (qa, qb)})))
        if sd not in (1, -1):
            return f"the slope in {q} does not keep one strict sign over [{qa}, {qb}] x the part"
        if sd != s2:
            return "the slope's sign disagrees with the signs at the bracket's ends"
        for n, dn in dps.items():
            if _read_or_none(dn, qs, dict(part, **{q: (qa, qb)})) is None:
                return f"the slope in the parameter {n} has no reading over the bracket x the part"
        leaves[0] += 1
        return None

    def walk(part, t, depth):
        if depth > 200 or not isinstance(t, dict):
            return "the tree is unreadable or too deep"
        if t.get("leaf") is True:
            return leaf(part, t)
        try:
            v, at, ov, parts = t["param"], Fraction(str(t["at"])), Fraction(str(t["overlap"])), t["parts"]
        except (KeyError, ValueError, TypeError, ZeroDivisionError):
            return "a cut is unreadable"
        if v not in part or not isinstance(parts, list) or len(parts) != 2:
            return "a cut names no parameter of the part, or has not two parts"
        lo, hi = part[v]
        if not ov > 0:
            return f"a cut of {v} with no overlap: a real parameter is not decided to one side"
        if not (lo < at - ov and at + ov < hi):
            return f"a cut of {v} (with its overlap) is not strictly inside the part"
        return (walk(dict(part, **{v: (lo, at + ov)}), parts[0], depth + 1)
                or walk(dict(part, **{v: (at - ov, hi)}), parts[1], depth + 1))

    why = walk(box, tree, 0)
    if why:
        return False, why
    where = "over the whole box" if leaves[0] == 1 else f"on each of {leaves[0]} overlapping parts that cover the box"
    return True, leaves[0], ("a root is BUILT for every value of the box: a strict sign change with the slope in "
                             f"{q} bounded away from zero, {where} "
                             "(the rule of lean/ZRootPar par_root / tree_root)")


def search_exists(g, q, qs, search, hull, budget=600):
    """The SEARCH for an existence certificate (outside the check; the kernel checks whatever it brings). Per part of
    the box: the root at the part's middle is located by bisection on the signs the reading gives at points, the
    bracket around it is widened until the law keeps a strict sign at each end over the whole part, and the slope
    is read once; a part where that fails is cut in two OVERLAPPING halves along its widest parameter.
    -> the certificate {"search", "exists"} or None."""
    try:
        dq = ZC.derivative(g, q)
    except ZC.NoDerivative:
        return None
    names = sorted(n for n in ZC._names(g) if n in qs and n != q and qs[n]["lo"] < qs[n]["hi"])
    if any(isinstance(qs[n]["lo"], float) or isinstance(qs[n]["hi"], float) for n in names):
        return None
    whole = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    slo, shi = (Fraction(str(x)) for x in search)
    hlo, hhi = (Fraction(str(x)) for x in hull)
    w, span = hhi - hlo, shi - slo
    outs = [w / 8, w / 2, 2 * w, span / 1024, span / 64, span / 8, span]
    cands = sorted({hlo, hhi} | {max(slo, hlo - d) for d in outs} | {min(shi, hhi + d) for d in outs}
                   | {hlo + w * Fraction(k, 4) for k in (1, 2, 3)})
    left = [budget]

    def sg(x, part):
        return _sign(_read_or_none(g, qs, dict(part, **{q: (x, x)})))

    def bracket(part):
        mid = {n: ((lo + hi) / 2,) * 2 for n, (lo, hi) in part.items()}
        pts = [(x, sg(x, mid)) for x in cands]
        pts = [(x, s) for x, s in pts if s in (1, -1)]
        pairs = sorted((pts[i + 1][0] - pts[i][0], i) for i in range(len(pts) - 1) if pts[i][1] != pts[i + 1][1])
        if not pairs:
            return None
        (a, sa), (b, _sb) = pts[pairs[0][1]], pts[pairs[0][1] + 1]
        d = max(w, span / 2 ** 20) / 2 ** 12
        for _ in range(40):
            if b - a <= d:
                break
            m = (a + b) / 2
            sm = sg(m, mid)
            if sm not in (1, -1):
                break
            if sm == sa:
                a = m
            else:
                b = m
        while True:
            qa, qb = max(slo, a - d), min(shi, b + d)
            s1, s2 = sg(qa, part), sg(qb, part)
            if s1 in (1, -1) and s2 in (1, -1) and s1 != s2:
                return qa, qb
            if qa == slo and qb == shi:
                return None
            d *= 2

    def build(part):
        left[0] -= 1
        if left[0] < 0:
            return None
        br = bracket(part)
        if br is not None and _sign(_read_or_none(dq, qs, dict(part, **{q: br}))) in (1, -1):
            return {"leaf": True, "qa": str(br[0]), "qb": str(br[1])}
        if not part:
            return None
        v = max(part, key=lambda n: (part[n][1] - part[n][0]) / (whole[n][1] - whole[n][0]))
        lo, hi = part[v]
        if (hi - lo) * 2 ** 40 < whole[v][1] - whole[v][0]:
            return None
        at, ov = (lo + hi) / 2, (hi - lo) / 64
        left_t = build(dict(part, **{v: (lo, at + ov)}))
        if left_t is None:
            return None
        right_t = build(dict(part, **{v: (at - ov, hi)}))
        if right_t is None:
            return None
        return {"param": v, "at": str(at), "overlap": str(ov), "parts": [left_t, right_t]}

    tree = build(dict(whole))
    return None if tree is None else {"search": [str(slo), str(shi)], "exists": tree}


# ---------------------------------------------------------------- the SEARCH (outside the check)
def _split_tree(g, q, qs, whole, box, piece, budget):
    """A partition of the parameter box on which every part's reading excludes a root for q in piece —
    or None. Halves the parameter widest relative to the whole box. budget: [readings left]."""
    budget[0] -= 1
    if budget[0] < 0:
        return None
    if _sign(_reading(g, qs, dict(box, **{q: piece}))) in (1, -1):
        return {"leaf": True}
    v = max(box, key=lambda n: (box[n][1] - box[n][0]) / (whole[n][1] - whole[n][0]))
    m = (box[v][0] + box[v][1]) / 2
    left = _split_tree(g, q, qs, whole, dict(box, **{v: (box[v][0], m)}), piece, budget)
    if left is None:
        return None
    right = _split_tree(g, q, qs, whole, dict(box, **{v: (m, box[v][1])}), piece, budget)
    if right is None:
        return None
    return {"param": v, "at": str(m), "parts": [left, right]}


def _check_tree(g, q, qs, box, piece, tree, depth=0):
    """The KERNEL's check of a partition: it tiles the box (each cut strictly inside its part), and every
    leaf's own reading excludes 0 for q in piece."""
    if depth > 200 or not isinstance(tree, dict):
        return False
    if tree.get("leaf") is True and len(tree) == 1:
        return _sign(_reading(g, qs, dict(box, **{q: piece}))) in (1, -1)
    try:
        v, at, parts = tree["param"], Fraction(str(tree["at"])), tree["parts"]
    except (KeyError, ValueError, TypeError, ZeroDivisionError):
        return False
    if v not in box or not (box[v][0] < at < box[v][1]) or not isinstance(parts, list) or len(parts) != 2:
        return False
    return (_check_tree(g, q, qs, dict(box, **{v: (box[v][0], at)}), piece, parts[0], depth + 1) and
            _check_tree(g, q, qs, dict(box, **{v: (at, box[v][1])}), piece, parts[1], depth + 1))


def search_certificate(g, q, qs, search, depth=40, max_pieces=4000, bracket_steps=200, split_budget=0,
                       goal=None, goal_budget=3000, tighten=0, tighten_budget=400):
    """goal = (lo, hi), either end None: the range a requirement asks of q. When the plain enclosure leaves
    it, ONE partition of the parameter box is searched to exclude every root beyond the goal (2026-10-10,
    blind test 2, the oil cooler: Tho <= 62 C needed; the plain hull was 72.7, the partition gives 60.4)."""
    cert = _search_plain(g, q, qs, search, depth, max_pieces, bracket_steps, split_budget)
    if cert is None:
        return cert
    if tighten and not cert.get("corners"):
        # no tight corners: pull each edge of the hull inward by bisection, each step ONE partition attempt
        kept = [(Fraction(p["lo"]), Fraction(p["hi"])) for p in cert["pieces"] if p["kind"] == "kept"]
        if kept:
            lo_e, hi_e = kept[0][0], kept[-1][1]
            glo = goal[0] if goal and goal[0] is not None else None
            ghi = goal[1] if goal and goal[1] is not None else None
            names_t = sorted(n for n in ZC._names(g) if n in qs and n != q and qs[n]["lo"] < qs[n]["hi"])
            box_t = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names_t}
            if names_t:
                best_hi, a, b = hi_e, lo_e + (hi_e - lo_e) / 2, hi_e
                for _ in range(tighten):            # largest excluded [x, hi_e]: x as low as possible
                    m = (a + b) / 2
                    if _split_tree(g, q, qs, box_t, box_t, (m, hi_e), [tighten_budget]) is not None:
                        best_hi, b = m, m
                    else:
                        a = m
                best_lo, a, b = lo_e, lo_e, lo_e + (hi_e - lo_e) / 2
                for _ in range(tighten):
                    m = (a + b) / 2
                    if _split_tree(g, q, qs, box_t, box_t, (lo_e, m), [tighten_budget]) is not None:
                        best_lo, a = m, m
                    else:
                        b = m
                ghi = best_hi if ghi is None else min(Fraction(str(ghi)), best_hi) if best_hi < hi_e else ghi
                glo = best_lo if glo is None else max(Fraction(str(glo)), best_lo) if best_lo > lo_e else glo
                goal = (glo if (glo is not None and glo > lo_e) else None, ghi if (ghi is not None and ghi < hi_e) else None)
    if not goal or (goal[0] is None and goal[1] is None):
        return cert
    names = sorted(n for n in ZC._names(g) if n in qs and n != q and qs[n]["lo"] < qs[n]["hi"])
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    if not names:
        return cert
    pieces = [(Fraction(p["lo"]), Fraction(p["hi"]), p["kind"], p.get("split")) for p in cert["pieces"]]
    changed, made = False, []
    for side in ("hi", "lo"):
        cut = goal[1] if side == "hi" else goal[0]
        if cut is None:
            continue
        cut = Fraction(str(cut))
        kept = [(a, b) for a, b, k, _ in pieces if k == "kept"]
        if not kept:
            break
        edge = kept[-1][1] if side == "hi" else kept[0][0]
        if (side == "hi" and edge <= cut) or (side == "lo" and edge >= cut):
            continue
        span = (cut, edge) if side == "hi" else (edge, cut)
        t = _split_tree(g, q, qs, box, box, span, [goal_budget])
        if t is None:
            continue
        made.append(t)
        # re-tile: everything beyond the cut becomes ONE rootless piece carrying the partition
        new = []
        for a, b, k, tr in pieces:
            if side == "hi":
                if b <= cut:
                    new.append((a, b, k, tr))
                elif a < cut:
                    new.append((a, cut, k, tr if k == "none" else None))
            else:
                if a >= cut:
                    new.append((a, b, k, tr))
                elif b > cut:
                    new.append((cut, b, k, tr if k == "none" else None))
        if side == "hi":
            new.append((cut, edge, "none", t))
            new += [(a, b, k, tr) for a, b, k, tr in pieces if a >= edge]
        else:
            new = [(a, b, k, tr) for a, b, k, tr in pieces if b <= edge] + [(edge, cut, "none", t)] + new
        # every rootless piece must still be one: a partition is kept only on its own span; a cut piece
        # without one is read again plainly, and one that no longer reads rootless becomes kept (sound)
        pieces = []
        for a, b, k, tr in new:
            if k == "none" and tr is not None and not any(tr is x for x in made):
                tr = None
            if k == "none" and tr is None and _sign(_reading(g, qs, dict(box, **{q: (a, b)}))) not in (1, -1):
                k = "kept"
            pieces.append((a, b, k, tr))
        changed = True
    if not changed:
        return cert
    return {"search": cert["search"],
            "pieces": [dict({"lo": str(a), "hi": str(b), "kind": k}, **({"split": tr} if k == "none" and tr else {}))
                       for a, b, k, tr in pieces]}


def _search_plain(g, q, qs, search, depth, max_pieces, bracket_steps, split_budget):
    """A certificate for check_implicit, found by bisection. The kernel does not trust it."""
    names = sorted(n for n in ZC._names(g) if n in qs and n != q and qs[n]["lo"] < qs[n]["hi"])
    box = {n: (qs[n]["lo"], qs[n]["hi"]) for n in names}
    lo, hi = (Fraction(str(x)) for x in search)

    trees = {}
    seen = {}          # (a, b) -> its kind: a reading is a function of the piece alone (g, qs and the box are
    #                    fixed here), and the level loop below asks the SAME pair of ruled-out neighbours again
    #                    at every level ("do they merge now?" - no, as one level before). MEASURED 2026-11-14,
    #                    a cooling tower's outlet at one point: 1348 readings for a certificate of 48 pieces.

    def kind(a, b):
        if (a, b) not in seen:
            seen[(a, b)] = _kind(a, b)
        return seen[(a, b)]

    def _kind(a, b):
        if _sign(_reading(g, qs, dict(box, **{q: (a, b)}))) in (1, -1):
            return "none"
        if split_budget and names:
            # the whole box does not exclude a root here: try a PARTITION of the parameter box (2026-10-10,
            # blind test 2, the oil cooler: with the affine reading, 85 parts exclude what 4000 plain could not)
            t = _split_tree(g, q, qs, box, box, (a, b), [split_budget])
            if t is not None:
                trees[(a, b)] = t
                return "none"
        return "kept"

    # level by level; only a kept piece at the EDGE of a kept run is split again (an interior one
    # holds roots for some p anyway — a box of parameters sweeps the root over a whole interval,
    # and splitting it all the way down cost 2^depth pieces, MEASURED 2026-10-10 on the fan)
    pieces = [(lo, hi, kind(lo, hi))]
    for _ in range(depth):
        out, changed = [], False
        for i, (a, b, k) in enumerate(pieces):
            edge = k == "kept" and (i == 0 or pieces[i - 1][2] == "none" or
                                    i == len(pieces) - 1 or pieces[i + 1][2] == "none")
            if not edge:
                out.append((a, b, k))
                continue
            m = (a + b) / 2
            out += [(a, m, kind(a, m)), (m, b, kind(m, b))]
            changed = True
        pieces = []                                     # adjacent RULED-OUT pieces merged when
        for a, b, k in out:                             # the union still reads rootless (a wider
            if pieces and k == "none" and pieces[-1][2] == "none" \
                    and kind(pieces[-1][0], b) == "none":   # piece reads wider); kept ones stay
                pieces[-1] = (pieces[-1][0], b, k)          # split, or the edge never sharpens
            else:
                pieces.append((a, b, k))
        if not changed or len(pieces) > max_pieces:
            break
    merged = []
    for a, b, k in pieces:
        if merged and merged[-1][2] == k and (k == "kept" or kind(merged[-1][0], b) == "none"):
            merged[-1] = (merged[-1][0], b, k)
        else:
            merged.append((a, b, k))
    cert = {"search": [str(lo), str(hi)],
            "pieces": [dict({"lo": str(a), "hi": str(b), "kind": k},
                            **({"split": trees[(a, b)]} if k == "none" and (a, b) in trees else {}))
                       for a, b, k in merged]}
    kept = [(a, b) for a, b, k in merged if k == "kept"]
    if not kept:
        return cert
    hull = (kept[0][0], kept[-1][1])
    try:
        sq = _sign(_reading(ZC.derivative(g, q), qs, dict(box, **{q: hull})))
    except ZC.NoDerivative:
        return cert                                    # min/max in g: the plain enclosure only
    if sq in (None, 0):
        return cert
    cert["unique"] = True
    mono = {}
    for n in names:
        try:
            r = _reading(ZC.derivative(g, n), qs, dict(box, **{q: hull}))
        except ZC.NoDerivative:
            return cert
        sp = _sign(r)
        if sp is None or (sp == 0 and r != (0, 0)):
            return cert
        mono[n] = {1: "+", -1: "-", 0: "0"}[0 if sp == 0 else -sp * sq]
    cert["monotone"] = mono
    corners = []
    at_point = {}      # (the corner, x) -> the sign read there: with no parameter of positive width (a law at
    #                    one point) the two corners are the same point and the second bracket is the first

    def sign_at(corner, env, x):
        key = (tuple(sorted(corner.items())), x)
        if key not in at_point:
            at_point[key] = _sign(_reading(g, qs, dict(env, **{q: (x, x)})))
        return at_point[key]

    for side in ("min", "max"):
        corner = {}
        for n in names:
            d_ = {"+": 1, "-": -1, "0": 0}[mono[n]]
            up = (d_ > 0) == (side == "max")
            corner[n] = box[n][1] if (up and d_ != 0) else box[n][0]
        env = {n: (v, v) for n, v in corner.items()}
        a, b = hull
        sa = sign_at(corner, env, a)
        sb = sign_at(corner, env, b)
        if sa in (None, 0) or sb in (None, 0) or sa == sb:
            return cert                                # the root may sit on the hull's edge: no bracket
        for _ in range(bracket_steps):
            m = (a + b) / 2
            sm = sign_at(corner, env, m)
            if sm in (None, 0):
                break
            if sm == sa:
                a = m
            else:
                b = m
            if b - a < (hull[1] - hull[0]) / 2 ** 60:
                break
        corners.append({"at": {n: str(v) for n, v in corner.items()}, "lo": str(a), "hi": str(b)})
    cert["corners"] = corners
    return cert
