# -*- coding: utf-8 -*-
"""
znum._real_roots (Sturm) ↔ lean/ZNone.lean — "no root outside the brackets", proved by the kernel per instance
(2026-11-27, the curator's audit «каждая деталь судьи — теорема»).

The solver narrows an unknown under a polynomial equation of degree ≥ 3 to the root brackets Sturm isolates
(`znumsolve._upoly_roots` → `znum._real_roots`); "no bracket" is a refutation. Soundness = NO ROOT IN ANY GAP between
the brackets. Sturm's theorem is not proved here; each instance is: every closed gap gets a certificate for
`ZNone.chk` — a bisection with overlapping halves (`split i t δ`, the constructive cut) whose leaves are interval
readings of the polynomial (Horner, `ZIv`/`ZXE`) that exclude 0 — and the kernel checks it by `decide`.
`ZNone.chk_sound` (zero axioms) then says: no point of the gap, in every constructive ordered field, is a root.

Battery: seeded integer polynomials of degree 3..5 on dyadic boxes inside [−1, 1] (there the Cauchy bound does not
cut the box, so the bisection points are dyadic). RATIONAL roots (dyadic, multiplicity 1–2): the identity
p = Π (x − r)^m · q is checked by the kernel (`ZNone.identX`) and q's gaps are certified — so a root of p in a closed
gap can only be one of the r — `lean/ZRootFactor.lean` `root_factor` (zero axioms): p ≈ a^m·q, p ≈ 0, q never 0
there ⇒ a ≈ 0, constructively in every CF.
MUTATION: one bracket merged into its gap (the gap now contains a root): the searcher finds no certificate, and a
forged `nz` leaf is REFUSED by the kernel.

Run:  python3 inventory/zsturm_lean_bridge.py   -> ZSTURM LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import znum                            # noqa: E402

LEAN = os.path.join(ROOT, "lean")


def is_dyadic(q):
    q = Fr(q)
    return q.denominator & (q.denominator - 1) == 0


def dlit(q):
    q = Fr(q)
    e = q.denominator.bit_length() - 1
    m = q.numerator
    p, n = (m, 0) if m >= 0 else (0, -m)
    return f"(⟨⟨{p}, {n}⟩, {e}⟩ : D)"


def horner_xe(coeffs):
    """coeffs a0..an (a0 constant): a0 + x(a1 + x(a2 + …))"""
    acc = f"(.cst {dlit(coeffs[-1])})"
    for c in reversed(coeffs[:-1]):
        acc = f"(.add (.cst {dlit(c)}) (.mul (.var 0) {acc}))"
    return acc


def horner_pe(coeffs):
    acc = f"(.cst {dlit(coeffs[-1])})"
    for c in reversed(coeffs[:-1]):
        acc = f"(.add (.cst {dlit(c)}) (.mul (.var 0) {acc}))"
    return acc


def factored_pe(roots, q):
    """Π (x − r)^m · q, as a PE"""
    acc = horner_pe(q)
    for r, m in roots:
        acc = f"(.mul (.pow (.sub (.var 0) (.cst {dlit(r)})) {m}) {acc})"
    return acc


def divide_out(coeffs, r):
    m, cur = 0, list(coeffs)
    while True:
        qq, rem = znum._pdivmod(cur, [-r, Fr(1)])
        if any(rem):
            return m, cur
        m, cur = m + 1, list(qq)


def iv_horner(coeffs, l, h):
    lo = hi = Fr(coeffs[-1])
    for c in reversed(coeffs[:-1]):
        ps = (lo * l, lo * h, hi * l, hi * h)
        lo, hi = min(ps) + c, max(ps) + c
    return lo, hi


def search(coeffs, l, h, depth=0):
    lo, hi = iv_horner(coeffs, l, h)
    margin = Fr(1, 1 << 100) * (1 + abs(lo) + abs(hi))
    if lo > margin or hi < -margin:
        return ".nz 0"
    if depth > 120:
        return None
    t = (l + h) / 2
    d = (h - l) / (1 << 12)
    a = search(coeffs, l, t + d, depth + 1)
    if a is None:
        return None
    b = search(coeffs, t - d, h, depth + 1)
    if b is None:
        return None
    return f"(.split 0 {dlit(t)} {dlit(d)} ({a}) ({b}))"


def gaps(pieces, L, H):
    out, cur = [], L
    for l, h in sorted(pieces):
        if cur < l:
            out.append((cur, l))
        cur = max(cur, h)
    if cur < H:
        out.append((cur, H))
    return out


def main():
    rnd = random.Random(20261127)
    boxes = [(Fr(-1), Fr(1)), (Fr(-1, 2), Fr(1)), (Fr(0), Fr(1)), (Fr(-1), Fr(3, 4)), (Fr(-3, 4), Fr(5, 8))]
    jobs, skipped_rational, no_root, with_roots = [], 0, 0, 0
    while len(jobs) < 60:
        deg = rnd.randint(3, 5)
        coeffs = [Fr(rnd.randint(-9, 9)) for _ in range(deg)] + [Fr(rnd.choice([c for c in range(-9, 10) if c != 0]))]
        L, H = rnd.choice(boxes)
        pieces = znum._real_roots(coeffs, L, H)
        if any(l == h for l, h in pieces) or not all(is_dyadic(x) for p in pieces for x in p):
            skipped_rational += 1
            continue
        gs = gaps(pieces, L, H)
        certs = [search(coeffs, a, b) for a, b in gs]
        if any(c is None for c in certs):
            print("  NO CERTIFICATE FOUND for a gap of", coeffs, (L, H), pieces); sys.exit(1)
        jobs.append((coeffs, L, H, pieces, gs, certs))
        no_root += not pieces
        with_roots += bool(pieces)
    # RATIONAL ROOTS: the code divides them out exactly; here p = Π (x − r)^m · q is an identity the kernel checks
    # (`identX`), and every gap — closed, its end may BE r — is certified root-free for q.
    rjobs = []
    rnd2 = random.Random(20261128)
    while len(rjobs) < 15:
        r0 = Fr(rnd2.randint(-7, 7), rnd2.choice([1, 2, 4, 8]))
        if not (-1 <= r0 <= 1):
            continue
        base = [Fr(rnd2.randint(-9, 9)) for _ in range(rnd2.randint(2, 4))] + [Fr(rnd2.choice([1, 2, 3, -1, -2]))]
        mult = rnd2.randint(1, 2)
        # (x − r0)^mult · base, computed by convolution
        poly = list(base)
        for _ in range(mult):
            poly = [(-r0) * poly[0]] + [poly[i - 1] - r0 * poly[i] for i in range(1, len(poly))] + [poly[-1]]
        L, H = Fr(-1), Fr(1)
        pieces = znum._real_roots(poly, L, H)
        exact = [l for l, h in pieces if l == h]
        if not all(is_dyadic(x) for pc in pieces for x in pc) or not exact:
            continue
        q, roots = list(poly), []
        for r in exact:
            m, q = divide_out(q, r)
            roots.append((r, m))
        gs = gaps(pieces, L, H)
        certs = [search(q, a, b) for a, b in gs]
        if any(c is None for c in certs):
            continue
        rjobs.append((poly, q, roots, L, H, pieces, gs, certs))
    # the mutation: the first job with a bracket, the bracket merged into the gap before it
    mut = next(j for j in jobs if j[3])
    coeffs, L, H, pieces, gs, certs = mut
    l0, h0 = sorted(pieces)[0]
    fake_gap = (L, h0)                                  # contains the root in (l0, h0]
    mut_search = search(coeffs, *fake_gap)
    lines = ["import ZNone", "open ZNumBin ZIv ZXE ZNone", "set_option maxRecDepth 4000000", "set_option maxHeartbeats 0", "set_option exponentiation.threshold 4096", ""]
    n_thm = 0
    for k, (coeffs, L, H, pieces, gs, certs) in enumerate(jobs):
        lines.append(f"def s{k} : Sys := ⟨[{horner_xe(coeffs)}], []⟩")
        for g, ((a, b), c) in enumerate(zip(gs, certs)):
            lines.append(f"theorem gap_{k}_{g} : chk s{k} (fun i => if i = 0 then some ({dlit(a)}, {dlit(b)}) else none) "
                         f"({c}) = true := by decide +kernel")
            n_thm += 1
    n_rthm = 0
    for k, (poly, q, roots, L, H, pieces, gs, certs) in enumerate(rjobs):
        lines.append(f"def rq{k} : Sys := ⟨[{horner_xe(q)}], []⟩")
        lines.append(f"theorem rid_{k} : identX {horner_pe(poly)} {factored_pe(roots, q)} = true := by decide +kernel")
        n_rthm += 1
        for g, ((a, b), c) in enumerate(zip(gs, certs)):
            lines.append(f"theorem rgap_{k}_{g} : chk rq{k} (fun i => if i = 0 then some ({dlit(a)}, {dlit(b)}) else none) "
                         f"({c}) = true := by decide +kernel")
            n_rthm += 1
    lines.append("#print axioms gap_0_0")
    k0 = jobs.index(mut)
    lines.append(f'#eval IO.println s!"FORGED {{chk s{k0} (fun i => if i = 0 then some ({dlit(fake_gap[0])}, '
                 f'{dlit(fake_gap[1])}) else none) (.nz 0)}}"')
    fd, path = tempfile.mkstemp(prefix="zsturm_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["bash", "-c", f"ulimit -s unlimited; lake env lean --tstack=400000 {path}"], cwd=LEAN, capture_output=True, text=True, timeout=3000)
    finally:
        os.unlink(path)
    ok = r.returncode == 0 and "error" not in r.stdout and "'gap_0_0' does not depend on any axioms" in r.stdout
    forged = "FORGED false" in r.stdout
    print(f"polynomials {len(jobs)} (degree 3..5; {with_roots} with root brackets, {no_root} refuted — no root in the "
          f"box): every gap's certificate ACCEPTED by the kernel (`decide +kernel`, no axioms): {n_thm} theorems, {'all' if ok else 'NOT all'}")
    print(f"rational roots: {len(rjobs)} polynomials (x − r)^m·q, the identity p = Π (x − r)^m·q and q's gaps: {n_rthm} "
          f"theorems accepted (with the identity and ZRootFactor.root_factor, a root of p in a gap is one of the r)")
    print(f"mutation (a bracket merged into its gap): searcher {'finds nothing' if mut_search is None else 'FOUND ONE'}, "
          f"forged leaf {'refused by the kernel' if forged else 'NOT refused'}")
    if not ok:
        print((r.stdout + r.stderr)[-3000:])
    if ok and forged and mut_search is None and no_root > 0 and with_roots > 0 and len(rjobs) > 0:
        print("ZSTURM LEAN BRIDGE GREEN — caught")
    else:
        print("ZSTURM LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
