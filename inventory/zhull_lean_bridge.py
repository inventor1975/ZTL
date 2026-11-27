# -*- coding: utf-8 -*-
"""
znumsolve._hull ↔ lean/ZHull.lean — the solver's narrowing bound is the kernel's exact one (2026-11-27).

`lean/ZHull.lean` proves, over any ordered ring with ZLP's laws (no axioms): narrowing x by `k·x + rest ⋈ 0` to
`k·x ≤ −rlo` (`le`), `k·x ≥ −rhi` (`ge`), `−rhi ≤ k·x ≤ −rlo` (`eq`) is SOUND (nothing satisfiable dropped) and, for
`le`/`ge`, EXACT (the sign-picked corner satisfies it). This stand checks that `znumsolve._hull` computes exactly those
bounds: on seeded random integer constraints, the kernel evaluates `rlo`/`rhi` over ℤ (`ZLP.intOMul`), and Python's
returned box, multiplied back by k, must equal −rlo / −rhi on the side the theorem names (sides swapped when k < 0).
MUTATION: one coefficient's box widened on the Python side only -> some bound differs.

Run:  python3 inventory/zhull_lean_bridge.py   -> ZHULL LEAN BRIDGE GREEN
"""
import os
import random
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import znumsolve as S                  # noqa: E402
from znum import INF                   # noqa: E402

LEAN = os.path.join(ROOT, "lean")


def cases(seed=20261127, n=300):
    rnd = random.Random(seed)
    out = []
    for _ in range(n):
        m = rnd.randint(0, 4)
        names = ["x"] + [f"p{j}" for j in range(m)]
        k = rnd.choice([c for c in range(-5, 6) if c != 0])
        terms = {"x": (Fraction(k), "x")}
        qs = {"x": {"lo": Fraction(-100), "hi": Fraction(100)}}
        for nm in names[1:]:
            lo = rnd.randint(-9, 9); hi = lo + rnd.randint(0, 9)
            qs[nm] = {"lo": Fraction(lo), "hi": Fraction(hi)}
            terms[nm] = (Fraction(rnd.randint(-6, 6)), nm)
        c0 = Fraction(rnd.randint(-20, 20))
        kind = rnd.choice(["le", "eq", "ge"])
        out.append((kind, c0, terms, qs, k))
    return out


def py_hull(kind, c0, terms, qs):
    if kind == "ge":       # ≥ 0 is ≤ 0 of the negated form; the solver reads it so (both sides flipped)
        terms2 = {key: (-c, nm) for key, (c, nm) in terms.items()}
        return S._hull("le", -c0, terms2, "x", qs), True
    return S._hull(kind, c0, terms, "x", qs), False


def main():
    cs = cases()
    lines = ["import ZHull", "open ZLP ZSuperpose ZHull", ""]
    for i, (kind, c0, terms, qs, k) in enumerate(cs):
        ts = ", ".join(f"⟨{int(c)}, {int(qs[nm]['lo'])}, {int(qs[nm]['hi'])}, 0, {'true' if c >= 0 else 'false'}⟩"
                       for key, (c, nm) in terms.items() if nm != "x")
        lines.append(f'#eval IO.println s!"K{i} {{rlo intOMul ({int(c0)}) ([{ts}] : List (STerm Int))}} {{rhi intOMul ({int(c0)}) ([{ts}] : List (STerm Int))}}"')
    fd, path = tempfile.mkstemp(prefix="zhull_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=1800)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-3000:])
    kern = {}
    for l in r.stdout.splitlines():
        if l.startswith("K"):
            a, lo, hi = l.split()
            kern[int(a[1:])] = (int(lo), int(hi))
    ok = bad = 0
    for i, (kind, c0, terms, qs, k) in enumerate(cs):
        rl, rh = kern[i]
        (lo, hi, _, _), flipped = py_hull(kind, c0, terms, qs)
        # the theorem's set for k·x
        want_lo = -rh if kind in ("eq", "ge") else None          # k·x ≥ −rhi
        want_hi = -rl if kind in ("eq", "le") else None          # k·x ≤ −rlo
        # Python's box for x, mapped to k·x
        if k > 0:
            kx_lo = None if lo == -INF else lo * k
            kx_hi = None if hi == INF else hi * k
        else:
            kx_lo = None if hi == INF else hi * k
            kx_hi = None if lo == -INF else lo * k
        good = kx_lo == want_lo and kx_hi == want_hi
        ok += good; bad += not good
        if not good and bad <= 3:
            print("  DIFF", kind, c0, terms, qs, k, (lo, hi), (kx_lo, kx_hi), (want_lo, want_hi), kern[i])
    print(f"constraints {len(cs)} (le/eq/ge, k of both signs, 0..4 other quantities): Python _hull == kernel bound {ok}, differ {bad}")
    # MUTATION: widen one box on the Python side
    caught = False
    for i, (kind, c0, terms, qs, k) in enumerate(cs):
        others = [nm for (c, nm) in terms.values() if nm != "x" and c != 0]
        if not others:
            continue
        qs2 = {**qs, others[0]: {"lo": qs[others[0]]["lo"] - 1, "hi": qs[others[0]]["hi"] + 1}}
        caught = py_hull(kind, c0, terms, qs2)[0][:2] != py_hull(kind, c0, terms, qs)[0][:2]
        break
    print(f"mutation (one box widened on the Python side): {'caught' if caught else 'NOT CAUGHT'}")
    if bad == 0 and caught:
        print("ZHULL LEAN BRIDGE GREEN")
    else:
        print("ZHULL LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
