# -*- coding: utf-8 -*-
"""
zlogexact ↔ lean/ZLnMul.lean — what an exact logarithm rests on, checked (2026-11-27).

READ 2026-11-27: `zlogexact` never uses Hermite–Lindemann for a verdict (`sign()` is 0 only for the formal zero;
otherwise it reads the floor's proved brackets of ln p, and a bracket straddling 0 gives no verdict). Its SOUNDNESS
rests on three things:
  1. ln(x·y) = ln x + ln y — PROVED on VR's continuum: `ZLnMul.rln_mul` (from `ZExpAdd5.rexpR_add`, exp's addition
     law, built today in five stages), with `rln_one`, `rln_respects`; zero axioms;
  2. the factorisation is a factorisation: n = Π p^e — checked HERE by the kernel for every n the stand uses (primality
     is NOT needed for soundness: ln of any product splits; it matters only for completeness, the zero test);
  3. the brackets of ln p — `ZLn` (proved), read by `zfunc.ln_pt`.
This stand: 300 seeded integers (and the stand's own 64, 8, 6, 10), `_factor` checked by the kernel's product
(`Nat` arithmetic, `decide`-free #eval), and `LogLin.ln(a/b)` = ln a − ln b as coefficient vectors.
MUTATION: one exponent off by one -> the kernel's product differs.

Run:  python3 inventory/zlogexact_lean_bridge.py   -> ZLOGEXACT LEAN BRIDGE GREEN
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
import zlogexact as L                  # noqa: E402

LEAN = os.path.join(ROOT, "lean")


def main():
    rnd = random.Random(20261127)
    ns = [64, 8, 6, 10, 1, 2, 97, 1024, 3 ** 7 * 5 ** 3] + [rnd.randint(2, 10 ** 7) for _ in range(300)]
    facs = [L._factor(n) for n in ns]
    mut = dict(facs[0]); p0 = next(iter(mut)); mut[p0] += 1
    lines = ["def prodPow : List (Nat × Nat) → Nat | [] => 1 | (p, e) :: r => p ^ e * prodPow r", ""]
    for k, f in enumerate(facs + [mut]):
        lst = "[" + ", ".join(f"({p}, {e})" for p, e in sorted(f.items())) + "]"
        lines.append(f'#eval IO.println s!"K{k} {{prodPow {lst}}}"')
    fd, path = tempfile.mkstemp(prefix="zlogexact_bridge_", suffix=".lean", dir=LEAN)
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=LEAN, capture_output=True, text=True, timeout=600)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        raise SystemExit("LEAN FAILED:\n" + (r.stdout + r.stderr)[-2000:])
    got = {int(l.split()[0][1:]): int(l.split()[1]) for l in r.stdout.splitlines() if l.startswith("K")}
    ok = sum(got[k] == n for k, n in enumerate(ns))
    caught = got[len(ns)] != ns[0]
    # ln(a/b) = ln a − ln b, as coefficient vectors (the linear half of the representation)
    lin = 0
    for _ in range(200):
        a, b = rnd.randint(1, 10 ** 5), rnd.randint(1, 10 ** 5)
        q = L.LogLin.ln(Fraction(a, b))
        d = L.LogLin.ln(a) - L.LogLin.ln(b)
        lin += (q.c == d.c and q.r == d.r)
    print(f"factorisations {len(ns)}: kernel product == n {ok}/{len(ns)}; ln(a/b) == ln a − ln b {lin}/200")
    print(f"mutation (one exponent + 1): {'caught' if caught else 'NOT CAUGHT'}")
    if ok == len(ns) and lin == 200 and caught:
        print("ZLOGEXACT LEAN BRIDGE GREEN")
    else:
        print("ZLOGEXACT LEAN BRIDGE RED"); sys.exit(1)


if __name__ == "__main__":
    main()
