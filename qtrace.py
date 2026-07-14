# -*- coding: utf-8 -*-
"""
qtrace — the quarantine tracer. Answers, by code: where does Z live, and on
which operation do we reach / lose quarantine?

Two registers, two very different answers (this is the point):

  * GREEDY (the verdict register, ztl.ev). Z is a TRAPDOOR: it lives only on a
    raw atom; the FIRST operator that touches it collapses it to T/F, and no
    chain of operations ever returns to Z. So "on which operation do we reach
    quarantine?" — NONE: greedy ops only DESTROY Z, never produce it. The
    tracer marks each atom that is Z and the exact operator where that Z
    collapses (⚡).

  * GROUNDING (the solver / lazy register, fixedpoint.least_fp_lazy). Here Z is
    where a self-referential sentence LANDS when its grounding fixed point does
    not resolve — the Liar and friends. The tracer runs the solver and flags
    which sentences reach quarantine.

Usage:
    python3 qtrace.py "not(not(p))"           # greedy, p defaults to Z
    python3 qtrace.py "imp(and(a,b),a)" a=T    # set verified atoms
    python3 qtrace.py --system                 # ground the paradox zoo
"""

import re
import sys

from ztl import T, F, Z, ev, show                       # noqa: E402


def _parse(s):
    """Tiny prefix parser: `op(arg,arg)` / atom → core tuple."""
    toks = re.findall(r"[(),]|[A-Za-z_][A-Za-z0-9_]*", s)
    pos = 0

    def node():
        nonlocal pos
        name = toks[pos]; pos += 1
        if pos < len(toks) and toks[pos] == "(":
            pos += 1
            args = [node()]
            while toks[pos] == ",":
                pos += 1
                args.append(node())
            pos += 1                                    # )
            return (name,) + tuple(args)
        return name

    return node()


# ------------------------------------------------------------- GREEDY tracer
def _walk(phi, env, depth):
    """Return (greedy value, printed block). Marks Z atoms and the operator
    where a Z collapses."""
    if isinstance(phi, str):
        v = phi if phi in (T, F, Z) else env.get(phi, Z)
        tag = "   ← unverified atom, in quarantine (Z)" if v == Z else ""
        return v, ["  " * depth + f"{phi} = {v}{tag}"]

    child_vals, child_blocks = [], []
    for c in phi[1:]:
        cv, cb = _walk(c, env, depth + 1)
        child_vals.append(cv)
        child_blocks.append(cb)
    v = ev(phi, env)
    # a greedy op never yields Z; if a direct input WAS Z, this is where it died
    collapse = any(cv == Z for cv in child_vals) and v != Z
    mark = f"   ⚡ Z collapses here → {v}" if collapse else ""
    block = ["  " * depth + f"{phi[0]} = {v}{mark}"]
    for cb in child_blocks:
        block += cb
    return v, block


def trace_greedy(formula_str, env=None):
    env = env or {}
    core = _parse(formula_str)
    atoms = sorted({a for a in _atoms(core)})
    full = {a: env.get(a, Z) for a in atoms}
    v, block = _walk(core, full, 0)
    print(f"GREEDY trace of  {show(core)}")
    print(f"  atoms: {', '.join(f'{a}={full[a]}' for a in atoms) or '(none)'}")
    print(f"  verdict: {v}\n")
    print("\n".join(block))
    zliving = [a for a in atoms if full[a] == Z]
    print(f"\n  Z lives on: {', '.join(zliving) or '(nowhere)'} — and dies at "
          f"the first ⚡ above each; the verdict is {v}, never Z "
          f"(greedy ops don't produce Z).")


def _atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi not in (T, F, Z):
            acc.add(phi)
    else:
        for x in phi[1:]:
            _atoms(x, acc)
    return acc


# ---------------------------------------------------------- GROUNDING tracer
def trace_system():
    """Ground the paradox zoo; flag which sentences reach quarantine (Z)."""
    from fixedpoint import ZOO, least_fp_lazy
    print("GROUNDING trace (the solver's least fixed point — where sentences "
          "LAND in quarantine):\n")
    for name, system in ZOO.items():
        fp = least_fp_lazy(system)
        print(f"  {name}")
        for s, defn in system.items():
            v = fp[s]
            q = "   ← QUARANTINE (Z: ungrounded)" if v == Z else ""
            print(f"      {s}: {show(defn)}  →  {v}{q}")
        print()
    print("  Here Z is REACHED (not destroyed): a self-referential sentence "
          "with no ground lands in Z. isZ(x)=¬(x↔x) detects it; the passport "
          "(zpassport.py) says WHY.")


if __name__ == "__main__":
    args = sys.argv[1:]
    if args and args[0] == "--system":
        trace_system()
    elif args:
        env = {}
        for a in args[1:]:
            if "=" in a:
                k, val = a.split("=", 1)
                env[k] = val.strip().upper()
        trace_greedy(args[0], env)
    else:
        for demo in ["not(not(p))", "imp(p,p)", "or(p,not(p))"]:
            trace_greedy(demo)
            print("\n" + "-" * 60 + "\n")
        trace_system()
