# -*- coding: utf-8 -*-
"""
WHAT VALUES CAN THE CLAIM STILL TAKE — down the tree as fast as up (2026-11-09).

THE CURATOR'S POINT (2026-11-09, after ZTL against CaDiCaL): «Мы идём вверх очень быстро, а вниз почему-то
медленно, хотя когда идём вниз все вердикты двоичные, они только на входе с Z.» Right, and the slowness was not the
values: `zbackward` LISTS every minimal set of grounds (an AND of 100 ORs of 10 has 10^100 of them), and
`zverify.hereditary_bit` walks 3^n refinements. The question "which values can the claim still take" needs neither.

THE PASS. For every node, the SET of values it can take over the fillings of the dirty atoms under it:
    a dirty atom      {T, F}   over completions        {T, F, Z} over refinements (a mark may stay a mark)
    a clean atom      {its value}
    op(A, B)          { table[op](a, b) : a in reach(A), b in reach(B) }
The last line is EXACT when A and B share no dirty atom — their fillings are then independent, every pair (a, b) is
attained together. ZTL's compound values are two-valued (Z only on atoms), so every inner set is a subset of {T, F}:
two bits per node, one pass — the cost of the forward pass.

A SHARED ATOM (the curator's "по 10 атомов"): an atom that occurs in both children is enumerated AT ITS LOWEST COMMON
NODE — below that node it is a constant of the world, so the children are independent again and the line above is
exact in each world; the node's set is the union over the worlds. The work is 2^k (3^k over refinements) per node,
k = the shared atoms open at that node; past `cap` the pass REFUSES aloud (None), it does not grind.

WHAT IS CHECKED, WHAT IS ARGUED.
  * "the claim can be T": a WITNESS filling is built down the tree and RE-EVALUATED by the forward judge (`ztl.ev`)
    — the answer carries its own check.
  * "the claim can NOT be T": rests on the exactness of the union-of-images line — argued above, checked by
    enumeration in test_zreach.py; the Lean theorem is NOT written yet (said, not hidden).
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ztl import T, F, Z, VALUES, OPS1, OPS2, ev     # noqa: E402

CAP = 12            # shared atoms open at one node: 2^12 worlds (3^12 over refinements ~ 5e5) — past it, refuse


def _is_atom(phi):
    return isinstance(phi, str) and phi not in VALUES


class _Tree:
    """Nodes numbered once; for every repeated dirty atom its lowest common node."""

    def __init__(self, phi, dirty):
        self.kids, self.label, self.parent, self.depth = [], [], [], []
        occ = {}
        stack = [(phi, -1, 0)]
        while stack:
            p, par, d = stack.pop()
            i = len(self.label)
            self.label.append(p if isinstance(p, str) else p[0])
            self.kids.append([])
            self.parent.append(par)
            self.depth.append(d)
            if par >= 0:
                self.kids[par].append(i)
            if isinstance(p, str):
                if p in dirty:
                    occ.setdefault(p, []).append(i)
            else:
                for c in reversed(p[1:]):
                    stack.append((c, i, d + 1))
        self.own = {}                         # node -> dirty atoms enumerated there
        self.ext = [set() for _ in self.label]   # node -> atoms fixed by an ANCESTOR's world
        for a, leaves in occ.items():
            if len(leaves) == 1:
                continue
            lca = self._lca(leaves)
            self.own.setdefault(lca, []).append(a)
            for leaf in leaves:               # every node strictly between the lca and a leaf sees `a` fixed
                j = leaf
                while j != lca:
                    self.ext[j].add(a)
                    j = self.parent[j]

    def _lca(self, nodes):
        def up(a, b):
            while self.depth[a] > self.depth[b]:
                a = self.parent[a]
            while self.depth[b] > self.depth[a]:
                b = self.parent[b]
            while a != b:
                a, b = self.parent[a], self.parent[b]
            return a
        x = nodes[0]
        for y in nodes[1:]:
            x = up(x, y)
        return x


def reach(phi, marking, mode="completion", cap=CAP):
    """-> {"values": frozenset, "witness": {value: filling}} or {"refused": why}.
    marking: atom -> T / F / Z (Z = dirty). mode "completion": every dirty atom filled T or F; "refinement": a dirty
    atom may also stay Z (zverify's refinements). A witness gives every dirty atom of phi a value (Z = left open)."""
    dirty = {a for a, v in marking.items() if v == Z}
    tr = _Tree(phi, dirty)
    leaf_vals = (T, F) if mode == "completion" else (T, F, Z)
    memo = {}

    def go(i, env):
        key = (i, tuple(sorted((a, env[a]) for a in tr.ext[i])))
        hit = memo.get(key)
        if hit is not None:
            return hit
        lab = tr.label[i]
        if not tr.kids[i]:                    # a leaf: an atom or a constant
            if lab in VALUES:
                out = {lab: None}
            elif lab in env:
                out = {env[lab]: None}
            elif lab in dirty:
                out = {v: None for v in leaf_vals}
            else:
                out = {marking[lab]: None}
            memo[key] = out
            return out
        own = tr.own.get(i, [])
        if len(own) + len(tr.ext[i]) > cap:
            raise _Refuse(f"{len(own) + len(tr.ext[i])} shared atoms open at one node (cap {cap})")
        out = {}
        for world in itertools.product(leaf_vals, repeat=len(own)):
            env2 = dict(env, **dict(zip(own, world))) if own else env
            if lab == "not":
                for a in go(tr.kids[i][0], env2):
                    out.setdefault(OPS1["not"](a), (world, a, None))
            else:
                A, B = go(tr.kids[i][0], env2), go(tr.kids[i][1], env2)
                f = OPS2[lab]
                for a in A:
                    for b in B:
                        out.setdefault(f(a, b), (world, a, b))
            if len(out) == 3 or (len(out) == 2 and Z not in out):
                break                         # every value a compound can take is already reached
        memo[key] = out
        return out

    try:
        root = go(0, {})
    except _Refuse as e:
        return {"refused": str(e)}
    except RecursionError:
        return {"refused": "the formula is deeper than Python's stack"}

    def witness(i, env, want, fill):
        lab = tr.label[i]
        if not tr.kids[i]:
            if lab in dirty and lab not in env:
                fill[lab] = want
            return
        world, a, b = go(i, env)[want]
        own = tr.own.get(i, [])
        env2 = dict(env, **dict(zip(own, world))) if own else env
        fill.update(zip(own, world))
        witness(tr.kids[i][0], env2, a, fill)
        if b is not None:
            witness(tr.kids[i][1], env2, b, fill)

    wit = {}
    for v in root:
        fill = {}
        witness(0, {}, v, fill)
        m2 = dict(marking, **fill)
        got = ev(phi, m2)
        if got != v:                          # the witness is checked by the forward judge, every time
            raise AssertionError(f"zreach: the witness for {v} evaluates to {got} — a bug, not an answer")
        wit[v] = fill
    return {"values": frozenset(root), "witness": wit}


class _Refuse(Exception):
    pass


def sat(phi, marking, target=T):
    """Can some completion of the dirty atoms make phi == target? -> ("YES", filling) / ("NO", None) /
    ("REFUSED", why). YES is checked by ev; NO rests on the exactness argued in the docstring."""
    r = reach(phi, marking, "completion")
    if "refused" in r:
        return "REFUSED", r["refused"]
    return ("YES", r["witness"][target]) if target in r["values"] else ("NO", None)
