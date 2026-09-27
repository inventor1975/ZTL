# -*- coding: utf-8 -*-
"""
redteam_logic_oracle — ZTL's logic core rebuilt from its DEFINITIONS (2026-09-27).

An independent oracle for the red team of the logic core. Nothing here imports
the code under test (ztl, zverify, ztljudge, fixedpoint, zpassport); every
notion is written again from the words that define it:

  tables     SPEC.md "The principle": op(..Z..) = AND over the classical
             substitutions {T, F} of each Z argument; T iff T is forced under
             EVERY reading. Classical kernels written here, not imported.
  ev         a formula's value: an atom reads its marking (constants T/F/Z are
             their own value), a compound applies its connective to the values
             of its children (occurrences independent; greedy collapse).
  grades     zverify's docstring: HEREDITARY — the verdict is unchanged under
             every partial refinement (each mark left a mark or verified to T
             or F; Lean `refines`); SOUND — every completion gives one
             classical answer equal to the verdict; else until-verification.
  judge      ztljudge.judge's docstring: EARNED = T & hereditary; REFUTED =
             F & hereditary; ON CREDIT = T & not hereditary; E = nothing
             unverified, and an absent subject; OPEN otherwise.
  lazy       strong Kleene (fixedpoint.py's docstring: "Z flows").
  passport   zpassport's docstring: per strongly connected component of the
             dependency graph, from the lazy least fixed point: GROUNDED /
             DOWNSTREAM / INPUT / PARADOX (0 classical models) / INTRINSIC
             (1) / UNDERDETERMINED (>= 2), and the greedy oscillation period.

Formulas are the kernel's AST: an atom is a str, constants "T"/"F"/"Z", and
("not", a) / (op, a, b) with op in and, or, imp, xor, xnor.
"""
from itertools import product

T, F, Z = "T", "F", "Z"
VALS = (T, F, Z)
CONSTS = (T, F, Z)

# classical kernels, as truth functions on booleans
KERN1 = {"not": lambda a: not a}
KERN2 = {"and": lambda a, b: a and b,
         "or": lambda a, b: a or b,
         "imp": lambda a, b: (not a) or b,
         "xor": lambda a, b: a != b,
         "xnor": lambda a, b: a == b}
READ = {T: (True,), F: (False,), Z: (True, False)}   # the classical readings


def lift1(op, x):
    return T if all(KERN1[op](a) for a in READ[x]) else F


def lift2(op, x, y):
    return T if all(KERN2[op](a, b) for a in READ[x] for b in READ[y]) else F


TABLE1 = {x: lift1("not", x) for x in VALS}
TABLE2 = {op: {(x, y): lift2(op, x, y) for x in VALS for y in VALS} for op in KERN2}


def ev(phi, env):
    """The greedy (ZTL) value. Iterative, so deep chains are fine."""
    stack, out = [(phi, 0)], []
    while stack:
        node, state = stack.pop()
        if isinstance(node, str):
            out.append(node if node in CONSTS else env[node])
        elif state == 0:
            stack.append((node, 1))
            for c in reversed(node[1:]):
                stack.append((c, 0))
        elif node[0] == "not":
            out.append(TABLE1[out.pop()])
        else:
            b = out.pop()
            a = out.pop()
            out.append(TABLE2[node[0]][(a, b)])
    return out[0]


def classical(phi, env):
    """Plain two-valued evaluation on a T/F environment (constants T/F only)."""
    if isinstance(phi, str):
        v = phi if phi in (T, F) else env[phi]
        return v == T
    if phi[0] == "not":
        return not classical(phi[1], env)
    return KERN2[phi[0]](classical(phi[1], env), classical(phi[2], env))


def atoms(phi):
    acc, stack = set(), [phi]
    while stack:
        n = stack.pop()
        if isinstance(n, str):
            if n not in CONSTS:
                acc.add(n)
        else:
            stack.extend(n[1:])
    return acc


# ------------------------------------------------------------------ grades
def refinements(marking):
    """Lean `refines v w`: w agrees with v wherever v is not the mark; where
    v is the mark, w is anything (mark, T or F). `marking` values: T/F/Z."""
    marks = sorted(a for a, v in marking.items() if v == Z)
    for combo in product(VALS, repeat=len(marks)):
        w = dict(marking)
        w.update(zip(marks, combo))
        yield w


def completions(marking):
    marks = sorted(a for a, v in marking.items() if v == Z)
    for combo in product((T, F), repeat=len(marks)):
        w = dict(marking)
        w.update(zip(marks, combo))
        yield w


def hereditary(phi, marking):
    v = ev(phi, marking)
    return all(ev(phi, w) == v for w in refinements(marking))


def sound(phi, marking):
    v = ev(phi, marking)
    return all(ev(phi, w) == v for w in completions(marking))


def grade(phi, marking):
    """marking: T/F/Z per atom of phi (Z = the mark)."""
    if hereditary(phi, marking):
        return "hereditary"
    return "sound" if sound(phi, marking) else "until-verification"


def disposition(verdict, grade_, unverified, absent):
    """ztljudge.judge's docstring, read literally."""
    if grade_ == "hereditary" and verdict == T:
        return "EARNED"
    if grade_ == "hereditary" and verdict == F:
        return "REFUTED"
    if verdict == T:
        return "ON CREDIT"
    if absent and not unverified:
        return "E"
    return "OPEN"


# ------------------------------------------------------------------ lazy
def k1(x):
    return {T: F, F: T, Z: Z}[x]


def k2(op, a, b):
    """Strong Kleene: the classical value if every reading of the Z inputs
    gives the same one, else Z (the 'Z flows' register)."""
    outs = {KERN2[op](x, y) for x in READ[a] for y in READ[b]}
    return (T if outs.pop() else F) if len(outs) == 1 else Z


def k1l(x):
    outs = {KERN1["not"](a) for a in READ[x]}
    return (T if outs.pop() else F) if len(outs) == 1 else Z


def ev_lazy(phi, env):
    if isinstance(phi, str):
        return phi if phi in CONSTS else env[phi]
    if phi[0] == "not":
        return k1l(ev_lazy(phi[1], env))
    return k2(phi[0], ev_lazy(phi[1], env), ev_lazy(phi[2], env))


# ------------------------------------------------------------------ passports
def deps(phi):
    return atoms(phi)


def lfp_lazy(system):
    v = {s: Z for s in system}
    while True:
        w = {s: ev_lazy(d, v) for s, d in system.items()}
        if w == v:
            return v
        v = w


def components(system):
    """SCCs by mutual reachability (quadratic, fine for small systems)."""
    names = sorted(system)
    reach = {s: set() for s in names}
    for s in names:
        todo = [d for d in deps(system[s]) if d in system]
        while todo:
            x = todo.pop()
            if x not in reach[s]:
                reach[s].add(x)
                todo.extend(d for d in deps(system[x]) if d in system)
    comps, seen = [], set()
    for s in names:
        if s in seen:
            continue
        c = sorted({s} | {t for t in reach[s] if s in reach[t]})
        seen |= set(c)
        comps.append(c)
    # dependencies first: a component after every component it reads
    order, placed = [], set()
    while len(order) < len(comps):
        for c in comps:
            if tuple(c) in placed:
                continue
            below = set()
            for s in c:
                below |= reach[s] - set(c)
            if all(any(b in d for d in order) for b in below):
                order.append(c)
                placed.add(tuple(c))
    return order


def greedy_period(comp, system, env, steps=64):
    v = {s: Z for s in comp}
    trace = [v]
    for _ in range(steps):
        v = {s: ev(system[s], {**env, **v}) for s in comp}
        if v in trace:
            return len(trace) - trace.index(v)
        trace.append(v)
    return None


def passports(system):
    """name -> (kind, detail) with detail = period / model count / permanence."""
    lfp = lfp_lazy(system)
    kind = {}
    for comp in components(system):
        cs = set(comp)
        if all(lfp[s] in (T, F) for s in comp):
            for s in comp:
                kind[s] = ("GROUNDED", None)
            continue
        env_names = set()
        for s in comp:
            env_names |= (deps(system[s]) & set(system)) - cs
        env = {n: lfp[n] for n in env_names}
        culprits = sorted(n for n in env_names if lfp[n] == Z)
        if culprits:
            perm = any(kind[c][0] == "PARADOX" or kind[c] == ("DOWNSTREAM", "permanent")
                       for c in culprits)
            k = ("DOWNSTREAM", "permanent" if perm else "conditional")
        elif len(comp) == 1 and not (deps(system[comp[0]]) & cs):
            k = ("INPUT", None)
        else:
            models = 0
            for combo in product((T, F), repeat=len(comp)):
                vc = dict(zip(comp, combo))
                if all(ev(system[s], {**env, **vc}) == vc[s] for s in comp):
                    models += 1
            p = greedy_period(comp, system, env)
            k = (("PARADOX", p) if models == 0 else ("INTRINSIC", 1) if models == 1
                 else ("UNDERDETERMINED", models))
        for s in comp:
            kind[s] = k
    return lfp, kind


# ------------------------------------------------------------------ generation
OPS = ["and", "or", "imp", "xor", "xnor"]


def random_formula(rnd, depth, atoms_, p_const=0.08):
    if depth == 0 or rnd.random() < 0.18:
        return rnd.choice(CONSTS) if rnd.random() < p_const else rnd.choice(atoms_)
    if rnd.random() < 0.2:
        return ("not", random_formula(rnd, depth - 1, atoms_, p_const))
    return (rnd.choice(OPS), random_formula(rnd, depth - 1, atoms_, p_const),
            random_formula(rnd, depth - 1, atoms_, p_const))


def all_formulas(size, leaves):
    """Every formula with exactly `size` nodes over the given leaves."""
    if size == 1:
        yield from leaves
        return
    for f in all_formulas(size - 1, leaves):
        yield ("not", f)
    for k in range(1, size - 1):
        for a in list(all_formulas(k, leaves)):
            for b in list(all_formulas(size - 1 - k, leaves)):
                for op in OPS:
                    yield (op, a, b)


SYM = {"and": "&", "or": "|", "imp": "->", "xor": "^", "xnor": "="}


def text_full(phi):
    """Fully parenthesised text for ztljudge.formalize."""
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "~" + text_full(phi[1])
    return f"({text_full(phi[1])} {SYM[phi[0]]} {text_full(phi[2])})"
