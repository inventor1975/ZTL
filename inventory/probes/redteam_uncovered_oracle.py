# -*- coding: utf-8 -*-
"""
The oracle for the red team of the UNCOVERED core (2026-09-28).

Written from the documents, importing NOTHING from the code under test
(no ztl, ztljudge, zverify, zbackward, zfl, zexpire, ztime, zfo,
quantifiers, tableau, tableau_fo, zsequent). Every definition below cites
where it was read:

  values, tables     SPEC.md / ONBOARDING §1.1: f*(x..) = AND over the
                     classical readings, subs(Z) = {T, F}, every occurrence
                     read independently (lean/ZTime.lean `lift1`, `lift2`).
  grades             lean/ZTime.lean: Refines, Hereditary, Completion, Sound;
                     until-verification is the residue (zverify's docstring).
  disposition        ztljudge.judge's docstring: EARNED = T & hereditary,
                     REFUTED = F & hereditary, ON CREDIT = T not hereditary,
                     E = nothing unverified but a subject absent, else OPEN.
  grammar            the reading the logic red team established by reading
                     `ztljudge.formalize` (REDTEAM-LOGIC-2026-09.md, notes):
                     ¬ tightest, then & > | > ^ > -> > =, all LEFT-associative.
                     Written here as a LAYERED grammar (one rule per level),
                     a different algorithm from the code's precedence climbing.
  reverse pass       zbackward's docstring: POSSIBLE = minimal S such that
                     SOME filling of S gives the target; GUARANTEED = minimal S
                     such that EVERY filling does; minimal = no proper subset
                     also qualifies (an antichain); `already` = the empty set.
  epoch              lean/EpochBoundary.lean: Step.verify (Z -> T/F),
                     Step.expire (T/F -> Z), EpochBlind; zfl.run's comment:
                     "one crossing per declared event", survives = same verdict.
  signed tableaux    tableau.py's docstring and lean/TableauCert.lean: a signed
                     set is closed iff NO marking satisfies every node
                     (a node (S, φ) holds iff the value of φ lies in S).
  quantifiers        quantifiers.py's docstring and lean/ZQuant.lean: over a
                     finite domain ∀ = T iff every instance is strictly T, else
                     F; ∃ = T iff some instance is strictly T, else F.

Exact: values are three strings, no floats anywhere.
"""

from itertools import product, combinations

T, F, Z = "T", "F", "Z"
E = "E"
VALS = (T, F, Z)
CONSTS = (T, F, Z)
BIN = ("and", "or", "imp", "xor", "xnor")

# ------------------------------------------------------------ the tables
_SUBS = {T: (True,), F: (False,), Z: (True, False)}
_CL = {"not": lambda a: not a,
       "and": lambda a, b: a and b,
       "or": lambda a, b: a or b,
       "imp": lambda a, b: (not a) or b,
       "xor": lambda a, b: a != b,
       "xnor": lambda a, b: a == b}


def lift(op, *xs):
    """The generating principle: T iff T under EVERY classical reading."""
    f = _CL[op]
    return T if all(f(*r) for r in product(*(_SUBS[x] for x in xs))) else F


def ev(phi, m):
    if isinstance(phi, str):
        if phi in CONSTS:
            return phi
        v = m.get(phi, Z)
        return Z if v == E else v          # E reaches the kernel as a mark
    if phi[0] == "not":
        return lift("not", ev(phi[1], m))
    return lift(phi[0], ev(phi[1], m), ev(phi[2], m))


def atoms(phi, acc=None):
    acc = set() if acc is None else acc
    if isinstance(phi, str):
        if phi not in CONSTS:
            acc.add(phi)
    else:
        for s in phi[1:]:
            atoms(s, acc)
    return acc


def size(phi):
    return 1 if isinstance(phi, str) else 1 + sum(size(s) for s in phi[1:])


# ------------------------------------------------------------ the grades
def _full(phi, m):
    out = {a: Z for a in atoms(phi)}
    out.update(m)
    return out


def refinements(m, names):
    """Lean `Refines m' m`: earned ground kept, a mark may stay or resolve."""
    marks = [a for a in names if m.get(a, Z) in (Z, E)]
    for vals in product(VALS, repeat=len(marks)):
        m2 = dict(m)
        m2.update(zip(marks, vals))
        yield m2


def completions(m, names):
    marks = [a for a in names if m.get(a, Z) in (Z, E)]
    for vals in product((T, F), repeat=len(marks)):
        m2 = dict(m)
        m2.update(zip(marks, vals))
        yield m2


def grade(phi, m):
    names = sorted(atoms(phi))
    m = _full(phi, m)
    v = ev(phi, m)
    if all(ev(phi, r) == v for r in refinements(m, names)):
        return "hereditary"
    if all(ev(phi, c) == v for c in completions(m, names)):
        return "sound"
    return "until-verification"


def disposition(phi, m):
    """ztljudge.judge's docstring, row by row."""
    mm = _full(phi, m)
    v, g = ev(phi, mm), grade(phi, mm)
    unv = [a for a in atoms(phi) if mm[a] == Z]
    gone = [a for a in atoms(phi) if mm[a] == E]
    if g == "hereditary" and v == T:
        return "EARNED"
    if g == "hereditary" and v == F:
        return "REFUTED"
    if v == T:
        return "ON CREDIT"
    if gone and not unv:
        return "E"
    return "OPEN"


# ------------------------------------------------------- 1. the grammar
LEVELS = ["xnor", "imp", "xor", "or", "and"]          # loosest .. tightest
SPELL = {"and": ["&", "∧"], "or": ["|", "∨"], "imp": ["->", "→"],
         "xor": ["^", "⊕"], "xnor": ["=", "↔", "<->"]}
TOK2OP = {s: op for op, ss in SPELL.items() for s in ss}
NEG = ["~", "¬"]


class Refused(Exception):
    pass


def lex(text):
    """Tokens, written from the docstring's alphabet: identifiers are runs of
    letters, digits and '_' (Python's str.isalnum is the only reading of
    'letter' used); operators by their spellings, longest first."""
    spell = sorted(TOK2OP, key=len, reverse=True) + NEG + ["(", ")"]
    out, i = [], 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
            continue
        for s in spell:
            if text.startswith(s, i):
                out.append("¬" if s in NEG else s if s in "()" else TOK2OP[s])
                i += len(s)
                break
        else:
            if c.isalnum() or c == "_":
                j = i
                while j < len(text) and (text[j].isalnum() or text[j] == "_"):
                    j += 1
                out.append(("id", text[i:j]))
                i = j
            else:
                raise Refused(f"character {c!r}")
    return out


def parse(text):
    """The layered grammar: level k := level k+1 (OP_k level k+1)*, folded
    to the LEFT; the unary level := '¬' unary | '(' level0 ')' | ident."""
    toks = lex(text)
    pos = 0

    def level(k):
        nonlocal pos
        if k == len(LEVELS):
            return unary()
        left = level(k + 1)
        while pos < len(toks) and toks[pos] == LEVELS[k]:
            pos += 1
            left = (LEVELS[k], left, level(k + 1))
        return left

    def unary():
        nonlocal pos
        if pos >= len(toks):
            raise Refused("end")
        t = toks[pos]
        if t == "¬":
            pos += 1
            return ("not", unary())
        if t == "(":
            pos += 1
            e = level(0)
            if pos >= len(toks) or toks[pos] != ")":
                raise Refused(")")
            pos += 1
            return e
        if isinstance(t, tuple):
            pos += 1
            return t[1]
        raise Refused(f"token {t!r}")

    e = level(0)
    if pos != len(toks):
        raise Refused("trailing")
    return e


def show_min(phi, style="ascii"):
    """Print with the FEWEST parentheses the layered grammar needs."""
    sym = {"and": "&", "or": "|", "imp": "->", "xor": "^", "xnor": "="} \
        if style == "ascii" else \
        {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}
    neg = "~" if style == "ascii" else "¬"

    def lvl(p):
        return len(LEVELS) if isinstance(p, str) or p[0] == "not" \
            else LEVELS.index(p[0])

    def go(p):
        if isinstance(p, str):
            return p
        if p[0] == "not":
            s = go(p[1])
            return neg + (s if lvl(p[1]) == len(LEVELS) else f"({s})")
        k = LEVELS.index(p[0])
        a, b = go(p[1]), go(p[2])
        if lvl(p[1]) < k:                   # looser on the left: parenthesise
            a = f"({a})"
        if lvl(p[2]) <= k:                  # right operand of a LEFT fold
            b = f"({b})"
        return f"{a} {sym[p[0]]} {b}"
    return go(phi)


def show_full(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + show_full(phi[1])
    s = {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}[phi[0]]
    return f"({show_full(phi[1])} {s} {show_full(phi[2])})"


# The USUAL convention, for the documents finding: ¬ > ∧ > ∨ > → > ↔, the
# arrow RIGHT-associative; ⊕ is placed with ↔ (the most common textbook
# placement: both are "equivalence-level" connectives).
CONV = {"and": (4, "L"), "or": (3, "L"), "imp": (2, "R"), "xor": (1, "L"),
        "xnor": (1, "L")}


def parse_conventional(text):
    toks = lex(text)
    pos = 0

    def expr(minp):
        nonlocal pos
        left = unary()
        while pos < len(toks) and toks[pos] in CONV and CONV[toks[pos]][0] >= minp:
            op = toks[pos]
            pos += 1
            p, assoc = CONV[op]
            right = expr(p if assoc == "R" else p + 1)
            left = (op, left, right)
        return left

    def unary():
        nonlocal pos
        t = toks[pos]
        if t == "¬":
            pos += 1
            return ("not", unary())
        if t == "(":
            pos += 1
            e = expr(0)
            pos += 1
            return e
        pos += 1
        return t[1]
    e = expr(0)
    if pos != len(toks):
        raise Refused("trailing")
    return e


# -------------------------------------------------- 2. the reverse pass
def outcome(phi, m, by_disposition):
    return disposition(phi, m) if by_disposition else ev(phi, _full(phi, m))


def hits(o, target):
    return o in target if isinstance(target, (set, frozenset)) else o == target


def families(phi, marking, target, by_disposition=True, grounds=None):
    """The minimal families over EVERY size, the empty set included.
    Returns (possible, guaranteed) as lists of tuples (sorted)."""
    if grounds is None:
        grounds = tuple(sorted(a for a, v in marking.items() if v == Z))
    q_pos, q_gua = {}, {}
    for k in range(len(grounds) + 1):
        for S in combinations(grounds, k):
            hs = []
            for vals in product((T, F), repeat=k):
                m2 = dict(marking)
                m2.update(zip(S, vals))
                hs.append(hits(outcome(phi, m2, by_disposition), target))
            q_pos[S], q_gua[S] = any(hs), all(hs)

    def minimal(q):
        good = [S for S, ok in q.items() if ok]
        return sorted((S for S in good
                       if not any(set(P) < set(S) for P in good)),
                      key=lambda s: (len(s), s))
    return minimal(q_pos), minimal(q_gua)


# ----------------------------------------------------------- 3. epochs
def kleene(phi, m):
    """The LAZY register (ztljudge._lazy's docstring: "Kleene's tables ...
    an unchecked atom survives negation (~Z is Z) and is ABSORBED by a
    decisive partner"); -> read as ~a | b; xor/xnor wait on any Z. zfl's
    `resolved_marking` gives a DEFINED row the value its sentence takes in
    the least fixed point of this jump; for a sentence over plain rows only
    (no self-reference) that is this evaluation, once."""
    if isinstance(phi, str):
        return phi if phi in CONSTS else m.get(phi, Z)
    if phi[0] == "not":
        return {T: F, F: T, Z: Z}[kleene(phi[1], m)]
    a, b = kleene(phi[1], m), kleene(phi[2], m)
    op = phi[0]
    if op == "imp":
        a, op = {T: F, F: T, Z: Z}[a], "or"
    if op == "and":
        return F if F in (a, b) else T if a == b == T else Z
    if op == "or":
        return T if T in (a, b) else F if a == b == F else Z
    if Z in (a, b):
        return Z
    return T if (a == b) == (op == "xnor") else F


def reach_all(phi, m0):
    """Every marking reachable by Step.verify / Step.expire (EpochBoundary),
    over the formula's atoms, by breadth-first search — not by the walking
    lemma, so the lemma is checked rather than assumed."""
    names = sorted(atoms(phi))
    start = tuple(m0.get(a, Z) for a in names)
    seen, todo = {start}, [start]
    while todo:
        cur = todo.pop()
        for i, v in enumerate(cur):
            nxt = []
            if v == Z:
                nxt = [T, F]
            else:
                nxt = [Z]
            for w in nxt:
                n2 = cur[:i] + (w,) + cur[i + 1:]
                if n2 not in seen:
                    seen.add(n2)
                    todo.append(n2)
    return [dict(zip(names, s)) for s in seen]


def epoch_blind(phi, m0):
    v = ev(phi, _full(phi, m0))
    return all(ev(phi, m) == v for m in reach_all(phi, m0))


def constant(phi):
    names = sorted(atoms(phi))
    vals = {ev(phi, dict(zip(names, c))) for c in product(VALS, repeat=len(names))}
    return len(vals) == 1


def depth2_pool(names=("p", "q")):
    """Every formula of depth <= 2 over the names, as a SET (ztime's
    'exhaustive formulas of depth <= 2'): depth 1 = one connective over
    atoms, depth 2 = one connective over depth <= 1."""
    d0 = list(names)
    d1 = [("not", a) for a in d0] + [(op, a, b) for op in BIN for a in d0 for b in d0]
    base = d0 + d1
    d2 = [("not", f) for f in d1] + [(op, a, b) for op in BIN for a in base for b in base]
    return list(dict.fromkeys(d0 + d1 + d2))


# ------------------------------------------------ 4. tableaux and FO
def sat_signed(nodes):
    """A signed set (list of (frozenset sign, formula)) is satisfiable iff
    some marking of its atoms puts every formula's value inside its sign."""
    names = sorted(set().union(*[atoms(f) for _, f in nodes])) if nodes else []
    for vals in product(VALS, repeat=len(names)):
        m = dict(zip(names, vals))
        if all(ev(f, m) in s for s, f in nodes):
            return True
    return False


def entails(prems, concl):
    names = sorted(set().union(atoms(concl), *[atoms(p) for p in prems]))
    for vals in product(VALS, repeat=len(names)):
        m = dict(zip(names, vals))
        if all(ev(p, m) == T for p in prems) and ev(concl, m) != T:
            return False
    return True


def fo_ev(phi, dom, I, env):
    """ZQuant's folds read as a definition: ∀ strict conj over the domain,
    ∃ strict disj; atoms read the interpretation (value T/F/Z)."""
    op = phi[0]
    if op in ("all", "ex"):
        vs = [fo_ev(phi[2], dom, I, {**env, phi[1]: d}) for d in dom]
        if op == "all":
            return T if all(v == T for v in vs) else F
        return T if any(v == T for v in vs) else F
    if op == "not":
        return lift("not", fo_ev(phi[1], dom, I, env))
    if op in BIN:
        return lift(op, fo_ev(phi[1], dom, I, env), fo_ev(phi[2], dom, I, env))
    args = tuple(env.get(t, t) for t in phi[1:])
    return I.get((op,) + args, Z)


def fo_preds(phi, acc=None):
    acc = {} if acc is None else acc
    op = phi[0]
    if op in ("all", "ex"):
        fo_preds(phi[2], acc)
    elif op == "not":
        fo_preds(phi[1], acc)
    elif op in BIN:
        fo_preds(phi[1], acc)
        fo_preds(phi[2], acc)
    else:
        acc[op] = len(phi) - 1
    return acc


def fo_consts(phi, bound=(), acc=None):
    acc = set() if acc is None else acc
    op = phi[0]
    if op in ("all", "ex"):
        fo_consts(phi[2], bound + (phi[1],), acc)
    elif op == "not":
        fo_consts(phi[1], bound, acc)
    elif op in BIN:
        fo_consts(phi[1], bound, acc)
        fo_consts(phi[2], bound, acc)
    else:
        for t in phi[1:]:
            if t not in bound:
                acc.add(t)
    return acc


def fo_interps(forms, dom):
    ar = {}
    for f in forms:
        fo_preds(f, ar)
    cells = [(p,) + args for p, k in sorted(ar.items())
             for args in product(dom, repeat=k)]
    for vals in product(VALS, repeat=len(cells)):
        yield dict(zip(cells, vals))


def fo_countermodel(prems, concl, dom, consts_to=None):
    """Enumerate every interpretation on `dom`; free constants are read as
    the elements `consts_to` maps them to (default: every assignment)."""
    forms = list(prems) + [concl]
    consts = sorted(set().union(*[fo_consts(f) for f in forms]))
    assigns = [consts_to] if consts_to is not None else \
        [dict(zip(consts, c)) for c in product(dom, repeat=len(consts))]
    for env in assigns:
        for I in fo_interps(forms, dom):
            if all(fo_ev(p, dom, I, env) == T for p in prems) and \
                    fo_ev(concl, dom, I, env) != T:
                return (dom, env, I)
    return None


def disposition_of(v, g):
    """The judge's disposition from verdict and grade, as its docstring states it
    (ztljudge.judge; no absent grounds in these documents): hereditary T is EARNED,
    hereditary F is REFUTED, T below hereditary is ON CREDIT, anything else OPEN.
    Added 2026-09-28 when the epoch floor's `survives` moved from the verdict letter
    to the disposition (PR #5, E1) — written from the document, not imported.
    NOT named `disposition`: that name is this oracle's own (phi, m) function, and
    shadowing it broke the backward sweep (295 false disagreements, 2026-09-28)."""
    if g == "hereditary":
        return "EARNED" if v == T else "REFUTED" if v == F else "OPEN"
    return "ON CREDIT" if v == T else "OPEN"
