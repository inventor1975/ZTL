# -*- coding: utf-8 -*-
"""
ZFL — Zero-trust Formal Language, v1.

The single design goal: everything valid in ZFL loads into the ZTL core
with no further questions. A ZFL document is JSON:

{
  "genre": "statement" | "system",
  "atoms":     { "rain": {"status": "Z", "means": "it is raining",
                          "note": "forecast unverified"} },
  "assert":    "imp(rain, umbrella)",          # statement genre
  "sentences": { "L": "not(Tr(L))" },          # system genre
  "ask": ["verdict", "warranty", "passport", "stipulations"]   # optional
}

Formulas: not(x), and(x,y), or(x,y), imp(x,y), xor(x,y), xnor(x,y),
constants T | F, atom names, and Tr(name) (system genre only).
In the system genre declared atoms become INPUT sentences (defined by
their own status constant) — unverified inputs imported into the system.

The optional "means" gloss states what T of the atom MEANS. It is the
polarity auditor: names lie (`fresh` already means "not revoked", so
"not fresh" asserts a positive fact), glosses do not. The validator
warns on a negated atom whose gloss is itself negative
(W_DOUBLE_NEGATION_MEANING) and on a missing gloss (W_NO_GLOSS), and
the back-reading verbalizes the formula by MEANING as well as by name —
so a name/meaning mismatch is visible before the run, not in review.

This module is deliberately AI-free: parser, validator with
machine-readable errors (the repair loop feeds on them), a
deterministic back-reading (the second, non-hallucinating auditor),
and converters into the ZTL core's native structures.
"""

import json
import re

GENRES = ("statement", "system")
CONNECTIVES = {"not": 1, "and": 2, "or": 2, "imp": 2, "xor": 2, "xnor": 2}
RESERVED = {"T", "F", "Z", "Tr", "not", "and", "or", "imp", "xor", "xnor"}
STATUSES = ("T", "F", "Z")
ASKS = ("verdict", "warranty", "passport", "stipulations")

# Cyrillic stays in NAME_RE on purpose: atom names may be in any language
NAME_RE = re.compile(r"[A-Za-zА-Яа-яЁё_][A-Za-zА-Яа-яЁё_0-9]*")


def err(code, where, hint):
    return {"level": "error", "code": code, "where": where, "hint": hint}


def warn(code, where, hint):
    return {"level": "warning", "code": code, "where": where, "hint": hint}


# ------------------------------------------------------------- parser
class FormulaError(Exception):
    def __init__(self, pos, msg):
        super().__init__(msg)
        self.pos = pos
        self.msg = msg


def tokenize(s):
    toks, i = [], 0
    while i < len(s):
        c = s[i]
        if c.isspace():
            i += 1
            continue
        if c in "(),":
            toks.append((c, i))
            i += 1
            continue
        m = NAME_RE.match(s, i)
        if not m:
            raise FormulaError(i, f"unexpected character '{c}'")
        toks.append((m.group(0), i))
        i = m.end()
    return toks


def parse_formula(s):
    """→ nested tuples: ('const','T'|'F') | ('atom',name) | ('tr',name)
    | (conn, arg[, arg])."""
    toks = tokenize(s)
    pos = [0]

    def peek():
        return toks[pos[0]] if pos[0] < len(toks) else (None, len(s))

    def eat(expected=None):
        t, p = peek()
        if t is None:
            raise FormulaError(p, "formula ends abruptly")
        if expected and t != expected:
            raise FormulaError(p, f"expected '{expected}', found '{t}'")
        pos[0] += 1
        return t, p

    def expr():
        t, p = eat()
        if t in ("(", ")", ","):
            raise FormulaError(p, f"expected a name or a connective, found '{t}'")
        if t in CONNECTIVES:
            eat("(")
            args = [expr()]
            for _ in range(CONNECTIVES[t] - 1):
                eat(",")
                args.append(expr())
            eat(")")
            return (t, *args)
        if t == "Tr":
            eat("(")
            name, np = eat()
            if not NAME_RE.fullmatch(name):
                raise FormulaError(np, "Tr expects a sentence name")
            eat(")")
            return ("tr", name)
        if t in ("T", "F"):
            return ("const", t)
        if t == "Z":
            raise FormulaError(p, "Z is not a formula constant: the mark lives on an atom"
                                  " (declare an atom with status: Z)")
        return ("atom", t)

    tree = expr()
    if pos[0] != len(toks):
        raise FormulaError(toks[pos[0]][1], "trailing garbage after the formula")
    return tree


def degenerates(tree):
    """xor/xnor with syntactically identical arguments — almost always
    a mis-encoded biconditional definition."""
    if tree[0] in ("xor", "xnor") and tree[1] == tree[2]:
        yield tree[0]
    if tree[0] in CONNECTIVES:
        for arg in tree[1:]:
            yield from degenerates(arg)


def walk(tree, kind):
    """All names of the given node kind ('atom' or 'tr')."""
    if tree[0] == kind:
        yield tree[1]
    elif tree[0] in CONNECTIVES:
        for arg in tree[1:]:
            yield from walk(arg, kind)


# --- the polarity auditor (the 2026-07-19 lesson) -------------------------
# An atom is a bare string to the core; nothing stops a formula from saying
# "not fresh" while the prose says "not revoked" — opposite polarities,
# since `fresh` ALREADY MEANS "not revoked". The cure is a gloss: what does
# T of this atom MEAN. Then two things become mechanical: the back-reading
# speaks meanings instead of names, and an atom whose meaning is already
# negative gets flagged when it appears under a negation.
_NEG_MARKERS = ("no ", "not ", "never", "none", "without", "absen", "lack",
                "free of", "нет", "не ", "без", "отсут", "отриц")


def negative_gloss(text):
    """Heuristic: does this gloss state a NEGATIVE fact? (auditor aid only)"""
    t = " " + (text or "").strip().lower()
    return any(m in t for m in _NEG_MARKERS)


def negated_atoms(tree):
    """Atom names appearing directly under a negation."""
    if tree[0] == "not":
        sub = tree[1]
        if sub[0] == "atom":
            yield sub[1]
        yield from negated_atoms(sub)
    elif tree[0] in CONNECTIVES:
        for arg in tree[1:]:
            yield from negated_atoms(arg)


# ---------------------------------------------------------- validation
def validate(text):
    """→ (doc|None, parsed|None, [errors and warnings])."""
    issues = []
    try:
        doc = json.loads(text)
    except json.JSONDecodeError as e:
        return None, None, [err("E_JSON", f"line {e.lineno}", str(e.msg))]
    if not isinstance(doc, dict):
        return None, None, [err("E_SCHEMA", "root", "a JSON object is required")]

    genre = doc.get("genre")
    if genre not in GENRES:
        return doc, None, [err("E_GENRE", "genre",
                               f"must be one of {GENRES}")]

    atoms = doc.get("atoms", {})
    if not isinstance(atoms, dict):
        return doc, None, [err("E_SCHEMA", "atoms", "an object is required")]
    for a, spec in atoms.items():
        if a in RESERVED or not NAME_RE.fullmatch(a):
            issues.append(err("E_RESERVED", a,
                              "atom name: letters/digits/_, not a reserved word"))
        st = spec.get("status") if isinstance(spec, dict) else None
        if st not in STATUSES:
            issues.append(err("E_ATOM_STATUS", a,
                              'an atom needs "status": "T" | "F" | "Z"'))

    ask = doc.get("ask", [])
    if not isinstance(ask, list):
        issues.append(err("E_TYPE", "ask", "a list of strings is required"))
        ask = []
    for a in ask:
        if a not in ASKS:
            issues.append(warn("W_ASK", str(a),
                               f"unknown ask; I know {ASKS}"))

    parsed = {}
    if genre == "statement":
        if "assert" not in doc:
            issues.append(err("E_EMPTY", "assert",
                              "the statement genre requires an assert formula"))
        elif not isinstance(doc["assert"], str):
            issues.append(err("E_TYPE", "assert", "a formula must be a string"))
        else:
            try:
                tree = parse_formula(doc["assert"])
                parsed["assert"] = tree
                for opd in degenerates(tree):
                    issues.append(warn("W_DEGENERATE", f"assert: {opd}(A,A)",
                                       "constant-like; a biconditional "
                                       "definition 'X iff Φ' is written as "
                                       "X := Φ, e.g. not(Tr(X))"))
                for name in walk(tree, "tr"):
                    issues.append(err("E_TR_IN_STATEMENT", f"Tr({name})",
                                      "Tr() lives only in the system genre"))
                used = set(walk(tree, "atom"))
                for name in used - set(atoms):
                    issues.append(err("E_UNDEF_ATOM", name,
                                      "declare the atom in atoms with a status"))
                for name in set(atoms) - used:
                    issues.append(warn("W_UNUSED_ATOM", name,
                                       "the atom is declared but unused"))
                # --- the polarity audit: names lie, glosses do not ---
                for name in used:
                    spec = atoms.get(name)
                    gloss = (spec.get("means") if isinstance(spec, dict)
                             else None)
                    if not gloss:
                        issues.append(warn(
                            "W_NO_GLOSS", name,
                            'no "means" gloss — state what T of this atom '
                            'MEANS, so the polarity can be audited '
                            '(e.g. "means": "the ground was revoked")'))
                for name in set(negated_atoms(tree)):
                    spec = atoms.get(name)
                    gloss = (spec.get("means") if isinstance(spec, dict)
                             else None)
                    if gloss and negative_gloss(gloss):
                        issues.append(warn(
                            "W_DOUBLE_NEGATION_MEANING", name,
                            f'the atom is negated in the formula, but its '
                            f'gloss is already negative ("{gloss}") — '
                            f'"not {name}" therefore asserts a POSITIVE '
                            f'fact; check that this is the polarity you '
                            f'mean'))
            except FormulaError as e:
                issues.append(err("E_FORMULA", f"assert, position {e.pos}",
                                  e.msg))
        # --- the temporal extension (E24): an optional verification
        # timeline — logical time, one tick = one verified atom ---
        tl = doc.get("timeline")
        if tl is not None:
            if not isinstance(tl, list):
                issues.append(err("E_TL_TYPE", "timeline",
                                  'a list of {"atom": name, "value": "T"|"F"}'))
            else:
                seen_ticks = set()
                for i, ev_ in enumerate(tl):
                    where = f"timeline[{i}]"
                    if not isinstance(ev_, dict) or \
                            set(ev_) != {"atom", "value"}:
                        issues.append(err("E_TL_TYPE", where,
                                          'each tick is {"atom": ..., '
                                          '"value": "T"|"F"}'))
                        continue
                    a, v = ev_["atom"], ev_["value"]
                    if a not in atoms:
                        issues.append(err("E_TL_ATOM", where,
                                          f"unknown atom '{a}' — declare it"))
                        continue
                    if v not in ("T", "F"):
                        issues.append(err("E_TL_VALUE", where,
                                          "a verification earns T or F"))
                    spec = atoms[a]
                    st = spec.get("status") if isinstance(spec, dict) else None
                    if st in ("T", "F"):
                        issues.append(err("E_TL_GROUND", where,
                                          f"'{a}' is already ground —"
                                          " only a mark (Z) can be verified"))
                    if a in seen_ticks:
                        issues.append(err("E_TL_REPEAT", where,
                                          f"'{a}' is verified twice —"
                                          " a mark resolves once"))
                    seen_ticks.add(a)
    else:  # system
        if doc.get("timeline") is not None:
            issues.append(err("E_TL_GENRE", "timeline",
                              "the timeline lives in the statement genre"))
        sentences = doc.get("sentences", {})
        if not isinstance(sentences, dict) or not sentences:
            issues.append(err("E_EMPTY", "sentences",
                              "the system genre requires sentences"))
            sentences = {}
        names = set(sentences) | set(atoms)
        for n in sentences:
            if n in RESERVED or not NAME_RE.fullmatch(n):
                issues.append(err("E_RESERVED", n, "a sentence name"
                                  " must not be a reserved word"))
            if n in atoms:
                issues.append(err("E_NAME_CLASH", n,
                                  "the name is both in atoms and in sentences"))
        parsed["sentences"] = {}
        for n, f in sentences.items():
            if not isinstance(f, str):
                issues.append(err("E_TYPE", n, "a formula must be a string"))
                continue
            try:
                tree = parse_formula(f)
                parsed["sentences"][n] = tree
                for opd in degenerates(tree):
                    issues.append(warn("W_DEGENERATE", f"{n}: {opd}(A,A)",
                                       "constant-like; 'X iff not X' is "
                                       "the definition X := not(Tr(X))"))
                for m in walk(tree, "tr"):
                    if m not in names:
                        issues.append(err("E_UNDEF_SENTENCE", f"Tr({m})",
                                          "no such sentence or atom"))
                for m in walk(tree, "atom"):
                    issues.append(err("E_BARE_ATOM", f"{n}: {m}",
                                      "in the system genre references are written as"
                                      " Tr(name); bare atoms are forbidden"))
            except FormulaError as e:
                issues.append(err("E_FORMULA", f"{n}, position {e.pos}",
                                  e.msg))

    fatal = [i for i in issues if i["level"] == "error"]
    return doc, (None if fatal else parsed), issues


# ----------------------------------------------- deterministic back-reading
STATUS_TXT = {"T": "verified: true", "F": "verified: false",
              "Z": "UNVERIFIED (mark Z)"}


def say(tree, system=False, glosses=None):
    op = tree[0]
    if op == "const":
        return "truth" if tree[1] == "T" else "falsehood"
    if op == "atom":
        if glosses and tree[1] in glosses:
            return f"[{glosses[tree[1]]}]"
        return f"\u201c{tree[1]}\u201d"
    if op == "tr":
        return f"\u201c{tree[1]}\u201d is true"
    a = [say(x, system, glosses) for x in tree[1:]]
    if op == "not":
        return f"not ({a[0]})"
    if op == "and":
        return f"({a[0]} and {a[1]})"
    if op == "or":
        return f"({a[0]} or {a[1]})"
    if op == "imp":
        return f"(if {a[0]} then {a[1]})"
    if op == "xor":
        return f"({a[0]} or {a[1]}, but not both)"
    return f"({a[0]} if and only if {a[1]})"


def back_reading(doc, parsed):
    """Template verbalization of what is ACTUALLY written — no AI."""
    lines = []
    atoms = doc.get("atoms", {})
    for a, spec in atoms.items():
        note = spec.get("note", "")
        gloss = spec.get("means", "")
        lines.append(f"Atom \u201c{a}\u201d \u2014 "
                     f"{STATUS_TXT.get(spec.get('status'), '?')}"
                     + (f"; T means: {gloss}" if gloss else "")
                     + (f" ({note})" if note else "") + ".")
    if doc["genre"] == "statement":
        lines.append(f"Asserted: {say(parsed['assert'])}.")
        gl = {a: spec.get("means") for a, spec in atoms.items()
              if isinstance(spec, dict) and spec.get("means")}
        if gl:
            lines.append("Read by meaning: "
                         + say(parsed["assert"], glosses=gl) + ".")
    else:
        for n, tree in parsed["sentences"].items():
            lines.append(f"Sentence \u201c{n}\u201d asserts: "
                         f"{say(tree, True)}.")
        if atoms:
            lines.append("The atoms enter the system as"
                         " verified/unverified inputs.")
    ask = doc.get("ask") or list(ASKS)
    lines.append("Asked: " + ", ".join(ask) + ".")
    return "\n".join(lines)


# ------------------------------------------------- converters to the core
def to_core_formula(tree):
    """ZFL tree → the ztl.py tuple/string format."""
    op = tree[0]
    if op == "const":
        return tree[1]                       # "T"/"F" literals
    if op == "atom" or op == "tr":
        return tree[1]                       # atom name string
    return (op,) + tuple(to_core_formula(x) for x in tree[1:])


def to_statement(doc, parsed):
    env = {a: spec["status"] for a, spec in doc.get("atoms", {}).items()}
    return env, to_core_formula(parsed["assert"])


def to_system(doc, parsed):
    system = {n: to_core_formula(t) for n, t in parsed["sentences"].items()}
    for a, spec in doc.get("atoms", {}).items():
        system[a] = spec["status"]           # INPUT sentences: constant defs
    return system
