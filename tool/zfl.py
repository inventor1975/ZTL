# -*- coding: utf-8 -*-
"""
ZFL — Zero-trust Formal Language, v1.

The single design goal: everything valid in ZFL loads into the ZTL core
with no further questions. A ZFL document is JSON:

{
  "genre": "statement" | "system",
  "atoms":     { "rain": {"status": "Z", "note": "прогноз не поверен"} },
  "assert":    "imp(rain, umbrella)",          # statement genre
  "sentences": { "L": "not(Tr(L))" },          # system genre
  "ask": ["verdict", "warranty", "passport", "stipulations"]   # optional
}

Formulas: not(x), and(x,y), or(x,y), imp(x,y), xor(x,y), xnor(x,y),
constants T | F, atom names, and Tr(name) (system genre only).
In the system genre declared atoms become INPUT sentences (defined by
their own status constant) — unverified inputs imported into the system.

This module is deliberately AI-free: parser, validator with
machine-readable errors (the repair loop feeds on them), deterministic
back-reading in Russian (the second, non-hallucinating auditor), and
converters into the ZTL core's native structures.
"""

import json
import re

GENRES = ("statement", "system")
CONNECTIVES = {"not": 1, "and": 2, "or": 2, "imp": 2, "xor": 2, "xnor": 2}
RESERVED = {"T", "F", "Z", "Tr", "not", "and", "or", "imp", "xor", "xnor"}
STATUSES = ("T", "F", "Z")
ASKS = ("verdict", "warranty", "passport", "stipulations")

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
            raise FormulaError(i, f"неожиданный символ «{c}»")
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
            raise FormulaError(p, "формула оборвана")
        if expected and t != expected:
            raise FormulaError(p, f"ожидалось «{expected}», найдено «{t}»")
        pos[0] += 1
        return t, p

    def expr():
        t, p = eat()
        if t in ("(", ")", ","):
            raise FormulaError(p, f"ожидалось имя или связка, найдено «{t}»")
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
                raise FormulaError(np, "Tr ожидает имя предложения")
            eat(")")
            return ("tr", name)
        if t in ("T", "F"):
            return ("const", t)
        if t == "Z":
            raise FormulaError(p, "Z — не константа формул: метку носит атом"
                                  " (объяви атом со status: Z)")
        return ("atom", t)

    tree = expr()
    if pos[0] != len(toks):
        raise FormulaError(toks[pos[0]][1], "лишний хвост после формулы")
    return tree


def walk(tree, kind):
    """All names of the given node kind ('atom' or 'tr')."""
    if tree[0] == kind:
        yield tree[1]
    elif tree[0] in CONNECTIVES:
        for arg in tree[1:]:
            yield from walk(arg, kind)


# ---------------------------------------------------------- validation
def validate(text):
    """→ (doc|None, parsed|None, [errors and warnings])."""
    issues = []
    try:
        doc = json.loads(text)
    except json.JSONDecodeError as e:
        return None, None, [err("E_JSON", f"строка {e.lineno}", str(e.msg))]
    if not isinstance(doc, dict):
        return None, None, [err("E_SCHEMA", "корень", "нужен JSON-объект")]

    genre = doc.get("genre")
    if genre not in GENRES:
        return doc, None, [err("E_GENRE", "genre",
                               f"нужно одно из {GENRES}")]

    atoms = doc.get("atoms", {})
    if not isinstance(atoms, dict):
        return doc, None, [err("E_SCHEMA", "atoms", "нужен объект")]
    for a, spec in atoms.items():
        if a in RESERVED or not NAME_RE.fullmatch(a):
            issues.append(err("E_RESERVED", a,
                              "имя атома: буквы/цифры/_, не зарезервировано"))
        st = spec.get("status") if isinstance(spec, dict) else None
        if st not in STATUSES:
            issues.append(err("E_ATOM_STATUS", a,
                              'у атома нужен "status": "T" | "F" | "Z"'))

    ask = doc.get("ask", [])
    if not isinstance(ask, list):
        issues.append(err("E_TYPE", "ask", "нужен список строк"))
        ask = []
    for a in ask:
        if a not in ASKS:
            issues.append(warn("W_ASK", str(a),
                               f"неизвестный вопрос; знаю {ASKS}"))

    parsed = {}
    if genre == "statement":
        if "assert" not in doc:
            issues.append(err("E_EMPTY", "assert",
                              "в жанре statement нужна формула assert"))
        elif not isinstance(doc["assert"], str):
            issues.append(err("E_TYPE", "assert", "формула — строка"))
        else:
            try:
                tree = parse_formula(doc["assert"])
                parsed["assert"] = tree
                for name in walk(tree, "tr"):
                    issues.append(err("E_TR_IN_STATEMENT", f"Tr({name})",
                                      "Tr() живёт только в жанре system"))
                used = set(walk(tree, "atom"))
                for name in used - set(atoms):
                    issues.append(err("E_UNDEF_ATOM", name,
                                      "объяви атом в atoms со status"))
                for name in set(atoms) - used:
                    issues.append(warn("W_UNUSED_ATOM", name,
                                       "атом объявлен, но не используется"))
            except FormulaError as e:
                issues.append(err("E_FORMULA", f"assert, позиция {e.pos}",
                                  e.msg))
    else:  # system
        sentences = doc.get("sentences", {})
        if not isinstance(sentences, dict) or not sentences:
            issues.append(err("E_EMPTY", "sentences",
                              "в жанре system нужны sentences"))
            sentences = {}
        names = set(sentences) | set(atoms)
        for n in sentences:
            if n in RESERVED or not NAME_RE.fullmatch(n):
                issues.append(err("E_RESERVED", n, "имя предложения"
                                  " не должно быть зарезервированным"))
            if n in atoms:
                issues.append(err("E_NAME_CLASH", n,
                                  "имя и в atoms, и в sentences"))
        parsed["sentences"] = {}
        for n, f in sentences.items():
            if not isinstance(f, str):
                issues.append(err("E_TYPE", n, "формула — строка"))
                continue
            try:
                tree = parse_formula(f)
                parsed["sentences"][n] = tree
                for m in walk(tree, "tr"):
                    if m not in names:
                        issues.append(err("E_UNDEF_SENTENCE", f"Tr({m})",
                                          "нет такого предложения или атома"))
                for m in walk(tree, "atom"):
                    issues.append(err("E_BARE_ATOM", f"{n}: {m}",
                                      "в system ссылки пишутся как Tr(имя);"
                                      " голые атомы запрещены"))
            except FormulaError as e:
                issues.append(err("E_FORMULA", f"{n}, позиция {e.pos}",
                                  e.msg))

    fatal = [i for i in issues if i["level"] == "error"]
    return doc, (None if fatal else parsed), issues


# ----------------------------------------------- deterministic back-reading
RU_STATUS = {"T": "поверен: истина", "F": "поверен: ложь",
             "Z": "НЕ поверен (метка Z)"}


def say(tree, system=False):
    op = tree[0]
    if op == "const":
        return "истина" if tree[1] == "T" else "ложь"
    if op == "atom":
        return f"«{tree[1]}»"
    if op == "tr":
        return f"истинно «{tree[1]}»"
    a = [say(x, system) for x in tree[1:]]
    if op == "not":
        return f"не ({a[0]})"
    if op == "and":
        return f"({a[0]} и {a[1]})"
    if op == "or":
        return f"({a[0]} или {a[1]})"
    if op == "imp":
        return f"(если {a[0]}, то {a[1]})"
    if op == "xor":
        return f"({a[0]} либо {a[1]}, но не оба)"
    return f"({a[0]} тогда и только тогда, когда {a[1]})"


def back_reading(doc, parsed):
    """Template verbalization of what is ACTUALLY written — no AI."""
    lines = []
    atoms = doc.get("atoms", {})
    for a, spec in atoms.items():
        note = spec.get("note", "")
        lines.append(f"Атом «{a}» — {RU_STATUS.get(spec.get('status'), '?')}"
                     + (f" ({note})" if note else "") + ".")
    if doc["genre"] == "statement":
        lines.append(f"Утверждается: {say(parsed['assert'])}.")
    else:
        for n, tree in parsed["sentences"].items():
            lines.append(f"Предложение «{n}» утверждает: {say(tree, True)}.")
        if atoms:
            lines.append("Атомы входят в систему как непроверенные/поверенные"
                         " входы.")
    ask = doc.get("ask") or list(ASKS)
    lines.append("Вопрос: " + ", ".join(ask) + ".")
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
