# -*- coding: utf-8 -*-
"""
Human ZFL — a keyboard-friendly surface syntax for statements, so a person
writes a line, not JSON. The JSON stays under the hood (zfl.py).

    a=F assert (d iff !c) impl ((b impl a) impl (b iff c))

Rules:
  * `assert` separates the verified-atom header from the claim.
  * status only for VERIFIED atoms (`a=F`, `b=T`); everything unnamed is Z
    (unverified) — the ZTL default.
  * word operators, infix, fully parenthesised except the top:
        !x / not x   → not      x and y   → and     x or y   → or
        x impl y     → imp      x xor y   → xor
        x iff y / x nxor y      → xnor
"""

import re

# surface word → core connective
BINOP = {"and": "and", "or": "or", "impl": "imp", "imp": "imp",
         "xor": "xor", "nxor": "xnor", "iff": "xnor", "xnor": "xnor"}
NEG = {"!", "not"}
# core → surface (for rendering back), the readable choices
SHOWBIN = {"and": "and", "or": "or", "imp": "impl", "xor": "xor",
           "xnor": "iff"}


def _tokenize(s):
    return re.findall(r"[()!]|[A-Za-z_][A-Za-z0-9_]*", s)


def _parse_formula(s):
    """Infix words + parens → core tuple. Nested binaries must be
    parenthesised; the top level may be `operand OP operand` bare."""
    toks = _tokenize(s)
    pos = 0

    def operand():
        nonlocal pos
        if pos >= len(toks):
            raise ValueError("формула обрывается")
        t = toks[pos]
        if t in NEG:
            pos += 1
            return ("not", operand())
        if t == "(":
            pos += 1
            e = expr()
            if pos >= len(toks) or toks[pos] != ")":
                raise ValueError("не закрыта скобка")
            pos += 1
            return e
        if t == ")":
            raise ValueError("лишняя )")
        pos += 1
        return t                       # an atom name

    def expr():
        nonlocal pos
        left = operand()
        if pos < len(toks) and toks[pos] in BINOP:
            op = toks[pos]; pos += 1
            right = operand()
            return (BINOP[op], left, right)
        return left

    tree = expr()
    if pos != len(toks):
        raise ValueError(f"не разобрано у '{toks[pos]}' — не хватает скобок?")
    return tree


def _to_prefix(t):
    if isinstance(t, str):
        return t
    if t[0] == "not":
        return f"not({_to_prefix(t[1])})"
    return f"{t[0]}({_to_prefix(t[1])},{_to_prefix(t[2])})"


def _atoms_in_order(t, acc):
    if isinstance(t, str):
        if t not in ("T", "F") and t not in acc:
            acc.append(t)
    else:
        for x in t[1:]:
            _atoms_in_order(x, acc)
    return acc


def human_to_doc(text):
    """The human line → the zfl.py document (dict). Raises ValueError."""
    parts = re.split(r"\bassert\b", text, maxsplit=1, flags=re.I)
    if len(parts) != 2:
        raise ValueError("нужно ключевое слово 'assert' между статусами и формулой")
    header, formula = parts
    declared = {a: st.upper() for a, st in
                re.findall(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([TFZtfz])", header)}
    tree = _parse_formula(formula)
    atoms = {a: {"status": declared.get(a, "Z")}
             for a in _atoms_in_order(tree, [])}
    return {"genre": "statement", "atoms": atoms, "assert": _to_prefix(tree)}


# ---- reverse: document → human line (for display / editing) ----------------
def _render(t):
    if isinstance(t, str):
        return t
    if t[0] == "not":
        c = t[1]
        return "!" + (_render(c) if isinstance(c, str) else _render(c))
    return f"({_render(t[1])} {SHOWBIN[t[0]]} {_render(t[2])})"


def _parse_prefix(s):
    """core prefix string → tuple (mirror of zfl's grammar, minimal)."""
    toks = re.findall(r"[(),]|[A-Za-z_][A-Za-z0-9_]*", s)
    pos = 0

    def node():
        nonlocal pos
        t = toks[pos]; pos += 1
        if pos < len(toks) and toks[pos] == "(":
            pos += 1
            args = [node()]
            while toks[pos] == ",":
                pos += 1
                args.append(node())
            pos += 1                    # )
            return (t, *args)
        return t
    return node()


def doc_to_human(doc):
    """The zfl.py document → the human line."""
    verified = " ".join(f"{a}={spec.get('status')}"
                        for a, spec in doc.get("atoms", {}).items()
                        if spec.get("status") in ("T", "F"))
    body = _render(_parse_prefix(doc["assert"]))
    if body.startswith("(") and body.endswith(")"):
        body = body[1:-1]              # drop the outer parens at top
    head = (verified + " ") if verified else ""
    return f"{head}assert {body}"


if __name__ == "__main__":
    demo = "a=F assert (d iff !c) impl ((b impl a) impl (b iff c))"
    doc = human_to_doc(demo)
    import json
    print("human →", demo)
    print("JSON  →", json.dumps(doc, ensure_ascii=False))
    print("back  →", doc_to_human(doc))
