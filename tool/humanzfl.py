# -*- coding: utf-8 -*-
"""
Human ZFL — a keyboard-friendly surface syntax for statements, so a person
writes a line, not JSON. The JSON stays under the hood (zfl.py).

    a=F assert (d iff !c) impl ((b impl a) impl (b iff c))

Rules:
  * `assert` separates the verified-atom header from the claim.
  * status only for VERIFIED atoms (`a=F`, `b=T`); everything unnamed is Z
    (unverified) — the ZTL default.
  * `w has no subject` DECLARES ABSENCE, and it is not `w=F` nor a boundary.
    `w=F` says the ground is false; a boundary says a reading is out of view;
    this says there is no ground to read at all. The judge keeps the three
    apart because they owe different things: `F` owes nothing, an unverified
    ground owes a check, and an absent one owes a REPAIR — no amount of
    checking will reach it. "The weapon has not been identified" leaves the
    question open; "no weapon was entered into the case" closes the order.
    A declaration of absence is billed: the report says which settlement it
    removed, so it cannot be used as a quiet way to stop being asked.

  * `b excludes T` DECLARES A BOUNDARY: `b` stays unverified, but the reading
    `b=T` is not admitted. The word is long on purpose. `b != T` would read as
    a claim about how things ARE — and that claim is `b=F`, which the language
    already has. This says something else: which completions are IN VIEW at
    all.

    That distinction is what lets the studio serve constructed worlds and not
    only the physical one. A jurisdiction may decline to consider a reading; a
    hypothesis may set one aside; a fiction may never contain it. In none of
    those cases is the reading false — it is out of view, and the two are not
    the same. So a boundary is a premise, never a discovery, and the engine
    prints what it costs: which readings it removed, and whether any of them
    would have changed the verdict. If it removes every reading, the answer is
    E — nothing to read — because a world with no admissible readings is not a
    world.
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
    # Boundaries first, so `b excludes T` is not read as the atom `excludes`.
    excluded = {}
    for a, st in re.findall(
            r"([A-Za-z_][A-Za-z0-9_]*)\s+excludes\s+([TFtf])\b", header, re.I):
        excluded.setdefault(a, set()).add(st.upper())
    header_wo_bounds = re.sub(
        r"[A-Za-z_][A-Za-z0-9_]*\s+excludes\s+[TFtf]\b", " ", header, flags=re.I)
    # `w has no subject` DECLARES ABSENCE: not "nobody checked w" but "there is
    # no w to check". The judge treats the two differently — the first keeps a
    # verification order open, the second cannot be filled at all — so the
    # surface language has to be able to say which one is meant.
    absent = set(re.findall(
        r"([A-Za-z_][A-Za-z0-9_]*)\s+has\s+no\s+subject\b",
        header_wo_bounds, re.I))
    header_wo_bounds = re.sub(
        r"[A-Za-z_][A-Za-z0-9_]*\s+has\s+no\s+subject\b", " ",
        header_wo_bounds, flags=re.I)
    declared = {a: st.upper() for a, st in
                re.findall(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([TFZtfz])",
                           header_wo_bounds)}
    declared.update({a: "E" for a in absent})
    tree = _parse_formula(formula)
    atoms = {a: {"status": declared.get(a, "Z")}
             for a in _atoms_in_order(tree, [])}
    doc = {"genre": "statement", "atoms": atoms, "assert": _to_prefix(tree)}
    if excluded:
        doc["boundary"] = {a: sorted(v) for a, v in excluded.items()}
    return doc


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
