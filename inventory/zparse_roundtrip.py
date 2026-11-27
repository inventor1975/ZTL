# -*- coding: utf-8 -*-
"""
The judge's parser (`ztljudge.formalize`) against its printers — the translation text → formula, checked both ways
(2026-11-27, the curator's audit «каждая деталь судьи — теорема»; a parser is a translation: it is checked by a round
trip, not proved).

  1. UNICODE, fully parenthesised (`ztljudge._show`): parse(show(φ)) == φ for 3000 seeded random formulas, atoms with
     Latin, Cyrillic, digits and underscores;
  2. ASCII, fully parenthesised (~ & | -> ^ = <->): the same;
  3. MINIMAL parentheses by the documented precedence (`_PREC`: ↔ 1 < → 2 < ⊕ 3 < ∨ 4 < ∧ 5) and LEFT association at
     equal precedence: the same — so the precedence table and the association the parser implements are the ones
     written down (→ is LEFT-associative here: a → b → c is (a → b) → c; said, since many texts take it to the right);
  4. REFUSALS: an unclosed '(', a trailing token, an empty text, a dangling operator, a stray character — each
     raises ValueError, never parses to something;
  5. MUTATION: a printer that drops the parentheses a lower-precedence right operand needs -> some formula comes back
     different.

Run:  python3 inventory/zparse_roundtrip.py   -> ZPARSE ROUNDTRIP GREEN
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import ztljudge as J                   # noqa: E402

OPS = ["and", "or", "imp", "xor", "xnor"]
ASCII = {"and": "&", "or": "|", "imp": "->", "xor": "^", "xnor": "<->"}
PREC = J._PREC
NAMES = ["a", "b2", "x_1", "ok", "давление", "т_3", "p", "q"]


def gen(rnd, d):
    if d == 0 or rnd.random() < 0.25:
        return rnd.choice(NAMES)
    if rnd.random() < 0.2:
        return ("not", gen(rnd, d - 1))
    return (rnd.choice(OPS), gen(rnd, d - 1), gen(rnd, d - 1))


def ascii_full(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "~" + ascii_full(phi[1])
    return f"({ascii_full(phi[1])} {ASCII[phi[0]]} {ascii_full(phi[2])})"


def minimal(phi, broken=False):
    """fewest parentheses: a binary child is wrapped when its precedence is lower, or, on the RIGHT, equal (left
    association); a negated compound is wrapped"""
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        c = phi[1]
        return "~" + (minimal(c, broken) if isinstance(c, str) or c[0] == "not" else f"({minimal(c, broken)})")
    op, l, r = phi
    def wrap(c, right):
        if isinstance(c, str) or c[0] == "not":
            return minimal(c, broken)
        need = PREC[c[0]] < PREC[op] or (right and PREC[c[0]] == PREC[op])
        if broken and right:
            need = False
        return f"({minimal(c, broken)})" if need else minimal(c, broken)
    return f"{wrap(l, False)} {ASCII[op]} {wrap(r, True)}"


def main():
    rnd = random.Random(20261127)
    fs = [gen(rnd, 4) for _ in range(3000)]
    res = {}
    for label, printer in (("unicode full", J._show), ("ascii full", ascii_full), ("minimal", minimal)):
        ok = sum(1 for f in fs if J.formalize(printer(f)) == f)
        res[label] = ok
        print(f"  {label:13s} parse(print(φ)) == φ: {ok}/{len(fs)}")
    bad_texts = ["(a & b", "a & b)", "", "a &", "& a", "a b", "a $ b", "~", "()"]
    refused = 0
    for t in bad_texts:
        try:
            J.formalize(t)
        except ValueError:
            refused += 1                  # only ValueError counts: a crash of another kind is a defect, not a refusal
    print(f"  refusals: {refused}/{len(bad_texts)} malformed texts raise")
    assoc = J.formalize("a -> b -> c") == ("imp", ("imp", "a", "b"), "c")
    print(f"  → associates to the LEFT: {assoc}")
    mut = sum(1 for f in fs if J.formalize(minimal(f, broken=True)) != f)
    print(f"  mutation (right-operand parentheses dropped): {mut} formulas come back different")
    if all(v == len(fs) for v in res.values()) and refused == len(bad_texts) and assoc and mut > 0:
        print("ZPARSE ROUNDTRIP GREEN")
    else:
        print("ZPARSE ROUNDTRIP RED"); sys.exit(1)


if __name__ == "__main__":
    main()
