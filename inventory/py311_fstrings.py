# -*- coding: utf-8 -*-
"""py311_fstrings — the f-string forms Python 3.12 accepts and the CI's Python 3.11 refuses (2026-11-05).

WHY. CI runs Python 3.11 (.github/workflows/regression.yml); this machine runs 3.12, whose f-strings (PEP 701) also
accept, inside a replacement field, a backslash in a string, the enclosing quote reused, and a comment. 3.11 refuses
all three with a SyntaxError. On 2026-11-05 one `re.sub(r'\\s+', ...)` inside an f-string (zfl.py, 6ffb732) turned
the remote regression red for a whole evening while every local run said ALL GREEN — local green is not remote green.
This scan runs in preflight, so the next one is caught before it is pushed.

A SELF-TEST first: the scanner must flag each of the three forms in a sample written for it, and pass a clean one —
a scanner that finds nothing on a clean repository proves nothing by itself.

Run:  python3 inventory/py311_fstrings.py      -> PY311 FSTRINGS GREEN, or the offending file:line list and exit 1
"""
import io
import pathlib
import re
import sys
import tokenize

ROOT = pathlib.Path(__file__).resolve().parent.parent
SKIP = {".lake", ".git", "venv", ".venv", "node_modules", "_attic", "__pycache__"}


def _quote(s):
    m = re.match(r"[rRbBuUfF]*('''|\"\"\"|'|\")", s)
    return m.group(1) if m else None


def scan_source(src):
    """-> [(line, what)] for every 3.12-only form inside an f-string replacement field"""
    out = []
    stack = []                                   # [quote, brace depth] per open f-string
    for t in tokenize.generate_tokens(io.StringIO(src).readline):
        if t.type == tokenize.FSTRING_START:
            if stack and stack[-1][1] > 0 and _quote(t.string) == stack[-1][0]:
                out.append((t.start[0], "a nested f-string reuses the enclosing quote"))
            stack.append([_quote(t.string), 0])
        elif t.type == tokenize.FSTRING_END:
            stack.pop()
        elif stack and t.type == tokenize.OP and t.string == "{":
            stack[-1][1] += 1
        elif stack and t.type == tokenize.OP and t.string == "}":
            stack[-1][1] -= 1
        elif stack and stack[-1][1] > 0 and t.type == tokenize.STRING:
            if "\\" in t.string:
                out.append((t.start[0], "a backslash in a string inside the expression"))
            if _quote(t.string) == stack[-1][0]:
                out.append((t.start[0], "the enclosing quote reused inside the expression"))
        elif stack and stack[-1][1] > 0 and t.type == tokenize.COMMENT:
            out.append((t.start[0], "a comment inside the expression"))
    return out


def self_test():
    bad = {
        "backslash": "x = f\"{re.sub(r'\\s+', '', v)}\"\n",
        "same quote": "x = f\"{d[\"k\"]}\"\n",
        "comment": "x = f\"{(1  # c\n)}\"\n",
    }
    for name, src in bad.items():
        assert scan_source(src), f"the scanner missed: {name}"
    assert scan_source("x = f\"{d['k']}\" + f'{v!r:>10}'\nvalue = re.sub(r'\\s+', '', v)\n") == []


def main_compile():
    """Python < 3.12 (the CI itself): an f-string is one token there, so the 3.12-only forms cannot be found by
    tokens — but this Python refuses them outright, so compiling every file IS the check. Self-tested the same way:
    each bad sample must fail to compile, the clean one must compile."""
    bad = ["x = f\"{re.sub(r'\\s+', '', v)}\"\n", "x = f\"{d[\"k\"]}\"\n", "x = f\"{(1  # c\n)}\"\n"]
    for src in bad:
        try:
            compile(src, "<sample>", "exec")
        except SyntaxError:
            continue
        raise AssertionError(f"this Python compiled a 3.12-only sample: {src!r}")
    compile("x = f\"{d['k']}\" + f'{v!r:>10}'\n", "<sample>", "exec")
    found = []
    for f in sorted(ROOT.rglob("*.py")):
        if SKIP & set(f.relative_to(ROOT).parts):
            continue
        try:
            src = f.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        try:
            compile(src, str(f), "exec")
        except SyntaxError as e:
            if "f-string" in str(e):
                found.append((f.relative_to(ROOT), e.lineno, str(e.msg)))
    for path, line, what in found:
        print(f"   {path}:{line}: {what}")
    if found:
        print(f"PY311 FSTRINGS RED — {len(found)} f-string(s) this Python cannot parse")
        sys.exit(1)
    print(f"PY311 FSTRINGS GREEN — every file compiles under Python {sys.version_info[0]}.{sys.version_info[1]}; "
          "the self-test's 3.12-only samples were refused")


def main():
    if not hasattr(tokenize, "FSTRING_START"):
        return main_compile()
    self_test()
    found = []
    for f in sorted(ROOT.rglob("*.py")):
        if SKIP & set(f.relative_to(ROOT).parts):
            continue
        try:
            src = f.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        try:
            hits = scan_source(src)
        except (tokenize.TokenError, SyntaxError, IndentationError):
            continue
        found += [(f.relative_to(ROOT), line, what) for line, what in hits]
    for path, line, what in found:
        print(f"   {path}:{line}: {what} — refused by Python 3.11 (CI)")
    if found:
        print(f"PY311 FSTRINGS RED — {len(found)} form(s) the CI's Python 3.11 cannot parse")
        sys.exit(1)
    print("PY311 FSTRINGS GREEN — no 3.12-only f-string form; the self-test caught all three on its samples")


if __name__ == "__main__":
    main()
