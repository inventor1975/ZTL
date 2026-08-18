# -*- coding: utf-8 -*-
"""
Does every tracked file parse on the Python CI actually runs?

WHY THIS EXISTS. On 2026-08-18 CI went red on `db/probe_ledger.py` with
"SyntaxError: unterminated string literal (detected at line 310)" — a file
nobody had touched, in a run that was ALL GREEN on the author's machine
minutes earlier. The cause: an f-string whose replacement field spanned three
lines. Python allows that from 3.12 (PEP 701); CI runs 3.11, whose tokenizer
does not. `inventory/note_claims.py` then failed too, because it runs the
probes by subprocess — one incompatibility, two red stands.

This is the same lesson `dilemmas/cogito.py` taught in a different costume:
**green on one machine is not a result.** There it was a file present in the
author's tree and absent from the repository; here it is syntax the author's
interpreter accepts and CI's does not. Both times the runner was honest about
what it saw and wrong about what would happen elsewhere.

WHY NOT `ast.parse(feature_version=...)`. It was tried first and reported zero
problems, because `feature_version` constrains the GRAMMAR and PEP 701 changed
the TOKENIZER. A check that cannot see the defect it was written for is worse
than no check, so this walks the token stream instead and looks for the
specific construct: an f-string that opens on one line and closes on another.

WHAT IT DOES NOT CATCH. Anything else that differs between 3.11 and 3.12, and
every difference between 3.11 and whatever a future CI runs. It answers one
question — the one that has actually cost a red build — and says so rather
than implying a general guarantee. The honest general check is running the
tests under the version CI uses, which this repository does not currently do.

Run:  python3 inventory/py_version_floor.py
"""
import io
import os
import subprocess
import sys
import tokenize

FLOOR = (3, 11)          # what .github/workflows/regression.yml installs


def workflow_version():
    """The Python CI installs, read from the workflow rather than assumed."""
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    wf = os.path.join(root, ".github", "workflows", "regression.yml")
    try:
        for line in open(wf, encoding="utf-8"):
            if "python-version" in line:
                v = line.split(":", 1)[1].strip().strip("'\"")
                return tuple(int(x) for x in v.split("."))
    except (OSError, ValueError):
        pass
    return None


def multiline_fstrings(path):
    """[(line, text)] — REPLACEMENT FIELDS that open on one line and close on
    another, inside a single-quoted f-string.

    NARROWED TWICE, and both narrowings were measured rather than reasoned.

    First a regex, which flagged three files: one real, one a set
    comprehension, one a dict.

    Then "an f-string spanning lines", which flagged six — all of them
    `f\"\"\"...\"\"\"`, whose newlines are legal in every version and are how
    this corpus prints its paragraphs. A check firing on the corpus's normal
    style would be turned off within a day.

    What actually breaks on 3.11 is the construct CI reported: an expression
    inside `{...}` continuing onto the next line, in a singly-quoted f-string.
    That is what this looks for and nothing else.
    """
    out = []
    try:
        src = open(path, encoding="utf-8").read()
    except OSError:
        return out
    if not hasattr(tokenize, "FSTRING_START"):     # pragma: no cover
        return out                                  # runner predates 3.12
    lines = src.splitlines()
    # `inside` is not decoration. Without it the brace counting runs over the
    # whole file and every dict or set literal split across lines is a hit:
    # the version before this one reported 395, which is not a narrowing
    # problem but a plain bug, and it would have been believed if the count
    # had come out plausible instead of absurd.
    inside, triple, depth, opened = False, False, 0, None
    try:
        for tok in tokenize.generate_tokens(io.StringIO(src).readline):
            if tok.type == tokenize.FSTRING_START:
                inside = True
                triple = tok.string.rstrip().endswith(('"""', "'''"))
                depth, opened = 0, None
            elif tok.type == tokenize.FSTRING_END:
                inside, triple, depth, opened = False, False, 0, None
            elif inside and not triple and tok.type == tokenize.OP:
                if tok.string == "{":
                    if depth == 0:
                        opened = tok.start[0]
                    depth += 1
                elif tok.string == "}" and depth:
                    depth -= 1
                    if depth == 0 and opened and tok.end[0] != opened:
                        out.append((opened, lines[opened - 1].strip()))
                    if depth == 0:
                        opened = None
    except (tokenize.TokenError, IndentationError, SyntaxError):
        pass
    return out


def main():
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    files = subprocess.run(["git", "ls-files", "*.py"], cwd=root,
                           capture_output=True, text=True).stdout.split()
    print("=" * 78)
    print("PYTHON FLOOR — does this run where CI runs it?")
    print("=" * 78)
    wf = workflow_version()
    print(f"\n  this interpreter        {sys.version_info.major}."
          f"{sys.version_info.minor}")
    print(f"  the workflow installs   "
          f"{'.'.join(map(str, wf)) if wf else 'unreadable'}")
    print(f"  the floor checked here  {'.'.join(map(str, FLOOR))}")
    if wf and wf != FLOOR:
        print(f"\n  NOTE: the workflow says {wf} and this file assumes {FLOOR}."
              f"\n  One of them is stale; fix before trusting the result below.")

    bad = [(f, ls) for f in files for ls in [multiline_fstrings(
        os.path.join(root, f))] if ls]
    n = sum(len(ls) for _f, ls in bad)
    print(f"\n  {len(files)} tracked python files scanned")
    print(f"  multi-line f-strings (3.12 syntax, SyntaxError on 3.11): {n}\n")
    for f, ls in bad:
        for line, text in ls:
            print(f"     {f}:{line}")
            print(f"        {text[:66]}")

    if sys.version_info < (3, 12):
        print("""
  This interpreter predates 3.12, so it could not have parsed the offending
  construct to find it. The scan above is empty for that reason and not
  because the corpus is clean. Run it on 3.12 or later.""")
        print("\nPYTHON FLOOR SKIPPED — needs 3.12 to detect 3.12 syntax.")
        return 0

    if n:
        print("""
  Each of these parses here and fails on CI. Move the expression out of the
  replacement field: compute it into a name on its own line, then interpolate
  the name. Shorter, and legal on both.""")
        print("\nPYTHON FLOOR RED — syntax this machine accepts and CI rejects.")
        return 1

    print("""
  Nothing here needs an interpreter newer than the one CI installs. This
  checks ONE difference — the one that cost a red build on 2026-08-18 — and
  not the general question, which only running the suite under CI's version
  would answer.""")
    print("\nPYTHON FLOOR GREEN — no 3.12-only syntax in the tracked corpus.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
