# -*- coding: utf-8 -*-
"""
zpy_lint — the checker for code written over ZTL (2026-11-09, pilot; see zpy.py).

It reads the SOURCE (no run) and reports three kinds of place:

  NOTNOT     a double negation (`not not x`, `~~x`). In ZTL ¬¬Z = T while Z itself reads F: removing the pair, the
             "simplification" every binary habit makes, changes the verdict. Flagged wherever it stands — the checker
             cannot know whether the operand may be unknown; the author says so by rewriting or by a `# zpy: ok`.
  CONFLATE   a call that can REFUSE (answers None / a refusal) read as a bool — `if f(...)`, `x if f(...) else y`,
             `not f(...)`, `f(...) and ...`, `assert f(...)`. A refusal then silently becomes "no". LIVE when the call
             passes a budget (it can refuse there and then); LATENT when it does not (it cannot refuse today — one
             added argument away from a silent bug).
  LAUNDER    an `except` of a refusal whose handler RETURNS a value that is not a refusal: "could not answer" turned
             into an answer.
  BYPASS     (in code that imports zpy) a comparison against an "IF STABLE" disposition label — the verdict read by hand and its path decided
             unnamed (2026-11-10, round 2 of the AI experiment: a model mapped EARNED IF STABLE to its positive
             outcome this way). The named way is zpy.decide(..., if_stable="classical").

Usage: python3 zpy_lint.py [paths...]   (directories are walked; prints one line per finding, then counts)
"""
import ast
import os
import sys

REFUSING = {"stable_bit", "hereditary_bit", "backward", "backward_tree", "reach", "sat"}


def _callee(node):
    f = node.func
    return f.id if isinstance(f, ast.Name) else f.attr if isinstance(f, ast.Attribute) else None


def _has_budget(call):
    if any(k.arg == "budget" and not (isinstance(k.value, ast.Constant) and k.value.value is None)
           for k in call.keywords):
        return True
    return _callee(call) in ("stable_bit", "hereditary_bit") and len(call.args) >= 3


def _refusing_calls(expr):
    """Refusing calls whose RESULT is the boolean (not calls nested deeper, e.g. as an argument of a comparison)."""
    if isinstance(expr, ast.Call) and _callee(expr) in REFUSING:
        return [expr]
    if isinstance(expr, ast.BoolOp):
        return [c for v in expr.values for c in _refusing_calls(v)]
    if isinstance(expr, ast.UnaryOp) and isinstance(expr.op, ast.Not):
        return _refusing_calls(expr.operand)
    return []


def lint_source(src, path="<src>"):
    out = []
    lines = src.splitlines()
    import warnings
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")      # other files' invalid escapes are not this checker's findings
            tree = ast.parse(src)
    except SyntaxError as e:
        return [(path, e.lineno or 0, "PARSE", str(e))]

    # BYPASS is a rule for code written OVER the layer: the kernel reads its own labels by design
    over_zpy = any(isinstance(x, (ast.Import, ast.ImportFrom)) and (
        (isinstance(x, ast.ImportFrom) and x.module == "zpy") or
        (isinstance(x, ast.Import) and any(a.name == "zpy" for a in x.names))) for x in ast.walk(tree))

    def ok(node):
        ln = lines[node.lineno - 1] if 0 < node.lineno <= len(lines) else ""
        return "zpy: ok" in ln

    for node in ast.walk(tree):
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.Not, ast.Invert)) \
                and isinstance(node.operand, ast.UnaryOp) and type(node.operand.op) is type(node.op) and not ok(node):
            out.append((path, node.lineno, "NOTNOT", ast.unparse(node)[:80]))
        tests = []
        if isinstance(node, (ast.If, ast.IfExp, ast.While)):
            tests = [node.test]
        elif isinstance(node, ast.Assert):
            tests = [node.test]
        elif isinstance(node, ast.BoolOp) or (isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not)):
            tests = [node]
        for t in tests:
            for c in _refusing_calls(t):
                if ok(c):
                    continue
                kind = "CONFLATE-LIVE" if _has_budget(c) else "CONFLATE-LATENT"
                out.append((path, c.lineno, kind, ast.unparse(c)[:80]))
        if over_zpy and isinstance(node, ast.Compare) and not ok(node):
            consts = [c.value for c in ast.walk(node) if isinstance(c, ast.Constant) and isinstance(c.value, str)]
            if any("IF STABLE" in c for c in consts):
                out.append((path, node.lineno, "BYPASS", ast.unparse(node)[:80]))
        if isinstance(node, ast.ExceptHandler) and node.type is not None and "Refus" in ast.unparse(node.type):
            for r in ast.walk(ast.Module(body=node.body, type_ignores=[])):
                said = ast.unparse(r.value).lower() if isinstance(r, ast.Return) and r.value is not None else ""
                # a refusal in another spelling ({"refused": ...}, ("refused", None), "отказ") is still a refusal
                if isinstance(r, ast.Return) and r.value is not None and not (
                        isinstance(r.value, ast.Call) and _callee(r.value) == "Refusal") \
                        and "refus" not in said and "отказ" not in said and not ok(r):
                    out.append((path, r.lineno, "LAUNDER", ast.unparse(r)[:80]))
    # one finding per (line, kind): a BoolOp and its If report the same call once
    seen, uniq = set(), []
    for f in out:
        k = (f[1], f[2], f[3])
        if k not in seen:
            seen.add(k)
            uniq.append(f)
    return uniq


def lint_paths(paths):
    out = []
    for p in paths:
        files = [p] if os.path.isfile(p) else [os.path.join(d, f) for d, _, fs in os.walk(p)
                                                 for f in fs if f.endswith(".py")]
        for f in sorted(files):
            if any(s in f for s in ("/_attic/", "/.lake/", "/__pycache__/", "/node_modules/", "/OLD/")):
                continue
            try:
                src = open(f, encoding="utf-8").read()
            except (OSError, UnicodeDecodeError):
                continue
            out += lint_source(src, f)
    return out


if __name__ == "__main__":
    found = lint_paths(sys.argv[1:] or ["."])
    for path, ln, kind, what in found:
        print(f"{path}:{ln}: {kind}: {what}")
    counts = {}
    for _, _, k, _ in found:
        counts[k] = counts.get(k, 0) + 1
    print("zpy_lint:", ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) or "nothing found")
