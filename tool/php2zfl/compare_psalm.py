#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
compare_psalm — the EXTERNAL DENOMINATOR, as a stand.

Runs Psalm's taint analysis and code2zfl on the same tree and prints one
table a person can read: how many each found, how many are the same lines,
what only Psalm found (and what we said there), what only we found (by
context). The fixtures I write can only test the questions I thought of;
Psalm's catalog is years older, and every line it has that we do not is
either a hole in our catalog or a defect in our judgement — measured here,
not guessed.

Needs Psalm 5 on PHP 8.3.6 (6.x demands >= 8.3.16). Point CODE2ZFL_PSALM at
the binary, e.g. a scratch project's vendor/bin/psalm.

Usage:
  python3 compare_psalm.py --root /path/to/site modules libraries [--overlay proj.json] [--php 7.4] [--md out.md]
"""
import argparse
import collections
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import code2zfl  # noqa: E402

# Psalm issue type -> our sink context
PSALM_CTX = {"TaintedSql": "sql", "TaintedInclude": "file", "TaintedFile": "file", "TaintedHeader": "header",
             "TaintedCallable": "callable", "TaintedShell": "shell", "TaintedHtml": "html", "TaintedEval": "code",
             "TaintedUnserialize": "deser", "TaintedCookie": "header", "TaintedSSRF": "file", "TaintedLdap": "sql",
             "TaintedTextWithQuotes": "html", "TaintedXpath": "sql", "TaintedSleep": "shell", "TaintedSystemSecret": "html"}


def run_psalm(psalm, root, dirs):
    with tempfile.TemporaryDirectory() as td:
        cfg = os.path.join(td, "psalm.xml")
        files = "".join(f'        <directory name="{d}" />\n' for d in dirs)
        with open(cfg, "w") as fh:
            fh.write('<?xml version="1.0"?>\n<psalm errorLevel="8" resolveFromConfigFile="false" findUnusedCode="false" '
                     'findUnusedBaselineEntry="false" xmlns="https://getpsalm.org/schema/config">\n'
                     f'    <projectFiles>\n{files}    </projectFiles>\n</psalm>\n')
        rep = os.path.join(td, "taint.json")
        r = subprocess.run([psalm, f"--config={cfg}", f"--root={root}", "--taint-analysis", "--no-cache",
                            "--no-progress", "--threads=4", f"--report={rep}"], cwd=root, capture_output=True, text=True)
        if not os.path.exists(rep):
            # HEAD AND TAIL. The exception message is at the top of Psalm's output and the
            # stack at the bottom; keeping only the last 1500 characters (as before)
            # dropped the one line that names the cause (2026-09-10, SMF: "Could not
            # locate trait statement" was cut off).
            out = r.stdout + r.stderr
            sys.exit("psalm produced no report:\n" + (out if len(out) <= 3000 else out[:1500] + "\n…\n" + out[-1500:]))
        return json.load(open(rep))


def _key(path, root, base):
    """One file, one name on both sides. Psalm reports paths relative to --root and
    resolves symlinks; code2zfl keeps the path it was given. Run from a root that links
    the project in (needed when a composer.json without vendor/ makes Psalm refuse), the
    two sides named the same file differently and the join found ZERO shared lines on
    SuiteCRM (2026-09-10) — a false zero from the join, not a property of the tools."""
    real = os.path.realpath(path if os.path.isabs(path) else os.path.join(root, path))
    return os.path.relpath(real, base)


def compare(psalm_issues, ours, root, base=None):
    base = base or os.path.realpath(root)
    P = {}
    for p in psalm_issues:
        P.setdefault((_key(p["file_name"], root, base), p["line_from"]), set()).add(p["type"])
    O = collections.defaultdict(list)
    for f in ours["files"]:
        rel = _key(f["file"], root, base)
        for s in f["sinks"]:
            O[(rel, s["line"])].append(s)
    ours_refuted = {k for k, ss in O.items() if any(s["disposition"] == "REFUTED" for s in ss)}
    shared = [k for k in P if k in ours_refuted]
    only_p = [k for k in P if k not in ours_refuted]
    only_o = [k for k in ours_refuted if k not in P]
    return P, O, shared, only_p, only_o


def table_md(P, O, shared, only_p, only_o, root):
    L = ["# code2zfl × Psalm", "", "| | Psalm | code2zfl |", "|---|---:|---:|",
         f"| found (lines) | **{len(P)}** | **{len(only_o) + len(shared)}** |",
         f"| same lines | {len(shared)} | {len(shared)} |",
         f"| only here | **{len(only_p)}** | **{len(only_o)}** |", ""]
    if only_p:
        L += ["## only Psalm — and what code2zfl said there", ""]
        for k in sorted(only_p):
            ss = O.get(k)
            mine = ", ".join(sorted({f"{s['ctx']}:{s['disposition']}" + (f" (weak {', '.join(s['weak'])})" if s["weak"] else "") for s in ss})) if ss else "no sink in our catalog"
            L.append(f"- `{k[0]}:{k[1]}` {'/'.join(sorted(P[k]))} → **{mine}**")
        L.append("")
    if only_o:
        by = collections.Counter()
        for k in only_o:
            for s in O[k]:
                if s["disposition"] == "REFUTED":
                    by[s["ctx"]] += 1
        L += ["## only code2zfl — by context (Psalm silent there)", ""]
        L += [f"- {c}: {n}" for c, n in by.most_common()]
        L.append("")
        for k in sorted(only_o):
            for s in O[k]:
                if s["disposition"] != "REFUTED":
                    continue
                why = s["sanitized"]["means"] if s["sanitized"]["status"] == "refuted" else s["tainted"]["means"]
                L.append(f"- `{k[0]}:{k[1]}` {s['ctx']} `{s['fn']}` in `{s['scope']}` — {why[:110]}")
        L.append("")
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", required=True)
    ap.add_argument("dirs", nargs="+", help="directories under root")
    ap.add_argument("--overlay", action="append", default=[])
    ap.add_argument("--php", default=None)
    ap.add_argument("--psalm", default=os.environ.get("CODE2ZFL_PSALM"))
    ap.add_argument("--md", default=None)
    ap.add_argument("--raw", default=None, help="dump both sides as JSON, to re-join without re-running")
    a = ap.parse_args()
    if not a.psalm or not os.path.exists(a.psalm):
        sys.exit("set CODE2ZFL_PSALM to a psalm binary (5.x on PHP < 8.3.16)")
    root = os.path.abspath(a.root)
    psalm_issues = run_psalm(a.psalm, root, a.dirs)
    ours = code2zfl.run([os.path.join(root, d) for d in a.dirs], a.overlay, "all", None, None, a.php)
    base = os.path.realpath(os.path.join(root, a.dirs[0])) if len(a.dirs) == 1 else os.path.realpath(root)
    P, O, shared, only_p, only_o = compare(psalm_issues, ours, root, base)
    if a.raw:
        with open(a.raw, "w", encoding="utf-8") as fh:
            json.dump({"root": root, "base": base, "psalm": psalm_issues,
                       "ours": [{"file": f["file"], "line": s["line"], "ctx": s["ctx"], "disposition": s["disposition"]}
                                for f in ours["files"] for s in f["sinks"]]}, fh, ensure_ascii=False)
    md = table_md(P, O, shared, only_p, only_o, root)
    if a.md:
        with open(a.md, "w", encoding="utf-8") as fh:
            fh.write(md)
    sys.stdout.write(md)


if __name__ == "__main__":
    main()
