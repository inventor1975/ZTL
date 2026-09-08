#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
code2zfl — code → atoms → ZFL2 → the ZTL judge.

The idea (curator, 2026-09-08): a model cannot lay a text out into atoms
without losing some; a parser can, because code is deterministic. So the
atomizer is an ALGORITHM (`atoms.php`, nikic/php-parser), and the only judge
is the ZTL core — the same `zfl2.run` the studio uses.

One document per SINK, three rows, one claim:

    tainted    an attacker-controlled value reaches the sink       (source facts)
    sanitized  on every path it was SUBSTITUTED by a verified one   (E40: no function launders)
    safe       := ~Tr(tainted) | Tr(sanitized)                      claim: safe

The judge returns the disposition and the weak link:
    EARNED     grounded — on the named substitution, or nothing attacker-controlled arrives
    REFUTED    an attacker-controlled value reaches the sink and nothing on the path substitutes it
    OPEN       the path crosses something this file cannot see; the weak link is NAMED
    ON CREDIT  true only while an unverified link holds

Why one document per sink is exact and not a shortcut: evaluation reads the
marking only at the atoms of the formula (`lean/NoGift.lean` evalF_congr,
`lean/ContextClosure.lean` eval_indep, `lean/Receipt.lean` receipt_complete —
all on []). Cutting a table into per-claim tables changes no verdict.

Boundaries (say them, do not hide them):
  * intra-procedural: a parameter, a global, an include, a DB row are Z;
  * a file that does not parse is E — "not judged", never "clean";
  * sanitization is per CONTEXT: an HTML escaper before SQL is F, not T;
    escaping without quotes is F; a transformation after escaping drops it;
  * the catalog is DATA and carries its own `measured` flag per sink context.

Usage:
  python3 code2zfl.py FILE_OR_DIR... [--overlay proj.json] [--ctx sql|all]
                      [--json out.json] [--md out.md] [--autoload vendor/autoload.php]
"""
import argparse
import json
import os
import subprocess
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))                      # ZTL/tool
sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))     # ZTL
import zfl2                                                    # noqa: E402

SKIP_DIRS = {"vendor", "node_modules", ".git", "cache", "backup", "_backup", "OLD", "attic"}


def php_files(paths):
    for p in paths:
        if os.path.isfile(p):
            yield p
            continue
        for root, dirs, files in os.walk(p):
            dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
            for f in sorted(files):
                if f.endswith(".php"):
                    yield os.path.join(root, f)


def atomize(files, overlays, autoload, catalog=None, php=None):
    cmd = ["php", os.path.join(HERE, "atoms.php")]
    if php:
        cmd += ["--php", php]
    if catalog:
        cmd += ["--catalog", catalog]
    for o in overlays:
        cmd += ["--overlay", o]
    cmd += list(files)
    env = dict(os.environ)
    if autoload:
        env["CODE2ZFL_AUTOLOAD"] = autoload
    r = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit(f"atoms.php failed ({r.returncode}): {r.stderr.strip()}")
    return json.loads(r.stdout)


# ------------------------------------------------------------ facts → ZFL2
def _g(s):
    """A ground is ONE WORD naming an act (E_GROUND_SPACES)."""
    s = s.replace("$", "").replace("->", "m.")
    return "".join(ch if (ch.isalnum() or ch in "-_.") else "-" for ch in s)


def sink_document(fact, ctx):
    line = fact["line"]
    t, src, san, z, q = fact["t"], fact["src"], fact["san"], fact["z"], fact["q"]
    san = dict(san) if isinstance(san, dict) else {}       # PHP encodes an empty map as []
    zu = fact.get("zu") or []
    # --- tainted
    if t == "T":
        k, name, l = src[0]
        tainted = {"status": "verified", "ground": _g(f"src-{name}-L{l}"),
                   "means": "attacker-controlled value reaches the sink: " + ", ".join(f"{n}@L{l}" for _, n, l in src)}
    elif t == "F":
        tainted = {"status": "refuted", "ground": _g(f"ast-const-L{line}"),
                   "means": "nothing attacker-controlled reaches the sink (constants only, read from the AST)"}
    else:
        tainted = {"status": "unverified",
                   "means": "origin not visible in this file: " + ", ".join(f"{w}@L{l}" for w, l in z)}
    # --- sanitized, per context
    if "*" in san:
        fn, l = san["*"]
        sanitized = {"status": "verified", "ground": _g(f"san-{fn}-L{l}"), "means": f"substituted by {fn} at L{l} (every context)"}
    elif ctx in san:
        fn, l = san[ctx]
        sanitized = {"status": "verified", "ground": _g(f"san-{fn}-L{l}"), "means": f"substituted by {fn} at L{l} for {ctx}"}
    elif ctx == "sql" and "sql-quoted" in san:
        fn, l = san["sql-quoted"]
        if q is True:
            sanitized = {"status": "verified", "ground": _g(f"san-{fn}-L{l}-quoted"), "means": f"escaped by {fn} at L{l} and placed inside quotes"}
        elif q is False:
            sanitized = {"status": "refuted", "ground": _g(f"ast-unquoted-L{line}"), "means": f"escaped by {fn} at L{l} but NOT inside quotes — escaping without quotes protects nothing"}
        else:
            sanitized = {"status": "unverified", "means": f"escaped by {fn} at L{l}; whether it sits inside quotes could not be read"}
    elif t == "F":
        sanitized = {"status": "unverified", "means": "not needed: nothing attacker-controlled arrives"}
    elif z:
        sanitized = {"status": "unverified", "means": "no substitution seen; the path crosses " + ", ".join(f"{w}@L{l}" for w, l in z)}
    else:
        wrong = ", ".join(f"{fn}@L{l} ({c})" for c, (fn, l) in san.items())
        sanitized = {"status": "refuted", "ground": _g(f"ast-path-L{line}"),
                     "means": "path read in full, no substitution for " + ctx + (f"; wrong-context only: {wrong}" if wrong else "")}
    # a part of UNKNOWN origin reaches the sink without a substitution: even when the attacker-controlled
    # parts are settled, safety is not established — the weak link is that part
    if sanitized["status"] == "verified" and zu:
        sanitized = {"status": "unverified",
                     "means": sanitized["means"] + "; but a part of unknown origin is not substituted: " + ", ".join(f"{w}@L{l}" for w, l in zu)}
    rows = [dict(name="tainted", ground_kind="act", **tainted),
            dict(name="sanitized", ground_kind="act", **sanitized),
            {"name": "safe", "status": "defined", "ground": "~Tr(tainted) | Tr(sanitized)",
             "means": f"the {ctx} sink {fact['fn']} at L{line} cannot be driven by an attacker"}]
    for r in rows:
        if r["status"] == "unverified":
            r.pop("ground", None); r.pop("ground_kind", None)
    return {"rows": rows, "claim": "safe"}


def judge(doc):
    r = zfl2.run(doc)
    errs = [i for i in r.get("issues", []) if i.get("level") == "error"]
    if errs or not r.get("ok", True):
        return {"disposition": "E", "grade": "-", "why": "document refused: " + "; ".join(f"{i.get('code')} {i.get('where')}" for i in errs), "weak": []}
    j = r["report"]["judge"]
    weak = []
    for name in j.get("unverified", []):
        if name == "safe":
            weak += [row["name"] for row in doc["rows"] if row["status"] == "unverified" and row["name"] != "safe"]
        else:
            weak.append(name)
    return {"disposition": j["disposition"], "grade": j["grade"], "verdict": j["verdict"], "weak": sorted(set(weak))}


def run(paths, overlays=(), ctx="sql", autoload=None, catalog=None, php=None):
    files = list(php_files(paths))
    if not files:
        sys.exit("no .php files")
    facts = atomize(files, overlays, autoload, catalog, php)
    out = {"tool": "code2zfl", "ctx": ctx, "php": facts.get("php"), "files": []}
    for f in facts["files"]:
        rec = {"file": f["file"], "lines": f["lines"], "parse_error": f["parse_error"],
               "includes": f["includes"], "sinks": []}
        if f["parse_error"]:
            rec["disposition"] = "E"
            out["files"].append(rec)
            continue
        for s in f["sinks"]:
            if ctx != "all" and s["ctx"] != ctx:
                continue
            doc = sink_document(s, s["ctx"])
            v = judge(doc)
            rec["sinks"].append({"line": s["line"], "fn": s["fn"], "ctx": s["ctx"], "scope": s["scope"],
                                 "disposition": v["disposition"], "grade": v["grade"], "weak": v["weak"],
                                 "tainted": doc["rows"][0], "sanitized": doc["rows"][1], "doc": doc})
        out["files"].append(rec)
    return out


def ledger_md(out):
    L = ["# code2zfl ledger", "", f"context: `{out['ctx']}` · grammar: PHP {out.get('php') or 'newest'}", ""]
    tot = Counter()
    for f in out["files"]:
        if f["parse_error"]:
            L.append(f"## {f['file']} — **E** (not judged: parse error {f['parse_error']})")
            tot["E"] += 1
            continue
        if not f["sinks"]:
            continue
        L.append(f"## {f['file']} ({f['lines']} lines, includes by expression at L{','.join(map(str, f['includes'])) or '—'})")
        L.append("")
        L.append("| line | sink | scope | disposition | grade | grounds / weak link |")
        L.append("|---|---|---|---|---|---|")
        for s in f["sinks"]:
            tot[s["disposition"]] += 1
            g = []
            for r in (s["tainted"], s["sanitized"]):
                if r["status"] in ("verified", "refuted"):
                    g.append(f"{r['name']}={r['status']}:{r['ground']}")
            if s["weak"]:
                g.append("weak: " + ", ".join(s["weak"]))
                for r in (s["tainted"], s["sanitized"]):
                    if r["status"] == "unverified" and "@L" in r["means"]:
                        g.append(r["name"] + " ← " + r["means"].split(": ", 1)[-1][:120])
            L.append(f"| L{s['line']} | `{s['fn']}` | `{s['scope']}` | **{s['disposition']}** | {s['grade']} | {'; '.join(g)} |")
        L.append("")
    L.append("## totals")
    L.append("")
    for k in ("REFUTED", "OPEN", "ON CREDIT", "EARNED", "E"):
        if tot[k]:
            L.append(f"- {k}: {tot[k]}")
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--overlay", action="append", default=[])
    ap.add_argument("--catalog", default=None)
    ap.add_argument("--ctx", default="sql")
    ap.add_argument("--autoload", default=os.environ.get("CODE2ZFL_AUTOLOAD"))
    ap.add_argument("--php", default=None, help="grammar version for legacy code, e.g. 7.4 (default: newest)")
    ap.add_argument("--json", default=None)
    ap.add_argument("--md", default=None)
    a = ap.parse_args()
    out = run(a.paths, a.overlay, a.ctx, a.autoload, a.catalog, a.php)
    md = ledger_md(out)
    if a.json:
        with open(a.json, "w", encoding="utf-8") as fh:
            json.dump(out, fh, ensure_ascii=False, indent=1)
    if a.md:
        with open(a.md, "w", encoding="utf-8") as fh:
            fh.write(md)
    else:
        sys.stdout.write(md)


if __name__ == "__main__":
    main()
