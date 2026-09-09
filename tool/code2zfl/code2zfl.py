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
import tempfile
from multiprocessing.pool import ThreadPool
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


def _atomize_batch(args):
    cmd, files, env = args
    r = subprocess.run(cmd + list(files), capture_output=True, text=True, env=env)
    if r.returncode != 0:
        return {"files": [], "_error": f"atoms.php failed ({r.returncode}): {r.stderr.strip()[:400]}"}
    return json.loads(r.stdout)


def summarise(files, overlays, autoload, catalog=None, php=None, jobs=None):
    """PASS 1 of cross-file sight: what every definition in the tree does with a tainted parameter.
    Written to a temp file and handed to pass 2, so a call into another file stops being opaque."""
    cmd = ["php", os.path.join(HERE, "atoms.php"), "--emit-summaries"]
    if php:
        cmd += ["--php", php]
    if catalog:
        cmd += ["--catalog", catalog]
    for o in overlays:
        cmd += ["--overlay", o]
    env = dict(os.environ)
    if autoload:
        env["CODE2ZFL_AUTOLOAD"] = autoload
    files = list(files)
    n = jobs if jobs and jobs > 0 else min(8, (os.cpu_count() or 1))
    batches = [files[i::n] for i in range(n)] if (n > 1 and len(files) >= 40) else [files]
    merged = {"functions": {}, "methods": {}, "parents": {}, "files": {}}
    with ThreadPool(max(1, len(batches))) as pool:
        for part in pool.map(_atomize_batch, [(cmd, b, env) for b in batches if b]):
            if part.get("_error"):
                sys.exit(part["_error"])
            for slot in ("functions", "methods"):                       # a name seen in two batches: same rule as inside one
                recs = part.get(slot) or {}
                if isinstance(recs, list):                                  # PHP writes an empty map as []
                    recs = {}
                for k, rec in recs.items():
                    merged[slot][k] = _summary_merge(merged[slot].get(k), rec)
            par = part.get("parents") or {}                              # a class has ONE parent: no meet, plain carry
            if isinstance(par, dict):
                merged["parents"].update(par)
            ff = part.get("files") or {}                                  # a file is summarised in exactly one batch
            if isinstance(ff, dict):
                merged["files"].update(ff)
    merged["inherit"] = _inherit(merged["files"])
    return merged


def _inherit(facts):
    """WHAT A FILE INHERITS FROM WHAT IT INCLUDES. A front controller guards the request once and every
    page that requires it is judged under that guard; without the closure the guard is invisible and the
    page reads as unprotected. Own facts are not folded in — pass 2 recomputes those from the file itself."""
    out = {}
    for path in facts:
        seen, stack, unk, grd, st = set(), list(facts[path].get("inc") or []), {}, [], []
        while stack:                                                      # transitive, cycles cut by `seen`
            q = stack.pop()
            if q in seen or q not in facts:
                continue
            seen.add(q)
            f = facts[q]
            for k, v in (f.get("unk") or {}).items():
                unk.setdefault(k, v)
            grd += f.get("grd") or []
            st += f.get("set") or []
            stack += f.get("inc") or []
        if unk or grd or st:
            out[path] = {"unk": unk, "grd": grd, "set": sorted(set(st))}
    return out


def _summary_merge(a, b):
    """Two summaries for one name: identical in substance -> keep; otherwise a CONFLICT that pass 2 reads as unknown.
    Mirrors summaryMerge() in atoms.php; needed here because batches run in separate processes."""
    if a is None:
        return b
    if a.get("conflict") and b.get("conflict"):
        return {"conflict": True, "files": _files(a) + _files(b)}
    if a.get("conflict"):
        return a
    if b.get("conflict"):
        return {"conflict": True, "files": _files(a) + _files(b)}
    strip = lambda r: {k: v for k, v in r.items() if k not in ("file", "line")}
    if strip(a) == strip(b):
        return a
    return {"conflict": True, "files": _files(a) + _files(b)}


def _files(r):
    """The files a summary came from. A CONFLICT record carries `files` and no `file` — merging one of
    those into a plain record used to put a None in the list and kill the whole run (CodeIgniter 4)."""
    out = list(r.get("files") or [])
    if r.get("file"):
        out.append(r["file"])
    return sorted(set(out))


def atomize(files, overlays, autoload, catalog=None, php=None, jobs=None, summaries=None):
    cmd = ["php", os.path.join(HERE, "atoms.php")]
    if summaries:
        cmd += ["--summaries", summaries]
    if php:
        cmd += ["--php", php]
    if catalog:
        cmd += ["--catalog", catalog]
    for o in overlays:
        cmd += ["--overlay", o]
    env = dict(os.environ)
    if autoload:
        env["CODE2ZFL_AUTOLOAD"] = autoload
    files = list(files)

    # ONE PROCESS PER BATCH, and the batches are interleaved rather than sliced. Measured 2026-09-09
    # on WordPress: contiguous slices put all of wp-includes/ID3 in one batch and the whole run took
    # as long as that batch (342 s of 334); interleaving spreads the expensive neighbours. Parallelism
    # was worth nothing until the node budget removed the single 297-second file — a reminder that
    # splitting work does not fix work that is quadratic in one place.
    n = jobs if jobs and jobs > 0 else min(8, (os.cpu_count() or 1))
    if n <= 1 or len(files) < 40:
        return _atomize_batch((cmd, files, env))
    batches = [files[i::n] for i in range(n)]
    with ThreadPool(n) as pool:
        parts = pool.map(_atomize_batch, [(cmd, b, env) for b in batches if b])
    out = dict(parts[0]); out["files"] = []
    for part in parts:
        if part.get("_error"):
            sys.exit(part["_error"])
        out["files"].extend(part["files"])
    order = {f: i for i, f in enumerate(files)}
    out["files"].sort(key=lambda r: order.get(r["file"], 0))
    return out


# ------------------------------------------------------------ facts → ZFL2
def _g(s):
    """A ground is ONE WORD naming an act (E_GROUND_SPACES)."""
    s = s.replace("$", "").replace("->", "m.")
    return "".join(ch if (ch.isalnum() or ch in "-_.") else "-" for ch in s)


# html sub-contexts (atoms.php Html lexer): what substitutes a value depends on where in the markup it lands.
# level 0: body text / double-quoted attribute — HTML escaping (" is encoded) is the substitution;
# level 1: single-quoted attribute — only an escaper that encodes ' (ENT_QUOTES);
# level 2: a URL attribute — URL-encoding (javascript: needs no quote at all);
# level 3: unquoted attribute, tag/attribute name, event handler, style, <script>, <style>, comment — only a
#          numeric/whitelist substitution ('*'). 'unknown' (an output whose position cannot be read): level 0, said so.
HLEVEL = {"text": 0, "attr-dq": 0, "script-dq": 0, "attr-sq": 1, "script-sq": 1, "attr-url": 2}
HNEED = {0: ("html", "html-sq", "header"), 1: ("html-sq", "header"), 2: ("header",), 3: ()}   # URL-encoding leaves no quote, bracket or ampersand
HJS = ("script", "script-sq", "script-dq")                                                     # a JavaScript encoder (`js`) substitutes inside <script>
HWHY = {"attr-sq": "a single quote ends a single-quoted attribute and this escaper does not encode it (ENT_QUOTES would)",
        "attr-url": "a URL attribute: `javascript:` needs neither quote nor angle bracket — URL-encoding substitutes, HTML escaping does not",
        "attr-unquoted": "an unquoted attribute value: a space ends it and starts a new attribute — HTML escaping encodes no space",
        "tag-name": "a tag-name position: HTML escaping is moot there", "attr-name": "an attribute-name position: HTML escaping is moot there",
        "attr-event": "an event-handler attribute: the browser decodes entities BEFORE running the script",
        "attr-style": "a style attribute: CSS syntax, not HTML", "style": "inside <style>: CSS syntax, not HTML",
        "script": "inside <script>, outside any string: HTML escaping does not reach the script parser",
        "script-sq": "inside a single-quoted script string and this escaper does not encode the quote (ENT_QUOTES would)",
        "script-code": "a script string that is RUN as code (setTimeout, eval, innerHTML, location…): its content executes, no quoting escape helps",
        "comment": "inside a comment: `-->` ends it"}


def html_row(fact, ctx, san, t, line):
    """The `sanitized` row for an html sink whose sub-context is known and demands more than plain HTML escaping;
    None when the generic reading applies."""
    hctx = fact.get("hctx")
    if ctx != "html" or hctx in (None, "unknown") or t == "F":
        return None
    if hctx in ("text", "attr-dq", "script-dq") and "html" in san:
        return None                                              # plain HTML escaping is the substitution here: the generic reading
    level = HLEVEL.get(hctx, 3)
    for k in HNEED[level] + (("js",) if hctx in HJS else ()):
        if k in san:
            fn, l = san[k]
            return {"status": "verified", "ground": _g(f"san-{fn}-L{l}"), "means": f"substituted by {fn} at L{l} for html, value lands in {hctx}"}
    have = [(k, san[k]) for k in ("html", "html-sq", "header", "js") if k in san]
    if have:
        k, (fn, l) = have[0]
        return {"status": "refuted", "ground": _g(f"ast-html-{hctx}-L{line}"),
                "means": f"escaped by {fn} at L{l} ({k}), but the value lands in {hctx}: {HWHY.get(hctx, hctx)}"}
    return None


def sink_document(fact, ctx):
    line = fact["line"]
    t, src, san, z, q = fact["t"], fact["src"], fact["san"], fact["z"], fact["q"]
    san = dict(san) if isinstance(san, dict) else {}       # PHP encodes an empty map as []
    zu = fact.get("zu") or []
    nu = bool(fact.get("nu"))
    hrow = html_row(fact, ctx, san, t, line)
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
    elif hrow is not None:
        sanitized = hrow
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
    elif ctx == "file" and "header" in san:
        # URL-ENCODED, AND THE SINK IS A FILE CALL. `file_get_contents("http://host/api?x=" . urlencode($v))`
        # is not path traversal — the scheme and host are literal, the value only reaches the query —
        # but neither is it proof of safety, since we do not read where the literal came from. Z, with
        # the encoder named. Measured 2026-09-09 on wp-slimstat.php:1567.
        fn, l = san["header"]
        sanitized = {"status": "unverified",
                     "means": f"URL-encoded by {fn} at L{l}; for a file/URL sink that is not a substitution, only a narrowing — read the literal around it"}
    elif nu:
        # an attacker-controlled part reaches the sink with NO substitution and its own path read in full;
        # whatever else sits beside it (a property, a DB row) cannot make that part safer
        sanitized = {"status": "refuted", "ground": _g(f"ast-path-L{line}"),
                     "means": "an attacker-controlled part reaches the sink unsubstituted, path read in full" + ("; other parts cross " + ", ".join(f"{w}@L{l}" for w, l in z) if z else "")}
    elif z:
        sanitized = {"status": "unverified", "means": "no substitution seen; the path crosses " + ", ".join(f"{w}@L{l}" for w, l in z)}
    else:
        wrong = ", ".join(f"{fn}@L{l} ({c})" for c, (fn, l) in san.items())
        sanitized = {"status": "refuted", "ground": _g(f"ast-path-L{line}"),
                     "means": "path read in full, no substitution for " + ctx + (f"; wrong-context only: {wrong}" if wrong else "")}
    if ctx == "html" and fact.get("hctx") == "unknown" and sanitized["status"] == "verified":
        sanitized["means"] += " (html sub-context not determined — read as body text)"
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


def run(paths, overlays=(), ctx="sql", autoload=None, catalog=None, php=None, jobs=None, cross=True):
    files = list(php_files(paths))
    if not files:
        sys.exit("no .php files")
    sumfile = None
    if cross and len(files) > 1:
        summaries = summarise(files, overlays, autoload, catalog, php, jobs)
        fd, sumfile = tempfile.mkstemp(prefix="code2zfl_sum_", suffix=".json")
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(summaries, fh, ensure_ascii=False)
    try:
        facts = atomize(files, overlays, autoload, catalog, php, jobs, sumfile)
    finally:
        if sumfile:
            os.unlink(sumfile)
    out = {"tool": "code2zfl", "ctx": ctx, "php": facts.get("php"), "files": []}
    for f in facts["files"]:
        rec = {"file": f["file"], "lines": f["lines"], "parse_error": f["parse_error"],
               "includes": f["includes"], "sinks": []}
        # a boundary the atomizer hit must reach the reader: past the inlining budget a call is
        # judged as unknown (Z), so this file's OPENs may be wider than they would otherwise be
        if f.get("inline_budget_exhausted"):
            rec["inline_budget_exhausted"] = True
        if f.get("node_budget_exhausted"):
            rec["node_budget_exhausted"] = True
        if f["parse_error"]:
            rec["disposition"] = "E"
            out["files"].append(rec)
            continue
        # a method that IS called in this file is judged at its call sites (its parameters have values
        # there); its standalone reading, where the parameters are Z, is kept only when nothing calls it
        called = {fn["scope"] for fn in f.get("functions", []) if isinstance(fn, dict) and fn.get("callers", 0) > 0}
        for s in f["sinks"]:
            if ctx != "all" and s["ctx"] != ctx:
                continue
            if s["scope"] in called and "→" not in s["scope"] and s["t"] != "T":
                zk = {w.split(":")[0] for w, _ in (s.get("z") or [])}
                if zk and zk <= {"param"}:
                    continue
            doc = sink_document(s, s["ctx"])
            v = judge(doc)
            rec["sinks"].append({"line": s["line"], "fn": s["fn"], "ctx": s["ctx"], "scope": s["scope"], "hctx": s.get("hctx"),
                                 "disposition": v["disposition"], "grade": v["grade"], "weak": v["weak"],
                                 "tainted": doc["rows"][0], "sanitized": doc["rows"][1], "doc": doc})
        out["files"].append(rec)
    return out


SECRET_FILES = ("config.php", "settings.php", "admin_settings.php", ".env")


def _source_line(path, line):
    """The sink's own line, for the human table. Never from a config file."""
    if os.path.basename(path).lower() in SECRET_FILES:
        return "(config file — line not shown)"
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            return fh.read().split("\n")[line - 1].strip()[:140]
    except (OSError, IndexError):
        return ""


def summary_md(out):
    """FOR A HUMAN: one table per run — file / sinks / REFUTED / OPEN / EARNED — then only the REFUTED
    sinks, each with a one-line reason and its own line of code. Everything else lives in the JSON."""
    L = [f"# code2zfl — summary (`{out['ctx']}`, PHP {out.get('php') or 'newest'})", ""]
    rows, tot = [], Counter()
    refuted = []
    for f in out["files"]:
        if f["parse_error"]:
            rows.append((f["file"], "E", 0, 0, 0)); tot["E"] += 1; continue
        if not f["sinks"]:
            continue
        c = Counter(s["disposition"] for s in f["sinks"])
        rows.append((f["file"], len(f["sinks"]), c["REFUTED"], c["OPEN"] + c["ON CREDIT"], c["EARNED"]))
        tot.update(c)
        for s in f["sinks"]:
            if s["disposition"] == "REFUTED":
                refuted.append((f["file"], s))
    L += ["| file | sinks | REFUTED | OPEN | EARNED |", "|---|---:|---:|---:|---:|"]
    for fl, n, r, o, e in sorted(rows, key=lambda r: (-(r[2] if isinstance(r[2], int) else 0), str(r[0]))):
        mark = "**" if isinstance(r, int) and r else ""
        L.append(f"| {fl} | {n} | {mark}{r}{mark} | {o} | {e} |")
    L.append(f"| **total** | {sum(r[1] for r in rows if isinstance(r[1], int))} | **{tot['REFUTED']}** | {tot['OPEN'] + tot['ON CREDIT']} | {tot['EARNED']} |")
    capped = [f["file"] for f in out["files"] if f.get("inline_budget_exhausted") or f.get("node_budget_exhausted")]
    if capped:
        L += ["", f"## inlining budget reached — {len(capped)} file(s)", "",
              "Past the budget a call inside the file is judged as unknown (Z), so these files' OPEN",
              "verdicts are wider than a full walk would give. Named, not hidden:", ""]
        L += [f"- `{c}`" for c in capped[:20]]
        if len(capped) > 20:
            L.append(f"- … and {len(capped) - 20} more")
    L += ["", f"## REFUTED — {len(refuted)}", ""]
    for fl, s in refuted:
        why = s["sanitized"]["means"] if s["sanitized"]["status"] == "refuted" else s["tainted"]["means"]
        L.append(f"- **{fl}:{s['line']}** `{s['fn']}` in `{s['scope']}` — {why}")
        L.append(f"  `{_source_line(fl, s['line'])}`")
    return "\n".join(L) + "\n"


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
            if s.get("hctx"):
                g.append("lands in " + s["hctx"])
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
    ap.add_argument("--jobs", type=int, default=None, help="parallel atomizer processes (default: min(8, cores))")
    ap.add_argument("--no-cross", action="store_true", help="skip pass 1: judge each file alone, as before cross-file sight")
    ap.add_argument("--json", default=None)
    ap.add_argument("--md", default=None)
    ap.add_argument("--summary", default=None, help="human summary: totals per file + REFUTED with code lines")
    a = ap.parse_args()
    out = run(a.paths, a.overlay, a.ctx, a.autoload, a.catalog, a.php, a.jobs, not a.no_cross)
    md = ledger_md(out)
    if a.summary:
        with open(a.summary, "w", encoding="utf-8") as fh:
            fh.write(summary_md(out))
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
