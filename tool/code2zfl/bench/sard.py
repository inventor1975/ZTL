#!/usr/bin/env python3
"""
sard.py — code2zfl against the SARD / Stivalet PHP vulnerability test suite (42 212 synthetic files, each labelled
safe/unsafe by its directory; file names carry SOURCE__SANITIZER__CONSTRUCTION).

    git clone --depth 1 https://github.com/stivalet/PHP-Vulnerability-test-suite.git /tmp/sard
    python3 bench/sard.py /tmp/sard/Injection/CWE_89 --ctx sql --out /tmp/cwe89.json

The file verdict is the WORST sink of that context in the file: REFUTED > OPEN > EARNED > NONE (no sink found);
E = parse error. The two numbers to read are printed first: unsafe->EARNED (the instrument says "clean" on a
planted flaw) and safe->REFUTED (an alarm on a fixed one). The tables by source / sanitizer / construction are
where a defect shows its shape. Measured numbers and the reading of every remaining disagreement: bench/README.md.
"""
import sys, os, json, time, argparse
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # tool/code2zfl
import code2zfl

RANK = {"REFUTED": 3, "OPEN": 2, "ON CREDIT": 2, "EARNED": 1}

def file_verdict(rec):
    if rec.get("parse_error"): return "E"
    best, worst = None, 0
    for s in rec["sinks"]:
        r = RANK.get(s["disposition"], 0)
        if r > worst: worst, best = r, s["disposition"]
    return {"ON CREDIT": "OPEN"}.get(best, best) or "NONE"

def tokens(path):
    b = os.path.basename(path)[:-4]
    p = b.split("__")
    while len(p) < 4: p.append("")
    return p[0], p[1], p[2], p[3]

ap = argparse.ArgumentParser()
ap.add_argument("dirs", nargs="+")
ap.add_argument("--ctx", default="sql")
ap.add_argument("--overlay", action="append", default=[])
ap.add_argument("--src", default=None, help="comma list of source tokens to keep")
ap.add_argument("--san", default=None)
ap.add_argument("--con", default=None, help="substring filter on construction token")
ap.add_argument("--limit", type=int, default=0)
ap.add_argument("--out", default=None)
ap.add_argument("--chunk", type=int, default=400)
a = ap.parse_args()

files = []
for d in a.dirs:
    for lab in ("safe", "unsafe"):
        p = os.path.join(d, lab)
        if not os.path.isdir(p): continue
        for f in sorted(os.listdir(p)):
            if not f.endswith(".php"): continue
            cwe, src, san, con = tokens(f)
            if a.src and src not in a.src.split(","): continue
            if a.san and san not in a.san.split(","): continue
            if a.con and a.con not in con: continue
            files.append((lab, os.path.join(p, f)))
if a.limit: files = files[:a.limit]
print(f"files: {len(files)}", file=sys.stderr)

t0 = time.time()
results = {}
paths = [f for _, f in files]
for i in range(0, len(paths), a.chunk):
    out = code2zfl.run(paths[i:i+a.chunk], a.overlay, a.ctx)
    for rec in out["files"]:
        results[rec["file"]] = rec
    print(f"  {min(i+a.chunk, len(paths))}/{len(paths)} {time.time()-t0:.0f}s", file=sys.stderr)
dt = time.time() - t0

rows = []
for lab, f in files:
    rec = results[f]
    v = file_verdict(rec)
    cwe, src, san, con = tokens(f)
    rows.append({"label": lab, "verdict": v, "cwe": cwe, "src": src, "san": san, "con": con, "file": f,
                 "sinks": [{"line": s["line"], "fn": s["fn"], "d": s["disposition"], "weak": s["weak"],
                            "t": s["tainted"]["means"], "s": s["sanitized"]["means"]} for s in rec.get("sinks", [])]})

def table(key):
    agg = defaultdict(Counter)
    for r in rows: agg[(r[key], r["label"])][r["verdict"]] += 1
    keys = sorted({k for k, _ in agg})
    print(f"\n== by {key}  (label -> REFUTED / OPEN / EARNED / NONE / E)")
    for k in keys:
        line = f"{k[:52]:52}"
        for lab in ("unsafe", "safe"):
            c = agg[(k, lab)]
            if sum(c.values()) == 0: continue
            line += f" | {lab:6} R{c['REFUTED']:4} O{c['OPEN']:4} E{c['EARNED']:4} N{c['NONE']:3} X{c['E']:2}"
        print(line)

tot = defaultdict(Counter)
for r in rows: tot[r["label"]][r["verdict"]] += 1
print(f"\n== TOTAL ctx={a.ctx} files={len(rows)} time={dt:.1f}s ({dt/max(1,len(rows))*1000:.0f} ms/file)")
for lab in ("unsafe", "safe"):
    c = tot[lab]; n = sum(c.values())
    if n: print(f"  {lab:6} n={n:5}  REFUTED {c['REFUTED']:5}  OPEN {c['OPEN']:5}  EARNED {c['EARNED']:5}  NONE {c['NONE']:4}  E {c['E']}")
u, s = tot["unsafe"], tot["safe"]
print(f"  unsafe->EARNED (MISS, says clean): {u['EARNED']}   safe->REFUTED (FALSE ALARM): {s['REFUTED']}")
for key in ("src", "san", "con"): table(key)
if a.out:
    json.dump(rows, open(a.out, "w"), ensure_ascii=False, indent=1)
