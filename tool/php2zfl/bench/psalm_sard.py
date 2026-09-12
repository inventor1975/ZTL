#!/usr/bin/env python3
"""
psalm_sard.py — the external denominator on the same corpus: Psalm 5 --taint-analysis over one SARD CWE dir
(safe/ + unsafe/), joined with the labels and with code2zfl's verdicts from bench/sard.py --out.

    CODE2ZFL_PSALM=/path/vendor/bin/psalm python3 bench/psalm_sard.py /tmp/sard/Injection/CWE_89 --types TaintedSql --ours /tmp/cwe89.json --mysqli

--mysqli: the CWE_89 corpus uses the removed mysql_* API, for which Psalm has no sink at all (0 TaintedSql on
9 552 files as they are); a copy is rewritten to mysqli_query($conn, ...) / mysqli_real_escape_string($conn, ...)
so that Psalm's taint LOGIC is what gets compared, not its catalog's age. Declared here, applied to the copy only.
"""
import sys, os, json, shutil, subprocess, collections, argparse, tempfile, time
PS = os.environ.get("CODE2ZFL_PSALM") or sys.exit("set CODE2ZFL_PSALM to a Psalm 5 binary (vendor/bin/psalm)")
ap = argparse.ArgumentParser(); ap.add_argument("cwe_dir"); ap.add_argument("--types", required=True, help="comma list of Psalm issue types that count as a hit")
ap.add_argument("--ours", required=True, help="bench JSON (v3/CWE_xx.json)"); ap.add_argument("--mysqli", action="store_true"); ap.add_argument("--out")
a = ap.parse_args()
types = set(a.types.split(","))
ours = {r["file"]: r for r in json.load(open(a.ours))}
work = tempfile.mkdtemp(prefix="psalm_"); 
files = {}
for lab in ("safe", "unsafe"):
    os.makedirs(os.path.join(work, lab))
    for f in sorted(os.listdir(os.path.join(a.cwe_dir, lab))):
        if not f.endswith(".php"): continue
        src = os.path.join(a.cwe_dir, lab, f); dst = os.path.join(work, lab, f)
        code = open(src, encoding="utf-8", errors="replace").read()
        if a.mysqli: code = code.replace("mysql_query(", "mysqli_query($conn, ").replace("mysql_real_escape_string(", "mysqli_real_escape_string($conn, ").replace("mysql_connect(", "mysqli_connect(")
        open(dst, "w", encoding="utf-8").write(code); files[f"{lab}/{f}"] = (lab, src)
open(os.path.join(work, "psalm.xml"), "w").write('<?xml version="1.0"?>\n<psalm errorLevel="8" resolveFromConfigFile="true" findUnusedCode="false" findUnusedBaselineEntry="false" xmlns="https://getpsalm.org/schema/config">\n<projectFiles><directory name="safe" /><directory name="unsafe" /></projectFiles></psalm>\n')
rep = os.path.join(work, "taint.json"); t0 = time.time()
r = subprocess.run([PS, "--config=psalm.xml", "--taint-analysis", "--no-cache", "--no-progress", "--threads=8", f"--report={rep}"], cwd=work, capture_output=True, text=True)
dt = time.time() - t0
if not os.path.exists(rep): sys.exit("no report: " + (r.stdout + r.stderr)[-2000:])
issues = json.load(open(rep)); hit = collections.defaultdict(set)
for i in issues: hit[i["file_name"]].add(i["type"])
print(f"psalm: {len(files)} files, {len(issues)} issues, {dt:.0f}s; types: {dict(collections.Counter(i['type'] for i in issues))}")
tot = collections.Counter(); bysan = collections.defaultdict(collections.Counter); rows = []
for rel, (lab, src) in files.items():
    p = bool(hit.get(rel, set()) & types); o = ours.get(src, {}).get("verdict", "?")
    san = os.path.basename(src).split("__")[2] if "__" in os.path.basename(src) else "?"
    tot[(lab, "psalm" if p else "silent")] += 1; tot[(lab, "ours:" + o)] += 1
    bysan[san][(lab, "P" if p else "-")] += 1; bysan[san][(lab, o[0])] += 1
    rows.append({"file": src, "label": lab, "psalm": p, "psalm_types": sorted(hit.get(rel, set())), "ours": o})
n = collections.Counter(l for l, _ in files.values())
print(f"unsafe n={n['unsafe']}: psalm HIT {tot[('unsafe','psalm')]}  silent {tot[('unsafe','silent')]}   | ours REFUTED {tot[('unsafe','ours:REFUTED')]} OPEN {tot[('unsafe','ours:OPEN')]} EARNED {tot[('unsafe','ours:EARNED')]}")
print(f"safe   n={n['safe']}: psalm ALARM {tot[('safe','psalm')]}  silent {tot[('safe','silent')]}   | ours REFUTED {tot[('safe','ours:REFUTED')]} OPEN {tot[('safe','ours:OPEN')]} EARNED {tot[('safe','ours:EARNED')]}")
print("by sanitizer:  unsafe[psalm hit / ours R O E]   safe[psalm alarm / ours R O E]")
for san in sorted(bysan):
    c = bysan[san]; u = sum(v for (l, k), v in c.items() if l == "unsafe" and k in "P-"); s = sum(v for (l, k), v in c.items() if l == "safe" and k in "P-")
    line = f"  {san[:46]:46}"
    if u: line += f" | unsafe {u:3}: P{c[('unsafe','P')]:3}  R{c[('unsafe','R')]:3} O{c[('unsafe','O')]:3} E{c[('unsafe','E')]:3}"
    if s: line += f" | safe {s:4}: P{c[('safe','P')]:3}  R{c[('safe','R')]:3} O{c[('safe','O')]:3} E{c[('safe','E')]:3}"
    print(line)
if a.out: json.dump(rows, open(a.out, "w"), indent=1)
shutil.rmtree(work)
