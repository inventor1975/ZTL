#!/usr/bin/env python3
"""
census.py — code2zfl over many project trees at once, keeping only what is worth keeping: the verdict
counts and the NAMED boundaries behind every OPEN. A labelled corpus scores the files that came back;
this one also shows the trees that did not come back at all, which is how three fatal defects were
found in this pass (bench/README.md, "Real projects, not synthetic").

    python3 bench/census.py <dir-of-projects> out.json

One line per project as it finishes, and out.json rewritten each time, so a run that dies halfway
still leaves everything before it. Per project it keeps counters only — 200 000 files fit in memory.
"""
import sys, os, json, time, collections
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))   # tool/code2zfl
import code2zfl

root, out = sys.argv[1], sys.argv[2]
res = {}
for p in sorted(q for q in os.listdir(root) if os.path.isdir(os.path.join(root, q))):
    t0 = time.time()
    try:
        o = code2zfl.run([os.path.join(root, p)], [], "all", None, jobs=16)
    except SystemExit as e:                      # atoms.php said no, loudly: that IS the finding
        res[p] = {"error": str(e)}; print(p, "ERROR", str(e)[:200], flush=True); continue
    except Exception as e:
        res[p] = {"error": repr(e)[:300]}; print(p, "EXC", repr(e)[:160], flush=True); continue
    disp, causes, kinds = collections.Counter(), collections.Counter(), collections.Counter()
    parse_err = 0
    for f in o["files"]:
        if f.get("parse_error"):
            parse_err += 1
        for s in f.get("sinks", []):
            disp[s["disposition"]] += 1
            if s["disposition"] != "OPEN":
                continue
            # the causes are the point: an OPEN that cannot name its boundary is a bug in the ledger
            ks = set()
            for c in (x.strip() for x in s["tainted"]["means"].split("in this file:", 1)[-1].split(",")):
                if not c:
                    continue
                name = c.rsplit("@", 1)[0]
                causes[name] += 1
                ks.add(name.split(":", 1)[0])
            kinds[frozenset(ks)] += 1
    res[p] = {"files": len(o["files"]), "parse_error": parse_err, "disp": dict(disp),
              "sec": round(time.time() - t0, 1), "causes": causes.most_common(60),
              "kinds": [[sorted(k), n] for k, n in kinds.most_common(25)]}
    print(f"{p:28} {len(o['files']):6} files {res[p]['sec']:7}s  {dict(disp)}", flush=True)
    json.dump(res, open(out, "w"), indent=1)
print("done")
