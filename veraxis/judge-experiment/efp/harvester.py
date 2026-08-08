#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""EFP harvester v0.1 — admits atoms into markings with witnesses.

Reads ONLY persisted corpus artifacts (the ledger git objects and the legacy
zip). Emits one marking JSON per gate: every T/F carries a witness supporting
that specific atom at that specific status (Protocol R-02/R-03); anything the
rules cannot support enters as Z (default-deny). No manual patching.

Usage: harvester.py <ledger_clone> <legacy_zip> <formulas.json> <out_dir>
"""
import ast, hashlib, io, json, os, re, subprocess, sys, zipfile
import xml.etree.ElementTree as ET

LEDGER, ZIPPATH, FORMULAS, OUT = sys.argv[1:5]

def git(*a):
    r = subprocess.run(["git", "-C", LEDGER] + list(a), capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[:200])
    return r.stdout

def git_bytes(*a):
    r = subprocess.run(["git", "-C", LEDGER] + list(a), capture_output=True)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.decode()[:200])
    return r.stdout

def blob(head, path):
    return git_bytes("show", f"{head}:{path}")

def tree_paths(head, prefix=""):
    return [l for l in git("ls-tree", "-r", "--name-only", head, prefix or ".").splitlines() if l]

_zip = zipfile.ZipFile(ZIPPATH)
def zmember(name):
    return _zip.read(name)

def sha(b): return hashlib.sha256(b).hexdigest()

def wit(kind, **kw):
    return {"kind": kind, **kw}

# ------------------------------------------------------------- rule handlers
def r_tree_identity(a):
    head = a["args"]["head"]
    tree = git("rev-parse", f"{head}^{{tree}}").strip()
    return ("T", wit("git-commit", head=head, tree=tree))

def _diff(base, head):
    return [l for l in git("diff", "--name-only", base, head).splitlines() if l]

def r_path_confinement(a):
    g = a["args"]
    paths = _diff(g["base"], g["head"])
    ok = all(any(p.startswith(px) for px in g["prefixes"]) for p in paths) and paths
    w = wit("git-tree-diff", base=g["base"], head=g["head"], paths_sha256=sha("\n".join(paths).encode()), n=len(paths))
    return ("T" if ok else "F", w)

def r_changed_file_set(a):
    g = a["args"]
    paths = sorted(_diff(g["base"], g["head"]))
    ok = paths == sorted(g["expected"])
    return ("T" if ok else "F", wit("git-tree-diff", base=g["base"], head=g["head"],
                                    paths=paths))

def r_member_identity(a):
    g = a["args"]
    try: d = blob(g["head"], g["path"])
    except RuntimeError: return ("F", wit("git-blob-missing", head=g["head"], path=g["path"]))
    ok = (len(d) == g["bytes"] and sha(d) == g["sha256"]
          and (("sha512" not in g) or hashlib.sha512(d).hexdigest() == g["sha512"]))
    return ("T" if ok else "F", wit("git-blob", head=g["head"], path=g["path"],
                                    bytes=len(d), sha256=sha(d)))

def _manifest_check(members_decl, physical, field_bytes, get_bytes, manifest_name):
    declared = {}
    for e in members_decl:
        p = e["path"]
        if p in declared: return False, f"duplicate {p}"
        declared[p] = e
    for p, e in declared.items():
        try: d = get_bytes(p)
        except Exception: return False, f"missing {p}"
        if not (e.get(field_bytes) == len(d) and e["sha256"] == sha(d)
                and (("sha512" not in e) or hashlib.sha512(d).hexdigest() == e["sha512"])):
            return False, f"mismatch {p}"
    und = set(physical) - set(declared) - {manifest_name}
    if und: return False, f"unmanifested {sorted(und)[:3]}"
    return True, "ok"

def r_manifest_accounting(a):
    g = a["args"]
    man = json.loads(blob(g["head"], g["manifest"]))
    root = g["root"]
    phys = [p[len(root):] for p in tree_paths(g["head"], root)]
    # manifest paths may be root-relative
    ok, why = _manifest_check(man["members"], phys, g["member_field_bytes"],
                              lambda p: blob(g["head"], root + p if not p.startswith(root) else p),
                              g["manifest"][len(root):])
    return ("T" if ok else "F", wit("git-manifest", head=g["head"], manifest=g["manifest"], detail=why))

def r_json_field(a):
    g = a["args"]
    try: d = json.loads(blob(g["head"], g["path"]))
    except RuntimeError: return ("Z", wit("git-blob-missing", head=g["head"], path=g["path"]))
    val = d.get(g["field"], "<ABSENT>")
    ok = val == g["expected"]
    return ("T" if ok else "F", wit("git-json", head=g["head"], path=g["path"],
                                    sha256=sha(blob(g["head"], g["path"])), field=g["field"], value=val))

def r_json_all_true(a):
    g = a["args"]
    d = json.loads(blob(g["head"], g["path"]))
    arr = d.get(g["array"], [])
    ok = bool(arr) and all(e.get(g["field"]) is True for e in arr)
    return ("T" if ok else "F", wit("git-json", head=g["head"], path=g["path"],
                                    sha256=sha(blob(g["head"], g["path"])), n=len(arr)))

def r_file_bytes(a):
    g = a["args"]
    try: d = blob(g["head"], g["path"])
    except RuntimeError: return ("F", wit("git-blob-missing", head=g["head"], path=g["path"]))
    if "n" in g: ok = len(d) == g["n"]
    else: ok = len(d) <= g.get("n_max", 0)
    return ("T" if ok else "F", wit("git-blob", head=g["head"], path=g["path"], bytes=len(d)))

def r_file_equals(a):
    g = a["args"]
    try: d = blob(g["head"], g["path"])
    except RuntimeError: return ("F", wit("git-blob-missing", head=g["head"], path=g["path"]))
    if "equals_path" in g:
        ok = d == blob(g["head"], g["equals_path"])
    elif "json_equals" in g:
        try: ok = json.loads(d) == g["json_equals"]
        except Exception: ok = False
    else:
        t = d.decode()
        ok = t == g["literal"] or ("alt_literal" in g and t == g["alt_literal"])
    return ("T" if ok else "F", wit("git-blob", head=g["head"], path=g["path"], sha256=sha(d)))

def r_file_absent(a):
    g = a["args"]
    present = g["path"] in tree_paths(g["head"], os.path.dirname(g["path"]) + "/")
    return ("T" if not present else "F", wit("git-tree", head=g["head"], path=g["path"], present=present))

def r_argv_equals(a):
    g = a["args"]
    d = json.loads(blob(g["head"], g["path"]))
    ok = d == g["argv"]
    return ("T" if ok else "F", wit("git-json", head=g["head"], path=g["path"],
                                    sha256=sha(blob(g["head"], g["path"]))))

def _junit(data):
    r = ET.fromstring(data)
    suite = r if r.tag == "testsuite" else r.find("testsuite")
    cases = {}
    for tc in suite.iter("testcase"):
        nid = f"{tc.get('classname')}::{tc.get('name')}"
        st = "F" if (tc.find("failure") is not None or tc.find("error") is not None) \
             else ("S" if tc.find("skipped") is not None else "P")
        cases[nid] = st
    return cases

def _junit_src(a):
    g = a["args"]
    if "head" in g: return blob(g["head"], g["path"]), wit("git-blob", head=g["head"], path=g["path"])
    return zmember(g["member"]), wit("zip-member", zip_sha256=g["zip_sha256"], member=g["member"])

def r_junit_counts(a):
    g = a["args"]
    data, w = _junit_src(a)
    c = _junit(data)
    got = (len(c), sum(1 for v in c.values() if v == "P"),
           sum(1 for v in c.values() if v == "F"), sum(1 for v in c.values() if v == "S"))
    ok = got == (g["collected"], g["passed"], g["failed"], g["skipped"])
    w["counts"] = got
    return ("T" if ok else "F", w)

def r_junit_failing_set(a):
    g = a["args"]
    data, w = _junit_src(a)
    c = _junit(data)
    fails = sorted(k for k, v in c.items() if v == "F")
    ok = fails == sorted(g["expected"])
    w["failing"] = fails
    return ("T" if ok else "F", w)

def r_zip_member_identity(a):
    g = a["args"]
    try: d = zmember(g["member"])
    except KeyError: return ("F", wit("zip-member-missing", member=g["member"]))
    ok = len(d) == g["bytes"] and sha(d) == g["sha256"]
    return ("T" if ok else "F", wit("zip-member", zip_sha256=g["zip_sha256"], member=g["member"],
                                    bytes=len(d), sha256=sha(d)))

def r_zip_manifest_accounting(a):
    g = a["args"]
    man = json.loads(zmember(g["manifest"]))
    phys = [i.filename for i in _zip.infolist() if not i.is_dir()]
    ok, why = _manifest_check(man["members"], phys, g["member_field_bytes"],
                              zmember, g["manifest"])
    return ("T" if ok else "F", wit("zip-manifest", zip_sha256=g["zip_sha256"], detail=why))

def r_ast_confinement(a):
    g = a["args"]
    s0 = zmember(g["s0"]).decode(); s1 = zmember(g["s1"]).decode()
    def units(src):
        t = ast.parse(src)
        return {getattr(n, "name", f"stmt@{n.lineno}"): ast.get_source_segment(src, n) for n in t.body}
    u0, u1 = units(s0), units(s1)
    changed = sorted(k for k in u0 if k in u1 and u0[k] != u1[k])
    same_keys = set(u0) == set(u1)
    within = set(changed) <= set(g["allowed_units"])
    import difflib
    hunks = 0
    for k in changed:
        d = list(difflib.unified_diff(u0[k].splitlines(), u1[k].splitlines(), lineterm="", n=0))
        hunks += sum(1 for ln in d if ln.startswith("@@"))
    iso_same = u0[g["byte_identical_unit"]] == u1[g["byte_identical_unit"]]
    ok = (same_keys and within and len(changed) == g["expected_changed"]
          and hunks == g["expected_hunks"] and iso_same)
    return ("T" if ok else "F", wit("zip-ast-diff", zip_sha256=g["zip_sha256"],
                                    changed=changed, hunks=hunks, iso_identical=iso_same))

HANDLERS = {
 "tree_identity": r_tree_identity, "path_confinement": r_path_confinement,
 "changed_file_set": r_changed_file_set, "member_identity": r_member_identity,
 "manifest_accounting": r_manifest_accounting, "json_field": r_json_field,
 "json_all_true": r_json_all_true, "file_bytes": r_file_bytes,
 "file_equals": r_file_equals, "file_absent": r_file_absent,
 "argv_equals": r_argv_equals, "junit_counts": r_junit_counts,
 "junit_failing_set": r_junit_failing_set, "zip_member_identity": r_zip_member_identity,
 "zip_manifest_accounting": r_zip_manifest_accounting, "ast_confinement": r_ast_confinement,
 "doc_cites": None,  # reserved; unimplemented rules yield Z
}

def main():
    spec = json.load(open(FORMULAS))
    os.makedirs(OUT, exist_ok=True)
    harv_id = sha(open(__file__, "rb").read())
    summary = []
    for gate in spec["gates"]:
        marking = {}
        for atom in gate["atoms"]:
            h = HANDLERS.get(atom["rule"])
            if h is None:
                marking[atom["atom"]] = {"status": "Z", "witness": None,
                                         "reason": "rule not implementable over persisted corpus"}
                continue
            try:
                st, w = h(atom)
            except Exception as e:
                st, w = "Z", {"kind": "harvest-error", "error": str(e)[:160]}
            marking[atom["atom"]] = {"status": st, "witness": w if st in ("T", "F") else w}
        doc = {"gate_id": gate["gate_id"], "item_id": gate["item_id"],
               "formula": gate["formula"], "marking": marking,
               "harvester_sha256": harv_id}
        p = os.path.join(OUT, gate["gate_id"] + ".marking.json")
        json.dump(doc, open(p, "w"), indent=1, ensure_ascii=False)
        summary.append((gate["gate_id"],
                        sum(1 for v in marking.values() if v["status"] == "T"),
                        sum(1 for v in marking.values() if v["status"] == "F"),
                        sum(1 for v in marking.values() if v["status"] == "Z")))
    print(f"harvester {harv_id[:16]}: {len(summary)} markings")
    for gid, t, f, z in summary:
        flag = "" if f == 0 and z == 0 else ("  <-- F present" if f else "  <-- Z present")
        print(f"  {gid:26s} T={t:3d} F={f} Z={z}{flag}")

if __name__ == "__main__":
    main()
