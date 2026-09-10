#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
fixbench — measure the tool against SECURITY FIXES the authors made themselves.

A labelled corpus tells you whether the instrument sees what a generator planted. This tells you
something the generator cannot: whether it sees what a real developer, in real code, later admitted
was a hole. The ground truth is the project's own history — a commit whose message says it fixes a
security problem — so it depends neither on a CVE database nor on anyone's memory.

For each such commit the tool runs on the tree BEFORE and the tree AFTER, over the files that
commit touched, and the pair is classified:

    CAUGHT      a REFUTED in a touched file before, and it is gone after
    STILL       REFUTED before and after — our verdict is about something the fix did not address
    MISSED      the touched files have sinks and every one came back EARNED — we said CLEAN where the
                author later escaped: a real miss
    OPENED      no REFUTED, but OPEN verdicts on those files: we named the place and refused to
                judge it. Not a hit and not silence — measured 2026-09-09, this is most of what
                looked like silence, and it is nearly always a value read back out of the database
                (`get_option`), where our answer is Z by policy
    NO-SINK     the touched files contain no sink at all — the vulnerable call is elsewhere, and
                there is nothing here for this instrument to judge
    NOISE       no REFUTED before, some after — the fix introduced a shape we dislike

CAUGHT is the only class that counts as a hit, and even it is coarse: it says the verdict moved
with the fix, not that our reasoning matched the developer's. Read the pair before claiming one.

    python3 bench/fixbench.py /path/to/plugin-clone [--overlay ...] [--jobs N] [--max N] [--out f.json]
"""
import argparse, json, os, re, subprocess, sys, tempfile, shutil, collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import code2zfl                                                            # noqa: E402

WORDS = r"security|vulnerab|xss|sql inject|injection|sanitiz|escap|csrf|traversal|rce|exploit|cve-"


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True).stdout


def fix_commits(repo, limit):
    out = git(repo, "log", "--all", "--format=%H\x1f%s")
    rows = []
    for line in out.splitlines():
        if "\x1f" not in line:
            continue
        h, subj = line.split("\x1f", 1)
        if re.search(WORDS, subj, re.I):
            rows.append((h, subj.strip()))
    return rows[:limit]


def touched_php(repo, h):
    out = git(repo, "diff-tree", "--no-commit-id", "--name-only", "-r", h)
    return [p for p in out.split() if p.endswith(".php")]


def tree_at(repo, h, dest):
    os.makedirs(dest, exist_ok=True)
    p = subprocess.Popen(["git", "-C", repo, "archive", h], stdout=subprocess.PIPE)
    subprocess.run(["tar", "-x", "-C", dest], stdin=p.stdout)
    p.wait()


def refuted_in(out, files):
    want = {os.path.normpath(f) for f in files}
    hits = []
    for f in out["files"]:
        rel = os.path.normpath(os.path.relpath(f["file"], f["_root"])) if "_root" in f else None
        for s in f["sinks"]:
            if s["disposition"] != "REFUTED":
                continue
            base = f["file"]
            if any(base.endswith(os.sep + w) or os.path.normpath(base).endswith(w) for w in want):
                hits.append((base.split(os.sep)[-1], s["line"], s["ctx"], s["fn"]))
    return hits


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("repo")
    ap.add_argument("--overlay", action="append", default=[])
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--max", type=int, default=40)
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    repo = os.path.abspath(a.repo)
    name = os.path.basename(repo.rstrip("/"))
    commits = fix_commits(repo, a.max)
    print(f"{name}: {len(commits)} security-worded commits")
    tally = collections.Counter()
    narrowed_n = 0
    # A WORDPRESS PLUGIN WITHOUT THE WORDPRESS OVERLAY IS MEASURED WITH ITS OWN SINKS INVISIBLE.
    # `$wpdb->get_var` is not in the base catalog, so `WHERE user_id=$user_id` is not a sink at all and
    # the line the developer fixed does not exist for the instrument. MEASURED 2026-09-10:
    # user-role-editor CAUGHT 4 with the overlay and 2 without, wp-e-commerce 11 and 10. A warning, not
    # a default — the run must stay exactly what the caller asked for.
    if not any("wordpress" in o for o in (a.overlay or [])):
        probe = subprocess.run(["grep", "-rlq", "--include=*.php", r"\$wpdb->", repo],
                               capture_output=True, text=True)
        if probe.returncode == 0:
            print("  ВНИМАНИЕ: дерево пользуется $wpdb, а overlays/wordpress.json не подан — "
                  "$wpdb->get_var и родня НЕ считаются стоками, и числа будут занижены.")
    rows = []
    for h, subj in commits:
        files = touched_php(repo, h)
        if not files:
            tally["no-php"] += 1
            continue
        work = tempfile.mkdtemp(prefix="fixbench_")
        try:
            before, after = os.path.join(work, "b"), os.path.join(work, "a")
            tree_at(repo, h + "^", before)
            tree_at(repo, h, after)
            present = [f for f in files if os.path.exists(os.path.join(before, f))]
            if not present:
                tally["added-only"] += 1
                continue
            ob = code2zfl.run([os.path.join(before, f) for f in present], a.overlay, "all", jobs=a.jobs)
            oa = code2zfl.run([os.path.join(after, f) for f in present if os.path.exists(os.path.join(after, f))],
                              a.overlay, "all", jobs=a.jobs)
            rb = [(os.path.basename(f["file"]), s["line"], s["ctx"], s["fn"])
                  for f in ob["files"] for s in f["sinks"] if s["disposition"] == "REFUTED"]
            ra = [(os.path.basename(f["file"]), s["line"], s["ctx"], s["fn"])
                  for f in oa["files"] for s in f["sinks"] if s["disposition"] == "REFUTED"]
            # SILENT has two meanings and they must not be one word. If the touched files contain no
            # sink of any kind, there is nothing here to judge — the vulnerable call lives in another
            # package (measured: wp-fastest-cache's SQLi fix guards a value passed to check_voted(),
            # which belongs to a different plugin that is not in this tree). Only a file that HAS
            # sinks and still produced no REFUTED is a miss of ours.
            sinks_before = sum(len(f["sinks"]) for f in ob["files"])
            open_before = sum(1 for f in ob["files"] for s in f["sinks"] if s["disposition"] == "OPEN")
            earned_only = sinks_before > 0 and open_before == 0
            # DID OUR VERDICT MOVE THE WAY THE FIX MOVED? Counted only to READ the OPENED bucket, never
            # folded into CAUGHT: a benchmark that renames its own misses into a nicer word is a
            # benchmark measuring itself. `ure_has_administrator_role($user_id)` is the shape — the
            # parameter's origin is outside the file, so we say OPEN both before and after, but the fix
            # added `is_numeric($user_id)` and after it the same sink is EARNED. That is the instrument
            # seeing the developer's change without ever having said REFUTED.
            sinks_after = sum(len(f["sinks"]) for f in oa["files"])
            open_after = sum(1 for f in oa["files"] for s in f["sinks"] if s["disposition"] == "OPEN")
            earn_before = sum(1 for f in ob["files"] for s in f["sinks"] if s["disposition"] == "EARNED")
            earn_after = sum(1 for f in oa["files"] for s in f["sinks"] if s["disposition"] == "EARNED")
            narrowed = (sinks_before == sinks_after and open_after < open_before
                        and earn_after > earn_before)
            if rb and len(ra) < len(rb):
                verdict = "CAUGHT"
            elif rb:
                verdict = "STILL"
            elif ra:
                verdict = "NOISE"
            elif sinks_before == 0:
                verdict = "NO-SINK"
            elif earned_only:
                verdict = "MISSED"          # we said CLEAN on every sink here: a real miss
            else:
                verdict = "OPENED"          # we named the place and withheld the verdict, not silence
            tally[verdict] += 1
            if verdict == "OPENED" and narrowed:
                narrowed_n += 1
            rows.append({"commit": h[:9], "subject": subj[:90], "files": present[:4],
                         "before": len(rb), "after": len(ra), "sinks": sinks_before,
                         "open_before": open_before, "open_after": open_after,
                         "earned_before": earn_before, "earned_after": earn_after,
                         "narrowed": narrowed, "verdict": verdict, "sample": rb[:3]})
            print(f"  {verdict:7} {h[:9]}  R{len(rb):3}→{len(ra):<3} O{open_before:<4}→{open_after:<4} "
                  f"E{earn_before:<4}→{earn_after:<4}{' NARROWED' if narrowed else ''} sinks={sinks_before:3}  {subj[:40]}")
        finally:
            shutil.rmtree(work, ignore_errors=True)
    print("  " + " | ".join(f"{k}: {v}" for k, v in sorted(tally.items())))
    if narrowed_n:
        print(f"  of the OPENED, {narrowed_n} NARROWED: our verdict moved the way the fix moved "
              f"(OPEN -> EARNED on the same sinks) without ever having said REFUTED")
    # A NUMBER MUST NOT TRAVEL WITHOUT ITS CONDITIONS. Three times on 2026-09-10 a figure measured under
    # one setup was compared with a figure measured under another and the difference read as a defect —
    # once a different tree, once a different clone, once THIS: a WordPress plugin run without
    # overlays/wordpress.json, where $wpdb->get_var is not a sink at all and the very line the developer
    # fixed does not exist for the instrument (user-role-editor CAUGHT 4 with the overlay, 2 without).
    print(f"  conditions: overlays={a.overlay or ['(none)']} jobs={a.jobs} repo={repo}")
    if a.out:
        json.dump({"repo": name, "tally": dict(tally), "rows": rows}, open(a.out, "w"), ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
