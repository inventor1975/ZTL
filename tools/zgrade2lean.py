"""zgrade2lean — the judge's verdicts as Lean theorems (lean/ZGrade.lean). Untrusted: Lean's kernel decides.

    python3 tools/zgrade2lean.py STAND.py [STAND2.py ...] --out lean/gen/ZGradeRun.lean

Runs each stand with `zverify.grade` instrumented, records every call made without a budget — (formula,
marking, grade, value) — and writes one Lean theorem per DISTINCT call:

    theorem gN : grade m φ = .hereditary ∧ evalF m φ = .T := by decide +kernel

so the kernel recomputes the grade and the value; a disagreement between the Python judge and the Lean
definitions fails the file. Marks (`"M"`) become refinable `Z`; a FIXED unknown (`"Z"`, `"E"` — never
refined by `grade`) becomes the constant `.cst .Z` in the formula, which is exactly how `grade` treats it.
"""
import json, os, runpy, sys, io, contextlib

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

GRADES = {"hereditary": ".hereditary", "sound": ".sound", "until-verification": ".untilVerification"}
VAL = {"T": "V.T", "F": "V.F", "Z": "V.Z"}
OPS = {"and": "conj", "or": "disj", "imp": "imp", "xor": "xor", "xnor": "xnor"}


def record_stand(path, calls):
    path = os.path.abspath(path)
    import zverify
    orig = zverify.grade

    def grade(phi, marking, budget=None):
        g = orig(phi, marking, budget)
        if budget is None:
            calls.append((phi, dict(marking), g, os.path.basename(path)))
        return g
    zverify.grade = grade
    # modules that imported `grade` by name: patch them too — and RESTORE them after (a wrapper left behind
    # would record the next stand's calls under this stand's name)
    patched = []
    for mod in list(sys.modules.values()):
        if mod is not None and getattr(mod, "grade", None) is orig:
            try:
                setattr(mod, "grade", grade); patched.append(mod)
            except Exception:
                pass
    old = os.getcwd()
    d = os.path.dirname(path)
    added = d not in sys.path
    if added:
        sys.path.insert(0, d)
    try:
        os.chdir(d)
        with contextlib.redirect_stdout(io.StringIO()):
            runpy.run_path(path, run_name="__main__")
    except SystemExit:
        pass
    finally:
        os.chdir(old)
        if added:
            sys.path.remove(d)
        zverify.grade = orig
        for mod in patched:
            setattr(mod, "grade", orig)
        # modules first imported DURING the stand may hold the wrapper too
        for mod in list(sys.modules.values()):
            if mod is not None and getattr(mod, "grade", None) is grade:
                try:
                    setattr(mod, "grade", orig)
                except Exception:
                    pass


def lean_fm(phi, idx, fixedZ):
    if isinstance(phi, str):
        if phi in VAL:
            return f"(.cst {VAL[phi]})"
        if phi in fixedZ:
            return "(.cst V.Z)"
        return f"(.atom {idx[phi]})"
    if phi[0] == "not":
        return f"(.neg {lean_fm(phi[1], idx, fixedZ)})"
    return f"(.{OPS[phi[0]]} {lean_fm(phi[1], idx, fixedZ)} {lean_fm(phi[2], idx, fixedZ)})"


def lean_marking(marking, idx):
    out = "V.Z"
    for a, i in sorted(idx.items(), key=lambda t: -t[1]):
        v = marking.get(a, "M")
        lv = VAL[v] if v in ("T", "F") else "V.Z"
        out = f"(cond (Nat.beq n {i}) {lv} {out})"
    return f"fun n => {out}"


HEAVY = 8          # marks from which the kernel's 3^k walk is replaced by a witness


def witness(phi, marking, marks, v, tries=20000):
    """A completion of the marks (the list of marks read F) that changes the value, or None."""
    from zmodal import ztl_eval
    import itertools, random
    cands = [[], list(marks)] + [[a] for a in marks] + [[b for b in marks if b != a] for a in marks]
    rnd = random.Random(7)
    for _ in range(tries):
        cands.append([a for a in marks if rnd.random() < 0.5])
    for S in cands:
        w = dict(marking); w.update({a: ("F" if a in S else "T") for a in marks})
        if ztl_eval(phi, w) != v:
            return S
    return None


def emit(calls, out):
    from ztl import atoms
    from zmodal import ztl_eval
    seen, thms, skipped = set(), [], {}
    for phi, marking, g, stand in calls:
        if g not in GRADES:
            skipped[g] = skipped.get(g, 0) + 1
            continue
        key = (repr(phi), repr(sorted(marking.items())))
        if key in seen:
            continue
        seen.add(key)
        ats = sorted(atoms(phi))
        fixedZ = {a for a in ats if marking.get(a, "M") not in ("T", "F", "M")}
        idx = {a: i for i, a in enumerate(a for a in ats if a not in fixedZ)}
        v = ztl_eval(phi, marking)
        n = len(thms)
        marks = [a for a in ats if marking.get(a, "M") == "M"]
        if len(marks) >= HEAVY:
            # walking 3^k readings in the kernel is out of reach: a NEGATIVE grade gets a witness completion
            if g != "until-verification":
                skipped["heavy " + g] = skipped.get("heavy " + g, 0) + 1
                continue
            S = witness(phi, marking, marks, v)
            if S is None:
                skipped["heavy, no witness found"] = skipped.get("heavy, no witness found", 0) + 1
                continue
            mk, fm = lean_marking(marking, idx), lean_fm(phi, idx, fixedZ)
            thms.append((stand, f"theorem g{n} : (¬ Stable ({mk}) {fm} ∧ ¬ Hered ({mk}) {fm}) ∧\n"
                                f"    evalF ({mk}) {fm} = {VAL[v]} :=\n"
                                f"  ⟨notStable_witness [{', '.join(str(idx[a]) for a in S)}] (by decide +kernel), by decide +kernel⟩"))
            continue
        thms.append((stand, f"theorem g{n} : grade ({lean_marking(marking, idx)}) {lean_fm(phi, idx, fixedZ)} = {GRADES[g]} ∧\n"
                            f"    evalF ({lean_marking(marking, idx)}) {lean_fm(phi, idx, fixedZ)} = {VAL[v]} := by decide +kernel"))
    by = {}
    for stand, t in thms:
        by.setdefault(stand, []).append(t)
    files, CH = [], 2000
    for stand, ts in by.items():
        for c in range(0, len(ts), CH):
            part = ts[c:c + CH]
            mod = "ZGradeRun_" + stand[:-3].replace("-", "_") + (f"_{c // CH}" if len(ts) > CH else "")
            fn = os.path.join(out, mod + ".lean")
            hdr = ["import ZGrade", "open ZGrade", "set_option maxRecDepth 100000", "",
                   f"/-! The judge's verdicts of `dilemmas/{stand}` (distinct calls {c}..{c + len(part) - 1} of {len(ts)}),",
                   "recomputed by the kernel. -/", ""]
            open(fn, "w").write("\n".join(hdr + part) + "\n")
            files.append(fn)
    return len(thms), skipped, files


if __name__ == "__main__":
    args = sys.argv[1:]
    out = args[args.index("--out") + 1] if "--out" in args else os.path.join(ROOT, "lean", "gen")
    stands = [a for a in args if a.endswith(".py")]
    os.makedirs(out, exist_ok=True)
    calls, per = [], {}
    for s in stands:
        before = len(calls)
        try:
            record_stand(s, calls)
            per[os.path.basename(s)] = len(calls) - before
        except Exception as e:                      # a stand that fails is reported, not hidden
            per[os.path.basename(s)] = f"FAILED: {type(e).__name__}: {str(e)[:80]}"
    n, skipped, files = emit(calls, out)
    print(json.dumps({"stands": per, "calls": len(calls), "theorems": n, "skipped": skipped, "files": len(files), "out": out},
                     ensure_ascii=False, indent=1))
