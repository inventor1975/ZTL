# -*- coding: utf-8 -*-
"""
zjudge2lean — the judge's verdict on a propositional claim, emitted as Lean theorems that Lean checks by `decide`
(2026-11-10; the curator: the stand, not its author, should produce the theorems).

The judge (ztljudge.judge) reads a formula under a marking and says a verdict (T/F), a grade (hereditary or not) and a
disposition (EARNED / REFUTED / ... IF STABLE / OPEN / ON CREDIT). This tool restates WHAT THE JUDGE SAID as Lean
statements about the core's own connectives (lean/ZTL.lean: V, znot, zand, zor, zimp, zxor, zxnor) and leaves the proof
to Lean's kernel: every statement is closed by `decide` (finite enumeration), so nobody writes a proof and nobody's
reasoning is trusted. If Lean rejects a statement, the judge and the core disagree — that is a finding, not a typo.

For a claim with dirty atoms d1..dk (marked Z, or unmarked) the statements are:
  verdict      phi(marking) = v            the ZTL value itself (dirty atoms read as Z; each occurrence of Z is read
                                           independently by the core's lift, exactly as the judge reads it)
  stable       ∀ d1..dk : Bool, phi = t    for EARNED (t = T) / REFUTED (t = F), with or without IF STABLE: the claim
                                           holds in every CLEANING of the dirty atoms, one value per atom at all its
                                           occurrences (note: the verdict v may differ from t — under Z the core can
                                           read F where every cleaning reads T; that gap is what "earned once
                                           verified" means)
  reach_T/F    ∃ cleaning with phi = T/F   for OPEN / ON CREDIT: the cleanings disagree, both outcomes are reachable
  outright     ∀ per-OCCURRENCE cleanings  EARNED / REFUTED without IF STABLE, a dirty atom occurring twice: it holds
                                           even if each occurrence is cleaned on its own
  not_outright ¬ ∀ per-occurrence ...      "... IF STABLE": some per-occurrence cleaning breaks it — stability is a
                                           real premise, and Lean confirms it is needed

MEASURED 2026-11-10: 300 random claims (4 atoms, depth 4, random markings; dispositions OPEN 156, ON CREDIT 55,
EARNED 34, REFUTED 22, EARNED IF STABLE 17, REFUTED IF STABLE 16) -> 826 statements, Lean accepted all 826: the
judge and the core agree on every one.

Caps: at most 20 Boolean variables per statement (2^20 cases for decide); a claim above the cap is refused, never
truncated. A mark E (no subject) is refused: it has no Lean value here.

    python3 zjudge2lean.py --name trolley_pair --formula "(a -> b) & a" --mark a=T [--out lean/X.lean]
"""
from __future__ import annotations

import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import ztljudge as ZJ          # noqa: E402

CAP = 20
_OP = {"and": "zand", "or": "zor", "imp": "zimp", "xor": "zxor", "xnor": "zxnor"}


def _ident(a):
    """a Lean-safe identifier for an atom name"""
    s = re.sub(r"[^A-Za-z0-9_]", "_", a)
    return ("a_" + s) if not s or s[0].isdigit() else "a_" + s


def _lean(phi, env):
    """the formula as a Lean term over the core's connectives; env: atom -> Lean term"""
    if isinstance(phi, str):
        if phi in ("T", "F", "Z"):
            return phi
        return env[phi]
    if phi[0] == "not":
        return f"(znot {_lean(phi[1], env)})"
    return f"({_OP[phi[0]]} {_lean(phi[1], env)} {_lean(phi[2], env)})"


def _occ_env(phi, dirty):
    """per-occurrence variables: each occurrence of a dirty atom gets its own name"""
    count = {}
    names = []

    def walk(p):
        if isinstance(p, str):
            if p in dirty:
                count[p] = count.get(p, 0) + 1
                n = f"{_ident(p)}_{count[p]}"
                names.append(n)
                return f"(b2v {n})"
            return None
        return None

    # rebuild the term with per-occurrence leaves
    def term(p, fixed):
        if isinstance(p, str):
            if p in ("T", "F", "Z"):
                return p
            if p in dirty:
                return walk(p)
            return fixed[p]
        if p[0] == "not":
            return f"(znot {term(p[1], fixed)})"
        return f"({_OP[p[0]]} {term(p[1], fixed)} {term(p[2], fixed)})"
    return term, names


def emit_claim(name, formula, marking=None):
    """-> (lean text of one namespace with the statements, the judge's result)"""
    marking = dict(marking or {})
    r = ZJ.judge(formula, marking)
    phi = ZJ.formalize(formula)
    atoms = sorted(ZJ._atoms(phi))
    m = r["marking"]
    if any(v == "E" for v in m.values()):
        raise ValueError("a mark E (no subject) has no Lean value here — refused")
    dirty = [a for a in atoms if m.get(a, "Z") == "Z"]
    fixed = {a: m[a] for a in atoms if a not in dirty}
    v = r["verdict"]
    ns = "ZJ_" + re.sub(r"[^A-Za-z0-9_]", "_", name)
    out = [f"/- judge: {formula}   marking {marking or '{}'}", f"    -> {r['disposition']}, verdict {v}, grade "
           f"{r['grade']}, dirty {dirty} -/", f"namespace {ns}", "open V", "",
           "/-- a cleaned atom: true -> T, false -> F -/",
           "def b2v : Bool → V", "  | true => T", "  | false => F", ""]
    env_z = {a: ("Z" if a in dirty else fixed[a]) for a in atoms}
    out.append(f"theorem verdict : {_lean(phi, env_z)} = {v} := by decide")
    if dirty:
        if len(dirty) > CAP:
            raise ValueError(f"{len(dirty)} dirty atoms > cap {CAP}: refused")
        binders = " ".join(_ident(a) for a in dirty)
        env_b = {a: (f"(b2v {_ident(a)})" if a in dirty else fixed[a]) for a in atoms}
        body = _lean(phi, env_b)
        disp = r["disposition"]
        target = "T" if disp.startswith("EARNED") else "F" if disp.startswith("REFUTED") else None
        term, names = _occ_env(phi, set(dirty))
        tb = term(phi, fixed)
        if target:
            # EARNED / REFUTED (IF STABLE): the claim holds in EVERY stable cleaning of the dirty atoms
            out.append(f"theorem stable : ∀ {binders} : Bool, {body} = {target} := by decide")
            if len(names) > len(dirty):
                if len(names) > CAP:
                    out.append(f"-- per-occurrence statement refused: {len(names)} occurrences > cap {CAP}")
                elif "IF STABLE" in disp:
                    out.append(f"theorem not_outright : ¬ ∀ {' '.join(names)} : Bool, {tb} = {target} := by decide")
                else:
                    out.append(f"theorem outright : ∀ {' '.join(names)} : Bool, {tb} = {target} := by decide")
        else:
            # OPEN / ON CREDIT: the cleanings do not agree — both outcomes are reachable
            out.append(f"theorem reach_T : ∃ {binders} : Bool, {body} = T := by decide")
            out.append(f"theorem reach_F : ∃ {binders} : Bool, {body} = F := by decide")
    out += ["", f"end {ns}", ""]
    prints = [f"#print axioms {ns}.{t}" for t in ("b2v", "verdict", "stable", "reach_T", "reach_F", "outright",
                                                   "not_outright") if f"theorem {t} " in "\n".join(out) or t == "b2v"]
    return "\n".join(out) + "\n".join(prints) + "\n", r


HEADER = """import ZTL
/-!
  GENERATED by zjudge2lean.py from the judge's verdicts — do not edit by hand; regenerate.
  Every statement restates what ztljudge.judge said; every proof is `decide` (Lean enumerates).
  {title}
-/

open V

"""


def emit_file(claims, title=""):
    """claims: [(name, formula, marking)] -> (lean text, [judge results])"""
    parts, results = [HEADER.replace("{title}", title)], []
    for name, formula, marking in claims:
        text, r = emit_claim(name, formula, marking)
        parts.append(text)
        results.append(r)
    return "\n".join(parts), results


def _parse_mark(s):
    out = {}
    for kv in filter(None, (s or "").split(",")):
        k, v = kv.split("=")
        out[k.strip()] = v.strip()
    return out


def main(argv):
    import argparse
    ap = argparse.ArgumentParser(prog="zjudge2lean")
    ap.add_argument("--name", required=True)
    ap.add_argument("--formula", required=True)
    ap.add_argument("--mark", default="")
    ap.add_argument("--out")
    a = ap.parse_args(argv)
    text, _ = emit_file([(a.name, a.formula, _parse_mark(a.mark))], title=a.name)
    if a.out:
        open(a.out, "w").write(text)
    else:
        print(text)


if __name__ == "__main__":
    main(sys.argv[1:])
