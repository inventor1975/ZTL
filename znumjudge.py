# -*- coding: utf-8 -*-
"""
znumjudge — the claims-sheet judge: numeric atoms inside core formulas.

Stage 4 of the ZNUM plan (E37). The instrument reads a claims sheet, lets
comparisons over quantities stand INSIDE propositional formulas, supplies
their T/F/Z verdicts from the numeric floor (znum), and has the UNCHANGED
core (ztljudge) judge the formula. Diagnostics merge both floors:

  disposition   EARNED / ON CREDIT / OPEN / REFUTED — core disposition,
                then capped by the numeric provenance axis: a claim that
                rides a forced-but-unearned comparison cannot rise above
                ON CREDIT (a bare number is credit, F2);
  next_check    one merged list, each entry naming its cure:
                  measure <quantity>   — interval too wide (numeric Z);
                  document <quantity>  — bounds unearned (credit);
                  verify <atom>        — propositional atom still a mark.

Sheet line format (extends ztljudge's ledger format):

    label :: formula :: quantities and marks

    formula     propositional over comparisons and plain atoms:
                sum(a,b) <= c & deadline_ok
                operators: & | ~ -> ^ =  (the core's own), comparisons:
                <= < >= > ==  over +, -, *, /, sum(...), numbers, quantities
                (a divisor whose interval spans 0 makes the atom Z, §25 echo)
    quantities  name=1000 earned:ref | name=[lo,hi] credit | name=? credit
                (=? means no bounds at all: (-inf, inf));
                plain atoms keep ztljudge marks: atom=T / atom=F

Run:  python3 znumjudge.py     (the riding sheet: our own live claims)
"""
import math
import os
import re
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztljudge import judge                                  # noqa: E402
from znum import EARNED, CREDIT, INF, qty, compare          # noqa: E402


# ------------------------------------------------------------ sheet parsing
_QTY = re.compile(
    r"^(?P<name>\w+)=(?:\[(?P<lo>-?[\d.]+|-inf),(?P<hi>[\d.]+|inf)\]"
    r"|(?P<point>-?[\d.]+)|(?P<unk>\?))$")
_CMP = re.compile(r"(<=|>=|==|<|>)")


def _num(s):
    if s in ("-inf",):
        return -INF
    if s in ("inf",):
        return INF
    return float(s) if "." in s else int(s)


def parse_quantities(text):
    """'a=1000 earned:inv-1, b=[1,5] credit, c=? credit, ok=T' →
    (quantities, propositional marks)."""
    quantities, marks = {}, {}
    parts, depth, cur = [], 0, ""
    for c in text:                       # split on commas outside brackets
        if c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        if c == "," and depth == 0:
            parts.append(cur); cur = ""
        else:
            cur += c
    parts.append(cur)
    for part in filter(None, (p.strip() for p in parts)):
        m = _QTY.match(part.split()[0]) if part.split() else None
        if m and (m.group("lo") or m.group("point") or m.group("unk")):
            if m.group("unk"):
                lo, hi = -INF, INF
            elif m.group("point") is not None:
                lo = hi = _num(m.group("point"))
            else:
                lo, hi = _num(m.group("lo")), _num(m.group("hi"))
            # trailing tokens: discreteness | provenance | unit (free order)
            prov, wit, discrete, unit = CREDIT, None, None, None
            for tok in part.split()[1:]:
                if tok == "int":
                    discrete = "int"
                elif re.match(r"^decimal\d+$", tok):
                    discrete = ("decimal", int(tok[7:]))
                elif tok.startswith("earned"):
                    prov = EARNED
                    _, _, w = tok.partition(":")
                    wit = w or None
                elif tok == "credit":
                    prov = CREDIT
                else:
                    unit = tok
            quantities[m.group("name")] = qty(lo, hi, prov, wit,
                                              discrete=discrete, unit=unit)
        else:
            name, _, val = part.partition("=")
            if val.strip().upper() in ("T", "F", "Z"):
                marks[name.strip()] = val.strip().upper()
            else:
                raise ValueError(f"cannot parse sheet entry: {part!r}")
    return quantities, marks


def _parse_arith(s, quantities):
    """A tiny arithmetic reader for one comparison side: numbers,
    quantities, + - *, and sum(...). Returns a znum expression."""
    s = s.strip()
    m = re.match(r"^sum\((?P<args>[^)]*)\)$", s)
    if m:
        return ("sum", [_parse_arith(a, quantities)
                        for a in m.group("args").split(",")])
    _TAG = {"+": "add", "-": "sub", "*": "mul", "/": "div"}
    for level in (("+",), ("-",), ("*", "/")):   # * and / share one tier
        depth = 0
        for i in range(len(s) - 1, 0, -1):      # rightmost, outside parens
            c = s[i]
            if c == ")":
                depth += 1
            elif c == "(":
                depth -= 1
            elif c in level and depth == 0:
                return (_TAG[c], _parse_arith(s[:i], quantities),
                        _parse_arith(s[i + 1:], quantities))
    if s.startswith("(") and s.endswith(")"):
        return _parse_arith(s[1:-1], quantities)
    if re.match(r"^-?[\d.]+$", s):
        return _num(s)
    if s in quantities:
        return s
    raise ValueError(f"unknown quantity or malformed arithmetic: {s!r}")


_KINDMAP = {"<=": ("le", False), "<": ("lt", False), "==": ("eq", False),
            ">=": ("le", True), ">": ("lt", True)}


def extract_comparisons(formula, quantities):
    """Replace each comparison in the formula with a fresh atom nc<i>;
    return (core_formula, {atom: (kind, e1, e2)})."""
    # the implication arrow contains '>', which is NOT a comparison:
    # normalize '->' to the core's unicode arrow before extraction
    # (bug found by the curator's question "if 4 > 3 then 5 > 3?")
    atoms, out, i = {}, formula.replace("->", "→"), 0
    # a comparison = maximal operator-free chunk containing a _CMP sign
    pattern = re.compile(r"[\w.+\-*/\s(),]+?(?:<=|>=|==|<|>)[\w.+\-*/\s(),]+")
    while True:
        m = pattern.search(out)
        if not m:
            return out, atoms
        chunk = m.group(0).strip()
        sign = _CMP.search(chunk).group(0)
        left, right = chunk.split(sign, 1)
        kind, swap = _KINDMAP[sign]
        e1, e2 = _parse_arith(left, quantities), _parse_arith(right, quantities)
        if swap:
            e1, e2 = e2, e1
        i += 1
        name = f"nc{i}"
        atoms[name] = (kind, e1, e2, chunk)
        out = out[:m.start()] + f" {name} " + out[m.end():]


# ----------------------------------------------------------------- judging
def judge_sheet_claim(formula, quantities, marks):
    """Judge one mixed claim. Numeric floor supplies comparison atoms;
    the unchanged core judges the formula; the provenance axis caps the
    disposition; next_check merges the cures of both floors."""
    core_formula, natoms = extract_comparisons(formula, quantities)
    marking, numeric = dict(marks), {}
    for name, (kind, e1, e2, chunk) in natoms.items():
        v, ped, used = compare(kind, e1, e2, quantities)
        marking[name] = v
        numeric[name] = {"comparison": chunk, "verdict": v,
                         "pedigree": sorted(ped), "used": sorted(used)}
    core = judge(core_formula, marking)

    # which comparison atoms are load-bearing for the core disposition?
    bearing = []
    for name in natoms:
        d = dict(marking); d[name] = "Z"
        if judge(core_formula, d)["disposition"] != core["disposition"]:
            bearing.append(name)

    # provenance cap (F2/F3): EARNED that rides an unearned forced
    # comparison is only ON CREDIT; the pedigree names the culprits
    credit_quantities = sorted({q for n in bearing
                                for q in numeric[n]["pedigree"]})
    disposition = core["disposition"]
    if disposition == "EARNED" and credit_quantities:
        disposition = "ON CREDIT"

    next_check = []
    # §21 discipline: once the verdict is hereditary, remaining checks buy
    # nothing — measure/verify cures are offered only while the claim is
    # still open or riding credit; document cures always accompany credit
    if disposition in ("OPEN", "ON CREDIT"):
        for n in natoms:
            if numeric[n]["verdict"] == "Z" and n in core["unverified"]:
                for q in numeric[n]["used"]:
                    if quantities[q]["lo"] != quantities[q]["hi"]:
                        next_check.append(f"measure {q}")
        for a in core["unverified"]:
            if a not in natoms:
                next_check.append(f"verify {a}")
    for q in credit_quantities:
        next_check.append(f"document {q}")

    return {"formula": formula, "core_formula": core_formula.strip(),
            "numeric_atoms": numeric, "core": core,
            "disposition": disposition,
            "credit_quantities": credit_quantities,
            "next_check": sorted(set(next_check), key=next_check.index)}


def load_sheet(path):
    """label :: formula :: quantities-and-marks  (one claim per line;
    '#' comments; separator '::' as in ztljudge)."""
    claims = []
    for raw in open(path, encoding="utf-8"):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        parts = [p.strip() for p in line.split("::")]
        if len(parts) != 3:
            raise ValueError(f"claim needs 'label :: formula :: data': {raw!r}")
        claims.append((parts[0], parts[1], parts[2]))
    return claims


def judge_sheet(claims):
    rows = []
    for label, formula, data in claims:
        quantities, marks = parse_quantities(data)
        r = judge_sheet_claim(formula, quantities, marks)
        r["label"] = label
        rows.append(r)
    return rows


# ================================================================ the ride
SHEET = [
    # our own live claims, as they stood on 2026-08-10
    ("phase_a_rate",
     "detected == attempted",
     "detected=50 earned:eh3-scored-40712058, attempted=50 earned:sealed-manifest-32b85214"),
    ("phase_a_rate_padded",                    # the dishonest cousin: 8-class
     "detected == attempted",                  # denominator never measured
     "detected=50 earned:eh3-scored-40712058, attempted=70 credit"),
    ("smeta",
     "sum(line1,line2,line3) <= budget & invoices_booked",
     "line1=1000 earned:inv-17, line2=2000 earned:inv-18, "
     "line3=[500,3000] credit, budget=5000 earned:order-o4, invoices_booked=T"),
    ("eligibility_employees",
     "employees < 75",
     "employees=? credit"),
    ("snapshot_pin",                           # the snapshot-citation catch
     "theorems == 371",
     "theorems=371 earned:tag-downstream-v0.2-56e1ff0"),
    ("snapshot_vs_current",                    # same words, current corpus
     "theorems == 371",
     "theorems=405 earned:axiom-audit-2026-08-10"),
]


if __name__ == "__main__":
    print("=" * 72)
    print("ZNUMJUDGE — the claims sheet, ridden on our own live claims")
    print("=" * 72)
    rows = judge_sheet(SHEET)
    for r in rows:
        print(f"\n  [{r['label']}]  {r['formula']}")
        for n, info in r["numeric_atoms"].items():
            ped = f"  credit:{info['pedigree']}" if info["pedigree"] else ""
            print(f"      {n}: {info['comparison']}  ->  {info['verdict']}{ped}")
        print(f"      -> {r['disposition']}"
              + (f"   next: {r['next_check']}" if r["next_check"] else ""))

    by = {r["label"]: r for r in rows}
    # the honest 6/6-measured rate is EARNED outright
    assert by["phase_a_rate"]["disposition"] == "EARNED"
    # the padded 8-class rate is REFUTED: 50 == 70 is forced false — and
    # the falsity itself rides the CREDIT denominator, so the refutation
    # is on credit too; either way, never EARNED
    assert by["phase_a_rate_padded"]["disposition"] in ("REFUTED", "ON CREDIT")
    assert by["phase_a_rate_padded"]["credit_quantities"] == ["attempted"]
    # smeta: numeric side open (wide line3) AND a propositional atom rides
    assert by["smeta"]["disposition"] == "OPEN"
    assert "measure line3" in by["smeta"]["next_check"]
    # eligibility: the UNRESOLVED_OWNER_FACT, mechanically
    assert by["eligibility_employees"]["disposition"] == "OPEN"
    assert by["eligibility_employees"]["next_check"] == ["measure employees"]
    # snapshot discipline: pinned figure EARNED; same words against the
    # current corpus REFUTED — the citation catch as a verdict
    assert by["snapshot_pin"]["disposition"] == "EARNED"
    assert by["snapshot_vs_current"]["disposition"] == "REFUTED"
    print()
    print("=" * 72)
    print("ZNUMJUDGE GREEN — mixed formulas judged by the unchanged core;")
    print("numeric atoms carry their two axes; the provenance cap holds")
    print("(no claim rises above ON CREDIT on unearned bounds); next_check")
    print("names the cure per quantity: measure / document / verify.")
