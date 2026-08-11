# -*- coding: utf-8 -*-
"""
znumjudge — the claims-sheet judge: numeric atoms inside core formulas.

Stage 4 of the ZNUM plan (E37). The instrument reads a claims sheet, lets
comparisons over quantities stand INSIDE propositional formulas, supplies
their T/F/Z verdicts from the numeric floor (znum), and has the UNCHANGED
core (ztljudge) judge the formula. Diagnostics merge both floors:

  disposition   EARNED / ON CREDIT / OPEN / REFUTED — core disposition,
                then capped by the numeric provenance axis: NO forced
                verdict rises above ON CREDIT while it rides unearned
                LOAD-BEARING bounds — in either direction, since if truth
                is not taken on credit neither is falsity (a bare number
                is credit, F2). The direction is kept in `polarity`
                ("toward T" / "toward F"), not in a fifth word;
  next_check    one merged list, each entry naming a cure that can
                actually cure (a quantity merely PRESENT in the pedigree
                is no carrier — the probe is widening it to full ignorance
                and seeing whether the verdict survives):
                  measure <quantity>   — interval too wide (numeric Z);
                  document <quantity>  — bounds unearned AND load-bearing;
                  contest type <q>:<t> — the LATTICE is what forces the
                                         verdict; a type is a formalization
                                         commitment, so no witness helps —
                                         the appeal is against the encoding;
                  verify <atom>        — propositional atom still a mark.

Sheet line format (extends ztljudge's ledger format):

    label :: formula :: quantities and marks

    formula     propositional over comparisons and plain atoms:
                sum(a,b) <= c & deadline_ok
                operators: & | ~ -> ^ =  (the core's own), comparisons:
                <= < >= > ==  over +, -, *, /, sum(...), numbers, quantities
                (a divisor whose interval spans 0 makes the atom Z, §25 echo)
    quantities  name=1000 earned:ref | name=[lo,hi] credit | name=? credit
                (=? means no bounds at all: (-inf, inf)); optional type
                token int | decimalK | fracM (multiples of 1/M: thirds,
                eighths — the lattice no decimal one can say) and an
                optional unit token. Numbers are read EXACTLY (0.1 is a
                tenth, 8/3 a third of eight): on floats the lattice
                tightening produced FALSE refutations of honest sums.
                Plain atoms keep ztljudge marks: atom=T / atom=F

Run:  python3 znumjudge.py     (the riding sheet: our own live claims)
"""
import math
import os
import re
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)

from ztljudge import judge                                  # noqa: E402
from znum import (EARNED, CREDIT, INF, qty, compare, num,   # noqa: E402
                  typename, bounds_bearing, type_bearing)


# ------------------------------------------------------------ sheet parsing
_VAL = r"-?\d+(?:\.\d+)?(?:/\d+)?"      # 5, 0.75, 8/3 — read exactly
_QTY = re.compile(
    rf"^(?P<name>\w+)=(?:\[(?P<lo>{_VAL}|-inf),(?P<hi>{_VAL}|inf)\]"
    rf"|(?P<point>{_VAL})|(?P<unk>\?))$")
_CMP = re.compile(r"(<=|>=|==|<|>)")


def _num(s):
    """Sheet numbers are EXACT: '0.10' is a tenth, '8/3' is a third of
    eight — never the binary float that happens to be nearby."""
    if s == "-inf":
        return -INF
    if s == "inf":
        return INF
    return num(s)


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
                elif re.match(r"^frac\d+$", tok):
                    discrete = ("frac", int(tok[4:]))
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
    if re.match(rf"^{_VAL}$", s):
        return _num(s)
    if s in quantities:
        return s
    raise ValueError(f"unknown quantity or malformed arithmetic: {s!r}")


_KINDMAP = {"<=": ("le", False), "<": ("lt", False), "==": ("eq", False),
            ">=": ("le", True), ">": ("lt", True)}


def _trim_parens(s, lo, hi):
    """Shrink [lo, hi) until it is a comparison and nothing but one: give
    back a ')' whose '(' lies outside, a '(' whose ')' lies outside, and
    a matched pair that merely WRAPS the comparison (the core keeps those
    parentheses and reads ' nc1 ' in their place)."""
    while lo < hi:
        chunk = s[lo:hi]
        if chunk[0].isspace():
            lo += 1
            continue
        if chunk[-1].isspace():
            hi -= 1
            continue
        bal, low = 0, 0
        for c in chunk:
            bal += (c == "(") - (c == ")")
            low = min(low, bal)
        if low < 0:                       # ')' with its opener outside
            hi = s.rindex(")", lo, hi)
            continue
        if bal > 0:                       # '(' with its closer outside
            lo = s.index("(", lo, hi) + 1
            continue
        if chunk[0] == "(" and chunk[-1] == ")":
            inner, wraps = 0, True        # do the two actually match?
            for k, c in enumerate(chunk[:-1]):
                inner += (c == "(") - (c == ")")
                if inner == 0 and k:
                    wraps = False
                    break
            if wraps:
                lo, hi = lo + 1, hi - 1
                continue
        break
    return lo, hi


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
        # the chunk may have swallowed parentheses that belong to the
        # FORMULA, not to the comparison — '~(a == b)', '(x > 10) ^ ok'
        # were unparseable until this trim (found 2026-08-11 by riding
        # invented claims against predicted verdicts)
        lo, hi = _trim_parens(out, m.start(), m.end())
        chunk = out[lo:hi].strip()
        sign = _CMP.search(chunk).group(0)
        left, right = chunk.split(sign, 1)
        kind, swap = _KINDMAP[sign]
        e1, e2 = _parse_arith(left, quantities), _parse_arith(right, quantities)
        if swap:
            e1, e2 = e2, e1
        i += 1
        name = f"nc{i}"
        atoms[name] = (kind, e1, e2, chunk)
        out = out[:lo] + f" {name} " + out[hi:]


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

    # provenance cap (F2/F3): NO forced verdict rises above ON CREDIT while
    # it rides unearned bounds — in EITHER direction. If truth is not taken
    # on credit, neither is falsity: a refutation bought with borrowed
    # bounds is a refutation on credit. The direction is not lost, it moves
    # to `polarity`; the disposition vocabulary stays the four words.
    # Only LOAD-BEARING credit caps (probe = widening, see znum): a
    # quantity that merely appears in the pedigree buys nothing.
    credit_quantities = sorted({q for n in bearing
                                for q in numeric[n]["pedigree"]})
    bearing_credit = sorted({q for n in bearing
                             for q in numeric[n]["pedigree"]
                             if bounds_bearing(*natoms[n][:3], quantities, q)})
    disposition, polarity = core["disposition"], None
    if disposition in ("EARNED", "REFUTED") and bearing_credit:
        polarity = "toward T" if disposition == "EARNED" else "toward F"
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
                # the witness falls due the moment the measurement lands:
                # a Z atom can show nothing non-bearing yet (re-marking it Z
                # is a no-op, so it never enters `bearing`), and surprising
                # the reader with 'document' AFTER the measure is worse than
                # naming the second-order cure now
                for q in numeric[n]["pedigree"]:
                    next_check.append(f"document {q}")
        for a in core["unverified"]:
            if a not in natoms:
                next_check.append(f"verify {a}")
    # a cure must be able to cure: a credit quantity earns a 'document'
    # line only where the verdict RIDES on its bounds (probe = widening it
    # to full ignorance, type kept), and where the LATTICE is what forces
    # the verdict the open appeal is a different one — contest the type,
    # since a type is a formalization commitment and no witness touches it
    for n in bearing:
        kind, e1, e2, _ = natoms[n]
        # (an atom that is already Z never enters `bearing` — re-marking it
        # Z is a no-op — so every atom here is forced and the probe applies)
        for q in numeric[n]["pedigree"]:
            if bounds_bearing(kind, e1, e2, quantities, q):
                next_check.append(f"document {q}")
        if numeric[n]["verdict"] in ("T", "F"):
            for q in numeric[n]["used"]:
                if type_bearing(kind, e1, e2, quantities, q):
                    next_check.append(
                        f"contest type {q}:"
                        f"{typename(quantities[q]['discrete'])}")

    return {"formula": formula, "core_formula": core_formula.strip(),
            "numeric_atoms": numeric, "core": core,
            "disposition": disposition, "polarity": polarity,
            "credit_quantities": credit_quantities,
            "bearing_credit": bearing_credit,
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
    ("kopecks",                                # exactness: an honest sum
     "line1 + line2 == total",                 # floats refuted this one
     "line1=29.7 decimal1 earned:inv-1, line2=0.3 decimal1 earned:inv-2, "
     "total=30 earned:order-44"),
    ("shared_whole",                           # 8 slices, 3 eaters, no knife
     "share == slices / eaters",
     "share=? int, slices=8 earned:cheque-771, eaters=3 earned:cheque-771"),
    ("negated_rate",                           # a comparison under '~'
     "~(detected == attempted)",               # (parenthesised: unparseable
     "detected=50 earned:eh3-scored-40712058, attempted=70 credit"),  # till
    ("parens_xor",                             #  2026-08-11)
     "(x > 10) ^ ok",
     "x=[20,30] earned:meter-3, ok=F"),
    ("nested_parens",
     "((line1 + 1) <= budget) & booked",
     "line1=1000 earned:inv-17, budget=5000 earned:order-o4, booked=T"),
    ("shared_thirds",                          # the same words, knife allowed
     "share == slices / eaters",
     "share=? frac3, slices=8 earned:cheque-771, eaters=3 earned:cheque-771"),
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
              + (f" ({r['polarity']})" if r["polarity"] else "")
              + (f"   next: {r['next_check']}" if r["next_check"] else ""))

    by = {r["label"]: r for r in rows}
    # the honest 6/6-measured rate is EARNED outright
    assert by["phase_a_rate"]["disposition"] == "EARNED"
    # the padded 8-class rate is REFUTED: 50 == 70 is forced false — and
    # the falsity itself rides the CREDIT denominator, so the refutation
    # is on credit too; either way, never EARNED
    # falsity is not taken on credit either: the padded rate is refuted by
    # a denominator nobody witnessed, so it is capped, with its direction kept
    assert by["phase_a_rate_padded"]["disposition"] == "ON CREDIT"
    assert by["phase_a_rate_padded"]["polarity"] == "toward F"
    assert by["phase_a_rate_padded"]["credit_quantities"] == ["attempted"]
    # smeta: numeric side open (wide line3) AND a propositional atom rides
    assert by["smeta"]["disposition"] == "OPEN"
    assert by["smeta"]["next_check"] == ["measure line3", "document line3"]
    # eligibility: the UNRESOLVED_OWNER_FACT, mechanically
    assert by["eligibility_employees"]["disposition"] == "OPEN"
    assert by["eligibility_employees"]["next_check"] == ["measure employees",
                                                         "document employees"]
    # snapshot discipline: pinned figure EARNED; same words against the
    # current corpus REFUTED — the citation catch as a verdict
    assert by["snapshot_pin"]["disposition"] == "EARNED"
    assert by["snapshot_vs_current"]["disposition"] == "REFUTED"
    # exact rationals: 29.7 + 0.3 == 30 is EARNED (on floats it was REFUTED —
    # a false accusation against an honest invoice, MEASURED 2026-08-11)
    assert by["kopecks"]["disposition"] == "EARNED"
    # the lattice refutes, and says the appeal that is actually open: no
    # document about `share` can help, only contesting the encoding
    assert by["shared_whole"]["disposition"] == "REFUTED"
    assert by["shared_whole"]["next_check"] == ["contest type share:int"]
    # allow thirds and the same words stop being a refutation
    assert by["shared_thirds"]["disposition"] == "OPEN"
    assert by["shared_thirds"]["next_check"] == ["measure share",
                                                 "document share"]
    # a comparison wrapped in parentheses is still a comparison: the
    # formula's parens stay with the formula, the atom is read out of them
    assert by["negated_rate"]["disposition"] == "ON CREDIT"
    assert by["negated_rate"]["polarity"] == "toward T"   # ~F, on credit
    assert by["negated_rate"]["next_check"] == ["document attempted"]
    assert by["parens_xor"]["disposition"] == "EARNED"
    assert by["nested_parens"]["disposition"] == "EARNED"
    print()
    print("=" * 72)
    print("ZNUMJUDGE GREEN — mixed formulas judged by the unchanged core;")
    print("numeric atoms carry their two axes; the provenance cap holds")
    print("(no claim rises above ON CREDIT on unearned bounds); next_check")
    print("names the cure per quantity: measure / document / contest type /")
    print("verify — and only cures that can cure (carriers probed by widening).")
