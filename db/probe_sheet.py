# -*- coding: utf-8 -*-
"""
The measurement week, day seven: the graph nobody has to type.

Six days established the shape and the killer. The instrument catches system
errors rather than fraud, and both its catches rest on one condition: SOMEBODY
HAD TO WRITE THE CITATION DOWN. Citations are honoured, never discovered.
That is daily work in exchange for a benefit that arrives only when something
goes wrong, which is the shape of every ledger nobody fills in.

So the test is not a better store. It is whether the condition can be removed
by going where the dependency graph ALREADY EXISTS. A spreadsheet knows that
C5 = A1 + B3 by construction; nobody records it, nobody maintains it, and it
cannot rot, because it IS the document.

Everything below runs on the standard library alone. An .xlsx is a zip of XML
and its formulas are in plain sight, so the workbook is generated here and
read back here, and the stand needs nothing installed anywhere.

Run:  python3 db/probe_sheet.py
"""
import os
import re
import sys
import tempfile
import xml.etree.ElementTree as ET
import zipfile

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, _ROOT)

NS = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"

# A small contract ledger as anybody would actually build it: inputs typed in,
# everything above them a formula. The shape is day one's, so the two runs can
# be compared — three invoice lines, VAT, a total, what was paid, a margin.
CELLS = [
    ("A1", None, "line_a"), ("B1", "3000", None),
    ("A2", None, "line_b"), ("B2", "1500", None),
    ("A3", None, "line_c"), ("B3", "2000", None),
    ("A4", None, "petty"),  ("B4", "750", None),
    ("A6", None, "subtotal"), ("B6", "SUM(B1:B4)", None),
    ("A7", None, "vat_rate"), ("B7", "0.2", None),
    ("A8", None, "vat"),    ("B8", "B6*B7", None),
    ("A9", None, "total"),  ("B9", "B6+B8", None),
    ("A10", None, "paid"),  ("B10", "5000", None),
    ("A11", None, "margin"), ("B11", "B9-B10", None),
    ("A13", None, "over_ceiling"), ("B13", "B9-9000", None),
]
FORMULA_CELLS = {"B6", "B8", "B9", "B11", "B13"}


def build_workbook(path):
    """A minimum valid .xlsx, written by hand. Five little XML files — which
    is itself part of the finding: reaching a spreadsheet's dependency graph
    needs no library, no server and no permission."""
    def cell(ref, value, label):
        if label is not None:
            return (f'<c r="{ref}" t="inlineStr"><is><t>{label}</t></is></c>')
        if ref in FORMULA_CELLS:
            return f'<c r="{ref}"><f>{value}</f></c>'
        return f'<c r="{ref}"><v>{value}</v></c>'

    rows = {}
    for ref, value, label in CELLS:
        rows.setdefault(int(re.sub(r"[A-Z]", "", ref)), []).append(
            cell(ref, value, label))
    body = "".join(f'<row r="{r}">{"".join(cs)}</row>'
                   for r, cs in sorted(rows.items()))
    sheet = ('<?xml version="1.0"?><worksheet xmlns="http://schemas.'
             'openxmlformats.org/spreadsheetml/2006/main"><sheetData>'
             + body + "</sheetData></worksheet>")
    with zipfile.ZipFile(path, "w") as z:
        z.writestr("[Content_Types].xml",
                   '<?xml version="1.0"?><Types xmlns="http://schemas.'
                   'openxmlformats.org/package/2006/content-types">'
                   '<Default Extension="rels" ContentType="application/'
                   'vnd.openxmlformats-package.relationships+xml"/>'
                   '<Override PartName="/xl/workbook.xml" ContentType='
                   '"application/vnd.openxmlformats-officedocument.'
                   'spreadsheetml.sheet.main+xml"/><Override PartName='
                   '"/xl/worksheets/sheet1.xml" ContentType="application/'
                   'vnd.openxmlformats-officedocument.spreadsheetml.'
                   'worksheet+xml"/></Types>')
        z.writestr("_rels/.rels",
                   '<?xml version="1.0"?><Relationships xmlns="http://'
                   'schemas.openxmlformats.org/package/2006/relationships">'
                   '<Relationship Id="rId1" Type="http://schemas.'
                   'openxmlformats.org/officeDocument/2006/relationships/'
                   'officeDocument" Target="xl/workbook.xml"/></Relationships>')
        z.writestr("xl/workbook.xml",
                   '<?xml version="1.0"?><workbook xmlns="http://schemas.'
                   'openxmlformats.org/spreadsheetml/2006/main" xmlns:r='
                   '"http://schemas.openxmlformats.org/officeDocument/2006/'
                   'relationships"><sheets><sheet name="ledger" sheetId="1" '
                   'r:id="rId1"/></sheets></workbook>')
        z.writestr("xl/_rels/workbook.xml.rels",
                   '<?xml version="1.0"?><Relationships xmlns="http://'
                   'schemas.openxmlformats.org/package/2006/relationships">'
                   '<Relationship Id="rId1" Type="http://schemas.'
                   'openxmlformats.org/officeDocument/2006/relationships/'
                   'worksheet" Target="worksheets/sheet1.xml"/>'
                   '</Relationships>')
        z.writestr("xl/worksheets/sheet1.xml", sheet)


# ------------------------------------------------------- reading the graph
_REF = re.compile(r"\$?([A-Z]{1,3})\$?(\d+)(?::\$?([A-Z]{1,3})\$?(\d+))?")


def _col(letters):
    n = 0
    for ch in letters:
        n = n * 26 + ord(ch) - 64
    return n


def _name(col, row):
    s = ""
    while col:
        col, r = divmod(col - 1, 26)
        s = chr(65 + r) + s
    return f"{s}{row}"


def expand(ref_match):
    """A1 stays one cell; A1:B4 becomes the eight cells it covers. Ranges are
    where a spreadsheet's graph stops being trivial — SUM(B1:B4) depends on
    four things and names none of them."""
    c1, r1, c2, r2 = ref_match.groups()
    if c2 is None:
        return [f"{c1}{r1}"]
    a, b = _col(c1), _col(c2)
    return [_name(c, r) for c in range(min(a, b), max(a, b) + 1)
            for r in range(min(int(r1), int(r2)), max(int(r1), int(r2)) + 1)]


def read_graph(path):
    """Every formula cell and what it depends on — taken from the file, with
    nobody asked and nothing annotated."""
    with zipfile.ZipFile(path) as z:
        root = ET.fromstring(z.read("xl/worksheets/sheet1.xml"))
    deps, constants, labels = {}, {}, {}
    for c in root.iter(NS + "c"):
        ref = c.get("r")
        f = c.find(NS + "f")
        if f is not None and f.text:
            deps[ref] = sorted({r for m in _REF.finditer(f.text)
                                for r in expand(m)})
            continue
        istr = c.find(NS + "is/" + NS + "t")
        v = c.find(NS + "v")
        if istr is not None:
            labels[ref] = istr.text
        elif v is not None:
            constants[ref] = v.text
    return deps, constants, labels


def fallout(deps, start):
    """What stops standing when `start` is withdrawn — the ledger's cascade,
    over a graph nobody wrote."""
    hit, frontier = set(), {start}
    while frontier:
        nxt = set()
        for cell, srcs in deps.items():
            if cell not in hit and frontier & set(srcs):
                hit.add(cell)
                nxt.add(cell)
        frontier = nxt
    return sorted(hit)


def main():
    print("=" * 78)
    print("THE GRAPH NOBODY HAS TO TYPE")
    print("=" * 78)
    tmp = tempfile.NamedTemporaryFile(suffix=".xlsx", delete=False)
    tmp.close()
    build_workbook(tmp.name)
    deps, constants, labels = read_graph(tmp.name)

    print(f"\n  the workbook, read back with zipfile and ElementTree only")
    print(f"    formula cells   {len(deps)}")
    print(f"    constant cells  {len(constants)}")
    print(f"    label cells     {len(labels)}")
    for cell in sorted(deps, key=lambda r: (len(r), r)):
        print(f"      {labels.get(_name(1, int(cell[1:])), '?'):12} "
              f"{cell} <- {', '.join(deps[cell])}")
    assert len(deps) == 5 and "B6" in deps and deps["B6"] == \
        ["B1", "B2", "B3", "B4"]

    print("\n  1. THE CASCADE, over a graph NOBODY WROTE DOWN")
    for bad in ("B2", "B7", "B10"):
        hit = fallout(deps, bad)
        who = labels.get(_name(1, int(bad[1:])), bad)
        print(f"      {who:9} ({bad}) turns out wrong  ->  "
              f"{', '.join(labels.get(_name(1, int(h[1:])), h) for h in hit)}")
    assert fallout(deps, "B2") == ["B11", "B13", "B6", "B8", "B9"]
    print("     One typo in a petty invoice line moves the subtotal, the VAT,")
    print("     the total, the margin and the ceiling test. Day one needed a")
    print("     human to write `earned:claim/dataset` for every one of those")
    print("     links. Here the count of links anybody typed is ZERO.")

    print("\n  2. WHAT THE HUMAN STILL OWES — measured, because this is the")
    print("     whole question")
    leaves = [c for c in constants]
    print(f"       cells in the sheet that carry a number   "
          f"{len(constants) + len(deps)}")
    print(f"       of those, derived by formula             {len(deps)}")
    print(f"       of those, typed in by a person           {len(leaves)}")
    share = 100 * len(leaves) // (len(constants) + len(deps))
    print(f"       so a ground is needed for                {share}% of them")
    print("     The graph is free; the GROUNDS are not. A spreadsheet knows")
    print("     that the total is the subtotal plus VAT. It has no idea that")
    print("     B1 came from invoice 17. But the annotation is owed only on")
    print("     the LEAVES — every derived figure inherits, computed. In a")
    print("     real model, where formulas outnumber inputs many times over,")
    print("     that share falls further; here the sheet is small and the")
    print("     honest number is the one printed above, not a hoped-for one.")

    print("\n  3. WHAT THIS DOES NOT REACH — named, not skipped")
    print("       * ranges are expanded here, but a formula naming another")
    print("         SHEET or another FILE is not followed;")
    print("       * a value pasted in from elsewhere looks exactly like a")
    print("         typed constant — the London Whale's copy-paste is")
    print("         invisible in the file, as it was in the model;")
    print("       * a wrong formula is a formula. SUM where AVERAGE was")
    print("         meant reads as an honest dependency and always will.")

    os.unlink(tmp.name)
    print("\n  THE RESULT, plainly: the killer condition is HALF removed, and")
    print("  the half that goes is the expensive one. Nobody maintains a")
    print("  dependency graph by hand; people do put a note against a number")
    print("  they typed. And the graph cannot rot, because it is not a")
    print("  description of the document — it IS the document.")
    print("\nSHEET PROBE GREEN — the cascade ran on a graph nobody wrote.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
