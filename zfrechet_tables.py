# -*- coding: utf-8 -*-
"""
zfrechet_tables — ZTL-I against the PUBLISHED tables of ZTL, cell by cell (2026-11-05, the curator: "у нас таблицы ЗТЛ
очень не однородные и не интуитивные, ты точно все проверил на генерацию. Проверь все 16 плюс операнд").

zfrechet.py section 1 compared the interval projection with tables it LIFTED ITSELF — circular for any table that is
not a plain lift. Here the yardstick is what ZTL publishes, read from three independent places:
  SITE   ztljudge-site/docs/ztl/tables.md — the 4 one-argument tables, the 16 two-argument tables, and the four
         COMPOSED tables ¬(a∧b), ¬(a∨b), ¬(a⊕b), ¬(a→b) set against the one-connective ↑ ↓ ↔ ↛;
  FILE   the curator's ~/Dropbox/Epic World/ZTL/ZTL-ALL-TABLES-16plus2.txt — 2 one-argument + 16 two-argument;
  CODE   ztl.py's NOT/AND/OR/IMP/XOR/XNOR.
The classical kernel of each table is read off its own T/F cells; ZTL-I gives every cell an interval (T = [1,1],
F = [0,0], Z = [0,1], every joint of the two arguments allowed); the projection "T iff lo = 1" must equal the
published cell. A composed table is a formula of two connectives: ZTL reads it node by node (each connective answers
T or F), so ZTL-I must project at EACH node — and must then reproduce exactly the cells where ¬(a∧b) differs from ↑.
"""
import os
import re
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ztl                                                     # noqa: E402

SITE = "/media/vitaly/SSD_1000GB/Projects/ztljudge-site/docs/ztl/tables.md"
FILE = os.path.expanduser("~/Dropbox/Epic World/ZTL/ZTL-ALL-TABLES-16plus2.txt")
V = ("T", "F", "Z")
DEG = {"T": (Fr(1), Fr(1)), "F": (Fr(0), Fr(0)), "Z": (Fr(0), Fr(1))}


def iv1(f, a):
    """[lo, hi] of P(f(A)) for P(A) in the interval a"""
    vals = [p * f(1) + (1 - p) * f(0) for p in a]
    return (min(vals), max(vals))


def iv2(f, a, b):
    vals = []
    for pa in a:
        for pb in b:
            for p11 in (max(Fr(0), pa + pb - 1), min(pa, pb)):
                p10, p01 = pa - p11, pb - p11
                vals.append(p11 * f(1, 1) + p10 * f(1, 0) + p01 * f(0, 1) + (1 - p11 - p10 - p01) * f(0, 0))
    return (min(vals), max(vals))


def proj(iv):
    return "T" if iv[0] == 1 else "F"


def parse_site():
    text = open(SITE, encoding="utf-8").read()
    out = {}
    for block in re.split(r"(?m)^### ", text)[1:]:
        title = block.split("\n", 1)[0].strip()
        rows = re.findall(r"(?m)^\| \*\*([TFZ])\*\* \|(.*)\|\s*$", block)
        if not rows:
            continue
        cells = {r: [c.strip() for c in rest.split("|")] for r, rest in rows}
        if all(len(v) == 1 for v in cells.values()):
            out[title] = {x: cells[x][0] for x in V}
        else:
            out[title] = {(x, y): cells[x][j] for x in V for j, y in enumerate(V)}
    return out


def parse_file():
    text = open(FILE, encoding="utf-8").read()
    out = {}
    for m in re.finditer(r"(?ms)^(U\d|B\d+)\)\s*(.*?)\n-+\n(.*?)(?=\n-{10,}|\n#### |\Z)", text):
        tag, body = m.group(1), m.group(3)
        if tag.startswith("U"):
            rows = dict(re.findall(r"(?m)^\s*([TFZ])\s*\|\s*([TFZ])\s*$", body))
            out[tag] = {x: rows[x] for x in V}
        else:
            rows = re.findall(r"(?m)^\s*([TFZ])\s*\|\s*([TFZ])\s+([TFZ])\s+([TFZ])\s*$", body)
            out[tag] = {(r[0], y): r[1 + j] for r in rows for j, y in enumerate(V)}
    return out


def stated_kernels():
    """the kernel each two-argument table of the file STATES in words: [ядро TFFF] = values on (TT, TF, FT, FF)"""
    text = open(FILE, encoding="utf-8").read()
    return {m.group(1): m.group(2) for m in re.finditer(r"(?m)^(B\d+)\).*?\[ядро ([TF]{4});", text)}


def table_kernel(t):
    return "".join(t[(x, y)] for x, y in (("T", "T"), ("T", "F"), ("F", "T"), ("F", "F")))


def same_table_in_file(name, file_):
    """the file's table for the SAME connective as a site table: '7. a ↑ b …' -> B7; id -> U1, ¬ -> U2; the two
    constant one-argument tables are not in the file — their definition is the yardstick"""
    m = re.match(r"(\d+)\.", name)
    if m:
        return file_[f"B{m.group(1)}"]
    return {"id x — identity (assertion)": file_.get("U1"), "¬x — NOT (negation)": file_.get("U2"),
            "⊤x — always T": {x: "T" for x in V}, "⊥x — always F": {x: "F" for x in V}}[name]


def kernel1(t):
    return lambda p: 1 if t["T" if p else "F"] == "T" else 0


def kernel2(t):
    return lambda x, y: 1 if t[("T" if x else "F", "T" if y else "F")] == "T" else 0


def check_table(name, t):
    """every cell of a published table against ZTL-I's projection; -> (cells, differing cells)"""
    bad = []
    if isinstance(next(iter(t)), str):
        f = kernel1(t)
        for x in V:
            if proj(iv1(f, DEG[x])) != t[x]:
                bad.append(x)
        return 3, bad
    f = kernel2(t)
    for x in V:
        for y in V:
            if proj(iv2(f, DEG[x], DEG[y])) != t[(x, y)]:
                bad.append((x, y))
    return 9, bad


def main():
    if not (os.path.exists(SITE) and os.path.exists(FILE)):
        # the yardsticks live in the site's source and in the curator's file, not in this repository: elsewhere (CI)
        # this stand is SKIPPED — a skip, never a pass (run_all reports it apart)
        print("SKIPPED: the published tables are read from the site source and the curator's file — not on this "
              "machine")
        return
    site, file_ = parse_site(), parse_file()
    plain = {k: v for k, v in site.items() if "against" not in k}
    composed = {k: v for k, v in site.items() if "against" in k}
    assert len(plain) == 20 and len(composed) == 4, (len(plain), len(composed))
    assert len(file_) == 18, len(file_)
    print("-" * 72)
    print("1. THE SITE: 4 ONE-ARGUMENT + 16 TWO-ARGUMENT TABLES, EVERY CELL")
    total = 0
    for name, t in plain.items():
        n, bad = check_table(name, t)
        total += n
        assert not bad, (name, bad)
    print(f"   {len(plain)} tables, {total} cells, 0 differ from ZTL-I's projection")
    print("-" * 72)
    print("2. THE CURATOR'S FILE: 2 ONE-ARGUMENT + 16 TWO-ARGUMENT TABLES, EVERY CELL")
    total = 0
    for tag, t in file_.items():
        n, bad = check_table(tag, t)
        total += n
        assert not bad, (tag, bad)
    print(f"   {len(file_)} tables, {total} cells, 0 differ")
    sk = stated_kernels()
    assert len(sk) == 16 and all(table_kernel(file_[b]) == sk[b] for b in sk), sk
    print("   each two-argument table's T/F cells are the kernel the file states in words (16 of 16)")
    # the file and the site carry the same 16 + the same id and NOT
    for name, t in plain.items():
        assert t == same_table_in_file(name, file_), name
    print("   and every site table equals the file's table of the SAME connective, cell by cell (20 of 20)")
    print("-" * 72)
    print("3. THE CODE: ztl.NOT, AND, OR, IMP, XOR, XNOR, CELL BY CELL")
    code = {"not": ztl.NOT, "and": ztl.AND, "or": ztl.OR, "imp": ztl.IMP, "xor": ztl.XOR, "xnor": ztl.XNOR}
    kern = {"and": lambda x, y: x & y, "or": lambda x, y: x | y, "imp": lambda x, y: (1 - x) | y,
            "xor": lambda x, y: x ^ y, "xnor": lambda x, y: 1 - (x ^ y)}
    for x in V:
        assert code["not"](x) == proj(iv1(lambda p: 1 - p, DEG[x]))
    for name, k in kern.items():
        for x in V:
            for y in V:
                assert code[name](x, y) == proj(iv2(k, DEG[x], DEG[y])), (name, x, y)
    print("   6 connectives, 3 + 45 cells: 0 differ")
    print("-" * 72)
    print("4. THE COMPOSED TABLES: ZTL-I PROJECTED AT EACH NODE")
    inner = {"¬(a ∧ b)": lambda x, y: x & y, "¬(a ∨ b)": lambda x, y: x | y,
             "¬(a ⊕ b)": lambda x, y: x ^ y, "¬(a → b)": lambda x, y: (1 - x) | y}
    for name, t in composed.items():
        key = name.split(" against")[0]
        f = inner[key]
        diffs_lift = []
        for x in V:
            for y in V:
                node = proj(iv2(f, DEG[x], DEG[y]))                       # the inner connective answers T or F
                outer = proj(iv1(lambda p: 1 - p, DEG[node]))             # then NOT reads that answer
                assert outer == t[(x, y)], (name, x, y, outer, t[(x, y)])
                one = {"¬(a ∧ b)": lambda a, b: 1 - (a & b), "¬(a ∨ b)": lambda a, b: 1 - (a | b),
                       "¬(a ⊕ b)": lambda a, b: 1 - (a ^ b), "¬(a → b)": lambda a, b: a & (1 - b)}[key]
                if proj(iv2(one, DEG[x], DEG[y])) != outer:
                    diffs_lift.append((x, y))
        print(f"   {key:9s} node by node = the site's table; differs from the one connective in {len(diffs_lift)} cell(s):"
              f" {diffs_lift}")
        # the site states the difference in words: "Differs from `a ↑ b` in 3 cell(s): (T, Z), (Z, T), (Z, Z)."
        said = re.search(rf"### {re.escape(name)}.*?Differs from `[^`]*` in (\d+) cell\(s\): ([^\n]*)\.",
                         open(SITE, encoding="utf-8").read(), re.S)
        assert said and int(said.group(1)) == len(diffs_lift), (name, said and said.group(1))
        assert said.group(2) == ", ".join(f"({x}, {y})" for x, y in diffs_lift), (name, said.group(2))
    print("-" * 72)
    print("5. SABOTAGE: ONE CELL FLIPPED IN ANY PUBLISHED TABLE IS CAUGHT")
    caught = 0
    for name, t in plain.items():
        for cell in t:
            flipped = dict(t)
            flipped[cell] = "F" if t[cell] == "T" else "T"
            # a flipped T/F cell changes the kernel itself, so test the Z cells (the ones ZTL decides) and the rest
            n, bad = check_table(name, flipped)
            if bad or flipped != same_table_in_file(name, file_):
                caught += 1
    total = sum(len(t) for t in plain.values())
    print(f"   {caught} of {total} single-cell flips caught")
    assert caught == total, (caught, total)
    print("-" * 72)
    print("ZFRECHET TABLES: every published table of ZTL is ZTL-I's projection, the composed ones node by node.")


if __name__ == "__main__":
    main()
