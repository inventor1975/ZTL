#!/usr/bin/env python3
"""«Где зеркало трескается» — три места, где привычная симметрия у нас рвётся.
Значения и подсвеченные клетки ВЫЧИСЛЯЮТСЯ из ztl.py, не вписаны руками."""
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))
import ztl
T, F, Z = ztl.T, ztl.F, ztl.Z
V = [T, F, Z]; NM = {T: "T", F: "F", Z: "Z"}
NOT, AND, OR, IMP = ztl.NOT, ztl.OR, ztl.OR, ztl.IMP
AND = ztl.AND
FILL = {"T": "#cfe8c9", "F": "#f2ccc9", "Z": "#dde2ea"}
EDGE = {"T": "#4b7a43", "F": "#a6413b", "Z": "#7d8794"}
HL = "#e8a13a"; INK = "#1b1b1b"; CELL = 40

def cell(x, y, m, hot):
    r = [f'<rect x="{x}" y="{y}" width="{CELL}" height="{CELL}" rx="6" '
         f'fill="{FILL[m]}" stroke="{HL if hot else EDGE[m]}" '
         f'stroke-width="{4 if hot else 1.4}"/>',
         f'<text x="{x+CELL/2}" y="{y+CELL/2+1}" font-size="19" font-weight="600" '
         f'fill="{INK}" text-anchor="middle" dominant-baseline="central">{m}</text>']
    return "".join(r)

def grid(sx, sy, fn, hotset):
    out = []
    for j, b in enumerate(V):
        out.append(f'<text x="{sx+30+j*CELL+CELL/2}" y="{sy+CELL/2}" font-size="13" '
                   f'fill="#666" text-anchor="middle" dominant-baseline="central">{NM[b]}</text>')
    by = sy + CELL
    for i, a in enumerate(V):
        out.append(f'<text x="{sx+14}" y="{by+i*CELL+CELL/2}" font-size="13" fill="#666" '
                   f'text-anchor="middle" dominant-baseline="central">{NM[a]}</text>')
        for j, b in enumerate(V):
            hot = (NM[a], NM[b]) in hotset
            out.append(cell(sx+30+j*CELL, by+i*CELL, NM[fn(a, b)], hot))
    return "".join(out)

def diffs(f, g):
    return {(NM[a], NM[b]) for a in V for b in V if f(a, b) != g(a, b)}

def txt(x, y, t, s=14, c="#333", w="400", a="start"):
    return f'<text x="{x}" y="{y}" font-size="{s}" fill="{c}" font-weight="{w}" text-anchor="{a}">{t}</text>'

def panel(sy, title, lhs_lbl, lhs, rhs_lbl, rhs):
    hot = diffs(lhs, rhs)
    gx1, gx2 = 150, 470
    out = [txt(70, sy-18, title, 17, INK, "700"),
           txt(gx1+75, sy-2, lhs_lbl, 14, "#444", "600", "middle"),
           txt(gx2+75, sy-2, rhs_lbl, 14, "#444", "600", "middle"),
           grid(gx1, sy+6, lhs, hot), grid(gx2, sy+6, rhs, hot),
           txt(410, sy+6+2*CELL, "≠", 30, HL, "700", "middle"),
           txt(720, sy+6+CELL, f"{len(hot)}", 34, HL, "700", "middle"),
           txt(720, sy+6+2*CELL+6, "клетки" if len(hot) in (2,3,4) else "клеток",
               13, "#888", "400", "middle"),
           txt(720, sy+6+2*CELL+24, "мимо", 13, "#888", "400", "middle")]
    return "".join(out)

def main():
    W, H = 860, 1040
    p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
         f'font-family="Georgia,\'DejaVu Serif\',serif">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
         txt(W/2, 44, "Где зеркало трескается", 26, INK, "700", "middle"),
         txt(W/2, 70, "три привычные симметрии, которые у нас НЕ выполняются "
                      "(подсвечены клетки-исключения)", 14, "#666", "400", "middle")]
    p.append(panel(150, "1. Де Морган для «и»:  отрицание не переносится внутрь",
                   "¬(a ∧ b)", lambda a, b: NOT(AND(a, b)),
                   "¬a ∨ ¬b", lambda a, b: OR(NOT(a), NOT(b))))
    p.append(panel(420, "2. Де Морган для «или»:  и здесь тоже",
                   "¬(a ∨ b)", lambda a, b: NOT(OR(a, b)),
                   "¬a ∧ ¬b", lambda a, b: AND(NOT(a), NOT(b))))
    p.append(panel(690, "3. Контрапозиция:  «если a то b» ≠ «если не-b то не-a»",
                   "a → b", lambda a, b: IMP(a, b),
                   "¬b → ¬a", lambda a, b: IMP(NOT(b), NOT(a))))
    ly = 900
    p.append(f'<line x1="70" y1="{ly-16}" x2="{W-70}" y2="{ly-16}" stroke="#e3e3e3"/>')
    p.append(txt(70, ly+6, "Все три — следствие одной жертвы: ¬Z = F "
                           "(отрицание непроверенного — ложь, а не «непроверено»).", 14, "#444"))
    p.append(txt(70, ly+28, "Оттого «или» из «и» отражением через «не» не получить, "
                            "а контрапозиция — уже не тождество.", 14, "#444"))
    p.append(txt(70, ly+54, "А ОДНО зеркало держится:  a → b  =  ¬a ∨ b  — совпадает полностью, "
                            "ноль расхождений.", 14, "#2f6b34", "600"))
    p.append(txt(70, ly+76, "Считано из ztl.py; подсветка — ровно клетки, где стороны "
                            "разошлись.", 12, "#999"))
    p.append("</svg>")
    out = pathlib.Path(__file__).parent / "zerkalo.svg"
    out.write_text("".join(p), encoding="utf-8")
    print("написано:", out.name, len("".join(p)), "байт")

if __name__ == "__main__":
    main()
