#!/usr/bin/env python3
"""Шесть таблиц ZTL одной картинкой. Значения БЕРУТСЯ ИЗ ztl.py — картинка
не может разойтись с кодом. Оси подписаны: a сверху вниз, b слева направо
(для «если» это важно, таблица несимметрична). Тело — только T и F:
третий знак живёт лишь по краям, во входах."""
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))
import ztl

NM = {ztl.T: "T", ztl.F: "F", ztl.Z: "Z"}
V = [ztl.T, ztl.F, ztl.Z]
FILL = {"T": "#cfe8c9", "F": "#f2ccc9", "Z": "#dde2ea"}
EDGE = {"T": "#4b7a43", "F": "#a6413b", "Z": "#7d8794"}
INK = "#1b1b1b"
CELL = 44

def C(x, y, m):
    return (f'<rect x="{x}" y="{y}" width="{CELL}" height="{CELL}" rx="6" '
            f'fill="{FILL[m]}" stroke="{EDGE[m]}" stroke-width="1.5"/>'
            f'<text x="{x+CELL/2}" y="{y+CELL/2+1}" font-size="21" font-weight="600" '
            f'fill="{INK}" text-anchor="middle" dominant-baseline="central">{m}</text>')

def lbl(x, y, t, size=13, col="#78808c", w="400", anch="middle"):
    return (f'<text x="{x}" y="{y}" font-size="{size}" fill="{col}" '
            f'font-weight="{w}" text-anchor="{anch}">{t}</text>')

def block_binary(sx, sy, sign, human, fn):
    bodyx = sx + 34
    out = [lbl(bodyx + CELL*1.5, sy+16, f"a {sign} b", 20, INK, "700"),
           lbl(bodyx + CELL*1.5, sy+34, human, 13, "#78808c")]
    # ось b сверху
    out.append(lbl(bodyx + CELL*1.5, sy+54, "b  (правый вход) →", 12, "#9aa1ac"))
    hy = sy + 62
    for j, b in enumerate(V):
        out.append(lbl(bodyx + j*CELL + CELL/2, hy+CELL/2, NM[b], 15, "#5b5b5b", "600", "middle"))
    body = hy + CELL + 4
    # ось a слева
    out.append(f'<text x="{sx+10}" y="{body+CELL*1.5}" font-size="12" fill="#9aa1ac" '
               f'text-anchor="middle" transform="rotate(-90 {sx+10} {body+CELL*1.5})">'
               f'a (левый вход) ↓</text>')
    for i, a in enumerate(V):
        yy = body + i*CELL
        out.append(lbl(sx+26, yy+CELL/2, NM[a], 15, "#5b5b5b", "600", "middle"))
        for j, b in enumerate(V):
            out.append(C(bodyx + j*CELL, yy, NM[fn(a, b)]))
    return "".join(out)

def block_not(sx, sy):
    bodyx = sx + 34
    out = [lbl(bodyx + CELL, sy+16, "не  p", 20, INK, "700"),
           lbl(bodyx + CELL, sy+34, "отрицание (¬)", 13, "#78808c")]
    hy = sy + 62
    out.append(lbl(bodyx + CELL/2, hy+CELL/2, "p", 15, "#5b5b5b", "600", "middle"))
    out.append(lbl(bodyx + CELL + CELL/2, hy+CELL/2, "не p", 14, "#5b5b5b", "600", "middle"))
    body = hy + CELL + 4
    for i, a in enumerate(V):
        yy = body + i*CELL
        out.append(C(bodyx, yy, NM[a]))
        out.append(C(bodyx + CELL, yy, NM[ztl.NOT(a)]))
    return "".join(out)

def main():
    W, H = 960, 920
    p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
         f'font-family="Georgia,\'DejaVu Serif\',serif">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
         lbl(W/2, 46, "Шесть таблиц ZTL", 27, INK, "700"),
         lbl(W/2, 74, "по краям — три знака входа:  T правда · F ложь · Z не проверено.  "
                      "В теле — только T и F.", 15, "#666")]
    colx = [70, 400, 720]
    rowy = [110, 490]
    p.append(block_not(colx[0], rowy[0]))
    bins = [("∧", "и", ztl.AND), ("∨", "или", ztl.OR),
            ("→", "если… то", ztl.IMP), ("⊕", "либо-либо", ztl.XOR),
            ("↔", "тождество", ztl.XNOR)]
    slots = [(colx[1], rowy[0]), (colx[2], rowy[0]),
             (colx[0], rowy[1]), (colx[1], rowy[1]), (colx[2], rowy[1])]
    for (sign, human, fn), (sx, sy) in zip(bins, slots):
        p.append(block_binary(sx, sy, sign, human, fn))
    # легенда
    ly = 760
    p.append(f'<line x1="70" y1="{ly-24}" x2="{W-70}" y2="{ly-24}" stroke="#e3e3e3"/>')
    p.append(lbl(70, ly, "Почему тело без Z:", 15, INK, "700", "start"))
    p.append(lbl(70, ly+22, "правило считает жадно — T только если правда вынуждена при "
                            "любом доигрывании непроверенного, иначе F.", 14, "#444", "400", "start"))
    p.append(lbl(70, ly+42, "Оттого третий знак нигде не выходит из связки — и оттого "
                            "двойное отрицание Z даёт T, а не Z (см. столбец «не p»).", 14, "#444", "400", "start"))
    p.append(lbl(70, ly+68, "Читать «если»:", 15, INK, "700", "start"))
    p.append(lbl(70, ly+90, "строка — левый вход a, столбец — правый вход b, клетка = a → b. "
                            "F → что угодно = T.", 14, "#444", "400", "start"))
    p.append(lbl(70, ly+110, "Таблица несимметрична — потому оси и подписаны.",
                14, "#444", "400", "start"))
    p.append("</svg>")
    out = pathlib.Path(__file__).parent / "tablicy.svg"
    out.write_text("".join(p), encoding="utf-8")
    print("написано:", out.name, len("".join(p)), "байт")

if __name__ == "__main__":
    main()
