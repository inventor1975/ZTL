#!/usr/bin/env python3
"""Четыре «отрицательные» связки в ZTL: NAND NOR NXOR NIMPL.
Показаны так, как их считает СУДЬЯ (жадно, ¬ поверх связки). Подсвечены
клетки, где это расходится с правилом, применённым к связке ЦЕЛИКОМ, —
тот же разрыв жадного и целого, что в девятой главе. Всё из ztl.py."""
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))
import ztl
T, F, Z = ztl.T, ztl.F, ztl.Z
V = [T, F, Z]; NM = {T: "T", F: "F", Z: "Z"}
NOT, AND, OR, IMP, XOR = ztl.NOT, ztl.AND, ztl.OR, ztl.IMP, ztl.XOR
lift2 = ztl.lift2
cnot = lambda a: F if a == T else T
cand = lambda a, b: T if (a == T and b == T) else F
cor = lambda a, b: T if (a == T or b == T) else F
cimp = lambda a, b: T if (a == F or b == T) else F
cxor = lambda a, b: T if a != b else F
FILL = {"T": "#cfe8c9", "F": "#f2ccc9", "Z": "#dde2ea"}
EDGE = {"T": "#4b7a43", "F": "#a6413b", "Z": "#7d8794"}
HL = "#e8a13a"; INK = "#1b1b1b"; CELL = 42

def txt(x, y, t, s=14, c="#333", w="400", a="start"):
    return f'<text x="{x}" y="{y}" font-size="{s}" fill="{c}" font-weight="{w}" text-anchor="{a}">{t}</text>'

def table(sx, sy, title, greedy, principled):
    hot = {(NM[a], NM[b]) for a in V for b in V if greedy(a, b) != principled(a, b)}
    out = [txt(sx + 30 + CELL*1.5, sy - 26, title, 18, INK, "700", "middle"),
           txt(sx + 30 + CELL*1.5, sy - 8, "b →", 12, "#9aa1ac", "400", "middle")]
    for j, b in enumerate(V):
        out.append(txt(sx + 30 + j*CELL + CELL/2, sy + CELL/2 + 4, NM[b], 14, "#5b5b5b", "600", "middle"))
    by = sy + CELL
    out.append(f'<text x="{sx+8}" y="{by+CELL*1.5}" font-size="12" fill="#9aa1ac" '
               f'text-anchor="middle" transform="rotate(-90 {sx+8} {by+CELL*1.5})">a ↓</text>')
    for i, a in enumerate(V):
        out.append(txt(sx + 22, by + i*CELL + CELL/2 + 4, NM[a], 14, "#5b5b5b", "600", "middle"))
        for j, b in enumerate(V):
            m = NM[greedy(a, b)]; hotc = (NM[a], NM[b]) in hot
            x = sx + 30 + j*CELL; y = by + i*CELL
            out.append(f'<rect x="{x}" y="{y}" width="{CELL}" height="{CELL}" rx="6" '
                       f'fill="{FILL[m]}" stroke="{HL if hotc else EDGE[m]}" '
                       f'stroke-width="{4 if hotc else 1.4}"/>')
            out.append(txt(x + CELL/2, y + CELL/2 + 6, m, 20, INK, "600", "middle"))
    return "".join(out), len(hot)

def main():
    W, H = 950, 760
    p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
         f'font-family="Georgia,\'DejaVu Serif\',serif">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
         txt(W/2, 42, "Четыре отрицательные связки ZTL", 24, INK, "700", "middle"),
         txt(W/2, 66, "так, как их считает судья: ¬ поверх связки, по шагам", 14, "#666", "400", "middle")]
    specs = [
        ("NAND  ¬(a∧b)", lambda a, b: NOT(AND(a, b)), lift2(lambda a, b: cnot(cand(a, b)))),
        ("NOR  ¬(a∨b)",  lambda a, b: NOT(OR(a, b)),  lift2(lambda a, b: cnot(cor(a, b)))),
        ("NXOR  ¬(a⊕b)", lambda a, b: NOT(XOR(a, b)), lift2(lambda a, b: cnot(cxor(a, b)))),
        ("NIMPL  ¬(a→b)", lambda a, b: NOT(IMP(a, b)), lift2(lambda a, b: cnot(cimp(a, b)))),
    ]
    slots = [(120, 170), (500, 170), (120, 420), (500, 420)]
    counts = []
    for (title, g, pr), (sx, sy) in zip(specs, slots):
        svg, n = table(sx, sy, title, g, pr); p.append(svg); counts.append((title.split()[0], n))
    ly = 610
    p.append(f'<line x1="60" y1="{ly-16}" x2="{W-60}" y2="{ly-16}" stroke="#e3e3e3"/>')
    p.append(txt(60, ly+4, "Оранжевым — клетки, где жадный счёт (как выше) расходится с правилом, приложенным к связке ЦЕЛИКОМ.", 13, "#444"))
    cs = ", ".join(f"{n}: {c}" for n, c in counts)
    p.append(txt(60, ly+26, f"Сколько таких клеток — {cs}. Тот же разрыв жадного и целого, что в девятой главе.", 13, "#444"))
    p.append(txt(60, ly+52, "Тонкость про NXOR: правило-к-целому даёт ровно наш ↔ (тождество), а жадное ¬(a⊕b) — нет, мимо на 5 клетках.", 13, "#2f6b34", "600"))
    p.append(txt(60, ly+78, "«Наши» рабочие таблицы — жадные: язык считает по шагам; NAND/NOR/… не отдельные связки, а ¬ поверх наших шести.", 13, "#555"))
    p.append(txt(60, ly+100, "Считано из ztl.py.", 12, "#999"))
    p.append("</svg>")
    (pathlib.Path(__file__).parent / "otricaniya.svg").write_text("".join(p), encoding="utf-8")
    print("написано, счётчики:", counts)

if __name__ == "__main__":
    main()
