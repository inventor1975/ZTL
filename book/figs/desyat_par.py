#!/usr/bin/env python3
"""Все 10 таблиц ZTL: ЖАДНЫЙ (наш) против ТЕРПЕЛИВОГО (супероценка).
Терпеливый молчит (Z) там, где ответ зависит от непроверенного; жадный
схлопывает это молчание в вердикт. Подсвечены ровно клетки схлопывания.
Всё из ztl.py; терпеливый = супероценка связки/композиции."""
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))
import ztl
T, F, Z = ztl.T, ztl.F, ztl.Z
V = [T, F, Z]; NM = {T: "T", F: "F", Z: "Z"}
NOT, AND, OR, IMP, XOR = ztl.NOT, ztl.AND, ztl.OR, ztl.IMP, ztl.XOR
subs = lambda x: [x] if x in (T, F) else [T, F]
cnot = lambda a: F if a == T else T
cand = lambda a, b: T if a == T and b == T else F
cor = lambda a, b: T if a == T or b == T else F
cimp = lambda a, b: T if a == F or b == T else F
cxor = lambda a, b: T if a != b else F
def pat2(cl, a, b):
    o = {cl(x, y) for x in subs(a) for y in subs(b)}
    return T if o == {T} else F if o == {F} else Z
def pat1(cl, a):
    o = {cl(x) for x in subs(a)}
    return T if o == {T} else F if o == {F} else Z
FILL = {"T": "#cfe8c9", "F": "#f2ccc9", "Z": "#dde2ea"}
EDGE = {"T": "#4b7a43", "F": "#a6413b", "Z": "#7d8794"}
HL = "#e8a13a"; INK = "#1b1b1b"; CELL = 33
def txt(x, y, t, s=13, c="#333", w="400", a="start"):
    return f'<text x="{x}" y="{y}" font-size="{s}" fill="{c}" font-weight="{w}" text-anchor="{a}">{t}</text>'

def cellrect(x, y, m, hot):
    return (f'<rect x="{x}" y="{y}" width="{CELL}" height="{CELL}" rx="5" fill="{FILL[m]}" '
            f'stroke="{HL if hot else EDGE[m]}" stroke-width="{3.5 if hot else 1.2}"/>'
            + txt(x + CELL/2, y + CELL/2 + 5, m, 16, INK, "600", "middle"))

def grid2(sx, sy, val, hotset):
    out = []
    for j, b in enumerate(V):
        out.append(txt(sx + 20 + j*CELL + CELL/2, sy + CELL/2 + 4, NM[b], 11, "#777", "400", "middle"))
    for i, a in enumerate(V):
        out.append(txt(sx + 10, sy + CELL + i*CELL + CELL/2 + 4, NM[a], 11, "#777", "400", "middle"))
        for j, b in enumerate(V):
            out.append(cellrect(sx + 20 + j*CELL, sy + CELL + i*CELL, NM[val(a, b)],
                                (NM[a], NM[b]) in hotset))
    return "".join(out)

def block2(sx, sy, name, greedy, cl):
    hot = {(NM[a], NM[b]) for a in V for b in V if greedy(a, b) != pat2(cl, a, b)}
    out = [txt(sx, sy - 6, name, 16, INK, "700"),
           txt(sx + 20 + CELL*1.5, sy + 12, "жадный", 11, "#a6413b", "600", "middle"),
           txt(sx + 175 + CELL*1.5, sy + 12, "терпеливый", 11, "#4b7a43", "600", "middle"),
           grid2(sx, sy + 16, greedy, hot),
           grid2(sx + 175, sy + 16, lambda a, b: pat2(cl, a, b), hot),
           txt(sx + 145, sy + 16 + CELL*2, "≠" if hot else "=", 20, HL if hot else "#4b7a43", "700", "middle")]
    return "".join(out), len(hot)

def block1(sx, sy):  # унарное ¬
    hot = {NM[a] for a in V if NOT(a) != pat1(cnot, a)}
    out = [txt(sx, sy - 6, "¬  не", 16, INK, "700"),
           txt(sx + 30, sy + 12, "жадный", 11, "#a6413b", "600", "middle"),
           txt(sx + 175 + 15, sy + 12, "терпеливый", 11, "#4b7a43", "600", "middle")]
    for i, a in enumerate(V):
        y = sy + 16 + CELL + i*CELL
        out.append(txt(sx + 10, y + CELL/2 + 4, NM[a], 11, "#777", "400", "middle"))
        out.append(cellrect(sx + 20, y, NM[NOT(a)], NM[a] in hot))
        out.append(txt(sx + 175 + 10, y + CELL/2 + 4, NM[a], 11, "#777", "400", "middle"))
        out.append(cellrect(sx + 175 + 20, y, NM[pat1(cnot, a)], NM[a] in hot))
    return "".join(out), len(hot)

def main():
    W, H = 830, 1360
    p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
         f'font-family="Georgia,\'DejaVu Serif\',serif">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
         txt(W/2, 40, "Все 10 таблиц: жадный против терпеливого", 22, INK, "700", "middle"),
         txt(W/2, 64, "терпеливый молчит (Z), где ответ зависит от непроверенного; "
                      "жадный схлопывает молчание в вердикт", 13, "#666", "400", "middle"),
         txt(W/2, 82, "оранжевым — ровно клетки схлопывания", 13, "#a6413b", "600", "middle")]
    y0 = 130; dy = 235; sx = 90
    counts = []
    svg, n = block1(sx, y0); p.append(svg); counts.append(("¬", n))
    base = [("∧  и", AND, cand), ("∨  или", OR, cor), ("→  если", IMP, cimp),
            ("⊕  либо", XOR, cxor), ("↔  тожд", lambda a, b: ztl.XNOR(a, b),
             lambda a, b: (T if a == b else F))]
    neg = [("¬(a∧b)", lambda a, b: NOT(AND(a, b)), lambda a, b: cnot(cand(a, b))),
           ("¬(a∨b)", lambda a, b: NOT(OR(a, b)), lambda a, b: cnot(cor(a, b))),
           ("¬(a⊕b)", lambda a, b: NOT(XOR(a, b)), lambda a, b: cnot(cxor(a, b))),
           ("¬(a→b)", lambda a, b: NOT(IMP(a, b)), lambda a, b: cnot(cimp(a, b)))]
    items = base + neg
    # ¬ занимает первый слот; дальше 5 слотов вниз, потом... всего 10 -> 5 строк x 2 колонки
    slots = []
    for r in range(5):
        slots.append((sx, y0 + r*dy))
        slots.append((sx + 400, y0 + r*dy))
    # первый слот уже занят ¬; перекрываем: положим ¬ в slot0, остальные 9 в slots[1..9]
    used = slots[1:1+len(items)]
    for (name, g, cl), (bx, by) in zip(items, used):
        svg, n = block2(bx, by, name, g, cl); p.append(svg); counts.append((name.split()[0], n))
    ly = y0 + 5*dy - 40
    p.append(f'<line x1="60" y1="{ly}" x2="{W-60}" y2="{ly}" stroke="#e3e3e3"/>')
    p.append(txt(60, ly+22, "Расхождений (клеток схлопывания): "
                            + ", ".join(f"{c}:{n}" for c, n in counts) + ".", 13, "#444"))
    p.append(txt(60, ly+44, "Больше нигде два судьи не спорят. Вся «незеркальность» ZTL — "
                            "одна операция: молчание → F.", 13, "#2f6b34", "600"))
    p.append(txt(60, ly+64, "Терпеливые таблицы — это сильный Клини; ZTL — он же, лишённый "
                            "права молчать. Считано из ztl.py.", 12, "#888"))
    p.append("</svg>")
    (pathlib.Path(__file__).parent / "desyat_par.svg").write_text("".join(p), encoding="utf-8")
    print("написано, счётчики:", counts)

if __name__ == "__main__":
    main()
