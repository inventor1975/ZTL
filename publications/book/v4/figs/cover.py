#!/usr/bin/env python3
"""Book v4 cover: the original cover (curator), only the bottom caption changed to the book's own words."""
import pathlib
W, H = 1000, 1414
INK = "#1b1b1b"
GREEN, RED, GREY = "#4b7a43", "#a6413b", "#7d8794"
p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
     f'font-family="Georgia,\'DejaVu Serif\',serif">',
     f'<rect width="{W}" height="{H}" fill="#faf8f3"/>',
     f'<rect x="26" y="26" width="{W-52}" height="{H-52}" fill="none" '
     f'stroke="#e2ddd0" stroke-width="2"/>',
     # крупное ZTL фоном — влезает с полями
     f'<text x="{W/2}" y="{H/2+130}" font-size="360" font-weight="700" '
     f'fill="#ece7db" text-anchor="middle" letter-spacing="20">ZTL</text>',
     # название
     f'<text x="{W/2}" y="240" font-size="120" font-weight="700" fill="{INK}" '
     f'text-anchor="middle">Проверили?</text>',
     f'<text x="{W/2}" y="308" font-size="33" fill="#555" text-anchor="middle" '
     f'font-style="italic">Введение в логику, которая не верит на слово</text>',
     # автор — байлайн под подзаголовком (без «куратор», по правилу)
     f'<text x="{W/2}" y="366" font-size="30" fill="{INK}" text-anchor="middle" '
     f'font-weight="600">Виталий Резник</text>',
     f'<g text-anchor="middle" font-size="40" font-weight="700">',
     f'<text x="{W/2-220}" y="{H-150}" fill="{GREEN}">истинно</text>',
     f'<text x="{W/2+20}" y="{H-150}" fill="{RED}">ложно</text>',
     f'<text x="{W/2+200}" y="{H-150}" fill="{GREY}">Z</text></g>',
     f'<text x="{W/2}" y="{H-100}" font-size="29" fill="#888" text-anchor="middle">'
     f'Z — это решаешь не ты</text>',
     '</svg>']
out = pathlib.Path(__file__).parent / "cover.svg"
out.write_text("".join(p), encoding="utf-8")
print(out)
