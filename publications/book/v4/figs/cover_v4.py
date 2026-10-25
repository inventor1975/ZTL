#!/usr/bin/env python3
"""Cover for book v4: honest machine with two boxes and a lamp; A5 proportion."""
import pathlib
W, H = 1000, 1414
INK, MUTED = "#1b1b1b", "#555"
GREEN, RED, GREY = "#4b7a43", "#a6413b", "#7d8794"
BOX = "#efe9dc"
p = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" '
     f'font-family="Georgia,\'DejaVu Serif\',serif">',
     f'<rect width="{W}" height="{H}" fill="#faf8f3"/>',
     f'<rect x="26" y="26" width="{W-52}" height="{H-52}" fill="none" stroke="#e2ddd0" stroke-width="2"/>',
     # title
     f'<text x="{W/2}" y="210" font-size="78" font-weight="700" fill="{INK}" text-anchor="middle">Честная машинка</text>',
     f'<text x="{W/2}" y="310" font-size="78" font-weight="700" fill="{INK}" text-anchor="middle">и обманщик</text>',
     f'<text x="{W/2}" y="385" font-size="34" fill="{MUTED}" text-anchor="middle" font-style="italic">'
     f'Введение в ZTL — логику нулевого доверия</text>',
     f'<text x="{W/2}" y="450" font-size="32" fill="{INK}" text-anchor="middle" font-weight="600">Виталий Резник</text>',
     # machine body
     f'<rect x="250" y="620" width="500" height="330" rx="28" fill="#fff" stroke="{INK}" stroke-width="5"/>',
     # lamp
     f'<circle cx="{W/2}" cy="700" r="46" fill="#f3d36b" stroke="{INK}" stroke-width="5"/>',
     # two boxes
     f'<rect x="300" y="800" width="160" height="110" rx="10" fill="{BOX}" stroke="{INK}" stroke-width="4"/>',
     f'<rect x="540" y="800" width="160" height="110" rx="10" fill="{BOX}" stroke="{INK}" stroke-width="4"/>',
     f'<text x="380" y="872" font-size="40" fill="{GREEN}" text-anchor="middle" font-weight="700">твоя</text>',
     f'<text x="620" y="874" font-size="56" fill="{GREY}" text-anchor="middle" font-weight="700">Z</text>',
     f'<text x="380" y="990" font-size="28" fill="{MUTED}" text-anchor="middle">ты</text>',
     f'<text x="620" y="990" font-size="28" fill="{MUTED}" text-anchor="middle">обманщик</text>',
     # values
     f'<g text-anchor="middle" font-size="38" font-weight="700">',
     f'<text x="{W/2-210}" y="{H-150}" fill="{GREEN}">истинно</text>',
     f'<text x="{W/2}" y="{H-150}" fill="{RED}">ложно</text>',
     f'<text x="{W/2+190}" y="{H-150}" fill="{GREY}">Z</text></g>',
     f'<text x="{W/2}" y="{H-100}" font-size="27" fill="#888" text-anchor="middle">'
     f'Z всегда в руках обманщика</text>',
     '</svg>']
out = pathlib.Path(__file__).parent / "cover_v4.svg"
out.write_text("".join(p), encoding="utf-8")
print(out)
