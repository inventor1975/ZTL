# -*- coding: utf-8 -*-
"""
Markdown paper -> print HTML -> PDF, by the same route v1.0 took.

The published v1.0 of the docket was produced by headless Chrome printing an
HTML file (its own metadata says so: Creator HeadlessChrome, Producer
Skia/PDF), and the HTML and whatever produced it were not kept. So v1.1 had
to rediscover the toolchain. This script is here so that v1.2 does not.

There is no pandoc and no LaTeX in this environment; there is python-markdown
and there is Chrome, which is exactly what v1.0 used.

FIGURES. The docket's markdown carries figure BRIEFS — blockquotes describing
a picture to be drawn — not images. The images of v1.0 exist only inside the
published PDF, so they were extracted from it (`pdfimages -j`) into
`paper/figures/` and are mapped by hand below. A brief with no mapped image
stays in the output as a visible brief, which is the honest default: better a
page that says "figure to be drawn here" than one that quietly lost a figure.

Usage:
    python3 paper/mkpdf.py paper/paradox-docket-EN-build.md \\
                           paper/paradox-docket-EN-v1.1.pdf
"""
import os
import re
import subprocess
import sys

import markdown

_HERE = os.path.dirname(os.path.abspath(__file__))

# figure number -> (image files, caption). Captions are v1.0's, read back out
# of the published PDF so the two versions do not drift apart.
FIGURES = {
    "1": (["figures/docket-003-000.jpg"],
          "Fig. 1 — a self-referential sentence is counted, "
          "and issued its verdict"),
    "2": (["figures/docket-007-001.jpg", "figures/docket-007-002.jpg",
           "figures/docket-007-003.jpg"],
          "Fig. 2 — The Three Worlds of Smith and Jones"),
    "3": (["figures/docket-008-004.jpg"],
          "Fig. 3 — The Group Photo: who holds which passport"),
}

CSS = """
@page { size: A4; margin: 20mm 17mm 18mm 17mm; }
body { font-family: "Georgia", "Times New Roman", serif; font-size: 10.5pt;
       line-height: 1.45; color: #111; }
h1 { font-size: 19pt; line-height: 1.2; margin: 0 0 .4em; }
h2 { font-size: 13.5pt; margin: 1.6em 0 .5em; page-break-after: avoid; }
h3 { font-size: 11.5pt; margin: 1.2em 0 .4em; page-break-after: avoid; }
p, li { orphans: 2; widows: 2; }
hr { border: none; border-top: 1px solid #bbb; margin: 1.4em 0; }
table { border-collapse: collapse; width: 100%; font-size: 8.8pt;
        margin: .8em 0; page-break-inside: avoid; }
th, td { border: 1px solid #999; padding: 3px 6px; text-align: left;
         vertical-align: top; }
th { background: #eee; }
code { font-family: "DejaVu Sans Mono", monospace; font-size: 9pt; }
pre { font-family: "DejaVu Sans Mono", monospace; font-size: 7.2pt;
      line-height: 1.25; background: #f6f6f6; border: 1px solid #ddd;
      padding: 6px 8px; white-space: pre-wrap; word-wrap: break-word; }
blockquote { border-left: 3px solid #bbb; margin: 1em 0; padding: .3em 0 .3em 1em;
             color: #444; font-size: 9.5pt; }
figure { margin: 1.2em 0; text-align: center; page-break-inside: avoid; }
figure img { max-width: 100%; height: auto; }
figure.panels img { max-width: 32%; margin: 0 .4%; vertical-align: top; }
figcaption { font-size: 9pt; color: #333; margin-top: .4em; font-style: italic; }
"""

_BRIEF = re.compile(r"^> \*\*\[FIGURE (\d+).*?\*\*\]\*\*\s*$",
                    re.MULTILINE | re.DOTALL)


def _figure_html(num):
    imgs, caption = FIGURES[num]
    cls = " class=\"panels\"" if len(imgs) > 1 else ""
    tags = "".join(f'<img src="{p}" />' for p in imgs)
    return (f'<figure{cls}>{tags}'
            f'<figcaption>{caption}</figcaption></figure>')


def substitute_figures(text):
    """Replace a figure brief by its image, or leave it visible if we have
    none — never drop it silently."""
    out, kept = [], []
    for block in text.split("\n\n"):
        m = re.match(r"> \*\*\[FIGURE (\d+)", block.strip())
        if m and m.group(1) in FIGURES:
            out.append(_figure_html(m.group(1)))
        else:
            if m:
                kept.append(m.group(1))
            out.append(block)
    if kept:
        print(f"  briefs with no image, left visible: {kept}")
    return "\n\n".join(out)


def build(src, dst):
    text = open(src, encoding="utf-8").read()
    text = substitute_figures(text)
    body = markdown.markdown(text, extensions=["tables", "fenced_code",
                                               "sane_lists", "attr_list",
                                               "md_in_html", "footnotes"])
    html_path = os.path.splitext(dst)[0] + ".html"
    open(html_path, "w", encoding="utf-8").write(
        f"<!doctype html><meta charset='utf-8'>"
        f"<title>{os.path.basename(src)}</title>"
        f"<style>{CSS}</style>\n{body}\n")
    cmd = ["google-chrome", "--headless", "--disable-gpu", "--no-sandbox",
           "--no-pdf-header-footer", "--virtual-time-budget=20000",
           f"--print-to-pdf={os.path.abspath(dst)}",
           "file://" + os.path.abspath(html_path)]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    if not os.path.exists(dst):
        print(r.stderr[-2000:])
        raise SystemExit("chrome produced no file")
    print(f"  {dst}  ({os.path.getsize(dst) // 1024} KB)")
    return dst


if __name__ == "__main__":
    src = sys.argv[1] if len(sys.argv) > 1 else \
        os.path.join(_HERE, "paradox-docket-EN-build.md")
    dst = sys.argv[2] if len(sys.argv) > 2 else \
        os.path.join(_HERE, "paradox-docket-EN-v1.1.pdf")
    os.chdir(_HERE)
    print("building", os.path.basename(src))
    build(os.path.basename(src), os.path.basename(dst))
