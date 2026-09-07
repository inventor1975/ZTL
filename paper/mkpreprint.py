#!/usr/bin/env python3
"""ZTL preprint: Markdown -> LaTeX (pandoc) -> PDF (lualatex).

The route v1.2 and v1.3 took (their PDFs say "LaTeX via pandoc", LuaTeX,
FreeSerif/FreeMono) — the command was never kept, so v1.4 had to rediscover
it by rebuilding v1.3's own text and comparing page counts. This script is
here so that v1.5 does not.

FONTS: FreeSerif / FreeMono are mandatory. Latin Modern silently drops the
logical glyphs (∧ ∨ ⊥ ⊨ ⊕ ↛ ⟹ …); a dropped glyph is a "Missing character"
line in the lualatex log, and this script fails on any such line rather
than shipping a PDF with holes.

Usage:
    python3 paper/mkpreprint.py paper/ZTL-draft_1.4.md paper/ZTL-preprint-v1.4.pdf [--margin 1in]
"""
import os, re, shutil, subprocess, sys, tempfile

def main():
    args = sys.argv[1:]
    margin = None
    if "--margin" in args:
        i = args.index("--margin"); margin = args[i + 1]; del args[i:i + 2]
    src, out = map(os.path.abspath, args)
    with tempfile.TemporaryDirectory() as tmp:
        tex = os.path.join(tmp, "paper.tex")
        hdr = os.path.join(tmp, "header.tex")
        with open(hdr, "w") as h:   # long runs of \texttt module names (acknowledgements) overflowed the margin at pandoc's 3em
            h.write("\\setlength{\\emergencystretch}{6em}\n")
        cmd = ["pandoc", src, "-f", "markdown", "-t", "latex", "-s", "-o", tex, "-H", hdr,
               "-V", "mainfont=FreeSerif", "-V", "monofont=FreeMono",
               # PDF metadata only (title-meta does not trigger \maketitle; the H1 stays the title on the page)
               "-V", "title-meta=ZTL — Zero-Trust Logic", "-V", "author-meta=Vitaly Reznik"]
        if margin:
            cmd += ["-V", f"geometry:margin={margin}"]
        subprocess.run(cmd, check=True)
        for _ in range(2):   # second pass settles page references
            r = subprocess.run(["lualatex", "-interaction=nonstopmode", "-halt-on-error", "paper.tex"],
                               cwd=tmp, capture_output=True, text=True)
        log = open(os.path.join(tmp, "paper.log"), encoding="utf-8", errors="replace").read()
        missing = sorted(set(re.findall(r"Missing character: There is no (\S+)", log)))
        if r.returncode != 0:
            sys.stderr.write(r.stdout[-3000:]); sys.exit("lualatex failed")
        shutil.copy(os.path.join(tmp, "paper.pdf"), out)
        shutil.copy(os.path.join(tmp, "paper.log"), out + ".log")   # kept beside the PDF (ignored by git)
        overfull = len(re.findall(r"^Overfull \\hbox", log, re.M))
    pages = subprocess.run(["pdfinfo", out], capture_output=True, text=True).stdout
    pages = re.search(r"Pages:\s+(\d+)", pages).group(1)
    fonts = sorted({l.split()[0].split("+")[-1] for l in
                    subprocess.run(["pdffonts", out], capture_output=True, text=True).stdout.splitlines()[2:] if l.strip()})
    print(f"{out}: {pages} pages; fonts {fonts}; overfull hboxes {overfull}; missing glyphs {missing or 'none'}")
    if missing:
        sys.exit("REFUSED: missing glyphs — a PDF with holes is not shipped")

if __name__ == "__main__":
    main()
