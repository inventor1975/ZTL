#!/usr/bin/env bash
# Build the whole v4 book: cover + contents (with page numbers, two passes) + intro + chapters.
# Usage: ./mkbook.sh [OUT.pdf]
set -e
cd "$(dirname "$0")"
out="${1:-Проверили-v4.pdf}"
tmp=/tmp/claude-1000/book-v4; mkdir -p "$tmp"
chapters=(00-vvedenie.md 0[1-9]-*.md 1[01]-*.md)
title() { grep -m1 '^# ' "$1" | sed 's/^# //'; }
toc() {   # $1 = file with "title<TAB>page" lines, or empty for the first pass
  echo '<div class="cover"><img src="figs/cover.png" alt="Проверили? Введение в ZTL"></div>'
  echo; echo '# Содержание {.unnumbered}'; echo; echo '<ul class="toc">'
  for f in "${chapters[@]}"; do
    t=$(title "$f"); n=$( [ -n "$1" ] && awk -F'\t' -v t="$t" '$1==t{print $2}' "$1" || echo "00")
    echo "<li><span class=\"t\">$t</span><span class=\"n\">$n</span></li>"
  done
  echo '</ul>'; echo
}
build() {  # $1 = toc page file or empty
  { toc "$1"; for f in "${chapters[@]}"; do sed '/<div class="cover">/d' "$f"; printf '\n\n'; done; } > "$tmp/book.md"
  ~/.local/bin/pandoc "$tmp/book.md" -s --embed-resources --resource-path="$PWD" \
    --css ../figs/book.css --css figs/v4.css -V lang=ru \
    --metadata title="Проверили? Введение в ZTL" -V title= -V pagetitle="Проверили? Введение в ZTL" \
    -o "$tmp/book.html"
  google-chrome --headless --disable-gpu --no-pdf-header-footer --print-to-pdf="$out" "$tmp/book.html" 2>/dev/null
}
build ""
# find the page where each chapter title starts
: > "$tmp/pages.tsv"
np=$(pdfinfo "$out" | awk '/Pages/{print $2}')
for f in "${chapters[@]}"; do
  t=$(title "$f"); head=$(echo "$t" | cut -c1-20)
  for ((p=3; p<=np; p++)); do
    if pdftotext -f $p -l $p "$out" - 2>/dev/null | head -3 | grep -q "^$head"; then printf '%s\t%s\n' "$t" "$p" >> "$tmp/pages.tsv"; break; fi
  done
done
build "$tmp/pages.tsv"
echo "$out: $(pdfinfo "$out" | awk '/Pages/{print $2}') стр."; cat "$tmp/pages.tsv"
