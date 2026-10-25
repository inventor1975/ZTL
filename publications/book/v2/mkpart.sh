#!/usr/bin/env bash
# Build a PDF of the given v2 chapters for reading on a phone: ./mkpart.sh OUT.pdf 01-*.md 02-*.md ...
set -e
cd "$(dirname "$0")"
out="$1"; shift
{ for f in "$@"; do cat "$f"; printf '\n\n'; done; } > /tmp/claude-1000/book-v2-part.md
~/.local/bin/pandoc /tmp/claude-1000/book-v2-part.md -s --embed-resources --resource-path="$PWD" --css ../figs/book.css \
  -V pagetitle="Проверили? v2" -o /tmp/claude-1000/book-v2-part.html
google-chrome --headless --disable-gpu --no-pdf-header-footer --print-to-pdf="$out" /tmp/claude-1000/book-v2-part.html 2>/dev/null
echo "$out: $(pdfinfo "$out" | awk '/Pages/{print $2}') стр."
