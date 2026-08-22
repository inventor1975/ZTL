#!/usr/bin/env bash
# Собирает КНИГА.pdf из глав. Требует: pandoc (~/.local/bin), google-chrome.
set -e
cd "$(dirname "$0")"
./build.py
~/.local/bin/pandoc КНИГА-полностью.md -s --embed-resources --css figs/book.css \
  -V pagetitle="Проверили?" -o kniga.html
google-chrome --headless --disable-gpu --no-pdf-header-footer \
  --print-to-pdf="КНИГА.pdf" "kniga.html" 2>/dev/null
pages=$(pdfinfo КНИГА.pdf | awk '/Pages/{print $2}')
echo "КНИГА.pdf готов: $pages страниц, $(( $(stat -c%s КНИГА.pdf) / 1024 )) КБ"
