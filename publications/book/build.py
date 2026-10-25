#!/usr/bin/env python3
"""Собирает КНИГА-полностью.md из глав. Титул и части — здесь, а не в сборке,
чтобы пересборка их больше не съедала."""
import pathlib, re

PARTS = {  # перед какой главой встаёт заголовок части
    1:  "ЧАСТЬ I. НУЖНО ТОЛЬКО УМЕТЬ СПОРИТЬ",
    4:  "ЧАСТЬ II. НУЖНО ЧИТАТЬ ТАБЛИЦУ",
    7:  "ЧАСТЬ III. НУЖНО НЕМНОГО АЛГЕБРЫ",
    9:  "ЧАСТЬ IV. НУЖНО ПОНИМАТЬ ФУНКЦИЮ",
    12: "ЧАСТЬ V. НУЖНО СЛЕДИТЬ ЗА ДОКАЗАТЕЛЬСТВОМ",
    14: "ЧАСТЬ VI. НУЖНА ЛОГИКА КАК ПРЕДМЕТ",
}
here = pathlib.Path(__file__).parent
out = [here.joinpath("00-front.md").read_text(encoding="utf-8").rstrip(), ""]
chapters = sorted(p for p in here.glob("*.md") if re.match(r"[01]\d-", p.name)
                  and not p.name.startswith("00-"))
for p in chapters:
    n = int(p.name[:2])
    if n in PARTS:
        out += ["", "", f"# {PARTS[n]}", "", "---", ""]
    out.append(p.read_text(encoding="utf-8").rstrip())
    out.append("")
text = "\n".join(out).rstrip() + "\n"
dst = here / "КНИГА-полностью.md"
dst.write_text(text, encoding="utf-8")
print(f"{len(chapters)} глав, {len(text.split())} слов, {len(text)//1024} КБ -> {dst.name}")
