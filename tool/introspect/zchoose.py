#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""zchoose — ТЕЛО яруса 3: выбиратель доброго среди истинного.

    ./zchoose.py <текст-файл> [--model claude-opus-4-8] [--key <файл>]

Ярус 3 (этика/выбор). Ниже: проверка (ztl.py — T/F/Z) и суд (zboundary — E).
Сюда приходит уже ИСТИННОЕ. Вопрос не «истинно ли», а «истинное — ДОБРОЕ ли,
или СОБЛАЗН (истинно, но во вред)». Задача — выбрать доброе, отбросить соблазн.

ЧЕСТНАЯ ГРАНИЦА. Соблазн НЕ вычислим из частей: вред живёт в УПОТРЕБЛЕНИИ, не в
утверждении — та же причина, по которой S не пускают в ядро (сломало бы truth-
functionality). Поэтому тело — НЕ алгоритм, а КОДИФИЦИРОВАННАЯ ПРОЦЕДУРА СУЖДЕНИЯ:
одна алгоритмическая зацепка (тэлл абсолюта) НАВОДИТ, а сам вердикт даёт судья
(Опус) по рубрике. Код-арбитр T/F/Z остаётся на ярусе 1; здесь честно — суждение.

ТРИ МЕТКИ ОСИ ЦЕННОСТИ (промерены обкаткой на границе, «О помощи», 2026-08-23):
    T   доброе — истинно и стоит само, не во вред.
    T?  T-УЯЗВИМОЕ — доброе КАК СКАЗАНО, но легко оборачивается во вред при иной
        рамке («сначала обеспечь себя»: мудрость ИЛИ вечное себя-вперёд).
    S   СОБЛАЗН — истинное зерно УЖЕ обёрнуто в оправдание холода/расчёта/сдачи
        («не спасёшь, сколько ни вкладывай»): нож уже повёрнут.

Различие T? и S — в РАМКЕ: обёрнуто ли УЖЕ, или лишь оборачиваемо. И соблазн часто
ЕДЕТ НА АБСОЛЮТЕ («всякий/никогда/сколько ни»): размашистость оборачивает правду в
яд, потому абсолют — тэлл, где искать. Дисциплина: не мазать доброе в S из паранойи
и не пропускать тонкий яд.
"""
from __future__ import annotations

import argparse
import os
import pathlib
import re
import sys

import anthropic

HERE = pathlib.Path(__file__).resolve().parent
DEFAULT_MODEL = "claude-opus-4-8"
MAX_TOKENS = 4000

# Тэлл абсолюта — единственная АЛГОРИТМИЧЕСКАЯ зацепка тела: наводит на места, где
# правда чаще всего оборачивается в яд. Это не вердикт, а «смотри сюда»: соблазн
# может быть и без абсолюта (тогда его берёт судья), и абсолют бывает невинным.
# Матчим по ГРАНИЦЕ СЛОВА, иначе «всё же» ложно ловится в «все», а «всех разумных»
# шумит — оставлены только ясные квантор-абсолюты, дискурсивное «всё же» убрано.
ABSOLUTES = [
    r"всяк\w*", r"кажд\w*", r"люб(ой|ому|ого|ая|ые)", r"никто", r"никого",
    r"никому", r"никогда", r"всегда", r"вечно", r"сколько ни", r"ни один\w*",
    r"ни одного", r"только тем\b", r"только те\b", r"лишь те\w*", r"во что бы",
]
_ABS_RE = re.compile(r"(?<!\w)(" + "|".join(ABSOLUTES) + r")(?!\w)")


def absolute_flags(text: str) -> list[str]:
    """Куски текста, несущие абсолют — где искать соблазн (тэлл, не вердикт)."""
    low = text.lower().replace("ё", "е")
    hits = []
    for m in _ABS_RE.finditer(low):
        s = max(0, m.start() - 24)
        e = min(len(text), m.end() + 30)
        hits.append(f"…{text[s:e].strip()}…  [абсолют: {m.group(1)}]")
    return hits


# Канонические метки оси ЦЕННОСТИ (ярус 3). Их ИМПОРТИРУЕТ тетрадь (introspect),
# чтобы S/T? были ОДНИМ определением на две руки, а не двумя. Тело — источник,
# тетрадь — рука. В коде и в рассуждении S = одно «истинно, но во вред», примеры разные.
VALUE_MARKS = """- T  = ДОБРОЕ: истинно и стоит само, не во вред.
- T? = T-УЯЗВИМОЕ: истинно и доброе КАК СКАЗАНО (в коде — инвариант держится СЕЙЧАС), \
но легко оборачивается во вред при иной рамке/входе. Скажи, во что оборачивается.
- S  = СОБЛАЗН (Seduction): истинное зерно УЖЕ обёрнуто во вред. В коде — утечка, рост \
без предела, инвариант, что не роняет, но копит вред. В рассуждении — истина, \
употреблённая для оправдания холода, расчёта, инструментализации, сдачи. Нож уже повёрнут."""

RUBRIC = """Ты — ярус ЭТИКИ/ВЫБОРА над логикой проверки. Тебе дают РАССУЖДЕНИЕ, в \
котором ходы УЖЕ считаются истинными. Твой вопрос не «истинно ли», а «истинное — \
ДОБРОЕ ли, или соблазн». Разложи текст на атомарные ходы и каждому поставь метку:

""" + VALUE_MARKS + """
- F  = ложь (опровержимо контрпримером). Z = размашистый абсолют на веру. E = судить не на чем.

КЛЮЧ РАЗЛИЧЕНИЯ T? и S — РАМКА: T? лишь ОБОРАЧИВАЕМО, S УЖЕ обёрнуто в этом тексте. \
Соблазн часто ЕДЕТ НА АБСОЛЮТЕ («всякий/никогда/сколько ни») — размашистость и есть \
обёртка. Дисциплина: НЕ мазать доброе в S из паранойи; НЕ пропускать тонкий яд.

Верни каждый ход: цитата (кратко) — [МЕТКА] — одна строка почему (для T?/S — в чём \
оборачивание/рамка). В конце — раздел ВЫБОР: какие ходы ОСТАВить (T, и T? с явным \
предупреждением рамки), какие ОТБРОСИТЬ (S), одной фразой — что выбрать по совести, \
а не «просто логично».

Текст:

{text}"""


def load_key(keyfile: str | None) -> str:
    k = os.environ.get("ANTHROPIC_API_KEY", "").strip()
    if k:
        return k
    for cand in (keyfile, os.environ.get("INTROSPECT_KEYFILE"),
                 str(HERE / ".anthropic_key"), str(HERE.parent / ".anthropic_key")):
        if cand and pathlib.Path(cand).is_file():
            return pathlib.Path(cand).read_text(encoding="utf-8").strip()
    sys.exit("нет ключа: ANTHROPIC_API_KEY, --key <файл> или .anthropic_key рядом")


def choose(text: str, model: str, key: str) -> str:
    """Суждение яруса 3: разметка T/T?/S + выбор. Судья — Опус."""
    client = anthropic.Anthropic(api_key=key)
    with client.messages.stream(
            model=model, max_tokens=MAX_TOKENS,
            thinking={"type": "adaptive"},
            messages=[{"role": "user", "content": RUBRIC.format(text=text)}]) as st:
        msg = st.get_final_message()
    return "".join(b.text for b in msg.content if b.type == "text").strip()


# ЧАНКИНГ — промерен 2026-08-23 (см. память project_atom_notebook_experiment). Целый
# длинный текст упирается в потолок ответа и ОБРЫВАЕТСЯ; чанки — единственный способ
# досчитать. Не быстрее и не дешевле (рубрика повторяется), плата — режем раму. Потому
# режем по ЕСТЕСТВЕННЫМ швам (заголовки/границы абзацев), НИКОГДА не поперёк абзаца:
# на ценностной оси рамка И ЕСТЬ суждение, и край куска пере-обрамляет пограничные T?/T.
def chunk_prose(text: str, target_lines: int = 50) -> list[tuple[str, str]]:
    """Резать прозу по швам: копим абзацы до target_lines непустых строк, заголовок
    (#…) открывает новый чанк. Возвращает [(метка-зачин, текст-чанка)]."""
    paras = [p for p in text.split("\n\n") if p.strip()]
    chunks: list[str] = []
    cur: list[str] = []
    cnt = 0
    for p in paras:
        stripped = p.lstrip()
        # ЖЁСТКИЙ шов — только заголовок ВЕРХНЕГО уровня (глава/часть: «# …», не «## …»),
        # иначе книга с подзаголовками крошится в сотню огрызков. «##»+ — мягкие, едут в куске.
        is_top = stripped.startswith("# ") or stripped.rstrip() in ("#",)
        if is_top and cur:                          # глава — естественный шов
            chunks.append("\n\n".join(cur)); cur, cnt = [], 0
        cur.append(p); cnt += p.count("\n") + 1
        if cnt >= target_lines and not is_top:      # добрали размер — рвём по границе абзаца
            chunks.append("\n\n".join(cur)); cur, cnt = [], 0
    if cur:
        chunks.append("\n\n".join(cur))
    out = []
    for c in chunks:
        first = next((l.strip() for l in c.splitlines() if l.strip()), "")
        out.append((first[:60], c))
    return out


def choose_chunked(chunks: list[tuple[str, str]], model: str, key: str,
                   jobs: int = 6) -> list[tuple[str, str]]:
    """Судить каждый чанк параллельно (как форки). Порядок чанков сохраняется."""
    import concurrent.futures as cf

    def one(item: tuple[str, str]) -> tuple[str, str]:
        label, ctext = item
        try:
            return label, choose(ctext, model, key)
        except Exception as e:                      # один чанк не роняет прогон
            return label, f"(ОШИБКА: {type(e).__name__}: {e})"

    with cf.ThreadPoolExecutor(max_workers=jobs) as pool:
        return list(pool.map(one, chunks))


def main() -> int:
    ap = argparse.ArgumentParser(description="ярус 3: выбрать доброе среди истинного")
    ap.add_argument("target", help="текст-файл рассуждения")
    ap.add_argument("--model", default=os.environ.get("INTROSPECT_MODEL", DEFAULT_MODEL))
    ap.add_argument("--key", default=None)
    ap.add_argument("--chunk", choices=["auto", "on", "off"], default="auto",
                    help="резать длинную прозу по швам (auto: по размеру; целое обрывается на потолке)")
    ap.add_argument("--jobs", type=int, default=6, help="чанков разом")
    args = ap.parse_args()

    text = pathlib.Path(args.target).read_text(encoding="utf-8", errors="replace")

    # 1) алгоритмическая зацепка — наводка, не вердикт
    flags = absolute_flags(text)
    print("=== ТЭЛЛ АБСОЛЮТА (где чаще прячется соблазн) ===")
    print("\n".join(f"  {f}" for f in flags) if flags else "  (абсолютов не найдено)")
    print()

    # 2) чанковать ли: длинное целиком обрывается на потолке ответа (промерено)
    nonempty = sum(1 for ln in text.splitlines() if ln.strip())
    do_chunk = args.chunk == "on" or (args.chunk == "auto" and nonempty > 60)
    key = load_key(args.key)

    if do_chunk:
        chunks = chunk_prose(text)
        print(f"=== ВЫБОР по {len(chunks)} чанкам (судья {args.model}); швы — заголовки/абзацы ===")
        print("(!) РАМКА: край чанка ПЕРЕ-ОБРАМЛЯЕТ пограничные T?/T — резано по естественным "
              "швам, но вердикт на стыке читай с этой поправкой.\n")
        for label, judg in choose_chunked(chunks, args.model, key, args.jobs):
            print(f"----- [{label}] -----")
            print(judg)
            print()
    else:
        print(f"=== ВЫБОР (судья {args.model}) ===")
        print(choose(text, args.model, key))
    return 0


if __name__ == "__main__":
    sys.exit(main())
