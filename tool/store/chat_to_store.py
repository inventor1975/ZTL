#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Чат Телеграма -> корпус CHAT атом-стора. Раз в сутки, БЕЗ форков и токенов.

ЗАМЫСЕЛ КУРАТОРА (2026-08-27): «можно не абзацами а сообщениями? Если да ложи
все разом… раз в 00:00». Единица — ОДНО СООБЩЕНИЕ, автор внутри текста.

ПОЧЕМУ АВТОР ВНУТРИ, А НЕ ТОЛЬКО В ИМЕНИ ФАЙЛА. Я возражал, что стор ответит
«сказано ли», а не «правда ли», и моё же вчерашнее враньё вернётся ко мне с
провенансом, выглядя заземлённым. Строку `[дата · чат · автор]` ставим впереди:
при поиске должно быть видно, чей голос, без открывания файла.

ПОПРАВКА 2026-08-30, И ОНА ВАЖНА. Прежняя редакция этой докстроки утверждала,
что МОИХ сообщений в корпусе нет вовсе («Логик 0»), потому что они живут в
`sent/`. **Это перестало быть правдой, а докстрока осталась.** Пересчёт по
самому корпусу, а не по замыслу:

    атомов в CHAT 3082 — Vitaly 1556, ЛОГИК 1101, ? 343, arcus18 48,
    the reviewer 24, IUSLererBot 6

То есть **больше трети корпуса — мой собственный голос**, и держится он там
под явной биркой «Логик — МОИ СЛОВА, не источник». Бирка спасает от того,
чтобы мой пересказ читался как свидетельство, но НЕ спасает от вытеснения:
чем больше моих реплик, тем реже ретрив достаёт его решения. Это уже
случалось (86% корпуса, см. память `project_chat_in_atomstore`).

Урок общий: докстрока — заявление о замысле, корпус — факт. Расходятся они
молча.

ПОРОГ СЛОВ = 1, НЕ 8. Умолчание в 8 слов выбросило бы ровно те реплики, ради
которых всё и делается: «Гони.», «Не строй тетрадь 2», «Учи ztl». Промерено
раньше на афоризмах: порог теряет КОРОТКОЕ, то есть часто лучшее.
"""
import collections, json, pathlib, subprocess, sys, tempfile

LOG   = pathlib.Path("/media/vitaly/SSD_1000GB/Projects/LogicBridge/tg_log.jsonl")
SENT  = pathlib.Path("/media/vitaly/SSD_1000GB/Projects/LogicBridge/sent")
STORE = pathlib.Path("/media/vitaly/SSD_1000GB/Projects/ztl-private/atomstore")
TOOL  = pathlib.Path(__file__).resolve().parent / "atomstore.py"
PY311 = "/home/vitaly/venvs/torch/bin/python3"
CHATS = {6783950513: "личный", -5101395964: "группа-the downstream conformance", -5319653310: "третий"}


def build(dst: pathlib.Path) -> dict[str, int]:
    buckets: dict[str, list[str]] = collections.defaultdict(list)
    for line in LOG.read_text(encoding="utf-8", errors="replace").splitlines():
        try:
            d = json.loads(line)
        except Exception:
            continue
        t = (d.get("text") or "").strip()
        if not t:
            continue
        who = d.get("from") or "?"
        when = (d.get("at") or "")[:16].replace("T", " ")
        chat = CHATS.get(d.get("chat_id"), str(d.get("chat_id")))
        buckets[who].append(f"[{when} · {chat} · {who}] {t}")
    # МОИ ОТВЕТЫ — по слову куратора 2026-08-27 («да твои тоже нужны»).
    # Возражение своё снимаю, но опасность остаётся и лечится ИМЕНЕМ: атом с
    # пометкой `Логик` — это то, что Я СКАЗАЛ, а не то, что установлено. Сегодня
    # я уверенно наговорил, что ZTL написан на питоне, что в сборке 34 сироты и
    # что постройка главы занимает миллисекунду. Всё три — ложь, и всё три
    # теперь в корпусе. Найдя такое, читать как показание, а не как источник.
    for f in sorted(SENT.glob("*.json")):
        try:
            d = json.loads(f.read_text(encoding="utf-8"))
        except Exception:
            continue
        t = (d.get("text") or "").strip()
        if not t:
            continue
        when = (d.get("sent_at") or "")[:16].replace("T", " ")
        chat = CHATS.get(d.get("chat_id"), str(d.get("chat_id")))
        # МАРКЕР НА КАЖДЫЙ АБЗАЦ, НЕ ТОЛЬКО НА ПЕРВЫЙ. `--direct` режет по
        # пустой строке, а мои ответы многоабзацные: при первой сборке маркер
        # достался 15% моих атомов (2356 из 15618), остальные легли безымянными
        # фрагментами — то есть защита, ради которой всё и делалось, не работала
        # на пяти шестых материала. Промерено, а не замечено на глаз.
        # ОДНО СООБЩЕНИЕ = ОДИН АТОМ, по слову куратора 2026-08-27: «пережми
        # своё в абзацы». Причина промерена: при разбиении по абзацам мои
        # реплики дали 15 606 атомов из 18 142 — 86% корпуса, — и решения
        # куратора (2206 атомов) в них ТОНУЛИ. Не подмена, а заглушение.
        # Схлопывая перевод строки, получаем ~1094 атома, соразмерно его 2206.
        one = " ".join(x.strip() for x in t.split("\n") if x.strip())
        buckets["Логик"].append(f"[{when} · {chat} · Логик — МОИ СЛОВА, не источник] {one}")

    for who, msgs in buckets.items():
        (dst / f"{who}.txt").write_text("\n\n".join(msgs), encoding="utf-8")
    return {w: len(m) for w, m in buckets.items()}


def main() -> int:
    if not LOG.exists():
        print(f"нет журнала: {LOG}"); return 1
    with tempfile.TemporaryDirectory() as tmp:
        src = pathlib.Path(tmp)
        counts = build(src)
        print("  собрано:", counts)
        for stage in (["atomize", "CHAT", str(src), "--direct", "--min-words", "1"],
                      ["index", "CHAT", "--multilingual"]):
            r = subprocess.run([PY311, str(TOOL), *stage, "--store", str(STORE)],
                               capture_output=True, text=True)
            print("  " + (r.stdout.strip().splitlines() or ["—"])[-1])
            if r.returncode:
                print("  СБОЙ:", r.stderr.strip()[-300:]); return r.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
