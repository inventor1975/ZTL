#!/usr/bin/env python3
"""Предсказать — потом посмотреть. Прибор против собственной уверенности.

Замысел куратора 2026-08-25: «ты же можешь предсказывать себе, что должен выдать
стор. И если нестыковка — проверять, кто врёт?»

Зачем именно так. Просто заглянуть в стор — значит увидеть верное и спокойно с ним
согласиться; ошибка при этом ПРОХОДИТ НЕЗАМЕЧЕННОЙ, потому что я не заметил, что
собирался сказать другое. Если же сначала записать предсказание, а потом смотреть,
расхождение становится ВИДИМЫМ СОБЫТИЕМ. И оно двустороннее:

    вру я           — память сползла, стор прав. Это надо знать про себя.
    врёт стор       — атомы устарели после правки источника, промах ретрива,
                      кривое извлечение. Это надо чинить в сторе.
    врёт ИСТОЧНИК   — самое ценное: документ противоречит другому документу или
                      сам себе (так нашлись две ошибки в книге 2026-08-25).

Считает и накапливает: сколько раз я угадал, сколько сполз, сколько раз виноват
прибор. Число моих промахов — не позор, а ЕДИНСТВЕННЫЙ способ узнать, где я
ненадёжен: до сих пор такого числа не было вовсе.
"""
from __future__ import annotations
import argparse
import json
import pathlib
import re
import subprocess
import sys
import tempfile
import time

HERE = pathlib.Path(__file__).resolve().parent
LOG_NAME = "predictions.jsonl"
VERDICTS = ("match", "my-drift", "store-wrong", "source-wrong", "unclear")


def ask(question: str, prediction: str, corpora: list[str], store: pathlib.Path,
        k: int = 6, log: pathlib.Path = None, question_alt: str = None) -> dict:
    """Записать предсказание, СПРОСИТЬ стор, показать рядом. Вердикт ставит человек
    или ассистент отдельной командой — прибор его НЕ угадывает за них."""
    # СПРАШИВАТЬ НА ОБОИХ ЯЗЫКАХ. Модель многоязычная, но РОДНОЙ язык ранжируется
    # выше: русский вопрос по английскому корпусу не поднял нужный атом вовсе, а
    # тот же вопрос по-английски поставил его ПЕРВЫМ (0.611). МЕРЕНО 2026-08-25 на
    # факте «609 ответов, ноль расхождений». Перевод — моя работа, не прибора.
    hits = []
    for q in [question] + ([question_alt] if question_alt else []):
        res = subprocess.run(
            [sys.executable, str(HERE / "atomstore.py"), "query", *corpora,
             "--question", q, "--answer", "x", "--store", str(store),
             "--out", str(pathlib.Path(tempfile.mkdtemp(prefix="predict-"))),
             "-k", str(k), "--gpu", "--multilingual"],
            capture_output=True, text=True)
        # ЖАЛОБЫ ПРИБОРА НЕ ГЛОТАТЬ. Прежде stderr уходил в никуда: «нет индекса»
        # и «индекс рассинхрон» читались как «стор промолчал», и я ставил себе
        # my-drift за ЧУЖУЮ поломку. Прибор, измеряющий мою надёжность, не должен
        # ошибаться в мою невыгоду молча. Найдено аудитом 2026-08-25.
        if res.returncode != 0 or res.stderr.strip():
            for line in res.stderr.strip().splitlines()[:4]:
                print(f"  ЖАЛОБА ПРИБОРА: {line}", file=sys.stderr)
        out = res.stdout
        for l in out.splitlines():
            l = l.strip()
            # «[0.» теряло совпадение 1.000 — самый релевантный атом до сравнения
            # не доходил. Берём любую строку вида «[<число>] …».
            if re.match(r"^\[\d", l) and l not in hits:
                hits.append(l)
    hits.sort(key=lambda h: -float(h[1:h.index("]")]))
    rec = {"id": f"p{int(time.time())}", "question": question,
           "prediction": prediction, "hits": hits, "verdict": None, "note": None}
    log = log or (HERE / LOG_NAME)
    with log.open("a", encoding="utf-8") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    print(f"\nВОПРОС: {question}")
    print(f"МОЁ ПРЕДСКАЗАНИЕ (записано ДО просмотра):\n    {prediction}\n")
    print("ЧТО ГОВОРИТ СТОР:")
    for h in hits:
        print("    " + h)
    print(f"\nid={rec['id']} — вердикт ставить командой:")
    print(f"    predict.py verdict {rec['id']} --verdict {{{'|'.join(VERDICTS)}}} --note '...'")
    return rec


def verdict(pid: str, v: str, note: str, log: pathlib.Path = None) -> None:
    log = log or (HERE / LOG_NAME)
    lines = log.read_text(encoding="utf-8").splitlines()
    hit = False
    for i, l in enumerate(lines):
        r = json.loads(l)
        if r["id"] == pid:
            r["verdict"], r["note"] = v, note
            lines[i] = json.dumps(r, ensure_ascii=False)
            hit = True
    if not hit:
        print(f"нет такого id: {pid}", file=sys.stderr); return
    log.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{pid}: вердикт {v}")


def stats(log: pathlib.Path = None) -> None:
    log = log or (HERE / LOG_NAME)
    if not log.exists():
        print("предсказаний пока нет"); return
    rows = [json.loads(l) for l in log.read_text(encoding="utf-8").splitlines() if l.strip()]
    judged = [r for r in rows if r["verdict"]]
    by: dict = {}
    for r in judged:
        by[r["verdict"]] = by.get(r["verdict"], 0) + 1
    print(f"предсказаний: {len(rows)}, с вердиктом: {len(judged)}")
    for v in VERDICTS:
        if by.get(v):
            print(f"    {v:14} {by[v]}")
    if judged:
        drift = by.get("my-drift", 0)
        print(f"\nмоя доля сползаний: {drift}/{len(judged)} = {100*drift/len(judged):.0f}%")
        print("(число маленькой выборки — НЕ выдавать за измеренную надёжность)")


def main() -> int:
    ap = argparse.ArgumentParser(description="Предсказать — потом посмотреть")
    sub = ap.add_subparsers(dest="cmd", required=True)
    pa = sub.add_parser("ask")
    pa.add_argument("--question", required=True)
    pa.add_argument("--predict", required=True, help="что, по-твоему, скажет источник")
    pa.add_argument("--question-alt", default=None,
                    help="тот же вопрос на другом языке — против перекоса ранга по языку")
    pa.add_argument("--corpora", nargs="+", required=True)
    pa.add_argument("--store", default="atomstore"); pa.add_argument("-k", type=int, default=6)
    pv = sub.add_parser("verdict")
    pv.add_argument("id"); pv.add_argument("--verdict", required=True, choices=VERDICTS)
    pv.add_argument("--note", default="")
    sub.add_parser("stats")
    a = ap.parse_args()
    if a.cmd == "ask":
        ask(a.question, a.predict, a.corpora, pathlib.Path(a.store), k=a.k,
            question_alt=a.question_alt)
    elif a.cmd == "verdict":
        verdict(a.id, a.verdict, a.note)
    else:
        stats()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
