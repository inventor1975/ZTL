#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""askztl — СКЛЕЙКА, а не прибор. Форк переводит, ЯДРО ZTL судит.

ПОЧЕМУ ЭТОТ ФАЙЛ ТАКОЙ КОРОТКИЙ. Тетрадь у нас ОДНА — студийная, и других мы
не делаем (слово куратора 2026-08-27). Студия — тонкая оболочка: внутри у неё
`_v2("zfl2").run(doc)`, то есть она зовёт ZTL напрямую как модуль и только
показывает ответ. Значит и нам ходить некуда: `zfl2` лежит рядом на диске.

ЧТО ЗДЕСЬ ЕСТЬ И ЧЕГО НЕТ.

Есть две команды и ничего больше: подготовить задачу форку, отдать вернувшуюся
таблицу ядру. Нет своей рубрики, нет своих меток, нет второго описания языка.

ПРОМПТ НЕ НАПИСАН РУКОЙ — ОН ПОРОЖДЁН ИЗ СПЕЦИФИКАЦИИ. `translator2.schema()`
вычитывает колонки, статусы, виды основания и операторы из `zfl2.COLUMNS` и
разборщиков; `translator2.vocabulary()` даёт слова интерфейса, чтобы модель не
выдумывала свои. В самом translator2 записано, почему так: «промпт, написанный
рукой, есть ВТОРОЕ ОПИСАНИЕ ЯЗЫКА». 2026-08-27 я написал такой рукой и дважды
на нём сломался — сперва основания прозой, потом формула у `refuted`. Правило
оба раза жило в ядре, а моя рука его не знала.

ИИ СТУДИИ НЕ ТРОГАЕМ. Переводит МОЙ форк — по слову куратора.

    ./askztl.py prepare <файл> [--lang ru]   задача форку: текст -> таблица
    ./askztl.py judge <rows.json>            ядро судит, печатает паспорт
    ./askztl.py selftest                     инварианты прогоном
"""
import argparse, json, pathlib, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))          # ZTL/tool — там zfl2 и translator2
import zfl2                                    # noqa: E402
import translator2                              # noqa: E402


def build_task(text: str, lang: str = "ru") -> str:
    """Задача форку. Всё, кроме одной обрамляющей фразы, взято ИЗ СПЕЦИФИКАЦИИ."""
    return (
        "Переведи текст ниже в документ ZFL2. Ты НЕ выносишь вердикт и НЕ "
        "оцениваешь текст — ты заполняешь клетки, судит потом ядро.\n\n"
        + translator2.schema(lang) + "\n\n"
        + translator2.vocabulary(lang) + "\n\n"
        "Верни ТОЛЬКО JSON документа, без пояснений.\n\nТекст:\n\n" + text)


def build_repair(doc: dict, issues: list) -> str:
    """Задача форку на ОДИН заход починки.

    Форма не выдумана: ровно так чинит `translator2.fill` — отдаёт модели
    МАШИНОЧИТАЕМЫЙ вывод валидатора и просит вернуть исправленный JSON. Один
    заход, а не цикл: у студии тоже один, и предел стоит в коде, а не в
    добросовестности.
    """
    return ("Этот документ ЗАБРАКОВАН ядром:\n\n"
            + json.dumps(issues, ensure_ascii=False, indent=1)
            + "\n\nВот он:\n\n" + json.dumps(doc, ensure_ascii=False, indent=1)
            + "\n\nВерни ИСПРАВЛЕННЫЙ JSON документа, один, без пояснений. "
              "Правь только то, на что указал валидатор.")


def judge(doc: dict) -> dict:
    """Ядро судит — той же строкой, какой зовёт его студия."""
    return zfl2.run(doc)


def render(res: dict) -> str:
    if not res.get("ok"):
        out = ["ДОКУМЕНТ НЕ ПРОШЁЛ — вердикта нет:"]
        for i in res.get("issues", []):
            out.append(f"  [{i.get('code')}] {i.get('where')}: {i.get('hint')}")
        return "\n".join(out)
    ap = res.get("applies", {})
    out = ["включились приборы: " + (", ".join(k for k, v in ap.items() if v) or "—")]
    rep = res.get("report", {}) or {}
    for name, items in rep.items():
        for it in items or []:
            comp = ", ".join(it.get("component", [])) if isinstance(it, dict) else str(it)
            kind = it.get("kind", "") if isinstance(it, dict) else ""
            detail = it.get("detail", "") if isinstance(it, dict) else ""
            out.append(f"  [{name}] {comp:22s} {kind:16s} {detail}")
    return "\n".join(out)


def _selftest() -> int:
    ok = fail = 0

    def check(name, cond):
        nonlocal ok, fail
        if cond: ok += 1; print(f"  OK  {name}")
        else:    fail += 1; print(f"  FAIL {name}")

    t = build_task("проба", "ru")
    # ПРОМПТ ИЗ СПЕЦИФИКАЦИИ, а не из моей головы: проверяем, что в нём есть то,
    # чего я руками не писал — колонки, о существовании которых я узнал из schema().
    check("промпт несёт колонку dimension", "dimension" in t)
    check("промпт несёт ground_kind", "ground_kind" in t)
    check("промпт несёт словарь интерфейса", "verified" in t and "проверено" in t)
    check("промпт не короче спецификации", len(t) > len(translator2.schema("ru")))

    doc = {"rows": [
        {"name": "p", "means": "вход непустой", "status": "verified", "ground": "by-assumption"},
        {"name": "q", "means": "индекс в границах", "status": "unverified"},
    ], "claim": "p & q"}
    r = judge(doc)
    check("годный документ проходит", r.get("ok") is True)

    bad = {"rows": [{"name": "p", "means": "x", "status": "T"}]}
    check("чужой статус отвергнут", judge(bad).get("ok") is False)

    liar = {"rows": [{"name": "L", "means": "это предложение ложно",
                      "status": "defined", "ground": "~(Tr(L))"}]}
    rl = judge(liar)
    det = json.dumps(rl.get("report", {}), ensure_ascii=False)
    check("лжец опознан как парадокс", rl.get("ok") and "PARADOX" in det)

    print(f"\n  итог: {ok} OK, {fail} FAIL")
    return 1 if fail else 0


def main() -> int:
    ap = argparse.ArgumentParser(description="склейка: форк переводит, ядро ZTL судит")
    sub = ap.add_subparsers(dest="cmd", required=True)
    pp = sub.add_parser("prepare"); pp.add_argument("target")
    pp.add_argument("--out", default=None); pp.add_argument("--lang", default="ru")
    pj = sub.add_parser("judge"); pj.add_argument("rows")
    pr = sub.add_parser("repair"); pr.add_argument("rows")
    pr.add_argument("--out", default=None)
    sub.add_parser("selftest")
    a = ap.parse_args()
    if a.cmd == "selftest":
        return _selftest()
    if a.cmd == "prepare":
        t = pathlib.Path(a.target)
        out = pathlib.Path(a.out) if a.out else t.with_suffix(t.suffix + ".task.md")
        out.write_text(build_task(t.read_text(encoding="utf-8"), a.lang), encoding="utf-8")
        print(f"задача -> {out}", file=sys.stderr)
        return 0
    doc = json.loads(pathlib.Path(a.rows).read_text(encoding="utf-8"))
    if a.cmd == "repair":
        issues = zfl2.validate(doc)
        if not any(i.get("level") == "error" for i in issues):
            print("чинить нечего — документ проходит", file=sys.stderr); return 0
        out = pathlib.Path(a.out) if a.out else pathlib.Path(a.rows).with_suffix(".repair.md")
        out.write_text(build_repair(doc, issues), encoding="utf-8")
        print(f"задача на починку -> {out}  ({len(issues)} замечаний)", file=sys.stderr)
        return 0
    print(render(judge(doc)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
