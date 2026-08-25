#!/usr/bin/env python3
"""Узкий мост: граница допуска ПЕРЕД приёмом посылки в zfl2. Ядро не тронуто.

Замысел. zfl2 берёт документ из строк; строка со `status: verified` — это
заявка на КРЕДИТ: «считай установленным». Откуда установлено, zfl2 не спрашивает
и спрашивать не должен — это не его вопрос. Его вопрос — что СЛЕДУЕТ.

Потому граница ставится ДО входа, а не внутри: строка, чьё основание пришло из
внешнего источника, входит как `verified` только с распиской допуска. Без
расписки она не отвергается с грохотом, а ПОНИЖАЕТСЯ до `unverified` — родного
значения zfl2 для «не установлено», того самого дефолта зеро-траста. Логика
дальше работает как всегда: кредита нет, следствия из него не выводится.

Инвариант G1 внешнего рецензента: внешняя посылка не входит в ядро следствия без объекта
допуска. Здесь он стоит МЕХАНИЧЕСКИ, а не как договорённость.

И ПОНИЖЕНИЕ НИКОГДА НЕ МОЛЧИТ. Тихо ослабить документ — то же самое зло, что
тихо его усилить: пользователь должен увидеть, ЧТО было понижено и почему.
Потому gate возвращает не только документ, но и список понижений с причинами.
"""
from __future__ import annotations
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from admission import admit, verify_certificate  # noqa: E402

# СЛОВАРЬ zfl2, взятый из кода, а не выдуманный (промерено 2026-08-25: сперва я
# написал ворота под изобретённые значения вроде "source", и они не совпали бы
# НИ С ЧЕМ, что zfl2 принимает — то есть ворота молча пропускали бы всё).
#   ground_kind: document | act | certificate | row
#   dimension:   evidence (подпирает) | authority (разрешает)
# Внешние — document/act/certificate: их приносит чужая сторона. `row` внутренняя
# ссылка на другую строку, своих ворот не требует (её строка их уже прошла).
SOURCE_KINDS = {"document", "act", "certificate"}


def _is_source_backed(row: dict) -> bool:
    kind = (row.get("ground_kind") or "").strip().lower()
    return kind in SOURCE_KINDS


def _is_authority_row(row: dict) -> bool:
    """Строка по оси ПРАВОМОЧИЯ, а не подпорки.

    У zfl2 эта ось СВОЯ, встроенная: evidence = подпирает, authority = разрешает.
    Она совпадает с G3 внешнего рецензента («поддержка источника сама по себе не делает
    источник правомочным»), и потому сертификат заземления — доказательство
    ПОДДЕРЖКИ — правомочия не выдаёт НИКОГДА. Такую строку ворота не пропускают
    даже с безупречной распиской: расписка отвечает не на тот вопрос."""
    return (row.get("dimension") or "").strip().lower() == "authority"


def gate_document(doc: dict, receipts: dict, purpose: str, epoch: str,
                  eligible: dict) -> tuple[dict, list]:
    """Пропустить документ zfl2 через границу допуска.

    receipts: {имя_строки: (GroundingCertificate, заявленный_digest)} — расписки,
    добытые путём query→guard→build_certificate.

    Возвращает (документ_после_ворот, понижения). Документ — КОПИЯ: исходный не
    правим, чтобы вызывающий мог показать оба и сравнить."""
    out = dict(doc)
    out["rows"] = []
    demotions = []
    for row in (doc.get("rows") or []):
        r = dict(row)
        name = (r.get("name") or "").strip()
        status = (r.get("status") or "").strip().lower()
        if status == "verified" and _is_source_backed(r):
            why = None
            got = receipts.get(name)
            if _is_authority_row(r):
                # G3: сертификат заземления — про ПОДДЕРЖКУ. Правомочие он не
                # устанавливает даже будучи безупречным. Ось authority у zfl2
                # своя, и допуск по поддержке её не закрывает.
                why = ("ось ПРАВОМОЧИЯ (authority): сертификат заземления "
                       "доказывает поддержку источника, а не право решать — "
                       "это отдельные ворота, здесь их нет")
            elif not got:
                why = "нет расписки допуска: внешний источник, а допуск не выдан"
            else:
                cert, claimed = got
                if not verify_certificate(cert, claimed):
                    why = ("расписка не сходится: пересчитанный digest ≠ "
                           "заявленному (подмена байтов источника или посылки)")
                else:
                    d = admit(cert, purpose, epoch, eligible)
                    if not d.admitted:
                        why = d.reason
            if why:
                r["status"] = "unverified"      # родной зеро-траст zfl2
                r["_demoted_from"] = "verified"
                r["_demotion_reason"] = why
                demotions.append({"row": name, "reason": why})
        out["rows"].append(r)
    return out, demotions


def run_gated(doc: dict, receipts: dict, purpose: str, epoch: str,
              eligible: dict) -> dict:
    """gate → zfl2.run. Отчёт несёт понижения РЯДОМ с выводом логики.

    Ключевое: zfl2 вызывается как есть, немодифицированный. Граница живёт
    снаружи и отдаёт ему уже типизированные посылки."""
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
    import zfl2                                     # noqa: E402  (ядро как есть)
    gated, demotions = gate_document(doc, receipts, purpose, epoch, eligible)
    report = zfl2.run(gated)
    report["admission"] = {
        "purpose": purpose, "epoch": epoch,
        "demoted": demotions,
        "note": ("Понижённые строки вошли как unverified: источник их не"
                 " подтвердил под этой целью и эпохой. Логика ниже считала"
                 " БЕЗ них как без установленных."),
    }
    return report
