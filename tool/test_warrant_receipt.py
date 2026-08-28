# -*- coding: utf-8 -*-
"""D2 — квитанция вердикта: что она связывает и на чём валится.

Наряд внешнего рецензента §13 D2. Стенд проверяет ровно те свойства, ради которых
квитанция и заводится: она переживает передачу, и любая подмена её роняет.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json
import zfl2
import warrant_receipt as wr

СДЕЛКА = {"claim": "deal_ok", "rows": [
    {"name": "rc", "means": "реестр перечитывают",
     "status": "unverified", "ground": ""},
    {"name": "pf", "means": "не в залоге", "status": "verified",
     "ground": "vypiska", "expires_on": "rc"},
    {"name": "po", "means": "документы в порядке", "status": "verified",
     "ground": "pts"},
    {"name": "deal_ok", "means": "сделку можно закрывать",
     "status": "defined", "ground": "Tr(pf) & Tr(po)"}]}

ЛЖЕЦ = {"claim": "L", "rows": [
    {"name": "L", "means": "это предложение ложно",
     "status": "defined", "ground": "~Tr(L)"}]}


def _rec(doc, epoch="epoch-A"):
    return wr.receipt(zfl2.run(doc), doc, epoch)


if __name__ == "__main__":
    print("=" * 72)
    print("D2. КВИТАНЦИЯ ВЕРДИКТА — наименьшая привязка через передачу")
    print("=" * 72)
    fails = 0

    def check(имя, ок):
        global fails
        fails += (not ок)
        print(f"   {'FAIL' if not ок else 'OK  '} {имя}")

    print("\n### 1. Квитанция сверяется сама с собой")
    r0 = _rec(СДЕЛКА)
    check("нетронутая квитанция проходит сверку", wr.verify(r0))
    check("отпечаток есть и он шестидесятичетырёхзначный",
          len(r0["digest"]) == 64)

    print("\n### 2. ЛЮБАЯ подмена роняет сверку — все пять полей")
    for поле, правка in (
            ("claim", lambda d: d.update(claim="что-то другое")),
            ("holding", lambda d: d["holding"].update(призрак="Z")),
            ("grounds", lambda d: d["grounds"].update(
                pf={"status": "verified", "ground": "ПОДДЕЛКА"})),
            ("verdict", lambda d: d["verdict"].update(value="F")),
            ("epoch", lambda d: d.update(epoch="epoch-Z")),
            ("expiry", lambda d: d["expiry"].clear())):
        порча = json.loads(json.dumps(r0))
        правка(порча)
        check(f"подмена поля {поле} валит сверку", not wr.verify(порча))

    print("\n### 3. Эпоха входит в отпечаток — переиспользовать нельзя молча")
    rA, rB = _rec(СДЕЛКА, "epoch-A"), _rec(СДЕЛКА, "epoch-B")
    check("одна разметка в разных эпохах — РАЗНЫЕ отпечатки",
          rA["digest"] != rB["digest"])

    print("\n### 4. Погашаемость едет вместе с вердиктом")
    rl = _rec(ЛЖЕЦ)
    check("лжец несёт UNREDEEMABLE", rl["verdict"]["credit"] == "UNREDEEMABLE")
    check("и называет имя", rl["verdict"]["unredeemable"] == ["L"])
    check("сделка несёт REDEEMABLE", r0["verdict"]["credit"] == "REDEEMABLE")

    print("\n### 5. События истечения едут вместе с основанием")
    check("основание pf помечено событием rc", r0["expiry"] == {"pf": "rc"})

    print("\n### 6. Одинаковый смысл — одинаковый отпечаток (канонизация)")
    переставлено = {"rows": list(reversed(СДЕЛКА["rows"])),
                    "claim": СДЕЛКА["claim"]}
    check("порядок строк не меняет отпечаток",
          _rec(переставлено)["digest"] == r0["digest"])

    print("\n### 6б. ЛЖИВАЯ КВИТАНЦИЯ — и чем она ловится")
    # Найдено 2026-08-28 прогоном, не рассуждением (слово куратора: ZTL не
    # интуитивен, проверять судьёй). Отпечаток ловит ПОДМЕНУ и не ловит ЛОЖЬ
    # ПРИ ИЗГОТОВЛЕНИИ: документ с выдуманными основаниями даёт квитанцию,
    # которая сверяется чисто и несёт T EARNED hereditary.
    ЛОЖЬ = {"claim": "deal_ok", "rows": [
        {"name": "pf", "means": "не в залоге", "status": "verified",
         "ground": "ЧТО-УГОДНО"},
        {"name": "po", "means": "документы", "status": "verified",
         "ground": "ТОЖЕ-ЧТО-УГОДНО"},
        {"name": "deal_ok", "means": "можно закрывать", "status": "defined",
         "ground": "Tr(pf) & Tr(po)"}]}
    ЧЕСТЬ = {"claim": "deal_ok", "rows": [
        {"name": "pf", "means": "не в залоге", "status": "verified",
         "ground": "vypiska"},
        {"name": "po", "means": "документы", "status": "verified",
         "ground": "pts"},
        {"name": "deal_ok", "means": "можно закрывать", "status": "defined",
         "ground": "Tr(pf) & Tr(po)"}]}
    РЕЕСТР = {"vypiska", "pts"}

    голая = wr.receipt(zfl2.run(ЛОЖЬ), ЛОЖЬ, "epoch-A")
    check("БЕЗ реестра лживая квитанция сверяется — дыра реальна",
          wr.verify(голая) and голая["verdict"]["disposition"] == "EARNED")
    подреестром = wr.receipt(zfl2.run(ЛОЖЬ, ground_registry=РЕЕСТР), ЛОЖЬ,
                             "epoch-A", ground_registry=РЕЕСТР)
    check("ПОД реестром та же ложь падает в OPEN",
          подреестром["verdict"]["disposition"] == "OPEN")
    честная = wr.receipt(zfl2.run(ЧЕСТЬ, ground_registry=РЕЕСТР), ЧЕСТЬ,
                         "epoch-A", ground_registry=РЕЕСТР)
    check("честный документ под тем же реестром зарабатывает как прежде",
          честная["verdict"]["disposition"] == "EARNED")
    check("квитанция БЕЗ реестра отличима от выписанной ПОД реестром",
          голая["registry"] is None and честная["registry"] is not None
          and голая["digest"] != честная["digest"])

    print("\n### 6в. ПОТОМКИ: отзыв предка роняет потомка")
    # Вектор D3 №12 из наряда внешнего рецензента — «чистый на вид потомок с негодным
    # предком». D1 показал, что MAM его выразить не может: связи между
    # объектами памяти там нет вовсе. Здесь она есть, и проверка ТРАНЗИТИВНА:
    # одноуровневая внука не ловит (промерено 2026-08-28, первая редакция).
    Р = {"vypiska", "pts", "akt"}

    def кв(doc, anc=None, reg=Р):
        return wr.receipt(zfl2.run(doc, ground_registry=reg), doc, "epoch-A",
                          ground_registry=reg, derived_from=anc)

    ДЕД = {"claim": "pf", "rows": [
        {"name": "pf", "means": "не в залоге", "status": "verified",
         "ground": "vypiska"}]}
    дед = кв(ДЕД)
    отец = кв({"claim": "deal_ok", "rows": [
        {"name": "pf", "means": "не в залоге", "status": "verified",
         "ground": "vypiska"},
        {"name": "po", "means": "акт", "status": "verified", "ground": "akt"},
        {"name": "deal_ok", "means": "сделку можно", "status": "defined",
         "ground": "Tr(pf) & Tr(po)"}]}, {"дед": дед})
    внук = кв({"claim": "pay", "rows": [
        {"name": "deal_ok", "means": "сделка закрыта", "status": "verified",
         "ground": "akt"},
        {"name": "pay", "means": "платить можно", "status": "defined",
         "ground": "Tr(deal_ok)"}]}, {"отец": отец})
    все = {"дед": дед, "отец": отец, "внук": внук}
    check("целая цепь стоит", wr.verify_descent(внук, все)["verdict"] == "STANDS")

    дед2 = кв(ДЕД, reg={"pts", "akt"})       # у деда отняли основание
    все2 = dict(все, дед=дед2)
    r = wr.verify_descent(внук, все2)
    check("отзыв у ДЕДА роняет ВНУКА через отца", r["verdict"] == "FALLEN")
    check("и называет причину до корня",
          r["broken"][0]["reason"] == "ANCESTOR_CHAIN_BROKEN"
          and r["broken"][0]["under"][0]["reason"] == "ANCESTOR_FELL")

    чужой = кв({"claim": "pf", "rows": [
        {"name": "pf", "means": "другое", "status": "verified",
         "ground": "akt"}]})
    r2 = wr.verify_descent(отец, dict(все, дед=чужой))
    check("ПОДМЕНА предка отличена от его ПАДЕНИЯ",
          r2["broken"][0]["reason"] == "ANCESTOR_SUBSTITUTED")
    check("пропавший предок — отдельная причина",
          wr.verify_descent(отец, {})["broken"][0]["reason"] == "ANCESTOR_MISSING")

    петля = dict(внук)
    петля["derived_from"] = {"сам": {"digest": внук["digest"],
                                     "disposition": "EARNED"}}
    r3 = wr.verify_descent(петля, {"сам": петля})
    check("петля в цепи даёт ОТКАЗ, а не переполнение стека",
          r3["verdict"] == "FALLEN")

    print("\n### 7. ЧЕГО ЭТО НЕ УСТАНАВЛИВАЕТ")
    print("   Квитанция не подписывает (ключи — дело потребителя), не")
    print("   ловит ЛОЖЬ ПРИ ИЗГОТОВЛЕНИИ сама по себе — для этого нужен")
    print("   реестр оснований, и без него она честно говорит registry=None;")
    print("   устанавливает истину источника (только что форсит разметка) и")
    print("   не переносит полномочие: предъявитель получает право ПРОВЕРИТЬ,")
    print("   а не право действовать.")

    if fails:
        raise SystemExit(f"D2 RED: {fails} расхождений")
    print("\n" + "=" * 72)
    print("WARRANT RECEIPT GREEN — вердикт переживает передачу и")
    print("проверяется на той стороне, а не пересказывается.")
