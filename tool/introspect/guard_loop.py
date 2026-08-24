#!/usr/bin/env python3
"""Grounded-answer loop с ЖЁСТКИМ пределом переправок — БЕЗ КЛЮЧА.

Куратор 2026-08-24 (1363): «влупи жёстко, а то слабые ИИ зациклятся».
Предел ≤ MAX_REDOS вшит в КОД (range), не в дисциплину — даже слабая модель не
прокрутит цикл дольше.

Скелет keyless: сам НИЧЕГО не генерит и не судит (нет API-вызовов). Ему дают два
колбэка — generate() и judge() — которые может исполнять форк / SELF / чужая
модель. Так предел железный у ЛЮБОГО, кто строит поверх (включая чужой раннер).

Петля: generate -> judge (guard). GROUNDED/REPAIRED -> отдать заземлённое.
REFUSED (заземлить нечего) -> переделать. Не более MAX_REDOS переправок, потом
СТОП: честное «не установлено за N попыток», без бесконечного цикла.
"""
from __future__ import annotations
from typing import Callable

MAX_REDOS = 3  # ЖЁСТКИЙ предел переправок. Меняй здесь — но не выше по прихоти.

# judge() возвращает кортеж (verdict, grounded_answer, ledger):
#   verdict ∈ {"GROUNDED","REPAIRED","REFUSED"}
#   grounded_answer — что можно отдать (только обоснованное + «не установлено»)
#   ledger — список строк «утверждение — [T|F|Z] — почему»
Generate = Callable[[str, str, list], str]              # (source, question, history) -> answer
Judge = Callable[[str, str, str], tuple[str, str, list]]  # (source, question, answer) -> (verdict, grounded, ledger)


def guarded_answer(source: str, question: str,
                   generate: Generate, judge: Judge,
                   max_redos: int = MAX_REDOS) -> dict:
    """Сгенерить и заземлить ответ, не более max_redos переправок. Возвращает dict:
    {status, answer, attempts, ledger, history}.
      status: grounded | repaired | not_established_after_cap
    """
    if max_redos < 1:
        raise ValueError("max_redos must be >= 1")
    history: list[dict] = []
    last_grounded, last_ledger = "", []
    for attempt in range(1, max_redos + 1):        # ЖЁСТКО: не более max_redos итераций
        answer = generate(source, question, history)
        verdict, grounded, ledger = judge(source, question, answer)
        last_grounded, last_ledger = grounded, ledger
        if verdict in ("GROUNDED", "REPAIRED"):
            return {"status": verdict.lower(), "answer": grounded,
                    "attempts": attempt, "ledger": ledger, "history": history}
        # REFUSED — заземлить нечего, идём на переправку (если остались).
        history.append({"attempt": attempt, "answer": answer,
                        "verdict": verdict, "ledger": ledger})
    # предел выбран — стоп, честный отказ, НЕ крутим дальше
    return {"status": "not_established_after_cap", "attempts": max_redos,
            "answer": last_grounded or "Не установлено источником "
                      f"(не удалось заземлить за {max_redos} попыток).",
            "ledger": last_ledger, "history": history}


# --- самотест со СТАБАМИ (без модели): доказать, что предел железный ---
def _selftest() -> int:
    ok = True

    # A) модель отказывает 2 раза, на 3-й заземляет -> должен вернуть grounded на 3-й.
    seq = ["REFUSED", "REFUSED", "GROUNDED"]
    calls = {"n": 0}
    def gen(_s, _q, _h): calls["n"] += 1; return f"draft {calls['n']}"
    def judge_a(_s, _q, _a):
        v = seq[calls["n"] - 1]
        return v, ("ЗАЗЕМЛЁННЫЙ ответ" if v != "REFUSED" else ""), [f"claim — [{'T' if v != 'REFUSED' else 'Z'}]"]
    r = guarded_answer("src", "q", gen, judge_a, max_redos=3)
    ok &= (r["status"] == "grounded" and r["attempts"] == 3)
    print(" A: отказ×2 → заземлил на 3-й:", r["status"], r["attempts"], "OK" if ok else "FAIL")

    # B) модель ВСЕГДА отказывает -> должен упереться в предел (не зациклиться).
    calls2 = {"n": 0}
    def gen2(_s, _q, _h): calls2["n"] += 1; return "draft"
    def judge_b(_s, _q, _a): return "REFUSED", "", ["claim — [Z]"]
    r2 = guarded_answer("src", "q", gen2, judge_b, max_redos=3)
    okb = (r2["status"] == "not_established_after_cap" and calls2["n"] == 3)
    ok &= okb
    print(" B: вечный отказ → стоп на 3, вызовов:", calls2["n"], "OK" if okb else "FAIL")

    # C) предел уважается и на 1
    r3 = guarded_answer("src", "q", gen2, judge_b, max_redos=1)
    okc = (r3["attempts"] == 1)
    ok &= okc
    print(" C: max_redos=1 уважается:", r3["attempts"], "OK" if okc else "FAIL")

    print("guard_loop selftest:", "OK" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(_selftest())
