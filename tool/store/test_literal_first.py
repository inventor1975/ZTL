# -*- coding: utf-8 -*-
"""Стенд на буквальный проход поиска (заведён 2026-08-30).

ПОВОД. Куратор искал свой афоризм по точной подстроке «но разрешает их сей
плут» — стор не выдал его даже в пятёрке, хотя текст лежит в корпусе. Причина
промерена: embedding отвечает на «похоже по мысли», а человек ищет «где
встречается вот это».

Стенд проверяет не только что находит, но и ЧТО НЕ ЛОМАЕТ: слишком короткий
запрос буквальным считаться не должен, иначе «не» совпадёт со всем подряд.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from atomstore import _literal_first, LITERAL_MIN, LITERAL_SCORE  # noqa: E402

ok = fail = 0


def check(имя, cond, why=""):
    global ok, fail
    if cond:
        ok += 1; print(f"  OK   {имя}")
    else:
        fail += 1; print(f"  FAIL {имя}  {why}")


A = {"atom": "Быть может, гений — парадоксам друг,\n но разрешает их сей плут!"}
B = {"atom": "Совесть — стоматолог души."}
C = {"atom": "Дать по шее тоже нужно, но не по принципу."}
ATOMS = [B, C, A]
SEM = [(0.9, B), (0.5, C), (-2.7, A)]      # как выдал бы один embedding

print("СТЕНД: буквальное совпадение идёт вперёд смыслового")

r = _literal_first("но разрешает их сей плут", ATOMS, SEM, 3)
check("точная подстрока выходит ПЕРВОЙ", r and r[0][1] is A, r[:1])
check("и помечена как буквальная, а не косинусом",
      r and r[0][0] == LITERAL_SCORE, r[0][0] if r else None)

check("перенос строки в источнике не мешает",
      _literal_first("друг, но разрешает", ATOMS, SEM, 3)[0][1] is A)
check("регистр не мешает",
      _literal_first("НО РАЗРЕШАЕТ ИХ СЕЙ ПЛУТ", ATOMS, SEM, 3)[0][1] is A)

# --- ЧТО НЕ ДОЛЖНО ЛОМАТЬСЯ
sem_only = _literal_first("что такое совесть на самом деле", ATOMS, SEM, 3)
check("без буквального совпадения выдача СМЫСЛОВАЯ, как была",
      [a for _, a in sem_only] == [a for _, a in SEM], sem_only)

check("СЛИШКОМ КОРОТКИЙ запрос буквальным не считается",
      _literal_first("но", ATOMS, SEM, 3)[0][1] is B,
      "иначе «но» совпадёт со всем подряд")
check(f"порог назван числом, а не на глаз (LITERAL_MIN={LITERAL_MIN})",
      isinstance(LITERAL_MIN, int) and LITERAL_MIN >= 4)

# --- ФАЛЬСИФИКАТОР: буквальное не должно ВЫТЕСНЯТЬ смысловое сверх k
r2 = _literal_first("но разрешает их сей плут", ATOMS, SEM, 3)
check("смысловые не выброшены, а сдвинуты ниже",
      len(r2) == 3 and B in [a for _, a in r2] and C in [a for _, a in r2], r2)
check("дублей нет: найденное буквально не повторяется смысловым",
      len({id(a) for _, a in r2}) == 3)

# --- k соблюдается
check("k соблюдается", len(_literal_first("но разрешает их сей плут", ATOMS, SEM, 1)) == 1)

print(f"\n{ok} OK, {fail} FAIL")
print("LITERAL-FIRST GREEN" if not fail else "LITERAL-FIRST RED")
sys.exit(1 if fail else 0)
