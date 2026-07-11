# ZTL — Zero-Trust Logic / логика нулевого доверия

Логика с принципом **«истина не выдаётся в кредит»**: вердикты всегда
двузначны (T/F), а третий символ Z (zero-trust, «истина не заслужена») —
метка непроверенного входа: она никогда не порождает T, если T не
вынуждена при любом классическом прочтении. Default deny, перенесённый
из безопасности в таблицы истинности; трёхсимвольные таблицы — рабочий
калькулятор этой политики (онтологический паспорт — препринт, §10).

Запуск (Python 3, без зависимостей):

```
python3 ztl.py         # таблицы + проверка опорных аксиом
python3 audit.py       # аудит тождеств: живые/павшие законы, MP, жадность
python3 entailment.py  # следование ⊨: правила против законов, теорема дедукции
python3 tableau.py     # исчисление: знаковые таблó + сверка с ⊨ (2462 пары)
python3 quantifiers.py # кванторы: строгие свидетели, UI/EG-асимметрия
python3 tableau_fo.py  # кванторные таблó + сверка с перебором (28 пар)
python3 paradoxes.py   # лжец, карусель, мститель
python3 fixedpoint.py  # карантин как неподвижная точка, два регистра
cd lean && lake build  # машинная проверка ядра: ноль аксиом
```

Спецификация и все проектные решения — в `SPEC.md`; рабочий черновик
препринта — `paper/ZTL-draft.md`. Родословная честная: функционально
ZTL — фрагмент внешнего слоя логики Бочвара B3 (1938), ядро {¬,∧,∨} —
в классе 8Kb*; своё — импликативный этаж (7 клеток дельты, вне условий
стандартности Россера–Тюркетта), порождающий принцип и двухрегистровая
теорема о карантине.

Проект возник 2026-07-10 из разбора парадокса лжеца; предшественник по
верфи — VSPL (временная параконсистентная логика потоков).

*AI-участие: проектировалось и написано в диалоге куратора (Виталий
Резник) с Claude (Anthropic); решения по развилкам — куратора.*

---

## English summary

**ZTL — Zero-Trust Logic.** A two-valued logic over marked (unverified)
inputs with one generating principle: *truth is never granted on credit* —
a connective returns T only if T is forced under every classical reading
of the unverified. Verdicts are always classical (T/F); the third symbol
Z is an input mark, not a truth value. Default deny, ported from security
into truth tables.

Highlights: machine-checked core in Lean 4 with **zero axioms** (no
propext, no Quot.sound, no choice), including a certified tableau engine
(soundness + completeness) and a native-rules engine proven equivalent;
measured bridges to six independent engineering traditions — IEEE NaN,
SQL NULL, taint tracking/IFC, abstract interpretation, imprecise
probabilities, provenance semirings; quarantine treatment of the liar,
Curry, Yablo and Russell (containment instead of explosion); verdicts
carry a stability warranty (local answer + supervaluational guarantee).

Run `python3 run_all.py` for the full regression (19 stands + Lean build).
License: MIT. Working draft of the preprint: `paper/ZTL-draft.md` (RU).
