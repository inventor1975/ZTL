# Как воспроизвести сравнение с ASPIC+ (PyArg)

внешний рецензент ссылается на это сравнение как на «frozen comparison against
python-argumentation 2.0.2». До 2026-08-31 оно таким НЕ БЫЛО: venv с
PyArg стоял в скратчпаде сессии и исчез бы вместе с ней. Сторонний
человек не смог бы повторить прогон — а именно на воспроизводимость
опирается всё, что мы про это говорим наружу.

## Постановка

    python3 -m venv ~/venvs/aspic
    ~/venvs/aspic/bin/pip install -r aspic_requirements.txt

Пин там git-коммитом, не диапазоном версий:
`python-argumentation @ git+https://github.com/DaphneOdekerken/PyArg.git@f907bac`
(Odekerken/Bex/Prakken). Версия по метаданным — 2.0.2.

## Прогон

    ~/venvs/aspic/bin/python3 aspic_settles.py     # их stability против нашего settles
    ~/venvs/aspic/bin/python3 aspic_relevance.py   # их relevance против нашей ширины
    ~/venvs/aspic/bin/python3 aspic_settles2.py    # наш вопрос, посчитанный на ИХ машине

Прогнозы заморожены ДО первого запуска в `aspic_*_ПРОГНОЗ.md`,
результаты — в `aspic_*_РЕЗУЛЬТАТ.md`.

## Что должно выйти — MEASURED 2026-08-31, долговечный venv

`aspic_settles.py`:
  случай 1 (основание не проверено)      -> UNSTABLE
  случай 2 (оба исхода дают shutdown)    -> UNSTABLE
  случай 3 (у литерала нет опор)         -> STABLE-UNSATISFIABLE
Случаи 1 и 2 СОВПАЛИ. Это НЕ «их величина слабее»: причина в их же
исходнике — в `get_all_axiom_completions` будущее, где основание так и
не проверено, входит в перебор наравне с проверенными. Их вопрос — «может
ли вывод ещё измениться», наш — «стоит ли эта проверка того».

`aspic_relevance.py`:
  B (нужны ВМЕСТЕ a и b) и C (хватает любого) дают ОДИН И ТОТ ЖЕ
  relevance ['-a','-b','a','b'], а наша ширина различает: 2 против 1.
  Контроль в скрипте отсекает объяснение «дело в длине списка».
