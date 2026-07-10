# -*- coding: utf-8 -*-
"""
Этап «киль»: отношение следования ZTL.

    Γ ⊨ φ  ⟺  всякое распределение значений, делающее ВСЕ посылки T,
              делает T и заключение (выделенное значение — только T).

Свойства, тарскианские ПО ПОСТРОЕНИЮ (доказательство — форма определения,
не перебор):
  * рефлексивность: φ ∈ Γ ⇒ Γ ⊨ φ;
  * монотонность: Γ ⊨ φ ⇒ Γ∪Δ ⊨ φ (посылок больше — распределений меньше);
  * cut: Γ ⊨ ψ и Γ,ψ ⊨ φ ⇒ Γ ⊨ φ.

Что промеряется перебором (MEASURED):
  1. Теорема дедукции: A ⊨ B против ⊨ A→B — стрелка строже следования.
  2. Батарея классических ПРАВИЛ как следований — что выжило.
  3. Паракомплектность: глатов нет (p,¬p недостижимы вместе), взрыв
     вакуумно валиден; ZTL паракомплетна, НЕ параконсистентна в ⊨-смысле.
"""

from ztl import T, F, Z, ev, atoms, all_envs, show


def entails(premises, conclusion):
    """None, если Γ ⊨ φ; иначе первый контрпример (распределение)."""
    names = atoms(conclusion, set())
    for prem in premises:
        atoms(prem, names)
    for env in all_envs(names):
        if all(ev(p, env) == T for p in premises) and ev(conclusion, env) != T:
            return env
    return None


def fmt_env(env):
    return ", ".join(f"{k}={v}" for k, v in sorted(env.items())) or "(пусто)"


p, q, r = "p", "q", "r"

RULES = [
    # (имя, посылки, заключение) — все классически валидны
    ("modus ponens         p, p→q ⊨ q",        [p, ("imp", p, q)], q),
    ("modus tollens        p→q, ¬q ⊨ ¬p",      [("imp", p, q), ("not", q)], ("not", p)),
    ("контрапозиция-правило p→q ⊨ ¬q→¬p",      [("imp", p, q)], ("imp", ("not", q), ("not", p))),
    ("дизъюнкт. силлогизм  p∨q, ¬p ⊨ q",       [("or", p, q), ("not", p)], q),
    ("∧-введение           p, q ⊨ p∧q",        [p, q], ("and", p, q)),
    ("∧-удаление           p∧q ⊨ p",           [("and", p, q)], p),
    ("∨-введение           p ⊨ p∨q",           [p], ("or", p, q)),
    ("¬¬-введение          p ⊨ ¬¬p",           [p], ("not", ("not", p))),
    ("¬¬-удаление          ¬¬p ⊨ p",           [("not", ("not", p))], p),
    ("транзитивность       p→q, q→r ⊨ p→r",    [("imp", p, q), ("imp", q, r)], ("imp", p, r)),
    ("монотонность-K       q ⊨ p→q",           [q], ("imp", p, q)),
    ("тавтология в заключ. p ⊨ q∨¬q",          [p], ("or", q, ("not", q))),
    ("взрыв                p, ¬p ⊨ q",         [p, ("not", p)], q),
    ("резолюция            p∨q, ¬p∨r ⊨ q∨r",   [("or", p, q), ("or", ("not", p), r)], ("or", q, r)),
]


def run_rules():
    print("-- БАТАРЕЯ КЛАССИЧЕСКИХ ПРАВИЛ КАК СЛЕДОВАНИЙ --")
    alive = dead = 0
    for name, prems, concl in RULES:
        cex = entails(prems, concl)
        if cex is None:
            print(f"  ✓ {name}")
            alive += 1
        else:
            print(f"  ✗ {name}   [контрпример: {fmt_env(cex)}]")
            dead += 1
    print(f"  Итого правил: живых {alive}, павших {dead}.")


def run_deduction_theorem():
    print("\n-- ТЕОРЕМА ДЕДУКЦИИ: A ⊨ B против ⊨ A→B --")
    pool = [p, ("not", p), ("and", p, q), ("or", p, q), ("imp", p, q), q]
    mismatch = []
    for A in pool:
        for B in pool:
            rule = entails([A], B) is None          # A ⊨ B
            law = entails([], ("imp", A, B)) is None  # ⊨ A→B
            if rule != law:
                mismatch.append((A, B, rule, law))
    # направление →-удаления: ⊨A→B ⇒ A⊨B (обязано держаться, MP семантический)
    broken_elim = [(A, B) for A, B, rule, law in mismatch if law and not rule]
    print(f"  Пар с расхождением: {len(mismatch)}; "
          f"из них ⊨A→B без A⊨B: {len(broken_elim)} (обязано быть 0)")
    for A, B, rule, law in mismatch[:4]:
        print(f"    {show(A)} ⊨ {show(B)}: {'да' if rule else 'нет'};   "
              f"⊨ {show(('imp', A, B))}: {'да' if law else 'нет'}")
    print("  Диагноз: стрелка СТРОЖЕ следования — введение → не работает,")
    print("  удаление → работает. Теорема дедукции: только слева направо.")


def run_paracomplete():
    print("\n-- ПАРАКОМПЛЕКТНОСТЬ, НЕ ПАРАКОНСИСТЕНТНОСТЬ --")
    both = [env for env in all_envs({"p"})
            if ev(p, env) == T and ev(("not", p), env) == T]
    print(f"  Распределений с v(p)=v(¬p)=T: {len(both)} — глатов нет,")
    print("  взрыв p,¬p ⊨ q валиден вакуумно (см. батарею).")
    lem = entails([], ("or", p, ("not", p)))
    print(f"  LEM ⊭ (контрпример {fmt_env(lem)}) — пробелы есть.")
    print("  Итог: ZTL паракомплетна (истина не всюду), параконсистентной")
    print("  в ⊨-смысле не является: противоречие невыразимо как пара истин.")


if __name__ == "__main__":
    print("=" * 72)
    print("КИЛЬ: ОТНОШЕНИЕ СЛЕДОВАНИЯ ZTL (выделенное значение {T})")
    print("=" * 72)
    run_rules()
    run_deduction_theorem()
    run_paracomplete()
