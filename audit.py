# -*- coding: utf-8 -*-
"""
Аудитор тождеств ZTL: брутфорс по всем распределениям значений.

Два вида проверок:
  * равенство двух формул (совпадение значений на всех распределениях);
  * общезначимость формулы (значение T на всех распределениях).
Плюс семантический modus ponens.

Каждый павший закон — не баг, а строка манифеста: цена принципа
«истина не в кредит». Список живых/павших печатается как MEASURED.
"""

from ztl import T, F, Z, VALUES, ev, atoms, all_envs, show

# --- каталог тождеств: (имя, формула слева, формула справа) ---
p, q, r = "p", "q", "r"

EQUALITIES = [
    ("двойное отрицание      ¬¬p = p",            ("not", ("not", p)), p),
    ("Де Морган 1            ¬(p∧q) = ¬p∨¬q",     ("not", ("and", p, q)), ("or", ("not", p), ("not", q))),
    ("Де Морган 2            ¬(p∨q) = ¬p∧¬q",     ("not", ("or", p, q)), ("and", ("not", p), ("not", q))),
    ("контрапозиция          p→q = ¬q→¬p",        ("imp", p, q), ("imp", ("not", q), ("not", p))),
    ("импликация через ∨     p→q = ¬p∨q",         ("imp", p, q), ("or", ("not", p), q)),
    ("⊕ дистрибутивной формой p⊕q = (p∧¬q)∨(¬p∧q)", ("xor", p, q), ("or", ("and", p, ("not", q)), ("and", ("not", p), q))),
    ("↔ дистрибутивной формой p↔q = (p∧q)∨(¬p∧¬q)", ("xnor", p, q), ("or", ("and", p, q), ("and", ("not", p), ("not", q)))),
    ("⊕ как отрицание ↔      p⊕q = ¬(p↔q)",       ("xor", p, q), ("not", ("xnor", p, q))),
    ("↔ через две импликации p↔q = (p→q)∧(q→p)",  ("xnor", p, q), ("and", ("imp", p, q), ("imp", q, p))),
    ("коммутативность ∧      p∧q = q∧p",          ("and", p, q), ("and", q, p)),
    ("коммутативность ∨      p∨q = q∨p",          ("or", p, q), ("or", q, p)),
    ("ассоциативность ∧      (p∧q)∧r = p∧(q∧r)",  ("and", ("and", p, q), r), ("and", p, ("and", q, r))),
    ("ассоциативность ∨      (p∨q)∨r = p∨(q∨r)",  ("or", ("or", p, q), r), ("or", p, ("or", q, r))),
    ("дистрибутивность ∧/∨   p∧(q∨r) = (p∧q)∨(p∧r)", ("and", p, ("or", q, r)), ("or", ("and", p, q), ("and", p, r))),
    ("дистрибутивность ∨/∧   p∨(q∧r) = (p∨q)∧(p∨r)", ("or", p, ("and", q, r)), ("and", ("or", p, q), ("or", p, r))),
    ("идемпотентность ∧      p∧p = p",            ("and", p, p), p),
    ("идемпотентность ∨      p∨p = p",            ("or", p, p), p),
    ("поглощение             p∧(p∨q) = p",        ("and", p, ("or", p, q)), p),
    ("нейтраль ∧             p∧T = p",            ("and", p, "T"), p),
    ("нейтраль ∨             p∨F = p",            ("or", p, "F"), p),
]

VALIDITIES = [
    ("исключённое третье     p∨¬p",               ("or", p, ("not", p))),
    ("непротиворечие         ¬(p∧¬p)",            ("not", ("and", p, ("not", p)))),
    ("рефлексивность →       p→p",                ("imp", p, p)),
    ("транзитивность →       ((p→q)∧(q→r))→(p→r)", ("imp", ("and", ("imp", p, q), ("imp", q, r)), ("imp", p, r))),
    ("закон Пирса            ((p→q)→p)→p",        ("imp", ("imp", ("imp", p, q), p), p)),
    ("утверждение консеквента q→(p→q)",           ("imp", q, ("imp", p, q))),
]


def check_equality(lhs, rhs):
    """Список распределений, на которых формулы расходятся."""
    names = atoms(lhs) | atoms(rhs)
    fails = []
    for env in all_envs(names):
        a, b = ev(lhs, env), ev(rhs, env)
        if a != b:
            fails.append((env, a, b))
    return fails


def check_validity(phi):
    """Список распределений, на которых формула не равна T."""
    fails = []
    for env in all_envs(atoms(phi)):
        v = ev(phi, env)
        if v != T:
            fails.append((env, v))
    return fails


def check_modus_ponens():
    """Семантический MP: всюду, где v(A)=T и v(A→B)=T, обязано v(B)=T.
    Проверяем на всех парах формул глубины <=1 над атомами p,q — включая
    случаи, где посылки содержат Z."""
    from itertools import product
    small = [p, q, ("not", p), ("not", q), ("and", p, q), ("or", p, q),
             ("imp", p, q), ("xor", p, q), ("xnor", p, q), "T", "F", "Z"]
    fails = []
    for A, B in product(small, repeat=2):
        names = atoms(A) | atoms(B)
        for env in all_envs(names):
            if ev(A, env) == T and ev(("imp", A, B), env) == T and ev(B, env) != T:
                fails.append((show(A), show(B), env))
    return fails


def check_eager_theorem():
    """Теорема жадности: ни одна СОСТАВНАЯ формула не принимает значение Z.
    Проверяем все формулы глубины 2 над p,q."""
    forms = [p, q, ("not", p)]
    depth2 = []
    for opn in ("and", "or", "imp", "xor", "xnor"):
        for a in forms:
            for b in forms:
                depth2.append((opn, a, b))
    depth2 += [("not", f) for f in depth2[:]]
    bad = []
    for phi in depth2:
        for env in all_envs(atoms(phi)):
            if ev(phi, env) == Z:
                bad.append((show(phi), env))
    return bad


def run_audit():
    print("=" * 72)
    print("АУДИТ ТОЖДЕСТВ ZTL (брутфорс по всем распределениям T/F/Z)")
    print("=" * 72)

    alive, dead = [], []
    for name, lhs, rhs in EQUALITIES:
        fails = check_equality(lhs, rhs)
        (alive if not fails else dead).append((name, fails))
    for name, phi in VALIDITIES:
        fails = check_validity(phi)
        (alive if not fails else dead).append((name + "  [общезначимость]", fails))

    print("\n-- ЖИВЫЕ ЗАКОНЫ --")
    for name, _ in alive:
        print("  ✓ " + name)

    print("\n-- ПАВШИЕ ЗАКОНЫ (цена принципа; первый контрпример) --")
    for name, fails in dead:
        env = fails[0][0]
        env_s = ", ".join(f"{k}={v}" for k, v in sorted(env.items()))
        got = fails[0][1:]
        print(f"  ✗ {name}   [{env_s} → {' vs '.join(got)}]")

    mp = check_modus_ponens()
    print("\n-- MODUS PONENS (семантический) --")
    if not mp:
        print("  ✓ держится: из v(A)=T и v(A→B)=T всюду следует v(B)=T")
    else:
        print(f"  ✗ падает, контрпримеров: {len(mp)}; первый: {mp[0]}")

    eager = check_eager_theorem()
    print("\n-- ТЕОРЕМА ЖАДНОСТИ --")
    if not eager:
        print("  ✓ подтверждена: составные формулы не принимают значение Z")
    else:
        print(f"  ✗ нарушена: {eager[0]}")

    print(f"\nИтого: живых {len(alive)}, павших {len(dead)}.")
    return alive, dead


if __name__ == "__main__":
    run_audit()
