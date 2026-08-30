#!/usr/bin/env python3
# Copyright 2026 Vitaly Reznik
# SPDX-License-Identifier: Apache-2.0
"""Нарезка прозы по швам — общая утилита, к ЯРУСУ ЦЕННОСТИ отношения не имеет.

Вынесено из `zchoose.py` 2026-08-30, когда ярус соблазна закрывался и уезжал в
приватный репозиторий. Атом-стор и `guard` брали отсюда только `chunk_prose`;
унести её вместе с рубрикой значило бы сломать стор, которым пользуются каждый
день. Поэтому режем по живому шву: нарезка остаётся публичной, оценка уезжает.
"""
from __future__ import annotations


def chunk_prose(text: str, target_lines: int = 50) -> list[tuple[str, str]]:
    """Резать прозу по швам: копим абзацы до target_lines непустых строк, заголовок
    верхнего уровня (# …) открывает новый чанк. Возвращает [(метка-зачин, текст)]."""
    paras = [p for p in text.split("\n\n") if p.strip()]
    chunks: list[str] = []
    cur: list[str] = []
    cnt = 0
    for p in paras:
        stripped = p.lstrip()
        is_top = stripped.startswith("# ") or stripped.rstrip() == "#"
        if is_top and cur:
            chunks.append("\n\n".join(cur)); cur, cnt = [], 0
        cur.append(p); cnt += p.count("\n") + 1
        if cnt >= target_lines and not is_top:
            chunks.append("\n\n".join(cur)); cur, cnt = [], 0
    if cur:
        chunks.append("\n\n".join(cur))
    out = []
    for c in chunks:
        first = next((ln.strip() for ln in c.splitlines() if ln.strip()), "")
        out.append((first[:60], c))
    return out
