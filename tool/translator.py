# -*- coding: utf-8 -*-
"""
ZTLStudio: the translator. The ONLY component allowed to hallucinate —
which is why it never judges: it negotiates understanding in Russian,
then emits ZFL, and repairs it against the validator's machine-readable
errors. The human signs off on the meaning; the deterministic
back-reading (zfl.py) audits the emission; the core judges.

Groq API, same conventions as the curator's other tools (UA header —
Cloudflare 1010; GROQ_API_KEY from the environment).
"""

import json
import os
import urllib.request

API = "https://api.groq.com/openai/v1/chat/completions"
MODEL = os.environ.get("ZTL_GROQ_MODEL", "llama-3.3-70b-versatile")
KEY_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        ".groq_key")


def get_key():
    """Env first; else the local untracked key file (the repo is public —
    the key must never live in code)."""
    key = os.environ.get("GROQ_API_KEY")
    if key:
        return key.strip()
    if os.path.exists(KEY_FILE):
        with open(KEY_FILE) as f:
            return f.read().strip()
    return None

ZFL_SPEC = """ZFL — формальный язык для ядра ZTL. Строго JSON:
{"genre": "statement"|"system",
 "atoms": {"имя": {"status": "T"|"F"|"Z", "note": "пояснение"}},
 "assert": "формула",                  // только в genre=statement
 "sentences": {"имя": "формула"},      // только в genre=system
 "ask": ["verdict","warranty","passport","stipulations"]}
Формулы: not(x), and(x,y), or(x,y), imp(x,y), xor(x,y), xnor(x,y),
константы T и F, имена атомов; в genre=system ссылки на предложения
ТОЛЬКО через Tr(имя), голые атомы в формулах system запрещены.
status: T = проверено-истина, F = проверено-ложь, Z = НЕ проверено.
statement = вопрос о вердикте высказывания над (не)проверенными атомами.
system = самореферентная система (парадоксы: предложения о истинности
друг друга и себя)."""

FEWSHOT = """Примеры.
1) «Лжец: это предложение ложно» →
{"genre":"system","sentences":{"L":"not(Tr(L))"},
 "ask":["passport"]}
2) «Крокодил вернёт ребёнка тогда и только тогда, когда мать угадает его
действие; мать говорит: не вернёшь» →
{"genre":"system","sentences":{"R":"Tr(M)","M":"not(Tr(R))"},
 "ask":["passport","stipulations"]}
3) «Датчик (не поверен) показывает перегрев; если перегрев, защита
сработает. Сработает ли защита?» →
{"genre":"statement",
 "atoms":{"overheat":{"status":"Z","note":"датчик не поверен"},
          "shutdown":{"status":"Z","note":"следствие"}},
 "assert":"imp(overheat, shutdown)","ask":["verdict","warranty"]}"""

UNDERSTAND_SYS = """Ты — переводчик смыслов для логической студии ZTL
(двузначные вердикты + метка Z «не проверено»; парадоксы уходят в
карантин, а не взрываются). Твоя задача — ТОЛЬКО понять человека, не
судить. Ответь по-русски структурированным пересказом:
— СУЩНОСТИ/АТОМЫ: что здесь элементарные утверждения; что из них
  проверено (истина/ложь), что не проверено;
— УТВЕРЖДАЕТСЯ: кто/что что утверждает (если есть самоссылки — скажи);
— ЖАНР: простое высказывание или самореферентная система;
— ВОПРОС: что человек хочет узнать.
Если что-то неясно — задай уточняющий вопрос. Кратко."""

EMIT_SYS = ("Ты — компилятор в ZFL. По согласованному пониманию выдай "
            "ТОЛЬКО валидный JSON ZFL, без пояснений и без markdown.\n\n"
            + ZFL_SPEC + "\n\n" + FEWSHOT)

REPAIR_SYS = ("Ты — ремонт ZFL по ошибкам валидатора. Выдай ТОЛЬКО "
              "исправленный JSON ZFL, без пояснений.\n\n" + ZFL_SPEC)


class TranslatorError(Exception):
    pass


def groq(messages, temperature=0.2):
    key = get_key()
    if not key:
        raise TranslatorError(
            "Ключ Groq не найден: задайте GROQ_API_KEY или положите ключ "
            "в файл tool/.groq_key (он в .gitignore) — пока работаю без "
            "ИИ (режим профи: пишите ZFL руками в среднем окне).")
    body = json.dumps({"model": MODEL, "messages": messages,
                       "temperature": temperature}).encode()
    req = urllib.request.Request(API, data=body, headers={
        "Authorization": f"Bearer {key}",
        "Content-Type": "application/json",
        "User-Agent": "ZTLStudio/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=60) as r:
            data = json.loads(r.read().decode())
    except Exception as e:
        raise TranslatorError(f"Groq недоступен: {e}")
    return data["choices"][0]["message"]["content"].strip()


def understand(history):
    """history: [{'role': 'user'|'assistant', 'content': str}, ...]"""
    return groq([{"role": "system", "content": UNDERSTAND_SYS}] + history)


def strip_fences(s):
    s = s.strip()
    if s.startswith("```"):
        s = s.split("\n", 1)[1] if "\n" in s else s
        if s.rstrip().endswith("```"):
            s = s.rstrip()[:-3]
    return s.strip()


def emit(understanding):
    out = groq([{"role": "system", "content": EMIT_SYS},
                {"role": "user", "content":
                 f"Согласованное понимание:\n{understanding}\n\nВыдай ZFL."}])
    return strip_fences(out)


def repair(zfl_text, issues):
    errs = "\n".join(f"- {i['code']} @ {i['where']}: {i['hint']}"
                     for i in issues if i["level"] == "error")
    out = groq([{"role": "system", "content": REPAIR_SYS},
                {"role": "user", "content":
                 f"ZFL:\n{zfl_text}\n\nОшибки валидатора:\n{errs}\n\n"
                 "Исправь и выдай ZFL."}])
    return strip_fences(out)
