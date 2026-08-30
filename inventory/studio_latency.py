# -*- coding: utf-8 -*-
"""Откуда берутся 28 секунд в студии — сон по 429 или сама модель?

ПОЧЕМУ НУЖЕН ПРИБОР. 2026-08-30 я замерил 28.6 с на ответ живой студии и
объяснил это «Кими медленная». Голый вызов той же модели — 1.2–6.1 с
(MEASURED 2026-08-31). Значит объяснение было догадкой. `providers._post`
на 429 спит 15/30/45 с; одного попадания хватает, чтобы 6 секунд стали 21.
Гипотезу надо не рассказывать, а РАЗДЕЛИТЬ: считаем 429 отдельно от времени.

ЧТО ЗАМЕРЯЕТСЯ. Настоящий вызов конвейера студии (`translator.understand`)
с подсчётом попаданий в 429 и времени сна. Печатаем три числа:
общее время, время в модели, время во сне. Пока сумма не сходится —
объяснение не принято.

ОСТОРОЖНО — КЛЮЧ ОБЩИЙ С ЖИВЫМ САЙТОМ. Промерено 2026-08-31: отпечаток
NVIDIA_API_KEY на mindreef и на моей машине СОВПАДАЕТ. Значит каждый мой
замер ест лимит публичной студии, и пока я мерил, посетитель получал 429,
ждал наш откат и видел отказ. Не гонять этот прибор, пока у сервера не
появится ОТДЕЛЬНЫЙ ключ.

КОНТРОЛЬ. Первым идёт голый короткий вызов: если и он даёт 429, замер
несостоятелен и мы это говорим, а не списываем на конвейер.
"""
import os, sys, time, json, urllib.request, urllib.error

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "tool"))
import providers, translator                                    # noqa: E402

HITS = {"429": 0, "sleep": 0.0}
_real_post = providers._post
_real_sleep = time.sleep


def _counting_sleep(sec):
    HITS["sleep"] += sec
    _real_sleep(sec)


def _counting_post(url, body, headers):
    """Обёртка НАД настоящим _post: считаем 429, не подменяя поведение."""
    providers.time.sleep = _counting_sleep
    try:
        return _real_post(url, body, headers)
    finally:
        providers.time.sleep = _real_sleep


def bare_call(model="moonshotai/kimi-k3"):
    key = ""
    p = os.path.expanduser("~/.config/nvidia-nim.env")
    if os.path.exists(p):
        for line in open(p):
            if "NVIDIA_API_KEY" in line:
                key = line.split("=", 1)[1].strip().strip('"')
    body = json.dumps({"model": model, "max_tokens": 8,
                       "messages": [{"role": "user", "content": "say ok"}]}).encode()
    r = urllib.request.Request(
        "https://integrate.api.nvidia.com/v1/chat/completions", data=body,
        headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"})
    t0 = time.time()
    try:
        with urllib.request.urlopen(r, timeout=90) as f:
            f.read()
        return True, time.time() - t0
    except urllib.error.HTTPError as e:
        return False, time.time() - t0


def main():
    ok, dt = bare_call()
    print(f"КОНТРОЛЬ — голый короткий вызов: "
          f"{'прошёл' if ok else 'ОТБИТ 429'}, {dt:.1f} с")
    if not ok:
        print("\nЗАМЕР НЕСОСТОЯТЕЛЕН: ограничитель уже сработал до начала.\n"
              "Ждать и повторить — иначе припишем конвейеру чужое время.")
        return 2

    providers._post = _counting_post
    text = ("если из A следует B, и A истинно, то B истинно")
    t0 = time.time()
    try:
        translator.understand([{"role": "user", "content": text}], mode="hyp")
        err = None
    except Exception as e:
        err = str(e)
    total = time.time() - t0
    model_time = total - HITS["sleep"]
    print(f"\nВЫЗОВ КОНВЕЙЕРА (understand, режим hyp)")
    print(f"  всего            : {total:6.1f} с")
    print(f"  из них сон по 429: {HITS['sleep']:6.1f} с")
    print(f"  из них модель    : {model_time:6.1f} с")
    if err:
        print(f"  ОТКАЗ: {err}")
    print("\nВЫВОД")
    if HITS["sleep"] > 0:
        print(f"  Сон занял {HITS['sleep']/total*100:.0f}% времени ответа.")
        print("  Значит 28 секунд — НЕ скорость модели, а наш откат по 429.")
    else:
        print("  429 не случилось; всё время — модель.")
        print(f"  Если это {model_time:.0f} с, объяснение «модель медленная» "
              f"держится; если единицы секунд — 28 с надо ловить под нагрузкой.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
