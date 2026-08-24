#!/usr/bin/env python3
"""Атом-стор — БЕЗ КЛЮЧА. Каталог атомов файлов, ЗЕРКАЛЯЩИЙ дерево источника.

Замысел куратора 2026-08-24: хранить АТОМЫ файлов (сырые claim'ы, НЕ вердикты),
composable по корпусам; вложенность стора = корень источника «а то запутается
какой файл где». Ретривал — эмбеддинги (выбор «а»), с ТРЕБОВАНИЕМ работать на
ОДНОМ ядре ЦП (device=cpu, 1 поток; GPU по флагу, не обязателен). Если модели/
либы нет — keyword-hash fallback на numpy (тоже одно ядро, без модели).

Структура:
  atomstore/<корпус>/<тот же subpath, что у источника>/<файл>.atoms.jsonl
Каждая строка atoms.jsonl: {"atom": "...", "src": "<subpath>", "chunk": N}.
Атом = СЫРАЯ единица источника (данные/индекс), НЕ вердикт (вердикт
пересчитываем guard'ом на каждый запрос — [[ZTL: леджер не хранит вердиктов]]).
Индекс (_vectors.npy/_atoms.jsonl) — ПРОИЗВОДНЫЙ кэш, пересчитывается.

Поток (как introspect): atomize (нарезать+таск на извлечение, зеркаля дерево) ->
ФОРК извлекает атомы -> collect (сложить в atoms.jsonl) -> index (эмбеднуть) ->
query (эмбеддинг-ретрив релевантных атомов -> guard-сверка ответа). Извлечение и
суд — форк/SELF, не ключ.
"""
from __future__ import annotations
import argparse
import json
import os
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from zchoose import chunk_prose  # noqa: E402

TEXT_EXT = {".md", ".txt", ".tex", ".rst", ".org"}
MODEL_NAME = "all-MiniLM-L6-v2"   # малая (~80МБ), быстрая на CPU, dim=384
# РУССКИЕ корпуса — только многоязычной моделью. all-MiniLM обучен на английском:
# на русском вопросе «какой порядок выката моста» он НЕ нашёл нужный абзац вовсе,
# многоязычная поставила его первым (0.627). МЕРЕНО 2026-08-25 на памяти (1844
# единицы). Индекс помнит свою модель в _embedder.txt; корпуса на разных моделях
# не смешивать в одном запросе — векторы несопоставимы.
MODEL_MULTILINGUAL = "paraphrase-multilingual-MiniLM-L12-v2"

EXTRACT_RUBRIC = """Извлеки из ТЕКСТА атомарные ФАКТ-утверждения — по одному на
строку, каждое самодостаточно (без «он/это/выше»), ровно то, что текст УТВЕРЖДАЕТ,
без домысла и без вывода за пределы сказанного. Не оценивай, не суди — только
раздели на минимальные проверяемые куски. Одна строка = один атом, начинай с «- »."""


def _mirror(src_root: pathlib.Path, f: pathlib.Path, store_root: pathlib.Path,
            corpus: str) -> pathlib.Path:
    """Зеркальный путь под atomstore/<corpus>/<subpath источника>/."""
    rel = f.relative_to(src_root)
    return store_root / corpus / rel.parent / (f.name + ".atoms.jsonl")


def atomize(corpus: str, src_root: pathlib.Path, store_root: pathlib.Path,
            tasks_root: pathlib.Path, target_lines: int = 40,
            per_file: bool = True) -> list[pathlib.Path]:
    """Подготовить ТАСК на извлечение атомов, ЗЕРКАЛЯ дерево. Судья (форк)
    заполнит, потом collect().

    per_file=True (норма, модель куратора «1 форк = 1 документ»): один таск на
    ВЕСЬ файл — форк читает документ целиком. Дёшево: нет 70× накладных от
    дробления на десятки кусков. per_file=False дробит на куски ~target_lines —
    запас для файла, что не влезает в окно форка."""
    written = []
    files = [p for p in sorted(src_root.rglob("*"))
             if p.is_file() and p.suffix.lower() in TEXT_EXT]
    for f in files:
        rel = f.relative_to(src_root)
        text = f.read_text(encoding="utf-8", errors="replace")
        chunks = [("", text)] if per_file else chunk_prose(text, target_lines=target_lines)
        atoms_path = _mirror(src_root, f, store_root, corpus)
        atoms_path.parent.mkdir(parents=True, exist_ok=True)
        for i, (title, chunk) in enumerate(chunks, 1):
            tdir = tasks_root / corpus / rel.parent / f.name
            tdir.mkdir(parents=True, exist_ok=True)
            body = (f"<!-- atomize {corpus}/{rel} chunk {i}/{len(chunks)} -->\n\n"
                    f"{EXTRACT_RUBRIC}\n\n=== ТЕКСТ ===\n{chunk}\n")
            tp = tdir / f"achunk-{i:02d}.md"
            tp.write_text(body, encoding="utf-8")
            written.append(tp)
    print(f"atomize: {len(files)} файлов, {len(written)} chunk-таск'ов "
          f"(зеркалит {src_root} -> {tasks_root/corpus})")
    print("  -> раздай ФОРКАМ (по субагенту на chunk-таск), каждый вернёт атомы "
          "строками «- ...»; потом `atomstore.py collect`.")
    return written


def atomize_batched(corpus: str, src_root: pathlib.Path, store_root: pathlib.Path,
                    tasks_root: pathlib.Path, target_words: int = 12000,
                    min_words: int = 200) -> list[pathlib.Path]:
    """ПАЧКАМИ: мелкие файлы — по нескольку в один форк, крупные — по форку.

    «1 форк = 1 документ» верно для документов. Для россыпи мелких файлов оно
    разорительно: у субагента ~45k накладных на запуск, и на файле в 650 слов
    99% расхода — не текст. МЕРЕНО на корпусе из 155 файлов: форк-на-файл =
    8,9 млн токенов, пачками = 2,44 млн (в 3,6 раза дешевле, тот же выход).

    Каждый атом в пачке несёт свой файл: форк пишет «- <<путь>> утверждение».
    Так провенанс не теряется, хотя форк читал несколько файлов разом."""
    files = [(p, len(p.read_text(encoding="utf-8", errors="replace").split()))
             for p in sorted(src_root.rglob("*"))
             if p.is_file() and p.suffix.lower() in TEXT_EXT]
    files = [(p, w) for p, w in files if w >= min_words]      # мелочь не атомизируем
    big = [(p, w) for p, w in files if w >= target_words]
    small = sorted([(p, w) for p, w in files if w < target_words], key=lambda x: -x[1])
    loads: list[list] = [[p] for p, _ in big]
    cur, cur_w = [], 0
    for p, w in small:
        if cur and cur_w + w > target_words:
            loads.append(cur); cur, cur_w = [], 0
        cur.append(p); cur_w += w
    if cur:
        loads.append(cur)

    tasks_root.mkdir(parents=True, exist_ok=True)
    written = []
    for i, group in enumerate(loads, 1):
        body = [f"<!-- atomize-batch {corpus} {i}/{len(loads)}, файлов {len(group)} -->", "",
                EXTRACT_RUBRIC, "",
                "ВАЖНО: в пачке НЕСКОЛЬКО файлов. Каждую строку начинай с пути "
                "файла в двойных угловых скобках, чтобы не потерять источник:",
                "    - <<путь/файла.md>> утверждение", ""]
        for p in group:
            rel = p.relative_to(src_root)
            body += [f"=== ФАЙЛ: {rel} ===",
                     p.read_text(encoding="utf-8", errors="replace"), ""]
        tp = tasks_root / corpus / f"batch-{i:02d}.md"
        tp.parent.mkdir(parents=True, exist_ok=True)
        tp.write_text("\n".join(body), encoding="utf-8")
        written.append(tp)
    total_w = sum(w for _, w in files)
    print(f"atomize-batch: {len(files)} файлов ({total_w:,} слов) -> {len(written)} пачек "
          f"в {tasks_root/corpus}")
    print("  -> по форку на ПАЧКУ; каждый вернёт строки «- <<файл>> атом»; "
          "потом `collect --batch`.")
    return written



def atomize_direct(corpus: str, src_root: pathlib.Path, store_root: pathlib.Path,
                   min_words: int = 8) -> int:
    """БЕЗ ФОРКОВ: абзац = единица, прямо в .atoms.jsonl. Ноль токенов.

    Для ПОИСКА, не для заземления. Форк нужен, когда из текста надо ИЗВЛЕЧЬ
    утверждения (переформулировать, раскрыть местоимения) — это работа модели.
    Но если нужно лишь НАЙТИ нужное место, извлекать нечего: эмбеддинг ложится
    на сырой абзац, и вся цена — секунды GPU.

    Помечает единицы `"kind": "raw"`, чтобы сырой кусок нельзя было спутать с
    извлечённым атомом: атом — то, что текст утверждает, абзац — просто текст.
    """
    total = 0
    for f in sorted(src_root.rglob("*")):
        if not (f.is_file() and f.suffix.lower() in TEXT_EXT):
            continue
        rel = f.relative_to(src_root)
        units = []
        for i, para in enumerate(f.read_text(encoding="utf-8", errors="replace").split("\n\n"), 1):
            s = " ".join(para.split())
            if len(s.split()) >= min_words:
                units.append({"atom": s, "src": str(rel), "chunk": i, "kind": "raw"})
        if not units:
            continue
        out = store_root / corpus / (str(rel) + ".atoms.jsonl")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text("\n".join(json.dumps(u, ensure_ascii=False) for u in units),
                       encoding="utf-8")
        total += len(units)
    print(f"atomize-direct: {total} сырых единиц (БЕЗ форков, 0 токенов) в {store_root/corpus}")
    return total


def collect_batched(corpus: str, src_root: pathlib.Path, store_root: pathlib.Path,
                    tasks_root: pathlib.Path) -> int:
    """Разобрать пачки по файлам: «- <<путь>> атом» -> зеркальные .atoms.jsonl."""
    per_file: dict = {}
    marker = re.compile(r"^-\s*<<([^>]+)>>\s*(.+)$")
    for tf in sorted((tasks_root / corpus).glob("batch-*.md")):
        for line in tf.read_text(encoding="utf-8").splitlines():
            m = marker.match(line.strip())
            if m:
                per_file.setdefault(m.group(1).strip(), []).append(m.group(2).strip())
    # НЕ ТЕРЯТЬ МОЛЧА. Пачка без атомов = форк ещё пишет (или упал), и сбор
    # в этот момент кладёт в стор неполный корпус БЕЗ единой жалобы. Так уже
    # потерялись три главы книги и 137 атомов (2026-08-25) — заметил случайно.
    empty = [f.name for f in sorted((tasks_root / corpus).glob("batch-*.md"))
             if not any(marker.match(l.strip())
                        for l in f.read_text(encoding="utf-8").splitlines())]
    if empty:
        print(f"  ВНИМАНИЕ: пачек без атомов {len(empty)} ({', '.join(empty)}) — "
              f"форки ещё пишут или упали. Стор соберётся НЕПОЛНЫМ.", file=sys.stderr)

    total = 0
    for rel, atoms in per_file.items():
        out = store_root / corpus / (rel + ".atoms.jsonl")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text("\n".join(json.dumps({"atom": a, "src": rel, "chunk": 1},
                                            ensure_ascii=False) for a in atoms),
                       encoding="utf-8")
        total += len(atoms)
    print(f"collect-batch: {total} атомов из {len(per_file)} файлов в {store_root/corpus}")
    return total


def collect(corpus: str, src_root: pathlib.Path, store_root: pathlib.Path,
            verdicts_root: pathlib.Path) -> int:
    """Сложить извлечённые форками атомы в <файл>.atoms.jsonl (зеркальный путь)."""
    total = 0
    for f in sorted(src_root.rglob("*")):
        if not (f.is_file() and f.suffix.lower() in TEXT_EXT):
            continue
        rel = f.relative_to(src_root)
        vdir = verdicts_root / corpus / rel.parent / f.name
        if not vdir.exists():
            continue
        atoms = []
        for vf in sorted(vdir.glob("achunk-*.md")):
            try:
                ci = int(vf.stem.split("-")[1])
            except (IndexError, ValueError):
                ci = 0
            for line in vf.read_text(encoding="utf-8").splitlines():
                s = line.strip()
                if s.startswith("- ") and len(s) > 3:
                    atoms.append({"atom": s[2:].strip(), "src": str(rel), "chunk": ci})
        out = _mirror(src_root, f, store_root, corpus)
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text("\n".join(json.dumps(a, ensure_ascii=False) for a in atoms),
                       encoding="utf-8")
        total += len(atoms)
        print(f"  {rel}: {len(atoms)} атомов -> {out}")
    print(f"collect: {total} атомов в {store_root/corpus}")
    return total


def load_atoms(store_root: pathlib.Path, corpora: list[str]) -> list[dict]:
    """Загрузить атомы выбранных корпусов (composable {ZTL}/{VR}/оба).
    Пропускает служебные _atoms.jsonl индекса."""
    out = []
    for c in corpora:
        for jf in sorted((store_root / c).rglob("*.atoms.jsonl")):
            if jf.name.startswith("_"):
                continue
            for line in jf.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if line:
                    d = json.loads(line)
                    d["corpus"] = c
                    out.append(d)
    return out


# ---------------------------------------------------------------------------
# Эмбеддер: одно ядро ЦП по умолчанию (требование куратора). Fallback без модели.
# ---------------------------------------------------------------------------
def get_embedder(prefer_gpu: bool = False, threads: int = 1, model_name: str = None):
    """(name, embed_fn). embed_fn: list[str] -> np.ndarray (нормированные строки).
    Пытается sentence-transformers на CPU/1-поток (GPU только по prefer_gpu).
    Падает на keyword-hash (numpy, без модели, тоже одно ядро) при любой ошибке."""
    if threads:
        os.environ.setdefault("OMP_NUM_THREADS", str(threads))
        os.environ.setdefault("MKL_NUM_THREADS", str(threads))
    import numpy as np
    try:
        import torch
        from sentence_transformers import SentenceTransformer
        if threads:
            torch.set_num_threads(threads)
        device = "cuda" if (prefer_gpu and torch.cuda.is_available()) else "cpu"
        name = model_name or MODEL_NAME
        model = SentenceTransformer(name, device=device)

        def embed(texts):
            if not texts:
                return np.zeros((0, model.get_embedding_dimension()), dtype="float32")
            return np.asarray(
                model.encode(list(texts), batch_size=64, show_progress_bar=False,
                             normalize_embeddings=True), dtype="float32")
        return f"sentence-transformers/{name}@{device}", embed
    except Exception as e:  # noqa: BLE001 — любой сбой -> честный fallback
        import hashlib
        import re
        DIM = 512
        print(f"  [embed] sentence-transformers недоступен ({type(e).__name__}); "
              f"keyword-hash fallback (numpy, одно ядро)", file=sys.stderr)

        def embed(texts):
            out = np.zeros((len(texts), DIM), dtype="float32")
            for i, t in enumerate(texts):
                for tok in re.findall(r"\w+", str(t).lower()):
                    h = int(hashlib.md5(tok.encode()).hexdigest(), 16) % DIM
                    out[i, h] += 1.0
                nrm = float(np.linalg.norm(out[i])) or 1.0
                out[i] /= nrm
            return out
        return "keyword-hash(numpy-fallback)", embed


def index(corpus: str, store_root: pathlib.Path, prefer_gpu: bool = False,
          threads: int = 1, model_name: str = None) -> int:
    """Эмбеднуть все атомы корпуса -> _vectors.npy + _atoms.jsonl (кэш).
    threads: ядер ЦП для эмбеддинга (1 = пол-гарантия; на большой машине ставь
    больше, но отдача падает после ~4-8 — упор в память, не в ядра)."""
    import numpy as np
    atoms = load_atoms(store_root, [corpus])
    name, embed = get_embedder(prefer_gpu=prefer_gpu, threads=threads, model_name=model_name)
    vecs = embed([a["atom"] for a in atoms])
    idir = store_root / corpus
    idir.mkdir(parents=True, exist_ok=True)
    np.save(idir / "_vectors.npy", vecs)
    (idir / "_atoms.jsonl").write_text(
        "\n".join(json.dumps(a, ensure_ascii=False) for a in atoms), encoding="utf-8")
    (idir / "_embedder.txt").write_text(name, encoding="utf-8")
    print(f"index: {len(atoms)} атомов эмбеднуто [{name}] -> {idir}")
    return len(atoms)


def retrieve(corpora: list[str], question: str, store_root: pathlib.Path,
             k: int = 8, prefer_gpu: bool = False, threads: int = 1,
             model_name: str = None) -> list[tuple]:
    """Топ-k атомов по косинусу к вопросу через корпуса (composable)."""
    import numpy as np
    name, embed = get_embedder(prefer_gpu=prefer_gpu, threads=threads, model_name=model_name)
    vecs, atoms = [], []
    for c in corpora:
        av = store_root / c / "_vectors.npy"
        aa = store_root / c / "_atoms.jsonl"
        if not (av.exists() and aa.exists()):
            print(f"  [retrieve] нет индекса для {c} — прогони `index {c}`", file=sys.stderr)
            continue
        v = np.load(av)
        cat = [json.loads(l) for l in aa.read_text(encoding="utf-8").splitlines() if l.strip()]
        if len(v) != len(cat):
            print(f"  [retrieve] {c}: индекс рассинхрон ({len(v)}≠{len(cat)}) — переиндексируй",
                  file=sys.stderr)
            continue
        vecs.append(v)
        atoms += cat
    if not atoms:
        return []
    V = np.vstack(vecs)
    q = embed([question])[0]
    sims = V @ q  # обе стороны нормированы -> косинус
    order = np.argsort(sims)[::-1][:k]
    return [(float(sims[i]), atoms[i]) for i in order]


def query(corpora: list[str], question: str, answer: str, store_root: pathlib.Path,
          out_dir: pathlib.Path, k: int = 8, prefer_gpu: bool = False,
          threads: int = 1, model_name: str = None) -> pathlib.Path:
    """Ретрив top-k атомов -> guard-таск (источник = атомы) для форк-сверки ответа.

    Ретрив идёт по вопросу И ПО КАЖДОМУ утверждению ответа. Только по вопросу —
    ловушка: утверждение, которого вопрос не касался, не притянет своих атомов,
    судья их не увидит и поставит Z «не установлено». Тогда промах ретрива
    выглядит как честный отказ источника, а это разные вещи."""
    import guard
    import re as _re
    keys = [question]
    for s in _re.split(r"(?<=[.!?;])\s+|\n+", answer or ""):
        s = s.strip(" -–—•\t")
        if len(s) > 15:                      # обрывки не ищем
            keys.append(s)
    seen, hits = set(), []
    for key_text in keys:
        for score, atom in retrieve(corpora, key_text, store_root, k=k,
                                    prefer_gpu=prefer_gpu, threads=threads,
                                    model_name=model_name):
            ident = (atom["corpus"], atom["src"], atom["atom"])
            if ident not in seen:
                seen.add(ident)
                hits.append((score, atom))
    hits.sort(key=lambda x: -x[0])
    if not hits:
        print("query: ничего не нашлось (пустой индекс?)")
        return out_dir
    lines = []
    for s, a in hits:
        lines.append(f"[{s:.3f}] ({a['corpus']}:{a['src']}#{a['chunk']}) {a['atom']}")
    source = "\n".join(lines)
    print(f"query: top-{len(hits)} атомов (корпуса {corpora}):")
    for ln in lines:
        print("  " + ln)
    guard.prepare(source, question, answer, out_dir, mode="roll")
    print(f"  -> guard-таск в {out_dir}; форк судит, потом `guard.py assemble`, "
          "петля с кап-лимитом — guard_loop.")
    return out_dir


def main() -> int:
    ap = argparse.ArgumentParser(description="Атом-стор БЕЗ КЛЮЧА: атомы файлов, зеркаля дерево источника")
    sub = ap.add_subparsers(dest="cmd", required=True)
    pa = sub.add_parser("atomize", help="нарезать источник и подготовить таски извлечения атомов")
    pa.add_argument("corpus"); pa.add_argument("src_root")
    pa.add_argument("--store", default="atomstore"); pa.add_argument("--tasks", default="atomstore_tasks")
    pa.add_argument("--lines", type=int, default=40)
    pa.add_argument("--direct", action="store_true",
                    help="БЕЗ форков: абзац = единица, сразу в стор (для ПОИСКА, не для заземления)")
    pa.add_argument("--batch", action="store_true",
                    help="паковать мелкие файлы по нескольку в форк (дешевле в разы на россыпи)")
    pa.add_argument("--target-words", type=int, default=12000, help="слов на пачку")
    pa.add_argument("--chunk", action="store_true",
                    help="дробить файл на куски ~--lines (запас для файлов сверх окна форка); "
                         "по умолчанию 1 задача = весь файл (1 форк = 1 документ)")
    pc = sub.add_parser("collect", help="сложить извлечённые форками атомы в .atoms.jsonl")
    pc.add_argument("corpus"); pc.add_argument("src_root")
    pc.add_argument("--store", default="atomstore"); pc.add_argument("--verdicts", default="atomstore_tasks")
    pc.add_argument("--batch", action="store_true", help="собрать выходы пачек («- <<файл>> атом»)")
    pi = sub.add_parser("index", help="эмбеднуть атомы корпуса (одно ядро CPU по умолч.)")
    pi.add_argument("corpus"); pi.add_argument("--store", default="atomstore")
    pi.add_argument("--gpu", action="store_true", help="использовать GPU если есть")
    pi.add_argument("--threads", type=int, default=1, help="ядер ЦП (1=пол-гарантия; отдача падает после ~4-8)")
    pi.add_argument("--multilingual", action="store_true",
                    help="многоязычная модель — ОБЯЗАТЕЛЬНА для русских корпусов")
    pq = sub.add_parser("query", help="ретрив top-k атомов + guard-таск сверки ответа")
    pq.add_argument("corpora", nargs="+")
    pq.add_argument("--question", required=True)
    pq.add_argument("--answer", required=True, help="ответ для сверки (строка или @файл)")
    pq.add_argument("--store", default="atomstore"); pq.add_argument("--out", default="atomstore_query.tasks")
    pq.add_argument("-k", type=int, default=8); pq.add_argument("--gpu", action="store_true")
    pq.add_argument("--threads", type=int, default=1, help="ядер ЦП для эмбеддинга запроса")
    pq.add_argument("--multilingual", action="store_true", help="если корпус индексирован многоязычной")
    pl = sub.add_parser("stats", help="сколько атомов в корпусе(ах)")
    pl.add_argument("corpora", nargs="+"); pl.add_argument("--store", default="atomstore")
    a = ap.parse_args()
    if a.cmd == "atomize":
        if a.direct:
            atomize_direct(a.corpus, pathlib.Path(a.src_root), pathlib.Path(a.store))
            return 0
        if a.batch:
            atomize_batched(a.corpus, pathlib.Path(a.src_root), pathlib.Path(a.store),
                            pathlib.Path(a.tasks), target_words=a.target_words)
            return 0
        atomize(a.corpus, pathlib.Path(a.src_root), pathlib.Path(a.store),
                pathlib.Path(a.tasks), target_lines=a.lines, per_file=not a.chunk)
    elif a.cmd == "collect":
        if a.batch:
            collect_batched(a.corpus, pathlib.Path(a.src_root), pathlib.Path(a.store),
                            pathlib.Path(a.verdicts))
            return 0
        collect(a.corpus, pathlib.Path(a.src_root), pathlib.Path(a.store),
                pathlib.Path(a.verdicts))
    elif a.cmd == "index":
        index(a.corpus, pathlib.Path(a.store), prefer_gpu=a.gpu, threads=a.threads,
              model_name=MODEL_MULTILINGUAL if a.multilingual else None)
    elif a.cmd == "query":
        ans = (pathlib.Path(a.answer[1:]).read_text(encoding="utf-8")
               if a.answer.startswith("@") else a.answer)
        query(a.corpora, a.question, ans, pathlib.Path(a.store),
              pathlib.Path(a.out), k=a.k, prefer_gpu=a.gpu, threads=a.threads,
              model_name=MODEL_MULTILINGUAL if a.multilingual else None)
    elif a.cmd == "stats":
        atoms = load_atoms(pathlib.Path(a.store), a.corpora)
        by = {}
        for x in atoms:
            by[x["corpus"]] = by.get(x["corpus"], 0) + 1
        print(f"атомов всего: {len(atoms)} | по корпусам: {by}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
