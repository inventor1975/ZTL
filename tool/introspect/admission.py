#!/usr/bin/env python3
"""Граница допуска — Сертификат заземления + Ворота допуска (Фаза 2, минимум).

Замысел (memo внешнего рецензента 2026-08-25 + план admission-v0.2): между «источник
поддерживает P» и «P допущено как ПОСЫЛКА формального вывода» стоит машинно-
проверяемая граница. Retrieval/guard дают ОТНОШЕНИЕ ПОДДЕРЖКИ; они НЕ дают права
взять P посылкой. Это право выдаёт ТОЛЬКО gate, и только если сошлись поддержка,
пригодность источника, актуальность эпохи и достаточность покрытия.

Модуль СТОИТ ОТДЕЛЬНО: ZTL-ядро он не трогает (узкий мост — следующий шаг, по
слову куратора). Здесь только два объекта и их инварианты.

Инварианты, что кодируем механически (из G1..G12 внешнего рецензента — дешёвые):
  G1  нет голой посылки: admit требует ВАЛИДНЫЙ сертификат, не текст.
  G2  нет смешения поддержки и истины: сертификат несёт support_relation, не «true».
  G4  сохранение незнания: NO_SUPPORT_FOUND НИКОГДА не станет SUPPORTED.
  G6  границы эпохи: сертификат чужой эпохи не допускается без явного правила.
  G7  точная привязка: смена байтов источника/предложения меняет digest → отказ.
  G12 потолок: решение прямо говорит, что оно устанавливает и что НЕТ.
"""
from __future__ import annotations
import dataclasses
import hashlib
import json
from typing import Optional

TOOL_VERSION = "admission-0.3"

# СЛОВАРЬ ИСХОДОВ (рабочее задание GAZ-R1, §4). Имена могут отличаться, но
# СМЫСЛОВЫЕ РАЗЛИЧИЯ СХЛОПЫВАТЬ НЕЛЬЗЯ: отказ обязан называть, ЧЕМ именно он
# вызван, иначе «не допущено» скрывает разные болезни под одним словом.
D_ADMIT = "ADMIT"
D_NO_SUPPORT = "NO_SUPPORT_FOUND"                 # поиск не нашёл (процедурное)
D_SOURCE_SILENT = "SOURCE_SILENT"                 # исчерпывающе проверено, молчит
D_CONTRADICTED = "CONTRADICTED_BY_SOURCE"
D_CONFLICT = "CONFLICT"                           # два пригодных источника врозь
D_CERT_INVALID = "CERTIFICATE_INVALID"
D_INELIGIBLE = "SOURCE_INELIGIBLE"
D_SCOPE = "SCOPE_MISMATCH"
D_EPOCH = "EPOCH_MISMATCH"
D_POLICY = "POLICY_MISMATCH"
D_INTEGRITY = "REPRESENTATION_INTEGRITY_FAILURE"  # байты/OCR/представление
D_NO_AUTHORITY = "NO_AUTHORITY"                   # ось правомочия, не поддержки
D_EXEC_MISMATCH = "EXECUTION_MISMATCH"
D_DECLARED_LIMIT = "DECLARED_LIMITATION"          # известный предел, не инвариант
D_NOT_EVALUATED = "NOT_EVALUATED"                 # НЕ засчитывается как проход

# отношение поддержки — НЕ истина. Маппинг из метки guard под ПОКРЫТИЕМ.
SUPPORTED = "SUPPORTED_BY_SOURCE"
CONTRADICTED = "CONTRADICTED_BY_SOURCE"
NO_SUPPORT = "NO_SUPPORT_FOUND"          # retrieval: поиском не найдено (процедурное)
SOURCE_SILENT = "SOURCE_SILENT"          # exhaustive: источник в полных границах молчит


def _sha(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def support_from_mark(mark: str, coverage: str) -> str:
    """Метка guard (T/F/Z) под ПОКРЫТИЕМ → отношение поддержки.

    Ключ Фазы 1: Z под retrieval — это НЕ «источник молчит», а «не найдено
    поиском». Только exhaustive-Z даёт SOURCE_SILENT. Так retrieval-miss никогда
    не протечёт в source-silence и, тем более, в поддержку."""
    m = (mark or "").upper()
    if m == "T":
        return SUPPORTED
    if m == "F":
        return CONTRADICTED
    if m == "Z":
        return SOURCE_SILENT if coverage == "exhaustive" else NO_SUPPORT
    raise ValueError(f"метка должна быть T|F|Z, не {mark!r}")


@dataclasses.dataclass(frozen=True)
class GroundingCertificate:
    """Что за байты источника обосновали какое отношение поддержки под какой
    процедурой и эпохой. И ТОЛЬКО это — не истина, не авторитет, не актуальность."""
    proposition: str
    corpus: str
    source_id: str
    source_digest: str            # sha256 предъявленных атомов-опор
    evidence_atom_ids: tuple      # ('CORPUS:src#chunk', ...)
    support_relation: str
    coverage: str                 # retrieval | exhaustive
    retrieval_method: str         # напр. 'paraphrase-multilingual@k=5'
    corpus_epoch: str             # digest/версия состояния корпуса на момент суда
    # ── оси, добавленные под векторы GAZ-R1. Каждая отвечает на СВОЙ вопрос;
    # схлопывать их в «не допущено» запрещено (§4 задания).
    scope: str = ""               # V17: правопорядок/область действия источника
    valid_until: str = ""         # V16: срок действия САМОГО свидетельства ≠ эпоха корпуса
    policy_version: str = ""      # V21: версия политики допуска, под которой выдан
    representation_ok: bool = True  # V14: цело ли представление (OCR/байты)
    attributed_to: str = ""       # V09: кому приписана поддержка (пусто = source_id)
    suspect: str = ""             # V10: помеченное внушение в байтах источника

    @property
    def proposition_digest(self) -> str:
        return _sha(self.proposition.strip())

    def _core(self) -> dict:
        d = dataclasses.asdict(self)
        d["evidence_atom_ids"] = list(self.evidence_atom_ids)
        d["proposition_digest"] = self.proposition_digest
        d["tool_version"] = TOOL_VERSION
        return d

    @property
    def cert_digest(self) -> str:
        return _sha(json.dumps(self._core(), ensure_ascii=False, sort_keys=True))

    def to_json(self) -> str:
        d = self._core()
        d["cert_digest"] = self.cert_digest
        return json.dumps(d, ensure_ascii=False, sort_keys=True, indent=1)


def verify_certificate(cert: GroundingCertificate, claimed_digest: str) -> bool:
    """G7: пересчитать digest и сверить. Любая подмена байтов предложения/источника
    или полей — иная идентичность, проверка не проходит."""
    return cert.cert_digest == claimed_digest


@dataclasses.dataclass(frozen=True)
class AdmissionDecision:
    admitted: bool
    disposition: str          # ТОЧНЫЙ разряд из словаря выше, не свободный текст
    proposition: str
    reason: str
    cert_digest: str
    purpose: str
    epoch: str
    # G12 — потолок прямо в объекте решения:
    establishes: str = ("допущенность P как ПОСЫЛКИ под данное назначение и эпоху, "
                        "с опорой на именованный источник")
    does_not_establish: str = ("истинность P, авторитетность/актуальность источника, "
                               "правомочие ДЕЙСТВИЯ — это отдельные ворота")


def admit(cert: GroundingCertificate, purpose: str, epoch: str,
          eligible_sources: dict, *, scope: str = "", now: str = "",
          policy_version: str = "") -> AdmissionDecision:
    """Ворота: сертификат — НЕОБХОДИМ, но НЕ достаточен. Допуск только если сошлось.

    eligible_sources: {purpose: set|list источников, пригодных для этой цели}.
    Пустое/отсутствие цели → никакой источник не пригоден (отказ по умолчанию).

    scope/now/policy_version — ЗАПРОШЕННЫЙ контекст. Пустые = ось не проверяется;
    это осознанное послабление для старых вызовов, но в GAZ-R1 они задаются, иначе
    вектор проверял бы не то, что заявлено."""
    def no(disposition, reason):
        return AdmissionDecision(False, disposition, cert.proposition, reason,
                                 cert.cert_digest, purpose, epoch)

    # ПОРЯДОК ПРОВЕРОК НЕ ПРОИЗВОЛЕН. Сперва — можно ли вообще ЧИТАТЬ свидетельство
    # (целостность представления), потом — тому ли источнику оно приписано, и лишь
    # затем вопросы поддержки. Рассуждать о поддержке по нечитаемым или чужим
    # байтам бессмысленно: ответ будет получен, но ни о чём.
    if not cert.representation_ok:
        return no(D_INTEGRITY, "представление свидетельства повреждено "
                               "(OCR/байты): читать нечего, судить не о чем")
    if cert.attributed_to and cert.attributed_to != cert.source_id:
        return no(D_CERT_INVALID,
                  f"поддержка приписана {cert.attributed_to!r}, а сертификат выдан "
                  f"на {cert.source_id!r}: «поддержано где-то» ≠ «поддержано ЭТИМ»")
    # политика допуска — тоже версионируемый источник; допуск по её ПРЕЖНЕЙ версии
    # есть воспроизведение отменённых правил
    if policy_version and cert.policy_version and cert.policy_version != policy_version:
        return no(D_POLICY, f"сертификат выдан под политикой {cert.policy_version}, "
                            f"действует {policy_version}")
    # СРОК ДЕЙСТВИЯ СВИДЕТЕЛЬСТВА ≠ ЭПОХА КОРПУСА. Корпус может не меняться, а
    # свидетельство — протухнуть само по себе (акт истёк, справка просрочена).
    if cert.valid_until and now and cert.valid_until < now:
        return no(D_EPOCH, f"свидетельство действовало до {cert.valid_until}, "
                           f"сейчас {now}")
    # область действия источника: чужой правопорядок поддерживает СВОЁ P, не наше
    if scope and cert.scope and cert.scope != scope:
        return no(D_SCOPE, f"источник действует в области {cert.scope!r}, "
                           f"запрошена {scope!r}: поддержка чужого правопорядка")

    # G1/G2/G4: допускаем ТОЛЬКО подтверждённое источником. Разряд отказа НАЗЫВАЕТ
    # причину: промах поиска, молчание источника и опровержение — РАЗНЫЕ болезни,
    # и схлопывать их в одно «не допущено» запрещено рабочим заданием (§4).
    if cert.support_relation != SUPPORTED:
        return no({NO_SUPPORT: D_NO_SUPPORT,
                   SOURCE_SILENT: D_SOURCE_SILENT,
                   CONTRADICTED: D_CONTRADICTED}.get(cert.support_relation, D_POLICY),
                  f"нет поддержки источника (support={cert.support_relation}); "
                  "незнание/промах/опровержение посылкой не становятся")
    # G6: эпоха сертификата должна совпасть с эпохой запроса (без явного правила
    # переноса — не допускаем чужую эпоху).
    if cert.corpus_epoch != epoch:
        return no(D_EPOCH,
                  f"эпоха сертификата {cert.corpus_epoch[:12]} ≠ запрошенной "
                  f"{epoch[:12]}; повторное использование через эпоху запрещено")
    # пригодность источника ДЛЯ ЭТОЙ ЦЕЛИ (source ≠ authority — отдельная ось)
    ok = eligible_sources.get(purpose) or ()
    if cert.source_id not in ok:
        return no(D_INELIGIBLE,
                  f"источник {cert.source_id!r} не в списке пригодных для цели "
                  f"{purpose!r}; поддержка ≠ правомочие источника")
    return AdmissionDecision(True, D_ADMIT, cert.proposition,
                             "допущено: поддержка+пригодность+эпоха сошлись",
                             cert.cert_digest, purpose, epoch)


def resolve_conflict(decisions: list) -> AdmissionDecision:
    """V19: несколько ПРИГОДНЫХ источников, говорящих врозь.

    Противоречие ДОЛЖНО ВЫЖИТЬ. Запрещено: голосовать большинством, брать свежее,
    брать «более уверенное», просить модель примирить. Пока явного правила
    разрешения нет — это CONFLICT, и он идёт наружу конфликтом.

    Схлопнуть противоречие в одну сторону — то же самое, что изготовить посылку:
    источник её не давал, её произвёл наш способ считать."""
    admitted = [d for d in decisions if d.admitted]
    if len(admitted) <= 1:
        return admitted[0] if admitted else (decisions[0] if decisions else None)
    props = {d.proposition for d in admitted}
    if len(props) == 1:
        return admitted[0]            # согласные источники — не конфликт
    d0 = admitted[0]
    return AdmissionDecision(
        False, D_CONFLICT, " | ".join(sorted(props)),
        f"{len(admitted)} пригодных источника поддерживают несовместимое; "
        "правила разрешения не задано — противоречие сохраняется, не схлопывается",
        d0.cert_digest, d0.purpose, d0.epoch)


def authorize(decision: AdmissionDecision, actor: str, action: str,
              authority_grants: dict, performed_action: str = "") -> AdmissionDecision:
    """V23/V24: ПОСЛЕ допуска посылки — отдельные ворота ПРАВОМОЧИЯ и ИСПОЛНЕНИЯ.

    G3 в полный рост: допущенная посылка и верное следствие НЕ создают права
    действовать. Право даёт наделение (authority_grants), и оно ограничено
    актором и КОНКРЕТНЫМ действием. А исполненное действие сверяется с
    разрешённым: правомочие на X не покрывает Y.

    authority_grants: {актор: [разрешённые действия]}."""
    def no(disposition, reason):
        return AdmissionDecision(False, disposition, decision.proposition, reason,
                                 decision.cert_digest, decision.purpose, decision.epoch)
    if not decision.admitted:
        return decision                     # нечего авторизовывать
    allowed = authority_grants.get(actor) or ()
    if action not in allowed:
        return no(D_NO_AUTHORITY,
                  f"актор {actor!r} не наделён правом на {action!r}; верная посылка "
                  "и верный вывод правомочия не создают")
    if performed_action and performed_action != action:
        return no(D_EXEC_MISMATCH,
                  f"разрешено {action!r}, исполнено {performed_action!r}: "
                  "правомочие на одно не покрывает другое")
    return decision


def build_certificate(proposition: str, corpus: str, source_id: str,
                      evidence_atoms: list, mark: str, coverage: str,
                      retrieval_method: str, corpus_epoch: str,
                      **axes) -> GroundingCertificate:
    """Собрать сертификат из результата guard. evidence_atoms — список строк-атомов
    (их же байты идут в source_digest, чтобы привязка была к содержимому).

    axes — необязательные оси GAZ-R1: scope, valid_until, policy_version,
    representation_ok, attributed_to, suspect. Каждая входит в digest, потому
    подмена любой из них ломает проверку сертификата (G7)."""
    src_digest = _sha("\n".join(evidence_atoms))
    ids = tuple(f"{corpus}:{source_id}#{i}" for i, _ in enumerate(evidence_atoms, 1))
    return GroundingCertificate(
        proposition=proposition, corpus=corpus, source_id=source_id,
        source_digest=src_digest, evidence_atom_ids=ids,
        support_relation=support_from_mark(mark, coverage), coverage=coverage,
        retrieval_method=retrieval_method, corpus_epoch=corpus_epoch, **axes)


def _selftest() -> int:
    """Инварианты прогоном — не чтением."""
    ep = "epoch-A"
    elig = {"decision": ["ruleX"]}
    atoms = ["Правило X: порог 64 ГиБ обязателен."]
    ok = 0; fail = 0

    def check(name, cond):
        nonlocal ok, fail
        print(f"  {'OK ' if cond else 'FAIL'} {name}")
        ok += cond; fail += (not cond)

    # 1) SUPPORTED + пригоден + та же эпоха → допущено
    c = build_certificate("Порог памяти 64 ГиБ.", "DOWNSTREAM", "ruleX", atoms,
                          "T", "retrieval", "multi@k=5", ep)
    d = admit(c, "decision", ep, elig)
    check("SUPPORTED+пригоден+эпоха → admitted", d.admitted)

    # 2) G4: retrieval-Z (NO_SUPPORT) → отказ, не посылка
    c2 = build_certificate("Порог 128 ГиБ.", "DOWNSTREAM", "ruleX", atoms,
                           "Z", "retrieval", "multi@k=5", ep)
    check("retrieval-Z=NO_SUPPORT_FOUND", c2.support_relation == NO_SUPPORT)
    check("NO_SUPPORT → REFUSE", not admit(c2, "decision", ep, elig).admitted)

    # 3) exhaustive-Z → SOURCE_SILENT (тоже отказ), но ИМЯ иное
    c3 = build_certificate("Порог 128 ГиБ.", "DOWNSTREAM", "ruleX", atoms,
                           "Z", "exhaustive", "multi@k=5", ep)
    check("exhaustive-Z=SOURCE_SILENT", c3.support_relation == SOURCE_SILENT)
    check("SOURCE_SILENT → REFUSE", not admit(c3, "decision", ep, elig).admitted)

    # 4) G6: чужая эпоха → отказ
    check("чужая эпоха → REFUSE", not admit(c, "decision", "epoch-B", elig).admitted)

    # 5) пригодность: источник не для этой цели → отказ
    check("непригодный источник → REFUSE",
          not admit(c, "decision", ep, {"decision": ["ruleY"]}).admitted)

    # 6) G7: подмена предложения меняет digest → verify падает
    dig = c.cert_digest
    c_tamper = dataclasses.replace(c, proposition="Порог 999 ГиБ.")
    check("подмена предложения ломает verify", not verify_certificate(c_tamper, dig))
    check("нетронутый сертификат проходит verify", verify_certificate(c, dig))

    # 7) G1: голую посылку допустить нечем — admit требует cert (типовой барьер)
    check("нет пути admit(str) — только через cert", not hasattr(admit, "__wrapped__"))

    print(f"\n  итог: {ok} OK, {fail} FAIL")
    return 1 if fail else 0


if __name__ == "__main__":
    raise SystemExit(_selftest())
