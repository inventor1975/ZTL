# Zenodo — что вставлять (грузишь ты; поля по-английски, пояснения для тебя по-русски)

Файл для загрузки: `agrippa-counted.pdf` (8 страниц). Исходник `agrippa-counted.tex` можно приложить вторым
файлом — тогда любой сможет пересобрать.

**Resource type:** Publication → Preprint

**Title:** Agrippa's Trilemma, Counted: Acts, Posits and the Formal Register

**Authors / Creators:** Reznik, Vitaly — ORCID 0009-0002-4103-6387 — Affiliation: Independent researcher

**Description** (вставить как есть):

Agrippa's trilemma says that a justification either regresses without end, closes into a circle, or breaks off at a
dogma. We read it by one number: how many admissible readings a chain of reasons has, under classical (supported)
semantics. On a finite base the regress cannot occur (on an infinite one it reads twice, like the dogma); an odd loop has no reading (a paradox); an even loop and the
dogma "p because p" have two each (one and the same fork); only a chain that reaches a ground, a reason that rests on
nothing, reads once. Grounds come in two kinds: the value of an act is computed from its content and is the same under
every base; the value of a posit (an axiom, a Thing) is set by the base, and a rival base always exists. We read this
as the thesis that knowledge rests on acts alone, while about Things Agrippa is right and his horns are the signature
of the formal register. The formal results are proved in Lean 4 on the empty axiom list (98 theorems in four modules,
github.com/inventor1975/ZTL, tag agrippa-preprint-v1.0). The count itself is old (Kripke's grounded, ungrounded and
paradoxical sentences); a literature check is reported with what was found and read, and novelty is claimed only for
applying the count to Agrippa, for the act/posit line and for the machine-checked proofs.

**Version:** 1.0

**Language:** English

**Keywords:** Agrippa's trilemma; Münchhausen trilemma; epistemic regress; justification; foundationalism;
coherentism; Pyrrhonism; Sextus Empiricus; liar paradox; truth-teller; Lean 4; formal verification; constructive
proof; three-valued logic; Zero-Trust Logic; independence; axiom of choice; conservativity

**License:** Creative Commons Attribution 4.0 International (CC BY 4.0)

**Related works** (Related identifiers):
- `https://github.com/inventor1975/ZTL/tree/agrippa-preprint-v1.0` — relation: **Is supplemented by** — resource
  type: Software (Lean-исходники, тег agrippa-preprint-v1.0 = коммит f8c4fae)
- `10.5281/zenodo.23019513` — relation: **References** (ZTL v2.1.2)
- `10.5281/zenodo.23647163` — relation: **References** (VR-Forms v1.0.3 — черновик, публикуется ПЕРВЫМ)

**Additional notes** (поле Notes):

Written with the substantial participation of the AI system Claude (Anthropic), model Opus 5.5, in a dialogue setting
under the author's direction; the AI is not an author (COPE/ICMJE). Every
theorem is checked by the Lean 4 kernel on the empty axiom list.

---

## Перед загрузкой — проверь сам

1. Имя и ORCID в PDF совпадают с профилем Zenodo (в PDF: Vitaly Reznik, 0009-0002-4103-6387).
2. Раскрытие ИИ — в PDF есть раздел «Acknowledgements and AI disclosure»; в Notes оно же коротко.
3. Ссылка на тег открывается (тег agrippa-preprint-v1.0 запушен 25.10, коммит f8c4fae).
4. Зенодо не даёт править файлы после публикации — только новой версией. Сначала «Save», посмотри превью, потом
   «Publish».
5. По желанию: включить архивирование GitHub-релизов в Zenodo и сделать из тега релиз — тогда у кода будет свой
   DOI. Это необязательно: тег уже закрепляет версию.
