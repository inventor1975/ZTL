# Gauntlet comparison — 2026-07-12

| case | groq/llama-3.3-70b | anthropic/haiku-4.5 |
|---|---|---|
| Лжец | ✓ PARADOX | ✓ PARADOX |
| Пиноккио | ✗ DOWNSTREAM, UNDERDETERMINED | ✓ PARADOX |
| Правдолюб | ✓ UNDERDETERMINED | ✓ UNDERDETERMINED |
| Карусель Журдена | ✓ PARADOX | ✓ PARADOX |
| Сократ и Платон | ✓ PARADOX | ✓ PARADOX |
| Чётная пара | ✓ UNDERDETERMINED | ✓ UNDERDETERMINED |
| Пара правдолюбов | ✓ UNDERDETERMINED | ✓ UNDERDETERMINED |
| Карри | ✓ PARADOX | ✓ PARADOX |
| Крокодил (пессимистка) | ✓ PARADOX | ✓ PARADOX |
| Крокодил (оптимистка) | ✓ UNDERDETERMINED | ✓ UNDERDETERMINED |
| Брадобрей | ✓ PARADOX | ✓ PARADOX |
| Рассел | ✓ PARADOX | ✓ INPUT, PARADOX (repair) |
| Ябло-обрезка | ✓  | ✓  |
| Эпименид | ✗ emit_fail | ✓ PARADOX (repair, clarified) |
| Датчик | ✗ chat_fail | ✗ refused_or_clarify (clarified) |
| Берри | ✗ accepted | ✓ REFUSED |
| Сорит (куча) | ✓ REFUSED | ✓ REFUSED |

**Totals:** groq 13/17 (3 of the misses are Groq 429 rate-limits), anthropic 16/17.

**Observations.** Haiku emits canonical minimal encodings (compressed Russell `not(Tr(R_in_R))` first try; Pinocchio and Socrates–Plato correct after one clarification) and holds the boundary 2/2 (Berry, sorites refused). It is more cautious — four cases needed a human-style 'yes, proceed' turn, which the gauntlet now grants once. llama is faster and needs no clarifications but flip-flops on Pinocchio (loses the negation in the loop) and leans on the repair loop more. The core judged every valid emission correctly in both runs — all divergences live in the translator, never in the arbiter.
