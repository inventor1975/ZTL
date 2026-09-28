# RED TEAM — the uncovered core (2026-09-28)

**Target.** master @ `1af886b`. These are the four parts the logic report
(REDTEAM-LOGIC-2026-09.md) names as not covered. Each is held against its own
stated definition:

1. **The propositional parser** on text with minimal parentheses:
   `ztljudge.formalize`, `_tokens` and `_show`.
2. **The reverse pass:** `zbackward.backward`, `zbackward.order` and
   `zfl.what_to_check`, with the memo added in `ea05959`.
3. **Time:** the epoch floor in `zfl.run`, `zexpire.py` and `ztime.py`,
   against `lean/EpochBoundary.lean` and `lean/ZTime.lean`.
4. **First order and tableaux:** `tableau.py`, `zsequent.py`,
   `quantifiers.py`, `tableau_fo.py` and `zfo.py`, against
   `lean/TableauCert*.lean`, `ZQuant.lean` and `ZSequent.lean`.

**Method.** The code is compared with an independent oracle,
`inventory/probes/redteam_uncovered_oracle.py`. The oracle imports none of the
code under test and cites, for each definition, the document it was read from.
- **The search** is `redteam_uncovered_search.py`. It is seeded, and its
  output is the same byte for byte under any `PYTHONHASHSEED`.
- **Two kinds of test:** seeded random search, plus exhaustive small spaces.
- **Exact:** values are the three strings T, F, Z; there are no floats.
- **What counts.** A wrong forced answer is a finding. A refusal is not: an
  exception from the parser, a budget, or "not computed".

**Result: five findings (three in the CODE, two in the DOCUMENTS) and four
notes.** Outside them the search found **no disagreement**:
- **The parser** is a consistent, unambiguous grammar that round-trips.
- **Families:** `backward`'s families agree with brute force wherever the
  empty set does not qualify and the search is not cut short.
- **The epoch floor** matches "one crossing per event" on every crossing.
- **Docstring numbers:** every number `ztime.py` and `zexpire.py` print there
  recomputes exactly.
- **Tableaux:** propositional and first-order tableaux, cut and weakening all
  agree with the semantics.

| # | kind | what | where |
|---|---|---|---|
| **B1** | CODE | when the target is reached **already** (the empty set qualifies), non-empty "minimal" sets are still listed, including atoms the claim does not contain; this reaches the studio | `zbackward.backward`, `zfl.what_to_check` |
| **B2** | CODE | a search **cut short** at `max_k` reports "no such set" (`possible_none`, `guaranteed_none`), and `order()` turns that into "НЕТ НАБОРА: недостижима никакой проверкой" or "ГАРАНТИИ НЕТ" | `zbackward.backward`, `order` |
| **B3** | CODE | a search **refused** at the cap also reports `possible_none: True`, and `order()` says "unreachable by any check" where a single ground settles it | `zbackward.backward`, `order` |
| **P1** | DOCUMENTS | the parser's precedence and associativity are stated nowhere, and four readings differ from the usual convention (`a -> b -> c` = `(a → b) → c`) | SPEC.md, ONBOARDING.md, `ztljudge`, the studio reference `zfldoc.py` |
| **E1** | DOCUMENTS | `zfl.run`'s epoch comment says "a survivor here is either independently grounded or empty"; `~p` survives the expiry of its only ground | `zfl.run`, the epoch floor comment |

No core file is changed. The stand `test_redteam_uncovered.py` fails on this
code (11 failing checks, about 1.5 s) and pins each finding with its minimal
reproduction. It is not registered in `run_all.py`.

---

## Findings

### B1 — CODE: `already`, and a "minimal" set beside it

The `zbackward` docstring:
- **`already`** is "цель достигнута БЕЗ единой проверки (**пустой набор**)":
  the target is reached without a single check, which is the empty set.
- **Minimality** is "в семействе нет набора, у которого собственное
  подмножество тоже подходит (антицепь)": no set in the family has a proper
  subset that also qualifies.

When `already` is true, ∅ qualifies, so the minimal family is exactly {∅}. No
non-empty set is minimal. The code starts its search at size 1 and never
compares against ∅, so it lists every set that qualifies:

| call | code | documented |
|---|---|---|
| `backward(p ∨ q, {p:T, q:Z}, "EARNED")` | already, possible `[(q)]`, guaranteed `[(q)]` | {∅}; nothing to check |
| `backward(p, {p:T, r:Z}, "EARNED")` | possible `[(r)]`, guaranteed `[(r)]`; **`r` is not in the formula** | {∅} |
| `backward(¬a, {a:Z}, "F", by value)` | already, **`guaranteed_none: True`**, which says no set guarantees F | ∅ guarantees F |

**It reaches the studio.** Take `zfl.run` on the claim `p | q`, with `p`
verified and `q` unverified:
- **The judge:** `EARNED — grounded; the unverified ['q'] do not matter`.
- **The same report's `what_to_check.EARNED`:** `{'already': True,
  'guaranteed': [['q']], …}`.

The second is the work order that `zbackward` says is written "only from
GUARANTEED sets". The same holds for `SETTLED` and for `REFUTED` whenever the
claim is already settled.

**Counted.** Of 33,968 `backward` calls, **4,804** hit this case. Of 1,594
claims sent through `what_to_check`, **634** did. Outside this case, the
families of `what_to_check` agree with brute force (0 of 1,594).

### B2 — CODE: a search cut short says "no such set"

`backward` searches sets up to `max_k = 4`. When that cuts the search short,
it adds the note `не_искал_дальше` ("о больших ничего не говорю", "I say
nothing about larger sets"). It still sets `possible_none` and
`guaranteed_none` to True.

The docstring defines those flags as "такого набора НЕТ" ("there is no such
set"). That is exactly the reading the note disclaims. `order()` reads only the
flags:

| call | `order()` says | brute force |
|---|---|---|
| `a∧b∧c∧d∧e`, all Z, `EARNED` | **"НЕТ НАБОРА: цель EARNED недостижима никакой проверкой"** | {a,b,c,d,e} makes it possible |
| `a∧b∧c∧d∧e`, all Z, SETTLED | **"ГАРАНТИИ НЕТ. …лишь ВОЗМОЖНА…"** | {a,b,c,d,e} guarantees it |
| `((¬a0 ∧ ((a1∧a2) ⊕ (a4↔a4))) ⊕ ¬a3)`, all Z, SETTLED | "ГАРАНТИИ НЕТ" | {a0…a4} guarantees it |

`order()` is the "наряд человеку", the work order a person follows. Here it
states a false impossibility, not a refusal.

**Counted.** Over 33,968 calls with `max_k` ∈ {2, 4}, the flags were wrong in
**104**. `order()` was wrong in **2** random cases, and in the hand-built ones
above.

**Not reachable from the studio.** `zfl.what_to_check` caps the unverified
inputs at `BACKWARD_CAP = 3 < MAX_K`.

### B3 — CODE: a refusal at the cap says "no such set"

Over `cap_grounds` (9 by disposition), `backward` returns the refusal
`отказ`. Beside it, it sets `possible_none: True` and `guaranteed_none: True`.

Take `order(g0 ∧ … ∧ g9, all Z, "REFUTED")`. It returns **"НЕТ НАБОРА: цель
REFUTED недостижима никакой проверкой"**. In fact any one ground refutes the
claim: `{g0}`, `{g1}`, and so on.

A refusal was turned into a forced "impossible". The docstring's own rule is
"молча пустой список читается как «ничего не надо», что противоположно правде"
(a silently empty list reads as "nothing needed", the opposite of the truth).
Here the refusal reads as "nothing will do", which is equally the opposite.

Not reachable from the studio: `what_to_check` refuses by itself first.

### P1 — DOCUMENTS: the reading is consistent, and stated nowhere

**What the parser does.** It was measured three ways, each against the
oracle's LAYERED grammar, a different algorithm from the code's precedence
climbing:
- every token string of length ≤ 6 over `p q ~ & | -> ^ = ( )`;
- random texts in minimal parentheses;
- random character soup.

**The reading:** `¬` binds tightest, then `&` > `|` > `^` > `->` > `=`. Every
binary operator is **left**-associative, and all spellings are the same
operator (`∧ ∨ → ⊕ ↔ <->`, `~ ¬`).

**Consistency:**
- Every text either parses to one tree or is refused with `ValueError`.
- Printing and re-reading is the identity, both for `_show` and for
  minimal-parenthesis printing.

**No document states this reading.** Checked:
- SPEC.md;
- ONBOARDING.md;
- `ztljudge`'s docstring, which lists the symbols only;
- JUDGE-API.md;
- the studio's operator reference `zfldoc.OP_HELP`, which explains each symbol
  but not how they combine.

The places where it differs from the usual convention (`¬ > ∧ > ∨ > → > ↔`, `→`
right-associative, `⊕` with `↔`):

| text | ZTL reads | the convention reads | differ classically? | differ with Z? |
|---|---|---|---|---|
| `a -> b -> c` | `(a → b) → c` | `a → (b → c)` | **yes** (a=F, b=T, c=F) | yes (10 of 27 markings) |
| `a -> b ^ c` | `a → (b ⊕ c)` | `(a → b) ⊕ c` | yes | yes |
| `a ^ b -> c` | `(a ⊕ b) → c` | `a ⊕ (b → c)` | yes | yes |
| `a = b ^ c` | `a ↔ (b ⊕ c)` | `(a ↔ b) ⊕ c` | no | **yes** (8 of 27) |

**Scale.** Of 20,000 random formulas printed in minimal parentheses (the
default run):
- 3,199 read differently under the convention;
- 2,651 of those differ in value on some marking.

With `--n 50000` the counts are 7,893 and 6,557.

Three of the four rows depend only on where `⊕` is placed, and textbooks do not
agree on that. The one that is not a matter of taste is `->`, which is
left-associative here and right-associative everywhere else. The word form
`implies` in `zfl` inherits the same reading.

This is not a bug: nothing contradicts it. The documents should state it, or
the reader should refuse unparenthesised chains of `->`.

**Nesting depth (a refusal, not a finding).**
- `(`×497 and `~`×993 raise `RecursionError`, at 995 and 994 characters.
  That is below `MAX_FORMULA_CHARS = 2000`. `zfl.run` turns it into
  `E_UNREADABLE`, as JUDGE-WORST-2026-09 already notes.
- A chain of `->` is read by a loop and has no limit; 4,000 links parse.

### E1 — DOCUMENTS: "a survivor is independently grounded or empty"

The epoch floor computes exactly what it says. It makes one crossing per
declared event, applied to the rows, and `survives` = same verdict. It
matched the oracle on all 4,705 crossings, including crossings through
`defined` rows.

The comment beside `survives` draws a conclusion from `EpochBoundary`:

> "a verdict that survives every crossing reads none of its grounds
> (EpochBoundary), so a survivor here is either independently grounded or
> empty."

`epoch_boundary_iff` is about **every** chain of `verify` and `expire`. It is
unrestricted epoch crossing, where earned ground may also come back with the
other value. The floor makes **one** declared expiry. Surviving that proves
nothing of the kind.

**The witness:** the claim `~p`, where `p` is verified and `expires_on: ev`:
- **before:** F / hereditary (REFUTED);
- **after:** F / until-verification (OPEN);
- **`survives`:** true.

`~p` reads only `p`. It is not independently grounded, and it is not empty,
because `p = F` makes it T. What survives is the greedy F of `¬Z`: the verdict
"did not earn T" in place of "refuted".

**Counted.** 1,118 of 4,705 crossings are survivors of this kind: the verdict
is unchanged, the marking the claim reads did change, the grade after is not
hereditary, and the claim is not constant.

The code's `survives` matches its own definition, so this is filed as a
DOCUMENTS finding. **The practical point:** a report can show `survives: true`
beside a disposition that went from REFUTED to OPEN.

---

## Notes (not findings)

- **`zbackward` by value reads `E` through `ztl.ev`.** `ev` is defined on
  T/F/Z; it gives `¬E = T` and `E ↔ E = T`, while the judge maps E to Z.
  Garbage in, and not reachable from the studio. It is excluded from the
  search.
- **The memo from `ea05959` changes nothing:** 0 of 33,968 calls, with the memo
  shared across targets as `what_to_check` shares it.
  - `backward`'s memo key has no formula in it, so a caller that shared one
    memo across two formulas would get wrong answers. Nobody does.
  - The epoch floor's `_judge_once` keys on the claim's own atoms. That is
    sound by the logic red team's result that foreign marks never move the
    judge, and it is confirmed here on 4,705 crossings.
- **`ztime.py` words the depth of its §6 witness three ways.** The witness
  `(a ∧ X) ∨ (¬a ∧ p)` is called "depth 3" in the header and "depth 4" in §2's
  print and §6's heading. By the depth used in its own "depth ≤ 2" pool, it
  has 5 nested connectives. Its U → S → H ladder is right.
- **Case.** In a formula, `t` is an atom and `T` is the constant. In a marking,
  `t` is read as T (`_read_mark` upper-cases marks). This is stated for marks
  only.

## What was searched (all seeded, `--seed 20260928`)

| section | space | checked | disagreements |
|---|---|---|---|
| parse | random trees (atoms p q r a1 x_y T F Z, depth ≤ 7) printed in minimal parentheses: ASCII, Unicode, `<->`; plus `formalize(_show(t))` | 150,000 | **0** |
| parse | EVERY token string of length ≤ 7 over `p q ~ & \| -> ^ = ( )` (6,286 accepted): accept or refuse, and the tree | 11,111,111 | **0** |
| parse | random character soup of 1–14 pieces, every spelling and junk | 50,000 | **0** |
| backward | 1–6 atoms, depth ≤ 4, T/F/Z marks with some E and foreign grounds; 7 targets (EARNED, REFUTED, SETTLED, ON CREDIT, OPEN, and T/F by value); `max_k` ∈ {2, 4}; families vs brute force over every size | 33,968 | **0** outside B1 (4,804) and B2 (104) |
| backward | `order()` vs brute force | 33,968 | B2 (2), and B3 by hand |
| backward | memo against no memo | 33,968 | **0** |
| what_to_check | 1–4 atoms, all three targets, vs the documented families | 1,594 | **0** outside B1 (634) |
| epoch | `zfl.run` on random documents (1–4 plain rows, 1–3 events, 40% with a `defined` row read through Kleene's lazy register) vs one crossing per event | 3,879 documents, 4,705 crossings | **0** (E1 counted apart: 1,118) |
| epoch | `ztime.gstate`, `zexpire.expire` then `gstate`, vs the grades of lean/ZTime.lean | 10,000 | **0** |
| epoch | `epoch_boundary_iff` by breadth-first search over `verify`/`expire` (not by the walking lemma): the depth-2 pool × 9 markings | 26,154 | **0** |
| numbers | ztime §1: 2,906 formulas, 29,812 ticks, 0 leaving H, 0 compound Z, U→H 14,818, S→U 108, nothing into S; §5: 13,059 × 78,354, 0 entries; §6: U, S, H. zexpire §2: 2,906 and 398. ONBOARDING: zsequent 5,292 cut instances. | all | **0** |
| tableau | every formula ≤ 5 nodes over {p, q, T, F, Z} (7,525) × every sign (all 8 subsets of {T, F, Z}), vs satisfiability | 60,200 | **0** |
| tableau | random signed sets (1–4 nodes, any sign, constants) vs satisfiability; `prove` vs entailment | 100,000 + 100,000 | **0** |
| sequent | identity T:φ,N:φ; weakening; cut on T/N and on F/P (fired 36,368 times) | 100,000 | **0** |
| first order | `quantifiers.ev_fo` vs the strict folds of ZQuant (P, Q, R, domains 1–3) | 10,000 | **0** |
| first order | `tableau_fo.prove_fo` vs every interpretation on domains 1–3 (≤ 9 cells, x read as 0) | 6,330 | **0** |
| first order | `zfo.prove` (arbitrary domains, budget 400). **valid** (516): no countermodel on any domain of 1–3 elements. **countermodel** (1,944): checked by the oracle's evaluation. **budget** (40): refusals | 2,500 | **0** |

"Found none" means none in that space. The following were **NOT covered**:

- **Lean.** Lean is not installed here, so no theorem was rebuilt. The Lean
  files were used as definitions, and their statements were checked as
  properties of the Python code: epoch_boundary_iff, hereditary_absorbing,
  grounded_hereditary, tproves_iff, closesN_iff and the ZQuant covers.
- **The reverse pass beyond 7 unverified grounds**, except the hand-built B2
  and B3 cases. Also not searched: `what_to_check` fed from `defined` rows,
  and `E` marks at the studio door, since `resolved_marking` never produces E.
- **The epoch floor with self-referential `defined` rows** (paradoxes and
  cycles). Only non-circular definitions were generated. Their lazy value was
  computed by the oracle, not by the passport. Also not covered: expiry
  interacting with a ground registry (`demote_unregistered`).
- **zfl's own rewriting before the parser.** `normalise`, the word operators
  (`and`, `or`, `not`, `implies`, `и`, `или`, `не`) and `Tr(…)` were not
  searched; only `ztljudge.formalize` was. One consequence: a row named with an
  operator word would be rewritten, and this is not checked.
- **zfo.**
  - **Completeness** was not searched: 40 budget refusals were left as
    refusals.
  - **Validity** was checked on domains of 1–3 elements only, not in general.
  - **Language:** one parameter `#a` and one free variable `x`. Constants,
    other free variables, and more than one binary predicate were not tried.
  - **Budget.** The `unguarded drinker` and `swap converse` still end in
    "budget", as zfo's own battery says.
- **Cost.** Timing was covered by JUDGE-PERF and JUDGE-WORST and was not
  measured here.

## Reproduce

```sh
python3 test_redteam_uncovered.py                     # the stand: RED, 11 failing checks, ~1.5 s
S=inventory/probes/redteam_uncovered_search.py
python3 $S --seed 20260928                            # every section at its default size, ~45 s
python3 $S --seed 20260928 --only parse --n 50000     # 11,111,111 token strings, 150,000 trees, ~3 min
python3 $S --seed 20260928 --only backward --n 5000   # 33,968 calls, 1,594 what_to_check
python3 $S --seed 20260928 --only epoch --n 5000      # 4,705 crossings; the ztime / zexpire numbers
python3 $S --seed 20260928 --only tableau --n 100000
python3 $S --seed 20260928 --only fo --n 10000
python3 -c "import zbackward as B; print(B.backward(('or','p','q'), {'p':'T','q':'Z'}, 'EARNED'))"   # B1
python3 -c "
import zbackward as B, ztljudge as J
phi = J.formalize('a & b & c & d & e'); m = {k: 'Z' for k in 'abcde'}
print(B.order(phi, m, 'EARNED'))                                   # B2
phi = J.formalize(' & '.join('g%d' % i for i in range(10))); m = {'g%d' % i: 'Z' for i in range(10)}
print(B.order(phi, m, 'REFUTED'))"                                 # B3
python3 -c "import ztljudge as J; print(J.formalize('a -> b -> c'))"                             # P1
```
