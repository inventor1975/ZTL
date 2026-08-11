# The heap (sorites) — RESOLVED (2026-08-11)

*The dilemma, from Eubulides of Miletus, the man who also gave us the
liar. One grain of sand is not a heap. Adding a single grain to something
that is not a heap cannot make it one — one grain never decides. Chain
that ten thousand times and a million grains are not a heap; run it
backwards and an empty table is. Every step is impeccable and the
conclusion is nonsense, so one of the three obvious things costs money
nobody paid. Every claim below stands on a run: the stand is `sorites.py`
in this folder. The strip is heap(n) for n = 0..10000, witnessed at both
ends (n ≥ 9000 a heap, n ≤ 10 not) and unwitnessed in the middle.*

## The measured path

**1. In the murk the premise is not "unknown" — it is DENIED.** `Z → Z`
is F in this logic, and so are `T → Z` and `Z → F`. Of the 10000
tolerance instances, 8990 come back F — exactly the unwitnessed band and
its two shoulders. "One grain never decides" is a law of free truth, and
free truth is precisely what this logic refuses to hand out; the fallen
`p → p` is the same coin.

**2. Tolerance as a whole is F, hereditarily — and the two witnessed
ends alone refute it.** Fill the middle in any way at all (a cut at 11,
at 100, at 4711, at 9000; all-T; all-F) and the universal is F every
time: a strip that begins F and ends T must jump somewhere. Honest note:
this half is the classical argument and it stands. No third value did
any work here.

**3. Where the sting actually is** — and not where this stand first
guessed. The prediction was "the quantifier De Morgan"; the measurement
refused it. `¬∀tolerance` is T and "some step fails" (`∃¬inst`) is T:
De Morgan holds. The break is one step further in, where classical logic
rewrites a failed implication as a cliff:

| p | q | ¬(p → q) | p ∧ ¬q |
|---|---|----------|--------|
| T | Z | T | **F** |
| Z | Z | T | **F** |
| Z | F | T | **F** |

"The step from n to n−1 does not hold" is earned. "n is a heap and n−1 is
not" is a different sentence. A step can fail because **neither**
neighbour has been witnessed — which is exactly the situation in the
middle of the strip. Classical logic identifies the two and hands you a
hidden sharp grain; the epistemicist then spends a career defending a
cutoff that arrived on an unpaid bill. Measured: "some grain is a cliff"
stays F while the middle is dark. (Read the F honestly: this logic
asserts only what is witnessed, so "no cliff" means "no cliff shown" —
default deny, the same move it makes on any unwitnessed claim.)

**4. The cure the machine names is an act, not a discovery.** 8989 cells
are free; settling one is not a measurement of sand, since nothing in the
world distinguishes 4710 grains from 4711. Stipulate a cut at 4711 and
the boundary appears — exactly one, exactly where it was put. Not found:
drawn. This is the freedom capstone of the foreknowledge dilemma from the
other side — where there is no ground there is no target, and that is
where our freedom lives.

**5. The everyday sorites, where it bites for money.** "The sum is
large" against a threshold nobody set: **ON CREDIT**, cure `document
threshold`. The same sum against a cited norm (`reg-44-p3`): **EARNED**.
Every legal and accounting threshold — "a large sum", "a material
deviation", "an overdue payment" — is a heap with money in it, and it is
cured the same way: by citing the act that drew the line. The yardstick
has to be a **shared** one; a private threshold reads the judge's own
wish (the retribution capstone, measured).

**6. And by our own classifier the heap is not a paradox at all.** Run
the passport that types the docket's twenty-four, with the liar standing
next to it for scale:

```
liar  : PARADOX      no classical models; period 2; refusal PERMANENT
h5    : INPUT        unverified input; refusal until verification
tol6  : DOWNSTREAM   culprits ['h5','h6'], refusal conditional
```

The liar is incurable — no act ever lifts him. A heap cell has two
models and is lifted the moment somebody decides. The tolerance premise
is not even ill in itself: it is infected by neighbours the passport
names. The heap looks like a paradox and is a pile of unanswered
questions with a conclusion riding on them.

*Register note, so the two numbers do not read as a contradiction: the
passport reads Z in the LAZY register ("not computed yet") because it
classifies the kind of refusal; the verdicts above read the GREEDY one
("truth is not taken on credit") because they decide whether to sign.
Two questions, two answers, both ours.*

## The statement

The sorites is not a disease of vague words and needs no logic of
degrees. It is a bill. Two of its three obvious things are honest: the
ends are witnessed, and modus ponens holds (this logic keeps it). The
third — "one grain never decides" — is free truth, and it is denied
exactly where the argument needs it, in the dark middle. What survives
the denial is only that tolerance fails *somewhere*; the sharp grain the
classical reading pulls out of that failure is a second, unpaid step. The
boundary is not hidden in the sand. It arrives when someone draws it, and
the only honest version of that act is a shared line one can cite.

## Aphorism candidates (for the curator to mint or discard)

- «Шаг ломается не там, где обрыв, а там, где по обе стороны темно.»
- «Куча начинается не там, где кончается песок, а там, где мы провели
  черту — и смогли её предъявить.»

## Reproduce

```
python3 dilemmas/solved/sorites/sorites.py
```

Six sections, all under `assert`; part of the unified runner
(`python3 run_all.py`).

## Acknowledgement and disclosure

Built with Claude Opus 5 (Anthropic) under Variant A — the model wrote
the stand and the analysis, the human curator Vitaly Reznik set the
question, judged the result and owns it. The prediction-before-the-run
discipline is what caught the wrong attribution in step 3, and it is
recorded here rather than quietly corrected.
