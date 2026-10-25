# Agrippa preprint — prior-art map (2026-10-25)

Two Sonnet literature checks (subscription), run against the exact claims C1–C5 below. Reading status is kept
as each check reported it: READ = full text or the relevant pages; SUMMARY = an SEP/encyclopedia page read through a
fetch summary; ABSTRACT = abstract or secondary report only; NOT READ = known only by citation. "Not found" means
"not found in roughly 30 English searches", never "does not exist".

## Our claims

- C1 One count of readings sorts the horns: regress impossible on a finite base; odd loop 0 (paradox); even loop
  2 (fork); "p because p" = the even loop (2); nullary ground 1. (lean/Agrippa.lean)
- C2 knowledge_iff_ground: exactly one reading iff the chain reaches a ground; constructive. (Agrippa.lean)
- C3 With and/or/not: knowledge = a value forced by acts; on a finite base, no loop and no posit ⇒ knowledge; an act
  can override a dogma. (lean/AgrippaNet.lean)
- C4 Act vs posit: an act's value is computed and base-invariant; a posit's value is set by the base, and a rival
  base reads it the other way. Agrippa's modes of disagreement and relativity = the signature of posits.
  (Agrippa.lean, act_absolute / posit_relative)
- C5 Three-valued reading: 2 readings = a verdict that an admissible future reverses (on credit); 1 = settled by one
  verification and hereditary after it (earned); 0 = no future. (lean/AgrippaZ.lean)
- Plus: ZDescent (a Thing's operational part = what is constructed without it; "true in every base" is not
  knowledge in ZTL); empirical knowledge = credit on a posit (the curator's decision, 25.10).

## Formal side

**C1 — the count is OLD; the reading of Agrippa by it is not found.**
- Gaifman, "Pointers to Truth", J. Phil. 89(5), 1992, 223–261 — READ pp. 238–239
  (haimgaifman.net/wp-content/uploads/2016/07/gaifman-1992-pointer-to-truth.pdf). Truth-teller: two total
  self-supporting valuations (T and F); liar: GAP in every one. That is already "2 vs 0" as a classifier.
- Walicki & Dyrkolbotn, "Paraconsistent Resolution", Australasian J. Logic 19(3), 2022, Art. 1; and
  "Paraconsistency, resolution and relevance", arXiv:1906.03476 — READ §§2–3. Graph normal form x ↔ ∧¬y_i = our
  support/negated-support; a sink x ↔ ⊤ = our nullary ground; classical models = kernels; "This statement is not
  false" as an even 2-cycle with two kernels; the liar (odd cycle) has none; no odd cycles ⇒ a kernel exists. No
  justification, regress or Agrippa; no "exactly one iff reaches a ground".
- Walicki, "Reference, paradoxes and truth", Synthese 171(1), 2009, 195–226, DOI 10.1007/s11229-008-9392-9 —
  NOT READ (closed access; no free copy found; author page at UiB gone). Pointer structures ≅ Boolean equation
  systems, paradox = no solution (abstract). References: Kripke, Gupta–Belnap, Gaifman, Cook, Yablo, Wen — no
  epistemology, no Agrippa. MUST BE READ BEFORE POSTING.
- Kripke 1975; Gupta & Belnap 1993 — SUMMARY (SEP "Revision Theory of Truth", "Liar Paradox" §4.3.5): truth-teller
  consistently either value (two Tarskian expansions); liar unstable.
- CATCH, to be stated in the text: in logic programming p ← p has ONE stable model (the empty one, by minimality),
  while its Clark completion p ↔ p has two. Fages 1994 (J. Methods Logic CS 1:51–60, ABSTRACT): they coincide only
  for tight programs. You & Yuan 1994/95, Lin & Zhao AAAI 2004 (ABSTRACT). "Dogma = even circle" holds under
  supported/classical semantics and fails under minimal/stable semantics — our answer: minimality is itself a
  chosen stop (already in Agrippa.lean's header).
- Regress on graphs: Miao, arXiv:2307.07524, App. B — READ: "generalized Münchhausen trilemma": every digraph has a
  root, a cycle or an infinite path; prose, existence only. Berker, "Coherentism via Graphs", Phil. Issues 25,
  2015, 322–352, DOI 10.1111/phis.12052 — READ intro: support graphs, no valuations, no negation, no fork.
- Infinite bases can be paradoxical (Yablo 1993; Cook 2004 JSL 69(3):767–774; Rabern–Rabern–Macauley JPL 2013 —
  ABSTRACT): finiteness is essential to C1/C2 and must be stated up front.

**C2** — no source states the equivalence. Nearest: Doyle 1979 (TMS, well-founded support, AI 12:231–272); Elkan
1990 (TMS labelings = stable models, AI 43:219–234); Pollock (unique status = warranted); Dung 1995 (AI 77:321–357,
no odd cycle ⇒ stable extension). Novelty: the constructive, kernel-checked iff.

**C3** — "T or dogma = T" is the strong-Kleene table (Kripke; Gaifman's rules, READ p. 239). Claim the theorem
(unique forced value, constructive necessity), not the table.

**C4** — not found as stated. Near: Brennan & Lee, Phronesis 59(3), 2014 (relativity mode, ABSTRACT); Lammenranta
2008 (disagreement mode); assumption-based argumentation (Bondarenko–Dung–Kowalski–Toni, AI 93, 1997, ABSTRACT).

**C5** — not found; nearest: Kripke partial → total fixed points; Gaifman's GAP; Pollock's provisional defeat.

Also: Vazquez, Manuscrito 42(3), 2019, DOI 10.1590/0100-6045.2019.V42N3.DV (READ partial) — the five modes as a
dialectical algorithm; Atkinson & Peijnenburg, Fading Foundations, 2017, and NDJFL 51(4), 2010 (ABSTRACT) —
probabilistic loops, a different object; Thomas's rules (Remy–Ruet–Thieffry 2008, ABSTRACT) — necessary
conditions only, an ancestor.

## Philosophical side

- Sextus, PH (Bury) — READ-PRIMARY: I.13 dogma = assent to the non-evident; the dogmatist "posits" (tithetai);
  I.19–20 appearances are not abolished, doubt is about "the account given of the appearance"; I.21–24 life guided
  by nature, passions, laws/customs, the arts, "undogmatically"; I.164–177 the five modes; Hypothesis answered by
  "we shall be no less worthy of credence every time that we make the opposite hypothesis" (I.173–174) — the rival
  base in Sextus's own words. CAVEAT: I.170 ff. applies the modes to "every matter of inquiry", sensibles included;
  the target is "real nature" — our reading rests on the I.19–20 contrast.
- Frede 1979 (urbane reading) vs Barnes 1990 / Burnyeat 1980 (rustic: even honey's sweetness is non-evident) —
  SUMMARY (SEP "Sextus Empiricus" §3.4, "Ancient Skepticism" §4.3–4.4). Barnes NOT READ. → the strongest referee
  objection to "the modes spare acting".
- Fogelin 1994 — ABSTRACT + Pasnau's review READ: ordinary knowledge only "relative to a level of scrutiny".
- Albert 1968 (dogmatic break-off) — secondary; "The Amphiboly in the Third Horn" (PhilArchive DAYTAI, 403 — NOT
  READ): the third horn conflates "terminates" with "terminates ungrounded" — CLOSE, read it.
- Acts as stopping points: Fichte (Tathandlung; two starting points, "pure selfhood and pure thinghood", theory
  cannot decide — SEP SUMMARY; Erste Einleitung NOT READ); Hintikka 1962 (performance, ABSTRACT); Wittgenstein OC
  §204 (justification ends in acting), §110; §402 NOT confirmed. None gives base-invariance.
- Construction vs postulation: Russell 1919 p.71 ("theft over honest toil"); Kant A713/B741; Brouwer; Hilbert —
  axioms define their objects, and ideal mathematics must be conservative over real statements (1926) — the
  closest ancestor of the act/posit line and of ZDescent.
- Independence: Feferman 2011 "Is CH a definite mathematical problem?" — definiteness = excluded middle holds;
  independence as evidence CH is indefinite (closest to "posit"); Hamkins 2012 multiverse (arXiv 1108.4223).
  Both ABSTRACT — read both in full (both free).
- Conservativity: Hilbert 1926; Field 1980 ("good mathematics is conservative"); Shapiro 1983 (J. Phil. 80) —
  Gödel-sentence objection: NAME THIS LIMIT. Reverse-math Π⁰₂ conservation (WKL₀ over PRA).
- Supervaluation: van Fraassen; Williamson 1994 on supertruth — "true in every completion is not knowledge in an
  unverified setting" NOT FOUND (pieces in Brouwer/Dummett, Feferman).
- Coherentism: the "alternative systems" objection (SEP "Coherentist Theories" §1) = our fork; BonJour 1985;
  Klein 1999 (infinitism).

## What is ours (as far as found)

The pieces are known; the JOIN is not found: Agrippa's horns sorted by one count 0/1/2; the constructive,
kernel-checked "exactly one reading iff a ground" and its and/or/not form; act = base-invariant vs posit = rival
base, as theorems; "two readings = on credit" in a three-valued logic; the supervaluation contrast. Claim the
combination and the proofs, never the pieces.

## To read in full before posting

1. Walicki 2009 (closed — needs the curator: library, purchase, or a request to the author).
2. Feferman 2011, Hamkins 2012 (free).
3. "The Amphiboly in the Third Horn" (PhilArchive).
4. Barnes 1990 (book), Kripke 1975, Gupta–Belnap 1993 (closed/book) — cite via SEP where not read, said so.
5. Fichte, Erste Einleitung (1797, free German text).

## Read in full, 2026-10-25 (third check)

- **Feferman**, "Is the Continuum Hypothesis a definite mathematical problem?", EFI draft 9/18/11, 26 pp.
  (math.stanford.edu/~feferman/papers/IsCHdefinite.pdf) — READ. "Definite" = excluded middle provable in a
  semi-constructive system SC-T (§3, pp. 23–25); in his own SCS+Pow CH is FORMALLY definite (concede); his ground
  for indefiniteness is that "arbitrary subsets of N" is underdetermined/vague (p. 21); the hierarchy is "posited"
  (p. 19); number theory has definite meaning (pp. 14–15, asserted, not proved); applied mathematics in W,
  conservative over PA (p. 22). No "rival models mark the posited" — that criterion is ours. PARTIAL overlap: cite
  for arithmetic-vs-posited-universe and W's conservativity.
- **Hamkins**, "The set-theoretic multiverse", RSL 5(3), 2012, arXiv:1108.4223v1 — READ. No constructed/posited
  line: constructed universes are as real as rivals (opposite polarity). CH "like a lightswitch" (p. 15) — cite
  for "independence = rival universes". COUNTER-THESIS for us: "not all models of ZFC have the same N or the same
  arithmetic truths" (p. 14); each model's N looks standard (p. 25). ⇒ OUR ACT MUST BE RESTRICTED to bounded,
  content-computed claims (our `Nat.beq` on given numerals); unbounded arithmetic (Con(ZFC)) is NOT an act in our
  sense and may itself be a posit. Say so; never claim all arithmetic is settled.
- **Day & Athos**, "The Amphiboly in the Third Horn: A Structural Equivocation in the Agrippan and Münchhausen
  Trilemmas", Zenodo 10.5281/zenodo.18888781, 2026-03-06 (PhilArchive DAYTAI, 403) — READ (Zenodo copy; same
  text assumed). Authors: Vox Day and "Claude Athos" (AI co-author); not peer-reviewed. Splits the third horn:
  "stops" (tautology) vs "no independent grounds for trust" (the damaging reading); a checked stop needs warrant
  from OUTSIDE the chain. No count, no "p because p" with two readings, no nullary act. PARTIAL (idea level): cite
  as prior work splitting the dogma horn; ours is structural (forced = one reading, computed, no outside warrant).
