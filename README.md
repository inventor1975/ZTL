# ZTL — Zero-Trust Logic

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21318981.svg)](https://doi.org/10.5281/zenodo.21318981)

A logic built on one principle: **truth is never granted on credit**.
Verdicts are always two-valued (T/F); the third symbol Z (zero-trust,
"truth not earned") is a mark on an unverified input: it never produces
T unless T is forced under every classical reading of the unverified.
Default deny, ported from security into truth tables; the three-symbol
tables are the working calculator of this policy (ontological passport —
preprint, §10).

Highlights: machine-checked core in Lean 4 with **zero axioms** (no
propext, no Quot.sound, no choice), including a certified tableau engine
(soundness + completeness) and a native-rules engine proven equivalent;
an algebraic passport — expressive completeness of the external layer,
a definable implication with a two-way deduction theorem, Craig
interpolation, machine-checked cut admissibility, and the Blok–Pigozzi
conditions verified on the matrix (**ZTL is algebraizable**, yet not
self-extensional); measured bridges to six
independent engineering traditions — IEEE NaN, SQL NULL, taint
tracking/IFC, abstract interpretation, imprecise probabilities,
provenance semirings; quarantine treatment of the liar, Curry, Yablo
and Russell (containment instead of explosion); verdicts carry a
stability warranty (local answer + supervaluational guarantee).

Honest pedigree: functionally ZTL is a fragment of the external layer of
Bochvar's B3 (1938); the {¬,∧,∨} core falls in the 8Kb* class. What is
ours: the implication floor (a 7-cell delta, outside the
Rosser–Turquette standardness conditions), the generating principle, and
the two-register quarantine theorem.

Run (Python 3, no dependencies):

```
python3 ztl.py         # tables + verification of the anchor axioms
python3 audit.py       # identity audit: alive/fallen laws, MP, greediness
python3 entailment.py  # entailment ⊨: rules vs laws, deduction theorem
python3 tableau.py     # calculus: signed tableaux + check against ⊨ (2462 pairs)
python3 quantifiers.py # quantifiers: strict witnesses, UI/EG asymmetry
python3 tableau_fo.py  # quantifier tableaux + check against enumeration (28 pairs)
python3 paradoxes.py   # liar, carousel, avenger
python3 fixedpoint.py  # quarantine as a fixed point, two registers
python3 zalgebra.py    # algebraic passport: J-operators, DDT for E, Blok–Pigozzi
python3 zinterp.py     # Craig interpolation via expressive completeness
python3 zsequent.py    # sequent reading: cut admissibility (semantic cut elimination)
python3 zfo.py         # first order over arbitrary domains: parameter tableaux
python3 zpassport.py   # quarantine passport: paradox / underdetermined / input
python3 bridge.py      # the stitch: 141 answers, Python against the Lean kernel
python3 zquasi.py      # quasivariety recon: SI generator, clone theorem, Plonka probe
python3 zipc.py        # the delta against intuitionism: G4ip vs the keel, incomparability
python3 zopsets.py     # operational sets (VR Part II): witnessed identity as ZTL atoms
python3 zchoice.py     # choice sequences (VR Part II): the stage court = lawless supervaluation
python3 zzhegalkin.py  # Zhegalkin: the {∧,⊕} basis survives entirely, the GF(2) ring falls
cd lean && lake build  # machine check of the core: zero axioms
```

Full regression: `python3 run_all.py` (33 stands + Lean build).

**ZTLStudio** (`tool/`): a local studio — a human states a paradox or
a claim in natural language, the AI only *translates* (negotiated
understanding → ZFL, the Zero-trust Formal Language, with a
deterministic Russian back-reading as the non-hallucinating auditor and
a validator-driven repair loop), and the measured ZTL core *judges*:
verdicts with warranties, quarantine passports, stipulation options.
`python3 tool/ztlstudio.py` → http://localhost:8190 (no dependencies;
without GROQ_API_KEY it runs in pro mode — write ZFL by hand).

The specification and all design decisions are in `SPEC.md`; the
preprint is `paper/ZTL-draft.md` — **published on Zenodo, latest v1.1
(§19 corrected: the warranty is a two-grade ladder); concept DOI
[10.5281/zenodo.21318981](https://doi.org/10.5281/zenodo.21318981)
always resolves to the latest version** (v1.0:
[10.5281/zenodo.21318982](https://doi.org/10.5281/zenodo.21318982);
text CC BY 4.0, code MIT). **Formalization blueprint**
(theorem map with dependency graph):
https://inventor1975.github.io/ZTL/

The project originated on 2026-07-10 from an analysis of the liar
paradox; its shipyard predecessor is VSPL (a temporal paraconsistent
logic of streams). License: MIT.

*AI participation: designed and written in a dialogue between the
curator (Vitaly Reznik) and Claude (Anthropic); all fork decisions are
the curator's.*
