# ZTL — Zero-Trust Logic

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
cd lean && lake build  # machine check of the core: zero axioms
```

Full regression: `python3 run_all.py` (23 stands + Lean build).

The specification and all design decisions are in `SPEC.md`; the working
preprint draft is `paper/ZTL-draft.md`. **Formalization blueprint**
(theorem map with dependency graph):
https://inventor1975.github.io/ZTL/

The project originated on 2026-07-10 from an analysis of the liar
paradox; its shipyard predecessor is VSPL (a temporal paraconsistent
logic of streams). License: MIT.

*AI participation: designed and written in a dialogue between the
curator (Vitaly Reznik) and Claude (Anthropic); all fork decisions are
the curator's.*
