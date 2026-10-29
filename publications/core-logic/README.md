# ZTL as a logic — the journal article (in preparation)

The article positions ZTL among three-valued logics: the uniqueness of its tables, where it stands on the
standard criteria, its neighbours (strong Kleene, Bochvar's external logic) and the judge built on it.
The text is not published here until the article is.

What a reader can rerun now:

| what | how (from the repository root) |
|---|---|
| every Lean theorem the article cites, on the empty axiom list | `cd lean && lake build` |
| every theorem of the corpus, one by one | `python3 inventory/axiom_audit.py` |
| the matrix facts and the census of laws | `python3 publications/ztl/core_logic_checks.py` |
| every other number the article quotes | `python3 publications/core-logic/paper_numbers.py` |

`paper_numbers.py` also checks that each number it computes appears in the text; without the text it says
so and checks the numbers only.

Prepared with AI assistance (Claude Opus 5.5, Anthropic); human curator Vitaly Reznik.
