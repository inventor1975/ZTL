Version 2.1.5 proves a dominance theorem (Lean, module ZDirty.lean, empty axiom list). The criterion is that a grant is right iff the dirty reading earns it. Under it, the verdict the ZTL judge calls EARNED (T now and under every refinement of the dirty atoms) is right wherever any classical substitution of the dirty atoms is right, whether uniform, like "dirty := false", or chosen atom by atom. It is also right on questions where each substitution is wrong. The judge can still be wrong (¬(p ∧ ¬p)), but then every substitution is wrong too. The matrix alone does not dominate (¬¬p), so the withdrawal in 2.1.4 of the older claim, which was made of the matrix, stands. 2.1.5 also proves that the dirty reading, taken as a semantics, is exactly strong Kleene logic, and that each ZTL connective is strong Kleene followed by the assertion operator.

Version 2.1.4 corrected 2.1.3. The tables ¬(a∧b), ¬(a∨b), ¬(a⊕b) and ¬(a→b) are compositions, not lifts, and are not Sheffer's stroke or Peirce's arrow (found by the author). The claim that no conservative default exists was withdrawn. The sink example depends on the form of the rule. Version notes are now in a Version history at the end of the PDF.

ZTL (Zero-Trust Logic) is a propositional logic for dirty data: parameters owned by another system, which may change them between two reads, so each occurrence of a dirty atom is read on its own. Atoms take three values, T, F and Z (dirty). Each connective returns T only if T is forced under every classical reading of its dirty arguments, and F otherwise, so no compound takes Z. The guarantee is per connective: a negation applied to a compound's F can yield T where not every reading supports it (¬¬p with p dirty), and the judge's heredity check is what catches this.

Proved in Lean, on the empty axiom list:
- On clean data ZTL is classical logic (evalF_agrees), and every ZTL validity is a classical tautology (ztl_taut_is_classical).
- No compound takes Z (evalF_classical).
- The dirty reading is strong Kleene logic (rd_is_kleene).
- Every F of ZTL is witnessed by a reading of the dirty occurrences (refusal_witnessed).
- Dominance of the earned verdict (earned_of_kleene, substitution_of_earned, strict_any).
- ¬¬p ⊨ p fails in ZTL and holds in every matrix whose negation is involutive (signature).
- Where no dirty atom stands under a negation, a T survives every cleaning (no_gift).

Measured, on stated finite pools:
- In the census of twenty-six classical laws, twelve hold on a dirty atom and fourteen are refuted with a witness.
- ZTL differs from Bochvar's external connectives in seven or eight cells, depending on the convention for external negation.

The repository holds 2,627 theorems across 144 modules, all on the empty axiom list.

Code, Lean sources and regression: https://github.com/inventor1975/ZTL

Prepared with Claude (Anthropic; Fable 5.1 and Opus 5.5) under the direction of the author, Vitaly Reznik, who bears the responsibility for the content.
