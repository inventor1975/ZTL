Version 2.1.6 splits the judge's earned verdict in two. EARNED is now exactly the strong Kleene T, and under the criterion of the dominance theorem (a grant is right iff the dirty reading earns it) it is never a wrong grant. What is T under every refinement of the dirty atoms but not Kleene-true is reported as EARNED IF STABLE, with the dirty atoms named that must read the same at every occurrence: the only place an earned grant of the judge can be wrong. The judge flags these grants; it does not avoid them, and the dominance theorem of 2.1.5, about both together, is unchanged. REFUTED and REFUTED IF STABLE mirror them. On the regression pool the judge's EARNED and REFUTED cells coincide with strong Kleene's T and F cells (2,450 and 1,274 of 14,530 cells with a dirty atom). 2.1.6 also adds Lean proofs, on the empty axiom list: the ZTL tables are the only decisive, sound and maximal ones; ZTL is the only truth-functional semantics that gives strong Kleene's verdict on each connective applied to atoms; every function from the values of the atoms to {T, F} is a ZTL formula, and so is each disposition of the judge on a formula; Craig interpolation; exactly the four directional connectives are complete alone; the judge dominates Bochvar's external logic and classical evaluation over all completions.

Version 2.1.5 proves a dominance theorem (Lean, module ZDirty.lean, empty axiom list). The criterion is that a grant is right iff the dirty reading earns it. Under it, the verdict the ZTL judge then called EARNED (T now and under every refinement of the dirty atoms) is right wherever any classical substitution of the dirty atoms is right, whether uniform, like "dirty := false", or chosen atom by atom. It is also right on questions where each substitution is wrong. The judge can still be wrong (¬(p ∧ ¬p)), but then every substitution is wrong too; since 2.1.6 that case is reported as EARNED IF STABLE. The matrix alone does not dominate (¬¬p), so the withdrawal in 2.1.4 of the older claim, which was made of the matrix, stands. 2.1.5 also proves that the dirty reading, taken as a semantics, is exactly strong Kleene logic, and that each ZTL connective is strong Kleene followed by the assertion operator.

Version 2.1.4 corrected 2.1.3. The tables ¬(a∧b), ¬(a∨b), ¬(a⊕b) and ¬(a→b) are compositions, not lifts, and are not Sheffer's stroke or Peirce's arrow (found by the author). The claim that no conservative default exists was withdrawn. The sink example depends on the form of the rule. Version notes are now in a Version history at the end of the PDF.

ZTL (Zero-Trust Logic) is a propositional logic for dirty data: parameters owned by another system, which may change them between two reads, so each occurrence of a dirty atom is read on its own. Atoms take three values, T, F and Z (dirty). Each connective returns T only if T is forced under every classical reading of its dirty arguments, and F otherwise, so no compound takes Z. The guarantee is per connective: a negation applied to a compound's F can yield T where not every reading supports it (¬¬p with p dirty), and the judge's heredity check is what catches this.

Proved in Lean, on the empty axiom list:
- On clean data ZTL is classical logic (evalF_agrees), and every ZTL validity is a classical tautology (ztl_taut_is_classical).
- No compound takes Z (evalF_classical).
- The dirty reading is strong Kleene logic (rd_is_kleene).
- Every F of ZTL is witnessed by a reading of the dirty occurrences (refusal_witnessed).
- Dominance of the earned verdict (earned_of_kleene, substitution_of_earned, strict_any).
- EARNED is exactly the strong Kleene T, REFUTED exactly the strong Kleene F (strict_earned_iff_kleene, strict_refuted_iff_kleene).
- The tables are the only decisive, sound and maximal ones (lift1_characterized, lift2_characterized); ZTL is the only compositional extension of strong Kleene's verdict (ztl_unique_compositional).
- Expressive completeness and Craig interpolation (ztl_expressively_complete, ztl_interpolation); each disposition of the judge is a ZTL formula (judge_speaks_ztl).
- ¬¬p ⊨ p fails in ZTL and holds in every matrix whose negation is involutive (signature).
- Where no dirty atom stands under a negation, a T survives every cleaning (no_gift).

Measured, on stated finite pools:
- In the census of twenty-six classical laws, twelve hold on a dirty atom and fourteen are refuted with a witness.
- ZTL differs from Bochvar's external connectives in seven or eight cells, depending on the convention for external negation.

The repository holds 2,780 theorems across 148 modules, all on the empty axiom list.

Code, Lean sources and regression: https://github.com/inventor1975/ZTL

Prepared with Claude (Anthropic; Fable 5.1 and Opus 5.5) under the direction of the author, Vitaly Reznik, who bears the responsibility for the content.
