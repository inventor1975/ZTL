Version 2.1.6 changes what the ZTL judge reports. EARNED and REFUTED are now exactly strong Kleene's T and F. Where strong Kleene is silent, EARNED IF STABLE and REFUTED IF STABLE say that every cleaning of the dirty atoms (every completion by T or F) gives T, resp. F: true (false) once every dirty atom is verified, to either value. ON CREDIT and OPEN are the rest. Strong Kleene's verdict and truth in every cleaning are the compositional and the thorough semantics of three-valued model checking (Bruns and Godefroid); ZTL's verdict is the third reading. The judge's grant is classical evaluation over all completions, with the label saying which grants also hold when each occurrence is read on its own; under the criterion that a grant is right iff the dirty reading earns it, the grant is right wherever a classical substitution of the dirty atoms is right. Under that criterion every EARNED IF STABLE is a wrong grant (2,440 of 14,530 cells with a dirty atom, against 950 wrong grants of the 2.1.5 verdict); EARNED alone is never one. E marks a ground with no subject. On the regression pool the dispositions agree with brute force on all 14,530 cells with a dirty atom. 2.1.6 also adds Lean proofs, on the empty axiom list: a characterization of the lifted tables (decisive, sound, maximal: the definition of the lift restated as three properties); expressive completeness and Craig interpolation (for every entailment) in the language with constants; the solo-completeness dichotomy of the sixteen binary connectives, with constants; each disposition of the judge as a ZTL formula; the translation of ZTL into Bochvar's external logic and back.

Version 2.1.5 proves a dominance theorem (Lean, module ZDirty.lean, empty axiom list). The criterion is that a grant is right iff the dirty reading earns it. Under it, the verdict the ZTL judge then called EARNED (T now and under every refinement of the dirty atoms, a refinement verifying some of them, each to one value) is right wherever any classical substitution of the dirty atoms is right, whether uniform, like "dirty := false", or chosen atom by atom. It is also right on questions where each substitution is wrong. The judge can still be wrong (¬(p ∧ ¬p)), but then every substitution is wrong too; since 2.1.6 the judge reports that case as EARNED IF STABLE. The matrix alone does not dominate (¬¬p), so the withdrawal in 2.1.4 of the older claim, which was made of the matrix, stands. 2.1.5 also proves that the dirty reading, taken as a semantics, is exactly strong Kleene logic, and that each ZTL connective is strong Kleene followed by the assertion operator.

Version 2.1.4 corrected 2.1.3. The tables ¬(a∧b), ¬(a∨b), ¬(a⊕b) and ¬(a→b) are compositions, not lifts, and are not Sheffer's stroke or Peirce's arrow (found by the author). The claim that no conservative default exists was withdrawn. The sink example depends on the form of the rule. Version notes are now in a Version history at the end of the PDF.

ZTL (Zero-Trust Logic) is a propositional logic for dirty data: parameters owned by another system, which may change them between two reads, so each occurrence of a dirty atom is read on its own. Atoms take three values, T, F and Z (dirty). Each connective returns T only if T is forced under every classical reading of its dirty arguments, and F otherwise, so no compound takes Z. The guarantee is per connective: a negation applied to a compound's F can yield T where not every reading supports it (¬¬p with p dirty), and the judge reports such a T as ON CREDIT.

Proved in Lean, on the empty axiom list:
- On clean data ZTL is classical logic (evalF_agrees), and every ZTL validity is a classical tautology (ztl_taut_is_classical).
- No compound takes Z (evalF_classical).
- The dirty reading is strong Kleene logic (rd_is_kleene).
- Every F of ZTL is witnessed by a reading of the dirty occurrences (refusal_witnessed).
- Dominance of the earned verdict (earned_of_kleene, substitution_of_earned, strict_any).
- EARNED is exactly the strong Kleene T, REFUTED exactly the strong Kleene F (strict_earned_iff_kleene, strict_refuted_iff_kleene); the judge's grant is exactly classical evaluation over all completions (grant_iff_enum) and right wherever a classical substitution is right (grant_right_where_substitution_right).
- Characterization of the tables (lift1_characterized, lift2_characterized).
- Expressive completeness and Craig interpolation, with constants (ztl_expressively_complete, ztl_interpolation); each disposition of the judge is a ZTL formula (judge_speaks_ztl).
- ¬¬p ⊨ p fails in ZTL and holds in every matrix whose negation is involutive (signature).
- Where no dirty atom stands under a negation, a T survives every cleaning (no_gift).

Measured, on stated finite pools:
- In the census of twenty-six classical laws, twelve hold on a dirty atom and fourteen are refuted with a witness.
- ZTL differs from Bochvar's external connectives in seven or eight cells, depending on the convention for external negation.

The repository holds 2,809 theorems across 149 modules, all on the empty axiom list.

Code, Lean sources and regression: https://github.com/inventor1975/ZTL

Prepared with Claude (Anthropic; Fable 5.1 and Opus 5.5) under the direction of the author, Vitaly Reznik, who bears the responsibility for the content.
