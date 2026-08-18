# Boundary-Relative Context Closure — frozen before the bench exists

2026-08-18, ~23:10. Written before a line of the bench, not edited afterwards.

## The claim under test, frozen

> **Boundary-Relative Context Closure.** Given a declared finite completion
> boundary `B`, a partially disclosed claim is warranted as `T` iff the claim
> remains `T` under every admissible substitution of each undisclosed `Z`
> within `B`:
>
>     CC_B(q, D) = T  ⟺  ∀ σ ∈ Subs_B(Z_D) : eval(q, σ) = T

The index `B` stays. Not closure in general — closure relative to a declared
boundary. Agrippa then does not refute the result; he fixes its outer limit.

**Hard constraint from the curator, and it is the whole point:** the ZTL core
is not modified. If the property needs a change of semantics the contribution
is weaker. A test harness around an unchanged `ztl.py` shows the property was
already in the kernel.

## The gap I must measure, named before running

The frozen formula substitutes a value for an **atom**. ZTL substitutes each
**occurrence** independently — that is the generating principle, and it is why
`Z ∨ Z = F`. The two are not the same quantifier, and the corpus already knows
a witness: `q = b ∨ ¬b` with `b` undisclosed gives `T` under every atom
substitution and `F` under ZTL.

So the bench must decide which of these holds, over an enumeration rather than
by argument:

**P1 — SOUNDNESS: there is no formula where ZTL says `T` and closure says `F`.**
Reason it should hold: atom substitutions are a subset of occurrence
substitutions, so forcing `T` under the larger set forces it under the smaller.
If a counterexample appears, ZTL is *not* a conservative approximation of
closure and the whole exhibit must be rethought — that finding would matter
more than the bench.

**P2 — INCOMPLETENESS: there are formulas where ZTL says `F` and closure says
`T`.** Minimal witness expected: `b ∨ ¬b`.

**P3 — the rate of divergence** over an enumeration of formulas of depth ≤ 2
with one hidden atom: **10–25%**. Cut-off both ways: above 40% I do not
understand what I am enumerating and must re-read before reporting; below 2%
the divergence is a curiosity rather than a boundary and should be reported as
such.

**P4 — the four demonstration cases behave as the curator specified:** full
disclosure `T`; immaterial concealment `T` with a hidden atom present; material
concealment loses `T` while every cryptographic check still passes; two
declared boundaries over one disclosure give two different closure results.

**P5 — case 3 will produce `F`, not `Z`.** The verdict is two-valued; a hidden
material ground does not leave the claim "unknown", it leaves it unwarranted.
Worth predicting because the paper will want to say "loses warrant", and the
honest phrase depends on which value comes out.

## What the bench cannot show, stated now

It cannot show that the boundary `B` is the right boundary. It cannot detect a
dependency the formalizer never encoded — that is the second adversary
(dishonest formalizer), and no harness over a committed graph reaches him.
Both limits go into the result, not into a later erratum.
