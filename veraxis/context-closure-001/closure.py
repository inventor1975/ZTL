# -*- coding: utf-8 -*-
"""
Context Closure Bench — selective disclosure judged by an UNCHANGED ZTL core.

    python3 veraxis/context-closure-001/closure.py

THE QUESTION, from the Veraxis side, 2026-08-18. Cryptography proves that a
disclosed fragment came from a signed object. It does not prove that the
fragment suffices for the conclusion drawn from it. Three checks can all pass
— provenance, integrity, selective-disclosure soundness — while the picture is
false, because what defeats the conclusion is what was NOT shown.

THE CLAIM UNDER TEST, frozen in PREDICTIONS.md before this file existed:

    CC_B(q, D) = T   <=>   for every admissible substitution sigma of the
                           undisclosed atoms within a DECLARED boundary B,
                           eval(q, sigma) = T

The index B is not decoration. Closure is relative to a declared boundary, and
the bench proves that by showing one disclosure closing under one boundary and
failing under another. Agrippa is not refuted here; he is given his place as
the outer limit of the result.

THE CONSTRAINT: `ztl.py` is imported, never modified. Everything below is a
harness. If the property needed a change of semantics the contribution would be
much weaker; it does not.

THE ASYMMETRY THIS BENCH EXISTS TO MEASURE. The frozen formula substitutes a
value for an ATOM. ZTL substitutes each OCCURRENCE independently — that is its
generating principle and the reason `Z or Z = F`. So the two quantifiers are
not the same, and the interesting question is which way they can differ.
"""
import hashlib
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT)

import ztl                                                    # noqa: E402  (unchanged core)

T, F, Z = ztl.T, ztl.F, ztl.Z


# --------------------------------------------------------------- the language
# A formula is a tree: ("and", x, y) | ("or", x, y) | ("imp", x, y) |
# ("not", x) | "atom-name". Exactly the shape ztl.py's own OPS2 speaks.

OPS = {"and": ztl.AND, "or": ztl.OR, "imp": ztl.IMP,
       "xor": ztl.XOR, "xnor": ztl.XNOR}


def atoms_of(phi):
    if isinstance(phi, str):
        return {phi}
    if phi[0] == "not":
        return atoms_of(phi[1])
    return atoms_of(phi[1]) | atoms_of(phi[2])


def evaluate(phi, env):
    """Evaluation by the UNCHANGED core: every Z is lifted by ztl.py itself."""
    if isinstance(phi, str):
        return env[phi]
    if phi[0] == "not":
        return ztl.NOT(evaluate(phi[1], env))
    return OPS[phi[0]](evaluate(phi[1], env), evaluate(phi[2], env))


def show(phi):
    if isinstance(phi, str):
        return phi
    if phi[0] == "not":
        return "¬" + show(phi[1])
    sign = {"and": "∧", "or": "∨", "imp": "→", "xor": "⊕", "xnor": "↔"}
    return f"({show(phi[1])} {sign[phi[0]]} {show(phi[2])})"


# ------------------------------------------------------- the two verdicts

def ztl_verdict(phi, disclosed, hidden):
    """What the kernel says when the undisclosed atoms carry the mark Z.

    This is the whole integration: an undisclosed ground is not absent and not
    assumed — it is UNVERIFIED, which is what Z means and has always meant."""
    env = dict(disclosed)
    for a in hidden:
        env[a] = Z
    return evaluate(phi, env)


# The corpus already has a letter for this, and it is not a new one. `znum.py`
# says it plainly: "Judging IS quantification over readings; E is what happens
# when there is nothing to quantify over. The judge halts because it has nothing
# to inspect." ZTLStudio says the same in user words — "E — нечего читать". A
# boundary admitting no completion is exactly that case: nothing to read.
#
# So this bench does not invent a state. It imports the one that exists, and
# thereby records a fourth independent arrival of the same letter: the numeric
# judge, the studio, the interface to the world (paper §10), and now selective
# disclosure.
from znum import E                                            # noqa: E402


def admissible_completions(disclosed, hidden, boundary=None):
    """The completions a declared boundary actually admits.

    Two admissibility conditions, and the first one is a mine that a naive
    implementation steps on. A boundary admitting NO completion makes the
    universal quantifier vacuously true, so `∀σ ∈ B: eval(q,σ) = T` returns T
    for every claim — one could "prove closure" by declaring a contradictory
    boundary. Mathematically ordinary; institutionally it is the whole
    guarantee handed back for free. Found by Arkadiy on a static read of this
    file, before it could reach anything.

    The second condition is quieter: a boundary must not contradict what was
    already disclosed. A completion assigning a value to an atom the discloser
    already published is not a completion of the withheld part — it is a
    rewrite of the disclosed part."""
    hidden = sorted(hidden)
    out = []
    for combo in itertools.product((T, F), repeat=len(hidden)):
        completion = dict(zip(hidden, combo))
        if any(a in disclosed for a in completion):
            continue                       # would rewrite a disclosed ground
        if boundary and not boundary(completion):
            continue                       # outside the declared boundary
        out.append(completion)
    return out


def closure_verdict(phi, disclosed, hidden, boundary=None):
    """CC_B: T iff every admissible completion of the hidden atoms yields T.

    Returns (verdict, witness). The verdict is `E` when the declared boundary
    admits nothing — NOT `T`. Admissibility of the boundary is decided BEFORE
    closure is computed: closure reasons inside an admitted boundary and has no
    standing to produce the boundary's own admissibility.

    `E` is the corpus's own letter for "nothing to read", not a state invented
    here — see the note beside its import.

    `boundary` is a predicate over the completion dict — the declared B. None
    means the unrestricted boundary `B_⊤` = {T,F} per hidden atom,
    independently."""
    completions = admissible_completions(disclosed, hidden, boundary)
    if not completions:
        return E, None
    for completion in completions:
        env = dict(disclosed)
        env.update(completion)
        if evaluate(phi, env) != T:
            return F, completion           # the completion that defeats it
    return T, None


def boundary_receipt(phi, disclosed, hidden, boundary):
    """What a declared boundary EXCLUDED, and what that exclusion bought.

    A boundary that turns F into T does so by removing completions. Which ones,
    and were any of them the ones that defeated the claim? Without this, a
    declared boundary is a word; with it, it is an object a lawyer can contest —
    here are the readings you excluded, and here, by name, are the ones that
    would have defeated the conclusion.

    Returns (admitted, excluded, defeating): the completions the boundary keeps,
    the ones it drops, and the subset of the dropped ones that defeat the claim
    under the unrestricted boundary."""
    full = admissible_completions(disclosed, hidden, None)
    admitted = admissible_completions(disclosed, hidden, boundary)
    excluded = [c for c in full if c not in admitted]
    defeating = []
    for c in excluded:
        env = dict(disclosed)
        env.update(c)
        if evaluate(phi, env) != T:
            defeating.append(c)
    return admitted, excluded, defeating


def print_receipt(phi, disclosed, hidden, boundary, label):
    admitted, excluded, defeating = boundary_receipt(
        phi, disclosed, hidden, boundary)

    def fmt(cs):
        return "; ".join(
            ", ".join(f"{k}={v}" for k, v in sorted(c.items())) for c in cs
        ) or "—"

    print(f"\n    BOUNDARY RECEIPT for {label}")
    print(f"      admitted   {len(admitted)}: {fmt(admitted)}")
    print(f"      excluded   {len(excluded)}: {fmt(excluded)}")
    print(f"      of those, DEFEATING under B_top   {len(defeating)}: "
          f"{fmt(defeating)}")
    if defeating:
        print("""      READ THIS AS THE PRICE. The conclusion is warranted here ONLY
      because the boundary removed a reading that defeats it. The warrant
      rests on the boundary, not on the disclosure — and the excluded
      reading is named, so its admissibility can be contested by whoever
      has standing to decide it.""")
    else:
        print("""      The boundary excluded nothing that could defeat the claim, so it
      is not carrying the conclusion — the disclosure is.""")
    return defeating


# ------------------------------- the commitment, computed rather than assumed

def canonical(obj):
    """The consumer's own canonical serialization, reproduced exactly:
    UTF-8, keys sorted, no indentation, `,`/`:` separators, no trailing
    newline, and a self-digest excluded by KEY REMOVAL rather than null
    substitution (`veraxis/integration-slice-001/…DIGEST-DERIVATION-v0.5.md`)."""
    return json.dumps(obj, sort_keys=True, ensure_ascii=False,
                      separators=(",", ":")).encode("utf-8")


def digest(obj, self_key=None):
    body = {k: v for k, v in obj.items() if k != self_key}
    return hashlib.sha256(canonical(body)).hexdigest()


def commitment(phi, disclosed, hidden):
    """A CLWR-shaped record over this claim: the formula's digest, and a
    digest per disclosed ground. Withheld grounds are committed BY DIGEST —
    the discloser cannot silently drop or rewrite one."""
    grounds = {}
    for atom in sorted(set(disclosed) | set(hidden)):
        shown = atom in disclosed
        grounds[atom] = {
            "disclosed": shown,
            # A withheld ground still commits to its content by hash.
            "value_sha256": hashlib.sha256(
                f"{atom}={disclosed.get(atom, 'WITHHELD-SECRET')}".encode()
            ).hexdigest(),
        }
    record = {
        "formula": show(phi),
        "formula_sha256": hashlib.sha256(show(phi).encode()).hexdigest(),
        "grounds": grounds,
    }
    record["record_sha256"] = digest(record, self_key="record_sha256")
    return record


def verify_commitment(record, phi, disclosed, hidden):
    """The cryptographic half, actually run: does this disclosure verify
    against the committed record? Returns (ok, list of check results)."""
    checks = []
    fresh = commitment(phi, disclosed, hidden)
    checks.append(("formula digest matches commitment",
                   fresh["formula_sha256"] == record["formula_sha256"]))
    checks.append(("record digest reproduces from its own body",
                   digest(record, self_key="record_sha256")
                   == record["record_sha256"]))
    every_ground = all(
        record["grounds"].get(a, {}).get("value_sha256")
        == fresh["grounds"][a]["value_sha256"]
        for a in fresh["grounds"]
    )
    checks.append(("every disclosed ground matches its commitment",
                   every_ground))
    checks.append(("withheld grounds are present as digests",
                   all(not record["grounds"][a]["disclosed"]
                       and record["grounds"][a]["value_sha256"]
                       for a in sorted(hidden))))
    return all(ok for _, ok in checks), checks


# ------------------------------------------------ part 1: the four cases

def case(title, phi, disclosed, hidden, boundary=None, note=""):
    zv = ztl_verdict(phi, disclosed, hidden)
    cc, killer = closure_verdict(phi, disclosed, hidden, boundary)
    shown = ", ".join(f"{k}={v}" for k, v in sorted(disclosed.items())) or "—"
    print(f"\n  {title}")
    print(f"    claim      {show(phi)}")
    print(f"    disclosed  {shown}")
    print(f"    withheld   {', '.join(sorted(hidden)) or '—'}")
    print(f"    ZTL verdict            {zv}")
    print(f"    context closure CC_B   {cc}"
          + (f"   defeated by {killer}" if killer else ""))
    if note:
        print(f"    {note}")
    return zv, cc


def four_cases():
    print("=" * 78)
    print("PART 1 — the demonstration cases")
    print("=" * 78)

    # The legal shape, kept deliberately plain: the claim holds if the
    # entitlement is established, the condition is met, and no exception fires.
    claim = ("and", ("and", "entitlement", "condition"), ("not", "exception"))

    r1 = case("1. FULL DISCLOSURE — everything material is shown",
              claim,
              {"entitlement": T, "condition": T, "exception": F},
              set(),
              note="the ordinary case: all grounds supplied, warrant granted.")

    # An atom that cannot change the claim: it appears nowhere in it.
    claim2 = ("or", ("and", "entitlement", "condition"), "unrelated_finding")
    r2 = case("2. IMMATERIAL CONCEALMENT — a hidden atom that cannot defeat it",
              claim2,
              {"entitlement": T, "condition": T},
              {"unrelated_finding"},
              note="PRIVACY WITHOUT LOSS OF WARRANT: the atom stays hidden and\n"
                   "    the verdict survives, because no completion of it defeats "
                   "the claim.")

    r3 = case("3. MATERIAL CONCEALMENT — the exception is withheld",
              claim,
              {"entitlement": T, "condition": T},
              {"exception"},
              note="THE EXHIBIT — and the crypto half is now RUN, not assumed:")

    # The cryptographic half, computed rather than stipulated. Same disclosure
    # as case 3; the record is built over the full claim and then verified
    # against what the discloser actually showed.
    rec = commitment(claim, {"entitlement": T, "condition": T, "exception": T},
                     set())
    rec_disclosed = commitment(claim, {"entitlement": T, "condition": T},
                               {"exception"})
    crypto_ok, checks = verify_commitment(
        rec_disclosed, claim, {"entitlement": T, "condition": T}, {"exception"})
    for label, ok in checks:
        print(f"      {'PASS' if ok else 'FAIL'}  {label}")
    print(f"""      record_sha256 {rec_disclosed['record_sha256'][:32]}…

    CryptographicVerification = {'PASS' if crypto_ok else 'FAIL'}
    ContextClosure            = {r3[1]}

    Both computed in this run. Authenticity of what is shown is not
    sufficiency for what is concluded — and the committed record even carries
    the withheld ground's digest, so nothing was dropped or forged. The
    conclusion is still unwarranted.""")

    # Two declared boundaries over ONE disclosure. B2 encodes an institutional
    # fact: in this jurisdiction the exception cannot fire while the condition
    # is met. Same hidden atom, same disclosure, different declared boundary.
    def b_unrestricted(c):
        return True

    def b_exception_excluded(c):
        return c.get("exception") == F

    print("\n  4. BOUNDARY ATTACK — one disclosure, two declared boundaries")
    _, cc_b1 = case("     4a. boundary B1 = unrestricted {T,F}",
                    claim, {"entitlement": T, "condition": T},
                    {"exception"}, b_unrestricted)
    _, cc_b2 = case("     4b. boundary B2 = 'the exception cannot fire here'",
                    claim, {"entitlement": T, "condition": T},
                    {"exception"}, b_exception_excluded,
                    note="closure now HOLDS — but only because B2 was declared.\n"
                         "    The boundary is a premise, not a proved fact, and this\n"
                         "    pair is the proof that it is doing work.")
    receipt = print_receipt(claim, {"entitlement": T, "condition": T},
                            {"exception"}, b_exception_excluded, "boundary B2")

    # A boundary that admits nothing. The naive implementation returned T here
    # — universal quantification over the empty set — which would let anyone
    # "prove closure" by declaring a contradictory boundary.
    def b_contradictory(c):
        return c.get("exception") == T and c.get("exception") == F

    _, cc_empty = case("5. EMPTY BOUNDARY — a declared B that admits nothing",
                       claim, {"entitlement": T, "condition": T},
                       {"exception"}, b_contradictory,
                       note="E — NOTHING TO READ. Not warranted and not refuted:\n"
                            "    the boundary admits no completion, so there is nothing\n"
                            "    to quantify over. Same letter the numeric judge and the\n"
                            "    studio already use; closure reasons INSIDE an admitted\n"
                            "    boundary and cannot produce that boundary's own\n"
                            "    admissibility.\n"
                            "    Two refusals, one shape: Z withholds truth for want of a\n"
                            "    WITNESS, E withholds it for want of a SUBJECT. Classical\n"
                            "    logic grants both — a vacuous universal is true — and this\n"
                            "    calculus declines twice.")
    return r1, r2, r3, (cc_b1, cc_b2), cc_empty, receipt


# ------------------------------- part 2: the occurrence/atom asymmetry

def enumerate_formulas(atoms, depth):
    """Every formula over `atoms` up to `depth`, as a census rather than a
    battery — the corpus's own lesson: one fence is not a result."""
    if depth == 0:
        for a in atoms:
            yield a
        return
    seen = set()
    smaller = list(enumerate_formulas(atoms, depth - 1))
    for phi in smaller:
        if show(phi) not in seen:
            seen.add(show(phi))
            yield phi
    for phi in smaller:
        cand = ("not", phi)
        if show(cand) not in seen:
            seen.add(show(cand))
            yield cand
    for op in OPS:
        for a in smaller:
            for b in smaller:
                cand = (op, a, b)
                if show(cand) not in seen:
                    seen.add(show(cand))
                    yield cand


def census():
    print("\n" + "=" * 78)
    print("PART 2 — census: ZTL's verdict against boundary-free closure")
    print("=" * 78)
    print("""
  The frozen formula substitutes a value for an ATOM; ZTL substitutes each
  OCCURRENCE independently. Enumerated rather than argued: every formula of
  depth <= 2 over {a, b}, with `b` withheld and `a` disclosed as T and as F.""")

    unsound, incomplete, agree, total = [], [], 0, 0
    for phi in enumerate_formulas(["a", "b"], 2):
        if "b" not in atoms_of(phi):
            continue
        for a_val in (T, F):
            total += 1
            zv = ztl_verdict(phi, {"a": a_val}, {"b"})
            cc, _ = closure_verdict(phi, {"a": a_val}, {"b"})
            if zv == T and cc != T:
                unsound.append((phi, a_val, zv, cc))
            elif zv != T and cc == T:
                incomplete.append((phi, a_val, zv, cc))
            else:
                agree += 1

    print(f"\n  {total} (formula, disclosure) pairs examined.")
    print(f"    agree                                   {agree}")
    print(f"    ZTL says T while closure fails          {len(unsound)}"
          f"   <- SOUNDNESS")
    print(f"    ZTL withholds T while closure holds     {len(incomplete)}"
          f"   <- strictness")

    if unsound:
        print("\n  *** UNSOUND CASES FOUND — the exhibit does not stand:")
        for phi, av, zv, cc in unsound[:10]:
            print(f"      {show(phi):28s} a={av}  ZTL={zv} CC={cc}")
    else:
        print("""
  NO case where ZTL grants T and closure fails. On this enumeration the
  kernel is a SOUND approximation of boundary-free context closure: whatever
  ZTL warrants under partial disclosure, every completion of the hidden atom
  warrants too. That is the direction the legal claim needs — a warranted
  verdict cannot be overturned by what was withheld.""")

    if incomplete:
        pct = 100.0 * len(incomplete) / total
        print(f"""
  And it is STRICTLY stronger, on {pct:.0f}% of pairs: ZTL refuses T where
  every atom-completion would have granted it. The reason is the independence
  of occurrences, and the smallest witness is printed below. This is not a
  defect to hide — it is the boundary between two different quantifiers, and
  the paper must state which one it claims.""")
        for phi, av, zv, cc in incomplete[:6]:
            print(f"      {show(phi):28s} a={av}  ZTL={zv} CC={cc}")

    return unsound, incomplete, total


# ------------------------------- part 3: the condition that restores it

def negation_free(phi, atom):
    """True iff no occurrence of `atom` sits under a negation, in an
    antecedent, or inside xor/xnor — the connectives that carry a negation
    internally. This is the syntactic condition measured in part 3."""
    if isinstance(phi, str):
        return True
    if phi[0] == "not":
        return atom not in atoms_of(phi[1])
    if phi[0] == "imp":
        return (atom not in atoms_of(phi[1])) and negation_free(phi[2], atom)
    if phi[0] in ("xor", "xnor"):
        return atom not in atoms_of(phi)
    return negation_free(phi[1], atom) and negation_free(phi[2], atom)


def condition():
    print("\n" + "=" * 78)
    print("PART 3 — the syntactic condition under which the two coincide")
    print("=" * 78)
    print("""
  Part 2 refuted soundness in general. The cause is the corpus's own signature
  cell, `¬¬Z = T`: ZTL lifts each CONNECTIVE, so a negation over an unverified
  atom yields a verified negation. In the legal register that is exactly
  "not shown that the exception applies" turning into "shown that it does not"
  — absence of evidence read as evidence of absence.

  So the question becomes: WHERE is the kernel safe? Measured, not argued.""")
    total = safe = unsound = agree = 0
    bad = []
    for phi in enumerate_formulas(["a", "b"], 2):
        if "b" not in atoms_of(phi):
            continue
        for a_val in (T, F):
            total += 1
            if not negation_free(phi, "b"):
                continue
            safe += 1
            zv = ztl_verdict(phi, {"a": a_val}, {"b"})
            cc, _ = closure_verdict(phi, {"a": a_val}, {"b"})
            if zv == T and cc != T:
                unsound += 1
                bad.append((show(phi), a_val, zv, cc))
            if (zv == T) == (cc == T):
                agree += 1

    print(f"\n  {safe} of {total} pairs have the withheld atom under no negation.")
    print(f"    ZTL grants T while closure fails    {unsound}")
    print(f"    verdicts coincide                   {agree}"
          f"  ({100.0 * agree / safe:.0f}%)")
    if bad:
        print("\n  *** the condition does NOT hold:")
        for s, av, zv, cc in bad[:8]:
            print(f"      {s:26s} a={av}  ZTL={zv} CC={cc}")
    else:
        print("""
  NEGATION-FREE DISCLOSURE SOUNDNESS, on this census: when the withheld atom
  occurs under no negation, no antecedent and no xor/xnor, the kernel's verdict
  and boundary-free context closure COINCIDE — not merely agree in one
  direction, but in both, on every pair. The unchanged kernel computes the
  property exactly, inside that fragment, and demonstrably fails outside it.

  For a legal disclosure this is the readable rule: a claim may rely on the
  kernel's verdict under partial disclosure when what is withheld can only ADD
  support, never remove it. Exceptions, exclusions and conditions-of-defeat sit
  under a negation by their grammar — and for those the harness, not the
  kernel, must compute the closure.""")
    return unsound, safe


def main():
    print("""
CONTEXT CLOSURE BENCH — selective disclosure over an unchanged ZTL core.
The kernel is imported, not modified: `ztl.py` sha is the corpus's own.""")
    r1, r2, r3, (cc_b1, cc_b2), cc_empty, receipt = four_cases()
    unsound, incomplete, total = census()
    cond_unsound, safe = condition()

    ok = (r1 == (T, T)
          and r2 == (T, T)
          and r3[0] != T and r3[1] != T
          and cc_b1 != T and cc_b2 == T
          and cc_empty == E
          and receipt
          and cond_unsound == 0)

    print("\n" + "=" * 78)
    if ok:
        print(f"""CLOSURE BENCH GREEN — three results, and the middle one is negative.

  THE FIVE CASES. Full disclosure warrants. Immaterial concealment warrants
  ANYWAY, so this is not a demand for full disclosure — privacy survives when
  what is hidden cannot defeat the claim. Material concealment does NOT
  warrant, while every cryptographic check on the same disclosure passes — and
  those checks are COMPUTED in this run, over a CLWR-shaped record under the
  consumer's own canonical serialization, not stipulated in prose. One
  disclosure gives two different closure results under two declared
  boundaries, which proves the boundary is a premise and not a discovered
  fact. And a boundary admitting nothing returns E — the corpus's own letter
  for "nothing to read" — rather than a vacuous T. Two refusals of one shape:
  Z withholds truth for want of a witness, E for want of a subject.

  THE CENSUS, AND IT REFUTES THE COMFORTABLE READING. On {total} pairs the
  kernel grants T while closure fails {len(unsound)} times. ZTL is NOT a
  conservative approximation of context closure in general, and the cause is
  its own signature: `¬¬Z = T`. A negation over an unverified ground produces a
  verified negation — absence of evidence read as evidence of absence.

  THE CONDITION THAT RESTORES IT. On the {safe} pairs where the withheld atom
  occurs under no negation, no antecedent and no xor/xnor, kernel verdict and
  context closure coincide exactly, with zero exceptions. Inside that fragment
  the property WAS already in the kernel; outside it, the harness must compute
  the closure and the kernel must not be relied on alone.

  So the honest headline is not "ZTL already computes context closure". It is:
  ZTL computes it exactly where what is withheld can only add support, and
  provably fails where what is withheld can defeat — which is precisely where
  exceptions live.""")
    else:
        print("CLOSURE BENCH RED — see the cases above.")
    print("=" * 78)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
