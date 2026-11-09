# -*- coding: utf-8 -*-
"""
zpy — ZTL AS A LAYER OF PYTHON, for code that an AI writes (2026-11-09, pilot).

THE CURATOR (2026-11-09): «Мы, люди, уже не будем писать код… Я бы хотел разработать первый язык для ИИ. И да, можно
на питоне слой сделать.» Settled in words first (the same evening), then built. What it is:

  1. A VALUE WITH ITS GROUND. A truth is not `True`; it is a claim over named facts, each EARNED (with what it was
     checked by), ON CREDIT (with whose word), or UNKNOWN — the same three the connector's warrant-form carries
     (connector/warrant.py) and the stand reports. Credit is fail-closed: the kernel reads it as Z, as the connector
     does; the claimed value is kept for the report.
  2. ONE REFUSAL. "I will not answer" is a value of its own (`Refusal`: why, and what would let it answer) — never
     `None`, never `False`. It replaces the three spellings the kernel grew (`{"refused": ...}` in zreach, `None` /
     "undetermined" in zverify, "отказ" in zbackward) at the layer's surface; the kernel itself is not touched.
  3. NO SILENT DECISION. `bool()` of a claim or a refusal RAISES (`Undecided`): `if claim:` does not run. A decision
     is written out — `decide(claim, earned=..., refuted=..., otherwise=...)`, three branches — or reads the cautious
     default by name: `claim.earned()` is True only for EARNED.
  4. CONNECTIVES BY ZTL'S TABLES. `&`, `|`, `~`, `.implies()`, `.xor()` build the formula; the verdict is ztljudge's
     (EARNED / ON CREDIT / OPEN / REFUTED / IF STABLE / E), computed by the kernel, not by this file.

WHAT IS PROVED UNDER IT, AND WHAT IS NOT. Under the connectives: the kernel's theorems (ZTL agrees with classical
logic on verified data — ClassicalAgreement.evalF_agrees; NoGift; ZReach). The layer's OWN rules — that `bool()`
raises, that a decision has three branches — are DESIGN, not theorems; what ZTL means for loops and mutable state
is not settled (said, not hidden). The checker for code written with it is zpy_lint.py.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from ztl import T, F, Z                     # noqa: E402

RESERVED = {"T", "F", "Z", "Tr", "not", "and", "or", "imp", "xor", "xnor"}   # as connector/warrant.RESERVED_NAMES


class Undecided(TypeError):
    """A claim or a refusal was used as a Python bool: a decision taken silently. Write it out."""


# ------------------------------------------------------------------------------------------------ grounds and facts
class Ground:
    __slots__ = ("kind", "by", "value")

    def __init__(self, kind, by, value):
        self.kind, self.by, self.value = kind, by, value      # kind: "earned" / "credit" / "unknown"

    def __repr__(self):
        v = {True: "T", False: "F", None: "?"}[self.value]
        return f"{self.kind}:{v}" + (f" by {self.by!r}" if self.by else "")


def _name(name):
    if not isinstance(name, str) or not name.isidentifier() or name in RESERVED:
        raise ValueError(f"zpy: {name!r} cannot name a fact (an identifier, not one of {sorted(RESERVED)})")
    return name


def fact(name, value, *, by):
    """A fact CHECKED: `by` says by what (a test, a measurement, a document). Empty `by` is refused."""
    if not by:
        raise ValueError(f"zpy: fact {name!r} without `by` — an earned value names what earned it")
    return Claim(_name(name), {name: T if value else F}, {name: Ground("earned", by, bool(value))})


def credit(name, value, *, source):
    """A value taken on someone's WORD: kept for the report, read by the kernel as Z (fail-closed)."""
    return Claim(_name(name), {name: Z}, {name: Ground("credit", source, bool(value))})


def unknown(name):
    """A fact nobody has checked or vouched for."""
    return Claim(_name(name), {name: Z}, {name: Ground("unknown", None, None)})


# ------------------------------------------------------------------------------------------------ claims
class Claim:
    """A formula over facts. Its verdict is the kernel's (ztljudge.judge), computed once and cached."""
    __slots__ = ("text", "marking", "grounds", "_v")
    __hash__ = None

    def __init__(self, text, marking, grounds):
        self.text, self.marking, self.grounds, self._v = text, marking, grounds, None

    def _join(self, other, op):
        if not isinstance(other, Claim):
            raise TypeError(f"zpy: a claim combines with a claim, not with {type(other).__name__} "
                            f"(a bare bool has no ground — make it fact(...) / credit(...) / unknown(...))")
        for n in set(self.grounds) & set(other.grounds):
            g1, g2 = self.grounds[n], other.grounds[n]
            if (g1.kind, g1.value) != (g2.kind, g2.value):
                raise ValueError(f"zpy: fact {n!r} with two grounds ({g1} / {g2})")
        return Claim(f"({self.text} {op} {other.text})", {**self.marking, **other.marking},
                     {**self.grounds, **other.grounds})

    def __and__(self, other):
        return self._join(other, "&")

    def __or__(self, other):
        return self._join(other, "|")

    def __invert__(self):
        return Claim(f"~{self.text}" if self.text.isidentifier() else f"~({self.text})", self.marking, self.grounds)

    def implies(self, other):
        return self._join(other, "->")

    def xor(self, other):
        return self._join(other, "^")

    def __bool__(self):
        raise Undecided(f"zpy: `if` on the claim {self.text!r} decides silently — use decide(claim, earned=..., "
                        f"refuted=..., otherwise=...) or claim.earned()")

    def __eq__(self, other):
        raise Undecided("zpy: `==` on a claim compares Python objects, not verdicts — read claim.disposition")

    # ---- reading the verdict
    def verdict(self, budget=None):
        if self._v is None:
            import ztljudge
            self._v = ztljudge.judge(self.text, dict(self.marking), budget)
        return self._v

    @property
    def disposition(self):
        return self.verdict()["disposition"]

    def earned(self):
        """The cautious default, BY NAME: True only when the claim is EARNED."""
        return self.disposition == "EARNED"

    def refuted(self):
        return self.disposition == "REFUTED"

    def report(self):
        """The verdict with each fact's ground: what to check, and on whose word the rest stands."""
        v = self.verdict()
        return {"claim": self.text, "disposition": v["disposition"], "why": v["why"],
                "grounds": {n: repr(g) for n, g in sorted(self.grounds.items())}}

    def __repr__(self):
        return f"Claim({self.text!r})"


def decide(claim, *, earned, refuted, otherwise):
    """THE THREE BRANCHES, all required. Each is a value or a callable; a callable gets the verdict dict.
    EARNED -> earned; REFUTED -> refuted; everything else (ON CREDIT, OPEN, IF STABLE, E) -> otherwise."""
    if not isinstance(claim, Claim):
        raise TypeError(f"zpy.decide: a Claim, not {type(claim).__name__}")
    v = claim.verdict()
    branch = {"EARNED": earned, "REFUTED": refuted}.get(v["disposition"], otherwise)
    return branch(v) if callable(branch) else branch


# ------------------------------------------------------------------------------------------------ the one refusal
class Refusal:
    """'I will not answer' as a value: why, and what would let it answer. Not None, not False — and not a bool."""
    __slots__ = ("why", "needs", "source")
    __hash__ = None

    def __init__(self, why, needs=None, source=None):
        self.why, self.needs, self.source = why, needs, source

    def __bool__(self):
        raise Undecided(f"zpy: a refusal ({self.why}) used as a bool — test it with is_refusal(x)")

    def __eq__(self, other):
        raise Undecided("zpy: `==` on a refusal — test it with is_refusal(x)")

    def __repr__(self):
        return f"Refusal({self.why!r}" + (f", needs={self.needs!r}" if self.needs else "") + ")"


def is_refusal(x):
    return isinstance(x, Refusal)


# ------------------------------------------------------------------------------------------------ the pilot: the kernel's three spellings, one at the surface
def stable(phi, marking, budget=None):
    """zverify.stable_bit: True / False, or a Refusal where it answers None."""
    import zverify
    r = zverify.stable_bit(phi, marking, budget)
    return Refusal("the completions were not walked: over the budget, and the exact pass refused",
                   needs="a larger budget", source="zverify.stable_bit") if r is None else r


def hereditary(phi, marking, budget=None):
    """zverify.hereditary_bit: True / False, or a Refusal where it answers None."""
    import zverify
    r = zverify.hereditary_bit(phi, marking, budget)
    return Refusal("the refinements were not walked: over the budget, and the exact pass refused",
                   needs="a larger budget", source="zverify.hereditary_bit") if r is None else r


def grade(phi, marking, budget=None):
    """zverify.grade: the grade, or a Refusal for "undetermined"."""
    import zverify
    g = zverify.grade(phi, marking, budget)
    return Refusal("no grade can be named within the budget", needs="a larger budget",
                   source="zverify.grade") if g == "undetermined" else g


def reach(phi, marking, mode="completion"):
    """zreach.reach: {values, witness}, or a Refusal for {"refused": ...}."""
    import zreach
    r = zreach.reach(phi, marking, mode)
    return Refusal(r["refused"], needs="fewer shared atoms at one node", source="zreach.reach") \
        if "refused" in r else r


def backward(phi, marking, target, **kw):
    """zbackward.backward: the families, or a Refusal where it refused ("отказ") or cut its search (flags None)."""
    import zbackward
    r = zbackward.backward(phi, marking, target, **kw)
    if r.get("отказ"):
        return Refusal(r["отказ"], needs="a narrower marking or a raised cap", source="zbackward.backward")
    if r.get("possible_none") is None and not r.get("already"):
        return Refusal(r.get("не_искал_дальше", "the search was cut"), needs="a larger max_k",
                       source="zbackward.backward")
    return r
