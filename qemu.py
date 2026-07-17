# -*- coding: utf-8 -*-
"""qemu — a textbook few-qubit emulator, stdlib only.

State vector over C^(2^n) as a plain list of complex numbers; gates as
explicit 2x2 maps; Born measurement with a seeded RNG; and the projection
lattice of ONE qubit (the subspaces of C^2) for the quantum-logic cells.

HONEST BY CONSTRUCTION: this is a CLASSICAL simulation. Its measurement
randomness is a pseudo-random generator, i.e. determinism in costume. It
demonstrates the GRAMMAR of the quantum stones — the negation fixed
point, the non-distributive lattice, the shape of the vacancy — but it
does not mint genuinely fresh bits: the theatre of the vacancy, not the
vacancy (see the will/vacancy ledger, 2026-07-16/17).
"""
import math


# ---------------------------------------------------------------- states
def zero(n):
    """|0...0> on n qubits."""
    amp = [0j] * (2 ** n)
    amp[0] = 1 + 0j
    return amp


def apply1(gate, k, amp):
    """Apply a 1-qubit gate ((a,b),(c,d)) to qubit k of the register."""
    n = len(amp)
    out = [0j] * n
    (a, b), (c, d) = gate
    step = 1 << k
    for i in range(n):
        if i & step == 0:
            j = i | step
            out[i] += a * amp[i] + b * amp[j]
            out[j] += c * amp[i] + d * amp[j]
    return out


X = ((0, 1), (1, 0))                                  # the quantum NOT
_s = 1 / math.sqrt(2)
H = ((_s, _s), (_s, -_s))                             # Hadamard


def measure(amp, k, rnd):
    """Born measurement of qubit k → (bit, collapsed state)."""
    step = 1 << k
    p1 = sum(abs(amp[i]) ** 2 for i in range(len(amp)) if i & step)
    bit = 1 if rnd.random() < p1 else 0
    norm = math.sqrt(p1 if bit else 1 - p1)
    return bit, [(amp[i] / norm
                  if ((i & step) != 0) == (bit == 1) else 0j)
                 for i in range(len(amp))]


def close(u, v, eps=1e-9):
    return max(abs(a - b) for a, b in zip(u, v)) < eps


# ------------------------------------- the projection lattice of C^2
# A subspace of C^2 is 0 ({0}), 2 (all of C^2), or ("line", ray).
def line(a, b):
    n = math.sqrt(abs(a) ** 2 + abs(b) ** 2)
    return ("line", (a / n, b / n))


def same_ray(u, v):
    ip = u[0].conjugate() * v[0] + u[1].conjugate() * v[1]
    return abs(abs(ip) - 1) < 1e-9


def meet(P, Q):
    """Intersection of subspaces — the honest, thrifty AND."""
    if P == 0 or Q == 0:
        return 0
    if P == 2:
        return Q
    if Q == 2:
        return P
    return P if same_ray(P[1], Q[1]) else 0


def join(P, Q):
    """Closed span — the generous OR: it MINTS states neither side has."""
    if P == 2 or Q == 2:
        return 2
    if P == 0:
        return Q
    if Q == 0:
        return P
    return P if same_ray(P[1], Q[1]) else 2


def dim(P):
    return 0 if P == 0 else (2 if P == 2 else 1)
