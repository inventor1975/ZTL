# -*- coding: utf-8 -*-
"""(A) Measure-not-guess: reconcile our single 18-cage with Finn's TWO
pre-complete classes B3ex,¬ and B3ex,−. Uses ZTL's own greedy lift (ztl.lift2).

Finn (Studia Logica 33:2, 1974, Remark 1): the external class B3ex has 7
maximal classes = 5 lifted Post classes + B3ex,¬ = [{¬x1 ∩̇ ¬x2}] and
B3ex,− = [{x̄1 ∩̇ x̄2}].  ¬ = J0 = "is-false" detector; ∩̇ = internal
(Z-infectious) conjunction. x̄ = "two-valued negation" (paywalled defn).
"""
from itertools import product
from ztl import T, F, Z, VALUES, lift2

# --- our greedy champions (lifts of the Boolean kernels) ---
znand = lift2(lambda a, b: T if not (a == T and b == T) else F)
znor  = lift2(lambda a, b: T if not (a == T or b == T) else F)

# --- Finn's building blocks ---
def J0(x):            # ¬ = external "is-false": 2 iff x=0  → here T iff x=F
    return T if x == F else F
def internal_and(a, b):   # ∩̇ : Bochvar internal conj, middle Z is infectious
    if a == Z or b == Z:
        return Z
    return T if (a == T and b == T) else F

# Finn's B3ex,¬ generator: ¬x1 ∩̇ ¬x2  (J0 outputs only {T,F}, so ∩̇ acts classically)
def finn_nor(x, y):   return internal_and(J0(x), J0(y))

# A candidate for the OTHER negation x̄ that is external yet differs on Z:
# "not-true" detector  (T iff x != T), i.e. treats Z as satisfying the negation.
def notTrue(x):       return T if x != T else F
def finn_nand_cand(x, y): return internal_and(notTrue(x), notTrue(y))

def table(op):
    return tuple(op(a, b) for a in VALUES for b in VALUES)

def show(name, op):
    t = table(op)
    print(f"  {name:12} = {t}")
    return t

print("=== our greedy champions (9 cells, input order (a,b) over T,F,Z) ===")
t_nand = show("znand", znand)
t_nor  = show("znor",  znor)
print("=== Finn's named generators ===")
t_fnor = show("¬x∩̇¬x", finn_nor)
t_fnand= show("x̄∩̇x̄?",  finn_nand_cand)

print("\n=== identity checks ===")
print(f"  znor  == ¬x∩̇¬x  (Finn B3ex,¬ gen) : {t_nor == t_fnor}")
print(f"  znand == ¬x∩̇¬x                     : {t_nand == t_fnor}")
print(f"  znand == x̄∩̇x̄? (not-true variant)  : {t_nand == t_fnand}")
print(f"  finn_nand_cand outputs only T/F?   : {all(v in (T, F) for v in t_fnand)}")

# --- clone closure by a single binary op over {projX, projY, cT, cF} ---
IDX = list(product(VALUES, repeat=2))           # 9 input rows
projX = tuple(a for a, b in IDX)
projY = tuple(b for a, b in IDX)
cT, cF = (T,)*9, (F,)*9

def clone_of(op):
    gens = {projX, projY, cT, cF}
    seen = set(gens)
    frontier = list(gens)
    while frontier:
        nf = []
        cur = list(seen)
        for u in cur:
            for v in cur:
                w = tuple(op(u[i], v[i]) for i in range(9))
                if w not in seen:
                    seen.add(w); nf.append(w)
        frontier = nf
    return seen

c_nand = clone_of(znand)
c_nor  = clone_of(znor)
c_fnand= clone_of(finn_nand_cand)
zand_t = table(lift2(lambda a, b: T if (a == T and b == T) else F))
zor_t  = table(lift2(lambda a, b: T if (a == T or  b == T) else F))

print("\n=== clones (single-operator, over projections+constants) ===")
print(f"  |[znand]|           = {len(c_nand)}")
print(f"  |[znor]|            = {len(c_nor)}")
print(f"  [znand] == [znor]   : {c_nand == c_nor}   <-- our SINGLE cage")
print(f"  AND-table in [znand]: {zand_t in c_nand}   (should be False: NAND can't rebuild ∧)")
print(f"  OR-table  in [znand]: {zor_t  in c_nand}")
print(f"  |[x̄∩̇x̄ variant]|    = {len(c_fnand)}")
print(f"  [x̄variant] == [znand]: {c_fnand == c_nand}   <-- a DIFFERENT class?")
