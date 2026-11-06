"""LRAT (text, CaDiCaL) -> Lean list of ZLrat.Step. Usage: lrat2lean.py NAME N K proof.lrat"""
import sys
name, N, K, path = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
lit = lambda x: f"p {x}" if x > 0 else f"n {-x}"
steps = []
for line in open(path):
    t = line.split()
    if not t: continue
    if t[1] == 'd':
        ids = [int(x) for x in t[2:-1]]
        steps.append(f".del [{', '.join(map(str, ids))}]")
    else:
        i = int(t[0]); z = t.index('0', 1)
        lits = [int(x) for x in t[1:z]]; hints = [int(x) for x in t[z+1:-1]]
        if any(h < 0 for h in hints): sys.exit("RAT hint: not supported")
        steps.append(f".add {i} [{', '.join(lit(x) for x in lits)}] [{', '.join(map(str, hints))}]")
print(f"def {name}_cert : List Step := [\n  " + ",\n  ".join(steps) + "]")
print(f"theorem {name}_unsat : ∀ a : Nat → Bool, fsat a (vdw {N} {K}) = false :=\n  check_sound (vdw {N} {K}) {name}_cert (by decide +kernel)")
print(f"#print axioms {name}_unsat")
