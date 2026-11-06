# van der Waerden CNF (same clause order as ZLrat.vdw). Usage: vdw.py N K > f.cnf; then
# cadical --lrat=true --binary=false f.cnf f.lrat; python3 lrat2lean.py NAME N K f.lrat
import sys
def vdw(n, k=3):
    """2-colour vdW(3,k) style: no mono 3-AP in colour 1 (true) and no k-AP in colour 0... here symmetric k=3 or W(3,k): colour True avoids 3-AP, colour False avoids k-AP."""
    cl=[]
    for d in range(1,n):
        for a in range(1,n+1):
            if a+2*d<=n: cl.append([-(a), -(a+d), -(a+2*d)])
            if a+(k-1)*d<=n: cl.append([a+i*d for i in range(k)])
    return cl
n,k=int(sys.argv[1]),int(sys.argv[2])
cl=vdw(n,k)
print(f"p cnf {n} {len(cl)}")
for c in cl: print(" ".join(map(str,c)),0)
