import sys, time
sys.path.insert(0, '.')
import mpmath as mp
print("mpmath backend:", mp.libmp.BACKEND)
import paper_side as P
import lean_side as L
from sympy import primerange

def paper_poly(n, d):
    out = {}
    for c, e in P.S_terms(n, d):
        out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c != 0}

def lean_poly(n, d):
    return {e: c for e, c in L.enumerationRHS_terms(n, d).items() if c != 0}

t = time.time()
bad = 0; cnt = 0
# polynomial identity (in sigma) between paper Thm 4.3 and Lean enumerationRHS
cases = [(n, d) for n in range(2, 61) for d in range(1, 7)]
cases += [(q, d) for q in list(primerange(3, 200)) for d in (1, 2, 3, 4, 5)]
cases += [(q + 1, d) for q in list(primerange(3, 200)) for d in (1, 2, 3, 4, 5)]
cases += [(n, d) for n in (30, 42, 210, 2000, 420, 1998) for d in (8, 12)]
for n, d in cases:
    cnt += 1
    if paper_poly(n, d) != lean_poly(n, d):
        bad += 1; print("POLY MISMATCH", n, d)
print(f"paper-vs-Lean enumeration polynomials compared: {cnt}, mismatches: {bad}")

# literal numSS (brute force over Config, IsShiftSymmetric) vs Lean enumerationRHS
bb = 0; bc = 0
for (n, d, s) in [(2,2,2),(3,2,2),(2,3,2),(4,2,2),(2,4,2),(6,1,2),(6,1,3),(12,1,2),(2,2,3),(3,2,3),(4,1,5),(10,1,2),(9,1,3),(4,1,4),(8,1,3),(15,1,2),(3,1,7),(5,1,4)]:
    b = L.numSS_brute(n, d, s); r = L.enumerationRHS(n, d, s)
    bc += 1; bb += b != r
    if b != r: print("BRUTE MISMATCH", n, d, s, b, r)
print(f"numSS brute vs Lean enumerationRHS: {bc} cases, mismatches: {bb}")
ref = {(2,2):8, (3,2):26, (5,2):182, (2,3):72, (3,3):6398, (6,2):801064}
print("Lean enumerationRHS reference values:", all(L.enumerationRHS(n,d,2)==v for (n,d),v in ref.items()))
print(f"time {time.time()-t:.1f}s")

# timing probe for the grid
t = time.time()
p = 1999
for d in range(1, 101):
    ph = L.phi(p, L.R(d)); w = L.win_i_margin(p, d)
    for s in (2,3,5,10,100,10**6):
        L.hyp_i_margin(p, s, d, ph); L.hyp_ii_margin(p, s, d, ph)
print(f"timing: 100 d-values x 6 sigma (Lean side) {time.time()-t:.2f}s")
