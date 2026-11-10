"""Independent checks of the promoted results; no project mathematical imports.

Enumerate actual subgroup sets, invert their inclusion poset, and compare with
the printed Gaussian formula. Also enumerate small configurations directly.
These are finite checks supplementing, not replacing, the proof review.
"""
from itertools import product
from math import prod, comb
from collections import Counter
from pathlib import Path
import json

def factor(n):
    ans = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            ans[p] = ans.get(p, 0)+1; n //= p
        p += 1
    if n > 1: ans[n] = 1
    return ans

def gauss(p, d, v):
    numerator = prod(p**d-p**i for i in range(v))
    denominator = prod(p**v-p**i for i in range(v))
    assert numerator % denominator == 0
    return numerator // denominator

def formula(N, ranks, sigma, k=None):
    ps = list(ranks); out = 0
    for vs in product(*(range(ranks[p]+1) for p in ps)):
        if not any(vs): continue
        h = prod(p**v for p,v in zip(ps,vs)); assert N % h == 0
        coefficient = (-1)**(1+sum(vs))*prod(p**comb(v,2)*gauss(p,ranks[p],v) for p,v in zip(ps,vs))
        weight = sigma**(N//h) if k is None else (comb(N//h,k//h)*(sigma-1)**((N-k)//h) if k%h==0 else 0)
        out += coefficient*weight
    return out

def group(ns):
    elements = list(product(*(range(n) for n in ns))); index = {g:i for i,g in enumerate(elements)}
    add = [[index[tuple((a+b)%n for a,b,n in zip(g,h,ns))] for h in elements] for g in elements]
    N = len(elements)
    cyclic = []
    for x in range(N):
        h = {0}; a = x
        while a not in h: h.add(a); a = add[a][x]
        cyclic.append(h)
    subs = {frozenset({0})}; todo = list(subs)
    while todo:
        H = todo.pop()
        for x in range(N):
            if x in H: continue
            K = frozenset(add[a][b] for a in H for b in cyclic[x])
            if K not in subs: subs.add(K); todo.append(K)
    mu = {}
    for H in sorted(subs,key=len):
        mu[H] = 1 if len(H)==1 else -sum(m for K,m in mu.items() if K < H)
    ranks = {p:sum(n%p==0 for n in ns) for p in factor(N)}
    for p,d in ranks.items():
        assert sum(all((p*g[i])%n==0 for i,n in enumerate(ns)) for g in elements)==p**d
    return N,add,mu,ranks

def tuples(limit, lower=2):
    yield ()
    for n in range(lower,limit+1):
        for rest in tuples(limit//n,n): yield (n,)+rest

def main():
    checks=Counter(); examples=[]
    groups = sorted(set(tuples(32)) | {(2,24),(4,12),(2,2,2,2,2,2),(3,3,3),(3,9),(3,27),(9,9),(6,12),(2,1,3),(1,),()})
    for ns in groups:
        N,add,mu,ranks = group(ns); checks['groups']+=1
        for sigma in (1,2,3):
            lattice = -sum(m*sigma**(N//len(H)) for H,m in mu.items() if len(H)>1)
            assert lattice==formula(N,ranks,sigma),(ns,sigma)
            assert (sigma**N-lattice)%N==0
            checks['lattice_enumerations']+=1
            total=0
            for k in range(N+1):
                lk=-sum(m*comb(N//len(H),k//len(H))*(sigma-1)**((N-k)//len(H)) for H,m in mu.items() if len(H)>1 and k%len(H)==0)
                assert lk==formula(N,ranks,sigma,k),(ns,sigma,k)
                total+=lk; checks['fixed_k_checks']+=1
            assert total==lattice
            if sigma**N <= 20000:
                hist=Counter()
                for s in product(range(sigma), repeat=N):
                    sym=any(all(s[add[u][v]]==s[u] for u in range(N)) for v in range(1,N))
                    if sym: hist[s.count(0)]+=1
                    # The indicator-correlation test, using every symbol, including absent ones.
                    for v in range(N):
                        corr=sum(int(s[u]==a)*int(s[add[u][v]]==a) for a in range(sigma) for u in range(N))
                        assert (corr==N)==all(s[add[u][v]]==s[u] for u in range(N))
                    checks['brute_configurations']+=1
                assert sum(hist.values())==lattice
                assert all(hist[k]==formula(N,ranks,sigma,k) for k in range(N+1))
                checks['brute_cases']+=1
        # All one-defect configurations have trivial stabilizer, including order one.
        for defect in range(N):
            s=[0]*N; s[defect]=1
            assert not any(all(s[add[u][v]]==s[u] for u in range(N)) for v in range(1,N))
            checks['one_defects']+=1
        if ns in ((2,24),(4,12)): examples.append({'cyclic_factors':ns,'binary_symmetric':formula(N,ranks,2),'subgroups':len(mu)})
    for N in range(1,513):
        fs=factor(N); ps=list(fs)
        cyclic=formula(N,dict.fromkeys(ps,1),2)
        for ds in product(*(range(1,fs[p]+1) for p in ps)):
            ranks=dict(zip(ps,ds))
            assert cyclic<=formula(N,ranks,2)
            for p in ps:
                if ranks[p]==fs[p]: continue
                raised=dict(ranks);raised[p]+=1
                for sigma in (2,3):
                    diff=formula(N,raised,sigma)-formula(N,ranks,sigma)
                    ac=sigma**(N//p)-formula(N//p,ranks,sigma)
                    assert diff==p**ranks[p]*ac and diff>0
                    checks['strict_rank_steps']+=1
    result={'result':'PASS','checks':dict(checks),'paper_examples':examples,'scope':'Independent subgroup-poset inversion and small exhaustive configurations; ranks up to six, trivial groups, singleton factors, several primes, all fixed-k boundaries.'}
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
