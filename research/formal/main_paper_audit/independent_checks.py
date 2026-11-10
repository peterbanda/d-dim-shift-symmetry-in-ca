"""Independent exact audit of the main paper. Standard library only.
Run from any directory. No project calculation functions are imported.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb, gcd, log10
import json


def primes(n):
    return [p for p in range(2, n + 1) if n % p == 0 and all(p % q for q in range(2, int(p**0.5) + 1))]


def gaussian(q, d, r):
    a = Fraction(1)
    for i in range(r):
        a *= Fraction(q ** (d - i) - 1, q ** (i + 1) - 1)
    assert a.denominator == 1
    return a.numerator


def formula(n, d, sigma):
    N = n**d
    ps = primes(n)
    count = 0
    hist = [0] * (N + 1)
    for ranks in product(range(d + 1), repeat=len(ps)):
        if not any(ranks):
            continue
        h, coef = 1, (-1) ** (1 + sum(ranks))
        for p, r in zip(ps, ranks):
            h *= p**r
            coef *= p**comb(r, 2) * gaussian(p, d, r)
        assert N % h == 0
        count += coef * sigma ** (N // h)
        for k in range(0, N + 1, h):
            hist[k] += coef * comb(N // h, k // h) * (sigma - 1) ** ((N - k) // h)
    return count, hist


def lattice(n, d):
    cells = list(product(range(n), repeat=d))
    indices = {x: i for i, x in enumerate(cells)}
    add = [[indices[tuple((a + b) % n for a, b in zip(x, y))] for y in cells] for x in cells]
    return cells, add


def brute(n, d, sigma):
    cells, add = lattice(n, d)
    hist = Counter()
    for s in product(range(sigma), repeat=len(cells)):
        if any(all(s[i] == s[j] for i, j in enumerate(shift)) for shift in add[1:]):
            hist[s.count(0)] += 1
    return sum(hist.values()), [hist[k] for k in range(len(cells) + 1)]


def subgroup_ie(n, d, sigma):
    cells, add = lattice(n, d)
    lines = set()
    for v in range(1, len(cells)):
        orbit, x = [], 0
        while not orbit or x != 0:
            orbit.append(x)
            x = add[x][v]
        if len(orbit) in primes(n):
            lines.add(frozenset(orbit))
    # Expand inclusion-exclusion, combining identical joins. No ranks,
    # Gaussian coefficients, primary decomposition, or enumeration formula.
    weights = {frozenset([0]): 1}
    for line in lines:
        next_weights = Counter(weights)
        for H, coef in weights.items():
            join = frozenset(add[x][y] for x in H for y in line)
            next_weights[join] -= coef
        weights = {H: c for H, c in next_weights.items() if c}
    N = len(cells)
    count, hist = sigma**N, [comb(N, k) * (sigma - 1)**(N-k) for k in range(N+1)]
    for H, coef in weights.items():
        h = len(H)
        assert N % h == 0
        count -= coef * sigma ** (N // h)
        for k in range(0, N + 1, h):
            hist[k] -= coef * comb(N // h, k // h) * (sigma - 1) ** ((N-k) // h)
    return count, hist


def early_prime_reads(p, sigma):
    # On Z_p the single subgroup is the entire lattice. Enumerate actual
    # reads until first mismatch, including the anchor.
    total = 0
    for s in product(range(sigma), repeat=p):
        reads = 1
        for b in s[1:]:
            reads += 1
            if b != s[0]:
                break
        total += reads
    return Fraction(total, sigma**p)


def main():
    brute_cases = [(n,d,s) for n in range(2,17) for d in range(1,5) for s in (1,2,3)
                   if n**d <= 16 and s**(n**d) <= 65536]
    configurations = 0
    for n,d,s in brute_cases:
        expected = formula(n,d,s)
        assert brute(n,d,s) == expected, (n,d,s)
        assert sum(expected[1]) == expected[0]
        configurations += s**(n**d)
    subgroup_cases = [(n,d,s) for n,d in [(2,4),(3,2),(4,2),(6,2),(10,2),(12,2),(15,1),(30,1),(60,1)]
                      for s in (1,2,3)]
    for n,d,s in subgroup_cases:
        assert subgroup_ie(n,d,s) == formula(n,d,s), (n,d,s)
    # Bounds and equality iff prime, directly using independent product formula.
    bound_cases = 0
    for n,d,s in product(range(2,25),range(1,5),(2,3,4)):
        N=n**d; ps=primes(n)
        # Only total count is needed; avoid constructing a long active-cell histogram.
        S=0
        for rr in product(range(d+1),repeat=len(ps)):
            if not any(rr):continue
            h=1;c=(-1)**(1+sum(rr))
            for p,r in zip(ps,rr):
                h*=p**r;c*=p**comb(r,2)*gaussian(p,d,r)
            S+=c*s**(N//h)
        F=sum((-1)**(r+1)*n**comb(r,2)*gaussian(n,d,r)*s**(n**(d-r)) for r in range(1,d+1))
        U=sum(gaussian(p,d,1)*s**(N//p) for p in ps)
        assert F<=S<=U and ((F==S)==(ps==[n])),(n,d,s)
        bound_cases+=1
    early = {}
    for p in (2,3,5,7,11,13):
        E=early_prime_reads(p,2)
        assert E==3-Fraction(1,2**(p-2))
        early[str(p)]=str(E)
    print(json.dumps(dict(brute_triples=len(brute_cases),configurations_enumerated=configurations,
        subgroup_triples=len(subgroup_cases),bound_triples=bound_cases,
        early_stop_binary_prime_expectations=early, status='PASS'),indent=2))

if __name__ == '__main__': main()
