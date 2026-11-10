#!/usr/bin/env python3
"""
Pre-validation of the three NEW results going into the paper revision
(claims C017, C010, C012/C013a). Nothing enters the .tex before passing here.

 [1] C017 k-active-cell formula in d dimensions:
     |S^a_{n,d,k}| = sum_{v != 0} (-1)^(1+|v|) prod_i r_d(p_i,v_i)
                     * C(N/h, k/h) * (sigma-1)^((N-k)/h),   h = prod p_i^{v_i},
     with C(a,b) := 0 unless b is an integer in [0,a].
     Tested against (a) definition-level brute force for (2,3), (2,4) and
     sigma up to 3, and (b) an independent subgroup-IE evaluator (brute-force
     generators + BFS closures) for (3,3), (4,3), (6,3), (12,2), (6,2) s=3 —
     every k. Consistency: sum_k |S^a_k| = |S|.

 [2] C010 upper bounds:
     (union)     |S| <= sum_{p|n} [d 1]_p sigma^(N/p)          (exact check)
     (odd lemma) [d 1]_p sigma^(N/p) <= 2 sigma^(N/2) for every ODD p | n
     (corollary) |S| <= (2^d - 1 + 2 log2 n) sigma^(N/2)
     for n <= 60, d <= 4, sigma in {2,3,4}; log2 comparisons via exact
     squaring: X <= c*sigma^(N/2)  checked as  X^2 <= c^2 sigma^N with
     rational c-brackets for the log2(n) part.

 [3] C012/C013a detection model in d dims: full enumeration for
     (n,d,sigma) in {(2,3,2),(2,3,3),(2,4,2)}: per-generator
     E[#orbits visited] must equal (1-Q^m)/(1-Q) exactly (Q = sigma^(1-p),
     m = N/p), and total expected visited cells <= sum_p [d 1]_p * p *
     (1 - sigma^(1-p))^(-1).

Run: python3 verify_paper_claims.py
"""

import itertools
import math
import sys
import platform
from fractions import Fraction

from verify_bruteforce import (prime_factors, is_prime, gaussian_binomial,
                               r_d, formula_count, all_cells,
                               prime_order_generators, closure)
from verify_banda2d import log2_bounds

FAILURES = []

def check(ok, label):
    print(f"    {label}: {'OK' if ok else 'FAILED'}")
    if not ok:
        FAILURES.append(label)

def binom0(a, b):
    if b < 0 or b > a:
        return 0
    return math.comb(a, b)

# ---------------------------------------------------------------- [1] k-active

def kactive_formula(n, d, s, k):
    ps = prime_factors(n)
    N = n ** d
    total = 0
    for v in itertools.product(range(d + 1), repeat=len(ps)):
        if all(x == 0 for x in v):
            continue
        coeff, h = 1, 1
        for p, vi in zip(ps, v):
            coeff *= r_d(p, vi, d)
            h *= p ** vi
        if k % h:
            continue
        total += ((-1) ** (1 + sum(v)) * coeff * binom0(N // h, k // h)
                  * (s - 1) ** ((N - k) // h))
    return total

def ie_k_counts_ddim(n, d, s):
    gens = prime_order_generators(n, d)
    N = n ** d
    trivial = frozenset([tuple([0] * d)])
    pairs, cache = [], {}
    stack = [(0, trivial, 0)]
    while stack:
        i, sub, chosen = stack.pop()
        if i == len(gens):
            if chosen:
                pairs.append(((-1) ** (chosen + 1), len(sub)))
            continue
        stack.append((i + 1, sub, chosen))
        key = (sub, gens[i])
        if key not in cache:
            cache[key] = closure(sub, gens[i], n, d)
        stack.append((i + 1, cache[key], chosen + 1))
    out = []
    for k in range(N + 1):
        t = 0
        for sign, h in pairs:
            if k % h == 0:
                t += sign * binom0(N // h, k // h) * (s - 1) ** ((N - k) // h)
        out.append(t)
    return out

def brute_k_counts_ddim(n, d, s, a=0):
    cells = all_cells(n, d)
    N = len(cells)
    idx = {c: i for i, c in enumerate(cells)}
    perms = []
    for v in cells:
        if all(x == 0 for x in v):
            continue
        perms.append([idx[tuple((c[j] + v[j]) % n for j in range(d))] for c in cells])
    out = [0] * (N + 1)
    for cfg in itertools.product(range(s), repeat=N):
        if any(all(cfg[i] == cfg[p[i]] for i in range(N)) for p in perms):
            out[sum(1 for x in cfg if x == a)] += 1
    return out

# ---------------------------------------------------------------- [3] detection

def detection_expectations(n, d, s):
    cells = all_cells(n, d)
    N = len(cells)
    idx = {c: i for i, c in enumerate(cells)}
    gens = prime_order_generators(n, d)
    gen_orbits = []
    for w in gens:
        seen, orbits = set(), []
        p = None
        for c in cells:
            if idx[c] in seen:
                continue
            orb, cur = [], c
            while idx[cur] not in seen:
                seen.add(idx[cur])
                orb.append(idx[cur])
                cur = tuple((cur[j] + w[j]) % n for j in range(d))
            orbits.append(orb)
        p = len(orbits[0])
        gen_orbits.append((w, p, orbits))
    tot_orb = [0] * len(gens)
    tot_cells = 0
    for cfg in itertools.product(range(s), repeat=N):
        for gi, (w, p, orbits) in enumerate(gen_orbits):
            vis = 0
            for orb in orbits:
                vis += 1
                tot_cells += len(orb)
                if any(cfg[j] != cfg[orb[0]] for j in orb[1:]):
                    break
            tot_orb[gi] += vis
    ncfg = s ** N
    return ([(w, p, Fraction(t, ncfg)) for (w, p, _), t in zip(gen_orbits, tot_orb)],
            Fraction(tot_cells, ncfg))

# ---------------------------------------------------------------- main

def main():
    print(f"python {sys.version.split()[0]} on {platform.platform()}")

    print("\n[1] C017 k-active formula (d >= 3 for the first time)")
    for n, d, s in [(2, 3, 2), (2, 3, 3), (2, 4, 2)]:
        bf = brute_k_counts_ddim(n, d, s)
        ok = all(kactive_formula(n, d, s, k) == bf[k] for k in range(n ** d + 1))
        check(ok, f"formula == definition-level brute force, n={n} d={d} s={s}, all k")
    for n, d, s in [(3, 3, 2), (4, 3, 2), (6, 3, 2), (12, 2, 2), (6, 2, 3), (2, 4, 3)]:
        ie = ie_k_counts_ddim(n, d, s)
        ok = all(kactive_formula(n, d, s, k) == ie[k] for k in range(n ** d + 1))
        check(ok, f"formula == independent subgroup-IE, n={n} d={d} s={s}, all k")
        check(sum(ie) == formula_count(n, d, s), f"sum_k == |S|, n={n} d={d} s={s}")

    print("\n[2] C010 upper bounds")
    bad_u = bad_l = bad_c = amb = 0
    for n in range(2, 61):
        ps = prime_factors(n)
        for d in range(1, 5):
            N = n ** d
            for s in (2, 3, 4):
                S = formula_count(n, d, s)
                ub = sum(gaussian_binomial(d, 1, p) * s ** (N // p) for p in ps)
                if S > ub:
                    bad_u += 1
                    print(f"    UNION BOUND FAILS n={n} d={d} s={s}")
                for p in ps:
                    if p == 2:
                        continue
                    lhs = gaussian_binomial(d, 1, p) * s ** (N // p)
                    if lhs * lhs > 4 * s ** N:      # (2 sigma^(N/2))^2 = 4 sigma^N
                        bad_l += 1
                        print(f"    ODD-PRIME LEMMA FAILS n={n} d={d} s={s} p={p}")
                lo, hi = log2_bounds(n)
                c_lo = 2 ** d - 1 + 2 * lo
                if S * S <= c_lo * c_lo * s ** N:
                    pass
                else:
                    c_hi = 2 ** d - 1 + 2 * hi
                    if S * S > c_hi * c_hi * s ** N:
                        bad_c += 1
                        print(f"    COROLLARY FAILS n={n} d={d} s={s}")
                    else:
                        amb += 1
                        print(f"    COROLLARY borderline n={n} d={d} s={s}")
    check(bad_u == 0, "union bound exact, n <= 60, d <= 4, s <= 4")
    check(bad_l == 0, "odd-prime term lemma [d 1]_p s^(N/p) <= 2 s^(N/2), same grid")
    check(bad_c == 0 and amb == 0, "corollary |S| <= (2^d-1+2log2 n) s^(N/2), same grid")

    print("\n[3] C012/C013a detection expectation model, d >= 3")
    for n, d, s in [(2, 3, 2), (2, 3, 3), (2, 4, 2)]:
        per_gen, cells_total = detection_expectations(n, d, s)
        ok = True
        for w, p, got in per_gen:
            Q = Fraction(1, s ** (p - 1))
            m = n ** d // p
            if got != (1 - Q ** m) / (1 - Q):
                ok = False
        check(ok, f"E[#orbits] == (1-Q^m)/(1-Q) per generator, n={n} d={d} s={s}")
        bound = sum(gaussian_binomial(d, 1, p) * p / (1 - s ** (1 - p))
                    for p in set(prime_factors(n)))
        check(float(cells_total) <= bound,
              f"E[total cells] = {float(cells_total):.2f} <= {bound:.2f}, n={n} d={d} s={s}")

    print("\n" + "=" * 70)
    if FAILURES:
        print(f"RESULT: {len(FAILURES)} failure(s):")
        for f in FAILURES:
            print("  -", f)
    else:
        print("RESULT: all pre-publication claims corroborated exactly.")

if __name__ == "__main__":
    main()
