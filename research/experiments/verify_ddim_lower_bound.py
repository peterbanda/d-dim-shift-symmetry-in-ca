#!/usr/bin/env python3
"""
Exact validation of every estimate in the round-3 proof of the d-dimensional
lower bound (claim C009) BEFORE it is committed to the write-up
(research/proofs/d_dim_proofs.tex).

Objects (first m primes p_1 < ... < p_k of n; p = p_{m+1}; N_j = n^d / p^j):

  q^m_d(c)  = sum over 0 != v in {0..d}^m of
              (-1)^(1+|v|) prod_i r_d(p_i, v_i) sigma^(n^d c / prod_i p_i^{v_i}),
  q^k_d(1)  = |S_{n^d}|  (main formula),
  B_j       = sigma^{N_j} - q^m_d(p^{-j}).

Checks:
 [1] Decomposition: q^{m+1} - q^m = sum_{j=1}^d (-1)^{j+1} r_d(p,j) B_j (exact).
 [2] Union interpretation bounds: 0 <= q^m_d(p^{-j}) <= sigma^{N_j}, and the
     union bound q^m_d(p^{-1}) <= sum_{i<=m} [d 1]_{p_i} sigma^{N_1/p_i}.
 [3] Coefficient estimates: [d j]_p <= 4 p^{j(d-j)} and
     sum_{j=2}^d r_d(p,j) <= 4(d-1) p^{d(d-1)/2}, for d <= 8, p in {2,3,5,7}.
 [4] Sufficient conditions of the chain lemma, and the chain itself:
     (I)  sigma^{N_1/2} >= 4 (n/p)^{d-1}      [=> B_1 >= sigma^{N_1}/2]
     (II) sigma^{N_1-N_2} >= 8(d-1) p^{d(d-1)/2}
     => q^m <= q^{m+1}; also direct check q^m <= q^{m+1}.
 [5] Base-case lemma: q^1 > F_d(n,sigma) for composite n (d >= 3), via the
     master condition (M): 2^{n^{d-1}} >= 12 d n^{d(d-1)/2} and exact
     comparison of q^1 vs F_d; plus C009 statement re-check |S| >= F_d with
     equality iff prime, now up to d = 5.

Run: python3 verify_ddim_lower_bound.py
"""

import itertools
import sys
import platform
from fractions import Fraction

from verify_bruteforce import prime_factors, is_prime, gaussian_binomial, r_d, formula_count

FAILURES = []

def check(ok, label):
    print(f"    {label}: {'OK' if ok else 'FAILED'}")
    if not ok:
        FAILURES.append(label)

def qdm(n, d, s, m, c=Fraction(1)):
    ps = prime_factors(n)[:m]
    total = 0
    for v in itertools.product(range(d + 1), repeat=m):
        if all(x == 0 for x in v):
            continue
        coeff = 1
        g = Fraction(n ** d)
        for p, vi in zip(ps, v):
            coeff *= r_d(p, vi, d)
            g /= p ** vi
        e = g * c
        assert e.denominator == 1, (n, d, m, c, v)
        total += (-1) ** (1 + sum(v)) * coeff * s ** int(e)
    return total

def F_d(n, d, s):
    return sum((-1) ** (r + 1) * r_d(n, r, d) * s ** (n ** (d - r)) for r in range(1, d + 1))

def multi_prime(limit):
    return [(n, prime_factors(n)) for n in range(6, limit + 1) if len(prime_factors(n)) >= 2]

def main():
    print(f"python {sys.version.split()[0]} on {platform.platform()}")

    grid = [(n, ps, d, s, m) for n, ps in multi_prime(30) for d in (2, 3, 4)
            for s in (2, 3) for m in range(1, len(ps))]
    print(f"\n[1] Five-part-style decomposition in d dims ({len(grid)} cases)")
    bad = 0
    for n, ps, d, s, m in grid:
        p = ps[m]
        lhs = qdm(n, d, s, m + 1) - qdm(n, d, s, m)
        rhs = 0
        for j in range(1, d + 1):
            Bj = s ** (n ** d // p ** j) - qdm(n, d, s, m, Fraction(1, p ** j))
            rhs += (-1) ** (j + 1) * r_d(p, j, d) * Bj
        if lhs != rhs:
            bad += 1
            print(f"    DECOMPOSITION BROKEN n={n} d={d} s={s} m={m}")
    check(bad == 0, "q^(m+1) - q^m == sum_j (-1)^(j+1) r_d(p,j) B_j exactly")

    print(f"\n[2] Union-interpretation bounds ({len(grid)} cases x j)")
    bad = 0
    for n, ps, d, s, m in grid:
        p = ps[m]
        for j in range(1, d + 1):
            q = qdm(n, d, s, m, Fraction(1, p ** j))
            if not 0 <= q <= s ** (n ** d // p ** j):
                bad += 1
                print(f"    SANDWICH FAILS n={n} d={d} s={s} m={m} j={j}")
        ub = sum(gaussian_binomial(d, 1, ps[i]) * s ** (n ** d // p // ps[i]) for i in range(m))
        if not qdm(n, d, s, m, Fraction(1, p)) <= ub:
            bad += 1
            print(f"    UNION BOUND FAILS n={n} d={d} s={s} m={m}")
    check(bad == 0, "0 <= q^m(p^-j) <= sigma^(N_j) and union bound at j=1")

    print("\n[3] Coefficient estimates")
    bad = 0
    for d in range(2, 9):
        for p in (2, 3, 5, 7):
            for j in range(0, d + 1):
                if gaussian_binomial(d, j, p) > 4 * p ** (j * (d - j)):
                    bad += 1
                    print(f"    GB BOUND FAILS d={d} p={p} j={j}")
            tail = sum(r_d(p, j, d) for j in range(2, d + 1))
            if tail > 4 * (d - 1) * p ** (d * (d - 1) // 2):
                bad += 1
                print(f"    TAIL BOUND FAILS d={d} p={p}: {tail}")
    check(bad == 0, "[d j]_p <= 4 p^(j(d-j)) and tail sum <= 4(d-1) p^(d(d-1)/2), d <= 8")

    print(f"\n[4] Chain sufficient conditions and the chain itself ({len(grid)} cases)")
    bad_cond = bad_chain = 0
    for n, ps, d, s, m in grid:
        p = ps[m]
        N1, N2 = n ** d // p, n ** d // p ** 2
        t = n // p if n % p == 0 else Fraction(n, p)
        condI = s ** N1 >= (4 * (Fraction(n, p)) ** (d - 1)) ** 2   # sigma^(N1/2) >= 4 t^(d-1), squared
        condII = s ** (N1 - N2) >= 8 * (d - 1) * p ** (d * (d - 1) // 2)
        if not (condI and condII):
            bad_cond += 1
            print(f"    CONDITION FAILS n={n} d={d} s={s} m={m}: I={condI} II={condII}")
        if not qdm(n, d, s, m) <= qdm(n, d, s, m + 1):
            bad_chain += 1
            print(f"    CHAIN FAILS n={n} d={d} s={s} m={m}")
    check(bad_cond == 0, "conditions (I) and (II) hold on the whole grid (d >= 2)")
    check(bad_chain == 0, "q^m <= q^(m+1) holds exactly on the whole grid")

    print("\n[5] Base case and C009 statement")
    bad = 0
    for n in range(4, 31):
        if is_prime(n):
            continue
        for d in (3, 4):
            for s in (2, 3):
                p1 = prime_factors(n)[0]
                condM = 2 ** (n ** (d - 1)) >= 12 * d * n ** (d * (d - 1) // 2)
                q1 = qdm(n, d, s, 1)
                if not condM:
                    bad += 1
                    print(f"    (M) FAILS n={n} d={d}")
                if not q1 > F_d(n, d, s):
                    bad += 1
                    print(f"    BASE CASE FAILS n={n} d={d} s={s}")
    check(bad == 0, "condition (M) and q^1 > F_d at composites, d in {3,4}, n <= 30")
    bad = 0
    for n in range(2, 13):
        for d in range(1, 6):
            for s in (2, 3):
                S = formula_count(n, d, s)
                F = F_d(n, d, s)
                if S < F or (S == F) != is_prime(n):
                    bad += 1
                    print(f"    C009 STATEMENT FAILS n={n} d={d} s={s}")
    check(bad == 0, "C009: F_d <= |S|, equality iff prime (n <= 12, d <= 5)")

    print("\n" + "=" * 70)
    if FAILURES:
        print(f"RESULT: {len(FAILURES)} failure(s):")
        for f in FAILURES:
            print("  -", f)
    else:
        print("RESULT: all round-3 proof estimates corroborated exactly.")

if __name__ == "__main__":
    main()
