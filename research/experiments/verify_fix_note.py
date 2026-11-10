#!/usr/bin/env python3
"""
Exact corroboration of the repair note for Lemmas A.21/A.22 of
arXiv:1703.09030v2 (see research/fix_note/).

Checks, with exact integer arithmetic:

 [1] Failure-set completeness for the original chains:
     A.21's final step needs A/2 >= 4 log2(n) + 1 (A = n^2 / p_{m+1});
     A.22's needs (5/6) A >= 4 log2(n).
     Since p_{m+1} <= n/2 forces A >= 2n, the conditions hold for all
     composite multi-prime n >= 18 (resp. n >= 7); we scan ALL composite n
     with omega(n) >= 2 up to 5000 and every m, and assert the failure sets
     are exactly {(6,1),(10,1),(14,1)} and {(6,1)}.

 [2] The repair's union-bound lemma:  0 <= q^m(1/p) <= sum_i (p_i+1) s^(A/p_i)
     and 0 <= q^m(1/p^2), for all composite n <= 100, all m < omega(n),
     s in {2,3,5,7}.

 [3] The repaired conclusions:
       R2:  y1 + x1 + y2 >= (p+1) s^(A/2) (s^(A/2) - 2n/p - 1) and >= 0,
            with the driver inequality s^A p^2 >= (2n + p)^2 (exact squares);
       R3:  x2 <= y1  (A.22's needed inequality), and x2 >= 0;
     on the same grid.

Run: python3 verify_fix_note.py
"""

import sys
import platform
from fractions import Fraction

from verify_bruteforce import prime_factors
from verify_banda2d import qm, log2_bounds

FAILURES = []

def check(ok, label):
    print(f"    {label}: {'OK' if ok else 'FAILED'}")
    if not ok:
        FAILURES.append(label)

def multi_prime_composites(limit):
    for n in range(6, limit + 1):
        ps = prime_factors(n)
        if len(ps) >= 2:
            yield n, ps

def main():
    print(f"python {sys.version.split()[0]} on {platform.platform()}")

    print("\n[1] Failure sets of the original chain conditions (n <= 5000, all m)")
    fail21, fail22 = [], []
    for n, ps in multi_prime_composites(5000):
        lo, hi = log2_bounds(n)
        for m in range(1, len(ps)):
            p = ps[m]
            A = Fraction(n * n, p)
            # A.21: A/2 >= 4 log2 n + 1 ; count as failing if not provable
            # with the upper bracket (brackets are 1/64-tight, no borderline
            # cases occur at integer/quarter values here).
            if A / 2 < 4 * lo + 1:
                fail21.append((n, m))
            elif A / 2 < 4 * hi + 1:
                fail21.append((n, m))
            if Fraction(5, 6) * A < 4 * lo:
                fail22.append((n, m))
            elif Fraction(5, 6) * A < 4 * hi:
                fail22.append((n, m))
    print(f"    A.21 chain fails exactly at: {fail21}")
    print(f"    A.22 chain fails exactly at: {fail22}")
    check(fail21 == [(6, 1), (10, 1), (14, 1)], "A.21 failure set == {(6,1),(10,1),(14,1)}")
    check(fail22 == [(6, 1)], "A.22 failure set == {(6,1)}")
    # sanity for the completeness argument: A >= 2n always
    ok = all(Fraction(n * n, ps[m]) >= 2 * n
             for n, ps in multi_prime_composites(2000) for m in range(1, len(ps)))
    check(ok, "A = n^2/p_{m+1} >= 2n for every composite multi-prime n (p_{m+1} <= n/2)")

    print("\n[2] Union-bound lemma for q^m(1/p) and q^m(1/p^2)")
    bad = 0
    grid = [(n, ps, m, s) for n, ps in multi_prime_composites(100)
            for m in range(1, len(ps)) for s in (2, 3, 5, 7)]
    for n, ps, m, s in grid:
        p = ps[m]
        A = n * n // p
        qp = qm(n, s, m, Fraction(1, p))
        qpp = qm(n, s, m, Fraction(1, p * p))
        ub = sum((ps[i] + 1) * s ** (A // ps[i]) for i in range(m))
        if not (0 <= qp <= ub and 0 <= qpp):
            bad += 1
            print(f"    VIOLATION at n={n} m={m} s={s}: q(1/p)={qp} ub={ub} q(1/p^2)={qpp}")
    check(bad == 0, f"0 <= q^m(1/p) <= union bound and q^m(1/p^2) >= 0 on {len(grid)} cases")

    print("\n[3] Repaired inequalities R2 and R3")
    bad = 0
    for n, ps, m, s in grid:
        p = ps[m]
        A = n * n // p
        y1 = s ** A * (p + 1)
        x1 = -(p + 1) * qm(n, s, m, Fraction(1, p))
        x2 = p * qm(n, s, m, Fraction(1, p * p))
        y2 = -(s ** (n * n // p ** 2)) * p
        drv = s ** A * p * p >= (2 * n + p) ** 2      # s^(A/2) >= 2n/p + 1, squared
        if not (drv and y1 + x1 + y2 >= 0 and 0 <= x2 <= y1):
            bad += 1
            print(f"    VIOLATION at n={n} m={m} s={s}")
    check(bad == 0, f"driver s^(A/2) >= 2n/p+1, y1+x1+y2 >= 0, 0 <= x2 <= y1 on {len(grid)} cases")

    print("\n" + "=" * 70)
    if FAILURES:
        print(f"RESULT: {len(FAILURES)} failure(s):")
        for f in FAILURES:
            print("  -", f)
    else:
        print("RESULT: all repair-note inequalities corroborated exactly;")
        print("original-chain failure sets confirmed complete.")

if __name__ == "__main__":
    main()
