#!/usr/bin/env python3
"""
Pre-validation of the two crossover-law propositions (claims C024, C025)
before they are added to the paper.

Proposition A (decay rate; C024): for all n >= 2, d >= 1, sigma >= 2,
with p1 = smallest prime factor, N = n^d:
    sigma^(N/p1)  <=  |S|  <=  2 log2(n) n^(d-1) sigma^(N/p1).
Hence 0 <= (1 - 1/p1) - c(n,d) <= log_sigma(2 n^(d-1) log2 n)/N -> 0.

Proposition B (inversion; C025): for prime p >= 3, sigma >= 2,
phi(d) = (1 - 1/p) p^d - (p+1)^d / 2:
 (i)  phi(d) > log_sigma(2 log2(p) p^(d-1))        ==> P_{(p+1)^d} > P_{p^d};
 (ii) phi(d) < -log_sigma(2 log2(p+1) (p+1)^(d-1)) ==> P_{(p+1)^d} < P_{p^d}.

Checks:
 [1] Prop A sandwich, exact integers with rational log2-brackets:
     n <= 20 & d <= 4, n <= 40 & d <= 3, n <= 12 & d = 5; sigma in {2,3}.
 [2] Prop B: exact sign of P(p+1) vs P(p) via integer cross-multiplication
     |S+| * sigma^(N_p) vs |S_p| * sigma^(N+) wherever feasible
     (p=3: d<=6; p=5: d<=5; p=7: d<=4; p=11,13: d<=3), agreement with
     log10-based signs on d <= 12, and NO case where a fired condition
     contradicts the actual sign.
"""

import math
import os
import sys
import platform
from fractions import Fraction

from verify_bruteforce import prime_factors, formula_count
from verify_banda2d import log2_bounds
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))  # repo root
from compute_dimension_insights import log10_P

FAILURES = []

def check(ok, label):
    print(f"    {label}: {'OK' if ok else 'FAILED'}")
    if not ok:
        FAILURES.append(label)

def main():
    print(f"python {sys.version.split()[0]} on {platform.platform()}")

    print("\n[1] Proposition A sandwich (exact)")
    grid = [(n, d) for n in range(2, 21) for d in (1, 2, 3, 4)]
    grid += [(n, d) for n in range(21, 41) for d in (1, 2, 3)]
    grid += [(n, 5) for n in range(2, 13)]
    bad = amb = 0
    for n, d in grid:
        p1 = prime_factors(n)[0]
        N = n ** d
        lo, hi = log2_bounds(n)
        for s in (2, 3):
            S = formula_count(n, d, s)
            base = s ** (N // p1)
            if S < base:
                bad += 1
                print(f"    LOWER FAILS n={n} d={d} s={s}")
            if S <= 2 * lo * n ** (d - 1) * base:
                pass
            elif S > 2 * hi * n ** (d - 1) * base:
                bad += 1
                print(f"    UPPER FAILS n={n} d={d} s={s}")
            else:
                amb += 1
    check(bad == 0 and amb == 0,
          f"sigma^(N/p1) <= |S| <= 2 log2(n) n^(d-1) sigma^(N/p1) on {len(grid)}x2 cases")

    print("\n[2] Proposition B inversion conditions vs actual signs")
    bad = 0
    exact_ranges = {3: 6, 5: 5, 7: 4, 11: 3, 13: 3}
    for p, dmax_exact in exact_ranges.items():
        for s in (2, 3):
            for d in range(1, 13):
                Np, Nq = p ** d, (p + 1) ** d
                phi = Fraction(p - 1, p) * Np - Fraction(Nq, 2)
                # actual sign
                if d <= dmax_exact:
                    Sp = formula_count(p, d, s)
                    Sq = formula_count(p + 1, d, s)
                    diff = Sq * s ** Np - Sp * s ** Nq      # sign of P(p+1)-P(p)
                    sign = (diff > 0) - (diff < 0)
                    lg = log10_P(p + 1, d, s) - log10_P(p, d, s)
                    if abs(lg) > 1e-6 and ((lg > 0) - (lg < 0)) != sign:
                        bad += 1
                        print(f"    LOG/EXACT SIGN MISMATCH p={p} d={d} s={s}")
                else:
                    lg = log10_P(p + 1, d, s) - log10_P(p, d, s)
                    sign = (lg > 0) - (lg < 0)
                # conditions (using safe upper brackets for log2)
                lo_p, hi_p = log2_bounds(p)
                lo_q, hi_q = log2_bounds(p + 1)
                thr_i = math.log(2 * float(hi_p) * p ** (d - 1)) / math.log(s)
                thr_ii = math.log(2 * float(hi_q) * (p + 1) ** (d - 1)) / math.log(s)
                if float(phi) > thr_i and sign != 1:
                    bad += 1
                    print(f"    COND (i) CONTRADICTED p={p} d={d} s={s}")
                if float(phi) < -thr_ii and sign != -1:
                    bad += 1
                    print(f"    COND (ii) CONTRADICTED p={p} d={d} s={s}")
    check(bad == 0, "no contradiction of (i)/(ii); log signs agree with exact signs")

    # exact curiosity: P(3) == P(4) at d=1 for every sigma?
    ok = all(formula_count(4, 1, s) * s ** 3 == formula_count(3, 1, s) * s ** 4
             for s in (2, 3, 4, 5))
    check(ok, "P(3) = P(4) at d=1 exactly, sigma <= 5 (boundary of the inversion)")

    print("\n" + "=" * 70)
    print("RESULT:", "all corroborated" if not FAILURES else f"{len(FAILURES)} failures")

if __name__ == "__main__":
    main()
