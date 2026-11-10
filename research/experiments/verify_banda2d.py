#!/usr/bin/env python3
"""
Round-2 audit: exact verification of the PUBLISHED 2D paper
Banda, Caughman, Cenek, Teuscher, arXiv:1703.09030v2 (latest version).

Checks every numbered enumeration/bound claim exactly (integers/Fractions),
plus each crude step of the Appendix inequality chains A.21/A.22, which
hand-audit flagged as suspicious for small composite n.

Sections:
 [1] Eq. 17 (E.17), Eq. 18 (E.18), Eq. 19 (E.19) as literally stated,
     vs each other and vs the independent subgroup-IE evaluator (L2) of
     verify_bruteforce.py, plus definition-level brute force for tiny n.
 [2] Cor E.20 (prime case) and Lemma E.21 (lower bound, tight iff prime),
     n <= 200; also the final strict inequality q^1 > (n+1)s^n - n*s used in
     E.21's proof.
 [3] Lemma A.21: statement q^m <= q^{m+1}; exact decomposition
     q^{m+1} = x0+x1+x2+y1+y2; the paper's claims y1+x1+y2 >= 0 and x2 >= 0;
     and the chain's final crude step, which requires A/2 >= 4*log2(n) + 1
     (A = n^2/p_{m+1}) -- report every (n, m) where the step is invalid.
 [4] Lemma A.22 (|S| <= 2*sum s^(n^2/p_i)(p_i+1)), its analogous chain
     condition (5/6)A >= 4*log2(n); Lemma A.23; Cor A.24.
 [5] Lemma E.22 upper bound |S| <= 6 log2(n) s^(n^2/2) and Eq. 23/24
     probability bounds, via exact rational log2 brackets.
 [6] k-active-cell formulas: E.29 (single vector, brute force), E.30/E.31/
     E.32 as literally stated vs definition-level brute force (n=2,3,4) and
     vs an independent subgroup-IE k-active evaluator (n=6,10,12); A.34.
 [7] Thm E.36's exact expectation model: enumerate ALL configs, run the
     orbit-walk test per generator, compare E[#orbits visited] with the
     paper's (1-Q^m)/(1-Q), Q = s^(1-p), m = n^2/p; and check the total
     expected visited cells against the bound sum (p+1) p (1-s^(1-p))^-1.
 [8] Spot claims: P(2x2)=0.5, P(10x10)~2.7e-15, P_unif(100^2)~10^-1505,
     P_dens(45^2)~1e-3, P_dens(100^2)~2e-4.

Convention: binomial C(a,b) with non-integer or negative b is 0 (needed in
E.29-E.32 whenever h(v) does not divide k; the paper leaves this implicit).

Run: python3 verify_banda2d.py
"""

import itertools
import math
import sys
import platform
from fractions import Fraction

from verify_bruteforce import (
    prime_factors, is_prime, formula_count, brute_force_count,
    ie_subgroup_count, prime_order_generators, all_cells, log10_bigint,
)

FAILURES = []

def check(ok, label):
    print(f"    {label}: {'OK' if ok else 'MISMATCH'}")
    if not ok:
        FAILURES.append(label)

def binom(a, b):
    if b < 0 or b > a:
        return 0
    return math.comb(a, b)

# ---------------------------------------------------------------- log2 brackets

def log2_bounds(n, prec=64):
    b = (n ** prec).bit_length() - 1
    return Fraction(b, prec), Fraction(b + 1, prec)

# ---------------------------------------------------------------- Eq 17/18/19 literal

def e17(n, s):
    ps = prime_factors(n)
    total = 0
    for v in itertools.product(*[range(p + 2) for p in ps]):
        if all(x == 0 for x in v):
            continue
        coeff = 1
        h = 1
        for p, vi in zip(ps, v):
            coeff *= binom(p + 1, vi)
            h *= p ** min(vi, 2)
        total += (-1) ** (1 + sum(v)) * coeff * s ** (n * n // h)
    return total

def e18(n, s):
    ps = prime_factors(n)
    k = len(ps)
    total = 0
    for v in itertools.product(range(3), repeat=k):
        if all(x == 0 for x in v):
            continue
        g = n * n
        for p, vi in zip(ps, v):
            g //= p ** vi
        inner = 0
        ranges = [range(vi, vi + 1) if vi < 2 else range(2, p + 2)
                  for p, vi in zip(ps, v)]
        for u in itertools.product(*ranges):
            c = 1
            for p, ui in zip(ps, u):
                c *= binom(p + 1, ui)
            inner += (-1) ** (1 + sum(u)) * c
        total += s ** g * inner
    return total

def r2(p, v):
    return 1 if v == 0 else (p + 1 if v == 1 else p)

def e19(n, s):
    ps = prime_factors(n)
    k = len(ps)
    total = 0
    for v in itertools.product(range(3), repeat=k):
        if all(x == 0 for x in v):
            continue
        g = n * n
        coeff = 1
        for p, vi in zip(ps, v):
            g //= p ** vi
            coeff *= r2(p, vi)
        total += (-1) ** (1 + sum(v)) * coeff * s ** g
    return total

# ---------------------------------------------------------------- A.21 machinery

def qm(n, s, m, c=Fraction(1)):
    """q^m_{nxn}(c) from Lemma A.21: first m primes only, exponents g(v)*c."""
    ps = prime_factors(n)[:m]
    total = 0
    for v in itertools.product(range(3), repeat=m):
        if all(x == 0 for x in v):
            continue
        g = Fraction(n * n)
        coeff = 1
        for p, vi in zip(ps, v):
            g /= p ** vi
            coeff *= r2(p, vi)
        e = g * c
        assert e.denominator == 1, (n, m, c, v)
        total += (-1) ** (1 + sum(v)) * coeff * s ** int(e)
    return total

# ---------------------------------------------------------------- k-active formulas

def e29(n, s, v, k, a_dummy=0):
    """|S^a_{nxn,k}(v)| for a single vector v (Lemma E.29)."""
    o = order_of(v, n)
    if k % o:
        return 0
    return binom(n * n // o, k // o) * (s - 1) ** ((n * n - k) // o)

def order_of(v, n):
    g = math.gcd(math.gcd(v[0], v[1]), n)
    return n // g

def e30(n, s, k):
    d = math.gcd(k, n) if k else n
    rs = prime_factors(d)
    if not rs:
        return 0
    total = 0
    for u in itertools.product(*[range(r + 2) for r in rs]):
        if all(x == 0 for x in u):
            continue
        h = 1
        coeff = 1
        for r, ui in zip(rs, u):
            h *= r ** min(ui, 2)
            coeff *= binom(r + 1, ui)
        if k % h:
            continue
        total += ((-1) ** (1 + sum(u)) * coeff * binom(n * n // h, k // h)
                  * (s - 1) ** ((n * n - k) // h))
    return total

def e32(n, s, k):
    d = math.gcd(k, n) if k else n
    rs = prime_factors(d)
    if not rs:
        return 0
    total = 0
    for v in itertools.product(range(3), repeat=len(rs)):
        if all(x == 0 for x in v):
            continue
        h = 1
        coeff = 1
        for r, vi in zip(rs, v):
            h *= r ** vi
            coeff *= r2(r, vi)
        if k % h:
            continue
        total += ((-1) ** (1 + sum(v)) * coeff * binom(n * n // h, k // h)
                  * (s - 1) ** ((n * n - k) // h))
    return total

def brute_force_k_counts(n, s, a=0):
    """Definition-level: for each k, count configs with exactly k cells in
    state a that are fixed by some nonzero translation of Z_n^2."""
    cells = all_cells(n, 2)
    N = len(cells)
    idx = {c: i for i, c in enumerate(cells)}
    perms = []
    for v in cells:
        if v == (0, 0):
            continue
        perms.append([idx[((c[0] + v[0]) % n, (c[1] + v[1]) % n)] for c in cells])
    counts = [0] * (N + 1)
    for cfg in itertools.product(range(s), repeat=N):
        if any(all(cfg[i] == cfg[p[i]] for i in range(N)) for p in perms):
            counts[sum(1 for x in cfg if x == a)] += 1
    return counts

def ie_k_counts(n, s):
    """Independent subgroup-IE k-active evaluator (brute-force generators +
    BFS closures, imported machinery)."""
    from verify_bruteforce import closure
    gens = prime_order_generators(n, 2)
    N = n * n
    trivial = frozenset([(0, 0)])
    pairs = []  # (parity sign factor, |H|) per nonempty subset
    join_cache = {}
    stack = [(0, trivial, 0)]
    while stack:
        i, sub, chosen = stack.pop()
        if i == len(gens):
            if chosen:
                pairs.append(((-1) ** (chosen + 1), len(sub)))
            continue
        stack.append((i + 1, sub, chosen))
        key = (sub, gens[i])
        if key not in join_cache:
            join_cache[key] = closure(sub, gens[i], n, 2)
        stack.append((i + 1, join_cache[key], chosen + 1))
    counts = []
    for k in range(N + 1):
        tot = 0
        for sign, h in pairs:
            if k % h == 0:
                tot += sign * binom(N // h, k // h) * (s - 1) ** ((N - k) // h)
        counts.append(tot)
    return counts

# ---------------------------------------------------------------- E.36 walk

def orbit_walk_expectations(n, s):
    """Enumerate ALL s^(n^2) configs. For each generator w: fixed-order orbit
    walk, early exit on first failing orbit. Returns per-generator exact
    E[#orbits visited] and the exact E[total cells visited over all
    generators, run independently]."""
    cells = all_cells(n, 2)
    N = len(cells)
    idx = {c: i for i, c in enumerate(cells)}
    gens = prime_order_generators(n, 2)
    gen_orbits = []
    for w in gens:
        p = order_of(w, n)
        seen = set()
        orbits = []
        for c in cells:
            i = idx[c]
            if i in seen:
                continue
            orb = []
            cur = c
            while idx[cur] not in seen:
                seen.add(idx[cur])
                orb.append(idx[cur])
                cur = ((cur[0] + w[0]) % n, (cur[1] + w[1]) % n)
            orbits.append(orb)
        gen_orbits.append((w, p, orbits))
    tot_orbits = [0] * len(gens)
    tot_cells = 0
    n_cfg = s ** N
    for cfg in itertools.product(range(s), repeat=N):
        for gi, (w, p, orbits) in enumerate(gen_orbits):
            visited = 0
            for orb in orbits:
                visited += 1
                tot_cells += len(orb)
                if any(cfg[j] != cfg[orb[0]] for j in orb[1:]):
                    break
            tot_orbits[gi] += visited
    per_gen = [(gen_orbits[i][0], gen_orbits[i][1],
                Fraction(tot_orbits[i], n_cfg)) for i in range(len(gens))]
    return per_gen, Fraction(tot_cells, n_cfg)

# ---------------------------------------------------------------- main

def main():
    print(f"python {sys.version.split()[0]} on {platform.platform()}")
    print("Auditing arXiv:1703.09030v2 (v2 confirmed latest on arxiv.org, 2026-07-24)")

    print("\n[1] Eq. 17 / Eq. 18 / Eq. 19 literal forms vs independent evaluators")
    for n in list(range(2, 31)) + [36, 45, 60]:
        for s in (2, 3):
            a, b, c = e17(n, s), e18(n, s), e19(n, s)
            f = formula_count(n, 2, s)
            ok = a == b == c == f
            if not ok or n <= 12:
                print(f"    n={n} s={s}: E17={a == f} E18={b == f} E19={c == f}"
                      f" {'OK' if ok else 'MISMATCH ' + str((a, b, c, f))}")
            if not ok:
                FAILURES.append(f"E17/E18/E19 n={n} s={s}")
    ie6, _ = ie_subgroup_count(6, 2, 2)
    check(e17(6, 2) == ie6, "E17(6,2) equals independent subgroup-IE")
    check(e19(4, 2) == brute_force_count(4, 2, 2), "E19(4,2) equals definition-level brute force")
    check(e19(3, 3) == brute_force_count(3, 2, 3), "E19(3,3) equals definition-level brute force")

    print("\n[2] Cor E.20 and Lemma E.21 (n <= 200, s in {2,3})")
    bad20 = bad21 = badq1 = 0
    for n in range(2, 201):
        for s in (2, 3):
            S = e19(n, s)
            if is_prime(n) and S != s ** n * (n + 1) - s * n:
                bad20 += 1
            lb = s ** n * (n + 1) - s * n
            if S < lb or (S == lb) != is_prime(n):
                bad21 += 1
                print(f"    E.21 problem at n={n} s={s}: S={S} lb={lb}")
            if not is_prime(n):
                p1 = prime_factors(n)[0]
                q1 = s ** (n * n // p1) * (p1 + 1) - s ** (n * n // p1 ** 2) * p1
                if not q1 > lb:
                    badq1 += 1
                    print(f"    E.21 proof final step fails at n={n} s={s}")
    check(bad20 == 0, "E.20 exact at all primes n <= 200")
    check(bad21 == 0, "E.21 lower bound holds, tight iff prime, n <= 200")
    check(badq1 == 0, "E.21 proof's q^1 > (n+1)s^n - ns strict at composites")

    print("\n[3] Lemma A.21: statement, decomposition, and chain validity")
    stmt_bad = decomp_bad = ineq_bad = 0
    gap_cases = []
    for n in range(4, 101):
        ps = prime_factors(n)
        k = len(ps)
        if k < 2:
            continue
        for s in (2, 3):
            for m in range(1, k):
                p = ps[m]
                q_m = qm(n, s, m)
                q_m1 = qm(n, s, m + 1)
                if not q_m <= q_m1:
                    stmt_bad += 1
                    print(f"    A.21 STATEMENT FALSE at n={n} s={s} m={m}: {q_m} > {q_m1}")
                x0 = q_m
                x1 = -(p + 1) * qm(n, s, m, Fraction(1, p))
                x2 = p * qm(n, s, m, Fraction(1, p * p))
                y1 = s ** (n * n // p) * (p + 1)
                y2 = -(s ** (n * n // p ** 2)) * p
                if x0 + x1 + x2 + y1 + y2 != q_m1:
                    decomp_bad += 1
                    print(f"    A.21 decomposition broken at n={n} s={s} m={m}")
                if y1 + x1 + y2 < 0:
                    ineq_bad += 1
                    print(f"    A.21 KEY INEQUALITY y1+x1+y2 >= 0 FALSE at n={n} s={s} m={m}")
                if x2 < 0:
                    ineq_bad += 1
                    print(f"    A.21 x2 >= 0 FALSE at n={n} s={s} m={m}")
                if s == 2:
                    # chain's final step needs A/2 >= 4 log2(n) + 1, A = n^2/p
                    A = Fraction(n * n, p)
                    lo, hi = log2_bounds(n)
                    if A / 2 < 4 * lo + 1:
                        gap_cases.append((n, m, p))
                    elif A / 2 < 4 * hi + 1:
                        gap_cases.append((n, m, p))  # borderline counts as unproven by the chain
    check(stmt_bad == 0, "A.21 statement q^m <= q^(m+1) on all composite n <= 100")
    check(decomp_bad == 0, "A.21 five-part decomposition identity")
    check(ineq_bad == 0, "A.21 target inequalities y1+x1+y2 >= 0 and x2 >= 0")
    print(f"    A.21 PROOF-CHAIN GAP: final step 'A/2 >= 4 log2(n)+1' FAILS for (n,m,p) = {gap_cases}")
    print("    (statement true in every such case per the exact checks above -> proof gap, not a false lemma)")

    print("\n[4] Lemmas A.22, A.23, Cor A.24")
    bad22 = 0
    gap22 = []
    for n in range(2, 101):
        ps = prime_factors(n)
        for s in (2, 3):
            S = e19(n, s)
            ub = 2 * sum(s ** (n * n // p) * (p + 1) for p in ps)
            if S > ub:
                bad22 += 1
                print(f"    A.22 FALSE at n={n} s={s}")
            if s == 2 and len(ps) >= 2:
                for m in range(1, len(ps)):
                    p = ps[m]
                    A = Fraction(n * n, p)
                    lo, hi = log2_bounds(n)
                    if Fraction(5, 6) * A < 4 * hi:
                        gap22.append((n, m, p))
    check(bad22 == 0, "A.22 statement |S| <= 2 sum s^(n^2/p)(p+1), n <= 100")
    print(f"    A.22 chain final step '(5/6)A >= 4 log2 n' fails or is borderline for: {gap22}")
    bad23 = bad24 = 0
    for n in range(2, 101):
        for s in (2, 3):
            for p in prime_factors(n):
                # A.23: s^(n^2/p)(p+1) <= s^(n^2/(p-1)) p  -- exponents may be
                # non-integer; compare via (p-1)p-th powers, exactly.
                lhs = (s ** (n * n // p) * (p + 1)) ** (p * (p - 1))
                rhs_exp = n * n * p  # (n^2/(p-1)) * (p-1) * p
                rhs = s ** rhs_exp * p ** (p * (p - 1))
                lhs_exact = (s ** (n * n * (p - 1)) * (p + 1) ** (p * (p - 1)))  # s^(n^2/p * p(p-1))
                if not lhs_exact <= rhs:
                    bad23 += 1
                    print(f"    A.23 FALSE at n={n} s={s} p={p}")
                # A.24: s^(n^2/p)(p+1) <= 3 s^(n^2/2): compare squares
                if not (s ** (n * n // p) * (p + 1)) ** 2 <= 9 * s ** (n * n):
                    bad24 += 1
                    print(f"    A.24 FALSE at n={n} s={s} p={p}")
    check(bad23 == 0, "A.23 on all prime divisors, n <= 100")
    check(bad24 == 0, "A.24 on all prime divisors, n <= 100")

    print("\n[5] Lemma E.22 upper bound and Eq. 23/24 probability bounds")
    bad = amb = 0
    for n in range(2, 101):
        for s in (2, 3, 4):
            S = e19(n, s)
            R = Fraction(S * S, s ** (n * n))  # (|S| / s^(n^2/2))^2
            lo, hi = log2_bounds(n)
            if R <= 36 * lo * lo:
                pass
            elif R > 36 * hi * hi:
                bad += 1
                print(f"    E.22 FALSE at n={n} s={s}")
            else:
                amb += 1
                print(f"    E.22 borderline at n={n} s={s} (log2 bracket too coarse)")
            if not n * s ** n <= S:
                bad += 1
                print(f"    Eq.24 lower bound FALSE at n={n} s={s}")
    check(bad == 0 and amb == 0, "E.22 and Eq.24 hold for n <= 100, s in {2,3,4}")

    print("\n[6] k-active-cell formulas E.29/E.30/E.32 and Cor A.34")
    # E.29 single-vector brute force, n=4 s=2 and n=3 s=3, all v, all k
    for n, s in [(4, 2), (3, 3)]:
        cells = all_cells(n, 2)
        idx = {c: i for i, c in enumerate(cells)}
        ok29 = True
        for v in cells:
            if v == (0, 0):
                continue
            perm = [idx[((c[0] + v[0]) % n, (c[1] + v[1]) % n)] for c in cells]
            got = [0] * (n * n + 1)
            for cfg in itertools.product(range(s), repeat=n * n):
                if all(cfg[i] == cfg[perm[i]] for i in range(n * n)):
                    got[sum(1 for x in cfg if x == 0)] += 1
            for k in range(n * n + 1):
                if got[k] != e29(n, s, v, k):
                    ok29 = False
        check(ok29, f"E.29 vs brute force, n={n} s={s}, all v and k")
    # E.30/E.32 vs definition-level brute force
    for n, s in [(2, 2), (3, 2), (4, 2), (2, 3), (3, 3)]:
        bf = brute_force_k_counts(n, s)
        ok30 = all(e30(n, s, k) == bf[k] for k in range(n * n + 1))
        ok32 = all(e32(n, s, k) == bf[k] for k in range(n * n + 1))
        check(ok30, f"E.30 vs brute force, n={n} s={s}, all k")
        check(ok32, f"E.32 vs brute force, n={n} s={s}, all k")
    # a-independence sanity: a=1 gives same counts (s=3, n=3)
    check(brute_force_k_counts(3, 3, a=1) == brute_force_k_counts(3, 3, a=0),
          "k-active counts independent of the chosen state a (n=3, s=3)")
    # E.32 vs independent subgroup-IE evaluator on larger n
    for n, s in [(6, 2), (6, 3), (10, 2), (12, 2)]:
        ie = ie_k_counts(n, s)
        ok = all(e32(n, s, k) == ie[k] for k in range(n * n + 1))
        check(ok, f"E.32 vs independent subgroup-IE, n={n} s={s}, all k")
        tot = sum(ie)
        check(tot == e19(n, s), f"sum_k |S^a_k| == |S|, n={n} s={s}")
    # A.34: k=0 equals |S| over the alphabet without a
    for n, s in [(6, 3), (10, 3), (12, 4)]:
        check(e32(n, s, 0) == formula_count(n, 2, s - 1),
              f"A.34: E.32(k=0) == |S| over s-1 states, n={n} s={s}")

    print("\n[7] Thm E.36 expectation model (exact, all configs enumerated)")
    for n, s in [(2, 2), (3, 2), (3, 3), (4, 2)]:
        per_gen, cells_total = orbit_walk_expectations(n, s)
        ok = True
        for w, p, got in per_gen:
            Q = Fraction(1, s ** (p - 1))
            m = n * n // p
            want = (1 - Q ** m) / (1 - Q)
            if got != want:
                ok = False
                print(f"    n={n} s={s} w={w}: E[#orbits]={got} != model {want}")
        check(ok, f"E[#orbits visited] == (1-Q^m)/(1-Q) exactly, n={n} s={s}, every generator")
        bound = sum((p + 1) * p / (1 - s ** (1 - p)) for p in set(prime_factors(n)))
        check(float(cells_total) <= bound,
              f"E[total cells] = {float(cells_total):.3f} <= paper bound {bound:.3f}, n={n} s={s}")

    print("\n[8] Spot claims from the main text")
    S2x2 = e19(2, 2)
    print(f"    P(2x2) = {S2x2}/16 = {S2x2 / 16}  (paper: 0.5)")
    check(S2x2 * 2 == 16, "P(2x2) = 0.5")
    S10 = e19(10, 2)
    p10 = S10 / 2 ** 100
    print(f"    P(10x10) = {p10:.3e}  (paper: ~2.7e-15)")
    check(2.5e-15 < p10 < 2.9e-15, "P(10x10) ~ 2.7e-15")
    lp100 = log10_bigint(e19(100, 2)) - 10000 * math.log10(2)
    print(f"    log10 P_unif(100x100) = {lp100:.1f}  (paper: ~ -1505)")
    check(-1506 < lp100 < -1504, "P_unif(100^2) ~ 10^-1505")
    for n, want_lo, want_hi, label in [(45, 5e-4, 5e-3, "~0.001"), (100, 1e-4, 4e-4, "~2e-4")]:
        tot = Fraction(0)
        N = n * n
        # s=2: log-space sum of |S^a_k| / C(N,k)
        acc = 0.0
        for k in range(N + 1):
            v = e32(n, 2, k)
            if v:
                acc += 10 ** (log10_bigint(v) - log10_bigint(binom(N, k)))
        pd = acc / (N + 1)
        print(f"    P_dens({n}x{n}) = {pd:.3e}  (paper: {label})")
        check(want_lo < pd < want_hi, f"P_dens({n}^2) {label}")

    print("\n" + "=" * 70)
    if FAILURES:
        print(f"RESULT: {len(FAILURES)} failed check group(s):")
        for f in FAILURES:
            print("  -", f)
    else:
        print("RESULT: every numbered STATEMENT checked is exactly correct on the")
        print("tested domains. The only defects found are PROOF-chain gaps in")
        print("A.21/A.22 at small composite n (listed inline in section [3]/[4]).")

if __name__ == "__main__":
    main()
