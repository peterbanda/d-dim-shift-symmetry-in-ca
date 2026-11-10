#!/usr/bin/env python3
"""Verifier for the enumeration of shift-symmetric configurations on every finite abelian group
(paper v10, Section 4.5: Theorem 4.7, Corollary 4.8, Remark 4.9).

    python3 verify_abelian.py            # from research/experiments/; deterministic, exact integers

G = Z_{n_1} x ... x Z_{n_k}, N = |G|, d_p = #{i : p | n_i} (the p-rank of G), sigma symbols.
A configuration s : G -> {0..sigma-1} is shift-symmetric if s(u + v) = s(u) for all u, for some
v != 0. Claim (Theorem 4.7, divisor form):

    |S_G| = sum_{h | R, h != 1} (-1)^(1 + Omega(h)) prod_{p | h} p^C(v_p(h), 2) [d_p, v_p(h)]_p sigma^(N / h),
    R = prod_p p^(d_p).

Independent evaluations, compared exactly:
  (B) definition-level brute force: every configuration, every nonzero v;
  (L) the full subgroup lattice: all subgroups of G generated as sets, the Moebius function
      mu(0, H) of that lattice computed by its defining recursion (no use of Hall's values or of
      the socle), |S_G| = sigma^N - sum_H mu(0, H) sigma^(N/|H|);
  (U) the definition as a union over v != 0 of Fix(<v>), by inclusion-exclusion over the cyclic subgroups
      (check [11]: the example of Corollary 4.8(i));
  (F) the closed formula, in two codings: divisor-indexed (as frozen in Lean) and vector-indexed,
      with Gaussian binomials from the product formula and from the q-Pascal recurrence.
Also checked: (F) = the paper's Theorem 4.4 on square tori; (F) depends on G only through N and
the p-ranks (non-isomorphic groups with equal N and ranks have equal counts, confirmed by (L)/(B));
and N | sigma^N - |S_G| (free action on the aperiodic configurations).
"""
import itertools
import sys
from math import comb, prod

import numpy as np


# ---------------------------------------------------------------- arithmetic helpers
def prime_factors(n):
    out, q = [], 2
    while q * q <= n:
        if n % q == 0:
            out.append(q)
            while n % q == 0:
                n //= q
        q += 1
    if n > 1:
        out.append(n)
    return out


def factorization(n):
    f, q = {}, 2
    while q * q <= n:
        while n % q == 0:
            f[q] = f.get(q, 0) + 1
            n //= q
        q += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def divisors(n):
    ds = [1]
    for p, e in factorization(n).items():
        ds = [d * p ** k for d in ds for k in range(e + 1)]
    return sorted(ds)


def gauss_prod(d, r, q):
    """[d r]_q by the product formula."""
    if r < 0 or r > d:
        return 0
    num = prod(q ** (d - i) - 1 for i in range(r))
    den = prod(q ** (i + 1) - 1 for i in range(r))
    assert num % den == 0
    return num // den


def gauss_pascal(d, r, q, _memo={}):
    """[d r]_q by the q-Pascal recurrence used in Lean (Statement.lean, gaussBinom)."""
    key = (d, r, q)
    if key not in _memo:
        if r == 0:
            v = 1
        elif d == 0:
            v = 0
        else:
            v = gauss_pascal(d - 1, r - 1, q) + q ** r * gauss_pascal(d - 1, r, q)
        _memo[key] = v
    return _memo[key]


def ranks(ns):
    N = prod(ns)
    return N, {p: sum(1 for n in ns if n % p == 0) for p in prime_factors(N)}


# ---------------------------------------------------------------- (F) the closed formula
def formula_divisor(ns, sigma):
    N, dp = ranks(ns)
    R = prod(p ** e for p, e in dp.items())
    tot = 0
    for h in divisors(R):
        if h == 1:
            continue
        f = factorization(h)
        omega = sum(f.values())
        coeff = prod(p ** comb(v, 2) * gauss_pascal(dp[p], v, p) for p, v in f.items())
        tot += (-1) ** (1 + omega) * coeff * sigma ** (N // h)
    return tot


def formula_vector(ns, sigma):
    N, dp = ranks(ns)
    ps = sorted(dp)
    tot = 0
    for v in itertools.product(*[range(dp[p] + 1) for p in ps]):
        if not any(v):
            continue
        H = prod(p ** vp for p, vp in zip(ps, v))
        c = prod(p ** (vp * (vp - 1) // 2) * gauss_prod(dp[p], vp, p) for p, vp in zip(ps, v))
        tot += (-1) ** (1 + sum(v)) * c * sigma ** (N // H)
    return tot


def formula_kactive(ns, sigma, k):
    """Corollary (d): shift-symmetric configurations with exactly k cells in a given state."""
    N, dp = ranks(ns)
    ps = sorted(dp)
    tot = 0
    for v in itertools.product(*[range(dp[p] + 1) for p in ps]):
        if not any(v):
            continue
        h = prod(p ** vp for p, vp in zip(ps, v))
        if k % h:
            continue                                   # binom(N/h, k/h) = 0 unless h | k
        c = prod(p ** comb(vp, 2) * gauss_prod(dp[p], vp, p) for p, vp in zip(ps, v))
        tot += (-1) ** (1 + sum(v)) * c * comb(N // h, k // h) * (sigma - 1) ** ((N - k) // h)
    return tot


def paper_formula(n, d, sigma):
    """Theorem 4.4 of the paper (square torus Z_n^d), coded from the paper's vector form."""
    ps = prime_factors(n)
    N = n ** d
    tot = 0
    for v in itertools.product(range(d + 1), repeat=len(ps)):
        if not any(v):
            continue
        c = prod(p ** comb(vp, 2) * gauss_prod(d, vp, p) for p, vp in zip(ps, v))
        tot += (-1) ** (1 + sum(v)) * c * sigma ** (N // prod(p ** vp for p, vp in zip(ps, v)))
    return tot


# ---------------------------------------------------------------- the group
class Group:
    def __init__(self, ns):
        self.ns = tuple(ns)
        self.N = prod(ns)
        self.elems = list(itertools.product(*[range(n) for n in ns]))
        idx = {e: i for i, e in enumerate(self.elems)}
        self.add = np.array([[idx[tuple((a + b) % n for a, b, n in zip(x, y, ns))]
                              for y in self.elems] for x in self.elems], dtype=np.int64)


# ---------------------------------------------------------------- (B) brute force
def brute(G, sigma, chunk=1 << 18, by_k=False):
    N = G.N
    total = sigma ** N
    perms = [G.add[:, v] for v in range(1, N)]        # u -> u + v, every nonzero v (index 0 = identity)
    count = 0
    hist = np.zeros(N + 1, dtype=np.int64)           # symmetric configurations by number of cells in state 0
    for start in range(0, total, chunk):
        idx = np.arange(start, min(total, start + chunk), dtype=np.int64)
        cfg = np.empty((idx.size, N), dtype=np.int8)
        x = idx.copy()
        for j in range(N):                             # base-sigma digits: cfg[:, j] = s(element j)
            cfg[:, j] = x % sigma
            x //= sigma
        sym = np.zeros(idx.size, dtype=bool)
        for pv in perms:
            sym |= (cfg[:, pv] == cfg).all(axis=1)
        count += int(sym.sum())
        if by_k:
            hist += np.bincount((cfg[sym] == 0).sum(axis=1), minlength=N + 1)
    return (count, hist) if by_k else count


# ---------------------------------------------------------------- (L) the subgroup lattice
def subgroups(G):
    N = G.N
    def mask(elems):
        m = 0
        for e in elems:
            m |= 1 << int(e)
        return m
    def members(m):
        return [i for i in range(N) if m >> i & 1]
    cyc = set()
    for g in range(N):
        cur, seen = 0, [0]
        while True:
            cur = int(G.add[cur, g])
            if cur == 0:
                break
            seen.append(cur)
        cyc.add(mask(seen))
    subs, frontier = set(cyc) | {1}, list(cyc)
    cyc = list(cyc)
    while frontier:
        new = []
        for H in frontier:
            hm = members(H)
            for C in cyc:
                if C & ~H == 0:
                    continue
                cm = members(C)
                J = mask(G.add[np.ix_(hm, cm)].ravel())
                if J not in subs:
                    subs.add(J)
                    new.append(J)
        frontier = new
    return subs


def lattice_count(G, sigma):
    subs = sorted(subgroups(G), key=lambda m: bin(m).count("1"))
    assert subs[0] == 1                                  # the trivial subgroup {0}
    mu = {}
    for H in subs:
        mu[H] = 1 if H == 1 else -sum(mu[K] for K in mu if K & ~H == 0)
    aperiodic = sum(mu[H] * sigma ** (G.N // bin(H).count("1")) for H in subs)
    return sigma ** G.N - aperiodic, len(subs)


def union_count(G, sigma):
    """(U) the definition read as a union: S_G = U_{v != 0} Fix(<v>). Inclusion-exclusion over the distinct
    nontrivial cyclic subgroups, carried as a signed count per join (Fix(H) n Fix(K) = Fix(H + K)); |Fix(J)|
    = sigma^(number of cosets of J), the cosets counted on the group. No prime-order reduction, no Moebius
    values, no Gaussian binomials."""
    N = G.N
    cyc = set()
    for g in range(1, N):
        cur, seen = 0, {0}
        while True:
            cur = int(G.add[cur, g])
            if cur == 0:
                break
            seen.add(cur)
        cyc.add(frozenset(seen))
    def join(H, K):
        return frozenset(int(G.add[h, k]) for h in H for k in K)
    def cosets(J):
        left, c = set(range(N)), 0
        while left:
            u = left.pop()
            left -= {int(G.add[u, j]) for j in J}
            c += 1
        return c
    dp = {}                                            # join -> sum over subsets T with that join of (-1)^(|T|+1)
    for C in cyc:
        new = dict(dp)
        for J, w in dp.items():
            K = join(J, C)
            new[K] = new.get(K, 0) - w
        new[C] = new.get(C, 0) + 1
        dp = {J: w for J, w in new.items() if w}
    return sum(w * sigma ** cosets(J) for J, w in dp.items()), len(cyc)


# ---------------------------------------------------------------- driver
def rect_groups(maxN, maxk, minn=2):
    out = []
    for k in range(1, maxk + 1):
        for ns in itertools.combinations_with_replacement(range(minn, maxN + 1), k):
            if prod(ns) <= maxN:
                out.append(ns)
    return out


def main():
    fails = 0
    def check(ok, msg):
        nonlocal fails
        print(("  ok   " if ok else "  FAIL ") + msg)
        if not ok:
            fails += 1

    print("[1] closed formula: divisor coding = vector coding; Gaussian binomials: product = q-Pascal")
    n_cmp = 0
    for ns in rect_groups(400, 4):
        for sigma in (1, 2, 3, 5):
            a, b = formula_divisor(ns, sigma), formula_vector(ns, sigma)
            if a != b:
                check(False, f"{ns} sigma={sigma}: {a} != {b}")
            n_cmp += 1
    for q in (2, 3, 4, 5, 7):
        for d in range(0, 8):
            for r in range(0, d + 2):
                if gauss_prod(d, r, q) != gauss_pascal(d, r, q):
                    check(False, f"gauss {d},{r},{q}")
    check(True, f"{n_cmp} (group, sigma) pairs agree; Gaussian binomials agree for q<=7, d<=7")

    print("[2] brute force (B) = lattice (L) = formula (F)")
    plan = [(2, 20), (3, 12), (4, 9), (5, 8)]           # (sigma, max N): sigma^N <= ~1.1e6
    n_b = 0
    for sigma, maxN in plan:
        for ns in rect_groups(maxN, 4):
            G = Group(ns)
            b = brute(G, sigma)
            l, nsub = lattice_count(G, sigma)
            f = formula_divisor(ns, sigma)
            ok = b == l == f
            n_b += 1
            if not ok or sigma == 2 and G.N in (12, 16, 18, 20):
                check(ok, f"Z{ns} sigma={sigma}: brute {b}, lattice {l} ({nsub} subgroups), formula {f}")
    check(fails == 0, f"{n_b} groups x alphabets checked by brute force (all rectangular groups with "
                      f"n_i >= 2, at most 4 factors, sigma^N <= 2^20)")

    print("[3] lattice (L) = formula (F) beyond brute force")
    n_l = 0
    big = [ns for ns in rect_groups(144, 4) if prod(ns) > 20]
    big += [(2, 2, 2, 2, 2, 2), (3, 3, 3, 3), (2, 2, 2, 2, 4), (6, 6, 6), (2, 4, 8), (5, 5, 5), (7, 7, 7), (3, 9, 9), (4, 4, 4, 4)]
    for ns in big:
        G = Group(ns)
        for sigma in (2, 3, 7):
            l, nsub = lattice_count(G, sigma)
            f = formula_divisor(ns, sigma)
            n_l += 1
            if l != f:
                check(False, f"Z{ns} sigma={sigma}: lattice {l} != formula {f}")
    check(fails == 0, f"{n_l} (group, sigma) pairs, N up to {max(prod(ns) for ns in big)}")

    print("[4] square tori: formula (F) = paper Theorem 4.4; reference values")
    for n in range(2, 31):
        for d in range(1, 5):
            for sigma in (1, 2, 3):
                if formula_divisor((n,) * d, sigma) != paper_formula(n, d, sigma):
                    check(False, f"square {n}^{d} sigma={sigma}")
    ref = {(2, 2): 8, (3, 2): 26, (5, 2): 182, (2, 3): 72, (3, 3): 6398, (6, 2): 801064}
    check(all(formula_divisor((n,) * d, 2) == v for (n, d), v in ref.items()),
          "square tori n<=30, d<=4, sigma<=3 agree with Theorem 4.4; reference values 8, 26, 182, 72, 6398, 801064")

    print("[5] dependence on N and the p-ranks only (non-isomorphic groups)")
    pairs = [((2, 8), (4, 4)), ((2, 2, 4), (2, 8)), ((2, 16), (4, 8)), ((3, 27), (9, 9)),
             ((2, 2, 8), (2, 4, 4)), ((4, 12), (2, 24)), ((6, 36), (12, 18))]
    for a, b in pairs:
        Na, ra = ranks(a)
        Nb, rb = ranks(b)
        same = Na == Nb and ra == rb
        la, _ = lattice_count(Group(a), 2)
        lb, _ = lattice_count(Group(b), 2)
        check((la == lb) == same and formula_divisor(a, 2) == la and formula_divisor(b, 2) == lb,
              f"Z{a} vs Z{b}: N {Na}/{Nb}, ranks {ra}/{rb}: lattice {la} / {lb} "
              f"({'equal, as predicted' if same else 'different ranks'})")

    print("[6] N | sigma^N - |S_G|")
    bad = [(ns, s) for ns in rect_groups(60, 3) for s in (2, 3, 4, 5)
           if (s ** prod(ns) - formula_divisor(ns, s)) % prod(ns) != 0]
    check(not bad, f"all rectangular groups with N <= 60, sigma in 2..5 ({len(bad)} failures)")

    print("[7] k-active counts (Corollary (d)): brute force per k = formula, every k")
    n_k = 0
    for sigma, maxN in [(2, 16), (3, 10), (4, 8)]:
        for ns in rect_groups(maxN, 4):
            tot, hist = brute(Group(ns), sigma, by_k=True)
            N = prod(ns)
            for k in range(N + 1):
                f = formula_kactive(ns, sigma, k)
                n_k += 1
                if f != hist[k]:
                    check(False, f"Z{ns} sigma={sigma} k={k}: brute {hist[k]} != formula {f}")
            if sum(formula_kactive(ns, sigma, k) for k in range(N + 1)) != formula_divisor(ns, sigma):
                check(False, f"Z{ns} sigma={sigma}: k-active counts do not sum to |S_G|")
    check(fails == 0, f"{n_k} (group, sigma, k) triples; the k-active counts sum to |S_G|")

    print("[8] fixed N: |S_G| strictly increasing in the rank profile (Corollary 4.8(ii); formula only)")
    n_pairs = 0
    for N in range(2, 1025):
        f = factorization(N)
        ps = sorted(f)
        profiles = list(itertools.product(*[range(1, f[p] + 1) for p in ps]))   # d_p in 1..e_p
        for sigma in (2, 3):
            val = {}
            for prof in profiles:
                ns = []                                   # a group with these ranks: d_p factors
                for p, dpp in zip(ps, prof):              # p^(e-d+1) x p x ... x p
                    ns += [p ** (f[p] - dpp + 1)] + [p] * (dpp - 1)
                assert prod(ns) == N and ranks(tuple(ns))[1] == dict(zip(ps, prof))
                val[prof] = formula_divisor(tuple(ns), sigma)
            for x in profiles:
                for y in profiles:
                    if x != y and all(a <= b for a, b in zip(x, y)):
                        n_pairs += 1
                        if not val[x] < val[y]:
                            check(False, f"N={N} sigma={sigma}: ranks {x} -> {val[x]} not < {y} -> {val[y]}")
    check(fails == 0, f"{n_pairs} comparable (profile, profile', sigma) pairs, N <= 1024, sigma in (2, 3): "
                      f"the cyclic group is the minimizer at fixed N")

    print("[9] Corollary 4.8(ii) identity: raising d_p by one at fixed N adds exactly p^(d_p) * ac(G''), |G''| = N/p, ranks of G")
    def ac(N, dp, sigma):                       # aperiodic count from the rank form (any group with these ranks)
        ns = []
        f = factorization(N)
        for q, e in f.items():
            k = dp.get(q, 0)
            ns += ([q ** (e - k + 1)] + [q] * (k - 1)) if k else []
        assert prod(ns) == N or N == 1
        return sigma ** N - (formula_divisor(tuple(ns), sigma) if N > 1 else 0)
    n_id = 0
    for N in range(2, 2001):
        f = factorization(N)
        ps = sorted(f)
        for prof in itertools.product(*[range(1, f[q] + 1) for q in ps]):
            dp = dict(zip(ps, prof))
            for q in ps:
                if dp[q] + 1 > f[q]:
                    continue
                dp2 = dict(dp); dp2[q] += 1
                for sigma in (2, 3, 5):
                    lhs = ac(N, dp, sigma) - ac(N, dp2, sigma)          # = |S_G'| - |S_G|
                    dpp = dict(dp)                                       # G'': order N/q, ranks of G
                    rhs = q ** dp[q] * ac(N // q, {r: k for r, k in dpp.items() if (N // q) % r == 0}, sigma)
                    n_id += 1
                    if lhs != rhs or rhs <= 0:
                        check(False, f"N={N} ranks={dp} p={q} sigma={sigma}: {lhs} vs {rhs}")
    check(fails == 0, f"{n_id} single rank steps (N <= 2000, sigma in 2, 3, 5): identity exact and the increment positive")

    print("[10] Remark 4.9(i): k-active counts by the full subgroup lattice (weights |Fix_k(H)|) = formula, every k")
    n_k10 = 0
    for ns in [g for g in rect_groups(64, 4) if prod(g) >= 4] + [(2, 2, 2, 2, 2), (3, 3, 3), (2, 4, 8), (6, 6)]:
        G = Group(ns)
        N = G.N
        subs = sorted(subgroups(G), key=lambda m: bin(m).count("1"))
        mu = {}
        for H in subs:
            mu[H] = 1 if H == 1 else -sum(mu[K] for K in mu if K & ~H == 0)
        for sigma in (2, 3):
            for k in range(N + 1):
                # aperiodic k-active count = sum_H mu(0,H) |Fix_k(H)|, |Fix_k(H)| = C(N/h, k/h)(sigma-1)^((N-k)/h) if h | k
                ap = 0
                for H in subs:
                    h = bin(H).count("1")
                    if k % h == 0:
                        ap += mu[H] * comb(N // h, k // h) * (sigma - 1) ** ((N - k) // h)
                total = comb(N, k) * (sigma - 1) ** (N - k)
                n_k10 += 1
                if total - ap != formula_kactive(ns, sigma, k):
                    check(False, f"Z{ns} sigma={sigma} k={k}: lattice {total - ap} != formula {formula_kactive(ns, sigma, k)}")
    check(fails == 0, f"{n_k10} (group, sigma, k) triples, N <= 64 (and four larger groups): lattice = formula")

    print("[11] Corollary 4.8(i) example: Z2 x Z24 and Z4 x Z12 (non-isomorphic; N = 48, d_2 = 2, d_3 = 1)")
    def orders(G):
        out = []
        for g in range(G.N):
            k, cur = 1, g
            while cur != 0:
                cur, k = int(G.add[cur, g]), k + 1
            out.append(k if g else 1)
        return sorted(out)
    G1, G2 = Group((2, 24)), Group((4, 12))
    check(orders(G1) != orders(G2) and max(orders(G1)) == 24 and max(orders(G2)) == 12,
          "non-isomorphic: largest element orders 24 and 12")
    for sigma, expect in ((2, 50388256), (3, 847330573761)):
        vals = []
        for G in (G1, G2):
            u, ncyc = union_count(G, sigma)
            l, nsub = lattice_count(G, sigma)
            f = formula_divisor(G.ns, sigma)
            vals.append((u, l, f, ncyc, nsub))
        ok = all(u == l == f == expect for u, l, f, _, _ in vals)
        check(ok, f"sigma={sigma}: union (U) = lattice (L) = formula (F) = {expect} for both groups "
                  f"({vals[0][3]} / {vals[1][3]} nontrivial cyclic subgroups, {vals[0][4]} / {vals[1][4]} subgroups)")

    print("ALL PASSED" if fails == 0 else f"{fails} FAILURES")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
