#!/usr/bin/env python3
"""
verify_erratum.py -- exact checks of every number and claim in
research/2d_fix_note/banda2d_bounds_fix.tex, the erratum to

  P. Banda, J. Caughman, M. Cenek, C. Teuscher, "Shift-symmetric
  configurations in two-dimensional cellular automata: Irreversibility,
  insolvability, and enumeration", Chaos 29, 063120 (2019),
  doi:10.1063/1.5089889, arXiv:1703.09030v2 (equation and lemma numbers
  below are those of arXiv v2, which the version of record shares).

Python 3 standard library only.  Every count and every inequality is
checked in exact integer or rational arithmetic (irrational quantities such
as sigma^(A/2) or log2(n) are removed by squaring, by raising to an integer
power, or by a certified rational bound).  Floats appear only in printed
decimal displays and in the optional plot-consistency check [F4].

Sections (item numbers refer to the numbered list of the erratum):
  [A] the count |S_{nxn}| (Eq. 19 = q^k): formula vs definition-level brute
      force vs an independent inclusion-exclusion over explicitly
      constructed subgroups; reference values.
  [B] item 1: standing assumptions n >= 2, |Sigma| >= 2; the exact set of
      degenerate exceptions of Eqs. (21)-(24) and (28).
  [C] items 2-3: k-active counts.  Brute force at the multi-prime n = 6;
      Eqs. (30), (31), corrected (32)-(33) vs subgroup IE for all
      0 <= k <= n^2; the printed (32)-(33) and its counterexample; the
      coincidence for prime powers; Lemma E.29 / Eq. (28).
  [D] item 4: proof of Lemma E.21 (prime powers; the strict base step).
  [E] item 5: the chains of Lemmas A.21/A.22 and their replacement
      (failure sets; the false first step of the A.22 chain; Lemma R1 =
      union identity on rectangular tori; the bounds used by Lemmas R2/R3;
      the statements A.21-A.24, E.21, E.22).
  [F] main text of the 2019 paper unchanged: P^unif and P^dens values,
      Fig. 7, and (optional, --fig9 PDF) the plotted curve of Fig. 9.

Run (from any directory):
  python3 verify_erratum.py [--fig9 PATH/arXiv-1703.09030v2.pdf] > verify_erratum_output.txt
Exit code 0 iff every check passes.
"""

import sys
import time
import math
import hashlib
import platform
import itertools
from fractions import Fraction
from math import comb, gcd, prod
from collections import Counter

sys.stdout.reconfigure(line_buffering=True)
T0 = time.time()
FAILS = []
NCHECKS = 0


def check(ok, label):
    global NCHECKS
    NCHECKS += 1
    print(f"    [{'OK' if ok else 'FAIL'}] {label}")
    if not ok:
        FAILS.append(label)


# ----------------------------------------------------------------------
# number theory
# ----------------------------------------------------------------------
def primes_of(n):
    """distinct prime factors of n, increasing"""
    ps, m, q = [], n, 2
    while q * q <= m:
        if m % q == 0:
            ps.append(q)
            while m % q == 0:
                m //= q
        q += 1
    if m > 1:
        ps.append(m)
    return ps


def is_prime(n):
    return n >= 2 and primes_of(n) == [n]


def is_composite(n):
    return n >= 4 and not is_prime(n)


def multi_prime(limit, lo=6):
    for n in range(lo, limit + 1):
        ps = primes_of(n)
        if len(ps) >= 2:
            yield n, ps


def log2_lower(n, den=1024):
    """certified rational L <= log2(n): largest a/den with 2^a <= n^den"""
    t = n ** den
    a = t.bit_length() - 1          # 2^a <= t < 2^(a+1)
    return Fraction(a, den)


# ----------------------------------------------------------------------
# the 2019 formulas
# ----------------------------------------------------------------------
def r_of(p, v):
    return (1, p + 1, p)[v]


def qm(n, s, ps, m, c=Fraction(1)):
    """q^m_{nxn}(c) of Lemma A.21: sum over 0 < v <= 2 in {0,1,2}^m of
    (-1)^(1+|v|) s^(g(v) c) prod r(i), g(v) = n^2 / prod p_i^v_i,
    for the ordered prime list ps (only ps[:m] is used)."""
    tot = 0
    for v in itertools.product(range(3), repeat=m):
        if not any(v):
            continue
        h = prod(ps[i] ** v[i] for i in range(m))
        e = Fraction(n * n, h) * c
        assert e.denominator == 1, (n, ps, m, c, v)
        tot += (-1) ** (1 + sum(v)) * s ** int(e) * prod(r_of(ps[i], v[i]) for i in range(m))
    return tot


def S_formula(n, s):
    """|S_{nxn}| by Eq. (19) (= q^k, k = omega(n)); n = 1 gives the empty sum 0"""
    ps = primes_of(n)
    return qm(n, s, ps, len(ps))


def fix_k(N, h, k, s):
    """|Fix(H) cap D^a_k| for |H| = h on a torus of N cells, with the
    convention: 0 unless k/h is an integer in {0..N/h}; 0^0 = 1"""
    if k % h or k < 0 or k // h > N // h:
        return 0
    return comb(N // h, k // h) * (s - 1) ** ((N - k) // h)


def kgcd_primes(n, k):
    return primes_of(gcd(k, n))     # gcd(0, n) = n


def eq30(n, k, s):
    N, rs = n * n, kgcd_primes(n, k)
    tot = 0
    for u in itertools.product(*[range(r + 2) for r in rs]):
        if not any(u):
            continue
        h = prod(r ** min(ui, 2) for r, ui in zip(rs, u))
        tot += (-1) ** (1 + sum(u)) * prod(comb(r + 1, ui) for r, ui in zip(rs, u)) * fix_k(N, h, k, s)
    return tot


def eq31(n, k, s):
    N, rs = n * n, kgcd_primes(n, k)
    tot = 0
    for v in itertools.product(range(3), repeat=len(rs)):
        if not any(v):
            continue
        h = prod(r ** v_i for r, v_i in zip(rs, v))
        top = [v_i if v_i < 2 else r + 1 for r, v_i in zip(rs, v)]
        for u in itertools.product(*[range(v_i, t + 1) for v_i, t in zip(v, top)]):
            tot += (-1) ** (1 + sum(u)) * fix_k(N, h, k, s) * prod(comb(r + 1, ui) for r, ui in zip(rs, u))
    return tot


def eq32(n, k, s, pair=None):
    """Eq. (32).  pair=None: corrected, r(i) from the primes r_i of gcd(k,n).
    pair = list: printed reading, r(i) from pair[i] (the i-th prime of n under
    a labelling) while h(v) uses r_i."""
    N, rs = n * n, kgcd_primes(n, k)
    tot = 0
    for v in itertools.product(range(3), repeat=len(rs)):
        if not any(v):
            continue
        h = prod(r ** v_i for r, v_i in zip(rs, v))
        rr = rs if pair is None else pair
        tot += (-1) ** (1 + sum(v)) * fix_k(N, h, k, s) * prod(r_of(rr[i], v[i]) for i in range(len(rs)))
    return tot


def eq33(n, k, pair=None):
    """Eq. (33) (|Sigma| = 2): Eq. (32) without the factor (|Sigma|-1)^..."""
    N, rs = n * n, kgcd_primes(n, k)
    tot = 0
    for v in itertools.product(range(3), repeat=len(rs)):
        if not any(v):
            continue
        h = prod(r ** v_i for r, v_i in zip(rs, v))
        if k % h or k // h > N // h:
            continue
        rr = rs if pair is None else pair
        tot += (-1) ** (1 + sum(v)) * comb(N // h, k // h) * prod(r_of(rr[i], v[i]) for i in range(len(rs)))
    return tot


# ----------------------------------------------------------------------
# independent evaluator: inclusion-exclusion over explicitly constructed
# cyclic subgroups of prime order of Z_a x Z_b, joins by explicit sumsets
# ----------------------------------------------------------------------
def prime_order_subgroups(a, b, p):
    subs = set()
    for x in range(a):
        for y in range(b):
            if (x, y) != (0, 0) and (p * x) % a == 0 and (p * y) % b == 0:
                subs.add(frozenset(((j * x) % a, (j * y) % b) for j in range(p)))
    return sorted(subs, key=sorted)


def ie_coefficients(a, b, primes):
    """returns (Counter h -> sum over nonempty J with |<J>| = h of (-1)^(|J|+1),
    list of |L_p|) for L = all prime-order subgroups for the given primes"""
    Ls = [prime_order_subgroups(a, b, p) for p in primes]
    L = [C for Lp in Ls for C in Lp]
    coeff = Counter()

    def rec(i, H, size):
        if i == len(L):
            if size:
                coeff[len(H)] += (-1) ** (size + 1)
            return
        rec(i + 1, H, size)
        C = L[i]
        if C <= H:
            H2 = H
        else:
            H2 = frozenset(((h0 + c0) % a, (h1 + c1) % b) for (h0, h1) in H for (c0, c1) in C)
        rec(i + 1, H2, size + 1)

    rec(0, frozenset({(0, 0)}), 0)
    return coeff, [len(Lp) for Lp in Ls]


def ie_union(coeff, Ncells, s):
    return sum(c * s ** (Ncells // h) for h, c in coeff.items())


def ie_k(coeff, Ncells, k, s):
    return sum(c * fix_k(Ncells, h, k, s) for h, c in coeff.items())


# ----------------------------------------------------------------------
# definition-level brute force
# ----------------------------------------------------------------------
def torus_perms(a, b):
    """for every nonzero v in Z_a x Z_b: the permutation u -> u + v of cells"""
    cells = [(x, y) for x in range(a) for y in range(b)]
    idx = {c: i for i, c in enumerate(cells)}
    perms = {}
    for v in cells:
        if v == (0, 0):
            continue
        perms[v] = [idx[((x + v[0]) % a, (y + v[1]) % b)] for (x, y) in cells]
    return cells, perms


def brute_S(a, b, s, vectors=None):
    """# configurations of Z_a x Z_b over s symbols fixed by at least one of
    the given nonzero translations (default: all nonzero translations)"""
    cells, perms = torus_perms(a, b)
    P = list(perms.values()) if vectors is None else [perms[v] for v in vectors]
    cnt = 0
    for cfg in itertools.product(range(s), repeat=len(cells)):
        for pm in P:
            if all(cfg[pm[i]] == cfg[i] for i in range(len(cells))):
                cnt += 1
                break
    return cnt


def brute_k_subsets(n, jmax):
    """number of j-subsets U of the n x n torus with U + v = U for some
    nonzero v, for j = 0..jmax < n^2 (definition level: U + v = U forces
    v = w - u0 for some w in U other than the least element u0, and every such
    candidate v is tested in full)"""
    cells, perms = torus_perms(n, n)
    N = n * n
    inv = {i: c for i, c in enumerate(cells)}
    vec_of = {}
    for i in range(N):
        for j in range(N):
            vec_of[(i, j)] = ((inv[j][0] - inv[i][0]) % n, (inv[j][1] - inv[i][1]) % n)
    out = {0: 1}  # empty set is fixed by every v
    for jj in range(1, jmax + 1):
        cnt = 0
        for U in itertools.combinations(range(N), jj):
            Us = set(U)
            u0 = U[0]
            for w in U:
                v = vec_of[(u0, w)] if w != u0 else None
                if v is None:
                    continue
                pm = perms[v]
                if all(pm[x] in Us for x in U):
                    cnt += 1
                    break
        out[jj] = cnt
    return out


def brute_k_sigma3_high(n, jmax):
    """sigma = 3, symbols {a, b, c}: number of configurations with exactly
    k = n^2 - j cells in state a that are fixed by some nonzero translation,
    for j = 0..jmax; W = set of non-a cells, coloured in {b, c}"""
    cells, perms = torus_perms(n, n)
    N = n * n
    out = {}
    for j in range(0, jmax + 1):
        if j == 0:
            out[N] = 1  # constant configuration
            continue
        cnt = 0
        for W in itertools.combinations(range(N), j):
            Ws = set(W)
            # candidate translations: those mapping W into W (necessary)
            cands = []
            w0 = W[0]
            for w in W:
                if w == w0:
                    continue
                v = ((cells[w][0] - cells[w0][0]) % n, (cells[w][1] - cells[w0][1]) % n)
                pm = perms[v]
                if all(pm[x] in Ws for x in W):
                    cands.append(pm)
            if not cands:
                continue
            for col in itertools.product((1, 2), repeat=j):
                cfg = [0] * N
                for x, cl in zip(W, col):
                    cfg[x] = cl
                for pm in cands:
                    if all(cfg[pm[x]] == cfg[x] for x in W):
                        cnt += 1
                        break
        out[N - j] = cnt
    return out


def dec(fr, digits=4):
    """decimal display of a positive Fraction: exact digits, truncated (not rounded)"""
    if fr == 0:
        return "0"
    e = 0
    while fr >= 10:
        fr /= 10
        e += 1
    while fr < 1:
        fr *= 10
        e -= 1
    mant = fr.numerator * 10 ** (digits - 1) // fr.denominator
    s = str(mant)
    return f"{s[0]}.{s[1:]}e{e:+d}"


def log10_ratio(num, den):
    """log10(num/den) for positive big ints, float display only"""
    a = num >> max(0, num.bit_length() - 60)
    b = den >> max(0, den.bit_length() - 60)
    return (math.log10(a) + max(0, num.bit_length() - 60) * math.log10(2)
            - math.log10(b) - max(0, den.bit_length() - 60) * math.log10(2))


# ======================================================================
def section_A():
    print("\n[A] |S_{nxn}| (Eq. 19): formula vs brute force vs explicit-subgroup IE")
    # brute force, every nonzero translation
    for (n, s, expect) in [(2, 2, 8), (2, 3, None), (3, 2, 26), (3, 3, None), (4, 2, 736)]:
        bf = brute_S(n, n, s)
        fo = S_formula(n, s)
        tag = f" (reference {expect})" if expect else ""
        check(bf == fo and (expect is None or bf == expect),
              f"n={n} sigma={s}: brute force {bf} = Eq. (19) {fo}{tag}")
    # explicit-subgroup IE on square tori (all primes of n)
    for n in (2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 15, 30):
        coeff, Lsz = ie_coefficients(n, n, primes_of(n))
        ok = Lsz == [p + 1 for p in primes_of(n)]
        for s in (2, 3, 5):
            ok &= ie_union(coeff, n * n, s) == S_formula(n, s)
        check(ok, f"n={n}: IE over {sum(Lsz)} explicit prime-order subgroups = Eq. (19) at sigma=2,3,5")
    check(S_formula(5, 2) == 182 and S_formula(6, 2) == 801064, "reference values |S_{5x5}|=182, |S_{6x6}|=801064 (sigma=2)")


def section_B():
    print("\n[B] item 1: standing assumptions n>=2, |Sigma|>=2; degenerate exceptions")
    fails = []
    for n in range(1, 41):
        for s in range(1, 5):
            S = 0 if n == 1 else S_formula(n, s)
            F = (n + 1) * s ** n - n * s
            L = log2_lower(n) if n >= 2 else Fraction(0)
            e22 = S * S <= 36 * L * L * s ** (n * n) if n >= 2 else S == 0   # S <= 6 log2(n) s^(n^2/2)
            rows = {
                "Eq21 bound": F <= S,
                "Eq21 iff": (F == S) == is_prime(n),
                "Eq22": e22,
                "Eq23": F <= S and e22,
                "Eq24 lower": n * s ** n <= S,          # n s^(-n^2+n) <= S/s^(n^2)
                "Eq24 upper": e22,
            }
            for name, ok in rows.items():
                if not ok:
                    fails.append((name, n, s))
    bad = [f for f in fails if f[1] >= 2 and f[2] >= 2]
    check(not bad, f"Eqs. (21)-(24): no failure with n>=2, sigma>=2 (n<=40, sigma<=4); {len(fails)} degenerate failures")
    kinds = Counter((f[0], 'n=1' if f[1] == 1 else 'sigma=1') for f in fails)
    for kk in sorted(kinds):
        print(f"      {kk[0]:<11} fails at {kk[1]}: {kinds[kk]} cases")
    n1 = sorted({f[0] for f in fails if f[1] == 1})
    s1 = sorted({f[0] for f in fails if f[1] >= 2 and f[2] == 1})
    check(n1 == ["Eq21 bound", "Eq23", "Eq24 lower"], f"n=1 (|S_1x1|=0): failing = {n1}")
    s1_iff = sorted({f[1] for f in fails if f[0] == "Eq21 iff" and f[2] == 1 and f[1] >= 2})
    check(s1 == ["Eq21 iff", "Eq24 lower"] and s1_iff == [m for m in range(2, 41) if is_composite(m)],
          f"sigma=1, n>=2: failing = {s1}; 'iff' fails exactly at the composite n")
    check(all(S_formula(n, 1) == 1 for n in range(2, 41)), "sigma=1: Eq. (19) gives |S|=1 (the single configuration) for 2<=n<=40")
    # Eq. (28) brute force: S^a_k(v) nonempty iff |<v>| divides k  -- needs k <= n^2 and sigma >= 2
    ok_std, viol = True, []
    for n, s in ((2, 2), (2, 3), (3, 2), (3, 3), (4, 2)):
        cells, perms = torus_perms(n, n)
        N = n * n
        for v, pm in perms.items():
            order = n // gcd(gcd(v[0], v[1]), n)
            fixed = [cfg for cfg in itertools.product(range(s), repeat=N)
                     if all(cfg[pm[i]] == cfg[i] for i in range(N))]
            ks = Counter(sum(1 for x in cfg if x == 0) for cfg in fixed)
            for k in range(0, N + 3):
                nonempty = ks[k] > 0
                if nonempty != (k % order == 0 and k <= N):
                    ok_std = False
                if nonempty != (k % order == 0):
                    viol.append((n, s, v, k))
                # Lemma E.29 count
                if k <= N and k % order == 0 and ks[k] != fix_k(N, order, k, s):
                    ok_std = False
    check(ok_std, "Eq. (28) and Lemma E.29 by brute force (n<=4): exact for 0<=k<=n^2, sigma>=2")
    check(viol and all(k > n * n for (n, s, v, k) in viol),
          f"Eq. (28) read for every k fails only at k>n^2 ({len(viol)} cases, e.g. {viol[0]})")
    # sigma = 1: D^a_k is empty for k < n^2, so Eq. (28) fails at sigma = 1
    check(all(fix_k(n * n, 1, k, 1) == 0 for n in (2, 3) for k in range(n * n)),
          "sigma=1: no configuration has k<n^2 cells in state a (Eq. (28) needs sigma>=2)")


def section_C():
    print("\n[C] items 2-3: k-active counts, Eqs. (30)-(33)")
    n, N = 6, 36
    t = time.time()
    sub = brute_k_subsets(6, 6)
    print(f"      brute force over all j-subsets of the 6x6 torus, j<=6 ({time.time() - t:.1f} s)")
    # sigma = 2: a configuration is its set of a-cells; complement symmetric too
    bf2 = {}
    for j, c in sub.items():
        bf2[j] = c
        bf2[N - j] = c
    t = time.time()
    bf3 = brute_k_sigma3_high(6, 4)
    print(f"      brute force sigma=3, k=32..36 ({time.time() - t:.1f} s)")
    coeff6, _ = ie_coefficients(6, 6, [2, 3])
    rows_ok = True
    print("        k  brute  Eq30  Eq31  Eq32corr  Eq32printed  Eq33corr  Eq33printed  (sigma=2)")
    for k in sorted(bf2):
        vals = (bf2[k], eq30(6, k, 2), eq31(6, k, 2), eq32(6, k, 2), eq32(6, k, 2, [2, 3]),
                eq33(6, k), eq33(6, k, [2, 3]), ie_k(coeff6, N, k, 2))
        rows_ok &= len({vals[0], vals[1], vals[2], vals[3], vals[5], vals[7]}) == 1
        print(f"      {k:3d} {vals[0]:6d} {vals[1]:5d} {vals[2]:5d} {vals[3]:9d} {vals[4]:12d} {vals[5]:9d} {vals[6]:12d}")
    check(rows_ok, "n=6, sigma=2, k in 0..6 and 30..36: brute force = Eq30 = Eq31 = corrected Eq32 = corrected Eq33 = IE")
    check(bf2[3] == 48 and eq32(6, 3, 2, [2, 3]) == 36 and eq33(6, 3, [2, 3]) == 36,
          "counterexample n=6, k=3, sigma=2: printed Eqs. (32),(33) give 36, true count 48")
    L3 = prime_order_subgroups(6, 6, 3)
    two = {len(frozenset(((a0 + b0) % 6, (a1 + b1) % 6) for (a0, a1) in C for (b0, b1) in D))
           for C in L3 for D in L3 if C != D}
    check(len(L3) == 4 and fix_k(36, 3, 3, 2) == comb(12, 1) == 12 and two == {9} and fix_k(36, 9, 3, 2) == 0
          and all(fix_k(36, h, 3, 2) == 0 for h in (2, 4)),
          "n=6, k=3: four subgroups of order 3, each fixing C(12,1)=12 such configurations; any two generate order 9 (fixes none); order-2 subgroups fix none")
    ok3 = all(bf3[k] == eq30(6, k, 3) == eq31(6, k, 3) == eq32(6, k, 3) == ie_k(coeff6, N, k, 3) for k in bf3)
    print("      sigma=3:", {k: (bf3[k], eq32(6, k, 3, [2, 3])) for k in sorted(bf3)}, "(brute, printed)")
    check(ok3, "n=6, sigma=3, k in 32..36: brute force = Eq30 = Eq31 = corrected Eq32 = IE")
    check(bf3[33] == 96 and eq32(6, 33, 3, [2, 3]) == 72, "n=6, k=33, sigma=3: true 96, printed 72 (k>n: range matters)")
    # every labelling of the primes of 6 fails at some k <= 6
    lab_ok = True
    for lab in itertools.permutations([2, 3]):
        bad = [k for k in range(0, 7) if len(kgcd_primes(6, k)) == 1 and eq32(6, k, 2, list(lab)) != bf2[k]]
        print(f"      labelling p=(p1,p2)={lab}: printed Eq. (32) wrong at k in {bad} (k<=6)")
        lab_ok &= bool(bad)
    check(lab_ok, "every labelling of the primes of n=6 gives a wrong value at some k<=6")
    # all k up to n^2, IE vs Eqs. (30)-(33); totals; printed failures
    for n in (6, 10, 12, 14, 15, 30):
        N = n * n
        coeff, _ = ie_coefficients(n, n, primes_of(n))
        ok, nprinted = True, 0
        for s in (2, 3):
            tot = 0
            for k in range(N + 1):
                ref = ie_k(coeff, N, k, s)
                ok &= ref == eq30(n, k, s) == eq31(n, k, s) == eq32(n, k, s)
                if s == 2:
                    ok &= ref == eq33(n, k)
                    nprinted += eq32(n, k, s, primes_of(n)) != ref
                tot += ref
            ok &= tot == S_formula(n, s)
        check(ok, f"n={n}: Eqs. (30),(31), corrected (32),(33) = subgroup IE for all 0<=k<={N}, sigma=2,3; sum_k = |S|"
                  f"  [printed Eq. (32) wrong at {nprinted} of {N + 1} k, sigma=2]")
    # prime powers: printed = corrected
    ok = all(eq32(n, k, s, primes_of(n)) == eq32(n, k, s)
             for n in (2, 3, 4, 5, 7, 8, 9, 16, 25, 27, 32) for k in range(n * n + 1) for s in (2, 3))
    check(ok, "n prime or prime power (n<=32): printed Eq. (32) = corrected for all k, sigma=2,3")
    # k > n is needed: Eq. (34) sums to n^2 and the formulas hold there (above)


def section_D():
    print("\n[D] item 4: proof of Lemma E.21")
    pp = [n for n in range(4, 401) if len(primes_of(n)) == 1 and not is_prime(n)]
    ok = all(S_formula(n, s) > (n + 1) * s ** n - n * s for n in pp for s in (2, 3, 4))
    check(ok, f"prime powers n=p^a, a>=2, n<=400 ({len(pp)} values), sigma=2,3,4: |S| > (n+1)s^n - ns (k=1 branch's 'equality' false)")
    check(S_formula(4, 2) == 736 and 5 * 2 ** 4 - 4 * 2 == 72, "n=4, sigma=2: |S|=736 (brute force in [A]) vs 72")
    ok, cases = True, 0
    for n in range(4, 401):
        if not is_composite(n):
            continue
        for s in (2, 3, 4):
            S = S_formula(n, s)
            F = (n + 1) * s ** n - n * s
            for p in primes_of(n):     # q^1 for any choice of first prime
                cases += 1
                A = n * n // p
                q1 = (p + 1) * s ** A - p * s ** (n * n // (p * p))
                ok &= q1 == qm(n, s, [p], 1)
                ok &= p * 2 <= n and S >= q1 >= s ** A >= s ** (2 * n) >= (n + 1) * s ** n > F
    check(ok, f"all composite n<=400, every prime p|n, sigma=2,3,4 ({cases} cases): "
              "|S| >= q^1 >= s^(n^2/p) >= s^(2n) >= (n+1)s^n > F, p <= n/2")
    ok = all((((n + 1) * s ** n - n * s) <= S_formula(n, s)) and
             ((((n + 1) * s ** n - n * s) == S_formula(n, s)) == is_prime(n))
             for n in range(2, 301) for s in (2, 3, 4))
    check(ok, "Lemma E.21 statement: bound and equality-iff-prime, 2<=n<=300, sigma=2,3,4")


def chain_quantities(n, s, ps, m):
    p = ps[m]
    A = n * n // p
    x0 = qm(n, s, ps, m)
    qp = qm(n, s, ps, m, Fraction(1, p))
    qpp = qm(n, s, ps, m, Fraction(1, p * p))
    x1 = -(p + 1) * qp
    x2 = p * qpp
    y1 = s ** A * (p + 1)
    y2 = -(s ** (n * n // (p * p))) * p
    return p, A, x0, qp, qpp, x1, x2, y1, y2


def section_E():
    print("\n[E] item 5: Lemmas A.21/A.22 -- chains and repair")
    # E1: failure sets, exact: cond21 <=> 2^(A-2) >= n^8 ; cond22 <=> 2^(5A) >= n^24
    def c21(n, A):
        return True if A - 2 >= 8 * n.bit_length() else (A >= 2 and 2 ** (A - 2) >= n ** 8)

    def c22(n, A):
        return True if 5 * A >= 24 * n.bit_length() else 2 ** (5 * A) >= n ** 24

    f21, f22, u21, u22 = [], [], set(), set()
    for n, ps in multi_prime(5000):
        for m in range(1, len(ps)):
            A = n * n // ps[m]
            if not c21(n, A):
                f21.append((n, m))
            if not c22(n, A):
                f22.append((n, m))
        for perm in itertools.permutations(ps):
            for m in range(1, len(ps)):
                A = n * n // perm[m]
                if not c21(n, A):
                    u21.add(n)
                if not c22(n, A):
                    u22.add(n)
    check(f21 == [(6, 1), (10, 1), (14, 1)] and f22 == [(6, 1)],
          f"increasing primes, n<=5000: A.21 last step fails at {f21}; A.22 last step at {f22}")
    check(u21 == {6, 10, 14} and u22 == {6}, f"any ordering of the primes: failing n = {sorted(u21)} (A.21), {sorted(u22)} (A.22)")
    check(all(n * n // ps[m] >= 2 * n for n, ps in multi_prime(2000) for m in range(len(ps))),
          "A = n^2/p >= 2n for every prime p of every multi-prime n <= 2000")

    # E2: first displayed step of the A.22 chain
    bad, cnt, ex = 0, 0, None
    for n, ps in multi_prime(200):
        for perm in (itertools.permutations(ps) if n <= 60 else [ps]):
            perm = list(perm)
            for m in range(1, len(perm)):
                for s in (2, 3):
                    p, A, x0, qp, qpp, x1, x2, y1, y2 = chain_quantities(n, s, perm, m)
                    lhs = Fraction(y1 - x1 - x2 - y2, p + 1)
                    rhs = s ** A + qp - qpp + s ** (A // p)
                    cnt += 1
                    ok = lhs < rhs and lhs - rhs == Fraction(qpp - s ** (A // p), p + 1) and qpp < s ** (A // p)
                    bad += not ok
                    if (n, m, s) == (6, 1, 2) and perm == [2, 3]:
                        ex = (lhs, rhs)
    check(bad == 0, f"A.22 chain, first step (y1-x1-x2-y2)/(p+1) >= s^A + q(1/p) - q(1/p^2) + s^(A/p) is FALSE in all {cnt} cases "
                    "(multi-prime n<=200, all m, sigma=2,3); LHS-RHS = (q(1/p^2)-s^(A/p))/(p+1) < 0")
    check(ex == (4278, 4280), f"n=6, |Sigma|=2: LHS = {ex[0]}, printed RHS = {ex[1]}")

    # E3: Lemma R1 -- union identity on rectangular tori
    print("      Lemma R1: q^m(c) = |union of Fix(C), C of order p_1..p_m| on Z_n x Z_(n/p) (c=1/p) and Z_(n/p)^2 (c=1/p^2)")
    nbf, nie, okR1 = 0, 0, True
    for n in (6, 10, 12, 14, 15, 18, 20, 21, 30):
        ps0 = primes_of(n)
        for perm in itertools.permutations(ps0):
            perm = list(perm)
            for m in range(1, len(perm)):
                p = perm[m]
                for (a, b, c) in ((n, n // p, Fraction(1, p)), (n // p, n // p, Fraction(1, p * p))):
                    coeff, Lsz = ie_coefficients(a, b, perm[:m])
                    okR1 &= Lsz == [q + 1 for q in perm[:m]]
                    for s in (2, 3, 5):
                        q = qm(n, s, perm, m, c)
                        okR1 &= ie_union(coeff, a * b, s) == q
                        nie += 1
                        if s ** (a * b) <= 2 ** 18:
                            # definition level: configurations fixed by some C (generator of C)
                            vecs = []
                            for qq in perm[:m]:
                                for C in prime_order_subgroups(a, b, qq):
                                    vecs.append(min(x for x in C if x != (0, 0)))
                            okR1 &= brute_S(a, b, s, vecs) == q
                            nbf += 1
    check(okR1, f"Lemma R1 identity: {nie} cases vs explicit-subgroup IE (|L_i| = p_i+1 asserted), {nbf} also vs brute force over all configurations")

    # E4-E7: sandwich, R2, R3, statements
    grid = []
    for n, ps in multi_prime(300):
        for perm in (itertools.permutations(ps) if n <= 100 else [ps]):
            for m in range(1, len(ps)):
                for s in (2, 3, 5):
                    grid.append((n, list(perm), m, s))
    okS = okR2 = okR3 = okStmt = True
    for n, perm, m, s in grid:
        p, A, x0, qp, qpp, x1, x2, y1, y2 = chain_quantities(n, s, perm, m)
        P = prod(perm[:m])
        Ssum = sum(q + 1 for q in perm[:m])
        okS &= sum(perm[:m]) <= P <= n // p and Ssum <= Fraction(2 * n, p) and p * 2 <= n
        for c, qv in ((Fraction(1, p), qp), (Fraction(1, p * p), qpp)):
            ub = sum((q + 1) * s ** int(Fraction(n * n, q) * c) for q in perm[:m])
            # ub <= (2n/p) s^(n^2 c / 2)  <=>  ub^2 <= (2n/p)^2 s^(n^2 c)
            okS &= 0 <= qv <= ub and ub * ub <= Fraction(2 * n, p) ** 2 * s ** int(n * n * c)
        # R2
        D = (p + 1) * s ** A - (y1 + x1 + y2)          # >= 0
        okR2 &= A >= 2 * n and D >= 0
        okR2 &= ((p + 1) * (2 * n + p)) ** 2 * s ** A >= (p * D) ** 2   # y1+x1+y2 >= (p+1)(s^A - (2n/p+1)s^(A/2))
        okR2 &= p * p * s ** A >= (2 * n + p) ** 2                      # s^(A/2) >= 2n/p + 1
        okR2 &= s ** A >= 4 ** n and 4 ** n >= (n + 1) ** 2 and (n + 1) * p >= 2 * n + p
        okR2 &= y1 + x1 + y2 >= 0
        # R3
        e = n * n // (p * p)
        okR3 &= x1 <= 0 and y2 <= 0 and x2 >= 0
        okR3 &= x2 * x2 <= 4 * n * n * s ** e <= y1 * y1               # x2 <= 2n s^(n^2/2p^2) <= y1
        okR3 &= Fraction(n * n, p) - Fraction(n * n, 2 * p * p) >= Fraction(3 * n, 2) and 4 * n * n <= 8 ** n
        q_next = qm(n, s, perm, m + 1)
        okR3 &= q_next == x0 + x1 + x2 + y1 + y2 and q_next <= x0 + 2 * y1 and x1 + x2 + y2 <= y1
        okStmt &= x0 <= q_next                                            # Lemma A.21
    check(okS, f"sandwich 0 <= q^m(c) <= sum(p_i+1)s^(n^2c/p_i) <= (2n/p)s^(n^2c/2), c=1/p and 1/p^2; sum p_i <= prod p_i <= n/p ({len(grid)} cases: multi-prime n<=300, all m, all prime orders for n<=100, sigma=2,3,5)")
    check(okR2, "Lemma R2: A>=2n, s^(A/2) >= 2^n >= n+1 >= 2n/p+1, y1+x1+y2 >= (p+1)s^(A/2)(s^(A/2)-2n/p-1) >= 0 (same grid)")
    check(okR3, "Lemma R3: x1<=0<=x2, y2<=0, x2 <= 2n s^(n^2/(2p^2)) <= y1, decomposition q^(m+1)=x0+x1+x2+y1+y2 <= x0+2y1 (same grid)")
    check(okStmt, "Lemma A.21 statement q^m <= q^(m+1) (same grid)")
    ok = True
    for n in range(2, 301):
        for s in (2, 3):
            S = S_formula(n, s)
            ok &= S <= 2 * sum(s ** (n * n // p) * (p + 1) for p in primes_of(n))
    check(ok, "Lemma A.22 statement |S| <= 2 sum s^(n^2/p_i)(p_i+1), 2<=n<=300, sigma=2,3")
    ok = True
    for n in range(2, 201):
        L = log2_lower(n)
        for s in (2, 3, 4):
            S = S_formula(n, s)
            ok &= S * S <= 36 * L * L * s ** (n * n)
    check(ok, "Lemma E.22 statement |S| <= 6 log2(n) s^(n^2/2), 2<=n<=200, sigma=2,3,4 (certified lower bound for log2 n)")
    ok = True
    for n in range(2, 41):
        for x in range(2, n + 1):
            for s in (2, 3):
                # s^(n^2/x)(x+1) <= s^(n^2/(x-1)) x  <=> raise to x(x-1)
                ok &= s ** (n * n * (x - 1)) * (x + 1) ** (x * (x - 1)) <= s ** (n * n * x) * x ** (x * (x - 1))
    check(ok, "Lemma A.23 for every integer 2<=x<=n (not only prime divisors), n<=40, sigma=2,3")
    # E8 witnesses at the failing pairs
    for n in (6, 10, 14):
        p, A, x0, qp, qpp, x1, x2, y1, y2 = chain_quantities(n, 2, primes_of(n), 1)
        print(f"      n={n}, sigma=2: y1={y1} x1={x1} x2={x2} y2={y2} y1+x1+y2={y1 + x1 + y2} y1-(x1+x2+y2)={y1 - x1 - x2 - y2}")
    p, A, x0, qp, qpp, x1, x2, y1, y2 = chain_quantities(6, 2, [2, 3], 1)
    check((y1 + x1 + y2, x2, y1 - x1 - x2 - y2) == (15632, 24, 17112), "n=6, sigma=2: y1+x1+y2=15632, x2=24, y1-(x1+x2+y2)=17112")


def pdens_scaled(n, variant, B=256):
    """sum_k floor(|S^a_k| 2^B / C(N,k)), sigma = 2 (Eq. 34 numerator), with
    |S^a_k| from Eq. (33): variant 'corr' (primes of gcd) or 'printed'
    (increasing primes of n).  Exact P^dens lies in
    [T/(N+1), (T+N+1)/(N+1)] * 2^-B."""
    N = n * n
    ps = primes_of(n)
    T = 0
    for k in range(N + 1):
        if gcd(k, n) == 1 and k not in (0, N):
            continue
        Sk = eq33(n, k) if variant == "corr" else eq33(n, k, ps)
        if Sk:
            T += (Sk << B) // comb(N, k)
    return T, N + 1


_PD = {}


def pdens_interval(n, variant, B=256):
    if (n, variant, B) not in _PD:
        T, D = pdens_scaled(n, variant, B)
        _PD[(n, variant, B)] = (Fraction(T, D << B), Fraction(T + D, D << B))
    return _PD[(n, variant, B)]


def section_F(fig9_pdf):
    print("\n[F] main text of the 2019 paper: values that must not change")
    check(Fraction(S_formula(2, 2), 2 ** 4) == Fraction(1, 2), "P^unif(2x2) = 1/2 (Sec. I: 0.5)")
    P10 = Fraction(S_formula(10, 2), 2 ** 100)
    check(Fraction(265, 10 ** 17) <= P10 < Fraction(275, 10 ** 17),
          f"P^unif(10x10) = {dec(P10, 4)}... in [2.65, 2.75) x 10^-15 (Sec. I: 'around 2.7 x 10^-15')")
    S100 = S_formula(100, 2)
    l10 = log10_ratio(S100, 2 ** 10000)
    check(round(l10) == -1505, f"log10 P^unif(100x100) = {l10:.2f} (Sec. VI: 'around 10^-1505')")
    check(brute_S(3, 3, 2) == 26, "Fig. 7: 26 binary shift-symmetric configurations on 3x3 (brute force)")
    check(all(S_formula(p, 2) == 2 ** p * (p + 1) - 2 * p for p in range(2, 101) if is_prime(p)),
          "Fig. 7 caption: |S| = 2^n(n+1) - 2n for prime n <= 100 (sigma=2)")
    lo, hi = pdens_interval(2, "corr")
    check(lo <= Fraction(3, 5) <= hi, "P^dens(2x2) = 3/5 (first point of Fig. 9)")
    res = {}
    for n in (45, 100):
        for var in ("corr", "printed"):
            res[(n, var)] = pdens_interval(n, var)
    l45, h45 = res[(45, "corr")]
    l100, h100 = res[(100, "corr")]
    print(f"      P^dens(45^2): corrected {dec(l45, 6)} ; printed Eq.(33) {dec(res[(45, 'printed')][0], 6)}")
    print(f"      P^dens(100^2): corrected {dec(l100, 6)} ; printed Eq.(33) {dec(res[(100, 'printed')][0], 6)}")
    check(dec(l45, 1) == dec(h45, 1) and Fraction(95, 100000) <= l45 and h45 < Fraction(105, 100000),
          f"P^dens(45^2) = {dec(l45, 4)} (Sec. IV A '0.001', Sec. I 'around 10^-3')")
    check(Fraction(195, 1000000) <= l100 and h100 < Fraction(205, 1000000),
          f"P^dens(100^2) = {dec(l100, 4)} (Sec. VI '2 x 10^-4')")
    if fig9_pdf:
        fig9(fig9_pdf)
    else:
        print("      [F4] Fig. 9 plot check skipped (no --fig9 PDF given)")


def fig9(path):
    """[F4] read the plotted polyline of Fig. 9 (page 9 of arXiv:1703.09030v2,
    vector graphics) and compare with the corrected P^dens (plot check)."""
    want = "214bb551a7475a0ac73140f300dec1b4aa16f9b7cd48afc9765771e3227604f0"
    h = hashlib.sha256(open(path, "rb").read()).hexdigest()
    check(h == want, f"[F4] PDF is arXiv:1703.09030v2 (sha256 {h[:16]}...)")
    if h != want:
        return
    import fitz  # PyMuPDF, only for this optional check
    page = fitz.open(path)[8]
    dr = page.get_drawings()

    def lines(d):
        return [it for it in d["items"] if it[0] == "l"]

    def poly(nseg):
        cand = [d for d in dr if len(d["items"]) == nseg and all(it[0] == "l" for it in d["items"]) and (d.get("width") or 0) > 0.3]
        assert len(cand) == 1
        its = lines(cand[0])
        pts = [(its[0][1].x, its[0][1].y)] + [(it[2].x, it[2].y) for it in its]
        return pts

    def ticks(nitems, axis):
        d = [d for d in dr if len(d["items"]) == nitems and (d.get("width") or 0) < 0.2]
        vals = set()
        for dd in d:
            for it in lines(dd):
                vals.add(round(it[1].x if axis == "x" else it[1].y, 3))
        return sorted(vals)

    out = {}
    for name, nseg, xt_items, yt_items, ns, decades in (("main", 98, 20, 10, range(10, 101, 10), [0, -1, -2, -3, -4]),
                                                        ("inset", 8, 18, 4, range(2, 11), [0, -1])):
        pts = poly(nseg)
        xt = ticks(xt_items, "x")
        yt = ticks(yt_items, "y")
        assert len(xt) == len(ns) and len(yt) == len(decades), (name, xt, yt)
        ns = list(ns)
        sx = (xt[-1] - xt[0]) / (ns[-1] - ns[0])
        sy = (yt[-1] - yt[0]) / (decades[0] - decades[-1])     # y grows downward
        n_first = ns[0] - (xt[0] - pts[0][0]) / sx
        maxdev = 0.0
        worst = None
        for i, (x, y) in enumerate(pts):
            n = round(n_first + (x - pts[0][0]) / sx)
            assert abs(n_first + (x - pts[0][0]) / sx - n) < 0.01
            plotted = decades[0] - (y - yt[0]) / sy
            lo, hi = pdens_interval(n, "corr")
            exact = math.log10(lo.numerator) - math.log10(lo.denominator) if lo.numerator < 10 ** 300 else \
                log10_ratio(lo.numerator, lo.denominator)
            dev = abs(plotted - exact)
            if dev > maxdev:
                maxdev, worst = dev, n
        out[name] = (len(pts), maxdev, worst, sy)
        print(f"      [F4] Fig. 9 {name}: {len(pts)} plotted points n={round(n_first)}..{round(n_first) + len(pts) - 1}; "
              f"max |log10 plotted - log10 corrected| = {maxdev:.4f} decades (at n={worst}; 1 pt = {1 / sy:.4f} decades)")
    check(out["main"][0] == 99 and out["inset"][0] == 9 and out["main"][1] < 0.0004 and out["inset"][1] < 0.0004,
          "[F4] Fig. 9 (n=2..100 and inset n=2..10) agrees with the corrected formula within 0.0004 decades (0.1%)")


def main():
    fig = None
    if "--fig9" in sys.argv:
        fig = sys.argv[sys.argv.index("--fig9") + 1]
    print("verify_erratum.py -- erratum to Chaos 29, 063120 (2019)")
    print(f"python {sys.version.split()[0]} on {platform.platform()}")
    me = hashlib.sha256(open(__file__, "rb").read()).hexdigest()
    print(f"script sha256 {me}")
    for sec in (section_A, section_B, section_C, section_D, section_E):
        t = time.time()
        sec()
        print(f"      ({time.time() - t:.1f} s)")
    t = time.time()
    section_F(fig)
    print(f"      ({time.time() - t:.1f} s)")
    print("\n" + "=" * 72)
    print(f"{NCHECKS} checks, {len(FAILS)} failed; runtime {time.time() - T0:.1f} s")
    if FAILS:
        for f in FAILS:
            print("  FAILED:", f)
        sys.exit(1)
    print("RESULT: ALL PASSED")


if __name__ == "__main__":
    main()
