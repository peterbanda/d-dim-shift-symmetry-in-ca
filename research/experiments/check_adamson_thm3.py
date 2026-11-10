#!/usr/bin/env python3
"""
check_adamson_thm3.py -- independent check of the counting theorems (Theorems 1, 2, 3) of

    D. Adamson, A. Deligkas, V. V. Gusev, I. Potapov,
    "Combinatorial algorithms for multidimensional necklaces",
    arXiv:2108.01990v2 (submitted 5 Nov 2021; PDF sha256 be25bb9b...d5212,
    TeX source e-print sha256 b8a75dda...6d7e3).

All page numbers below are the printed page numbers of the v2 PDF (they coincide
with the PDF page index).

What is computed, for every grid n = (n_1, ..., n_d) with all n_i >= 2 and
N = n_1 * ... * n_d <= 16 (every ORDERED tuple, because Theorem 3 is not
symmetric in the coordinates), and for alphabet sizes q = sigma = 2, 3:

 (a) BRUTE FORCE, at definition level.  Every configuration w : Z_{n_1} x ... x
     Z_{n_d} -> {0..q-1} is enumerated; for every non-zero translation g we test
     w(x+g) = w(x) for all cells x.  This gives the stabilizer Stab(w) of every
     word, hence
       * atranslational words   = #{w : Stab(w) = 0}       (p.6 definition)
       * atranslational necklaces = (atranslational words) / N (free orbits)
       * necklaces              = sum_w |Stab(w)| / N         (orbit-stabilizer)
       * Lyndon words (aperiodic necklaces), Definition 4 read cyclically
         (period box m with m_i | n_i, i.e. Stab(w) meets no coordinate axis)
     For q^N <= 2^21 the necklace count and the Lyndon count are additionally
     obtained by explicit orbit enumeration (canonical = minimal code over all
     translates), without orbit-stabilizer, and Definition 4 is also evaluated
     LITERALLY (any box m <= n, not necessarily m_i | n_i).

 (b) THE PAPER'S FORMULAS AS PRINTED.
       Theorem 1 (p.6 and p.12), and the last display of its proof (p.13);
       Theorem 2 (p.7 and p.13);
       Theorem 3 (p.7; p.14 twice; restated p.16), with G(l,n) (p.7, p.14-15),
       I(i,l,n) and H(i,l,n,d) (p.7 and p.15), and Lemma 3 (p.15, proof p.16).
     Theorem 3 is ambiguous / internally inconsistent in print; every reading
     choice is a switch of the class `Reading` below (documented there), and
     ALL 2*6*4*5*3 = 720 combinations are evaluated.

 (c) CLOSED FORM.  |A_neck| = (q^N - |S|) / N with |S| from Theorem 4.7 of the paper
     (paper v10; rank formula: d_p = #{i : p | n_i}).

 (d) DIAGNOSIS.  The exact replacement of Lemma 3,
         |L^n| - |A^n| = sum_{0 != H <= G, H meets no axis} |A(G/H)|,
     where A(G/H) are the atranslational necklaces on the quotient group G/H
     (counted by the closed form with the p-ranks of G/H), is verified against
     brute force stabilizer by stabilizer; each such H is labelled by its
     "Hermite box" a(H) = (a_1..a_d) (a_j = n_j / |proj_j(H cap (Z_{n_1..n_j} x 0))|),
     which is the size of the paper's "translational period".  The paper's
     (i,l) terms of Theorem 3 are printed next to the true contributions.

Result (see adamson_check_output.txt):
  * Theorem 1 (statement) and Theorem 2 agree with brute force on all 84 (grid, q)
    pairs (Theorem 2 needs Definition 4 read with m_i | n_i).  The last display of
    the proof of Theorem 1 (p.13) is wrong as printed (n = (3), q = 2: 6 vs 4).
  * Theorem 3 matches on all 84 pairs under NONE of the 720 readings (best 66/84).
    Defect classes (section 9 of the output):
      D1  l = 1 excluded by "1 < l < n_d"                     (2x2: 3 vs 2)
      D2  base counted on the untwisted box, not on G/H        (2x4: 28 vs 27)
      D3  period boxes outside (n_1..n_{i-1}, l, 1..1); H(i,l,n,d) double counts
                                                               (2x2x3: 335 vs 326; 2x2x2)
      D4  coefficient -mu(n_i/l) kills existing contributions  (4x4: 4056 vs 4050)
      D5  displayed H (= 1 at i = d) contradicts the p.15 text (2x3: 8 vs 9; 1-D n=4)

Usage:  python3 adamson_check.py [--quick] > adamson_check_output.txt
        (--quick skips q = 3 brute force for N >= 13; default runs everything,
         about 5-10 minutes on one core.)

Exact integer arithmetic throughout (Python ints / Fractions); numpy is used only
for the brute-force enumeration (uint8 / int64, no floating point).
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import sys
import time
from fractions import Fraction
from functools import lru_cache
from typing import NamedTuple

import numpy as np

# ---------------------------------------------------------------------------
# 1. elementary number theory
# ---------------------------------------------------------------------------


def divisors(n: int) -> list[int]:
    return [k for k in range(1, n + 1) if n % k == 0]


def factorize(n: int) -> dict[int, int]:
    f: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def mobius(n: int) -> int:
    f = factorize(n)
    if any(e > 1 for e in f.values()):
        return 0
    return -1 if len(f) % 2 else 1


def phi(n: int) -> int:
    r = n
    for p in factorize(n):
        r = r // p * (p - 1)
    return r


def lcm_list(xs) -> int:
    r = 1
    for x in xs:
        r = r * x // math.gcd(r, x)
    return r


def prod(xs) -> int:
    r = 1
    for x in xs:
        r *= x
    return r


def gauss_binom(e: int, v: int, p: int) -> int:
    """Gaussian binomial [e choose v]_p (exact)."""
    if v < 0 or v > e:
        return 0
    num, den = 1, 1
    for k in range(v):
        num *= p ** (e - k) - 1
        den *= p ** (k + 1) - 1
    assert num % den == 0
    return num // den


def r_coef(e: int, p: int, v: int) -> int:
    """r_e(p, v) = p^{binom(v,2)} [e choose v]_p (THEOREMS.md, Setting)."""
    return p ** (v * (v - 1) // 2) * gauss_binom(e, v, p)


# ---------------------------------------------------------------------------
# 2. closed form (c): Theorem 4.7 of the paper (v10)
# ---------------------------------------------------------------------------


def S_closed(N: int, ranks: dict[int, int], q: int) -> int:
    """|S_G| for a finite abelian group with |G| = N and p-ranks `ranks`."""
    primes = sorted(p for p, dp in ranks.items() if dp > 0)
    total = 0
    for v in itertools.product(*[range(ranks[p] + 1) for p in primes]):
        if sum(v) == 0:
            continue
        h = prod(p ** vp for p, vp in zip(primes, v))
        assert N % h == 0
        coef = prod(r_coef(ranks[p], p, vp) for p, vp in zip(primes, v))
        total += (-1) ** (1 + sum(v)) * coef * q ** (N // h)
    return total


def grid_ranks(n: tuple[int, ...]) -> dict[int, int]:
    N = prod(n)
    return {p: sum(1 for ni in n if ni % p == 0) for p in factorize(N)} if N > 1 else {}


def A_neck_closed_group(N: int, ranks: dict[int, int], q: int) -> int:
    """Atranslational necklaces (free orbits) on an abelian group: (q^N - |S|)/N."""
    if N == 1:
        return q
    x = q ** N - S_closed(N, ranks, q)
    assert x % N == 0, (N, ranks, q)
    return x // N


def A_neck_closed(n: tuple[int, ...], q: int) -> int:
    return A_neck_closed_group(prod(n), grid_ranks(n), q)


# ---------------------------------------------------------------------------
# 3. the group Z_{n_1} x ... x Z_{n_d}
# ---------------------------------------------------------------------------


class Grid:
    """Cells/translations as tuples; linear index with coordinate 1 fastest."""

    def __init__(self, n: tuple[int, ...]):
        self.n = n
        self.d = len(n)
        self.N = prod(n)
        self.elems = list(itertools.product(*[range(k) for k in reversed(n)]))
        self.elems = [tuple(reversed(e)) for e in self.elems]  # coordinate 1 fastest
        self.index = {e: k for k, e in enumerate(self.elems)}
        assert all(self.index[e] == self.lin(e) for e in self.elems)

    def lin(self, x) -> int:
        k, stride = 0, 1
        for xi, ni in zip(x, self.n):
            k += (xi % ni) * stride
            stride *= ni
        return k

    def add(self, x, y):
        return tuple((a + b) % m for a, b, m in zip(x, y, self.n))

    def mul(self, k, x):
        return tuple((k * a) % m for a, m in zip(x, self.n))

    def order(self, x) -> int:
        return lcm_list([m // math.gcd(a, m) for a, m in zip(x, self.n)]) if x else 1

    def is_axis(self, x) -> bool:
        return sum(1 for a in x if a) == 1

    def perm(self, g) -> np.ndarray:
        """perm[x] = index(x+g): (tau_g w)(x) = w(x+g) = w[perm[x]]."""
        return np.array([self.index[self.add(x, g)] for x in self.elems], dtype=np.int64)

    # -- subgroups ---------------------------------------------------------
    def subgroups(self) -> list[frozenset]:
        zero = tuple(0 for _ in self.n)
        start = frozenset([zero])
        seen = {start}
        stack = [start]
        while stack:
            S = stack.pop()
            for g in self.elems:
                if g in S:
                    continue
                T = set()
                for k in range(self.order(g)):
                    kg = self.mul(k, g)
                    for s in S:
                        T.add(self.add(s, kg))
                T = frozenset(T)
                if T not in seen:
                    seen.add(T)
                    stack.append(T)
        return sorted(seen, key=lambda H: (len(H), sorted(H)))

    def hermite_box(self, H) -> tuple[int, ...]:
        """a_j = n_j / |{h_j : h in H, h_{j+1} = ... = h_d = 0}|; prod a_j = N/|H|."""
        a = []
        for j in range(self.d):
            Pj = {h[j] for h in H if all(h[t] == 0 for t in range(j + 1, self.d))}
            a.append(self.n[j] // len(Pj))
        assert prod(a) * len(H) == self.N
        return tuple(a)

    def quotient_ranks(self, H) -> dict[int, int]:
        """p-ranks of G/H: |(G/H)/p(G/H)| = |G / (H + pG)| = p^{d_p}."""
        ranks = {}
        Q = self.N // len(H)
        for p in factorize(Q) if Q > 1 else {}:
            pG = {self.mul(p, x) for x in self.elems}
            HpG = {self.add(h, y) for h in H for y in pG}
            idx = self.N // len(HpG)
            e = 0
            while idx % p == 0:
                idx //= p
                e += 1
            assert idx == 1
            ranks[p] = e
        return ranks


# ---------------------------------------------------------------------------
# 4. brute force (a)
# ---------------------------------------------------------------------------


class Brute(NamedTuple):
    words_free: int          # atranslational words
    neck: int                # necklaces (orbit-stabilizer)
    lyndon: int              # aperiodic necklaces, Definition 4 read cyclically
    a_neck: int              # atranslational necklaces
    stab_words: dict         # frozenset(Stab) -> number of words with exactly this stabilizer
    neck_explicit: int | None        # necklaces by explicit canonical forms
    lyndon_explicit: int | None      # Lyndon necklaces by explicit canonical forms (cyclic Def 4)
    lyndon_literal_def4: int | None  # Lyndon necklaces with Definition 4 read literally


def brute_force(n: tuple[int, ...], q: int, explicit_limit: int = 1 << 21,
                chunk: int = 1 << 20) -> Brute:
    G = Grid(n)
    N = G.N
    nonzero = [g for g in G.elems if any(g)]
    perms = [G.perm(g) for g in nonzero]
    axis_mask = 0
    for b, g in enumerate(nonzero):
        if G.is_axis(g):
            axis_mask |= 1 << b
    total = q ** N
    pw = np.array([q ** j for j in range(N)], dtype=np.int64)
    hist = np.zeros(1 << len(nonzero), dtype=np.int64)
    explicit = total <= explicit_limit
    if explicit:
        canon_all = np.empty(total, dtype=np.int64)
        periodic_lit = np.zeros(total, dtype=bool)
        # literal Definition 4: any box m <= n (m != n), w_j = w_{j mod m} for all j
        lit_maps = []
        for m in itertools.product(*[range(1, k + 1) for k in n]):
            if tuple(m) == tuple(n):
                continue
            lit_maps.append(np.array([G.index[tuple(x % mi for x, mi in zip(e, m))]
                                      for e in G.elems], dtype=np.int64))
    for start in range(0, total, chunk):
        k = np.arange(start, min(total, start + chunk), dtype=np.int64)
        C = np.empty((len(k), N), dtype=np.uint8)
        for j in range(N):
            C[:, j] = (k // pw[j]) % q
        mask = np.zeros(len(k), dtype=np.int64)
        for b, pm in enumerate(perms):
            fixed = (C[:, pm] == C).all(axis=1)
            mask |= fixed.astype(np.int64) << b
        hist += np.bincount(mask, minlength=hist.size)
        if explicit:
            canon = k.copy()
            for pm in perms:
                code = C[:, pm].astype(np.int64) @ pw
                np.minimum(canon, code, out=canon)
            canon_all[start:start + len(k)] = canon
            for mp in lit_maps:
                periodic_lit[start:start + len(k)] |= (C[:, mp] == C).all(axis=1)
    # aggregate by stabilizer
    zero = tuple(0 for _ in n)
    stab_words = {}
    neck_num = lyn_num = 0
    for m in np.nonzero(hist)[0]:
        m = int(m)
        S = frozenset([zero] + [nonzero[b] for b in range(len(nonzero)) if m >> b & 1])
        # sanity: a stabilizer is a subgroup
        assert all(G.add(x, y) in S for x in S for y in S)
        cnt = int(hist[m])
        stab_words[S] = cnt
        neck_num += cnt * len(S)
        if m & axis_mask == 0:
            lyn_num += cnt * len(S)
    assert neck_num % N == 0 and lyn_num % N == 0
    words_free = int(hist[0])
    assert words_free % N == 0
    # sanity: |Fix(<g>)| = q^{N/ord(g)} for every g
    for b, g in enumerate(nonzero):
        fixcount = sum(c for S, c in stab_words.items() if g in S)
        assert fixcount == q ** (N // G.order(g)), (n, q, g)
    ne = le = ll = None
    if explicit:
        ks = np.arange(total, dtype=np.int64)
        is_canon = canon_all == ks
        ne = int(is_canon.sum())
        # cyclic Def 4: stabilizer meets no axis; recompute per word from canonical
        # orbits: a necklace is Lyndon iff its canonical word has no axis period
        # (periodicity is translation invariant in the cyclic reading)
        axis_perms = [pm for b, pm in enumerate(perms) if axis_mask >> b & 1]
        Cc = np.empty((int(is_canon.sum()), N), dtype=np.uint8)
        kc = ks[is_canon]
        for j in range(N):
            Cc[:, j] = (kc // pw[j]) % q
        axis_per = np.zeros(len(kc), dtype=bool)
        for pm in axis_perms:
            axis_per |= (Cc[:, pm] == Cc).all(axis=1)
        le = int((~axis_per).sum())
        # literal Def 4: necklace aperiodic iff EVERY word of it is aperiodic (p.6)
        bad = np.zeros(total, dtype=bool)
        bad[canon_all[periodic_lit]] = True
        ll = int((is_canon & ~bad).sum())
    return Brute(words_free, neck_num // N, lyn_num // N, words_free // N, stab_words,
                 ne, le, ll)


# ---------------------------------------------------------------------------
# 5. Theorems 1 and 2 as printed (b)
# ---------------------------------------------------------------------------


def thm1_statement(n: tuple[int, ...], q: int) -> Fraction:
    """Theorem 1 (p.6, p.12): (1/N) sum_{f_i | n_i} prod phi(f_i) q^{N/lcm(f)}."""
    N = prod(n)
    s = 0
    for f in itertools.product(*[divisors(k) for k in n]):
        s += prod(phi(fi) for fi in f) * q ** (N // lcm_list(f))
    return Fraction(s, N)


def thm1_proof_display(n: tuple[int, ...], q: int) -> Fraction:
    """Last display of the proof of Theorem 1 (p.13, TeX eq. multidimensional_necklaces):
    (1/N) sum_{f_i | n_i} prod phi(n_i/f_i) q^{N/lcm(f)}  -- as printed."""
    N = prod(n)
    s = 0
    for f in itertools.product(*[divisors(k) for k in n]):
        s += prod(phi(ni // fi) for ni, fi in zip(n, f)) * q ** (N // lcm_list(f))
    return Fraction(s, N)


@lru_cache(maxsize=None)
def necklaces_T1(n: tuple[int, ...], q: int) -> int:
    v = thm1_statement(n, q)
    assert v.denominator == 1
    return int(v)


@lru_cache(maxsize=None)
def lyndon_T2(n: tuple[int, ...], q: int) -> int:
    """Theorem 2 (p.7, p.13): sum_{f|n} prod mu(n_i/f_i) |N_q^f| (|N| by Theorem 1)."""
    s = 0
    for f in itertools.product(*[divisors(k) for k in n]):
        c = prod(mobius(ni // fi) for ni, fi in zip(n, f))
        if c:
            s += c * necklaces_T1(tuple(f), q)
    return s


# ---------------------------------------------------------------------------
# 6. Theorem 3 as printed, with every reading choice (b)
# ---------------------------------------------------------------------------


class Reading(NamedTuple):
    """One way of reading the printed Theorem 3.

    sup  -- superscript of |A_q^{...}| in the summand:
        'd-1': (n_1,...,n_{d-1}, l)  [Theorem 3 on p.7, both statements on p.14,
                                       statement of Lemma 3 on p.15]
        'i-1': (n_1,...,n_{i-1}, l)  [end of proof of Lemma 3, restated Theorem 3
                                       and its proof on p.16; ranking formulas p.9, p.23;
                                       the proof of Lemma 3 speaks of a "translational
                                       period of size (n_1,...,n_{i-1}, l, 1, ..., 1)"]
    lower, upper -- which l | n_i, l != n_i give a non-zero summand.  Print (all
        statements p.7/14/15/16): "0 if l = n_i; ... if 1 < l < n_d", leaving
        l = 1 and n_d <= l < n_i undefined.  We read undefined cases as 0.
        lower 'l>1'  : as printed;  'l>=1': include l = 1 (the proof of Lemma 3,
                       p.16, says "as P(1) = 1, both the prime and non-prime cases can
                       be combined", and the ranking versions p.9 and p.23 use "l < n_i").
        upper 'l<n_d': as printed;  'l<n_i': the p.9/p.23 variant (n_d -> n_i).
    l1base -- for l = 1 (only when lower = 'l>=1'): 'A' as printed, or 'L' = use the
        Lyndon count |L^{(n_1..)}| (p.23: "a must be either in A(...) if l > 1 or
        L(w_1) if l = 1").
    H -- H(i,l,n,d) (p.7, p.15):
        'formula-prod': the display literally: prod_{j=i}^{d} of a j-independent
                        bracket, i.e. bracket^(d-i+1), with 1 at i = d;
        'formula'     : the display with the (vacuous) prod_{j=i}^d dropped;
        'text'        : p.15 prose: "If i = d then H is either 1, if l = n_d, or
                        |G(l,n)| otherwise", recursion as displayed, no prod;
        'text-prod'   : 'text' base case with the literal prod (power d-i+1).
    G -- membership of x in G(l,n) (p.7; p.14-15; Lemma 2 p.15), with k = n_d/l and
        x^j read as j*x (the paper's g^t = t-fold translation, p.12):
        'forall-exists': for all i: k x_i = 0 mod n_i, and exists i with
                         j x_i != 0 mod n_i for all 1 <= j <= k-1 (as printed);
        'exists'       : both conditions for the same existential i only;
        'order'        : the prose of p.7: "repeating g n_d/l times returns the identity
                         ... repeating g less than n_d/l [times] returns some distinct
                         group operation", i.e. ord(x) = n_d/l;
        'nonzero'      : 'forall-exists' plus x_i in 1..n_i-1 (proof of Lemma 3, p.16);
        'power'        : x_i^j read as an integer power mod n_i.
    ev -- how the smaller |A| on the right-hand side are evaluated:
        'oracle': exact values (closed form, verified by brute force) -- isolates the
                  top-level identity;
        'rec-L' : Theorem 3 recursively, 1-D base |A| = |L| (p.14: "1D atranslational
                  necklaces are equivalent to Lyndon words"), size-1 dims dropped;
        'rec-T3': Theorem 3 recursively down to d = 1 as well (d = 0: q).
    I(i,l,n) is unambiguous (recursive display, p.7/p.15) and is used as printed.
    """
    sup: str
    lower: str
    upper: str
    l1base: str
    H: str
    G: str
    ev: str

    def short(self) -> str:
        return "/".join(self)


def all_readings() -> list[Reading]:
    out = []
    for sup in ("d-1", "i-1"):
        for lower in ("l>1", "l>=1"):
            for upper in ("l<n_d", "l<n_i"):
                for l1base in (("A",) if lower == "l>1" else ("A", "L")):
                    for H in ("formula-prod", "formula", "text", "text-prod"):
                        for G in ("forall-exists", "exists", "order", "nonzero", "power"):
                            for ev in ("oracle", "rec-L", "rec-T3"):
                                out.append(Reading(sup, lower, upper, l1base, H, G, ev))
    return out


LITERAL = Reading("d-1", "l>1", "l<n_d", "A", "formula-prod", "forall-exists", "oracle")


def G_member(x, coords, k, mode) -> bool:
    if mode == "order":
        return lcm_list([m // math.gcd(a, m) for a, m in zip(x, coords)]) == k if coords else k == 1
    if mode == "power":
        mult = lambda j, a, m: pow(a, j, m)
    else:
        mult = lambda j, a, m: (j * a) % m
    cond_all = all(mult(k, a, m) == 0 for a, m in zip(x, coords))
    ex = [all(mult(j, a, m) != 0 for j in range(1, k)) for a, m in zip(x, coords)]
    if mode in ("forall-exists", "power"):
        return cond_all and any(ex)
    if mode == "nonzero":
        return cond_all and any(ex) and all(a != 0 for a in x)
    if mode == "exists":
        return any(mult(k, a, m) == 0 and e for a, m, e in zip(x, coords, ex))
    raise ValueError(mode)


@lru_cache(maxsize=None)
def G_size(l: int, n: tuple[int, ...], mode: str) -> int:
    d = len(n)
    assert n[d - 1] % l == 0
    k = n[d - 1] // l
    coords = n[:d - 1]
    return sum(1 for x in itertools.product(*[range(m) for m in coords])
               if G_member(x, coords, k, mode))


def I_fun(i: int, l: int, n: tuple[int, ...]) -> int:
    d = len(n)
    if i == d or l > 1:
        return 0
    if n[i - 1] == n[d - 1]:
        return 1 + I_fun(i, l, n[:-1])
    return I_fun(i, l, n[:-1])


def H_fun(i: int, l: int, n: tuple[int, ...], R: Reading) -> int:
    d = len(n)
    if i == d:
        if R.H in ("formula", "formula-prod"):
            return 1
        return 1 if l == n[d - 1] else G_size(l, n, R.G)
    inner = (G_size(1, n, R.G) - I_fun(i, l, n)) * H_fun(i, l, n[:-1], R)
    if R.H.endswith("-prod"):
        return inner ** (d - i + 1)
    return inner


class IllFounded(Exception):
    pass


def strip1(n):
    return tuple(k for k in n if k != 1)


def thm3_terms(n: tuple[int, ...], q: int, R: Reading, _stack=None):
    """Returns (value, L, terms) with terms = list of dicts per (i,l) with a summand."""
    if _stack is None:
        _stack = set()
    if R.ev != "oracle":
        n = strip1(n)
    d = len(n)
    if d == 0:
        return q, q, []
    L = lyndon_T2(n, q)
    if R.ev == "rec-L" and d == 1:
        return L, L, []
    key = (n, q, R)
    if key in _stack:
        raise IllFounded(n)
    _stack = _stack | {key}
    terms = []
    total = 0
    for i in range(1, d + 1):
        ni = n[i - 1]
        for l in divisors(ni):
            if l == ni:
                continue
            if R.lower == "l>1" and l <= 1:
                continue
            ub = n[d - 1] if R.upper == "l<n_d" else ni
            if not l < ub:
                continue
            coef = prod(-mobius(n[t - 1]) for t in range(i + 1, d)) * (-mobius(ni // l))
            size = (n[:d - 1] + (l,)) if R.sup == "d-1" else (n[:i - 1] + (l,))
            if coef == 0:
                terms.append(dict(i=i, l=l, coef=0, size=size, base=None, H=None, term=0))
                continue
            if l == 1 and R.l1base == "L":
                base = lyndon_T2(strip1(size), q) if strip1(size) else q
            elif R.ev == "oracle":
                base = A_neck_closed(size, q)
            else:
                base = thm3_terms(size, q, R, _stack)[0]
            Hv = H_fun(i, l, n, R)
            t = coef * base * Hv
            terms.append(dict(i=i, l=l, coef=coef, size=size, base=base, H=Hv, term=t))
            total += t
    return L - total, L, terms


@lru_cache(maxsize=None)
def thm3_value(n, q, R):
    """Value of Theorem 3 under reading R; None if the recursion is ill-founded."""
    try:
        return thm3_terms(n, q, R)[0]
    except IllFounded:
        return None
    except RecursionError:
        return None


# ---------------------------------------------------------------------------
# 7. exact decomposition of translational Lyndon necklaces (d)
# ---------------------------------------------------------------------------


@lru_cache(maxsize=None)
def subgroup_data(n: tuple[int, ...]):
    """All subgroups H != 0 meeting no coordinate axis, with Hermite box and G/H ranks."""
    G = Grid(n)
    out = []
    for H in G.subgroups():
        if len(H) == 1:
            continue
        if any(G.is_axis(h) for h in H):
            continue
        out.append(dict(H=H, order=len(H), box=G.hermite_box(H),
                        qranks=G.quotient_ranks(H)))
    return out


def translational_lyndon_by_H(n, q):
    """[(H-data, |A(G/H)|)] -- number of translational Lyndon necklaces with Stab = H."""
    N = prod(n)
    return [(h, A_neck_closed_group(N // h["order"], h["qranks"], q)) for h in subgroup_data(n)]


def group_name(order: int, ranks: dict[int, int], n: tuple[int, ...], H) -> str:
    """Isomorphism type of G/H by elementary divisors (computed from element orders)."""
    G = Grid(n)
    # orders of cosets: ord(x+H) = min k>0 with kx in H
    cnt = {}
    for x in G.elems:
        k = 1
        while G.mul(k, x) not in H:
            k += 1
        cnt[k] = cnt.get(k, 0) + 1
    # the multiset of element orders determines a finite abelian group
    # (each coset counted |H| times)
    cnt = {k: v // len(H) for k, v in cnt.items()}
    # brute-force match against products of cyclic groups of order `order`
    def partitions_types(m):
        f = factorize(m)
        per_p = []
        for p, e in f.items():
            parts = []
            def rec(rem, mx, cur):
                if rem == 0:
                    parts.append(list(cur))
                    return
                for a in range(min(rem, mx), 0, -1):
                    rec(rem - a, a, cur + [a])
            rec(e, e, [])
            per_p.append([[p ** a for a in pt] for pt in parts])
        for combo in itertools.product(*per_p):
            yield [c for part in combo for c in part]
    for cyc in partitions_types(order) if order > 1 else [[]]:
        # element order distribution of prod Z_c
        dist = {}
        for x in itertools.product(*[range(c) for c in cyc]):
            o = lcm_list([c // math.gcd(a, c) for a, c in zip(x, cyc)]) if cyc else 1
            dist[o] = dist.get(o, 0) + 1
        if dist == cnt:
            # combine coprime cyclic factors into invariant-factor-free notation
            return "x".join(f"Z{c}" for c in sorted(cyc)) if cyc else "1"
    return "?"


# ---------------------------------------------------------------------------
# 8. main
# ---------------------------------------------------------------------------


def grids_upto(Nmax: int):
    out = []
    def rec(cur, p):
        if cur:
            out.append(tuple(cur))
        for k in range(2, Nmax // p + 1):
            rec(cur + [k], p * k)
    rec([], 1)
    return sorted(out, key=lambda n: (prod(n), len(n), n))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--json", default=None)
    args = ap.parse_args()
    t0 = time.time()
    P = lambda *a: print(*a, flush=True)

    # --- reference values of the project (CLAUDE.md) ------------------------
    P("== 0. Closed form sanity anchors (Theorem 4.7, sigma = 2) ==")
    refs = {(2, 2): 8, (3, 3): 26, (5, 5): 182, (2, 2, 2): 72, (3, 3, 3): 6398, (6, 6): 801064}
    for n, v in refs.items():
        s = S_closed(prod(n), grid_ranks(n), 2)
        P(f"  |S_{n}| = {s}  (reference {v})  {'OK' if s == v else 'FAIL'}")
        assert s == v
    # Z2xZ8 vs Z4xZ4 (THEOREMS.md (c)): 736 each
    assert S_closed(16, {2: 2}, 2) == 736

    grids = grids_upto(16)
    P(f"\nGrids: all ordered tuples with n_i >= 2 and N <= 16: {len(grids)} grids; q in (2, 3)")

    # --- brute force ----------------------------------------------------------
    P("\n== 1. Brute force (definition level) vs closed form, Theorem 1, Theorem 2 ==")
    hdr = ("grid", "N", "q", "A_words", "A_neck", "closed", "neck", "Thm1", "Thm1p13",
           "Lyn", "Thm2", "LynLit", "expl")
    P("  " + " ".join(f"{h:>10}" for h in hdr))
    results = {}
    for n in grids:
        for q in (2, 3):
            N = prod(n)
            if args.quick and q == 3 and N >= 13:
                continue
            b = brute_force(n, q)
            cf = A_neck_closed(n, q)
            t1 = thm1_statement(n, q)
            t1p = thm1_proof_display(n, q)
            t2 = lyndon_T2(n, q)
            ok_closed = cf == b.a_neck
            ok_t1 = t1 == b.neck
            ok_t2 = t2 == b.lyndon
            expl = ""
            if b.neck_explicit is not None:
                assert b.neck_explicit == b.neck and b.lyndon_explicit == b.lyndon
                expl = "ok"
            assert ok_closed and ok_t1 and ok_t2, (n, q)
            results[(n, q)] = b
            t1p_s = str(t1p) if t1p != t1 else "=Thm1"
            P("  " + " ".join(f"{x:>10}" for x in (
                "x".join(map(str, n)), N, q, b.words_free, b.a_neck, cf, b.neck,
                str(t1), t1p_s, b.lyndon, t2,
                "-" if b.lyndon_literal_def4 is None else b.lyndon_literal_def4, expl)))
    P(f"  [all {len(results)} (grid,q) pairs: brute A_neck == closed form, "
      f"Theorem 1 == brute necklaces, Theorem 2 == brute Lyndon (cyclic Def. 4)]")
    P(f"  [elapsed {time.time() - t0:.1f}s]")

    # --- Theorem 3: all readings ---------------------------------------------
    P("\n== 2. Theorem 3 under every reading (720 readings) ==")
    readings = all_readings()
    keys = sorted(results, key=lambda k: (prod(k[0]), len(k[0]), k[0], k[1]))
    score = {}
    for R in readings:
        m = 0
        mw = 0
        first = None
        illf = 0
        for k in keys:
            n, q = k
            v = thm3_value(n, q, R)
            if v is None:
                illf += 1
            if v == results[k].a_neck:
                m += 1
            elif first is None:
                first = (k, v, results[k].a_neck)
            if v == results[k].words_free:
                mw += 1
        score[R] = (m, mw, first, illf)
    tot = len(keys)
    best = max(score.values(), key=lambda s: s[0])[0]
    P(f"  pairs tested: {tot};  readings that match ALL pairs: "
      f"{sum(1 for s in score.values() if s[0] == tot)}")
    P(f"  best number of matches (necklace reading): {best}/{tot}")
    P(f"  best number of matches against atranslational WORDS (p.7 wording): "
      f"{max(s[1] for s in score.values())}/{tot}")
    P(f"  readings giving an ill-founded recursion on some grid: "
      f"{sum(1 for s in score.values() if s[3])}")
    P("  top readings (sup/lower/upper/l1base/H/G/ev : matches, first failure (grid,q) value vs true):")
    ranked = sorted(readings, key=lambda R: -score[R][0])
    for R in ranked[:25]:
        m, mw, first, illf = score[R]
        P(f"    {R.short():58s} {m:3d}/{tot}  first fail {first[0]}: {first[1]} vs {first[2]}")
    P("  literal reading " + LITERAL.short() + f": {score[LITERAL][0]}/{tot}, first fail "
      f"{score[LITERAL][2]}")
    # failure set common to all readings
    always_fail = []
    for k in keys:
        if all(thm3_value(k[0], k[1], R) != results[k].a_neck for R in readings):
            always_fail.append(k)
    P(f"  (grid,q) pairs on which EVERY one of the 720 readings fails: {len(always_fail)}")
    P("    " + ", ".join(f"{'x'.join(map(str, k[0]))}/q{k[1]}" for k in always_fail))
    oracle_R = [R for R in readings if R.ev == "oracle"]
    always_fail_or = [k for k in keys
                      if all(thm3_value(k[0], k[1], R) != results[k].a_neck for R in oracle_R)]
    P(f"  restricted to the {len(oracle_R)} 'oracle' readings (exact values for the smaller |A|,")
    P(f"  so that only the top-level identity is tested), pairs failing under EVERY reading: "
      f"{len(always_fail_or)}")
    P("    " + ", ".join(f"{'x'.join(map(str, k[0]))}/q{k[1]}" for k in always_fail_or))
    P("  (with recursive evaluation some of these are 'repaired' by compensating errors in the")
    P("   recursively computed smaller |A|, e.g. 2x4/q2 with 2x2 evaluated to 3 instead of 2.)")
    # by dimension
    for dd in (1, 2, 3, 4):
        ks = [k for k in keys if len(k[0]) == dd]
        bestd = max(sum(1 for k in ks if thm3_value(k[0], k[1], R) == results[k].a_neck)
                    for R in readings)
        P(f"  d = {dd}: {len(ks)} pairs, best reading matches {bestd}")
    # the readings of G(l,n) coincide for N <= 16; show that they differ in general
    P("  note: G readings 'forall-exists' and 'order' agree on all grids used here; they differ")
    P(f"  e.g. |G(1,(2,3,6))| = {G_size(1, (2, 3, 6), 'forall-exists')} ('forall-exists') vs "
      f"{G_size(1, (2, 3, 6), 'order')} ('order').")

    best_R = ranked[0]
    P(f"\n  Best-scoring reading used below: {best_R.short()}")

    # --- full comparison table ------------------------------------------------
    P("\n== 3. Full comparison table: true atranslational necklaces vs Theorem 3 ==")
    P("  columns: true = brute force = closed form; T3lit = literal reading; T3best = best reading;")
    P("           #ok = number of the 720 readings that give the true value")
    P(f"  {'grid':>8} {'N':>3} {'q':>2} {'L(Thm2)':>8} {'true A':>8} {'A words':>9} "
      f"{'T3lit':>8} {'T3best':>8} {'#ok':>4}")
    table_rows = []
    for k in keys:
        n, q = k
        b = results[k]
        lit = thm3_value(n, q, LITERAL)
        bv = thm3_value(n, q, best_R)
        nok = sum(1 for R in readings if thm3_value(n, q, R) == b.a_neck)
        P(f"  {'x'.join(map(str, n)):>8} {prod(n):>3} {q:>2} {b.lyndon:>8} {b.a_neck:>8} "
          f"{b.words_free:>9} {str(lit):>8} {str(bv):>8} {nok:>4}")
        table_rows.append(dict(grid=n, q=q, L=b.lyndon, A_neck=b.a_neck, A_words=b.words_free,
                               T3_literal=lit, T3_best=bv, n_readings_ok=nok))

    # --- diagnosis -----------------------------------------------------------
    P("\n== 4. Exact replacement of Lemma 3, checked stabilizer by stabilizer ==")
    P("  |L| - |A| = sum over H != 0 meeting no axis of |A(G/H)|  (necklaces with Stab = H)")
    for k in keys:
        n, q = k
        b = results[k]
        rows = translational_lyndon_by_H(n, q)
        s = sum(a for _, a in rows)
        assert s == b.lyndon - b.a_neck, (k, s, b.lyndon - b.a_neck)
        N = prod(n)
        for h, a in rows:
            words = b.stab_words.get(h["H"], 0)
            assert words * h["order"] == a * N, (k, h["H"])
    P(f"  verified on all {len(keys)} (grid,q) pairs, and for every single stabilizer H")
    P("  (words with Stab(w) = H, brute force) = (N/|H|) * |A(G/H)| (closed form on G/H).")

    P("\n== 5. Where Theorem 3 goes wrong: printed (i,l) terms vs true contributions ==")
    P("  The paper's (i,l) summand is meant to count translational Lyndon necklaces whose")
    P("  translational period has size (n_1..n_{i-1}, l, 1..1) (proof of Lemma 3, p.16).")
    P("  True contributions are listed by stabilizer H, with its period box a(H), the")
    P("  quotient G/H, and |A(G/H)| versus the paper's base count |A^{box}| on the")
    P("  untwisted torus Z_{a_1} x ... x Z_{a_d}.")
    focus = [((2, 2), 2), ((2, 4), 2), ((4, 2), 2), ((2, 2, 2), 2), ((3, 3), 2), ((2, 8), 2),
             ((4, 4), 2), ((2, 2, 4), 2), ((2, 2, 2, 2), 2)]
    show_R = [LITERAL,
              Reading("i-1", "l>=1", "l<n_i", "A", "text", "forall-exists", "oracle"),
              best_R]
    seen = set()
    show_R = [R for R in show_R if not (R in seen or seen.add(R))]
    for n, q in focus:
        b = results[(n, q)]
        P(f"\n  grid {n}, q = {q}: L = {b.lyndon}, true A = {b.a_neck}, "
          f"true |L \\ A| = {b.lyndon - b.a_neck}")
        for h, a in translational_lyndon_by_H(n, q):
            box = h["box"]
            gn = group_name(prod(n) // h["order"], h["qranks"], n, h["H"])
            untw = A_neck_closed(strip1(box), q) if strip1(box) else q
            form = None
            for i in range(1, len(n) + 1):
                if box[:i - 1] == n[:i - 1] and box[i - 1] < n[i - 1] and all(x == 1 for x in box[i:]):
                    form = (i, box[i - 1])
            gens = sorted(h["H"])[1:]
            P(f"    H = <{' '.join(''.join(map(str, g)) for g in gens)}> |H|={h['order']} "
              f"box a(H)={box} G/H={gn}: |A(G/H)|={a} necklaces; "
              f"untwisted |A^box|={untw}; paper form (i,l)={form}")
        for R in show_R:
            try:
                v, L, terms = thm3_terms(n, q, R)
            except (IllFounded, RecursionError):
                P(f"    reading {R.short()}: ill-founded recursion")
                continue
            ts = "; ".join(f"(i={t['i']},l={t['l']}): coef {t['coef']} * |A^{t['size']}|={t['base']}"
                           f" * H={t['H']} = {t['term']}" for t in terms if t['term'] or t['coef'])
            P(f"    reading {R.short()}: value {v}  [{ts if ts else 'no non-zero summand'}]")

    # attribution table for every failing pair under two readings
    for tag, RR in (("most favourable reading", best_R), ("proof-faithful reading", PROOF_READING)):
        P(f"\n== 5b. Attribution, {tag} " + RR.short() + " ==")
        P("  per (i,l): paper summand vs TRUE number of translational Lyndon necklaces whose")
        P("  stabilizer has period box (n_1..n_{i-1}, l, 1..1); 'other' = boxes not of that form.")
        attribution(keys, results, RR, P)

    # explicit missed necklace on 2x4
    P("\n== 6. Explicit witness on the 2 x 4 grid (q = 2) ==")
    _witnesses(P)

    P("\n== 9. Defect classes with minimal witnesses (q = 2) ==")
    rows = [
        ("D1 l = 1 excluded by '1 < l'", (2, 2), LITERAL),
        ("D1 (fixed by l>=1)", (2, 2), Reading("d-1", "l>=1", "l<n_d", "A", "text", "forall-exists", "oracle")),
        ("D5 H display (=1 at i=d) vs p.15 text", (2, 3), Reading("d-1", "l>=1", "l<n_d", "A", "formula", "forall-exists", "oracle")),
        ("D5 (text H)", (2, 3), Reading("d-1", "l>=1", "l<n_d", "A", "text", "forall-exists", "oracle")),
        ("D5 also in 1-D: H display, d = 1", (4,), LITERAL),
        ("D2 untwisted base (Z4 vs Z2^2)", (2, 4), best_R),
        ("D2 untwisted base (Z8 vs Z2xZ4)", (2, 8), best_R),
        ("D4 Moebius factor -mu(4) = 0", (4, 4), best_R),
        ("D3 box (2,1,3) outside the ansatz", (2, 2, 3), best_R),
        ("D3 box (2,1,3), proof-faithful", (2, 2, 3), PROOF_READING),
        ("D3'+D3 overcount in H, box (2,1,2)", (2, 2, 2), PROOF_READING),
    ]
    for label, n, R in rows:
        b = results[(n, 2)]
        P(f"  {label:40s} grid {'x'.join(map(str, n)):>6}: Thm 3 = {thm3_value(n, 2, R)}, "
          f"true = {b.a_neck}   [{R.short()}]")

    P(f"\n[total elapsed {time.time() - t0:.1f}s]")

    if args.json:
        out = dict(
            source="arXiv:2108.01990v2",
            table=[dict(r, grid=list(r["grid"])) for r in table_rows],
            readings=[dict(reading=R.short(), matches=score[R][0], matches_words=score[R][1],
                           first_fail=None if score[R][2] is None else
                           [list(score[R][2][0][0]), score[R][2][0][1], score[R][2][1], score[R][2][2]])
                      for R in readings],
        )
        with open(args.json, "w") as fh:
            json.dump(out, fh, indent=1)


PROOF_READING = Reading("i-1", "l>=1", "l<n_i", "A", "text", "forall-exists", "oracle")


def attribution(keys, results, RR, P):
    for k in keys:
        n, q = k
        b = results[k]
        v = thm3_value(n, q, RR)
        if v == b.a_neck:
            continue
        try:
            _, _, terms = thm3_terms(n, q, RR)
        except (IllFounded, RecursionError):
            P(f"  {'x'.join(map(str, n)):>8} q{q}: ill-founded")
            continue
        paper = {(t["i"], t["l"]): t["term"] for t in terms}
        true_il, other = {}, 0
        for h, a in translational_lyndon_by_H(n, q):
            box = h["box"]
            form = None
            for i in range(1, len(n) + 1):
                if box[:i - 1] == n[:i - 1] and box[i - 1] < n[i - 1] and all(x == 1 for x in box[i:]):
                    form = (i, box[i - 1])
            if form is None:
                other += a
            else:
                true_il[form] = true_il.get(form, 0) + a
        cells = []
        for il in sorted(set(paper) | set(true_il)):
            pv, tv = paper.get(il, 0), true_il.get(il, 0)
            if pv or tv:
                cells.append(f"({il[0]},{il[1]}): {pv} vs {tv}{'' if pv == tv else ' *'}")
        if other:
            cells.append(f"other boxes: 0 vs {other} *")
        P(f"  {'x'.join(map(str, n)):>8} q{q}: value {v} vs true {b.a_neck}; " + "; ".join(cells))



def _witnesses(P):
    G = Grid((2, 4))
    # word as slices along dimension 2: slice y = (w(0,y), w(1,y))
    slices = ["ab", "ba", "ba", "ab"]
    w = {(x, y): slices[y][x] for x in range(2) for y in range(4)}
    stab = [g for g in G.elems if all(w[G.add(c, g)] == w[c] for c in G.elems)]
    P(f"  w = slices {slices} (slice y = (w(0,y), w(1,y))); Stab(w) = {stab}")
    base = {(x, y): slices[y][x] for x in range(2) for y in range(2)}
    G22 = Grid((2, 2))
    stab_base = [g for g in G22.elems if all(base[G22.add(c, g)] == base[c] for c in G22.elems)]
    P(f"  its translational period u = slices {slices[:2]} on Z2 x Z2 has Stab(u) = {stab_base}")
    P("  -> w is a translational Lyndon word (no axis period, Stab = <(1,2)>), but its period")
    P("     u is NOT atranslational, so w is not counted by the (i,l) = (2,2) term")
    P("     (-mu(2)) |A^{(2,2)}| H = 1*2*1 = 2; the true count for this stabilizer is")
    P("     |A(Z2xZ4/<(1,2)>)| = |A(Z4)| = 3.")

    def stab_of(n, w):
        Gx = Grid(n)
        return [g for g in Gx.elems if all(w[Gx.add(c, g)] == w[c] for c in Gx.elems)]

    def canon_code(n, w):
        Gx = Grid(n)
        return min(tuple(w[Gx.add(c, g)] for c in Gx.elems) for g in Gx.elems)

    P("\n== 7. Witness for the Moebius factor: 4 x 4 grid (q = 2) ==")
    u = "aaab"
    w = {(x, y): u[(x + y) % 4] for x in range(4) for y in range(4)}
    P(f"  w(x,y) = u(x+y), u = {u}: slices {[''.join(w[(x, y)] for x in range(4)) for y in range(4)]}")
    P(f"  Stab(w) = {stab_of((4, 4), w)}  (order 4, period box (4,1), G/H = Z4, Lyndon)")
    P("  Such necklaces (two stabilizers <(1,1)>, <(1,3)>, 3 necklaces each for q = 2) belong to")
    P("  the summand (i,l) = (2,1), whose printed coefficient is -mu(n_2/l) = -mu(4) = 0.")

    P("\n== 8. Witnesses on the 2 x 2 x 2 grid (q = 2) ==")
    c = {(x1, x2): "ab"[(x1 + x2) % 2] for x1 in range(2) for x2 in range(2)}  # u = ab, g = (1)
    G22 = Grid((2, 2))
    words = {}
    for h in [(1, 0), (0, 1), (1, 1)]:
        w = {(x1, x2, y): c[G22.add((x1, x2), G22.mul(y, h))]
             for x1 in range(2) for x2 in range(2) for y in range(2)}
        words[h] = w
        P(f"  base 'ab' -> checkerboard c (dims 1-2), then c : <c>_h with h = {h}: "
          f"Stab = {stab_of((2, 2, 2), w)}, canonical = {''.join(canon_code((2, 2, 2), w))}")
    P("  h = (1,1) gives a word with an axis period (excluded by I(2,1,n) = 1); h = (1,0) and")
    P("  h = (0,1) give the SAME word, yet H(2,1,(2,2,2),3) = |G(1,n)| - I = 3 - 1 = 2 counts it")
    P("  twice (h and h + (1,1) coincide because (1,1) fixes the checkerboard).")
    w = {}
    for x1 in range(2):
        for x2 in range(2):
            w[(x1, x2, 0)] = c[(x1, x2)]
            w[(x1, x2, 1)] = "a"
    P(f"  w = [checkerboard ; constant a] (slices along dim 3): Stab = {stab_of((2, 2, 2), w)};")
    P("  its period box is (2,1,2), not of the form (n_1..n_{i-1}, l, 1..1): no summand of")
    P("  Theorem 3 is designed to count it (2 such necklaces for q = 2).")



if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
