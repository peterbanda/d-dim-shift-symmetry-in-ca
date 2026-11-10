#!/usr/bin/env python3
"""Checks for Remark 9.4 (read complexity) of the paper and the paragraph after it (the Fourier route).
Run from research/experiments/; deterministic (seeded), exact.

[1] Fourier route: Stab(s) = {v : m_s(v) = 0}, m_s(v) = N - sum_a (I_a * I_a)(v) (cyclic correlation on
    Z_n^d), computed with one d-dimensional FFT per symbol present (float64, rounded; the values are
    integers <= N, and the rounding error is asserted < 0.25) = the stabilizer by definition, on random
    and on planted-symmetric configurations over many tori and alphabets.
[2] One-defect lemma: for N >= 2, a configuration equal to a constant except in exactly one cell has
    trivial stabilizer -- exhaustive over tori with N <= 64, every cell, every pair of symbols (sigma <= 3).
[3] The key step of the lower bound: for every proper subset U of the cells and every constant a, the
    partial configuration "a on U" has both a shift-symmetric completion (the constant) and an aperiodic
    one (a single defect outside U) -- exhaustive over all subsets U for N <= 12, sigma = 2.
[4] Minimax over all deterministic adaptive algorithms (decision trees): the least worst-case number of
    reads that decides shift symmetry is exactly N, by exhaustive game-tree search on tiny tori.
"""
import itertools
import sys
from functools import lru_cache
from math import prod

import numpy as np

rng = np.random.default_rng([2026, 11, 6, 3])


def elements(n, d):
    return list(itertools.product(range(n), repeat=d))


def stab_definition(s):
    """s: d-dim numpy array (Z_n^d); every v with s(u + v) = s(u) for all u."""
    n, d = s.shape[0], s.ndim
    return {v for v in elements(n, d) if np.array_equal(np.roll(s, shift=[-x for x in v], axis=tuple(range(d))), s)}


def stab_fft(s, sigma):
    n, d = s.shape[0], s.ndim
    N = s.size
    agree = np.zeros(s.shape)
    for a in np.unique(s):                                   # symbols present: at most min(sigma, N)
        F = np.fft.fftn((s == a).astype(float))
        agree += np.fft.ifftn(F.conj() * F).real             # (I_a * I_a)(v) = sum_u I_a(u) I_a(u + v)
    m = N - agree
    err = np.abs(m - np.round(m)).max()
    assert err < 0.25, err
    m = np.round(m).astype(int)
    return {tuple(int(x) for x in v) for v in zip(*np.nonzero(m == 0))}


def planted(n, d, sigma):
    """A configuration fixed by a random nonzero translation (constant on the orbits of <w>)."""
    w = tuple(int(x) for x in rng.integers(0, n, d))
    while not any(w):
        w = tuple(int(x) for x in rng.integers(0, n, d))
    s = -np.ones((n,) * d, dtype=int)
    for u in elements(n, d):
        if s[u] >= 0:
            continue
        c = int(rng.integers(0, sigma))
        x = u
        while s[x] < 0:
            s[x] = c
            x = tuple((xi + wi) % n for xi, wi in zip(x, w))
    return s


def main():
    fails = 0
    def check(ok, msg):
        nonlocal fails
        print(("  ok   " if ok else "  FAIL ") + msg)
        fails += not ok

    print("[1] FFT stabilizer = stabilizer by definition")
    cases = 0
    tori = [(n, 1) for n in range(2, 41)] + [(n, 2) for n in range(2, 13)] + [(n, 3) for n in range(2, 7)] + [(n, 4) for n in (2, 3, 4)]
    for n, d in tori:
        for sigma in (2, 3, 5):
            for trial in range(6):
                s = planted(n, d, sigma) if trial % 2 else rng.integers(0, sigma, (n,) * d)
                if stab_fft(s, sigma) != stab_definition(s):
                    check(False, f"n={n} d={d} sigma={sigma} trial={trial}")
                cases += 1
    check(fails == 0, f"{cases} configurations on {len(tori)} tori (d = 1..4), sigma in (2, 3, 5), half planted-symmetric")

    print("[2] one defect => trivial stabilizer")
    cnt = 0
    for n, d in [(n, d) for d in (1, 2, 3) for n in range(2, 9) if n ** d <= 64]:
        for sigma in (2, 3):
            for a, b in itertools.permutations(range(sigma), 2):
                for u in elements(n, d):
                    s = np.full((n,) * d, a)
                    s[u] = b
                    cnt += 1
                    if stab_definition(s) != {(0,) * d}:
                        check(False, f"n={n} d={d} a={a} b={b} u={u}")
    check(fails == 0, f"{cnt} one-defect configurations (N <= 64)")

    print("[3] every proper read set U leaves the answer open on a constant configuration")
    cnt = 0
    for n, d in [(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (12, 1), (2, 2), (3, 2), (2, 3)]:
        els = elements(n, d)
        N = len(els)
        for r in range(N):
            for U in itertools.combinations(range(N), r):
                outside = [i for i in range(N) if i not in U]
                s = np.zeros((n,) * d, dtype=int)
                s[els[outside[0]]] = 1                       # a defect outside U
                cnt += 1
                if stab_definition(s) != {(0,) * d} or len(stab_definition(np.zeros((n,) * d, dtype=int))) < 2:
                    check(False, f"n={n} d={d} U={U}")
    check(fails == 0, f"{cnt} (torus, proper subset U) pairs, sigma = 2")

    print("[4] minimax over all adaptive algorithms = N")
    for n, d, sigma in [(2, 1, 2), (3, 1, 2), (4, 1, 2), (5, 1, 2), (2, 2, 2), (6, 1, 2), (3, 1, 3), (2, 2, 3), (7, 1, 2), (8, 1, 2), (2, 3, 2), (3, 2, 2)]:
        els = elements(n, d)
        N = len(els)
        idx = {e: i for i, e in enumerate(els)}
        shifts = [[idx[tuple((x + y) % n for x, y in zip(e, v))] for e in els] for v in els[1:]]
        sym = {}
        for cfg in itertools.product(range(sigma), repeat=N):
            sym[cfg] = any(all(cfg[p[i]] == cfg[i] for i in range(N)) for p in shifts)

        @lru_cache(maxsize=None)
        def value(partial):                                  # partial: tuple with -1 = unread
            comps = [c for c in sym if all(p < 0 or p == x for p, x in zip(partial, c))]
            answers = {sym[c] for c in comps}
            if len(answers) == 1:
                return 0
            best = N + 1
            for i in range(N):
                if partial[i] < 0:
                    worst = max(value(partial[:i] + (a,) + partial[i + 1:]) for a in range(sigma))
                    best = min(best, 1 + worst)
            return best

        v = value((-1,) * N)
        check(v == N, f"Z_{n}^{d}, sigma={sigma}: least worst-case reads = {v} (N = {N})")

    print("ALL PASSED" if fails == 0 else f"{fails} FAILURES")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
