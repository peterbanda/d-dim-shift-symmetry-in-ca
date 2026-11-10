"""Step 1 -- paper-only reconstruction of Proposition 10.2 (Inversion law),
shift_symmetry_d_dimensions.tex lines 980-1001, Def 2.1 (203-211),
Thm 4.3 (403-412, with notation of l.267 and Def. of r_d l.396-401),
Cor. (P^unif = |S|/sigma^{n^d}, l.694-697).

Written BEFORE reading any Lean file.
"""
from fractions import Fraction
from itertools import product
import mpmath as mp

mp.mp.dps = 80  # >= 60 significant digits


# ---------- Proposition 10.2 objects ----------
def phi_paper(p, d):
    """phi(d) = (1 - 1/p) p^d - 1/2 (p+1)^d, exact rational (d integer >= 0)."""
    return (1 - Fraction(1, p)) * Fraction(p) ** d - Fraction(1, 2) * Fraction(p + 1) ** d


def dc_paper(p):
    """d_c(p) = ln(2 - 2/p) / ln(1 + 1/p)."""
    p = mp.mpf(p)
    return mp.log(2 - 2 / p) / mp.log(1 + 1 / p)


def logb(base, x):
    return mp.log(x) / mp.log(base)


def thr_i_paper(p, sigma, d):
    """log_sigma(2 log_2(p) p^{d-1})."""
    return logb(sigma, 2 * logb(2, p) * mp.mpf(p) ** (d - 1))


def thr_ii_paper(p, sigma, d):
    """-log_sigma(2 log_2(p+1) (p+1)^{d-1})."""
    return -logb(sigma, 2 * logb(2, p + 1) * mp.mpf(p + 1) ** (d - 1))


def frac_to_mpf(fr):
    return mp.mpf(fr.numerator) / mp.mpf(fr.denominator)


def hyp_i_paper(p, sigma, d):
    """phi(d) > log_sigma(2 log_2(p) p^{d-1}); returns (bool, margin)."""
    m = frac_to_mpf(phi_paper(p, d)) - thr_i_paper(p, sigma, d)
    return m > 0, m


def hyp_ii_paper(p, sigma, d):
    """phi(d) < -log_sigma(2 log_2(p+1) (p+1)^{d-1}); returns (bool, margin)."""
    m = thr_ii_paper(p, sigma, d) - frac_to_mpf(phi_paper(p, d))
    return m > 0, m


def win_i_paper(p, d):
    """integer d >= 1 with d <= d_c(p) - 20."""
    return d >= 1 and mp.mpf(d) <= dc_paper(p) - 20


def win_ii_paper(p, d):
    """integer d >= d_c(p) + 20."""
    return mp.mpf(d) >= dc_paper(p) + 20


# ---------- Theorem 4.3 (enumeration) ----------
def factor(n):
    fs, m, q = {}, n, 2
    while q * q <= m:
        while m % q == 0:
            fs[q] = fs.get(q, 0) + 1
            m //= q
        q += 1
    if m > 1:
        fs[m] = fs.get(m, 0) + 1
    return sorted(fs)


def gauss_binom(d, r, p):
    num, den = 1, 1
    for i in range(r):
        num *= p ** (d - i) - 1
        den *= p ** (i + 1) - 1
    assert num % den == 0
    return num // den


def r_d(p, v, d):
    if v == 0:
        return 1
    return p ** (v * (v - 1) // 2) * gauss_binom(d, v, p)


def S_terms(n, d):
    """List of (coef, exponent) with |S| = sum coef * sigma^exponent (Thm 4.3)."""
    ps = factor(n)
    N = n ** d
    terms = []
    for v in product(range(d + 1), repeat=len(ps)):
        if not any(v):
            continue
        sgn = -1 if sum(v) % 2 == 0 else 1  # (-1)^{1+|v|}
        c = sgn
        h = 1
        for pi, vi in zip(ps, v):
            c *= r_d(pi, vi, d)
            h *= pi ** vi
        assert N % h == 0
        terms.append((c, N // h))
    return terms


def S_count(n, d, sigma):
    if sigma == 2:
        return sum(c << e if c > 0 else -((-c) << e) for c, e in S_terms(n, d))
    return sum(c * sigma ** e for c, e in S_terms(n, d))
