"""PR #1 review: exact arithmetic, standard library, no project imports.

Checks window membership and sufficient logarithmic bounds using integers.
Also reconstructs the probability polynomials from the paper's enumeration
formula and certifies their comparison using a rigorous leading-term bound.
Run from any directory; outputs JSON. These finite checks supplement Lean.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import comb
import json


def primes_to(limit):
    sieve = [True] * (limit + 1)
    sieve[:2] = [False, False]
    for p in range(2, limit + 1):
        if sieve[p]:
            for k in range(p * p, limit + 1, p):
                sieve[k] = False
    return [p for p in range(2, limit + 1) if sieve[p]]


def gaussian(q, d, r):
    value = Fraction(1)
    for i in range(r):
        value *= Fraction(q ** (d - i) - 1, q ** (i + 1) - 1)
    assert value.denominator == 1
    return value.numerator


def probability_polynomial(n, d):
    """Integer coefficients indexed by the (negative) exponent of sigma."""
    ps = [p for p in primes_to(n) if n % p == 0]
    coeffs = [[p ** comb(r, 2) * gaussian(p, d, r) for r in range(d + 1)] for p in ps]
    powers = [[p ** r for r in range(d + 1)] for p in ps]
    N = n ** d
    result = defaultdict(int)
    for ranks in product(range(d + 1), repeat=len(ps)):
        if not any(ranks):
            continue
        divisor, coefficient = 1, (-1) ** (1 + sum(ranks))
        for i, r in enumerate(ranks):
            divisor *= powers[i][r]
            coefficient *= coeffs[i][r]
        assert N % divisor == 0
        result[N // divisor - N] += coefficient
    return {e: c for e, c in result.items() if c}


def exact_window_flags(p, d):
    # q^(d+20) <= 2-2/p, and q^(d-20) >= 2-2/p, respectively.
    # Cross multiplication removes logarithms and negative exponents.
    A, B = p ** (d - 1), (p + 1) ** d
    return (B * (p + 1) ** 20 <= 2 * (p - 1) * A * p ** 20,
            B * p ** 20 >= 2 * (p - 1) * A * (p + 1) ** 20)


def floor_center(p):
    a, b, k = 1, 1, 0
    while b * (p + 1) * p <= 2 * (p - 1) * a * p:
        a *= p
        b *= p + 1
        k += 1
    assert b * p <= 2 * (p - 1) * a
    assert b * (p + 1) * p > 2 * (p - 1) * a * p
    return k, b * p == 2 * (p - 1) * a


def polynomial_sign_certificate(p, d, lower):
    # Orient the difference so the claimed sign is positive.
    left, right = ((p + 1, p) if lower else (p, p + 1))
    terms = defaultdict(int, probability_polynomial(left, d))
    for e, c in probability_polynomial(right, d).items():
        terms[e] -= c
    terms = {e: c for e, c in terms.items() if c}
    exponents = sorted(terms, reverse=True)
    lead = terms[exponents[0]]
    assert lead > 0, (p, d, lower, 'wrong leading sign')
    if len(exponents) == 1:
        return {'p': p, 'd': d, 'branch': 'lower' if lower else 'upper', 'terms': 1}
    gap = exponents[0] - exponents[1]
    tail = sum(abs(terms[e]) for e in exponents[1:])
    # For every sigma >= 2, |scaled tail| <= tail / sigma^gap.
    # This proves positivity without constructing sigma^(n^d).
    if gap < tail.bit_length():
        assert lead * (1 << gap) > tail, (p, d, lower, 'dominance inconclusive')
    return {'p': p, 'd': d, 'branch': 'lower' if lower else 'upper',
            'terms': len(terms), 'gap_bits': gap.bit_length(), 'tail_bits': tail.bit_length()}


def exact_probability(n, d, sigma):
    N = n ** d
    count = sum(c * sigma ** (e + N) for e, c in probability_polynomial(n, d).items())
    assert 0 < count <= sigma ** N
    return Fraction(count, sigma ** N)


def main():
    checked = lower_hits = upper_hits = 0
    first_lower_prime = None
    for p in primes_to(1999)[1:]:
        p20, q20 = p ** 20, (p + 1) ** 20
        A, B = 1, p + 1
        for d in range(1, p + 26):
            lower = B * q20 <= 2 * (p - 1) * A * p20
            upper = B * p20 >= 2 * (p - 1) * A * q20
            assert not (lower and upper)
            twice_phi = 2 * (p - 1) * A - B
            # log_sigma(2 log_2(m) m^(d-1)) <= 1+d*ceil(log_2(m))
            # for all sigma>=2. bit_length is a conservative integer ceiling.
            if lower:
                assert twice_phi > 2 * (1 + d * p.bit_length()), (p, d)
                lower_hits += 1
                if first_lower_prime is None:
                    first_lower_prime = p
            if upper:
                assert -twice_phi > 2 * (1 + d * (p + 1).bit_length()), (p, d)
                upper_hits += 1
            checked += 1
            A *= p
            B *= p + 1
    assert first_lower_prime == 37
    assert [d for d in range(1, 10) if exact_window_flags(37, d)[0]] == [1, 2, 3, 4]
    assert floor_center(3) == (1, True)
    assert floor_center(31) == (20, False)
    assert floor_center(37) == (24, False)
    assert not exact_window_flags(3, 20)[1] and exact_window_flags(3, 21)[1]

    certificates = []
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 31, 37, 43, 47, 61, 97):
        floor, integral = floor_center(p)
        upper = floor + (0 if integral else 1) + 20
        points = {(upper, False), (upper + 1, False)}
        if floor - 20 >= 1:
            points |= {(1, True), (floor - 20, True)}
        for d, lower in sorted(points):
            assert exact_window_flags(p, d)[0 if lower else 1]
            certificates.append(polynomial_sign_certificate(p, d, lower))

    exact_count_cases = 0
    for p in (37, 41, 43, 47):
        for d in (1, 2):
            assert exact_window_flags(p, d)[0]
            for sigma in (2, 3, 5):
                assert exact_probability(p, d, sigma) < exact_probability(p + 1, d, sigma)
                exact_count_cases += 1
    print(json.dumps({'status': 'PASS', 'prime_dimension_pairs': checked,
        'lower_window_hits': lower_hits, 'upper_window_hits': upper_hits,
        'first_prime_with_nonempty_lower_window': first_lower_prime,
        'exact_count_comparisons': exact_count_cases,
        'probability_sign_certificates_all_alphabets_ge_2': certificates}, indent=2))


if __name__ == '__main__':
    main()
