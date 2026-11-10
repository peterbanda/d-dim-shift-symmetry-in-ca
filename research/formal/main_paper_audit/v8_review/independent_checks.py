"""Definition-level checks for the v8 changes. Standard library; no project imports.

Enumerate subsets of actual projective lines and compute their vector-space
spans, then enumerate EVERY binary full-neighborhood CA on each small torus.
These are finite corroboration, not substitutes for the general Lean proofs.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import product
import json


def gaussian(p, d, r):
    value = Fraction(1)
    for i in range(r):
        value *= Fraction(p ** (d - i) - 1, p ** (i + 1) - 1)
    assert value.denominator == 1
    return value.numerator


def mobius_check(p, d):
    vectors = list(product(range(p), repeat=d))
    zero = (0,) * d
    reps = set()
    for v in vectors[1:]:
        a = next(x for x in v if x)
        reps.add(tuple(x * pow(a, -1, p) % p for x in v))
    reps = sorted(reps)
    spans = [frozenset([zero])]
    signed_by_span = defaultdict(int)
    signed_by_rank = [0] * (d + 1)
    for mask in range(1 << len(reps)):
        if mask:
            bit = mask & -mask
            v = reps[bit.bit_length() - 1]
            old = spans[mask ^ bit]
            span = frozenset(tuple((a + t*b) % p for a, b in zip(w, v))
                             for w in old for t in range(p))
            spans.append(span)
        span = spans[mask]
        rank = next(r for r in range(d + 1) if p**r == len(span))
        sign = (-1) ** mask.bit_count()
        signed_by_span[span] += sign
        signed_by_rank[rank] += sign
    for span, value in signed_by_span.items():
        rank = next(r for r in range(d + 1) if p**r == len(span))
        assert value == (-1)**rank * p**(rank * (rank - 1) // 2)
        assert sum(v for w, v in signed_by_span.items() if w <= span) == (len(span) == 1)
    assert signed_by_rank == [(-1)**r * p**(r*(r-1)//2) * gaussian(p, d, r)
                              for r in range(d + 1)]
    assert signed_by_rank[0] == 1  # includes the empty set of lines
    return dict(p=p, d=d, lines=len(reps), subsets=len(spans),
                subspaces=len(signed_by_span), coefficients=signed_by_rank)


def dynamics_check(n, d):
    cells = list(product(range(n), repeat=d))
    N = len(cells)
    index = {v:i for i, v in enumerate(cells)}
    shifts = [[index[tuple((x + y) % n for x, y in zip(u, v))]
               for u in cells] for v in cells]
    configs = range(1 << N)
    translated = [[sum(((x >> j) & 1) << i for i, j in enumerate(perm))
                   for perm in shifts] for x in configs]
    stabs = [sum(1 << v for v, y in enumerate(row) if y == x)
             for x, row in enumerate(translated)]
    rules = 1 << (1 << N)
    orbit_visits = 0
    for rule in range(rules):
        # Full-neighborhood local rule is an arbitrary Boolean truth table.
        # At cell u it reads x translated by u, exactly as in Definition 2.4.
        phi = [sum(((rule >> z) & 1) << u for u, z in enumerate(row))
               for row in translated]
        for x in configs:
            assert stabs[x] & ~stabs[phi[x]] == 0
            seen, y = set(), x
            while y not in seen:
                seen.add(y)
                assert stabs[x] & ~stabs[y] == 0
                orbit_visits += 1
                y = phi[y]
    all_shifts = (1 << N) - 1
    if (n, d) == (4, 1):
        target = sum((i % 2) << i for i in range(4))
        assert stabs[0] == all_shifts and 1 < stabs[target] < all_shifts
    if (n, d) == (2, 2):
        # Three allowed outputs. Each loses an input symmetry, yet no one
        # nonzero translation is lost by ALL outputs: quantifier-order test.
        targets = [sum((sum(a*b for a,b in zip(v,u)) % 2) << i
                       for i,u in enumerate(cells)) for v in cells[1:]]
        broken = [stabs[0] & ~stabs[y] for y in targets]
        assert all(broken)
        assert broken[0] & broken[1] & broken[2] == 0
    return dict(n=n, d=d, configurations=1 << N, rules=rules,
                one_step_checks=rules*(1 << N), trajectory_visits=orbit_visits)


if __name__ == '__main__':
    result = {'mobius':[mobius_check(p,d) for p,d in
                        [(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(5,1),(5,2)]],
              'dynamics':[dynamics_check(n,d) for n,d in [(2,1),(3,1),(4,1),(2,2)]],
              'status':'PASS'}
    print(json.dumps(result, indent=2))
