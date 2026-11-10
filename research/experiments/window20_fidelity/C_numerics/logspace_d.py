"""(d) probability form in high-precision log space, with rigorous tail bounds.

From Theorem 4.3 / Lean enumerationRHS:  |S_{n^d}| = sum_{h | rad(n)^d, h != 1} coeffOf(d,h) s^{N/h}.
Top term: h = p1 (smallest prime of n), coefficient [d 1]_{p1} = (p1^d-1)/(p1-1) > 0, exponent N/p1.
Every other h satisfies h >= nxt := min(p1^2 [if d>=2], p2 [if k>=2]), so N/h <= N/nxt, and
|coeffOf(d,h)| <= prod_{q | h} q^{C(v,2)} [d v]_q <= (3.47)^k rad(n)^{C(d,2)}
(using [d v]_q <= q^{v(d-v)} / prod_j (1-2^{-j}) < 3.47 q^{v(d-v)} and C(v,2)+v(d-v) <= C(d,2)).
Hence |S| = s^{N/p1} (c_top + delta), |delta| <= B := T (3.47)^k rad^{C(d,2)} s^{-(N/p1 - N/nxt)},
T = (d+1)^k - 2, and   log_s P_{n^d} in (N/p1 - N) + [log_s(c_top - B), log_s(c_top + B)]   if B < c_top.
"""
import sys, time
from multiprocessing import Pool
sys.path.insert(0, '.')
import mpmath as mp
import lean_side as L
from sympy import primerange

mp.mp.dps = 80
SIGMAS = (2, 3, 5, 10, 100, 10**6)
LN347 = mp.log(mp.mpf('3.47'))


def logP_interval(n, d, s):
    ps = L.prime_factors(n)
    p1, k = ps[0], len(ps)
    N = n ** d
    E_top = N // p1
    int_part = E_top - N
    c_top = (p1 ** d - 1) // (p1 - 1)
    cands = ([p1 * p1] if d >= 2 else []) + ([ps[1]] if k >= 2 else [])
    lns = mp.log(s)
    if not cands:
        B = mp.mpf(0)
    else:
        nxt = min(cands)
        gap = E_top - N // nxt
        assert gap > 0
        T = (d + 1) ** k - 2
        lnB = mp.log(T) + k * LN347 + (d * (d - 1) // 2) * mp.log(L.rad(n)) - gap * lns
        B = mp.exp(max(lnB, mp.mpf(-10**7)))   # still an upper bound for the tail
    if B >= c_top:
        return None
    lo = mp.log(c_top - B) / lns
    hi = mp.log(c_top + B) / lns
    return int_part, lo, hi


def decide(p, d, s):
    """Returns (sign, margin_lower_bound) of D = log_s P_{(p+1)^d} - log_s P_{p^d}: +1 (composite
    advantage proved), -1 (prime advantage proved), 0 (undecided / bound invalid)."""
    a, b = logP_interval(p + 1, d, s), logP_interval(p, d, s)
    if a is None or b is None:
        return 0, None
    X = a[0] - b[0]                      # exact integer part (= phi(d))
    rlo, rhi = a[1] - b[2], a[2] - b[1]  # real part interval
    assert abs(rlo) < 1e30 and abs(rhi) < 1e30
    if abs(X) > 10 ** 40:
        return (1 if X > 0 else -1), mp.mpf(abs(X))
    lo, hi = mp.mpf(X) + rlo, mp.mpf(X) + rhi
    if lo > 0:
        return 1, lo
    if hi < 0:
        return -1, -hi
    return 0, None


def self_test():
    """Interval must contain the exact value log_s(|S_{(p+1)^d}| s^{-(p+1)^d}) - log_s(|S_{p^d}| s^{-p^d})."""
    n_ok = n_bad = n_skip = 0
    for p in (3, 5, 7, 11, 13, 37, 41):
        for d in range(1, 8):
            if (p + 1) ** d > 2 * 10 ** 5:
                continue
            for s in (2, 3, 10):
                ivals = []
                for n in (p, p + 1):
                    iv = logP_interval(n, d, s)
                    S = L.enumerationRHS(n, d, s)
                    exact = mp.log(mp.mpf(S)) / mp.log(s) - n ** d
                    if iv is None:
                        n_skip += 1; continue
                    tol = mp.mpf(10) ** -60
                    inside = iv[0] + iv[1] - tol <= exact <= iv[0] + iv[2] + tol
                    n_ok += inside; n_bad += (not inside)
                    if not inside:
                        print("SELF-TEST FAIL", n, d, s, exact, iv)
    return n_ok, n_bad, n_skip


def run_prime(p):
    dcp = L.dc(p)
    dmax = int(mp.ceil(dcp)) + 60
    out = dict(p=p, ii_pts=0, ii_ok=0, ii_und=0, i_pts=0, i_ok=0, i_und=0, bad=[], min_ii=None, min_i=None)
    for d in range(1, dmax + 1):
        wi = d >= 1 and (p + 1) ** (d + 20) <= 2 * (p - 1) * p ** (d + 19)
        wii = d >= 21 and (p + 1) ** (d - 20) >= 2 * (p - 1) * p ** (d - 21)
        if not (wi or wii):
            continue
        for s in SIGMAS:
            sg, m = decide(p, d, s)
            if wii:
                out['ii_pts'] += 1
                if sg == -1:
                    out['ii_ok'] += 1
                    out['min_ii'] = m if out['min_ii'] is None else min(out['min_ii'], m)
                elif sg == 0:
                    out['ii_und'] += 1
                else:
                    out['bad'].append(('ii', p, d, s))
            if wi:
                out['i_pts'] += 1
                if sg == 1:
                    out['i_ok'] += 1
                    out['min_i'] = m if out['min_i'] is None else min(out['min_i'], m)
                elif sg == 0:
                    out['i_und'] += 1; out['bad'].append(('i-undecided', p, d, s))
                else:
                    out['bad'].append(('i', p, d, s))
    return out


if __name__ == '__main__':
    t0 = time.time()
    ok, bad, skip = self_test()
    print(f"self-test (interval contains exact log_s P, small tori): {ok} contained, {bad} not, {skip} bound-invalid skipped")
    primes = list(primerange(3, 2001))
    with Pool(8) as pool:
        res = pool.map(run_prime, primes[::-1], chunksize=1)
    tot = lambda k: sum(r[k] for r in res)
    print(f"(d) prime branch d >= dc(p)+20: {tot('ii_pts')} points, prime advantage proved at {tot('ii_ok')}, "
          f"undecided {tot('ii_und')}, contradicted {sum(1 for r in res for b in r['bad'] if b[0]=='ii')}")
    print(f"    smallest proved margin |log_s(P_(p+1)^d / P_p^d)| on branch (ii): "
          f"{mp.nstr(min(r['min_ii'] for r in res if r['min_ii'] is not None), 8)}")
    print(f"    composite branch (bonus, log space) d <= dc(p)-20: {tot('i_pts')} points, composite advantage proved at "
          f"{tot('i_ok')}, undecided {tot('i_und')}, contradicted {sum(1 for r in res for b in r['bad'] if b[0]=='i')}; undecided points: {[b for r in res for b in r['bad'] if b[0]=='i-undecided']}")
    print(f"    smallest proved margin on branch (i): {mp.nstr(min(r['min_i'] for r in res if r['min_i'] is not None), 8)}")
    print("    contradictions:", [b for r in res for b in r['bad'] if b[0] in ('i', 'ii')][:10])
    # a few explicit sample points for the report
    for (p, d, s) in [(3, 21, 2), (5, 23, 2), (7, 25, 2), (37, 45, 2), (1999, int(mp.ceil(L.dc(1999) + 20)), 2)]:
        a, b = logP_interval(p + 1, d, s), logP_interval(p, d, s)
        X = a[0] - b[0]
        print(f"    sample p={p} d={d} sigma={s}: log_s P_(p+1)^d - log_s P_p^d = X + r with X = phi(d) exact "
              f"({'%d bits' % abs(X).bit_length() if abs(X) > 10**40 else X}, sign {'-' if X < 0 else '+'}), "
              f"r in [{mp.nstr(a[1]-b[2], 10)}, {mp.nstr(a[2]-b[1], 10)}]")
    print(f"time {time.time() - t0:.1f}s")
