"""(a) paper reading vs literal Lean transcription on the grid; (b) the
criteria-form claim on the grid.
Grid: primes 3 <= p <= 2000; sigma in {2,3,5,10,100,10^6}; integers 1 <= d <= ceil(dc(p)) + 60.
Paper side: exact integers where the paper's quantity is rational (phi(d); the
window conditions via the exact equivalent (p+1)^{d+20} <= 2(p-1)p^{d+19} etc.),
log thresholds summed as ln2 + ln ln p - ln ln 2 + (d-1) ln p (different route).
Lean side: lean_side.py (mpmath, rpow, Real.logb of the literal product).
"""
import sys, json, time
from multiprocessing import Pool
sys.path.insert(0, '.')
import mpmath as mp
import lean_side as L
from sympy import primerange, isprime

mp.mp.dps = 80
SIGMAS = (2, 3, 5, 10, 100, 10**6)
TIE = mp.mpf(10) ** -60


def paper_window_i(p, d):          # d >= 1 and d <= dc(p) - 20  (exact)
    return d >= 1 and (p + 1) ** (d + 20) <= 2 * (p - 1) * p ** (d + 19)


def paper_window_ii(p, d):         # d >= dc(p) + 20  (exact)
    return d >= 21 and (p + 1) ** (d - 20) >= 2 * (p - 1) * p ** (d - 21)


def paper_twice_phi(p, d):         # 2*phi(d) = 2(p-1)p^{d-1} - (p+1)^d   (exact, d >= 1)
    return 2 * (p - 1) * p ** (d - 1) - (p + 1) ** d


def run_prime(p):
    res = dict(p=p, points=0, dis_wi=0, dis_wii=0, dis_hi=0, dis_hii=0, examples=[],
               win_i_pts=0, win_ii_pts=0, viol_i=0, viol_ii=0, viol_examples=[],
               lean_ties=[], min_abs_lean_win_margin=None, min_abs_lean_hyp_margin=None,
               max_phi_reldiff=mp.mpf(0), Cneed_i=None, Cneed_ii=None)
    dcp = L.dc(p)
    dmax = int(mp.ceil(dcp)) + 60
    lnp, ln2 = mp.log(p), mp.log(2)
    lnlnp, lnln2, lnlnp1 = mp.log(mp.log(p)), mp.log(ln2), mp.log(mp.log(p + 1))
    lnp1 = mp.log(p + 1)
    minwin, minhyp = None, None
    for d in range(1, dmax + 1):
        # ---- window conditions
        wi_p, wii_p = paper_window_i(p, d), paper_window_ii(p, d)
        mi, mii = L.win_i_margin(p, d), L.win_ii_margin(p, d)
        wi_l, wii_l = mi >= 0, mii >= 0
        # exact tie resolution, applied only where a numeric near-tie is detected:
        # at p = 3 the two log arguments are the same rational 4/3, so dc(3) = 1 exactly
        if abs(mi) < TIE:
            res['lean_ties'].append((p, d, 'win_i', mp.nstr(mi, 5)))
            wi_l = (d <= 1 - 20) if p == 3 else None
        if abs(mii) < TIE:
            res['lean_ties'].append((p, d, 'win_ii', mp.nstr(mii, 5)))
            wii_l = (d >= 1 + 20) if p == 3 else None
        aw = min(abs(mi), abs(mii))
        if not (p == 3 and aw < TIE):
            minwin = aw if minwin is None else min(minwin, aw)
        if wi_l != wi_p:
            res['dis_wi'] += 1; res['examples'].append(('win_i', p, d))
        if wii_l != wii_p:
            res['dis_wii'] += 1; res['examples'].append(('win_ii', p, d))
        # ---- phi
        tphi = paper_twice_phi(p, d)
        phi_p = mp.mpf(tphi) / 2
        phi_l = L.phi(p, L.R(d))
        if phi_p != 0:
            res['max_phi_reldiff'] = max(res['max_phi_reldiff'], abs(phi_l - phi_p) / abs(phi_p))
        for s in SIGMAS:
            res['points'] += 1
            lns = mp.log(s)
            thr_i = (ln2 + lnlnp - lnln2 + (d - 1) * lnp) / lns            # paper route
            thr_ii = -(ln2 + lnlnp1 - lnln2 + (d - 1) * lnp1) / lns
            hi_p, hii_p = phi_p > thr_i, phi_p < thr_ii
            hmi, hmii = L.hyp_i_margin(p, s, d, phi_l), L.hyp_ii_margin(p, s, d, phi_l)
            hi_l, hii_l = hmi > 0, hmii > 0
            for m, scale in ((hmi, phi_l), (hmii, phi_l)):
                rel = abs(m) / max(mp.mpf(1), abs(scale))
                minhyp = rel if minhyp is None else min(minhyp, rel)
            if hi_l != hi_p:
                res['dis_hi'] += 1; res['examples'].append(('hyp_i', p, s, d))
            if hii_l != hii_p:
                res['dis_hii'] += 1; res['examples'].append(('hyp_ii', p, s, d))
            # ---- (b) criteria-form claim (Lean transcription; identical to paper if no disagreement)
            if wi_l:
                res['win_i_pts'] += 1
                if not hi_l:
                    res['viol_i'] += 1; res['viol_examples'].append(('i', p, s, d))
            if wii_l:
                res['win_ii_pts'] += 1
                if not hii_l:
                    res['viol_ii'] += 1; res['viol_examples'].append(('ii', p, s, d))
            # smallest window constant that would work on the grid
            if d < dcp and not hi_l:
                c = dcp - d
                res['Cneed_i'] = c if res['Cneed_i'] is None else max(res['Cneed_i'], c)
            if d > dcp and not hii_l:
                c = d - dcp
                res['Cneed_ii'] = c if res['Cneed_ii'] is None else max(res['Cneed_ii'], c)
    res['min_abs_lean_win_margin'] = minwin
    res['min_abs_lean_hyp_margin'] = minhyp
    res['dmax'] = dmax
    return res


if __name__ == '__main__':
    t0 = time.time()
    primes = [q for q in primerange(3, 2001)]
    assert all(isprime(q) for q in primes) and primes[0] == 3 and primes[-1] == 1999
    with Pool(8) as pool:
        out = pool.map(run_prime, primes[::-1], chunksize=1)
    out.sort(key=lambda r: r['p'])
    tot = lambda k: sum(r[k] for r in out)
    print(f"primes: {len(primes)} (3..{primes[-1]}), sigmas: {SIGMAS}")
    print(f"(p,d) pairs: {sum(r['dmax'] for r in out)}, grid points (p,sigma,d): {tot('points')}")
    print(f"(a) disagreements  window(i): {tot('dis_wi')}  window(ii): {tot('dis_wii')}  "
          f"hyp(i): {tot('dis_hi')}  hyp(ii): {tot('dis_hii')}")
    ex = [e for r in out for e in r['examples']][:10]
    print("    examples:", ex)
    ties = [t for r in out for t in r['lean_ties']]
    print(f"    Lean-side numeric near-ties (|margin| < 1e-60) on window antecedents: {ties} "
          f"(resolved exactly: dc(3) = 1 since 2-2/3 = 1+1/3)")
    print(f"    min |window margin| over p >= 5: {mp.nstr(min(r['min_abs_lean_win_margin'] for r in out if r['p'] != 3), 6)}")
    print(f"    min relative |hypothesis margin|: {mp.nstr(min(r['min_abs_lean_hyp_margin'] for r in out), 6)}")
    print(f"    max rel. diff phi (Lean rpow vs exact integer): {mp.nstr(max(r['max_phi_reldiff'] for r in out), 6)}")
    print(f"(b) branch (i) exercised at {tot('win_i_pts')} points (primes with nonempty branch: "
          f"{sum(1 for r in out if r['win_i_pts'] > 0)}, smallest p = {min((r['p'] for r in out if r['win_i_pts'] > 0), default=None)}), "
          f"violations: {tot('viol_i')}")
    print(f"    branch (ii) exercised at {tot('win_ii_pts')} points (all {sum(1 for r in out if r['win_ii_pts'] > 0)} primes), "
          f"violations: {tot('viol_ii')}")
    print("    violation examples:", [e for r in out for e in r['viol_examples']][:10])
    ci = max((r['Cneed_i'] for r in out if r['Cneed_i'] is not None), default=None)
    cii = max((r['Cneed_ii'] for r in out if r['Cneed_ii'] is not None), default=None)
    arg_i = max((r for r in out if r['Cneed_i'] is not None), key=lambda r: r['Cneed_i'])['p']
    arg_ii = max((r for r in out if r['Cneed_ii'] is not None), key=lambda r: r['Cneed_ii'])['p']
    print(f"    tightest constant on grid: (i) needs C > {mp.nstr(ci, 6)} (p={arg_i}), (ii) needs C > {mp.nstr(cii, 6)} (p={arg_ii})")
    print(f"time {time.time() - t0:.1f}s")
