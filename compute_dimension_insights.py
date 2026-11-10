#!/usr/bin/env python3
"""
Dimension-dependence and criticality charts (charts 12-16), post-audit.

All quantities derive from the CERTIFIED enumeration formula (claim C001,
research/claims.yaml): |S| and P = |S|/sigma^(n^d) are evaluated in log10
space by exact-coefficient log-sum-exp (leading term + signed corrections),
which agrees with exact integer evaluation wherever both are feasible
(checked below in main()).

Charts:
 12  log10 P vs dimension d for representative n            (collapse)
 13  decay rate c(n,d) = -log_sigma(P)/n^d vs d             (universality classes 1 - 1/p1)
 14  log10 P vs n at d = 2 and d = 3                        (pattern flip, audited)
 15  prime-composite inversion: Delta(d) = log10 P(p+1)-log10 P(p),
     measured crossing d_c vs prediction ln(2(1-1/p))/ln((p+1)/p)
 16  correction ratio |T2/T1| vs d and the crossover scale d*(p)

sigma = 2 throughout.
"""

import math
import sys
import itertools

sys.path.insert(0, 'research/experiments')
from verify_bruteforce import prime_factors, is_prime, gaussian_binomial, r_d, formula_count, log10_bigint

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

LOG10_2 = math.log10(2)

# ------------------------------------------------------------ log-space |S|

def log10_S(n, d, s=2):
    """log10 |S_{n^d}| via signed log-sum-exp over the certified formula."""
    ps = prime_factors(n)
    k = len(ps)
    N = n ** d
    terms = []
    for v in itertools.product(range(d + 1), repeat=k):
        if all(x == 0 for x in v):
            continue
        coeff = 1
        div = 1
        for p, vi in zip(ps, v):
            coeff *= r_d(p, vi, d)
            div *= p ** vi
        t = log10_bigint(coeff) + (N // div) * math.log10(s)
        terms.append(((-1) ** (1 + sum(v)), t))
    L = max(t for _, t in terms)
    tot = sum(sg * 10 ** (t - L) for sg, t in terms if t - L > -300)
    return L + math.log10(tot)

def log10_P(n, d, s=2):
    return log10_S(n, d, s) - n ** d * math.log10(s)

def decay_rate(n, d, s=2):
    """c(n,d) = -log_sigma(P)/N in [1/2 - o(1), 1 - 1/p1]."""
    return -log10_P(n, d, s) / (n ** d * math.log10(s))

# ------------------------------------------------------------ chart 12

def chart12():
    fig, ax = plt.subplots(figsize=(9, 6))
    ns = [2, 3, 4, 5, 6, 10, 12]
    cmap = plt.cm.viridis(np.linspace(0, 0.9, len(ns)))
    for n, col in zip(ns, cmap):
        dmax = max(2, int(math.log(10 ** 12) / math.log(n)))
        ds = list(range(1, min(dmax, 12) + 1))
        ys = [log10_P(n, d) for d in ds]
        ax.plot(ds, ys, '-o', color=col, ms=4,
                label=f'n = {n}' + (' (prime)' if is_prime(n) else ''))
    ax.set_yscale('symlog', linthresh=1)
    ax.set_xlabel('dimension d')
    ax.set_ylabel(r'$\log_{10} P^{\mathrm{unif}}$   (symlog axis)')
    ax.set_title('Shift-symmetry probability vs dimension ($\\sigma$=2):\n'
                 'no threshold — double-exponential collapse $P \\approx \\sigma^{-c\\,n^d}$')
    ax.legend(fontsize=9, ncol=2)
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig('charts/chart12_logP_vs_d.png', dpi=150)
    plt.close(fig)

# ------------------------------------------------------------ chart 13

def chart13():
    fig, ax = plt.subplots(figsize=(9.5, 6))
    class_color = {2: 'tab:blue', 3: 'tab:orange', 5: 'tab:green',
                   7: 'tab:red', 11: 'tab:purple', 13: 'tab:brown'}
    for n in range(2, 14):
        p1 = prime_factors(n)[0]
        dmax = max(2, int(math.log(10 ** 12) / math.log(n)))
        ds = list(range(1, min(dmax, 14) + 1))
        cs = [decay_rate(n, d) for d in ds]
        ax.plot(ds, cs, '-o', ms=3.5, color=class_color[p1], alpha=0.85,
                label=f'n={n}')
    for p1, col in class_color.items():
        ax.axhline(1 - 1 / p1, color=col, ls='--', lw=1, alpha=0.6)
        ax.text(13.55, 1 - 1 / p1, f'$1-1/{p1}$', color=col, fontsize=8,
                va='center')
    ax.axhspan(0, 0.5, color='gray', alpha=0.08)
    ax.text(1.1, 0.47, 'forbidden by the upper bound:  $c \\geq 1/2 - o(1)$',
            fontsize=8, color='gray')
    ax.set_xlabel('dimension d')
    ax.set_ylabel(r'decay rate  $c(n,d) = -\log_\sigma P \,/\, n^d$')
    ax.set_ylim(0.4, 1.0)
    ax.set_xlim(0.8, 15.6)
    ax.set_title('Decay-rate universality classes ($\\sigma$=2): every $n$ converges to\n'
                 '$c \\to 1 - 1/p_1(n)$, set by the SMALLEST prime factor alone (proven sandwich)')
    ax.legend(fontsize=7, ncol=4, loc='lower right')
    ax.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig('charts/chart13_decay_rate_classes.png', dpi=150)
    plt.close(fig)

# ------------------------------------------------------------ chart 14

def chart14():
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.2))
    for ax, d in zip(axes, (2, 3)):
        ns = list(range(2, 31))
        ys = [log10_P(n, d) for n in ns]
        pm = [is_prime(n) for n in ns]
        ax.plot(ns, ys, '-', color='gray', alpha=0.5, lw=0.8)
        ax.scatter([n for n, q in zip(ns, pm) if not q],
                   [y for y, q in zip(ys, pm) if not q],
                   c='steelblue', s=26, label='composite', zorder=3)
        ax.scatter([n for n, q in zip(ns, pm) if q],
                   [y for y, q in zip(ys, pm) if q],
                   c='crimson', marker='D', s=30, label='prime', zorder=4)
        ax.set_xlabel('lattice side n')
        ax.set_ylabel(r'$\log_{10} P$')
        ax.grid(alpha=0.3)
        ax.legend(fontsize=9)
        if d == 2:
            ax.set_title('d = 2: every prime p ≥ 5 is a local dip\n(a theorem; n = 3 is the exception: P(3) > P(4))')
        else:
            ax.set_title('d = 3: the pattern BREAKS\n'
                         '(P(5) > P(6): prime beats composite)')
            ax.annotate('P(5) > P(6)', xy=(5.5, (log10_P(5, 3) + log10_P(6, 3)) / 2),
                        xytext=(9, -60), fontsize=10, color='black',
                        arrowprops=dict(arrowstyle='->', lw=1))
    fig.suptitle('Prime/composite extremal pattern: true at d = 2, false for d ≥ 3 ($\\sigma$=2)', y=1.02)
    fig.tight_layout()
    fig.savefig('charts/chart14_pattern_flip.png', dpi=150, bbox_inches='tight')
    plt.close(fig)

# ------------------------------------------------------------ chart 15

def inversion_curve(p, dmax):
    ds, deltas = [], []
    for d in range(1, dmax + 1):
        ds.append(d)
        deltas.append(log10_P(p + 1, d) - log10_P(p, d))
    return ds, deltas

def crossing(ds, deltas):
    if deltas[0] < 1e-9:            # crossing at or before d = 1 (pair (3,4): exactly d = 1)
        return float(ds[0])
    for i in range(len(ds) - 1):
        if deltas[i] >= 0 > deltas[i + 1]:
            x0, x1, y0, y1 = ds[i], ds[i + 1], deltas[i], deltas[i + 1]
            return x0 + y0 * (x1 - x0) / (y0 - y1)
    return None

def chart15():
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(13, 5.2))
    primes = [3, 5, 7, 11, 13]
    meas, pred = [], []
    cmap = plt.cm.plasma(np.linspace(0, 0.8, len(primes)))
    for p, col in zip(primes, cmap):
        dmax = 12 if p <= 7 else 11
        ds, deltas = inversion_curve(p, dmax)
        ax1.plot(ds, deltas, '-o', ms=4, color=col, label=f'({p}, {p+1})')
        dc = crossing(ds, deltas)
        meas.append(dc)
        dc_pred = math.log(2 * (1 - 1 / p)) / math.log((p + 1) / p)
        pred.append(dc_pred)
        if dc:
            ax1.axvline(dc, color=col, ls=':', lw=1, alpha=0.6)
    ax1.axhline(0, color='black', lw=1)
    ax1.set_yscale('symlog', linthresh=1)
    ax1.set_xlabel('dimension d')
    ax1.set_ylabel(r'$\log_{10}\,[P(p{+}1)\,/\,P(p)]$   (symlog)')
    ax1.set_title('Composite advantage $\\to$ prime advantage:\nsign flips at a pair-dependent $d_c$')
    ax1.legend(fontsize=9, title='pair (prime, even)')
    ax1.grid(alpha=0.3)

    ax2.plot(primes, pred, 's--', color='gray',
             label=r'predicted  $d_c=\ln(2(1{-}1/p))/\ln(1{+}1/p)$')
    ax2.plot(primes, meas, 'o-', color='crimson', label='measured (interpolated zero)')
    ps = np.linspace(3, 14, 100)
    ax2.plot(ps, ps * math.log(2), ':', color='steelblue', alpha=0.8,
             label=r'line $p\,\ln 2$  ($d_c = p\ln 2 + O(1)$)')
    ax2.set_xlabel('prime p')
    ax2.set_ylabel(r'inversion dimension $d_c$')
    ax2.set_title('The inversion dimension grows LINEARLY in p:\n$d_c \\approx p\\ln 2$ — a crossover, not a critical point')
    ax2.legend(fontsize=9)
    ax2.grid(alpha=0.3)
    fig.tight_layout()
    fig.savefig('charts/chart15_inversion_dimension.png', dpi=150)
    plt.close(fig)
    return list(zip(primes, meas, pred))

# ------------------------------------------------------------ chart 16

def log10_T2_over_T1(p, d, s=2):
    return (log10_bigint(p * gaussian_binomial(d, 2, p))
            - log10_bigint(gaussian_binomial(d, 1, p))
            - p ** (d - 2) * (p - 1) * math.log10(s))

def dstar(p, theta=0.05, s=2):
    prev = None
    for d in range(2, 60):
        r = log10_T2_over_T1(p, d, s)
        if r <= math.log10(theta):
            if prev is None:
                return float(d)
            return (d - 1) + (prev - math.log10(theta)) / (prev - r)
        prev = r
    return float('nan')

def chart16():
    fig, ax = plt.subplots(figsize=(9, 6))
    for p, col in zip([2, 3, 5, 7], ['tab:blue', 'tab:orange', 'tab:green', 'tab:red']):
        ds = list(range(2, 11))
        ys = [log10_T2_over_T1(p, d) for d in ds]
        ax.plot(ds, ys, '-o', ms=4, color=col, label=f'p = {p}')
    ax.axhline(math.log10(0.05), color='black', ls='--', lw=1)
    ax.text(8.2, math.log10(0.05) + 3, '5% threshold', fontsize=9)
    ax.set_yscale('symlog', linthresh=1)
    ax.set_xlabel('dimension d')
    ax.set_ylabel(r'$\log_{10}|T_2/T_1|$   (symlog)')
    ax.set_title('Correction term dies doubly-exponentially: $|T_2/T_1| \\sim \\sigma^{-p^{d-2}(p-1)}$\n'
                 'smooth crossover at $d^*$, no divergence, no non-analyticity')
    ax.legend()
    ax.grid(alpha=0.3)
    axins = ax.inset_axes([0.55, 0.55, 0.42, 0.4])
    prs = [p for p in range(2, 50) if is_prime(p)]
    dstars = [dstar(p) for p in prs]
    axins.plot(prs, dstars, 'o', ms=3, color='dimgray')
    xs = np.linspace(2, 50, 200)
    axins.plot(xs, 1 + 2.5 / np.log(xs), '-', color='crimson', lw=1,
               label=r'$1 + 2.5/\ln p$ (indicative fit)')
    axins.set_xlabel('p', fontsize=8)
    axins.set_ylabel(r'$d^*(p)$, 5%', fontsize=8)
    axins.tick_params(labelsize=7)
    axins.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig('charts/chart16_correction_crossover.png', dpi=150)
    plt.close(fig)

# ------------------------------------------------------------ main

if __name__ == '__main__':
    # sanity: log-space evaluator vs exact integers on feasible cases
    for n, d in [(2, 2), (3, 2), (5, 2), (6, 2), (2, 3), (3, 3), (6, 3), (12, 2)]:
        exact = log10_bigint(formula_count(n, d, 2))
        approx = log10_S(n, d, 2)
        assert abs(exact - approx) < 1e-9, (n, d, exact, approx)
    print('log-space evaluator matches exact integers on 8 cases')

    chart12(); print('chart12 done')
    chart13(); print('chart13 done')
    chart14(); print('chart14 done')
    rows = chart15(); print('chart15 done; inversion dimensions:')
    for p, m, pr in rows:
        print(f'  p={p}: measured d_c = {m:.2f}, predicted = {pr:.2f}, p*ln2 = {p*math.log(2):.2f}')
    chart16(); print('chart16 done')
