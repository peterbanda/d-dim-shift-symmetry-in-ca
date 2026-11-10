#!/usr/bin/env python3
"""
Shift-Symmetric Configurations in d-Dimensional Cellular Automata
Computes exact counts and probabilities, generates charts.
"""

import math
import itertools
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np

# ── Helpers ──────────────────────────────────────────────────────────

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def prime_factors(n):
    """Distinct prime factors of n, sorted."""
    factors = []
    temp, d = n, 2
    while d * d <= temp:
        if temp % d == 0:
            factors.append(d)
            while temp % d == 0: temp //= d
        d += 1
    if temp > 1: factors.append(temp)
    return factors

def gaussian_binomial(d, r, p):
    """[d choose r]_p — Gaussian binomial coefficient (exact integer)."""
    if r < 0 or r > d: return 0
    if r == 0 or r == d: return 1
    if r > d - r: r = d - r
    result = 1
    for i in range(r):
        result = result * (p**(d - i) - 1) // (p**(i + 1) - 1)
    return result

def r_d_coeff(p, v, d):
    """d-dimensional coefficient: r_d(p, v) = p^{v(v-1)/2} * [d choose v]_p."""
    if v == 0: return 1
    return p ** (v * (v - 1) // 2) * gaussian_binomial(d, v, p)

def count_shift_symmetric(n, d, sigma=2):
    """Exact count |S_{n^d}| using the d-dimensional enumeration formula."""
    primes = prime_factors(n)
    k = len(primes)
    if k == 0: return 0  # n=1

    N = n ** d
    total = 0

    for v in itertools.product(range(d + 1), repeat=k):
        if all(vi == 0 for vi in v): continue

        sign = (-1) ** (1 + sum(v))
        coeff = 1
        divisor = 1
        for i in range(k):
            coeff *= r_d_coeff(primes[i], v[i], d)
            divisor *= primes[i] ** v[i]

        exponent = N // divisor
        total += sign * coeff * (sigma ** exponent)

    return total

def log10_probability(n, d, sigma=2):
    """log10(P) = log10(|S|) - n^d * log10(sigma)."""
    count = count_shift_symmetric(n, d, sigma)
    if count <= 0: return float('-inf')
    return math.log10(count) - (n ** d) * math.log10(sigma)

# ── Verification ─────────────────────────────────────────────────────

def verify():
    """Check formulas against known values from the paper."""
    print("=" * 60)
    print("VERIFICATION against Banda et al. (2019)")
    print("=" * 60)

    # d=2, |Σ|=2
    tests_d2 = [
        (2, 2, 8,     0.5),
        (3, 2, 26,    None),
        (5, 2, 182,   None),
    ]
    for n, d, expected_count, expected_prob in tests_d2:
        count = count_shift_symmetric(n, d)
        prob = count / (2 ** (n**d))
        status = "✓" if count == expected_count else "✗"
        print(f"  n={n}, d={d}: |S|={count} (expected {expected_count}) {status}  P={prob:.6e}")

    # n=10, d=2: paper says P ≈ 2.7 × 10^{-15}
    count_10 = count_shift_symmetric(10, 2)
    prob_10 = count_10 / (2 ** 100)
    print(f"  n=10, d=2: |S|={count_10}  P={prob_10:.4e} (paper: ~2.7e-15)")

    # d=3 cross-checks
    count_2_3 = count_shift_symmetric(2, 3)
    print(f"  n=2, d=3: |S|={count_2_3} (expected 72)  {'✓' if count_2_3==72 else '✗'}")

    count_3_3 = count_shift_symmetric(3, 3)
    print(f"  n=3, d=3: |S|={count_3_3} (expected 6398)  {'✓' if count_3_3==6398 else '✗'}")

    # Verify Gaussian binomials
    print("\nGaussian binomial spot checks:")
    assert gaussian_binomial(3, 1, 2) == 7,  f"[3,1]_2 = {gaussian_binomial(3,1,2)}"
    assert gaussian_binomial(3, 2, 2) == 7,  f"[3,2]_2 = {gaussian_binomial(3,2,2)}"
    assert gaussian_binomial(4, 2, 2) == 35, f"[4,2]_2 = {gaussian_binomial(4,2,2)}"
    assert gaussian_binomial(3, 1, 3) == 13, f"[3,1]_3 = {gaussian_binomial(3,1,3)}"
    print("  All Gaussian binomial checks passed ✓")

    # Verify r_d coefficients for d=2
    assert r_d_coeff(2, 0, 2) == 1
    assert r_d_coeff(2, 1, 2) == 3   # p+1 = 3
    assert r_d_coeff(2, 2, 2) == 2   # p = 2
    assert r_d_coeff(3, 1, 2) == 4   # p+1 = 4
    assert r_d_coeff(3, 2, 2) == 3   # p = 3
    print("  All r_d coefficient checks (d=2) passed ✓")

    # Verify r_d coefficients for d=3
    assert r_d_coeff(2, 1, 3) == 7
    assert r_d_coeff(2, 2, 3) == 14  # 2 * 7
    assert r_d_coeff(2, 3, 3) == 8   # 2^3
    assert r_d_coeff(3, 1, 3) == 13
    assert r_d_coeff(3, 2, 3) == 39  # 3 * 13
    assert r_d_coeff(3, 3, 3) == 27  # 3^3
    print("  All r_d coefficient checks (d=3) passed ✓")

    print()

# ── Chart 1: Prime dips in probability (d=2) ─────────────────────────

def chart1_prime_dips_d2(ns, save_path):
    """log10(P) vs n for d=2, highlighting primes."""
    print("Computing Chart 1: Prime dips (d=2) ...")
    d = 2
    log_probs = []
    for n in ns:
        lp = log10_probability(n, d)
        log_probs.append(lp)
        if n % 10 == 0:
            print(f"  n={n}: log10(P) = {lp:.2f}")

    prime_mask = [is_prime(n) for n in ns]
    comp_mask  = [not p for p in prime_mask]

    fig, ax = plt.subplots(figsize=(12, 5))
    ns_arr = np.array(ns)
    lp_arr = np.array(log_probs)

    ax.plot(ns_arr, lp_arr, '-', color='gray', alpha=0.4, linewidth=0.8)
    ax.scatter(ns_arr[comp_mask], lp_arr[comp_mask], c='steelblue', s=18,
               label='Composite n', zorder=3, alpha=0.7)
    ax.scatter(ns_arr[prime_mask], lp_arr[prime_mask], c='crimson', s=30,
               label='Prime n', zorder=4, marker='D')

    ax.set_xlabel('Lattice size n', fontsize=12)
    ax.set_ylabel('log$_{10}$(P)', fontsize=12)
    ax.set_title('Probability of Shift-Symmetry on $\\mathbb{Z}_n^2$  (|$\\Sigma$|=2)',
                 fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(save_path, dpi=150)
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Chart 2: Dimension comparison ────────────────────────────────────

def chart2_dimension_comparison(save_path):
    """log10(P) vs n for d=2,3,4 side by side."""
    print("Computing Chart 2: Dimension comparison ...")
    configs = [
        (2, range(2, 51), 'steelblue'),
        (3, range(2, 21), 'darkorange'),
        (4, range(2, 11), 'forestgreen'),
    ]

    fig, ax = plt.subplots(figsize=(10, 6))
    for d, ns, color in configs:
        log_probs = []
        x_vals = []
        for n in ns:
            lp = log10_probability(n, d)
            log_probs.append(lp)
            x_vals.append(n)
            print(f"  d={d}, n={n}: log10(P) = {lp:.2f}")

        x_arr = np.array(x_vals)
        lp_arr = np.array(log_probs)
        prime_mask = np.array([is_prime(n) for n in x_vals])

        ax.plot(x_arr, lp_arr, '-o', color=color, markersize=4, alpha=0.7,
                label=f'd = {d}')
        ax.scatter(x_arr[prime_mask], lp_arr[prime_mask], c='crimson', s=40,
                   zorder=5, marker='D', edgecolors='black', linewidths=0.5)

    ax.set_xlabel('Lattice size n', fontsize=12)
    ax.set_ylabel('log$_{10}$(P)', fontsize=12)
    ax.set_title('Shift-Symmetry Probability Across Dimensions  (|$\\Sigma$|=2)',
                 fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)

    # Add annotation for prime markers
    ax.scatter([], [], c='crimson', marker='D', edgecolors='black',
               linewidths=0.5, label='Prime n (all dims)')
    ax.legend(fontsize=10)

    fig.tight_layout()
    fig.savefig(save_path, dpi=150)
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Chart 3: Symmetry count (d=2) ───────────────────────────────────

def chart3_count_d2(ns, save_path):
    """log10(|S|) vs n for d=2 with paper's Figure 6 style."""
    print("Computing Chart 3: Count |S| (d=2) ...")
    d = 2
    log_counts = []
    for n in ns:
        count = count_shift_symmetric(n, d)
        lc = math.log10(count) if count > 0 else 0
        log_counts.append(lc)

    prime_mask = np.array([is_prime(n) for n in ns])
    comp_mask = ~prime_mask
    ns_arr = np.array(ns)
    lc_arr = np.array(log_counts)

    fig, ax = plt.subplots(figsize=(12, 5))
    ax.plot(ns_arr, lc_arr, '-', color='gray', alpha=0.4, linewidth=0.8)
    ax.scatter(ns_arr[comp_mask], lc_arr[comp_mask], c='steelblue', s=18,
               label='Composite n', zorder=3, alpha=0.7)
    ax.scatter(ns_arr[prime_mask], lc_arr[prime_mask], c='crimson', s=30,
               label='Prime n (local minima)', zorder=4, marker='D')

    ax.set_xlabel('Lattice size n', fontsize=12)
    ax.set_ylabel('log$_{10}$( |S$_{n \\times n}$| )', fontsize=12)
    ax.set_title('Number of Shift-Symmetric Configs on $\\mathbb{Z}_n^2$  (|$\\Sigma$|=2)',
                 fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    fig.tight_layout()
    fig.savefig(save_path, dpi=150)
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Chart 4: Scaling with dimension for fixed prime n ────────────────

def chart4_dimension_scaling(save_path):
    """For prime n=2,3,5, log10(P) vs dimension d."""
    print("Computing Chart 4: Dimension scaling ...")
    primes_to_plot = [2, 3, 5]
    colors = ['steelblue', 'darkorange', 'forestgreen']
    max_d = {2: 10, 3: 7, 5: 5}  # limit d to keep computation tractable

    fig, ax = plt.subplots(figsize=(9, 6))
    for p, color in zip(primes_to_plot, colors):
        ds = list(range(1, max_d[p] + 1))
        log_probs = []
        for d in ds:
            lp = log10_probability(p, d)
            log_probs.append(lp)
            print(f"  n={p}, d={d}: log10(P) = {lp:.2f}")
        ax.plot(ds, log_probs, '-o', color=color, markersize=6,
                label=f'n = {p} (prime)', linewidth=2)

    ax.set_xlabel('Dimension d', fontsize=12)
    ax.set_ylabel('log$_{10}$(P)', fontsize=12)
    ax.set_title('Shift-Symmetry Probability vs Dimension  (|$\\Sigma$|=2, prime n)',
                 fontsize=14)
    ax.legend(fontsize=11)
    ax.grid(True, alpha=0.3)
    ax.xaxis.set_major_locator(mticker.MaxNLocator(integer=True))
    fig.tight_layout()
    fig.savefig(save_path, dpi=150)
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Main ─────────────────────────────────────────────────────────────

if __name__ == '__main__':
    verify()

    base = 'charts'  # run from the project root
    ns_100 = list(range(2, 101))

    chart1_prime_dips_d2(ns_100, f'{base}/chart1_probability_d2.png')
    chart3_count_d2(ns_100, f'{base}/chart3_count_d2.png')
    chart2_dimension_comparison(f'{base}/chart2_dimension_comparison.png')
    chart4_dimension_scaling(f'{base}/chart4_dimension_scaling.png')

    print("\nAll charts generated successfully.")
