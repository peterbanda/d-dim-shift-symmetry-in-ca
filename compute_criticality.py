#!/usr/bin/env python3
"""
Investigate criticality in shift-symmetry as a function of dimension d.
Questions:
  1. Does d being prime matter?
  2. Is there a "critical dimension" where behavior changes qualitatively?
  3. How does the correction structure evolve with d?
"""

import math
import itertools
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np

# ── Reuse core functions from compute_charts.py ─────────────────────

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
    if r < 0 or r > d: return 0
    if r == 0 or r == d: return 1
    if r > d - r: r = d - r
    result = 1
    for i in range(r):
        result = result * (p**(d - i) - 1) // (p**(i + 1) - 1)
    return result

def r_d_coeff(p, v, d):
    if v == 0: return 1
    return p ** (v * (v - 1) // 2) * gaussian_binomial(d, v, p)

def count_shift_symmetric(n, d, sigma=2):
    primes = prime_factors(n)
    k = len(primes)
    if k == 0: return 0
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
    count = count_shift_symmetric(n, d, sigma)
    if count <= 0: return float('-inf')
    return math.log10(count) - (n ** d) * math.log10(sigma)

def individual_terms_prime_n(p, d, sigma=2):
    """For prime n=p, compute each term T_r in the formula separately.
    Returns list of (r, sign*coeff, exponent, term_value) for r=1..d.
    """
    terms = []
    for r in range(1, d + 1):
        sign = (-1) ** (r + 1)
        coeff = r_d_coeff(p, r, d)
        exponent = p ** (d - r)
        value = sign * coeff * (sigma ** exponent)
        terms.append((r, sign * coeff, exponent, value))
    return terms

# ── Analysis 1: Correction ratio |T_2/T_1| vs d ────────────────────

def chart_correction_ratio(save_path):
    """
    For prime n = 2, 3, 5: compute |T_2|/|T_1| as function of d.
    This reveals the 'upper critical dimension' where the single-term
    approximation becomes valid.
    """
    print("=" * 60)
    print("ANALYSIS: Correction ratio |T₂/T₁| vs dimension d")
    print("=" * 60)

    primes_n = [2, 3, 5]
    colors = ['steelblue', 'darkorange', 'forestgreen']
    max_d = {2: 12, 3: 8, 5: 6}

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5.5))

    for p, color in zip(primes_n, colors):
        ds = list(range(2, max_d[p] + 1))
        ratios = []
        for d in ds:
            terms = individual_terms_prime_n(p, d)
            T1 = abs(terms[0][3])
            T2 = abs(terms[1][3]) if len(terms) > 1 else 0
            ratio = T2 / T1 if T1 > 0 else 0
            ratios.append(ratio)
            print(f"  n={p}, d={d}: |T₂/T₁| = {ratio:.6e}, "
                  f"T₁ coeff={terms[0][1]}, T₂ coeff={terms[1][1] if len(terms)>1 else 0}")

        ds_arr = np.array(ds)
        r_arr = np.array(ratios)

        # Left: linear scale (shows the bump)
        ax1.plot(ds_arr, r_arr, '-o', color=color, markersize=6,
                 label=f'n = {p}', linewidth=2)

        # Right: log scale (shows the decay)
        valid = r_arr > 0
        ax2.plot(ds_arr[valid], r_arr[valid], '-o', color=color, markersize=6,
                 label=f'n = {p}', linewidth=2)

    # Mark the "critical" threshold
    ax1.axhline(y=0.05, color='red', linestyle='--', alpha=0.5, label='5% threshold')
    ax2.axhline(y=0.05, color='red', linestyle='--', alpha=0.5, label='5% threshold')

    ax1.set_xlabel('Dimension d', fontsize=12)
    ax1.set_ylabel('|T₂| / |T₁|', fontsize=12)
    ax1.set_title('Correction Ratio (linear scale)', fontsize=13)
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)
    ax1.xaxis.set_major_locator(mticker.MaxNLocator(integer=True))
    ax1.set_ylim(-0.02, 0.6)

    ax2.set_xlabel('Dimension d', fontsize=12)
    ax2.set_ylabel('|T₂| / |T₁|  (log scale)', fontsize=12)
    ax2.set_title('Correction Ratio (log scale)', fontsize=13)
    ax2.set_yscale('log')
    ax2.legend(fontsize=10)
    ax2.grid(True, alpha=0.3)
    ax2.xaxis.set_major_locator(mticker.MaxNLocator(integer=True))

    fig.suptitle('When Does the Single-Term Approximation Become Valid?',
                 fontsize=14, fontweight='bold', y=1.01)
    fig.tight_layout()
    fig.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Analysis 2: P vs d with prime d highlighted ─────────────────────

def chart_prime_d_test(save_path):
    """
    For n=2, plot log10(P) vs d from d=1 to 15.
    Highlight prime d vs composite d. If prime d matters,
    we'd see anomalies at d = 2, 3, 5, 7, 11, 13.
    """
    print("\n" + "=" * 60)
    print("ANALYSIS: Does prime d matter? (n=2, |Σ|=2)")
    print("=" * 60)

    n = 2
    ds = list(range(1, 16))
    log_probs = []
    for d in ds:
        lp = log10_probability(n, d)
        log_probs.append(lp)
        prime_tag = " ← PRIME d" if is_prime(d) else ""
        print(f"  d={d:2d}: log₁₀(P) = {lp:12.4f}{prime_tag}")

    ds_arr = np.array(ds)
    lp_arr = np.array(log_probs)
    prime_d = np.array([is_prime(d) for d in ds])
    comp_d = ~prime_d

    # Compute successive ratios to detect anomalies
    print("\n  Successive ratios Δ(d+1)/Δ(d):")
    deltas = np.diff(lp_arr)
    for i in range(len(deltas) - 1):
        if deltas[i] != 0:
            ratio = deltas[i + 1] / deltas[i]
            d_from = ds[i + 1]
            prime_tag = " ← PRIME" if is_prime(d_from) else ""
            print(f"    d={d_from:2d}→{d_from+1}: ratio = {ratio:.4f}{prime_tag}")

    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 9), height_ratios=[2, 1])

    # Top: log10(P) vs d
    ax1.plot(ds_arr, lp_arr, '-', color='gray', alpha=0.5, linewidth=1)
    ax1.scatter(ds_arr[comp_d], lp_arr[comp_d], c='steelblue', s=50,
                label='Composite d', zorder=3)
    ax1.scatter(ds_arr[prime_d], lp_arr[prime_d], c='crimson', s=80,
                label='Prime d', zorder=4, marker='D', edgecolors='black', linewidths=0.5)

    ax1.set_xlabel('Dimension d', fontsize=12)
    ax1.set_ylabel('log₁₀(P)', fontsize=12)
    ax1.set_title('Shift-Symmetry Probability vs Dimension for n=2  (|Σ|=2)\n'
                  'Does prime d cause spikes or dips?', fontsize=13)
    ax1.legend(fontsize=11)
    ax1.grid(True, alpha=0.3)
    ax1.xaxis.set_major_locator(mticker.MaxNLocator(integer=True))

    # Bottom: successive ratio of differences (should be ≈ 2 if smooth)
    if len(deltas) > 1:
        ratios = []
        d_labels = []
        colors_bar = []
        for i in range(len(deltas) - 1):
            if deltas[i] != 0:
                ratios.append(deltas[i + 1] / deltas[i])
                d_labels.append(ds[i + 1])
                colors_bar.append('crimson' if is_prime(ds[i + 1]) else 'steelblue')

        ax2.bar(range(len(ratios)), ratios, color=colors_bar, alpha=0.7, edgecolor='black',
                linewidth=0.5)
        ax2.set_xticks(range(len(ratios)))
        ax2.set_xticklabels([str(d) for d in d_labels])
        ax2.axhline(y=2.0, color='green', linestyle='--', alpha=0.7,
                    label=f'Expected ratio (n={n})')
        ax2.set_xlabel('Dimension d', fontsize=12)
        ax2.set_ylabel('Δ(d+1) / Δ(d)', fontsize=12)
        ax2.set_title('Smoothness test: ratio of consecutive log₁₀(P) differences\n'
                      '(should approach n=2 if no criticality)', fontsize=11)
        ax2.legend(fontsize=10)
        ax2.grid(True, alpha=0.3, axis='y')

    fig.tight_layout()
    fig.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Analysis 3: Zigzag amplitude vs d ───────────────────────────────

def chart_zigzag_amplitude(save_path):
    """
    The 'zigzag amplitude' = gap between prime and composite P values.
    Compare P(prime) / P(composite neighbor) across dimensions.
    Uses specific pairs: (n=5 prime, n=6 composite) and (n=11, n=12).
    """
    print("\n" + "=" * 60)
    print("ANALYSIS: Prime-composite gap amplification with dimension")
    print("=" * 60)

    pairs = [(5, 6), (7, 8), (11, 12)]
    colors = ['steelblue', 'darkorange', 'forestgreen']
    max_d = {(5, 6): 5, (7, 8): 4, (11, 12): 3}

    fig, ax = plt.subplots(figsize=(10, 6))

    for (p_n, c_n), color in zip(pairs, colors):
        ds = list(range(2, max_d[(p_n, c_n)] + 1))
        gaps = []
        for d in ds:
            lp_prime = log10_probability(p_n, d)
            lp_comp = log10_probability(c_n, d)
            gap = lp_comp - lp_prime  # positive = composite has higher P
            gaps.append(gap)
            print(f"  d={d}: P({c_n})/P({p_n}) in log₁₀ = {gap:.2f}"
                  f"  [P({p_n})=10^{lp_prime:.1f}, P({c_n})=10^{lp_comp:.1f}]")

        ax.plot(ds, gaps, '-o', color=color, markersize=8, linewidth=2,
                label=f'n={c_n} (comp) vs n={p_n} (prime)')

    ax.set_xlabel('Dimension d', fontsize=12)
    ax.set_ylabel('log₁₀( P_composite / P_prime )', fontsize=12)
    ax.set_title('Prime-Composite Probability Gap vs Dimension\n'
                 'How much more likely is shift-symmetry for composite n?',
                 fontsize=13)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.xaxis.set_major_locator(mticker.MaxNLocator(integer=True))

    fig.tight_layout()
    fig.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Analysis 4: Full term decomposition ─────────────────────────────

def print_term_decomposition():
    """Print the individual terms for small cases to show structure."""
    print("\n" + "=" * 60)
    print("TERM DECOMPOSITION for prime n=2, |Σ|=2")
    print("=" * 60)
    p = 2
    for d in range(1, 8):
        terms = individual_terms_prime_n(p, d)
        total = sum(t[3] for t in terms)
        N = p ** d
        total_configs = 2 ** N
        prob = total / total_configs
        prime_tag = "  ← PRIME d" if is_prime(d) else ""

        print(f"\n  d={d}{prime_tag}:  N={N} cells,  |Σ|^N = 2^{N}")
        for r, sc, exp, val in terms:
            pct = abs(val) / abs(terms[0][3]) * 100 if terms[0][3] != 0 else 0
            print(f"    T_{r}: ({sc:+d}) × 2^{exp} = {val:+d}  "
                  f"[{pct:.1f}% of |T₁|]")
        print(f"    Total |S| = {total},  P = {prob:.6e}")

# ── Main ─────────────────────────────────────────────────────────────

if __name__ == '__main__':
    base = 'charts'  # run from the project root

    print_term_decomposition()
    chart_correction_ratio(f'{base}/chart5_correction_ratio.png')
    chart_prime_d_test(f'{base}/chart6_prime_d_test.png')
    chart_zigzag_amplitude(f'{base}/chart7_zigzag_amplitude.png')

    print("\n" + "=" * 60)
    print("All criticality analyses complete.")
    print("=" * 60)
