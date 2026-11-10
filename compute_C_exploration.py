#!/usr/bin/env python3
"""
Deep exploration of the upper critical dimension d* and the constant C
in the scaling law d* ~ 1 + C / log(p).

Uses analytical log-space computation to avoid overflow.
"""

import math
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np
from scipy.optimize import curve_fit

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

def gaussian_binomial(d, r, p):
    if r < 0 or r > d: return 0
    if r == 0 or r == d: return 1
    if r > d - r: r = d - r
    result = 1
    for i in range(r):
        result = result * (p**(d - i) - 1) // (p**(i + 1) - 1)
    return result

def log10_correction_ratio(p, d, sigma=2):
    """
    Compute log10(|T_2/T_1|) analytically, avoiding huge exponentials.

    |T_2/T_1| = [p * GB(d,2,p)] / GB(d,1,p) * sigma^{p^{d-2} - p^{d-1}}

    In log10:
    = log10(p * GB(d,2,p) / GB(d,1,p)) - p^{d-2}(p-1) * log10(sigma)
    """
    if d < 2:
        return float('inf')  # only T_1 exists at d=1

    gb1 = gaussian_binomial(d, 1, p)  # (p^d - 1)/(p - 1)
    gb2 = gaussian_binomial(d, 2, p)

    # r_d(p,2) = p^{2(2-1)/2} * gb2 = p * gb2
    # r_d(p,1) = p^{1(1-1)/2} * gb1 = gb1
    coeff_ratio = p * gb2 / gb1

    log_coeff = math.log10(coeff_ratio)
    log_exp = -p**(d - 2) * (p - 1) * math.log10(sigma)

    return log_coeff + log_exp

def find_dstar(p, threshold=0.05, sigma=2, max_d=50):
    """
    Find d* where |T_2/T_1| first drops below threshold.
    Returns interpolated fractional d* for smooth plotting.
    """
    log_thresh = math.log10(threshold)

    # At d=1, there's only T_1, so ratio is 0 (already below).
    # Check d=2 first.
    prev_log_ratio = float('inf')  # d=1 sentinel

    for d in range(2, max_d + 1):
        log_ratio = log10_correction_ratio(p, d, sigma)

        if log_ratio <= log_thresh:
            # Interpolate between d-1 and d
            if prev_log_ratio == float('inf'):
                return float(d)
            # Linear interpolation in log space
            # prev at d-1 was above, current at d is below
            frac = (prev_log_ratio - log_thresh) / (prev_log_ratio - log_ratio)
            return (d - 1) + frac

        prev_log_ratio = log_ratio

    return float(max_d)

# ── Compute for many primes ──────────────────────────────────────────

def compute_all():
    primes = [p for p in range(2, 501) if is_prime(p)]
    print(f"Computing d* for {len(primes)} primes from 2 to {primes[-1]}")
    print()

    thresholds = [0.01, 0.05, 0.10]
    results = {t: [] for t in thresholds}

    for p in primes:
        for t in thresholds:
            ds = find_dstar(p, threshold=t)
            results[t].append(ds)
            if p <= 50 or p % 50 == 1:
                if t == 0.05:
                    print(f"  p={p:4d}: d*(5%) = {ds:.3f}")

    return primes, results

# ── Chart A: d* vs p for multiple thresholds ─────────────────────────

def chart_dstar_vs_p(primes, results, save_path):
    print("\nGenerating Chart A: d* vs p ...")

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(15, 6))
    colors = {0.01: 'forestgreen', 0.05: 'steelblue', 0.10: 'darkorange'}
    labels = {0.01: '1% threshold', 0.05: '5% threshold', 0.10: '10% threshold'}

    p_arr = np.array(primes, dtype=float)

    for t in [0.10, 0.05, 0.01]:
        ds_arr = np.array(results[t])
        ax1.plot(p_arr, ds_arr, 'o-', color=colors[t], markersize=2,
                 linewidth=0.8, label=labels[t], alpha=0.8)

    ax1.set_xlabel('Prime p', fontsize=12)
    ax1.set_ylabel('Critical dimension d*', fontsize=12)
    ax1.set_title('Upper Critical Dimension vs Prime', fontsize=13)
    ax1.legend(fontsize=10)
    ax1.grid(True, alpha=0.3)

    # Right panel: d* vs 1/ln(p) — should be linear if d* = 1 + C/ln(p)
    inv_logp = 1.0 / np.log(p_arr)

    for t in [0.10, 0.05, 0.01]:
        ds_arr = np.array(results[t])
        ax2.plot(inv_logp, ds_arr, 'o', color=colors[t], markersize=3,
                 label=labels[t], alpha=0.7)

        # Fit d* = 1 + C / ln(p), i.e., d* = 1 + C * (1/ln(p))
        # Only fit primes where d* > 2 (otherwise floored)
        mask = ds_arr > 2.01
        if np.sum(mask) >= 2:
            def model(x, C):
                return 1 + C * x
            popt, pcov = curve_fit(model, inv_logp[mask], ds_arr[mask])
            C_fit = popt[0]
            C_err = np.sqrt(pcov[0, 0])

            x_fit = np.linspace(0, inv_logp[0] * 1.05, 100)
            ax2.plot(x_fit, model(x_fit, C_fit), '--', color=colors[t],
                     linewidth=2, label=f'  C = {C_fit:.3f} +/- {C_err:.3f}')
            print(f"  Threshold {t}: C = {C_fit:.4f} +/- {C_err:.4f}")
        else:
            # Fit with intercept free
            def model2(x, a, b):
                return a + b * x
            popt, pcov = curve_fit(model2, inv_logp, ds_arr)
            a_fit, b_fit = popt
            x_fit = np.linspace(0, inv_logp[0] * 1.05, 100)
            ax2.plot(x_fit, model2(x_fit, *popt), '--', color=colors[t],
                     linewidth=2,
                     label=f'  fit: {a_fit:.2f} + {b_fit:.2f}/ln(p)')
            print(f"  Threshold {t}: a={a_fit:.4f}, b={b_fit:.4f}")

    ax2.set_xlabel('1 / ln(p)', fontsize=12)
    ax2.set_ylabel('Critical dimension d*', fontsize=12)
    ax2.set_title('d* vs 1/ln(p) — Testing d* = 1 + C/ln(p)', fontsize=13)
    ax2.legend(fontsize=9)
    ax2.grid(True, alpha=0.3)

    fig.suptitle('Deep Exploration of the Critical Dimension Scaling Constant C',
                 fontsize=14, fontweight='bold', y=1.01)
    fig.tight_layout()
    fig.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Chart B: Correction ratio heatmap ────────────────────────────────

def chart_ratio_heatmap(save_path):
    """Heatmap of log10|T2/T1| across (p, d) space."""
    print("\nGenerating Chart B: Correction ratio heatmap ...")

    primes_small = [p for p in range(2, 52) if is_prime(p)]
    ds = list(range(2, 16))

    data = np.full((len(primes_small), len(ds)), np.nan)

    for i, p in enumerate(primes_small):
        for j, d in enumerate(ds):
            lr = log10_correction_ratio(p, d)
            if lr > 2: lr = 2  # cap for display
            if lr < -20: lr = -20
            data[i, j] = lr

    fig, ax = plt.subplots(figsize=(12, 7))
    im = ax.imshow(data, aspect='auto', cmap='RdYlBu',
                   vmin=-20, vmax=0,
                   extent=[ds[0]-0.5, ds[-1]+0.5, len(primes_small)-0.5, -0.5])

    ax.set_yticks(range(len(primes_small)))
    ax.set_yticklabels([str(p) for p in primes_small])
    ax.set_xticks(ds)
    ax.set_xlabel('Dimension d', fontsize=12)
    ax.set_ylabel('Prime p', fontsize=12)
    ax.set_title('log₁₀|T₂/T₁| — Correction Ratio Landscape\n'
                 'Blue = single-term regime, Red = multi-term regime', fontsize=13)

    # Add contour at threshold
    X, Y = np.meshgrid(ds, range(len(primes_small)))
    ax.contour(X, Y, data, levels=[math.log10(0.05)],
               colors='black', linewidths=2, linestyles='--')

    cbar = fig.colorbar(im, ax=ax, label='log₁₀|T₂/T₁|')
    cbar.ax.axhline(y=math.log10(0.05), color='black', linewidth=2, linestyle='--')

    fig.tight_layout()
    fig.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Chart C: Enhanced correction ratio (many primes) ─────────────────

def chart_correction_many_primes(save_path):
    """Like chart 5 but with many more primes."""
    print("\nGenerating Chart C: Correction ratio for many primes ...")

    prime_configs = [
        (2,  12, 'steelblue'),
        (3,   8, 'darkorange'),
        (5,   6, 'forestgreen'),
        (7,   5, 'crimson'),
        (11,  4, 'purple'),
        (13,  4, 'brown'),
        (17,  3, 'teal'),
        (23,  3, 'olive'),
        (31,  3, 'navy'),
        (47,  3, 'magenta'),
    ]

    fig, ax = plt.subplots(figsize=(12, 6))

    for p, max_d, color in prime_configs:
        ds = list(range(2, max_d + 1))
        log_ratios = [log10_correction_ratio(p, d) for d in ds]

        # Convert to linear ratio for display
        ratios = [10**lr for lr in log_ratios]

        ax.plot(ds, ratios, '-o', color=color, markersize=5,
                label=f'p = {p}', linewidth=1.5, alpha=0.8)

    ax.axhline(y=0.05, color='red', linestyle='--', alpha=0.5,
               linewidth=2, label='5% threshold')
    ax.set_xlabel('Dimension d', fontsize=12)
    ax.set_ylabel('|T₂| / |T₁|', fontsize=12)
    ax.set_title('Correction Ratio |T₂/T₁| vs Dimension for Many Primes', fontsize=13)
    ax.legend(fontsize=9, ncol=2)
    ax.grid(True, alpha=0.3)
    ax.set_ylim(-0.02, 0.6)
    ax.xaxis.set_major_locator(mticker.MaxNLocator(integer=True))

    fig.tight_layout()
    fig.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Chart D: Detailed d* with error analysis ─────────────────────────

def chart_C_fit_detail(primes, results, save_path):
    """Focused chart on extracting C with confidence intervals."""
    print("\nGenerating Chart D: C extraction detail ...")

    t = 0.05
    p_arr = np.array(primes, dtype=float)
    ds_arr = np.array(results[t])
    ln_p = np.log(p_arr)

    fig, axes = plt.subplots(2, 2, figsize=(14, 10))

    # (0,0): d* - 1 vs 1/ln(p)
    ax = axes[0, 0]
    dstar_minus1 = ds_arr - 1
    inv_lnp = 1.0 / ln_p
    ax.plot(inv_lnp, dstar_minus1, 'o', color='steelblue', markersize=3, alpha=0.6)

    # Fit through origin: (d*-1) = C / ln(p) = C * (1/ln(p))
    mask = dstar_minus1 > 1.01  # only points not floored at d*=2
    if np.sum(mask) >= 2:
        C_vals = dstar_minus1[mask] * ln_p[mask]
        C_mean = np.mean(C_vals)
        C_std = np.std(C_vals)
        x_fit = np.linspace(0, max(inv_lnp) * 1.05, 100)
        ax.plot(x_fit, C_mean * x_fit, 'r--', linewidth=2,
                label=f'C = {C_mean:.3f} +/- {C_std:.3f}')
    ax.set_xlabel('1 / ln(p)', fontsize=11)
    ax.set_ylabel('d* - 1', fontsize=11)
    ax.set_title('(d* - 1) vs 1/ln(p)', fontsize=12)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # (0,1): C(p) = (d*-1) * ln(p) vs p
    ax = axes[0, 1]
    C_each = dstar_minus1 * ln_p
    ax.plot(p_arr, C_each, 'o', color='forestgreen', markersize=3, alpha=0.6)
    if np.sum(mask) >= 2:
        ax.axhline(y=C_mean, color='red', linestyle='--', linewidth=2,
                   label=f'Mean C = {C_mean:.3f}')
        ax.axhspan(C_mean - C_std, C_mean + C_std, alpha=0.1, color='red')
    ax.set_xlabel('Prime p', fontsize=11)
    ax.set_ylabel('C(p) = (d* - 1) ln(p)', fontsize=11)
    ax.set_title('Pointwise C(p) — should be constant if scaling holds', fontsize=12)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # (1,0): d* vs p, zoomed into small primes
    ax = axes[1, 0]
    small_mask = p_arr <= 50
    ax.plot(p_arr[small_mask], ds_arr[small_mask], 'o-', color='steelblue',
            markersize=5, linewidth=1)
    # Overlay the fit
    if np.sum(mask) >= 2:
        p_cont = np.linspace(2, 50, 200)
        ax.plot(p_cont, 1 + C_mean / np.log(p_cont), 'r--', linewidth=2,
                label=f'd* = 1 + {C_mean:.2f}/ln(p)')
    ax.set_xlabel('Prime p', fontsize=11)
    ax.set_ylabel('d* (5% threshold)', fontsize=11)
    ax.set_title('d* vs p (small primes, zoomed)', fontsize=12)
    ax.legend(fontsize=10)
    ax.grid(True, alpha=0.3)

    # (1,1): Residuals
    ax = axes[1, 1]
    if np.sum(mask) >= 2:
        predicted = 1 + C_mean / ln_p
        residuals = ds_arr - predicted
        ax.plot(p_arr, residuals, 'o', color='darkorange', markersize=3, alpha=0.6)
        ax.axhline(y=0, color='black', linewidth=0.5)
        ax.set_xlabel('Prime p', fontsize=11)
        ax.set_ylabel('d* - (1 + C/ln p)', fontsize=11)
        ax.set_title(f'Residuals from fit (C={C_mean:.3f})', fontsize=12)
        ax.grid(True, alpha=0.3)

    fig.suptitle('Extracting C from d* = 1 + C / ln(p)  [5% threshold]',
                 fontsize=14, fontweight='bold')
    fig.tight_layout()
    fig.savefig(save_path, dpi=150, bbox_inches='tight')
    plt.close(fig)
    print(f"  Saved: {save_path}")

# ── Main ─────────────────────────────────────────────────────────────

if __name__ == '__main__':
    base = 'charts'  # run from the project root

    primes, results = compute_all()

    chart_dstar_vs_p(primes, results, f'{base}/chart8_dstar_vs_p.png')
    chart_ratio_heatmap(f'{base}/chart9_ratio_heatmap.png')
    chart_correction_many_primes(f'{base}/chart10_correction_many_primes.png')
    chart_C_fit_detail(primes, results, f'{base}/chart11_C_fit_detail.png')

    print("\nAll C-exploration charts generated.")
