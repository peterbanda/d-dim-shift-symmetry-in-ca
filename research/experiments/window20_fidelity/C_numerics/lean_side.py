"""Step 2 -- literal Python transcription of the Lean side:
  ShiftSym.P09.inversionExplicitWindow20Statement / inversionWindow20Statement
  (Shiftsym/Paper/S09_CrossoverLaws_Window20.lean),
  ShiftSym.P09.phi, ShiftSym.P09.dc (Shiftsym/Paper/S09_CrossoverLaws.lean),
  ShiftSym.probUnif, numSS (Shiftsym/Paper/Common.lean),
  enumerationRHS / coeffOf / rdCoeff / gaussBinom / rad (Shiftsym/Statement.lean),
  IsShiftSymmetric / shift / Lat / Config (Shiftsym/Definitions.lean).
Conventions: Real.log x = log|x|, log 0 = 0; x / 0 = 0 in R; Real.logb b x =
log x / log b; Nat subtraction truncates at 0; rpow for positive base.
"""
from functools import lru_cache
from itertools import product
import mpmath as mp

mp.mp.dps = 80


def R(x):                     # cast to ℝ
    return mp.mpf(x)


def nsub(a, b):               # ℕ subtraction
    return a - b if a >= b else 0


def rdiv(a, b):               # real division with x/0 = 0
    return mp.mpf(0) if b == 0 else a / b


def rlog(x):                  # Real.log
    return mp.mpf(0) if x == 0 else mp.log(abs(x))


def logb(b, x):               # Real.logb b x = log x / log b
    return rdiv(rlog(x), rlog(b))


def rpow(x, y):               # Real.rpow, only needed for x > 0 here
    assert x > 0
    return mp.exp(mp.log(x) * y)


# noncomputable def phi (p : ℕ) (x : ℝ) : ℝ :=
#   (1 - 1 / (p : ℝ)) * (p : ℝ) ^ x - (1 / 2) * ((p : ℝ) + 1) ^ x
def phi(p, x):
    P = R(p)
    return (1 - rdiv(R(1), P)) * rpow(P, x) - rdiv(R(1), R(2)) * rpow(P + 1, x)


# noncomputable def dc (p : ℕ) : ℝ :=
#   Real.log (2 - 2 / (p : ℝ)) / Real.log (1 + 1 / (p : ℝ))
def dc(p):
    P = R(p)
    return rdiv(rlog(2 - rdiv(R(2), P)), rlog(1 + rdiv(R(1), P)))


# Real.logb (σ : ℝ) (2 * Real.logb 2 (p : ℝ) * (p : ℝ) ^ (d - 1))
def lhs_i(p, s, d):
    return logb(R(s), 2 * logb(R(2), R(p)) * R(p) ** nsub(d, 1))


# -Real.logb (σ : ℝ) (2 * Real.logb 2 ((p : ℝ) + 1) * ((p : ℝ) + 1) ^ (d - 1))
def rhs_ii(p, s, d):
    return -logb(R(s), 2 * logb(R(2), R(p) + 1) * (R(p) + 1) ** nsub(d, 1))


def antecedents(p, s, d, isprime):
    return isprime(p) and 3 <= p and 2 <= s and 1 <= d


# window antecedents  (d : ℝ) ≤ dc p - 20   and   dc p + 20 ≤ (d : ℝ)
# returned as signed margins (>= 0 means the antecedent holds) for tie detection
def win_i_margin(p, d):
    return (dc(p) - 20) - R(d)


def win_ii_margin(p, d):
    return R(d) - (dc(p) + 20)


def hyp_i_margin(p, s, d, phi_val=None):     # lhs_i < phi p d
    ph = phi(p, R(d)) if phi_val is None else phi_val
    return ph - lhs_i(p, s, d)


def hyp_ii_margin(p, s, d, phi_val=None):    # phi p d < rhs_ii
    ph = phi(p, R(d)) if phi_val is None else phi_val
    return rhs_ii(p, s, d) - ph


# ---------------- numSS / probUnif ----------------
def numSS_brute(n, d, s):
    """Nat.card {s : (Fin d → ZMod n) → Fin σ // ∃ v ≠ 0, shift v s = s}."""
    cells = list(product(range(n), repeat=d))
    idx = {c: i for i, c in enumerate(cells)}
    perms = [[idx[tuple((a + b) % n for a, b in zip(u, v))] for u in cells]
             for v in cells if any(v)]
    cnt = 0
    for cfg in product(range(s), repeat=len(cells)):
        if any(all(cfg[pm[i]] == cfg[i] for i in range(len(cells))) for pm in perms):
            cnt += 1
    return cnt


def prime_factors(n):
    fs, m, q = [], n, 2
    while q * q <= m:
        if m % q == 0:
            fs.append(q)
            while m % q == 0:
                m //= q
        q += 1
    if m > 1:
        fs.append(m)
    return fs


def factorization(h):
    out, m, q = {}, h, 2
    while q * q <= m:
        while m % q == 0:
            out[q] = out.get(q, 0) + 1
            m //= q
        q += 1
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


@lru_cache(maxsize=None)
def gaussBinom(q, dd, r):
    # | _, 0 => 1 | 0, _ + 1 => 0 | dd + 1, r + 1 => gB q dd r + q^(r+1) * gB q dd (r+1)
    if r == 0:
        return 1
    if dd == 0:
        return 0
    return gaussBinom(q, dd - 1, r - 1) + q ** r * gaussBinom(q, dd - 1, r)


def rdCoeff(q, v, dd):        # q ^ (v.choose 2) * gaussBinom q dd v
    return q ** (v * (v - 1) // 2) * gaussBinom(q, dd, v)


def rad(n):
    out = 1
    for q in prime_factors(n):
        out *= q
    return out


def divisors_of_rad_pow(n, dd):
    """((rad n) ^ dd).divisors, generated from the prime factorization."""
    ps = prime_factors(n)
    for es in product(range(dd + 1), repeat=len(ps)):
        h = 1
        for q, e in zip(ps, es):
            h *= q ** e
        yield h


def coeffOf(dd, h):
    fz = factorization(h)
    bigOmega = sum(fz.values())
    c = (-1) ** (1 + bigOmega)
    for q, e in fz.items():
        c *= rdCoeff(q, e, dd)
    return c


def enumerationRHS_terms(n, dd):
    """sum_{h ∈ (rad n ^ dd).divisors.erase 1} coeffOf dd h * σ ^ (n ^ dd / h); returns {exp: coef}."""
    N = n ** dd
    out = {}
    for h in divisors_of_rad_pow(n, dd):
        if h == 1:
            continue
        e = N // h                       # ℕ division (exact here)
        out[e] = out.get(e, 0) + coeffOf(dd, h)
    return out


def enumerationRHS(n, dd, s):
    t = enumerationRHS_terms(n, dd)
    if s == 2:
        return sum((c << e) if c > 0 else -((-c) << e) for e, c in t.items())
    return sum(c * s ** e for e, c in t.items())
