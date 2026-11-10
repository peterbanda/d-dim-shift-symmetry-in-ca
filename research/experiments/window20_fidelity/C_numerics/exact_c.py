"""(c) probability form, composite branch, EXACT with Python integers:
for 1 <= d <= dc(p) - 20:  |S_{p^d}| * s^{(p+1)^d} < |S_{(p+1)^d}| * s^{p^d}
(<=> probUnif p d s < probUnif (p+1) d s, s > 0)."""
import sys, time
sys.path.insert(0, '.')
import paper_side as P
import lean_side as L
import mpmath as mp

def poly_paper(n, d):
    out = {}
    for c, e in P.S_terms(n, d):
        out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}

def poly_lean(n, d):
    return {e: c for e, c in L.enumerationRHS_terms(n, d).items() if c}

def evalpoly(poly, s):
    if s == 2:
        return sum((c << e) if c > 0 else -((-c) << e) for e, c in poly.items())
    return sum(c * s ** e for e, c in poly.items())

def window_i_exact(p, d):
    return d >= 1 and (p + 1) ** (d + 20) <= 2 * (p - 1) * p ** (d + 19)

cases = [(p, d, s) for p in (37, 41, 43, 47) for d in (1, 2, 3, 4) for s in (2, 3)]
cases += [(p, 5, 2) for p in (41, 43, 47)]
ok = bad = 0
for (p, d, s) in cases:
    t = time.time()
    assert window_i_exact(p, d) and L.win_i_margin(p, d) > 0, (p, d)
    pp, pl = poly_paper(p, d), poly_lean(p, d)
    qp, ql = poly_paper(p + 1, d), poly_lean(p + 1, d)
    assert pp == pl and qp == ql
    Sp, Sq = evalpoly(pl, s), evalpoly(ql, s)
    if s == 2:
        lhs, rhs = Sp << ((p + 1) ** d), Sq << (p ** d)
    else:
        lhs, rhs = Sp * s ** ((p + 1) ** d), Sq * s ** (p ** d)
    res = lhs < rhs
    ok += res; bad += (not res)
    # margin: log_s(rhs/lhs) approx via bit lengths, and phi(d) for comparison
    margin_bits = rhs.bit_length() - lhs.bit_length()
    phi = (2 * (p - 1) * p ** (d - 1) - (p + 1) ** d) // 2
    print(f"p={p} d={d} sigma={s}: |S_p^d|*s^((p+1)^d) < |S_(p+1)^d|*s^(p^d): {res}; "
          f"bitlen(rhs)-bitlen(lhs)={margin_bits} (phi(d)*log2(s)={mp.nstr(phi*mp.log(s,2),8)}); "
          f"sizes {lhs.bit_length()}/{rhs.bit_length()} bits; {time.time()-t:.1f}s", flush=True)
print(f"(c) exact composite-branch checks: {ok} true, {bad} false, of {len(cases)}")
