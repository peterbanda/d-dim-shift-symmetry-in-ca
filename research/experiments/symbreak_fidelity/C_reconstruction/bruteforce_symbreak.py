#!/usr/bin/env python3
"""Independent brute force for the Cor 8.2 clause (C_reconstruction).

Clause: "every pattern-recognition or image-processing task whose required
output breaks a symmetry of some admissible input" is unsolvable by
translation-equivariant CA on Z_n^d.

Conventions (paper Def 2.1): (tau_v s)(u) = s(u+v); Stab(s) = {v : tau_v s = s}.
y "breaks a symmetry of x"  <=>  exists v in Stab(x) with v not in Stab(y)
                             <=>  NOT (Stab(x) subset Stab(y)).
An equivariant global map on a finite abelian group G is Phi(s)(u) = phi(s(u+.))
for a function phi : Sigma^G -> Sigma (Def 2.3 with offsets = all of G).

Exact integer arithmetic only. Alphabet size 2. Deterministic (fixed seed).
Run: python3 -I bruteforce_symbreak.py
"""
import itertools
import random
import sys
import time

SEED = 20261027


def make_group(dims):
    elems = list(itertools.product(*[range(n) for n in dims]))
    idx = {e: i for i, e in enumerate(elems)}
    add = [[idx[tuple((a + b) % n for a, b, n in zip(x, y, dims))] for y in elems]
           for x in elems]
    return elems, add


class Torus:
    def __init__(self, dims):
        self.dims = dims
        self.elems, self.add = make_group(dims)
        m = self.m = len(self.elems)
        self.nconf = 1 << m
        bit = lambda s, u: (s >> u) & 1
        # shift[v][s] = tau_v s, (tau_v s)(u) = s(u+v)
        self.shift = [[sum(bit(s, self.add[u][v]) << u for u in range(m))
                       for s in range(self.nconf)] for v in range(m)]
        # stab[s] = bitmask over group elements v with tau_v s = s
        self.stab = [sum(1 << v for v in range(m) if self.shift[v][s] == s)
                     for s in range(self.nconf)]
        # pat[s][u] = index of the pattern (s(u+g))_{g in G}; note pattern = tau_u s
        self.pat = [[self.shift[u][s] for u in range(m)] for s in range(self.nconf)]

    def name(self):
        return " x ".join("Z%d" % n for n in self.dims)

    def keeps(self, x, y):
        """Stab(x) subset Stab(y)."""
        return self.stab[x] & ~self.stab[y] == 0

    def phi_table(self, phi):
        """Global map Phi as a list Phi[s], phi given as an int bit-table on 2^m patterns."""
        m = self.m
        return [sum(((phi >> p) & 1) << u for u, p in enumerate(self.pat[s]))
                for s in range(self.nconf)]

    def check_iterates(self, Phi):
        """For every x, follow x, Phi x, Phi^2 x, ... until a repeat; count violations
        of Stab(x) subset Stab(Phi^k x). Returns (violations, max_k_checked)."""
        viol = 0
        maxk = 0
        for x in range(self.nconf):
            seen = {x}
            y = x
            k = 0
            while True:
                y = Phi[y]
                k += 1
                if not self.keeps(x, y):
                    viol += 1
                if y in seen:
                    break
                seen.add(y)
            maxk = max(maxk, k)
        return viol, maxk

    def is_equivariant(self, Phi):
        return all(Phi[self.shift[v][s]] == self.shift[v][Phi[s]]
                   for v in range(self.m) for s in range(self.nconf))

    def one_step_images(self, x):
        """Exact set {Phi(x) : Phi equivariant}: Phi(x)(u) = phi(tau_u x) depends only on
        phi restricted to the orbit of x, so enumerate all phi on that orbit."""
        pats = self.pat[x]
        D = sorted(set(pats))
        out = set()
        for vals in range(1 << len(D)):
            f = {p: (vals >> i) & 1 for i, p in enumerate(D)}
            out.add(sum(f[p] << u for u, p in enumerate(pats)))
        return out

    def pair_counts(self):
        tot = brk = brk_sym = brk_asym = 0
        for x in range(self.nconf):
            for y in range(self.nconf):
                tot += 1
                if not self.keeps(x, y):
                    brk += 1
                    if self.stab[y] != 1:   # Stab(y) != {0}: y shift-symmetric
                        brk_sym += 1
                    else:
                        brk_asym += 1
        return tot, brk, brk_sym, brk_asym


def run_all_maps(T, out):
    """Enumerate ALL 2^(2^m) equivariant maps (feasible for m <= 4)."""
    nmaps = 1 << T.nconf
    viol = 0
    maxk = 0
    reach = [0] * T.nconf          # union over Phi,k>=1 of Phi^k(x), as bitmask over configs
    rev_viol_maps = 0              # maps with some x where Stab(Phi x) not subset Stab(x)
    for phi in range(nmaps):
        Phi = T.phi_table(phi)
        if phi < 64 or phi % 4099 == 0:      # spot-check equivariance definitionally
            assert T.is_equivariant(Phi)
        v, k = T.check_iterates(Phi)
        viol += v
        maxk = max(maxk, k)
        rv = False
        for x in range(T.nconf):
            y = x
            for _ in range(T.nconf + 1):
                y = Phi[y]
                reach[x] |= 1 << y
            if not T.keeps(Phi[x], x):
                rv = True
        rev_viol_maps += rv
    keepset = [sum(1 << y for y in range(T.nconf) if T.keeps(x, y)) for x in range(T.nconf)]
    sharp = all(reach[x] == keepset[x] for x in range(T.nconf))
    return nmaps, viol, maxk, sharp, rev_viol_maps


def run_orbit_exhaustive(T):
    """One-step exhaustive over all equivariant maps via orbit restriction, + sharpness."""
    viol = 0
    sharp = True
    for x in range(T.nconf):
        imgs = T.one_step_images(x)
        keep = {y for y in range(T.nconf) if T.keeps(x, y)}
        viol += sum(1 for y in imgs if y not in keep)
        if imgs != keep:
            sharp = False
    return viol, sharp


def run_sampled(T, nrand, rng):
    """Iterates for random phi tables plus all rules on <=3-cell neighbourhoods."""
    m = T.m
    viol = 0
    maxk = 0
    count = 0
    # (a) all local rules on every offset set of size 1..3
    for b in (1, 2, 3):
        for offs in itertools.combinations(range(m), b):
            for rule in range(1 << (1 << b)):
                # phi(pattern) = rule(pattern restricted to offsets)
                phi = 0
                for p in range(1 << m):
                    key = sum(((p >> o) & 1) << i for i, o in enumerate(offs))
                    phi |= ((rule >> key) & 1) << p
                Phi = T.phi_table(phi)
                v, k = T.check_iterates(Phi)
                viol += v
                maxk = max(maxk, k)
                count += 1
    # (b) uniformly random full tables
    for _ in range(nrand):
        phi = rng.getrandbits(1 << m)
        Phi = T.phi_table(phi)
        v, k = T.check_iterates(Phi)
        viol += v
        maxk = max(maxk, k)
        count += 1
    return count, viol, maxk


def task_level_Z2(T):
    """Z_2: enumerate EVERY task (adm subset, req relation) and every equivariant map.
    Check: RequiresSymBreak(T) -> no Phi solves T (Solves: forall x in adm, exists k>=0,
    Phi^k x in req x). Also count tasks covered by the symmetry-breaking hypothesis
    but not by the literal 'leave S from an input in S' hypothesis."""
    n = T.nconf
    maps = [T.phi_table(phi) for phi in range(1 << n)]
    reachk = []   # reachk[i][x] = bitmask of {Phi^k x : k >= 0}
    for Phi in maps:
        r = []
        for x in range(n):
            msk = 1 << x
            y = x
            for _ in range(n + 1):
                y = Phi[y]
                msk |= 1 << y
            r.append(msk)
        reachk.append(r)
    keep = [sum(1 << y for y in range(n) if T.keeps(x, y)) for x in range(n)]
    insym = [T.stab[x] != 1 for x in range(n)]
    outS = sum(1 << y for y in range(n) if T.stab[y] == 1)   # asymmetric configs
    bad = covered_sb = covered_leave = sb_not_leave = sb_not_leave_nonempty = 0
    for adm in range(1 << n):
        xs = [x for x in range(n) if (adm >> x) & 1]
        for reqs in itertools.product(range(1 << n), repeat=len(xs)):
            req = dict(zip(xs, reqs))
            sb = any(req[x] & keep[x] == 0 for x in xs)
            leave = any(insym[x] and (req[x] & ~outS) == 0 for x in xs)
            covered_sb += sb
            covered_leave += leave
            if sb and not leave:
                sb_not_leave += 1
                if all(req[x] for x in xs):
                    sb_not_leave_nonempty += 1
            if leave and not sb:
                raise AssertionError("leave-S task not covered by symmetry breaking")
            if sb:
                for r in reachk:
                    if all(r[x] & req[x] for x in xs):
                        bad += 1
    return covered_sb, covered_leave, sb_not_leave, sb_not_leave_nonempty, bad


def main():
    rng = random.Random(SEED)
    t0 = time.process_time()
    print("Cor 8.2 symmetry-breaking clause: independent brute force (sigma = 2)")
    print("seed", SEED)
    print()
    # sanity anchors (CLAUDE.md reference values): |S| = #{s : Stab(s) != {0}}
    for dims, ref in (((2, 2), 8), ((3, 3), 26), ((2, 2, 2), 72)):
        T = Torus(dims)
        got = sum(1 for s in range(T.nconf) if T.stab[s] != 1)
        assert got == ref, (dims, got, ref)
        print("sanity |S_%s| = %d (reference %d)" % (T.name(), got, ref))
    print()
    rows = []
    full = [(2,), (3,), (4,), (2, 2)]
    orbit_only = [(5,), (6,), (2, 2, 2), (3, 3), (2, 4)]
    sampled = [(6,)]
    for dims in full + orbit_only:
        T = Torus(dims)
        tot, brk, brk_sym, brk_asym = T.pair_counts()
        ov, osharp = run_orbit_exhaustive(T)
        line = {"torus": T.name(), "m": T.m, "configs": T.nconf, "pairs": tot,
                "breaking": brk, "breaking_sym": brk_sym, "breaking_asym": brk_asym,
                "orbit_viol": ov, "orbit_sharp": osharp}
        if dims in full:
            nmaps, viol, maxk, sharp, revmaps = run_all_maps(T, sys.stdout)
            line.update(allmaps=nmaps, iter_viol=viol, maxk=maxk, reach_sharp=sharp,
                        reverse_incl_failing_maps=revmaps)
        if dims in sampled:
            cnt, viol, maxk = run_sampled(T, 20000, rng)
            line.update(sampled_maps=cnt, sampled_iter_viol=viol, sampled_maxk=maxk)
        rows.append(line)
        print(line)
        sys.stdout.flush()
    print()
    T2 = Torus((2,))
    csb, cleave, sbnl, sbnl_ne, bad = task_level_Z2(T2)
    print("Z2 task-level (all 17^4 = 83521 (adm,req) tasks x all 16 maps): tasks with RequiresSymBreak =",
          csb, "; with RequiresLeavingS =", cleave, "; SymBreak-but-not-LeavingS =", sbnl,
          "(of which with all accept sets nonempty:", sbnl_ne, ")",
          "; SymBreak tasks solved by some equivariant map =", bad)
    print()
    print("| torus | #configs | #equivariant maps checked | violations | #breaking pairs | "
          "#symmetric-but-breaking pairs |")
    print("|---|---|---|---|---|---|")
    for r in rows:
        if "allmaps" in r:
            mc = "all %d (iterates k<=%d) + one-step orbit-exhaustive" % (r["allmaps"], r["maxk"])
            v = r["iter_viol"] + r["orbit_viol"]
        elif "sampled_maps" in r:
            mc = ("one-step orbit-exhaustive (all 2^64) + %d explicit maps iterated (k<=%d)"
                  % (r["sampled_maps"], r["sampled_maxk"]))
            v = r["orbit_viol"] + r["sampled_iter_viol"]
        else:
            mc = "one-step orbit-exhaustive (all 2^%d)" % r["configs"]
            v = r["orbit_viol"]
        print("| %s | %d | %s | %d | %d | %d |" % (r["torus"], r["configs"], mc, v,
                                                r["breaking"], r["breaking_sym"]))
    print()
    print("reachable set {Phi^k(x)} == {y : Stab x <= Stab y} for every x (sharpness):",
          all(r.get("reach_sharp", True) and r["orbit_sharp"] for r in rows))
    print("CPU seconds: %.1f" % (time.process_time() - t0))


if __name__ == "__main__":
    main()
