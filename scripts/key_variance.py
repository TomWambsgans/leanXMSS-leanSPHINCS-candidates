#!/usr/bin/env python3
"""How much the security of one key varies around the mean, forest vs FORS, each at its own cover lifetime.

The cover attack (forest_attack.py, fors_security.py) and the proofs bound the forgery probability averaged
over the signer's randomness. A given key has one realized history: the number of signatures of each
instance and what they revealed. Its per-query cover rate, in units of 2^-127 per digest query, is

    Y = 2^(127 - h) * sum over the 2^b kept instances of c_i,

c_i the probability that a uniform digest landing on instance i has its whole FTS opening revealed by the
earlier signatures of instance i. E[Y] = 1 at the cover lifetime. This script gives the law of Y across keys.
  FORS:   c = prod over the k trees of D_t / 2^a, D_t the distinct revealed leaves of tree t (exact).
  forest: c = prod over the 8 coordinates of phi, phi the covered fraction of one coordinate (forest_attack.py
          `pools`: per signature a uniform leaf, and in each of the 2 subtrees a uniform WOTS key and table
          entry; a key reveals the componentwise max of its codewords). Monte Carlo, pinned to the exact mean.
The loads are iid Poisson(N / 2^b), so Y is compound Poisson: its variance is exact, its law by FFT.

Usage: python3 scripts/key_variance.py [--h 24] [--b 24,20,14,8] [--samples 100000]   (needs numpy and scipy)
Prints, per kept height b and variant: sd/mean of Y, the share of the variance that comes from the cover
given the load (the rest is the load), and log2(Y / E[Y]) at the quantiles 1e-2, 1e-3 and 1e-6 (how many
bits weaker than the mean the weakest key in 100, 1000, 10^6 is).
"""
import argparse, math, os, sys
from multiprocessing import Pool
import numpy as np
from scipy.stats import poisson

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "formal", "sphincs", "scripts"))
sys.path.insert(0, HERE)
import forest_attack as fa
import forest_certificates as fc
import forest_table as ft
import scheme

D = 0.01                           # log2 grid step
LO = -420.0                        # log2 grid lower end
NG = int((120.0 - LO) / D) + 1
GRID = LO + D * np.arange(NG)
NMAX = 130                         # largest load per instance (the mass beyond is printed)
A = scheme.FORS_HEIGHT

# ---------- the forest: phi for a load n, Monte Carlo ----------
TAB = np.array(ft.table(), dtype=np.int8)
_cnt = np.zeros((5,) * 6, dtype=np.int64)
for w in TAB: _cnt[tuple(w)] += 1
_K = _cnt.astype(np.float64)
for ax in range(6): _K = np.cumsum(_K, axis=ax)
KF = _K.ravel() / 256.0            # K(m) / 256: the table entries below the revealed maximum m
PW = 5 ** np.arange(5, -1, -1)
PF = fa.tree_P(fa.f_of_counts(_cnt), 4, 2, 3)   # exact E[phi | n]


def phi_samples(args):
    """log2 phi of S coordinates of an instance that signed n times."""
    n, S, seed = args
    rng = np.random.default_rng(seed)
    chunk, out, done = max(1, min(S, 400000 // n)), [], 0
    while done < S:
        c = min(chunk, S - done)
        M = np.full((c, 256, 6), -1, dtype=np.int8)          # 16 leaves x 2 subtrees x 8 keys
        rows = np.repeat(np.arange(c), n)
        leaf = rng.integers(16, size=(c, n))
        for j in (0, 1):
            g = (leaf * 16 + j * 8 + rng.integers(8, size=(c, n))).ravel()
            np.maximum.at(M, (rows, g), TAB[rng.integers(256, size=c * n)])
        opened = M[:, :, 0] >= 0
        idx = (np.where(opened[:, :, None], M, 0).astype(np.int64) * PW).sum(axis=2)
        kv = np.where(opened, KF[idx], 0.0).reshape(c, 16, 2, 8).mean(axis=3)
        out.append(kv.prod(axis=2).mean(axis=1))
        done += c
    return n, np.log2(np.concatenate(out))


def selfconv(p, off, times):
    """times-fold convolution of a pmf on a log grid, as (offset, array)."""
    res, base = None, (off, p)
    while times:
        if times & 1:
            res = base if res is None else (res[0] + base[0], np.convolve(res[1], base[1]))
        times >>= 1
        if times: base = (2 * base[0], np.convolve(base[1], base[1]))
    return res


def binned(x, w, step):
    pos = x / step; i = np.floor(pos).astype(np.int64); f = pos - i
    lo = i.min(); p = np.zeros(i.max() - lo + 2)
    np.add.at(p, i - lo, w * (1 - f)); np.add.at(p, i - lo + 1, w * f)
    return lo, p / p.sum()


def forest_cond(samples):
    """n -> (log2 c values, pmf): the 8-fold product of phi, its mean pinned to the exact P[n]^8."""
    with Pool(min(os.cpu_count() or 1, 14)) as pool:
        phis = dict(pool.map(phi_samples, [(n, samples, 1000 + n) for n in range(NMAX, 0, -1)]))
    out = {}
    for n in range(1, NMAX + 1):
        lo, p = binned(phis[n], np.ones(len(phis[n])), D)
        off, q = selfconv(p, lo, 8)
        vals = (off + np.arange(len(q))) * D
        out[n] = (vals + math.log2(PF[n] ** 8 / (q * 2.0 ** vals).sum()), q)
    return out


def fors_cond(k):
    """n -> (log2 c values, pmf): exact occupancy of each tree, k-fold."""
    M, out = 2 ** A, {}
    occ = np.zeros(NMAX + 2); occ[0] = 1.0
    for n in range(1, NMAX + 1):
        d = np.arange(len(occ)); new = occ * d / M
        new[1:] += occ[:-1] * (M - d[:-1]) / M
        occ = new
        dv = np.nonzero(occ > 1e-40)[0]
        lo, p = binned(np.log2(dv / M), occ[dv], 0.001)
        off, q = selfconv(p, lo, k)
        vals = (off + np.arange(len(q))) * 0.001
        keep = q > 1e-60; vals, q = vals[keep], q[keep]
        out[n] = (vals + math.log2((1 - (1 - 2.0 ** -A) ** n) ** k / (q * 2.0 ** vals).sum()), q)
    return out


# ---------- the law of Y ----------
def levy(cond, h, b, lam):
    """The intensity of the instances' contributions on the log2 grid, and the mass of loads above NMAX."""
    nu, pn = np.zeros(NG), poisson.pmf(np.arange(NMAX + 1), lam)
    for n in range(1, NMAX + 1):
        vals, q = cond[n]
        pos = (vals + 127 - h - LO) / D; i = np.floor(pos).astype(np.int64); f = pos - i
        w = q * 2.0 ** b * pn[n]
        np.add.at(nu, i, w * (1 - f)); np.add.at(nu, i + 1, w * f)
    return nu, poisson.sf(NMAX, lam) * 2.0 ** b


def law(nu, y0=1e-3):
    """FFT law of Y: contributions below y0 as a Gaussian, the others compound Poisson on a linear grid."""
    y = 2.0 ** GRID; small = y < y0
    mu_s, var_s = (nu[small] * y[small]).sum(), (nu[small] * y[small] ** 2).sum()
    dy = min(2e-4, math.sqrt((nu * y * y).sum()) / 400)
    sf = np.cumsum(nu[::-1])[::-1]
    ymax = 4 * max(2.0, 2.0 ** GRID[min(np.searchsorted(-sf, -1e-9), NG - 1)])
    L = 1 << int(math.ceil(math.log2(ymax / dy)))
    pos, w = y[~small] / dy, nu[~small]
    keep = pos < L - 2; pos, w = pos[keep], w[keep]
    i = np.floor(pos).astype(np.int64); f = pos - i
    g = np.zeros(L); np.add.at(g, i, w * (1 - f)); np.add.at(g, i + 1, w * f)
    om = 2 * np.pi * np.fft.rfftfreq(L)
    pmf = np.clip(np.fft.irfft(np.exp(np.fft.rfft(g) - g.sum() - 0.5 * var_s * (om / dy) ** 2), L), 0, None)
    hw = int(10 * math.sqrt(var_s) / dy) + 1
    pmf = np.roll(pmf, hw)
    return mu_s + (np.arange(L) - hw) * dy, pmf / pmf.sum()


def report(name, cond, h, b, N):
    lam = N / 2.0 ** b
    nu, beyond = levy(cond, h, b, lam)
    y = 2.0 ** GRID
    mean, var = (nu * y).sum(), (nu * y * y).sum()
    grid, pmf = law(nu)
    sf = np.cumsum(pmf[::-1])[::-1]
    qs = [math.log2(grid[min(np.searchsorted(-sf, -q), len(grid) - 1)] / mean) for q in (1e-2, 1e-3, 1e-6)]
    pn = poisson.pmf(np.arange(NMAX + 1), lam)
    e1 = np.array([0] + [(2.0 ** cond[n][0] * cond[n][1]).sum() for n in range(1, NMAX + 1)])
    e2 = np.array([0] + [(2.0 ** (2 * cond[n][0]) * cond[n][1]).sum() for n in range(1, NMAX + 1)])
    vl, vc = (pn * e1 ** 2).sum(), (pn * (e2 - e1 ** 2)).sum()
    print(f"{b:>3} {name:7s} {N:12.4g} {mean:6.3f} {math.sqrt(var) / mean:8.3f} {vc / (vl + vc):7.0%} "
          + " ".join(f"{x:+7.2f}" for x in qs) + f"   {beyond:.0e}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--h", type=int, default=24)
    ap.add_argument("--b", default=None, help="kept heights, comma-separated (default: h,20,14,8)")
    ap.add_argument("--samples", type=int, default=100000, help="Monte Carlo coordinates per load (forest)")
    args = ap.parse_args()
    h = args.h
    bs = [int(x) for x in args.b.split(",")] if args.b else [h, 20, 14, 8]
    forest, fors = forest_cond(args.samples), fors_cond(scheme.FORS_TREES)
    print(f"h = {h}; log2(Y / E[Y]) at the quantiles, each variant at its own cover lifetime N")
    print("  b variant            N   E[Y]  sd/mean  cover   1e-2    1e-3    1e-6   beyond NMAX")
    for b in bs:
        report("forest", forest, h, b, fc.attack(h, "pruned", b))
        report("FORS", fors, h, b, 2.0 ** scheme.fors_log2_lifetime(h, b, A, scheme.FORS_TREES))


if __name__ == "__main__":
    main()
