"""Unified cost / security model (see research/README.md) for n = 16 hypertree signatures with different bottom few-time schemes.

Units: SHA-256 compressions, FIPS 205 SHA2 layout with the PK.seed block precomputed:
PRF, F, H = 1; T_l = ceil((22 + 16 l + 9) / 64); one message-hash grinding attempt = 7 (PRF_msg + H_msg);
verifier H_msg = 4. Signer keeps a 16 KiB (1024-node) keygen-time cache of the top XMSS tree: it stores one
level of the top tree, so each signature rebuilds 2^max(0, h'-10) top leaves. Lower layers are rebuilt fully.

Layers: d XMSS layers of height h'. Upper-layer one-time signature: SLH-DSA WOTS+ (w=4, len 68, as in the
d=1 design) or WOTS+C (w=16, l=32, S=240, 4-byte counter, as in Kudinov-Nick / SHRINCS).
Bottom few-time schemes (FTS): FORS, FORS+C, PORS+FP (hang below the bottom XMSS leaves, one per leaf), or
HG-WOTS (the bottom XMSS leaves themselves are HG-WOTS keys that sign the message).
Optional verifier-enforced proof of work: g zero bits in the digest (adds g bits to every forgery term).

Security (generic-attack model, as in SPHINCS+/Kudinov-Nick): per-query forgery probability
  sum_r Pois(lambda, r) * P_forge(r) * 2^-g,  lambda = q / 2^h,   required <= 2^-128 (max convention).
"""

import math
import sys
from functools import lru_cache

from octopus_pmf import pmf_leftfilled  # MIT, copied unmodified from github.com/MehdiAbri/PORS-FP


@lru_cache(maxsize=None)
def _octopus_cdf(t, k):
    pmf = pmf_leftfilled(t, k)
    cdf, acc = {}, 0.0
    for m in sorted(pmf):
        acc += pmf[m]
        cdf[m] = acc
    return cdf


def pors_success_prob(t, k, mmax):
    """P(|Octopus auth set| <= mmax) for a uniform k-subset of t leaves."""
    cdf = _octopus_cdf(t, k)
    below = [m for m in cdf if m <= mmax]
    return cdf[max(below)] if below else 0.0


def mmax_for(a, k, grind_bits):
    """Smallest Octopus bound m_max reachable with about 2^grind_bits expected attempts."""
    for m, c in sorted(_octopus_cdf(k * 2**a, k).items()):
        if c >= 2.0**-grind_bits:
            return m

N = 16
MSG_ATTEMPT = 7
HMSG_VERIFY = 4
CACHE_NODES = 1024
LN2 = math.log(2)


def T(l):
    return math.ceil((22 + N * l + 9) / 64)


# ------------------------------------------------------------------ one-time signatures in the layers
OTS = {
    # name: (bytes, keygen per leaf incl. its tree node, verify, sign-time grinding per layer)
    "wots4": (68 * N, 68 + 68 * 3 + T(68) + 1, 68 * 3 + T(68), 0),
    "wots16": (35 * N, 35 + 35 * 15 + T(35) + 1, 35 * 15 + T(35), 0),
    "wotsc16": (32 * N + 4, 32 + 32 * 15 + T(32) + 1, (15 * 32 - 240) + 1 + T(32), 66),
}


def log2_add(x, y):
    b, l = max(x, y), min(x, y)
    return b if b == -math.inf else b + math.log2(1 + 2 ** (l - b))


def poisson_sum(log2q, h, log2_pforge, rmax=10**6):
    """log2 of sum_r Pois(lambda, r) * P_forge(r); log2_pforge(r) -> log2 probability (<= 0)."""
    lam = 2.0 ** (log2q - h)
    lp = -lam / LN2
    tot = -math.inf
    r = 0
    while r < rmax:
        r += 1
        lp += math.log2(lam) - math.log2(r)
        term = lp + log2_pforge(r)
        tot = log2_add(tot, term)
        if r > lam and term < tot - 50:
            break
    return tot


def lifetime(h, log2_pforge, target=128.0, lo=0.0, hi=None):
    """Largest log2 q with -log2(sum) >= target."""
    hi = hi if hi is not None else h + 16.0
    if -poisson_sum(lo, h, log2_pforge) < target:
        return None
    for _ in range(40):
        mid = (lo + hi) / 2
        if -poisson_sum(mid, h, log2_pforge) >= target:
            lo = mid
        else:
            hi = mid
    return lo


# ------------------------------------------------------------------ bottom few-time schemes
class FORS:
    kind = "FORS"

    def __init__(self, a, k):
        self.a, self.k = a, k

    def size(self):
        return self.k * (self.a + 1) * N

    def sign(self):
        return self.k * (3 * 2**self.a - 1) + T(self.k)

    def verify(self):
        return self.k * (1 + self.a) + T(self.k)

    def attempts(self):
        return 1.0

    def log2_pforge(self, r):
        t = 2.0**self.a
        return self.k * math.log2(-math.expm1(r * math.log1p(-1 / t)))

    def __str__(self):
        return f"FORS a={self.a} k={self.k}"


class FORSC(FORS):
    """FORS+C: the last of k trees is forced to index 0 by grinding and omitted from the signature."""
    kind = "FORS+C"

    def size(self):
        return (self.k - 1) * (self.a + 1) * N

    def sign(self):
        return (self.k - 1) * (3 * 2**self.a - 1) + T(self.k - 1)

    def verify(self):
        return (self.k - 1) * (1 + self.a) + T(self.k - 1)

    def attempts(self):
        return 2.0**self.a

    def log2_pforge(self, r):
        t = 2.0**self.a
        return (self.k - 1) * math.log2(-math.expm1(r * math.log1p(-1 / t))) - self.a

    def __str__(self):
        return f"FORS+C a={self.a} k={self.k}"


class PORSFP:
    """PORS+FP: one tree of t = k 2^a leaves, k distinct indices, Octopus auth set padded to m_max."""
    kind = "PORS+FP"

    def __init__(self, a, k, mmax):
        self.a, self.k, self.mmax = a, k, mmax
        self.t = k * 2**a
        self._p = pors_success_prob(self.t, k, mmax)

    def size(self):
        return (self.k + self.mmax) * N

    def sign(self):
        return 2 * self.t + (self.t - 1)

    def verify(self):
        return self.k + (self.k + self.mmax - 1)  # corrected node count (k + m - 1)

    def attempts(self):
        return 1.0 / self._p

    @lru_cache(maxsize=None)
    def log2_pforge(self, r):
        # C(min(rk, t), k) / C(t, k), conservative (ignores the m_max filter on the forger)
        m = min(r * self.k, self.t)
        if m < self.k:
            return -math.inf
        return (math.lgamma(m + 1) - math.lgamma(self.k + 1) - math.lgamma(m - self.k + 1)
                - (math.lgamma(self.t + 1) - math.lgamma(self.k + 1) - math.lgamma(self.t - self.k + 1))) / LN2

    def __str__(self):
        return f"PORS+FP a={self.a} k={self.k} m={self.mmax}"


class HGWOTS:
    """HG-WOTS leaves at the bottom layer; cov[r] = -log2 cover(r) (r >= 2) from the exact calculator."""
    kind = "HG-WOTS"

    def __init__(self, k, s, j, w, w2, dg, dh, log2nu, cov):
        self.k, self.s, self.j, self.w, self.w2, self.dg, self.dh = k, s, j, w, w2, dg, dh
        self.log2nu = log2nu
        self.cov = dict(cov)  # r -> bits
        self.gmin = max(0.0, 128 - log2nu)

    def nodes(self):
        return (self.k - self.j) * self.s + self.j

    def size(self):
        return self.nodes() * N

    def leaf_keygen(self):
        k, s = self.k, self.s
        return k * s + k * s * (self.w - 1) + k * T(s) + k * (self.w2 - 1) + T(k) + 1

    def verify(self):
        kr = self.k - self.j
        return kr * self.dg + kr * T(self.s) + kr * (self.w2 - 1) + self.dh + T(self.k)

    def attempts(self):
        return 2.0**self.gmin

    def log2_pforge(self, r):
        # security at r uses = gmin + cov[r] (r >= 2); r = 1: 128 bits (digest-limited)
        if r == 1:
            return -128.0
        rr = max(k for k in self.cov if k <= r) if r not in self.cov else r
        c = self.cov[rr] if r in self.cov else 0.0  # beyond computed r: bound cover by 1 (conservative)
        return -(self.gmin + c)

    def __str__(self):
        return f"HG k={self.k} s={self.s} j={self.j} w={self.w} w2={self.w2} dg={self.dg} dh={self.dh}"


# ------------------------------------------------------------------ whole scheme
def evaluate(fts, d, hp, ots="wotsc16", pow_bits=0, pruned_lifetime=16, life_target=None):
    h = d * hp
    osize, oleaf, over, ogrind = OTS[ots]
    hg = isinstance(fts, HGWOTS)
    bottom_leaf = fts.leaf_keygen() if hg else oleaf
    n_ots_layers = d - 1 if hg else d
    size = N + fts.size() + n_ots_layers * osize + h * N  # R + FTS + WOTS sigs + auth paths

    def trees_cost(keep_top_log2, keep_low_log2):
        """per-signature tree work with the 16 KiB cache; keep_* = log2 of real (unpruned) leaves per tree."""
        top_leaf = bottom_leaf if d == 1 else oleaf
        c = max(0.0, keep_top_log2 - math.log2(CACHE_NODES))
        cost = 2.0**c * top_leaf + min(2.0**keep_top_log2, CACHE_NODES)
        for layer in range(d - 1):
            leafc = bottom_leaf if layer == 0 else oleaf
            cost += 2.0**keep_low_log2 * (leafc + 1)
        return cost

    grind_attempts = fts.attempts() * 2.0**pow_bits
    fts_sign = 0.0 if hg else fts.sign()
    sign = trees_cost(hp, hp) + fts_sign + MSG_ATTEMPT * grind_attempts + ogrind * n_ots_layers
    keygen = 2.0**hp * ((bottom_leaf if d == 1 else oleaf) + 1)
    verify = HMSG_VERIFY + fts.verify() + n_ots_layers * over + h

    lp = (lambda r: fts.log2_pforge(r) - pow_bits)
    life = lifetime(h, lp)

    out = dict(fts=str(fts), kind=fts.kind, d=d, hp=hp, h=h, ots=ots, g=pow_bits, size=size,
               keygen=keygen, sign=sign, verify=verify, life=life, attempts=grind_attempts)
    # pruned mode: keep 2^(h - P) real bottom instances, P = life - pruned_lifetime, split evenly over layers
    if life is not None and life > pruned_lifetime:
        P = life - pruned_lifetime
        per = P / d
        kp = trees_cost(hp - per, hp - per)
        out["P"] = P
        out["keygen_p"] = 2.0 ** (hp - per) * ((bottom_leaf if d == 1 else oleaf) + 1)
        out["sign_p"] = kp + fts_sign + MSG_ATTEMPT * grind_attempts * 2.0**P + ogrind * n_ots_layers
        # alternative for d = 1 or when grinding explodes: prune only the top tree (keygen), none below
        out["sign_p_toponly"] = trees_cost(hp - min(P, hp), hp) + fts_sign + MSG_ATTEMPT * grind_attempts * 2.0**min(P, hp)
        out["keygen_p_toponly"] = 2.0 ** (hp - min(P, hp)) * ((bottom_leaf if d == 1 else oleaf) + 1)
    return out


def fmt(x):
    if x is None:
        return "-"
    for dv, u in ((1e9, "B"), (1e6, "M"), (1e3, "K")):
        if x >= dv * 0.9995:
            return f"{x / dv:.3g}{u}"
    return f"{x:.0f}"


# -cov(r) = -log2 cover(r) for the 896-byte HG-WOTS set k=26 s=4 j=16 w=16 w2=4 dg=30 dh=24, from
# `python3 scripts/hgwots_security.py --r 2 3 4 5 6 7 8` (log2 nu = 165.0, so no encoding grinding).
HG896 = dict(params=(26, 4, 16, 16, 4, 30, 24), log2nu=165.0,
             cov={2: 82.1, 3: 53.5, 4: 40.6, 5: 32.7, 6: 27.3, 7: 23.2, 8: 20.1})


def designs():
    hg = HGWOTS(*HG896["params"], HG896["log2nu"], HG896["cov"])
    return [
        ("A  current: d=1 h=22, WOTS+ w=4, FORS a=12 k=15", FORS(12, 15), 1, 22, "wots4"),
        ("B  d=1 h=21, WOTS+C, PORS+FP a=13 k=14 (FP 2^4)", PORSFP(13, 14, mmax_for(13, 14, 4)), 1, 21, "wotsc16"),
        ("C  d=2 h=26, WOTS+C, PORS+FP a=15 k=9 (FP 2^4)", PORSFP(15, 9, mmax_for(15, 9, 4)), 2, 13, "wotsc16"),
        ("D  d=2 h=26, WOTS+ w=16, FORS a=13 k=11", FORS(13, 11), 2, 13, "wots16"),
        ("E  d=3 h=33, WOTS+C, PORS+FP a=10 k=12 (FP 2^14)", PORSFP(10, 12, mmax_for(10, 12, 14)), 3, 11, "wotsc16"),
        ("F  d=4 h=44, WOTS+C, HG-WOTS 896 B, no FORS", hg, 4, 11, "wotsc16"),
    ]


def main():
    print("Costs in SHA-256 compressions (16 KiB keygen cache). Lifetime = log2 signatures at 128 bits.\n")
    print(f"{'design':50s} | size | life  | keygen  sign    verify | 2^16-pruned keygen sign")
    for name, fts, d, hp, ots in designs():
        r = evaluate(fts, d, hp, ots=ots)
        print(f"{name:50s} | {r['size']:4d} | {r['life']:5.2f} | {fmt(r['keygen']):7s} {fmt(r['sign']):7s} {r['verify']:5.0f}  |"
              f" {fmt(r.get('keygen_p')):7s} {fmt(r.get('sign_p'))}")
    print("\nLifetime (log2 signatures at 128 bits) with a verifier-enforced g-bit digest condition:")
    print(f"{'design':50s} |  g=0    g=8   g=16   g=24 | grinding bits per doubling")
    for name, fts, d, hp, ots in designs():
        L = [evaluate(fts, d, hp, ots=ots, pow_bits=g)["life"] for g in (0, 8, 16, 24)]
        print(f"{name:50s} | " + "  ".join(f"{x:5.2f}" for x in L) + f" | {16 / (L[2] - L[0]):.1f}")


if __name__ == "__main__":
    main()
