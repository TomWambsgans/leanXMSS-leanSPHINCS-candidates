#!/usr/bin/env python3
"""Sizes, costs and lifetime of the leanSPHINCS candidate: SLH-DSA with d = 1, FORS, and WOTS+C (w = 4).

Default parameters: n = 16, h = 26, a = 10, k = 24, WOTS+C with 64 chains, target sum S = 120, 32-bit counter.
With --sweep, lists (h, a) combinations, taking for each the smallest k reaching the target lifetime.

Costs are SHA-256 compressions (SHA2 instantiation, PK.seed block precomputed as a midstate):
  PRF, F, H, WOTS+C digest   1 each
  T_l                        ceil((22 + 16 l + 9) / 64)
  H_msg                      5  (2 for SHA-256(R||PK.seed||PK.root||M') with a short or pre-hashed M',
                                 3 for the two MGF1 blocks, whose common 64-byte prefix is hashed once)
  message attempt            7  (PRF_msg 2 + H_msg 5), the unit of pruned-mode grinding
The signer's keygen-time cache (default 1 MiB = 2^16 nodes) stores one level of the XMSS tree; each signature
rebuilds the subtree below its cached node and hashes the cached level up to the root for the upper path.
Pruned keys keep 2^(h - (L - Lp)) real leaves (L = log2 full lifetime, Lp = log2 pruned lifetime) and grind
the message randomizer about 2^(L - Lp) times to land on one of them.
"""

import argparse
import math
from functools import lru_cache

from fors_security import Params, forgery_bits_poisson, max_log2_sigs

N = 16
CHAINS = 64  # WOTS+C with lg_w = 2 and n = 16: 128 / 2 digits, no checksum
W = 4
HMSG, PRFMSG = 5, 2
ATTEMPT = HMSG + PRFMSG


def T(l):
    return math.ceil((22 + N * l + 9) / 64)


@lru_cache(maxsize=None)
def n_sum(l, w, s):
    """Number of l-tuples in [0, w-1] with sum s."""
    poly = [1]
    for _ in range(l):
        new = [0] * (len(poly) + w - 1)
        for i, c in enumerate(poly):
            for d in range(w):
                new[i + d] += c
        poly = new
    return poly[s] if 0 <= s < len(poly) else 0


LEAF = CHAINS + CHAINS * (W - 1) + T(CHAINS) + 1  # PRF + full chains + T_64 + one tree node = 274


def digest_bytes(h, a, k):
    return math.ceil(k * a / 8) + math.ceil(h / 8)


def sig_bytes(h, a, k):
    return N + k * (a + 1) * N + 4 + CHAINS * N + h * N  # R, FORS, counter, WOTS+C, auth path


def wots_tries(S):
    return 4**CHAINS / n_sum(CHAINS, W, S)


def fors_sign(a, k):
    return k * (3 * 2**a - 1) + T(k)  # PRF + F per leaf, H per inner node, T_k


def wots_sign(S):
    return CHAINS + S + wots_tries(S)  # PRF per chain, S chain steps, counter search (1 per try)


def verify(h, a, k, S):
    """(hash calls, compressions); constant for every signature."""
    steps = (W - 1) * CHAINS - S
    calls = 1 + k * (1 + a) + 1 + 1 + steps + 1 + h
    comp = HMSG + k * (1 + a) + T(k) + 1 + steps + T(CHAINS) + h
    return calls, comp


def cache_cost(leaves_log2, cache_nodes):
    """Per-signature tree work for a tree of 2^leaves_log2 real leaves with the keygen-time cache.

    Best of two layouts for each height c: store every level >= c (rebuild 2^c leaves), or store only
    level c (rebuild 2^c leaves and hash the stored level up to the root for the upper path)."""
    if 2 ** (leaves_log2 + 1) <= cache_nodes:
        return 0.0  # the whole (kept) tree is cached
    best = math.inf
    for c in range(1, math.ceil(leaves_log2) + 1):
        if 2 ** (leaves_log2 - c + 1) <= cache_nodes:
            best = min(best, 2**c * LEAF)
        if 2 ** (leaves_log2 - c) <= cache_nodes:
            best = min(best, 2**c * LEAF + 2 ** (leaves_log2 - c))
    return best


def lifetime(h, a, k):
    return max_log2_sigs(128, Params("", N, h, a, k, 30), "poisson", "max")


def fmt(x):
    for dv, u in ((1e9, "B"), (1e6, "M"), (1e3, "K")):
        if x >= dv * 0.9995:
            return f"{x / dv:.3g}{u}"
    return f"{x:.0f}"


def report(h, a, k, S, cache_nodes, pruned):
    L = lifetime(h, a, k)
    calls, comp = verify(h, a, k, S)
    print(f"leanSPHINCS: n={N} h={h} d=1 a={a} k={k} WOTS+C w={W} l={CHAINS} S={S}, "
          f"m={digest_bytes(h, a, k)} B digest, cache {cache_nodes * N // 1024} KiB\n")
    print(f"signature {sig_bytes(h, a, k)} B = R {N} + FORS {k * (a + 1) * N} + counter 4 + WOTS+C {CHAINS * N} "
          f"+ auth {h * N};  pk {2 * N} B, sk {4 * N} B")
    print(f"lifetime at 128 bits: 2^{L:.2f} signatures")
    print(f"verification (constant): {calls} hash calls, {comp} compressions "
          f"(FORS {k * (1 + a)}, WOTS+C chains {(W - 1) * CHAINS - S}, auth {h})\n")

    print("WOTS+C target sum S:  S | log2 valid digests | expected counter tries | verifier chain steps")
    for s in (96, 104, 112, 120, 128, 132):
        mark = "  <- chosen" if s == S else ""
        print(f"                     {s:3d} | {math.log2(n_sum(CHAINS, W, s)):18.2f} | {wots_tries(s):22.0f} | {(W - 1) * CHAINS - s:3d}{mark}")

    fs, ws = fors_sign(a, k), wots_sign(S)
    full = cache_cost(h, cache_nodes) + fs + ws + ATTEMPT
    print(f"\nfull key:   keygen {fmt(2**h * LEAF)}, signing {fmt(full)} "
          f"(tree {fmt(cache_cost(h, cache_nodes))}, FORS {fmt(fs)}, WOTS+C {fmt(ws)})")
    for Lp in pruned:
        kept = h - (L - Lp)
        grind = ATTEMPT * 2 ** (L - Lp)
        sign = grind + cache_cost(kept, cache_nodes) + fs + ws
        print(f"pruned 2^{Lp:g}: keep 2^{kept:.2f} leaves, keygen {fmt(2**kept * LEAF)}, signing {fmt(sign)} "
              f"(grinding {fmt(grind)} = 2^{L - Lp:.2f} tries)")


def sweep(hs, as_, target, S, cache_nodes, Lp, max_sig):
    print(f"d=1, WOTS+C S={S}; smallest k with 128-bit lifetime >= 2^{target:g}; pruned to 2^{Lp:g}; "
          f"cache {cache_nodes * N // 1024} KiB. Costs in SHA-256 compressions.\n")
    print("| h | a | k | sig B | lifetime | keygen | sign | pruned keygen | pruned sign | verify |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for h in hs:
        for a in as_:
            k = next((k for k in range(1, 200) if forgery_bits_poisson(target, h, a, k) >= 128), None)
            if k is None or sig_bytes(h, a, k) > max_sig:
                continue
            L = lifetime(h, a, k)
            fs, ws = fors_sign(a, k), wots_sign(S)
            kept = h - (L - Lp)
            full = cache_cost(h, cache_nodes) + fs + ws + ATTEMPT
            pr = ATTEMPT * 2 ** (L - Lp) + cache_cost(kept, cache_nodes) + fs + ws
            print(f"| {h} | {a} | {k} | {sig_bytes(h, a, k):,} | 2^{L:.2f} | {fmt(2**h * LEAF)} | {fmt(full)} "
                  f"| {fmt(2**kept * LEAF)} | {fmt(pr)} | {verify(h, a, k, S)[1]} |")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], epilog=__doc__.split("\n\n", 1)[1],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--h", type=int, nargs="+", default=[26])
    ap.add_argument("--a", type=int, nargs="+", default=[10])
    ap.add_argument("--k", type=int, default=24)
    ap.add_argument("--S", type=int, default=120, help="WOTS+C target digit sum (default 120)")
    ap.add_argument("--cache-kib", type=int, default=1024, help="keygen-time cache (default 1024 KiB)")
    ap.add_argument("--pruned", type=float, nargs="+", default=[16, 18, 20], help="log2 pruned lifetimes")
    ap.add_argument("--sweep", action="store_true", help="scan --h and --a with the smallest k for --lifetime")
    ap.add_argument("--lifetime", type=float, default=30, help="target log2 lifetime for --sweep (default 30)")
    ap.add_argument("--max-sig", type=int, default=8192, help="max signature bytes for --sweep")
    args = ap.parse_args()
    cache_nodes = args.cache_kib * 1024 // N
    if args.sweep:
        sweep(args.h, args.a, args.lifetime, args.S, cache_nodes, args.pruned[0], args.max_sig)
    else:
        report(args.h[0], args.a[0], args.k, args.S, cache_nodes, args.pruned)


if __name__ == "__main__":
    main()
