#!/usr/bin/env python3
"""Keygen / signing / verification cost of d = 1 SLH-DSA parameter sets, normal and pruned.

For each tree height h and FORS tree height a, takes the smallest k that keeps the target security
level (8n bits) for 2^LIFETIME signatures, and reports:
  - signature size and the exact log2 signature limit at the target level;
  - keygen: build the whole XMSS tree (2^h WOTS+ leaves);
  - signing with a keygen-time cache of CACHE_KIB: the cache holds the one tree level that fits
    (2^c nodes), so each signature rebuilds the 2^(h-c) leaves below its cached node, then does
    FORS, one WOTS+ signature and one H_msg;
  - pruned mode for 2^PRUNED_LIFETIME signatures: only 2^h / 2^(limit - PRUNED_LIFETIME) leaves
    are real WOTS+ keys (the rest are surrogates), so keygen and the per-signature rebuild shrink
    by that factor, and R is ground about 2^(limit - PRUNED_LIFETIME) times to hit a real leaf.
    FORS is not pruned.

Costs are SHA-256 compressions for the SHA2 variant, with the PK.seed block precomputed:
PRF, F and H take 1 compression, T_l takes ceil((22 + n*l + 9) / 64), and one H_msg attempt
(PRF_msg + H_msg on a short or pre-hashed message) is taken as GRIND_COST compressions.
"""

import argparse
import math

from fors_security import Params, forgery_bits_poisson, max_log2_sigs

ADRS_C = 22  # bytes of compressed ADRS in the SHA2 instantiation


def t_cost(n, blocks):
    """Compressions for T_l over `blocks` n-byte inputs (PK.seed block precomputed)."""
    return math.ceil((ADRS_C + n * blocks + 9) / 64)


def wots_len(n, lgw):
    w = 1 << lgw
    len1 = math.ceil(8 * n / lgw)
    len2 = math.floor(math.log2(len1 * (w - 1)) / lgw) + 1
    return len1 + len2


def evaluate(n, h, a, k, lgw, args):
    w = 1 << lgw
    wlen = wots_len(n, lgw)
    level = 8 * n

    leaf = wlen + wlen * (w - 1) + t_cost(n, wlen) + 1  # PRF + chains + T_len + one tree node
    wots_sign = wlen + wlen * (w - 1) / 2  # PRF + average chain walk
    fors = k * (3 * 2**a - 1) + t_cost(n, k)

    cache_nodes = args.cache_kib * 1024 // n
    cached_levels = min(h, int(math.log2(cache_nodes)))  # tree levels above the cached one
    rebuild = 2 ** (h - cached_levels) * leaf + 2**cached_levels  # subtree + path above cache

    limit = max_log2_sigs(level, Params("", n, h, a, k, args.lifetime), "poisson", "max")
    prune = max(0.0, limit - args.pruned_lifetime)  # log2 of the fraction of leaves pruned
    kept = h - prune  # log2 of real WOTS+ leaves
    rebuild_p = 2 ** max(0.0, kept - cached_levels) * leaf + 2**cached_levels

    return {
        "h": h, "a": a, "k": k,
        "sig": n * (1 + k * (a + 1) + wlen + h),
        "limit": limit,
        "keygen": 2**h * leaf,
        "sign": fors + wots_sign + rebuild + args.grind_cost,
        "keygen_p": 2**kept * leaf + h,
        "sign_p": fors + wots_sign + rebuild_p + args.grind_cost * 2**prune,
        "verify": k * (a + 1) + t_cost(n, k) + wlen * (w - 1) + t_cost(n, wlen) + h + 4,
    }


def pareto(rows):
    """Drop rows beaten on both signature size and signing cost by another row of the same h."""
    return [r for r in rows if not any(
        o["h"] == r["h"] and o["sig"] <= r["sig"] and o["sign"] <= r["sign"] and o is not r
        and (o["sig"], o["sign"]) != (r["sig"], r["sign"]) for o in rows)]


def fmt(x):
    """3 significant digits with a K / M / B suffix: 451K, 1.23M, 4.88B."""
    for div, unit in ((1e9, "B"), (1e6, "M"), (1e3, "K")):
        if x >= div * 0.9995:  # so 999,600 prints as 1M, not 1e+03K
            return f"{x / div:.3g}{unit}"
    return f"{x:.0f}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                 epilog=__doc__.split("\n\n", 1)[1],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=16, help="hash length in bytes (default 16)")
    ap.add_argument("--lgw", type=int, default=2, help="log2 of the Winternitz parameter (default 2, w = 4)")
    ap.add_argument("--h", type=int, nargs="+", default=list(range(18, 27)), help="tree heights (default 18..26)")
    ap.add_argument("--a", type=int, nargs="+", default=list(range(6, 25)), help="FORS tree heights (default 6..24)")
    ap.add_argument("--lifetime", type=float, default=24, help="log2 signatures at full security (default 24)")
    ap.add_argument("--pruned-lifetime", type=float, default=16, help="log2 signatures after pruning (default 16)")
    ap.add_argument("--cache-kib", type=int, default=16, help="keygen-time cache size in KiB (default 16)")
    ap.add_argument("--max-sig", type=int, default=5120, help="max signature size in bytes (default 5120)")
    ap.add_argument("--grind-cost", type=float, default=7, help="compressions per H_msg attempt (default 7)")
    ap.add_argument("--all", action="store_true", help="also show rows dominated on (size, signing cost)")
    args = ap.parse_args()

    level = 8 * args.n
    rows = []
    for h in args.h:
        for a in args.a:
            k = next((k for k in range(1, 200)
                      if forgery_bits_poisson(args.lifetime, h, a, k) >= level), None)
            if k is None:
                continue
            r = evaluate(args.n, h, a, k, args.lgw, args)
            if r["sig"] <= args.max_sig:
                rows.append(r)
    if not args.all:
        rows = pareto(rows)

    print(f"n={args.n} d=1 w={1 << args.lgw}, {level}-bit security for 2^{args.lifetime:g} signatures, "
          f"{args.cache_kib} KiB cache, sig <= {args.max_sig} B; "
          f"pruned: 2^{args.pruned_lifetime:g} signatures. Costs in SHA-256 compressions.\n")
    print(f"| h | a | k | sig B | limit | keygen | sign | pruned keygen | pruned sign | verify |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    for r in rows:
        print(f"| {r['h']} | {r['a']} | {r['k']} | {r['sig']:,} | 2^{r['limit']:.2f} | {fmt(r['keygen'])} "
              f"| {fmt(r['sign'])} | {fmt(r['keygen_p'])} | {fmt(r['sign_p'])} | {r['verify']:.0f} |")


if __name__ == "__main__":
    main()
