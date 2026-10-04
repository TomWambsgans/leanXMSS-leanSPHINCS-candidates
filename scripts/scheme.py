#!/usr/bin/env python3
"""Sizes, compression counts and lifetime of the leanSphincs candidate (the numbers in leanSPHINCS.tex).

Costs count compression-function calls of a hash with 64-byte blocks and no padding overhead, such as
BLAKE2s: hashing l bytes costs max(1, ceil(l / 64)). Every call hashes tw (16 B) || P (16 B) || input.
"""

import argparse
import math

from adaptive_lifetime import max_signatures
from fors_security import Params, forgery_bits_exact, max_log2_sigs

N = 16  # bytes per hash value
PREFIX = 32  # tweak and public parameter


def comp(input_bytes):
    return max(1, math.ceil((PREFIX + input_bytes) / 64))


def n_sum(v, q, s):
    """Number of v-tuples in [0, q-1] with sum s."""
    poly = [1]
    for _ in range(v):
        new = [0] * (len(poly) + q - 1)
        for i, c in enumerate(poly):
            for d in range(q):
                new[i + d] += c
        poly = new
    return poly[s] if 0 <= s < len(poly) else 0


def fmt(x):
    for dv, u in ((1e9, "B"), (1e6, "M"), (1e3, "K")):
        if x >= dv * 0.9995:
            return f"{x / dv:.3g}{u}"
    return f"{x:.0f}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--h", type=int, default=26)
    ap.add_argument("--a", type=int, default=10)
    ap.add_argument("--k", type=int, default=24)
    ap.add_argument("--lg-w", type=int, default=2, help="bits per WOTS chain; chains have length 2^lg_w")
    ap.add_argument("--T", type=int, default=120, help="sum of the signed chain positions")
    ap.add_argument("--cache-mib", type=float, nargs="+", default=[1, 16, 1024],
                    help="signer cache sizes for full-key signing (MiB)")
    ap.add_argument("--pruned-cache-kib", type=float, nargs="+", default=[16, 1024],
                    help="signer cache sizes for pruned-key signing (KiB)")
    ap.add_argument("--pruned", type=int, nargs="+", default=[13, 20], help="log2 kept leaves")
    ap.add_argument("--threshold", type=int, default=12, help="log2 kept leaves for the threshold estimate")
    x = ap.parse_args()
    h, a, k, lg_w, T = x.h, x.a, x.k, x.lg_w, x.T
    v, q = -(-128 // lg_w), 2**lg_w  # v chains of length q cover the 128-bit message

    # per-call costs (input after the 32-byte prefix)
    derive, step, node, enc = comp(32), comp(N), comp(2 * N), comp(N + 4)
    wots_pk, fors_roots = comp(v * N), comp(k * N)
    rnd, msg_block = comp(32 + 32), comp(N + N + 32)  # S || m ;  rho || root || m
    blocks = math.ceil((h + k * a) / 256)

    if not 0 <= T <= v * (q - 1):
        ap.error(f"--T must be between 0 and {v * (q - 1)}")
    alpha = n_sum(v, q, T) / q**v  # probability that a counter gives sum T
    leaf = v * derive + v * (q - 1) * step + wots_pk
    fors_sign = k * (2**a * (derive + step) + (2**a - 1) * node) + fors_roots
    wots_sign = enc / alpha + v * derive + T * step
    verify = blocks * msg_block + k * (step + a * node) + fors_roots + enc + ((q - 1) * v - T) * step + wots_pk + h * node
    keygen = derive + 2**h * leaf + (2**h - 1) * node
    size = N + k * (1 + a) * N + 4 + v * N + h * N
    L = max_log2_sigs(127, Params("", 16, h, a, k, 30), "exact", "max")  # average FORS rate 2^-127 per query

    def average_log2_sigs(b, level=127):
        """Lifetime from the *average* FORS rate of a fresh digest (signatures spread over 2^b FORS
        instances, the digest landing in the subtree with probability 2^(b - h)). Not safe against
        forgers that choose between the FORS and WOTS searches after seeing their signatures."""
        def bits(log2_q):
            return min(8 * N, (h - b) + forgery_bits_exact(log2_q, b, a, k))
        lo, hi = 0.0, b + 12.0
        for _ in range(50):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if bits(mid) >= level else (lo, mid)
        return lo

    def tree_cost(height, cache_nodes):
        """Per-signature tree work: the best of keeping one level c (rebuild the 2^c leaves below the cached
        node, hash the cached level up) or keeping every level >= c (rebuild the 2^c leaves below)."""
        if 2 ** (height + 1) - 1 <= cache_nodes:
            return 0
        best = 2**height * leaf + (2**height - 1) * node  # no usable cache: rebuild the whole tree
        for c in range(1, height + 1):
            below = 2**c * leaf + (2**c - 1) * node
            if 2 ** (height - c + 1) - 1 <= cache_nodes:
                best = min(best, below)
            if 2 ** (height - c) <= cache_nodes:
                best = min(best, below + (2 ** (height - c) - 1) * node)
        return best

    def nodes(mib):
        return int(mib * 2**20) // N

    print(f"leanSphincs candidate: h={h} a={a} k={k}, WOTS+C with {v} chains of length {q} and T={T}; "
          f"costs in 64-byte compressions")
    print(f"  signature {size} B (rho 16, FORS {k * (1 + a) * N}, counter 4, WOTS {v * N}, path {h * N}); pk 32 B")
    print(f"  per call: derive {derive}, chain {step}, node {node}, encode {enc}, WOTS leaf {wots_pk}, "
          f"FORS roots {fors_roots}, randomizer {rnd}, digest {blocks} x {msg_block}")
    print(f"  WOTS encoding: {math.log2(n_sum(v, q, T)):.2f} bits of valid encodings, "
          f"expected {1 / alpha:.0f} counters")
    if (h, a, k) == (26, 10, 24):
        print(f"  lifetime at 127 bits against adaptive forgers (adaptive_lifetime.py): "
              f"2^{math.log2(max_signatures(h)):.2f} signatures; average-rate estimate 2^{L:.2f}")
    else:
        print(f"  average-rate lifetime estimate at 127 bits (not adaptive-safe): 2^{L:.2f} signatures")
    print(f"  verification: {verify} compressions")
    print(f"  WOTS leaf {leaf}; key generation {keygen:,} ({fmt(keygen)})")
    for mib in x.cache_mib:
        tree = tree_cost(h, nodes(mib))
        sign = rnd + blocks * msg_block + fors_sign + wots_sign + tree
        print(f"  signing with a {mib:g} MiB cache: {fmt(sign)} "
              f"(tree {fmt(tree)}, FORS {fmt(fors_sign)}, WOTS {fmt(wots_sign)})")
    for b in x.pruned:
        kg = derive + 2**b * leaf + (2**b - 1) * node + (h - b) * (derive + node)  # subtree + surrogate path
        grind = 2 ** (h - b) * (rnd + msg_block)  # idx is in the first digest block
        base = grind + (blocks - 1) * msg_block + fors_sign + wots_sign
        signs = ", ".join(f"{fmt(base + tree_cost(b, nodes(kib / 1024)))} with {kib:g} KiB"
                          for kib in x.pruned_cache_kib)
        life = (f"lifetime 2^{math.log2(max_signatures(b)):.2f} (average-rate estimate 2^{average_log2_sigs(b):.2f})"
                if (h, a, k) == (26, 10, 24) else f"average-rate lifetime 2^{average_log2_sigs(b):.2f}")
        print(f"  pruned, 2^{b} leaves: {life}, key generation {fmt(kg)}, "
              f"signing {signs} (grinding {fmt(grind)})")

    # Threshold signing (adapted from PRAWNS): every FORS secret is F(addr) for a threshold PRF F. A one-time
    # ceremony hashes the secrets of the 2^b kept instances (FORS leaves and WOTS chains) and publishes the
    # FORS leaves and the WOTS signature of every FORS root; signing reveals 24 values of F, with no MPC.
    b = x.threshold
    mpc_hashes = 2**b * (k * 2**a + v * (q - 1))
    public = 2**b * (k * 2**a * N + v * N + 4)
    try_cost = comp(N + 4) + msg_block  # R = H(R_0, ctr), then the first digest call
    grind = 2 ** (h - b) * try_cost
    rebuild = k * (2**a - 1) * node  # the combiner rebuilds the 24 FORS paths from the public leaves
    life = max_signatures(b) if (h, a, k) == (26, 10, 24) else 2 ** average_log2_sigs(b)
    print(f"  threshold, 2^{b} kept leaves (lifetime 2^{math.log2(life):.2f}): {fmt(mpc_hashes)} MPC hashes at keygen, public data "
          f"{public / 1e9:.3g} GB; signing: grinding {fmt(grind)} + FORS paths {fmt(rebuild)} compressions, no MPC")
    # Keygen with a DKG: n-party replicated-sharing MPC, t = (n + 1) / 2, hash-based F. Bytes per operator for
    # one FORS leaf and one 3-step WOTS chain, measured by `cargo run --release -p rss --bin bench`.
    measured = {3: (1699, 5064), 5: (2039, 6078), 7: (2186, 6514)}
    # Trusted dealer: F costs comb(n, t - 1) hashes per secret with the hash-based F.
    dealer = derive + 2**b * leaf + (2**b - 1) * node + (h - b) * (derive + node)
    dealer += 2**b * (fors_sign + wots_sign)
    for n, (per_leaf, per_chain) in measured.items():
        f = n // 2
        traffic = 2**b * (k * 2**a * per_leaf + v * per_chain)
        dealer_n = dealer + 2**b * (k * 2**a + v) * (math.comb(n, f) - 1)
        print(f"    {f + 1}-of-{n}: DKG traffic {traffic / 1e9:.3g} GB per operator; "
              f"trusted dealer {fmt(dealer_n)} compressions")

if __name__ == "__main__":
    main()
