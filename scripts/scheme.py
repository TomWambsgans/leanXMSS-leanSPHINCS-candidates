#!/usr/bin/env python3
"""Sizes, compression counts and lifetime of the leanSphincs candidate (the numbers in leansphincs.tex).

Costs count compression-function calls of a hash with 64-byte blocks and no padding overhead, such as
BLAKE2s: hashing l bytes costs max(1, ceil(l / 64)). Every call hashes tw (16 B) || P (16 B) || input.
"""

import argparse
import math

from blake2s_circuit import chain
from fors_security import Params, max_log2_sigs

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
    ap.add_argument("--cache-mib", type=float, nargs="+", default=[0, 1, 1024],
                    help="signer cache sizes for full-key signing (MiB)")
    ap.add_argument("--pruned-cache-kib", type=float, nargs="+", default=[0, 1, 16],
                    help="signer cache sizes for pruned-key signing (KiB)")
    ap.add_argument("--pruned", type=int, nargs="+", default=[12, 14, 16], help="log2 kept leaves")
    ap.add_argument("--threshold", type=int, default=12, help="log2 kept leaves for the threshold estimate")
    ap.add_argument("--bits-per-and", type=float, nargs="+", default=[1.0, 1.5],
                    help="MPC traffic per AND gate per operator (estimate)")
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
    L = max_log2_sigs(128, Params("", 16, h, a, k, 30), "exact", "max")

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
    print(f"  lifetime at 128 bits: 2^{L:.2f} signatures")
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
        print(f"  pruned, 2^{b} leaves: lifetime 2^{L - (h - b):.2f}, key generation {fmt(kg)}, "
              f"signing {signs} (grinding {fmt(grind)})")

    # Threshold signing: BLAKE2s runs in MPC only on secret inputs. A compression has 80 G functions of 184
    # AND gates each (two three-operand and two two-operand 32-bit additions); blake2s_circuit.py counts them
    # and the AND-depth, i.e. the number of MPC rounds.
    and_gates = chain(1)[0]
    depth = {s: chain(s)[1] for s in range(1, q)}  # AND-depth (MPC rounds) of s chained hashes
    b = x.threshold
    dkg = 2**b * v * (q - 1)  # chain steps of the kept WOTS keys
    fresh = k * 2**a + T  # one instance, preprocessed: FORS leaf hashes and WOTS chain steps
    try_cost = comp(N + 4) + msg_block  # R = H(R_0, ctr), then the first digest call
    online = 2**h * try_cost  # grind until idx is the instance drawn for this signature
    trivial = 2 ** (h - b) * try_cost  # grind until idx lands in the kept subtree

    def traffic(c):
        def size(nbytes):
            for dv, u in ((1e9, "GB"), (1e6, "MB"), (1e3, "KB")):
                if nbytes >= dv:
                    return f"{nbytes / dv:.3g} {u}"
            return f"{nbytes:.0f} B"
        return " / ".join(size(c * and_gates * bpa / 8) for bpa in x.bits_per_and)

    print(f"  threshold, 2^{b} kept leaves, {and_gates} AND gates per compression, traffic per operator at "
          f"{' / '.join(map(str, x.bits_per_and))} bits per AND:")
    print(f"    DKG: {fmt(dkg)} MPC compressions, {traffic(dkg)}, {depth[q - 1]} rounds")
    # FORS leaves, one opening, then the WOTS chains (the chain ends are public, so at most q - 2 steps)
    print(f"    preprocessing a new FORS instance: {fmt(fresh)} MPC compressions, {traffic(fresh)}, "
          f"{depth[1] + (1 + depth[q - 2] if q > 2 else 0)} rounds")
    print(f"    online: no MPC, grinding {fmt(online)} compressions in the clear "
          f"(trivial variant without preprocessing: {fmt(trivial)})")
    # Key rotation variant: every secret is H(S, addr) for a shared master secret S, derived in MPC (one more
    # MPC hash per secret); rotating only re-randomizes the shares of S.
    depth[q] = chain(q)[1]
    dkg_rot, fresh_rot = 2**b * v * q, fresh + k * 2**a + v
    print(f"    key rotation variant (secrets derived in MPC from a shared S): DKG {fmt(dkg_rot)} MPC compressions, "
          f"{traffic(dkg_rot)}, {depth[q]} rounds; FORS instance {fmt(fresh_rot)}, {traffic(fresh_rot)}, "
          f"{depth[2] + (1 + depth[q - 1] if q > 2 else 0)} rounds")

    # Trusted dealer (PRAWNS): the dealer computes every FORS instance of the kept leaves and the WOTS
    # signature of every FORS root in the clear, and publishes the FORS leaves and those WOTS signatures.
    dealer = derive + 2**b * leaf + (2**b - 1) * node + (h - b) * (derive + node)
    dealer += 2**b * (fors_sign + wots_sign)
    public = 2**b * (k * 2**a * N + v * N + 4)
    rebuild = k * (2**a - 1) * node  # the combiner rebuilds the 24 FORS paths from the public leaves
    print(f"  trusted dealer, 2^{b} kept leaves: dealer keygen {fmt(dealer)} compressions, public data "
          f"{public / 1e9:.3g} GB; signing: grinding {fmt(trivial)} + FORS paths {fmt(rebuild)} compressions, no MPC")


if __name__ == "__main__":
    main()
