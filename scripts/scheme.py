#!/usr/bin/env python3
"""Sizes and permutation counts of the leanSphincs candidate (the costs in leanSPHINCS.tex).

Costs count Keccak-f[1600] permutations of Keccak-256 (rate 136 bytes, at least one byte of padding):
hashing l bytes costs floor(l / 136) + 1. Every call hashes P (16 B) || address (16 B) || input.
A pruned signer tries the randomizers R_0 + i * delta, with R_0 and delta (odd) the two halves of one hash
of the seed and the message. The digest input P || address || m || rho is 80 bytes, one block, so an
attempt costs one permutation.

The lifetimes are the ones proved in Lean (formal/sphincs/scripts/forest_certificates.py, PARAMS) and,
for comparison, the cover attack they are measured against (ATTACK, from forest_attack.py).
"""

import argparse
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "formal", "sphincs", "scripts"))
import forest_certificates as fc
import forest_table

N = 16  # bytes per hash value
PREFIX = 32  # the public parameter and the address
RATE = 136  # Keccak-256


def comp(input_bytes):
    return (PREFIX + input_bytes) // RATE + 1


def merged(key_bytes):
    """The WOTS+C encoding hashes the forest key with the 4-byte counter last (there is no key hash).
    Returns (verifier's cost, whole blocks the signer absorbs once, cost of one counter)."""
    fixed = PREFIX + key_bytes
    return comp(key_bytes + 4), fixed // RATE, (fixed % RATE + 4) // RATE + 1


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
    ap.add_argument("--h", type=int, default=fc.TOTAL, help="tree height; the full key keeps all 2^h instances")
    ap.add_argument("--lg-w", type=int, default=2, help="bits per WOTS chain; chains have length 2^lg_w")
    ap.add_argument("--T", type=int, default=123, help="sum of the signed chain positions")
    ap.add_argument("--cache-mib", type=float, nargs="+", default=[1, 16, 1024],
                    help="signer cache sizes for full-key signing (MiB)")
    ap.add_argument("--pruned-cache-kib", type=float, nargs="+", default=[16, 1024],
                    help="signer cache sizes for pruned-key signing (KiB)")
    ap.add_argument("--pruned", type=int, nargs="+", default=[13, 20], help="log2 kept leaves")
    ap.add_argument("--threshold", type=int, default=12, help="log2 kept leaves for the threshold estimate")
    x = ap.parse_args()
    h, lg_w, T = x.h, x.lg_w, x.T
    v, q = -(-128 // lg_w), 2**lg_w  # v chains of length q cover the 128-bit message

    # The few-time signature: 8 coordinates of 16 super-children; a super-child hashes the top nodes of its
    # 2 sub-trees of 8 WOTS children; a child is 6 chains of 4 steps under a leaf hash, signed at a codeword
    # of digit sum 5. No tree or sub-tree has a root hash, and the forest key is not hashed either.
    coords, supers, subs, children, chains, chain_steps, digit_sum = 8, 16, 2, 8, 6, 4, 5
    sub_path, top_path = int(math.log2(children)), int(math.log2(supers))
    coord_bits = top_path + subs * (sub_path + 8)

    # per-call costs (input after the 32-byte prefix)
    derive, step, node = comp(32), comp(N), comp(2 * N)
    wots_pk, key_leaf, super_hash = comp(v * N), comp(chains * N), comp(subs * 2 * N)
    enc, enc_fixed, enc_try = merged(coords * 2 * N)
    rnd, digest = comp(32 + 32), comp(32 + N)  # S || m ;  m || rho: one call of h + 8 * 26 bits
    attempt = digest  # the digest call, at randomizer R_0 + i * delta

    if not 0 <= T <= v * (q - 1):
        ap.error(f"--T must be between 0 and {v * (q - 1)}")
    alpha = n_sum(v, q, T) / q**v  # probability that a counter gives sum T
    # One derivation hash gives two secrets (its two 16-byte halves): two chain starts of a WOTS key.
    leaf = v // 2 * derive + v * (q - 1) * step + wots_pk
    wots_key = chains // 2 * derive + chains * chain_steps * step + key_leaf
    subtree = children * wots_key + (children - 2) * node
    coord = supers * (subs * subtree + super_hash) + (supers - 2) * node
    forest_sign = coords * coord
    wots_sign = enc_fixed + enc_try / alpha + v // 2 * derive + T * step
    values = subs * (chains + sub_path) + top_path
    per_coord = subs * (digit_sum * step + key_leaf + (sub_path - 1) * node) + super_hash + (top_path - 1) * node
    verify = digest + coords * per_coord + enc + ((q - 1) * v - T) * step + wots_pk + h * node
    keygen = derive + 2**h * leaf + (2**h - 1) * node
    size = N + coords * values * N + 4 + v * N + h * N

    def lifetimes(b):
        """(proved in Lean, cover attack) for a key that keeps a subtree of 2^b leaves."""
        proved = next((n for (bb, n, _) in fc.PARAMS if bb == b), None)
        return proved, fc.ATTACK.get(b)

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

    def show(b, label, kg=None):
        proved, attack = lifetimes(b)
        life = "" if proved is None else (f"lifetime {fmt(proved)} ({fmt(attack)} for the cover attack), ")
        grind = 2 ** (h - b) * attempt
        base = grind + rnd + digest - attempt + forest_sign + wots_sign
        caches = x.pruned_cache_kib if b < h else [1024 * c for c in x.cache_mib]
        signs = ", ".join(f"{fmt(base + tree_cost(b, nodes(kib / 1024)))} with "
                          f"{kib / 1024:g} MiB" if kib >= 1024 else
                          f"{fmt(base + tree_cost(b, nodes(kib / 1024)))} with {kib:g} KiB"
                          for kib in caches)
        extra = "" if kg is None else f"key generation {fmt(kg)}, "
        print(f"  {label}: {life}{extra}signing {signs} (grinding {fmt(grind)})")

    print(f"leanSphincs candidate: h={h}, a two-level WOTS forest of {coords} coordinates, WOTS+C with {v} "
          f"chains of length {q} and T={T}; costs in Keccak-f permutations (Keccak-256)")
    print(f"  signature {size} B (rho 16, forest {coords * values * N}, counter 4, WOTS {v * N}, path {h * N}); "
          f"pk {2 * N} B")
    print(f"  digest: {h} + {coords} * {coord_bits} = {h + coords * coord_bits} bits, one call")
    print(f"  per call: derive {derive}, chain {step}, node {node}, encode {enc} (forest key + counter; signer "
          f"{enc_fixed} once + {enc_try} per counter), WOTS leaf {wots_pk}, randomizer {rnd}, digest {digest}")
    print(f"  WOTS encoding: {math.log2(n_sum(v, q, T)):.2f} bits of valid encodings, "
          f"expected {1 / alpha:.0f} counters, {fmt(wots_sign)} permutations")
    print(f"  verification: {verify} permutations ({per_coord} per coordinate, {values} values per coordinate)")
    print(f"  WOTS leaf {leaf}; forest key {wots_key} per child, {fmt(forest_sign)} per instance")
    print(f"  key generation {keygen:,} ({fmt(keygen)})")
    show(h, f"full key, 2^{h} leaves")
    for b in x.pruned:
        kg = derive + 2**b * leaf + (2**b - 1) * node + (h - b) * (derive + node)  # subtree + surrogate path
        show(b, f"pruned, 2^{b} leaves", kg)

    # Threshold signing (adapted from PRAWNS): every secret is F(addr) for a threshold PRF F. A one-time
    # ceremony hashes the chains of the 2^b kept instances and publishes the chain values under F; a
    # signature reveals the values below the tops, one per non-zero digit of the 16 codewords.
    b = x.threshold
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    opened = coords * subs
    forest_chains = coords * supers * subs * children * chains
    mpc_hashes = 2**b * (forest_chains * chain_steps + v * (q - 1))
    public = 2**b * (forest_chains * chain_steps * N + v * N + 4)
    proved, _ = lifetimes(b)
    print(f"  threshold, 2^{b} kept leaves (lifetime {fmt(proved) if proved else 'n/a'}): "
          f"{opened * sum(nonzero) / len(nonzero):.2f} values revealed per signature on average, at most "
          f"{opened * max(nonzero)}; {fmt(mpc_hashes)} MPC hashes at keygen, public data {public / 1e9:.3g} GB")
    # Keygen with a DKG: n-party replicated-sharing MPC, t = (n + 1) / 2, hash-based F. Bytes per operator for
    # one leaf hash and one 3-step chain, measured by `cargo run --release -p rss --bin bench`. A 4-step forest
    # chain is counted as a measured 3-step chain plus one measured leaf hash.
    measured = {3: (4553, 13625), 5: (5464, 16352), 7: (5855, 17522)}
    for n, (per_leaf, per_chain) in measured.items():
        traffic = 2**b * (forest_chains * (per_chain + per_leaf) + v * per_chain)
        print(f"    {n // 2 + 1}-of-{n}: DKG traffic {traffic / 1e9:.3g} GB per operator")


if __name__ == "__main__":
    main()
