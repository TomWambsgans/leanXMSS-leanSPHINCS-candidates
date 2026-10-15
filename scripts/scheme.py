#!/usr/bin/env python3
"""Sizes and permutation counts of the leanSphincs candidate and of its spicy variant (the costs in leanSPHINCS.tex).
The lifetimes printed here are estimates from the cover model; the note quotes the limits proved in Lean.

Costs count Keccak-f[1600] permutations of SHA3-256 (rate 136 bytes, at least one byte of padding):
hashing l bytes costs floor(l / 136) + 1. Every call hashes P (16 B) || address (16 B) || input.
A pruned signer tries the randomizers R_0 + i, with R_0 one hash of the seed and the message. The digest
input P || address || m || rho is 80 bytes, one block, so an attempt costs one permutation.
"""

import argparse
import math
import os
import sys

from fors_security import Params, forgery_bits_exact, max_log2_sigs

N = 16  # bytes per hash value
PREFIX = 32  # the public parameter and the address


RATE = 136  # SHA3-256


def comp(input_bytes):
    return (PREFIX + input_bytes) // RATE + 1


def merged(tops_bytes):
    """The WOTS+C encoding hashes the FTS tops with the 4-byte counter last (there is no FTS key hash).
    Returns (verifier's cost, whole blocks the signer absorbs once, cost of one counter)."""
    fixed = PREFIX + tops_bytes
    return comp(tops_bytes + 4), fixed // RATE, (fixed % RATE + 4) // RATE + 1


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
    ap.add_argument("--T-spicy", type=int, default=123, help="the same for the spicy variant")
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
    derive, step, node = comp(32), comp(N), comp(2 * N)
    # A FORS tree has no root hash, and there is no FORS key hash: the WOTS+C encoding absorbs the two nodes
    # below the root of every tree, then the counter.
    wots_pk = comp(v * N)
    enc, enc_fixed, enc_try = merged(2 * k * N)
    rnd, msg_block = comp(32 + 32), comp(32 + N)  # S || m ;  m || rho
    blocks = math.ceil((h + k * a) / 256)
    digest = blocks * msg_block
    attempt = msg_block  # the first digest call, at randomizer R_0 + i

    if not 0 <= T <= v * (q - 1):
        ap.error(f"--T must be between 0 and {v * (q - 1)}")
    alpha = n_sum(v, q, T) / q**v  # probability that a counter gives sum T
    # One derivation hash gives two secrets (its two 16-byte halves): two chain starts, or two FORS leaves.
    leaf = v // 2 * derive + v * (q - 1) * step + wots_pk
    fors_sign = k * (2**a // 2 * derive + 2**a * step + (2**a - 2) * node)
    wots_sign = enc_fixed + enc_try / alpha + v // 2 * derive + T * step
    verify = digest + k * (step + (a - 1) * node) + enc + ((q - 1) * v - T) * step + wots_pk + h * node
    keygen = derive + 2**h * leaf + (2**h - 1) * node
    size = N + k * (1 + a) * N + 4 + v * N + h * N
    L = max_log2_sigs(127, Params("", 16, h, a, k, 30), "exact", "max")  # the FORS term at 2^-127 per query

    def pruned_log2_sigs(b, level=127):
        """Lifetime of a key that keeps a subtree of 2^b leaves: the signatures spread over its 2^b FORS
        instances, and a forger's digest must also land in the subtree (probability 2^(b - h))."""
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
          f"costs in Keccak-f permutations (SHA3-256)")
    print(f"  signature {size} B (rho 16, FORS {k * (1 + a) * N}, counter 4, WOTS {v * N}, path {h * N}); pk {2 * N} B")
    print(f"  per call: derive {derive}, chain {step}, node {node}, encode {enc} (FORS tops + counter; signer "
          f"{enc_fixed} once + {enc_try} per counter), WOTS leaf {wots_pk}, randomizer {rnd}, digest {digest}")
    print(f"  WOTS encoding: {math.log2(n_sum(v, q, T)):.2f} bits of valid encodings, "
          f"expected {1 / alpha:.0f} counters")
    print(f"  lifetime at 127 bits: 2^{L:.2f} signatures")
    print(f"  verification: {verify} permutations")
    print(f"  WOTS leaf {leaf}; key generation {keygen:,} ({fmt(keygen)})")
    for mib in x.cache_mib:
        tree = tree_cost(h, nodes(mib))
        sign = rnd + digest + fors_sign + wots_sign + tree
        print(f"  signing with a {mib:g} MiB cache: {fmt(sign)} "
              f"(tree {fmt(tree)}, FORS {fmt(fors_sign)}, WOTS {fmt(wots_sign)})")
    for b in x.pruned:
        kg = derive + 2**b * leaf + (2**b - 1) * node + (h - b) * (derive + node)  # subtree + surrogate path
        grind = 2 ** (h - b) * attempt  # idx is in the first digest call
        base = grind + rnd + digest - attempt + fors_sign + wots_sign
        signs = ", ".join(f"{fmt(base + tree_cost(b, nodes(kib / 1024)))} with {kib:g} KiB"
                          for kib in x.pruned_cache_kib)
        print(f"  pruned, 2^{b} leaves: lifetime 2^{pruned_log2_sigs(b):.2f}, key generation {fmt(kg)}, "
              f"signing {signs} (grinding {fmt(grind)})")

    # The spicy variant (leanSPHINCS.tex, section 3): FORS is replaced by a two-level WOTS forest. 8 trees of
    # 16 leaves; a leaf hashes the top nodes of 2 subtrees of 8 WOTS keys; a WOTS key is 6 chains of 4 steps
    # under a leaf hash, signed at a codeword of digit sum 5. No tree or subtree has a root hash.
    trees, tree_leaves, subs, keys, chains, chain_steps, digit_sum = 8, 16, 2, 8, 6, 4, 5
    key_leaf, leaf_hash = comp(chains * N), comp(subs * 2 * N)
    enc_s, enc_fixed_s, enc_try_s = merged(trees * 2 * N)
    T_s = x.T_spicy
    alpha_s = n_sum(v, q, T_s) / q**v
    wots_sign_s = enc_fixed_s + enc_try_s / alpha_s + v // 2 * derive + T_s * step
    wots_key = chains // 2 * derive + chains * chain_steps * step + key_leaf
    subtree = keys * wots_key + (keys - 2) * node
    tree = tree_leaves * (subs * subtree + leaf_hash) + (tree_leaves - 2) * node
    forest_sign = trees * tree
    sub_path, tree_path = int(math.log2(keys)), int(math.log2(tree_leaves))
    values = subs * (chains + sub_path) + tree_path
    per_tree = subs * (digit_sum * step + key_leaf + (sub_path - 1) * node) + leaf_hash + (tree_path - 1) * node
    digest_s = msg_block  # 26 + 8 * 26 = 234 bits: one digest call
    size_s = N + trees * values * N + 4 + v * N + h * N
    verify_s = digest_s + trees * per_tree + enc_s + ((q - 1) * v - T_s) * step + wots_pk + h * node
    print(f"spicy (two-level WOTS forest): signature {size_s} B ({1 - size_s / size:.1%} smaller), verification "
          f"{verify_s} permutations ({1 - verify_s / verify:.1%} fewer; {per_tree} per tree, {values} values per tree)")
    print(f"  WOTS key {wots_key}; forest signing {fmt(forest_sign)} (FORS {fmt(fors_sign)}); WOTS+C T={T_s}, expected "
          f"{1 / alpha_s:.0f} counters, {fmt(wots_sign_s)}; key generation unchanged")
    for mib in x.cache_mib:
        tree_c = tree_cost(h, nodes(mib))
        print(f"  signing with a {mib:g} MiB cache: {fmt(rnd + digest_s + forest_sign + wots_sign_s + tree_c)}")
    for b in x.pruned:
        grind = 2 ** (h - b) * attempt
        base = grind + rnd + digest_s - attempt + forest_sign + wots_sign_s
        signs = ", ".join(f"{fmt(base + tree_cost(b, nodes(kib / 1024)))} with {kib:g} KiB" for kib in x.pruned_cache_kib)
        print(f"  pruned, 2^{b} leaves: signing {signs} (grinding {fmt(grind)})")
    # Threshold signing (adapted from PRAWNS): every FORS secret is F(addr) for a threshold PRF F. A one-time
    # ceremony hashes the secrets of the 2^b kept instances (FORS leaves and WOTS chains) and publishes the
    # FORS leaves and the WOTS signature of every FORS root; signing reveals 24 values of F, with no MPC.
    b = x.threshold
    mpc_hashes = 2**b * (k * 2**a + v * (q - 1))
    public = 2**b * (k * 2**a * N + v * N + 4)
    try_cost = msg_block  # R = R_0 + i, then the first digest call
    grind = 2 ** (h - b) * try_cost
    rebuild = k * (2**a - 2) * node  # the combiner rebuilds the 24 FORS paths from the public leaves
    print(f"  threshold, 2^{b} kept leaves (lifetime 2^{pruned_log2_sigs(b):.2f}): {fmt(mpc_hashes)} MPC hashes at keygen, public data "
          f"{public / 1e9:.3g} GB; signing: grinding {fmt(grind)} + FORS paths {fmt(rebuild)} permutations, no MPC")
    # Keygen with a DKG: n-party replicated-sharing MPC, t = (n + 1) / 2, hash-based F. Bytes per operator for
    # one FORS leaf and one 3-step WOTS chain, measured by `cargo run --release -p rss --bin bench`.
    measured = {3: (4553, 13625), 5: (5464, 16352), 7: (5855, 17522)}
    # Trusted dealer: F costs comb(n, t - 1) hashes per secret with the hash-based F.
    # The threshold PRF gives one secret per evaluation.
    leaf1 = v * derive + v * (q - 1) * step + wots_pk
    fors1 = k * (2**a * (derive + step) + (2**a - 2) * node)
    dealer = derive + 2**b * leaf1 + (2**b - 1) * node + (h - b) * (derive + node)
    dealer += 2**b * (fors1 + enc_fixed + enc_try / alpha + v * derive + T * step)
    for n, (per_leaf, per_chain) in measured.items():
        f = n // 2
        traffic = 2**b * (k * 2**a * per_leaf + v * per_chain)
        dealer_n = dealer + 2**b * (k * 2**a + v) * (math.comb(n, f) - 1)
        print(f"    {f + 1}-of-{n}: DKG traffic {traffic / 1e9:.3g} GB per operator; "
              f"trusted dealer {fmt(dealer_n)} permutations")

    # Spicy threshold signing: a signature reveals the chain values below the top, one per non-zero digit of the
    # 16 codewords. The ceremony hashes every chain of the forest 4 times (the secret, positions 1 to 3 published
    # under F, and the top) instead of every FORS leaf once; a 4-step chain is counted as a measured 3-step chain
    # plus one measured leaf hash. Public data: 4 values per chain.
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "formal", "sphincs", "scripts"))
    import forest_table
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    opened = trees * subs
    forest_chains = trees * tree_leaves * subs * keys * chains
    mpc_hashes_s = 2**b * (forest_chains * chain_steps + v * (q - 1))
    public_s = 2**b * (forest_chains * chain_steps * N + v * N + 4)
    print(f"  spicy threshold: {opened * sum(nonzero) / len(nonzero):.2f} values revealed per signature on average, at most "
          f"{opened * max(nonzero)} (FORS: {k}); 2^{b} kept leaves: {fmt(mpc_hashes_s)} MPC hashes at keygen, "
          f"public data {public_s / 1e9:.3g} GB")
    for n, (per_leaf, per_chain) in measured.items():
        traffic_s = 2**b * (forest_chains * (per_chain + per_leaf) + v * per_chain)
        print(f"    {n // 2 + 1}-of-{n}: DKG traffic {traffic_s / 1e9:.3g} GB per operator")

if __name__ == "__main__":
    main()
