#!/usr/bin/env python3
"""Sizes and compression counts of the leanSphincs candidate in its 24 configurations (leanSPHINCS.tex).

Three toggles: the height h (22, 24, 26, 28: about 2^26, 2^28, 2^30, 2^32 signatures), the shape
(pruned: one tree of height h of which the key builds a kept subtree of 2^b leaves, b = h being the
full key, the signer grinding the randomizer into it; layered: a hypertree whose key builds the top
layer only) and the hash. Every call hashes P (16 B) || address (16 B) || payload, each hash with its
own layout:

  Keccak-256  P inline; l bytes cost floor(l / 136) + 1 Keccak-f permutations.
  BLAKE2s     P inline; l bytes cost ceil(l / 64) compressions (no padding byte), so a node,
              P || address || left || right, is exactly one 64-byte block.
  SHA-256     P alone in a zero-padded 64-byte block, compressed once per key; the l bytes after it cost
              ceil((l + 9) / 64) compressions (the 0x80 byte and the 8-byte length).

The digest input puts the randomizer alone in the last block (Keccak-256: the whole 80-byte input is one
block; SHA-256: 16 zero bytes before it), and the WOTS+C encoding puts its counter in the last block:
a grinding attempt and a counter cost one compression each, with every hash.

The lifetimes are the ones proved in Lean (formal/sphincs/scripts/forest_certificates.py, PARAMS and
LAYERED) and, for comparison, the cover attack they are measured against (ATTACK, from forest_attack.py).
The same figures are pinned by the Rust tests (crates/sphincs, `Config::verify_compressions`).
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
P_LEN, ADDR = 16, 16
HEIGHTS = (22, 24, 26, 28)
LAYERED = {22: (10, 6, 6), 24: (12, 6, 6), 26: (8, 6, 6, 6), 28: (10, 6, 6, 6)}  # top layer first
PRUNED = (8, 10, 12, 13, 14, 20)  # kept subtree heights b < h with a certificate, besides b = h


class Hash:
    def __init__(self, name, block, inline_p, padding, digest_pad):
        self.name, self.block, self.inline_p, self.padding, self.digest_pad = name, block, inline_p, padding, digest_pad
        self.prefix = P_LEN + ADDR if inline_p else ADDR  # hashed per call before the payload
        self.per_key = 0 if inline_p else 1  # SHA-256's block of P

    def cost(self, length):
        """Compressions of `length` bytes after the cached part."""
        if self.name == "Keccak-256":
            return length // self.block + 1
        return max(1, -(-(length + self.padding) // self.block))

    def call(self, payload):
        return self.cost(self.prefix + payload)

    def midstate(self, fixed, tail):
        """(whole blocks of prefix || fixed, absorbed once; cost of the rest with each tail)"""
        n = self.prefix + fixed
        return n // self.block, self.cost(n % self.block + tail)


HASHES = [Hash("Keccak-256", 136, True, 0, 0), Hash("BLAKE2s", 64, True, 0, 0), Hash("SHA-256", 64, False, 9, 16)]

# WOTS+C: 64 chains of length 4, target sum 123. The forest: 8 coordinates; a coordinate is a top tree of
# height 4 over 16 super-children; a super-child hashes the top nodes of its 2 sub-trees of height 3 over 8
# WOTS children; a child is 6 chains of 4 steps under a leaf hash, signed at a codeword of digit sum 5.
V, Q, T = 64, 4, 123
COORDS, SUPERS, SUBS, CHILDREN, CHAINS, STEPS, DIGIT_SUM = 8, 16, 2, 8, 6, 4, 5
SUB_PATH, TOP_PATH = 3, 4
VALUES = SUBS * (CHAINS + SUB_PATH) + TOP_PATH  # per coordinate
FOREST_BYTES = COORDS * VALUES * N
LAYER_BYTES = 4 + V * N  # counter and chain values; the path adds h_l nodes


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


ALPHA = n_sum(V, Q, T) / Q**V  # probability that a counter gives sum T


def layers(h, shape):
    """Layer heights, top first."""
    return LAYERED[h] if shape == "layered" else (h,)


def kept(h, shape, b):
    return LAYERED[h][0] if shape == "layered" else b


def size(h, shape):
    return 16 + FOREST_BYTES + len(layers(h, shape)) * LAYER_BYTES + h * N


class Costs:
    """Per-call and per-component compressions of one hash."""

    def __init__(self, H):
        c = H.call
        self.H = H
        self.derive, self.step, self.node = c(32), c(N), c(2 * N)
        self.wots_pk, self.child_leaf, self.super_hash = c(V * N), c(CHAINS * N), c(SUBS * 2 * N)
        self.rnd = c(32 + 32)  # S || m: R_0 and delta
        self.digest = c(32 + H.digest_pad + 16)  # m || (pad) || rho
        self.digest_fixed, self.attempt = H.midstate(32 + H.digest_pad, 16)
        self.leaf = V // 2 * self.derive + V * (Q - 1) * self.step + self.wots_pk
        wots_key = CHAINS // 2 * self.derive + CHAINS * STEPS * self.step + self.child_leaf
        subtree = CHILDREN * wots_key + (CHILDREN - 2) * self.node
        coord = SUPERS * (SUBS * subtree + self.super_hash) + (SUPERS - 2) * self.node
        self.forest_sign = COORDS * coord
        self.per_coord = (SUBS * (DIGIT_SUM * self.step + self.child_leaf + (SUB_PATH - 1) * self.node)
                          + self.super_hash + (TOP_PATH - 1) * self.node)

    def encoding(self, message):
        """(verifier's cost, signer's whole blocks absorbed once, cost of one counter)"""
        fixed, per = self.H.midstate(message, 4)
        return self.H.call(message + 4), fixed, per

    def message_len(self, layer):
        """What the WOTS+C key of a layer (0 = bottom) signs: the 16 forest nodes, or a root."""
        return COORDS * 2 * N if layer == 0 else N

    def verify(self, h, shape):
        total = self.H.per_key + self.digest + COORDS * self.per_coord
        for layer, height in enumerate(reversed(layers(h, shape))):
            enc, _, _ = self.encoding(self.message_len(layer))
            total += enc + ((Q - 1) * V - T) * self.step + self.wots_pk + height * self.node
        return total

    def wots_sign(self, layer):
        _, fixed, per = self.encoding(self.message_len(layer))
        return fixed + per / ALPHA + V // 2 * self.derive + T * self.step

    def keygen(self, h, shape, b):
        top, bb = layers(h, shape)[0], kept(h, shape, b)
        return (2 * self.H.per_key + self.derive + 2**bb * self.leaf + (2**bb - 1) * self.node
                + (top - bb) * (self.derive + self.node))

    def tree_cost(self, height, cache_nodes):
        """Per-signature work in a tree of 2^height leaves: the best of keeping one level c (rebuild the 2^c
        leaves below the cached node, hash the cached level up) or keeping every level >= c."""
        if 2 ** (height + 1) - 1 <= cache_nodes:
            return 0
        best = 2**height * self.leaf + (2**height - 1) * self.node
        for c in range(1, height + 1):
            below = 2**c * self.leaf + (2**c - 1) * self.node
            if 2 ** (height - c + 1) - 1 <= cache_nodes:
                best = min(best, below)
            if 2 ** (height - c) <= cache_nodes:
                best = min(best, below + (2 ** (height - c) - 1) * self.node)
        return best

    def sign(self, h, shape, b, cache_bytes):
        """Expected compressions of one signature with a cache of the top tree's nodes."""
        ls = layers(h, shape)
        bb = kept(h, shape, b)
        grind = 2 ** (h - bb) * self.attempt if shape == "pruned" else self.attempt
        total = self.rnd + self.digest_fixed + grind + self.digest - self.attempt + self.forest_sign
        total += sum(self.wots_sign(layer) for layer in range(len(ls)))
        total += sum(2**hl * self.leaf + (2**hl - 1) * self.node for hl in ls[1:])  # the lower trees
        return total, grind, self.tree_cost(bb, cache_bytes // N)


def fmt(x):
    for dv, u in ((1e9, "B"), (1e6, "M"), (1e3, "K")):
        if x >= dv * 0.9995:
            return f"{x / dv:.3g}{u}"
    return f"{x:.0f}"


def lifetimes(h, shape, b):
    """(proved in Lean, cover attack), None when not certified."""
    return fc.lifetime(h, shape, b), fc.attack(h, shape, b)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--hash", choices=[H.name for H in HASHES], nargs="+", default=[H.name for H in HASHES])
    ap.add_argument("--h", type=int, nargs="+", default=list(HEIGHTS), choices=HEIGHTS)
    ap.add_argument("--pruned", type=int, nargs="+", default=[13, 20], help="log2 kept leaves of pruned keys")
    ap.add_argument("--cache-kib", type=float, nargs="+", default=[16, 1024], help="signer cache sizes (KiB)")
    ap.add_argument("--table", action="store_true", help="one line per configuration: size, verification, lifetime")
    x = ap.parse_args()
    hashes = [H for H in HASHES if H.name in x.hash]

    if x.table:
        print("hash        h  shape          size  verify  keygen    proved N   (cover attack)")
        for H in hashes:
            C = Costs(H)
            for h in x.h:
                for shape, b in [("pruned", h)] + [("pruned", bb) for bb in x.pruned] + [("layered", None)]:
                    proved, attack = lifetimes(h, shape, b)
                    label = shape if shape == "layered" else ("full" if b == h else f"pruned {b}")
                    life = "not certified" if proved is None else f"{proved:>11,} ({fmt(attack) if attack else '?'})"
                    print(f"{H.name:<10} {h:>2}  {label:<10} {size(h, shape):>8,} {C.verify(h, shape):>7} "
                          f"{fmt(C.keygen(h, shape, b)):>7}  {life}")
        return

    print(f"leanSphincs candidate: a two-level WOTS forest of {COORDS} coordinates under WOTS+C with {V} chains of "
          f"length {Q} and T={T}; {math.log2(n_sum(V, Q, T)):.2f} bits of valid encodings, expected "
          f"{1 / ALPHA:.0f} counters; costs in compressions (Keccak-f permutations for Keccak-256)")
    for H in hashes:
        C = Costs(H)
        enc0, fixed0, _ = C.encoding(C.message_len(0))
        enc1, _, _ = C.encoding(C.message_len(1))
        print(f"\n{H.name}: per call derive {C.derive}, chain {C.step}, node {C.node}, forest WOTS leaf "
              f"{C.child_leaf}, super-child {C.super_hash}, WOTS+C leaf {C.wots_pk}, digest {C.digest} "
              f"({C.digest_fixed} once + {C.attempt} per attempt), encoding of the forest key {enc0} ({fixed0} once + "
              f"1 per counter), of a root {enc1}" + (", the block of P once per key" if H.per_key else ""))
        print(f"  forest: {C.per_coord} per coordinate to verify, {fmt(C.forest_sign)} per instance to sign")
        for h in x.h:
            for shape in ("pruned", "layered"):
                ls = layers(h, shape)
                bs = [h] + x.pruned if shape == "pruned" else [None]
                desc = "one tree" if shape == "pruned" else "layers " + "+".join(map(str, ls))
                print(f"  h={h} {shape} ({desc}): signature {size(h, shape):,} B, verification {C.verify(h, shape)}")
                for b in bs:
                    proved, attack = lifetimes(h, shape, b)
                    life = "not certified" if proved is None else f"lifetime {fmt(proved)} (cover attack {fmt(attack)})"
                    signs = []
                    for kib in x.cache_kib:
                        base, grind, tree = C.sign(h, shape, b, int(kib * 1024))
                        signs.append(f"{fmt(base + tree)} with {kib:g} KiB")
                    label = "" if b is None else ("full key: " if b == h else f"pruned b={b}: ")
                    print(f"    {label}{life}, keygen {fmt(C.keygen(h, shape, b))}, signing {', '.join(signs)}")

    # Threshold signing (DKG, no dealer): the MPC builds the XMSS part only (the top layer, or the kept subtree);
    # before a message it prepares 16 random instances (their forest keys, WOTS+C signatures and paths), and
    # online it grinds onto one of the 16 and opens only the forest chains the message selects.
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    opened = COORDS * SUBS
    print(f"\nthreshold: {opened * sum(nonzero) / len(nonzero):.2f} forest chain values opened per signature on "
          f"average, at most {opened * max(nonzero)}; online grinding onto 16 prepared instances: about 2^h / 16 "
          f"digest attempts ({', '.join(f'h={h}: {fmt(2 ** h / 16)}' for h in x.h)})")


if __name__ == "__main__":
    main()
