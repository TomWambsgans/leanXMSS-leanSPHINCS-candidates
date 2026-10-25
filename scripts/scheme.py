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
LAYERED = {22: (10, 6, 6), 24: (12, 6, 6), 26: (12, 7, 7), 28: (12, 8, 8)}  # top layer first
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
    ap.add_argument("--json", action="store_true", help="every figure of the site, as JSON (site/data.json)")
    x = ap.parse_args()
    hashes = [H for H in HASHES if H.name in x.hash]

    if x.json:
        import json
        print(json.dumps(site_data(), indent=1))
        return

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

    print()
    threshold(x.h)


def site_data():
    """Every configuration (height, shape, kept subtree, hash) with its figures, and the threshold and hardware-wallet
    figures, for the site."""
    out = {"configs": [], "threshold": [], "wallet": {}}
    for H in HASHES:
        C = Costs(H)
        for h in HEIGHTS:
            for shape in ("pruned", "layered"):
                for b in ([h] + list(PRUNED) if shape == "pruned" else [h]):
                    proved, attack = lifetimes(h, shape, b)
                    signs = {}
                    for kib in (16, 1024, 16 * 1024):
                        base, grind, tree = C.sign(h, shape, b, kib * 1024)
                        signs[str(kib)] = round(base + tree)
                    out["configs"].append(dict(hash=H.name, h=h, shape=shape, b=b, layers=list(layers(h, shape)),
                                               size=size(h, shape), verify=C.verify(h, shape),
                                               keygen=round(C.keygen(h, shape, b)), sign=signs,
                                               grind=round(2 ** (h - b)) if shape == "pruned" else 1,
                                               lifetime=proved, attack=attack))
    for H in HASHES:
        C = Costs(H)
        ands = ANDS[H.name]
        for h in HEIGHTS:
            for shape, b in [("pruned", bb) for bb in PRUNED] + [("layered", h)]:
                ls = layers(h, shape)
                keygen = C.keygen(h, shape, b)
                lower = sum(2**hl * C.leaf + (2**hl - 1) * C.node for hl in ls[1:])
                prep = C.forest_sign + lower + len(ls) * (V // 2 * C.derive + T * C.step)
                out["threshold"].append(dict(hash=H.name, h=h, shape=shape, b=b, lifetime=lifetimes(h, shape, b)[0],
                                             keygen=round(keygen), prep=round(prep), grind=2**h // PREPARED,
                                             keygen_gb=keygen * ands * BITS_PER_AND / 8 / 1e9,
                                             prep_mb=prep * ands * BITS_PER_AND / 8 / 1e6))
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    out["rates"] = DEVICES
    out["wallet"] = dict(prepared=PREPARED, ledger_prepared={h: wallet_prepared(h) for h in HEIGHTS},
                         ledger_grind={h: 2**h // wallet_prepared(h) for h in HEIGHTS}, stark_verify=STARK_VERIFY, stark_verify_s=STARK_VERIFY_SECONDS, host_rate=HOST_RATE, device_rate=DEVICE_RATE,
                         opened_avg=COORDS * SUBS * sum(nonzero) / len(nonzero), opened_max=COORDS * SUBS * max(nonzero))
    return out


# Threshold signing (DKG, no dealer) and hardware wallets, with Keccak-256. The MPC builds the XMSS part only
# (the top layer, or the kept subtree); before a message it prepares random instances (their forest keys,
# WOTS+C signatures, lower trees and paths), one per signature, and online the signers grind onto one of
# PREPARED instances in the clear and open only the forest chain values the message selects.
PREPARED = 16
# The hardware wallet prepares enough instances that the host grinds and proves at most HOST_GRIND digests.
HOST_GRIND = 2**20


def wallet_prepared(h):
    return max(PREPARED, 2**h // HOST_GRIND)

KECCAK_ANDS = 36_300  # AND gates of one Keccak-f[1600] call with a public part and a truncated output
# AND gates of one compression in a binary MPC: Keccak-f as above; SHA-256, the Bristol-format circuit (22,573);
# BLAKE2s, 10 rounds of 8 G functions of 6 additions modulo 2^32 at 31 AND gates each (14,880).
ANDS = {"Keccak-256": KECCAK_ANDS, "SHA-256": 22_573, "BLAKE2s": 10 * 8 * 6 * 31}
# Traffic of honest-majority MPC with malicious security (with abort), per AND gate and per operator: about 1 bit,
# the semi-honest cost of replicated sharing among three parties (Araki et al., CCS 2016), the malicious check
# being sublinear (Boyle et al., CCS 2019; Goyal and Song, CRYPTO 2020).
BITS_PER_AND = 1
STARK_VERIFY = 10_000  # compressions to verify the STARK of a least grinding index on the device
STARK_VERIFY_SECONDS = 3  # assumed time of that verification on the device, whatever the hash
HOST_RATE = 2**19  # hashes per second the host proves in a STARK (the hash of the configuration): 2 s per 2^20
DEVICE_RATE = 5.8e3  # Keccak-f permutations per second of a Ledger Nano S+ (hwbench)

# Compressions per second of each device, per hash. The Ledger Nano S+ is measured for each hash (hwbench:
# github.com/TomWambsgans/hardware-wallet-benchmark). The CPUs are given for Keccak-f (a laptop and a server,
# all cores, 2^27 and 2^29 per second); the other hashes scale by the single-core ratio measured with
# `openssl speed -bytes 16384 -evp` on an AMD Ryzen 7 PRO 8700GE (SHA-NI): SHA-256 2.43 GB/s, BLAKE2s
# 0.731 GB/s, SHA3-256 0.666 GB/s, i.e. 38.0M, 11.4M and 4.90M compressions (64, 64 and 136 bytes) per second.
# On the CPUs, SHA-256 is counted at the BLAKE2s rate.
OPENSSL = {"Keccak-256": 666.18e6 / 136, "BLAKE2s": 730.52e6 / 64, "SHA-256": 730.52e6 / 64}
DEVICES = {
    "Ledger Nano S+": {"Keccak-256": 5.8e3, "BLAKE2s": 32.6e3, "SHA-256": 23.6e3},
    "laptop": {name: 2**27 * OPENSSL[name] / OPENSSL["Keccak-256"] for name in OPENSSL},
    "server": {name: 2**29 * OPENSSL[name] / OPENSSL["Keccak-256"] for name in OPENSSL},
}


def threshold(heights):
    C = Costs(HASHES[0])
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    opened = COORDS * SUBS
    print(f"threshold (Keccak-256): {opened * sum(nonzero) / len(nonzero):.2f} forest chain values opened per "
          f"signature on average, at most {opened * max(nonzero)}")
    for h in heights:
        for shape, b in (("pruned", 12), ("layered", None)):
            ls = layers(h, shape)
            keygen = C.keygen(h, shape, b)
            lower = sum(2**hl * C.leaf + (2**hl - 1) * C.node for hl in ls[1:])
            prep = C.forest_sign + lower + len(ls) * (V // 2 * C.derive + T * C.step)
            gb = keygen * KECCAK_ANDS * BITS_PER_AND / 8 / 1e9
            pm = prep * KECCAK_ANDS * BITS_PER_AND / 8 / 1e6
            label = f"pruned b={b}" if shape == "pruned" else "layered"
            print(f"  h={h} {label}: keygen MPC {fmt(keygen)} permutations ({gb:.3g} GB per operator); "
                  f"preprocessing {fmt(prep)} per signature ({pm:.0f} MB); online grinding {fmt(2 ** h / PREPARED)} attempts")
    print(f"hardware wallet: the device prepares max({PREPARED}, 2^h / 2^{HOST_GRIND.bit_length() - 1}) instances and the host grinds "
          f"2^h / that many digests ({', '.join(f'h={h}: {wallet_prepared(h)} prepared, {fmt(2 ** h / wallet_prepared(h))} digests, '
          f'{2 ** h / wallet_prepared(h) / HOST_RATE:.2g} s to prove' for h in heights)});"
          f" the device verifies the STARK in about {fmt(STARK_VERIFY)} compressions, counted as {STARK_VERIFY_SECONDS} s")

if __name__ == "__main__":
    main()
