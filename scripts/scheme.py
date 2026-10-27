#!/usr/bin/env python3
"""Sizes and compression counts of the leanSphincs candidate in its 24 configurations (leanSPHINCS.tex), with
its few-time signature (FTS) a two-level WOTS forest (spicy) or FORS (vanilla).

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

The vanilla FTS is FORS with k trees of height a and no root hash (the WOTS+C key signs the 2k nodes below
the roots), as in leanSphincs v1. For each configuration it is the FORS with the smallest signature among
those whose cover attack (fors_security.py) needs at least as many signatures as the forest's and whose
instance costs no more hashes to build than a forest; its lifetime is not proved in Lean.
"""

import argparse
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "formal", "sphincs", "scripts"))
import forest_certificates as fc
import forest_table
from fors_security import forgery_bits_exact

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

# WOTS+C: 64 chains of length 4, target sum 128. The forest: 8 coordinates; a coordinate is a top tree of
# height 4 over 16 super-children; a super-child hashes the top nodes of its 2 sub-trees of height 3 over 8
# WOTS children; a child is 6 chains of 4 steps under a leaf hash, signed at a codeword of digit sum 5.
V, Q, T = 64, 4, 128
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


def fors_log2_lifetime(h, b, a, k, level=127):
    """log2 of the FORS cover lifetime of a key keeping 2^b of 2^h instances: the signatures spread over the
    2^b instances, and a forger's digest must also land in the kept subtree (probability 2^(b - h))."""
    def ok(log2_q):
        return min(8 * N, (h - b) + forgery_bits_exact(log2_q, b, a, k)) >= level
    if not ok(0):
        return None
    lo, hi = 0.0, b + 14.0
    for _ in range(45):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if ok(mid) else (lo, mid)
    return lo


def fors_instance(a, k):
    """Hashes to build a FORS instance, one per call: a derivation per two leaves, a hash per leaf, the nodes."""
    return k * (2**a // 2 + 2**a + 2**a - 2)


FOREST_INSTANCE = COORDS * (SUPERS * (SUBS * (CHILDREN * (CHAINS // 2 + CHAINS * STEPS + 1) + CHILDREN - 2) + 1)
                            + SUPERS - 2)
_FORS = {}


def fors(h, shape, b):
    """(k, a) of the vanilla FTS of a configuration (see above)."""
    key = (h, shape, b)
    if key not in _FORS:
        target = math.log2(fc.attack(h, shape, b))
        bb = h if shape == "layered" else b
        def lives(a, k):
            life = fors_log2_lifetime(h, bb, a, k)
            return life is not None and life >= target
        best = None
        for a in range(2, 20):
            hi = FOREST_INSTANCE // fors_instance(a, 1)  # the most trees within the forest's instance cost
            if hi < 1 or not lives(a, hi):
                continue
            lo = 0  # the fewest trees that live long enough: lives(a, hi), not lives(a, lo)
            while hi - lo > 1:
                mid = (lo + hi) // 2
                lo, hi = (lo, mid) if lives(a, mid) else (mid, hi)
            cand = (hi * (1 + a), hi * a, hi, a)
            best = cand if best is None or cand < best else best
        _FORS[key] = best[2:]
    return _FORS[key]


def fts_bytes(variant, h, shape, b):
    if variant == "spicy":
        return FOREST_BYTES
    k, a = fors(h, shape, b)
    return k * (1 + a) * N


def size(h, shape, variant="spicy", b=None):
    return 16 + fts_bytes(variant, h, shape, b) + len(layers(h, shape)) * LAYER_BYTES + h * N


class Costs:
    """Per-call and per-component compressions of one hash."""

    def __init__(self, H, fts=None):
        """`fts` is None for the forest (spicy), or the (k, a) of FORS (vanilla)."""
        c = H.call
        self.H, self.fts = H, fts
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
        if fts is None:
            self.fts_sign, self.fts_verify, self.fts_nodes = self.forest_sign, COORDS * self.per_coord, COORDS * 2
            # opening the forest walks again the chains of the 16 WOTS keys it opens from their secrets, up to below
            # the tops (as the Rust signer does)
            self.fts_open = COORDS * SUBS * (CHAINS * STEPS - DIGIT_SUM) * self.step
        else:
            k, a = fts
            self.fts_sign = k * (2**a // 2 * self.derive + 2**a * self.step + (2**a - 2) * self.node)
            self.fts_verify, self.fts_nodes, self.fts_open = k * (self.step + (a - 1) * self.node), 2 * k, 0

    def digest_calls(self, h):
        """Hash calls of the digest: the index and the FTS fields, 256 bits per call."""
        bits = h + (COORDS * 26 if self.fts is None else self.fts[0] * self.fts[1])
        return -(-bits // 256)

    def encoding(self, message):
        """(verifier's cost, signer's whole blocks absorbed once, cost of one counter)"""
        fixed, per = self.H.midstate(message, 4)
        return self.H.call(message + 4), fixed, per

    def message_len(self, layer):
        """What the WOTS+C key of a layer (0 = bottom) signs: the FTS's top nodes, or a root."""
        return self.fts_nodes * N if layer == 0 else N

    def verify(self, h, shape):
        total = self.H.per_key + self.digest_calls(h) * self.digest + self.fts_verify
        for layer, height in enumerate(reversed(layers(h, shape))):
            enc, _, _ = self.encoding(self.message_len(layer))
            total += enc + ((Q - 1) * V - T) * self.step + self.wots_pk + height * self.node
        return total

    def wots_sign(self, layer):
        _, fixed, per = self.encoding(self.message_len(layer))
        return fixed + per / ALPHA + V // 2 * self.derive + T * self.step

    def counters(self, h, shape):
        """The WOTS+C counter searches of a signature (done in the clear by a threshold signer)."""
        return sum(self.wots_sign(layer) - V // 2 * self.derive - T * self.step for layer in range(len(layers(h, shape))))

    def keygen(self, h, shape, b):
        top, bb = layers(h, shape)[0], kept(h, shape, b)
        return (2 * self.H.per_key + self.derive + 2**bb * self.leaf + (2**bb - 1) * self.node
                + (top - bb) * (self.derive + self.node))

    # Threshold signing: what the MPC itself hashes. The chain secrets are outputs of F, which the operators
    # share locally (hash-based F); the WOTS public keys, the tree nodes and the forest key are hashed in the
    # clear once the chain ends are open, and the surrogates come from coin tossing. So the MPC runs only
    # the chain steps: Q - 1 per WOTS+C chain, STEPS per forest chain, and the commitment H(s).
    def mpc_keygen(self, h, shape, b):
        return 2 ** kept(h, shape, b) * V * (Q - 1) * self.step

    def mpc_prep(self, h, shape):
        if self.fts is None:
            fts = COORDS * SUPERS * SUBS * CHILDREN * CHAINS * STEPS * self.step
        else:  # one hash per FORS leaf
            fts = self.fts[0] * 2 ** self.fts[1] * self.step
        lower = sum(2**hl * V * (Q - 1) * self.step for hl in layers(h, shape)[1:])
        return fts + lower + self.step

    # The hardware wallet: preparing an instance (its forest, the lower trees, the WOTS+C signatures and the
    # path in the kept subtree or top layer, with a 16 KiB cache); online, re-deriving the opened chain values
    # and recovering the forest key from the opening, to check the host's nodes against its hash.
    def ledger_prep(self, h, shape, b):
        ls = layers(h, shape)
        lower = sum(2**hl * self.leaf + (2**hl - 1) * self.node for hl in ls[1:])
        return (self.fts_sign + lower + sum(self.wots_sign(layer) for layer in range(len(ls)))
                + self.tree_cost(kept(h, shape, b), 16 * 1024 // N))

    def device_online(self):
        if self.fts is None:
            opened = COORDS * SUBS * (CHAINS // 2 * self.derive + (CHAINS * STEPS - DIGIT_SUM) * self.step)
        else:  # the k opened secrets
            opened = self.fts[0] * self.derive
        return opened + self.fts_verify + 1

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
        # the landing digest is computed once more in full, then the FTS instance is built and opened
        total = self.rnd + self.digest_fixed + grind + self.digest_calls(h) * self.digest + self.fts_sign + self.fts_open
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
    ap.add_argument("--pruned", type=int, nargs="+", default=[12, 20], help="log2 kept leaves of pruned keys")
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
                    k, a = fors(h, shape, b)
                    CV = Costs(H, (k, a))
                    signs, signs_v = {}, {}
                    for kib in (16, 1024, 16 * 1024):
                        base, grind, tree = C.sign(h, shape, b, kib * 1024)
                        signs[str(kib)] = round(base + tree)
                        base, grind, tree = CV.sign(h, shape, b, kib * 1024)
                        signs_v[str(kib)] = round(base + tree)
                    life_v = fors_log2_lifetime(h, h if shape == "layered" else b, a, k)
                    out["configs"].append(dict(hash=H.name, h=h, shape=shape, b=b, layers=list(layers(h, shape)),
                                               size=size(h, shape), verify=C.verify(h, shape),
                                               keygen=round(C.keygen(h, shape, b)), sign=signs,
                                               grind=round(2 ** (h - b)) if shape == "pruned" else 1,
                                               lifetime=proved, attack=attack,
                                               vanilla=dict(k=k, a=a, size=size(h, shape, "vanilla", b),
                                                            verify=CV.verify(h, shape), sign=signs_v,
                                                            attack=round(2**life_v))))
    for H in HASHES:
        C = Costs(H)
        ands = ANDS[H.name]
        for h in HEIGHTS:
            for shape, b in [("pruned", bb) for bb in PRUNED] + [("layered", h)]:
                ls = layers(h, shape)
                keygen, prep = C.mpc_keygen(h, shape, b), C.mpc_prep(h, shape)
                # the hardware wallet computes the whole instance, and signs it with WOTS+C
                lower = sum(2**hl * C.leaf + (2**hl - 1) * C.node for hl in ls[1:])
                ledger = C.ledger_prep(h, shape, b)
                CV = Costs(H, fors(h, shape, b))
                prep_v = CV.mpc_prep(h, shape)
                vanilla = dict(prep=round(prep_v), prep_mb=prep_v * ands * BITS_PER_AND / 8 / 1e6,
                               ledger_prep=math.ceil(CV.ledger_prep(h, shape, b)), device_online=CV.device_online())
                out["threshold"].append(dict(hash=H.name, h=h, shape=shape, b=b, lifetime=lifetimes(h, shape, b)[0],
                                             keygen=round(keygen), prep=round(prep), grind=2**h // THRESHOLD_PREPARED,
                                             and_depth=and_depth(H.name), keygen_rounds=rounds(H.name, Q - 1), prep_rounds=rounds(H.name, STEPS),
                                             ledger_prep=math.ceil(ledger), device_online=C.device_online(),
                                             keygen_gb=keygen * ands * BITS_PER_AND / 8 / 1e9,
                                             prep_mb=prep * ands * BITS_PER_AND / 8 / 1e6, vanilla=vanilla))
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    out["rates"] = DEVICES
    out["wallet"] = dict(prepared=THRESHOLD_PREPARED, ledger_prepared={h: wallet_prepared(h) for h in HEIGHTS},
                         ledger_grind={h: 2**h // wallet_prepared(h) for h in HEIGHTS}, stark_verify=STARK_VERIFY, stark_verify_s=STARK_VERIFY_SECONDS, host_rate=HOST_RATE, device_rate=DEVICE_RATE,
                         opened_avg=COORDS * SUBS * sum(nonzero) / len(nonzero), opened_max=COORDS * SUBS * max(nonzero))
    return out


# Threshold signing (DKG, no dealer) and hardware wallets, with Keccak-256. The MPC builds the XMSS part only
# (the top layer, or the kept subtree); before a message it prepares a random instance (its forest key,
# WOTS+C signatures, lower trees and path), one per signature, and online the signers grind onto it in the
# clear, about 2^h attempts (cheap in the clear), and open only the forest chain values the message selects.
THRESHOLD_PREPARED = 1
# The hardware wallet prepares at least PREPARED instances, and enough that the host grinds and proves at most
# HOST_GRIND digests.
PREPARED = 16
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


def and_depth(name):
    """AND-depth of one compression in the circuits counted in ANDS (XOR and rotations are free): Keccak-f has
    one layer of AND gates per round; for BLAKE2s and SHA-256, the depth of every bit is followed through the
    ripple-carry adders, c[i+1] = c[i] ^ ((a[i] ^ c[i]) & (b[i] ^ c[i]))."""
    if name == "Keccak-256":
        return 24
    z = [0] * 32
    def add(a, b):
        out, c = [], 0
        for i in range(32):
            out.append(max(a[i], b[i], c))
            c = max(a[i], b[i], c) + 1
        return out
    def xor(*ws): return [max(t) for t in zip(*ws)]
    def rot(w, r): return w[r:] + w[:r]
    def shr(w, r): return w[r:] + [0] * r
    def and_(a, b): return [max(x, y) + 1 for x, y in zip(a, b)]
    if name == "BLAKE2s":
        v = [z] * 16
        def g(a, b, c, d):
            for r1, r2 in ((16, 12), (8, 7)):
                v[a] = add(add(v[a], v[b]), z); v[d] = rot(xor(v[d], v[a]), r1)
                v[c] = add(v[c], v[d]); v[b] = rot(xor(v[b], v[c]), r2)
        for _ in range(10):
            for q in ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
                      (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)):
                g(*q)
        return max(map(max, v))
    w = [z] * 16
    for t in range(16, 64):
        s0 = xor(rot(w[t - 15], 7), rot(w[t - 15], 18), shr(w[t - 15], 3))
        s1 = xor(rot(w[t - 2], 17), rot(w[t - 2], 19), shr(w[t - 2], 10))
        w.append(add(add(add(s1, w[t - 7]), s0), w[t - 16]))
    a = b = c = d = e = f = g_ = h = z
    for t in range(64):
        t1 = add(add(add(h, xor(rot(e, 6), rot(e, 11), rot(e, 25))), xor(g_, and_(e, xor(f, g_)))), w[t])
        t2 = add(xor(rot(a, 2), rot(a, 13), rot(a, 22)), xor(and_(xor(a, b), xor(a, c)), a))
        h, g_, f, e, d, c, b, a = g_, f, e, add(d, t1), c, b, a, add(t1, t2)
    return max(map(max, (a, b, c, d, e, f, g_, h)))


# Communication rounds of the MPC: one per layer of AND gates, the hash chains of every key in parallel and their
# steps one after another (Q - 1 at key generation, STEPS for the forest in preprocessing), then one to open.
def rounds(name, steps):
    return steps * and_depth(name) + 1
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
            keygen, prep = C.mpc_keygen(h, shape, b), C.mpc_prep(h, shape)
            lower = sum(2**hl * C.leaf + (2**hl - 1) * C.node for hl in ls[1:])
            ledger = C.ledger_prep(h, shape, b)
            gb = keygen * KECCAK_ANDS * BITS_PER_AND / 8 / 1e9
            pm = prep * KECCAK_ANDS * BITS_PER_AND / 8 / 1e6
            label = f"pruned b={b}" if shape == "pruned" else "layered"
            print(f"  h={h} {label}: keygen MPC {fmt(keygen)} permutations ({gb:.3g} GB per operator); "
                  f"preprocessing {fmt(prep)} per signature ({pm:.0f} MB; on a hardware wallet, which also signs with "
                  f"WOTS+C, {fmt(ledger)}); online grinding {fmt(2 ** h / THRESHOLD_PREPARED)} attempts")
    # The alternative for a pruned key: every forest of the kept subtree prepared at key generation, once.
    for H in HASHES:
        C = Costs(H)
        forests = 2**12 * (C.mpc_prep(24, "pruned") - C.step) * ANDS[H.name] * BITS_PER_AND / 8 / 1e12
        lifetime = lifetimes(24, "pruned", 12)[0] * C.mpc_prep(24, "pruned") * ANDS[H.name] * BITS_PER_AND / 8 / 1e12
        # rounded against the alternative: its cost up, the preprocessing it saves down
        print(f"threshold, every forest at keygen (h=24, b=12, {H.name}): {math.ceil(forests * 100) / 100:.2f} TB per operator "
              f"once, against {math.floor(lifetime * 10) / 10:.1f} TB of preprocessing over the lifetime")
    print(f"hardware wallet: the device prepares max({PREPARED}, 2^h / 2^{HOST_GRIND.bit_length() - 1}) instances and the host grinds "
          f"2^h / that many digests ({', '.join(f'h={h}: {wallet_prepared(h)} prepared, {fmt(2 ** h / wallet_prepared(h))} digests, '
          f'{2 ** h / wallet_prepared(h) / HOST_RATE:.2g} s to prove' for h in heights)});"
          f" the device verifies the STARK in about {fmt(STARK_VERIFY)} compressions, counted as {STARK_VERIFY_SECONDS} s")

if __name__ == "__main__":
    main()
