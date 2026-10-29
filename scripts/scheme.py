#!/usr/bin/env python3
"""Sizes and compression counts of the leanSphincs candidate in its 60 configurations (leanSPHINCS.tex).

Four toggles: the lifetime (about 2^24, 2^26, ..., 2^32 signatures), the shape (pruned: one tree of height
h = log2(lifetime) - 4 of which the key builds a kept subtree of 2^b leaves, b = h being the full key, the
signer grinding the randomizer into it; layered: a hypertree of height 24 to 28 whose key builds the top layer
only, UNIFORM), the hash and the few-time signature (FTS): a two-level WOTS forest or FORS. Every call
hashes P (16 B) || address (16 B) || payload, each hash with its own layout:

  Keccak-256  P inline; l bytes cost floor(l / 136) + 1 Keccak-f permutations.
  BLAKE2s     P inline; l bytes cost ceil(l / 64) compressions (no padding byte), so a node,
              P || address || left || right, is exactly one 64-byte block.
  SHA-256     P alone in a zero-padded 64-byte block, compressed once per key; the l bytes after it cost
              ceil((l + 9) / 64) compressions (the 0x80 byte and the 8-byte length).

The digest input puts the randomizer alone in the last block (Keccak-256: the whole 80-byte input is one
block; SHA-256: 16 zero bytes before it), and the WOTS+C encoding puts its counter in the last block:
a grinding attempt and a counter cost one compression each, with every hash.

The lifetimes are the ones proved in Lean (the PARAMS and LAYERED tables of
formal/sphincs/scripts/forest_certificates.py and fors_certificates.py) and, for comparison, the cover
attack they are measured against (ATTACK).
The forest's sizes and verification costs are also pinned by the Rust tests (crates/sphincs,
`Config::verify_compressions`).

The FORS FTS has k trees of height a and no root hash (the WOTS+C key signs the 2k nodes below
the roots): k = 24, a = 10 for every pruned key, the fewest trees whose proved limit for the full key still
reaches 2^(h+4) signatures, so that verification does not depend on the pruning. A layered key is at least
24 high: at 2^24 and 2^26 signatures its instances are used fewer times, and it takes a lighter FTS (UNIFORM):
FORS 19x9 and 23x9, a forest of 6 and 7 coordinates.
"""

import argparse
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "formal", "sphincs", "scripts"))
import forest_certificates as fc
import fors_certificates as vc
import forest_table
from fors_security import forgery_bits_exact

N = 16  # bytes per hash value
P_LEN, ADDR = 16, 16
LIFETIMES = (24, 26, 28, 30, 32)  # log2 of the nominal lifetime
HEIGHTS = (20, 22, 24, 26, 28)  # the pruned key of each lifetime: h = L - 4
LAYERED = {24: (10, 7, 7), 26: (10, 8, 8), 28: (10, 9, 9)}  # top layer first
PRUNED = (8, 10, 12, 13, 14, 20)  # kept subtree heights b < h with a certificate, besides b = h
# The layered key of each lifetime: (height, forest coordinates, FORS (k, a)).
UNIFORM = {24: (24, 6, (19, 9)), 26: (24, 7, (23, 9)), 28: (24, 8, (24, 10)), 30: (26, 8, (24, 10)), 32: (28, 8, (24, 10))}


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


FORS_HEIGHT = 10
FORS_TREES = 24


def fors(h, shape, b):
    """(k, a) of the FORS FTS of a pruned key, and of the layered keys from 2^28 on (UNIFORM has the others)."""
    return FORS_TREES, FORS_HEIGHT


def fts_bytes(variant, h, shape, b, coords=COORDS, ka=None):
    if variant == "forest":
        return coords * VALUES * N
    k, a = ka or fors(h, shape, b)
    return k * (1 + a) * N


def size(h, shape, variant="forest", b=None, coords=COORDS, ka=None):
    return 16 + fts_bytes(variant, h, shape, b, coords, ka) + len(layers(h, shape)) * LAYER_BYTES + h * N


class Costs:
    """Per-call and per-component compressions of one hash."""

    def __init__(self, H, fts=None, coords=COORDS):
        """`fts` is None for the forest (of `coords` coordinates), or the (k, a) of FORS."""
        c = H.call
        self.H, self.fts, self.coords = H, fts, coords
        self.derive, self.step, self.node = c(32), c(N), c(2 * N)
        self.wots_pk, self.child_leaf, self.super_hash = c(V * N), c(CHAINS * N), c(SUBS * 2 * N)
        self.rnd = c(32 + 32)  # S || m: R_0 and delta
        self.digest = c(32 + H.digest_pad + 16)  # m || (pad) || rho
        self.digest_fixed, self.attempt = H.midstate(32 + H.digest_pad, 16)
        self.leaf = V // 2 * self.derive + V * (Q - 1) * self.step + self.wots_pk
        wots_key = CHAINS // 2 * self.derive + CHAINS * STEPS * self.step + self.child_leaf
        subtree = CHILDREN * wots_key + (CHILDREN - 2) * self.node
        coord = SUPERS * (SUBS * subtree + self.super_hash) + (SUPERS - 2) * self.node
        self.forest_sign = coords * coord
        self.per_coord = (SUBS * (DIGIT_SUM * self.step + self.child_leaf + (SUB_PATH - 1) * self.node)
                          + self.super_hash + (TOP_PATH - 1) * self.node)
        if fts is None:
            self.fts_sign, self.fts_verify, self.fts_nodes = self.forest_sign, coords * self.per_coord, coords * 2
            # opening the forest walks again the chains of the 2 * coords WOTS keys it opens from their secrets, up to below
            # the tops (as the Rust signer does)
            self.fts_open = coords * SUBS * (CHAINS * STEPS - DIGIT_SUM) * self.step
        else:
            k, a = fts
            self.fts_sign = k * (2**a // 2 * self.derive + 2**a * self.step + (2**a - 2) * self.node)
            self.fts_verify, self.fts_nodes, self.fts_open = k * (self.step + (a - 1) * self.node), 2 * k, 0

    def digest_calls(self, h):
        """Hash calls of the digest: the index and the FTS fields, 256 bits per call."""
        bits = h + (self.coords * 26 if self.fts is None else self.fts[0] * self.fts[1])
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
            fts = self.coords * SUPERS * SUBS * CHILDREN * CHAINS * STEPS * self.step
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
            opened = self.coords * SUBS * (CHAINS // 2 * self.derive + (CHAINS * STEPS - DIGIT_SUM) * self.step)
        else:  # the k opened secrets
            opened = self.fts[0] * self.derive
        return opened + self.fts_verify + self.H.call(self.fts_nodes * N)  # and the hash of the FTS key

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
    """(proved in Lean, cover attack) of a pruned forest key, None when not certified."""
    return fc.lifetime(h, shape, b), fc.attack(h, shape, b)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--hash", choices=[H.name for H in HASHES], nargs="+", default=[H.name for H in HASHES])
    ap.add_argument("--lt", type=int, nargs="+", default=list(LIFETIMES), choices=LIFETIMES, help="log2 lifetimes")
    ap.add_argument("--pruned", type=int, nargs="+", default=[12, 20], help="log2 kept leaves of pruned keys")
    ap.add_argument("--cache-kib", type=float, nargs="+", default=[16, 1024], help="signer cache sizes (KiB)")
    ap.add_argument("--table", action="store_true", help="one line per configuration: size, verification, lifetime")
    ap.add_argument("--json", action="store_true", help="every figure of the site, as JSON (site/data.json)")
    x = ap.parse_args()
    hashes = [H for H in HASHES if H.name in x.hash]
    chosen = [c for c in configurations() if c[0] in x.lt and (c[2] == "layered" or c[3] == c[1] or c[3] in x.pruned)]

    if x.json:
        import json
        print(json.dumps(site_data(), indent=1))
        return

    if x.table:
        print("hash       2^L  h  shape            size  verify  keygen    proved N   (cover attack)")
        for H in hashes:
            for L, h, shape, b, coords, ka in chosen:
                C = Costs(H, None, coords)
                n, attack = proved(fc, L, h, shape, b)
                label = f"layered {coords} trees" if shape == "layered" else ("full" if b == h else f"pruned {b}")
                life = "not certified" if n is None else f"{n:>11,} ({fmt(attack) if attack else '?'})"
                print(f"{H.name:<10} {L:>2} {h:>2}  {label:<12} {size(h, shape, coords=coords):>8,} {C.verify(h, shape):>7} "
                      f"{fmt(C.keygen(h, shape, b)):>7}  {life}")
        return

    print(f"leanSphincs candidate: a two-level WOTS forest of {COORDS} trees (fewer for the layered keys of "
          f"2^24 and 2^26: 6 and 7 trees) under WOTS+C with {V} chains of "
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
        for L, h, shape, b, coords, ka in chosen:
            C = Costs(H, None, coords)
            if b == h:
                desc = "one tree" if shape == "pruned" else "layers " + "+".join(map(str, layers(h, shape))) + f", {coords} coordinates"
                print(f"  2^{L}, h={h} {shape} ({desc}): signature {size(h, shape, coords=coords):,} B, verification {C.verify(h, shape)}")
            n, attack = proved(fc, L, h, shape, b)
            life = "not certified" if n is None else f"lifetime {fmt(n)} (cover attack {fmt(attack)})"
            signs = []
            for kib in x.cache_kib:
                base, grind, tree = C.sign(h, shape, b, int(kib * 1024))
                signs.append(f"{fmt(base + tree)} with {kib:g} KiB")
            label = "" if shape == "layered" else ("full key: " if b == h else f"pruned b={b}: ")
            print(f"    {label}{life}, keygen {fmt(C.keygen(h, shape, b))}, signing {', '.join(signs)}")

    print()
    threshold(x.lt)


def configurations():
    """(L, h, shape, b, forest coordinates, FORS (k, a)) of every configuration, by lifetime 2^L."""
    for L in LIFETIMES:
        h = L - 4
        for b in [h] + [bb for bb in PRUNED if bb < h]:
            yield L, h, "pruned", b, COORDS, (FORS_TREES, FORS_HEIGHT)
        hl, coords, ka = UNIFORM[L]
        yield L, hl, "layered", hl, coords, ka


def proved(fts, L, h, shape, b):
    """(proved in Lean, cover attack) of the forest (fc) or FORS (vc), None when not certified."""
    if shape == "layered":
        return fts.uniform_lifetime(L), fts.uniform_attack(L)
    return fts.lifetime(h, shape, b), fts.attack(h, shape, b)


def site_data():
    """Every configuration (lifetime, shape, kept subtree, hash) with its figures, and the threshold and
    hardware-wallet figures, for the site."""
    out = {"configs": [], "threshold": [], "wallet": {}}
    for H in HASHES:
        for L, h, shape, b, coords, ka in configurations():
            C, CV = Costs(H, None, coords), Costs(H, ka)
            proved_f, attack_f = proved(fc, L, h, shape, b)
            proved_v, attack_v = proved(vc, L, h, shape, b)
            signs, signs_v = {}, {}
            for kib in (16, 1024, 16 * 1024):
                base, grind, tree = C.sign(h, shape, b, kib * 1024)
                signs[str(kib)] = round(base + tree)
                base, grind, tree = CV.sign(h, shape, b, kib * 1024)
                signs_v[str(kib)] = round(base + tree)
            out["configs"].append(dict(hash=H.name, lt=L, h=h, shape=shape, b=b, layers=list(layers(h, shape)),
                                       coords=coords, size=size(h, shape, coords=coords), verify=C.verify(h, shape),
                                       keygen=round(C.keygen(h, shape, b)), sign=signs,
                                       grind=round(2 ** (h - b)) if shape == "pruned" else 1,
                                       lifetime=proved_f, attack=attack_f,
                                       fors=dict(k=ka[0], a=ka[1], size=size(h, shape, "fors", b, ka=ka),
                                                 verify=CV.verify(h, shape), sign=signs_v,
                                                 lifetime=proved_v, attack=attack_v)))
    for H in HASHES:
        ands = ANDS[H.name]
        for L, h, shape, b, coords, ka in configurations():
            if shape == "pruned" and b == h:
                continue  # the full key is not for threshold signing
            C, CV = Costs(H, None, coords), Costs(H, ka)
            keygen, prep = C.mpc_keygen(h, shape, b), C.mpc_prep(h, shape)
            ledger = C.ledger_prep(h, shape, b)
            prep_v = CV.mpc_prep(h, shape)
            # the Ledger signs with a 16 KiB cache: alone, or assisted from prepared instances
            alone = [C.sign(h, shape, b, 16 * 1024), CV.sign(h, shape, b, 16 * 1024)]
            alone = [base + tree for base, grind, tree in alone]
            np_ = ledger_prepared(h, H.name, [C.device_online(), CV.device_online()], alone)
            fors_th = dict(lifetime=proved(vc, L, h, shape, b)[0],
                           prep=round(prep_v), prep_mb=prep_v * ands * BITS_PER_AND / 8 / 1e6, prep_rounds=rounds(H.name, 1 if shape == "pruned" else Q - 1),
                           ledger_prep=math.ceil(CV.ledger_prep(h, shape, b)), device_online=CV.device_online())
            out["threshold"].append(dict(hash=H.name, lt=L, h=h, shape=shape, b=b, lifetime=proved(fc, L, h, shape, b)[0],
                                         keygen=round(keygen), prep=round(prep), grind=2**h // THRESHOLD_PREPARED,
                                         and_depth=and_depth(H.name), keygen_rounds=rounds(H.name, Q - 1), prep_rounds=rounds(H.name, STEPS),
                                         ledger_prep=math.ceil(ledger), device_online=C.device_online(),
                                         ledger_prepared=np_, ledger_grind=2**h // np_,
                                         keygen_gb=keygen * ands * BITS_PER_AND / 8 / 1e9,
                                         prep_mb=prep * ands * BITS_PER_AND / 8 / 1e6, fors=fors_th))
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    out["rates"] = DEVICES
    out["wallet"] = dict(prepared=THRESHOLD_PREPARED, stark_verify=STARK_VERIFY, stark_verify_s=STARK_VERIFY_SECONDS, host_rate=HOST_RATE, device_rate=DEVICE_RATE,
                         opened_avg=COORDS * SUBS * sum(nonzero) / len(nonzero), opened_max=COORDS * SUBS * max(nonzero))
    return out


# Threshold signing (DKG, no dealer) and hardware wallets, with Keccak-256. The MPC builds the XMSS part only
# (the top layer, or the kept subtree); before a message it prepares a random instance (its forest key,
# WOTS+C signatures, lower trees and path), one per signature, and online the signers grind onto it in the
# clear, about 2^h attempts (cheap in the clear), and open only the forest chain values the message selects.
THRESHOLD_PREPARED = 1
# The hardware wallet prepares at least PREPARED instances, and enough that the host grinds and proves at most
# HOST_GRIND digests (HOST_GRIND_TOP at the largest height, so that the device prepares 4 times fewer instances).
PREPARED = 16
HOST_GRIND = 2**20
HOST_GRIND_TOP = 2**22


def wallet_prepared(h):
    return max(PREPARED, 2**h // (HOST_GRIND_TOP if h == max(HEIGHTS) else HOST_GRIND))


def shown_time(s):
    """A time as the site writes it: two significant digits rounded up, in h, min, s, ms or µs (site `time`)."""
    def sig2(v):
        return str(math.ceil(v - 1e-9)) if v >= 10 else f"{math.ceil(v * 10 - 1e-9) / 10:.1f}".removesuffix(".0")
    units = [(3600, "h", math.inf), (60, "min", 60), (1, "s", 60), (1e-3, "ms", 1000), (1e-6, "µs", 1000)]
    i = 0
    while i < len(units) - 1 and s < units[i][0]:
        i += 1
    if i > 0 and float(sig2(s / units[i][0])) >= units[i][2]:
        i -= 1
    return sig2(s / units[i][0]) + " " + units[i][1]


def ledger_prepared(h, name, device_online, alone):
    """The instances the Ledger prepares for a configuration: wallet_prepared(h), doubled while assisted signing is
    slower online than the Ledger signing alone, for either FTS (`device_online` and `alone`, in compressions, one per
    FTS), as long as it can win at all (the STARK verification alone takes STARK_VERIFY_SECONDS)."""
    rate = DEVICES["Ledger Nano S+"][name]
    p = wallet_prepared(h)
    def slower(p):  # not faster as the site shows the two times (shown_time)
        return any(online >= a / rate or shown_time(online) == shown_time(a / rate) for o, a in zip(device_online, alone)
                   for online in [max(1, round(2**h / p)) / HOST_RATE[name] + STARK_VERIFY_SECONDS + o / rate])
    if all(STARK_VERIFY_SECONDS + o / rate < a / rate for o, a in zip(device_online, alone)):
        while slower(p):
            p *= 2
    return p

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
# hashes per second a STARK prover proves, per hash: the host's proof of the grinding, and signature aggregation
HOST_RATE = {"Keccak-256": 500_000, "SHA-256": 750_000, "BLAKE2s": 1_000_000}
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


def threshold(lts):
    C = Costs(HASHES[0])
    nonzero = [sum(1 for d in w if d) for w in forest_table.table()]
    opened = COORDS * SUBS
    print(f"threshold (Keccak-256): {opened * sum(nonzero) / len(nonzero):.2f} forest chain values opened per "
          f"signature on average, at most {opened * max(nonzero)} (with {COORDS} trees)")
    for L in lts:
        for shape in ("pruned", "layered"):
            h, coords = (L - 4, COORDS) if shape == "pruned" else UNIFORM[L][:2]
            b = 12 if shape == "pruned" else h
            C = Costs(HASHES[0], None, coords)
            ls = layers(h, shape)
            keygen, prep = C.mpc_keygen(h, shape, b), C.mpc_prep(h, shape)
            lower = sum(2**hl * C.leaf + (2**hl - 1) * C.node for hl in ls[1:])
            ledger = C.ledger_prep(h, shape, b)
            gb = keygen * KECCAK_ANDS * BITS_PER_AND / 8 / 1e9
            pm = prep * KECCAK_ANDS * BITS_PER_AND / 8 / 1e6
            label = f"pruned b={b}" if shape == "pruned" else f"layered, {coords} coordinates"
            print(f"  2^{L}, h={h} {label}: keygen MPC {fmt(keygen)} permutations ({gb:.3g} GB per operator); "
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
    print(f"hardware wallet: the device prepares max({PREPARED}, 2^h / 2^{HOST_GRIND.bit_length() - 1}) instances (2^h / 2^{HOST_GRIND_TOP.bit_length() - 1} at h = {max(HEIGHTS)}) and the host grinds "
          f"2^h / that many digests ({', '.join(f'h={h}: {wallet_prepared(h)} prepared, {fmt(2 ** h / wallet_prepared(h))} digests, '
          f'{2 ** h / wallet_prepared(h) / HOST_RATE["Keccak-256"]:.2g} s to prove (Keccak-256)' for h in HEIGHTS)});"
          f" the device verifies the STARK in about {fmt(STARK_VERIFY)} compressions, counted as {STARK_VERIFY_SECONDS} s")

if __name__ == "__main__":
    main()
