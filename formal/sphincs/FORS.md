# FORS in Lean

`FORS` (`lakefile.toml`, namespace `FORS`) is the Lean library of the FORS variant. It is
`LeanForest` with one part replaced: the few-time signature is FORS instead of the two-level WOTS
forest. The hypertree, the WOTS+C keys, the pruning, the deterministic signer and the SUF-CMA
statement are the same, so this file only records what FORS changes; the rest is in
[FOREST.md](FOREST.md) and [PROOF.md](PROOF.md).

## The few-time signature

FORS is `k` trees of `2^a` leaves (`Params.forsTrees`, `Params.forsHeight`); the library is generic
in `(k, a)` and only the certificates fix them: `a = 10` and `k = 25` everywhere, so that
verification is the same for every pruning (`scripts/scheme.py`, `fors`). A leaf is the hash of one
secret, and one hash of the seed gives the two secrets of a sibling pair (`leafPair`), as everywhere
else in the scheme.

No tree has a root hash. A tree is hashed up to level `a - 1`, and the few-time key is the `2k`
nodes of that level themselves (`ForsKey`): no hash folds them, and the WOTS+C encoding of the
bottom layer absorbs them before its counter (`rootsPayload`, `nodePayload`). The address of a
tree's root exists and no algorithm uses it; a `forsNode` at level j is the node of tree level
j + 1 (`HashDomain`). FORS addresses pack the tree, the level and the node in `hi`
(`forsSlot`, `nodePosition`) and the instance in `lo`: type byte 15 for a leaf, 17 for a node.

An opening is one secret and its path of `a` nodes per tree, the last one the other node of level
`a - 1`, so the signature carries `k` openings (`signature_size`). The signer computes an
instance's FORS key in `forsKeyCost` hashes and opens one tree in `treeOpenCost`.

## The digest

`h + k a` bits do not fit in one hash output, so the digest is `digestCalls = ⌈(h + k a) / 256⌉`
calls — two in every configuration. Each call is its own hash domain (`HashDomain`, type byte 12,
the call number in `hi`), their outputs are concatenated low call first (`digestValue`) and the
result is truncated to `h + k a` bits (`truncateMessageDigest`). The index is the low `h` bits, so
it is read from the first call alone (`digestIndex`, `blockIndex`, `digestIndex_truncate`), and the
leaf of tree `κ` is bits `h + a κ ..` (`leafOffset`, `digestLeaves`). A fresh digest's kept view is
uniform (`Security.evalDist_digestBlock_uniform`).

## Proved lifetimes

Signature limits `N` with 127 bits, one theorem each in [Main.lean](FORS/Main.lean) (e.g.
`h24_pruned12`), collected by `requestedSecurity`; layered keys: 8 + 6 + 6, 10 + 6 + 6, 10 + 7 + 7,
10 + 8 + 8 and 10 + 9 + 9.

| h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 20 | 21,240,000 | — | 392,100 | 201,300 | 103,200 | 27,260 | 7,186 | 21,240,000 |
| 22 | 86,910,000 | 23,050,000 | 424,100 | 217,700 | 111,800 | 29,440 | 7,759 | 86,910,000 |
| 24 | 354,200,000 | 24,970,000 | 459,500 | 235,700 | 120,900 | 31,760 | 8,359 | 354,200,000 |
| 26 | 1,426,000,000 | 27,030,000 | 496,100 | 254,400 | 130,500 | 34,330 | 9,019 | 1,426,000,000 |
| 28 | 5,707,000,000 | 29,240,000 | 536,400 | 275,000 | 140,900 | 37,030 | 9,721 | 5,707,000,000 |

As a share of the lifetime in the FORS cover model (the attack that covers every one of the `k`
trees; `scripts/scheme.py`, `fors_log2_lifetime`):

| h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 20 | 93.8% | — | 88.7% | 87.9% | 86.9% | 85.5% | 83.9% | 93.8% |
| 22 | 95.9% | 94.4% | 89.3% | 88.4% | 87.6% | 86.0% | 84.4% | 95.9% |
| 24 | 97.7% | 95.0% | 90.1% | 89.2% | 88.3% | 86.5% | 84.8% | 97.7% |
| 26 | 98.4% | 95.6% | 90.6% | 89.7% | 88.8% | 87.2% | 85.4% | 98.4% |
| 28 | 98.4% | 96.2% | 91.3% | 90.4% | 89.5% | 87.7% | 86.0% | 98.4% |

Every limit is a larger share of its own cover attack than the forest's is of the forest's
(79.5–97.8%, [README.md](README.md)).

## What the proof changes

The route of [PROOF.md](PROOF.md) is unchanged. Two steps differ.

**The grinding signer reads the digest of a (message, randomizer) pair call by call.** A trial reads only the block that carries the
index and tests landing on it; the remaining calls of the pair are read later, in the final
assembly, and only if it landed. So the fair-share argument runs over the pair's whole tuple of
blocks ([ScanSigner/FairShare.lean](FORS/ScanSigner/FairShare.lean): `pblk`, `pcache`, `viewOf`,
`fresh_view_mean`), while landing and
the pool counts still rest on the first block alone (`blk`). `all_read_bound` is the ingredient: a
family of cached entries, read in order, is left untouched, so a value that only reads them is its
value at their cached answers. A pair that is fresh when a trial reads its first block has its
remaining calls presampled, so the whole tuple is uniform at once
([CoverPotential/Presample.lean](FORS/CoverPotential/Presample.lean), `interp_presample_new`).

**The cover bound is over `k` independent trees.** The cover event: in every tree, the forgery's digest
selects a leaf the run has already revealed (`TreeCov`, `Covered`). The first two moments of the per-tree cover fraction have closed
forms in `A = 2^a` — `1 - (1 - 1/A)^n` and its second-moment companion
([CoverBound/FirstMoment.lean](FORS/CoverBound/FirstMoment.lean),
[CoverBound/SecondMoment.lean](FORS/CoverBound/SecondMoment.lean)) — which replace the forest's
codeword tables; [CoverBound/MomentBounds.lean](FORS/CoverBound/MomentBounds.lean) turns them
into kernel-checked rational tables and
[CoverBound/HTermOption.lean](FORS/CoverBound/HTermOption.lean) raises them to the k-th power.
