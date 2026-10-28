# FORS in Lean

`FORS` (`lakefile.toml`, namespace `FORS`) is the Lean library of the FORS variant. It is
`LeanForest` with one part replaced: the few-time signature is FORS instead of the two-level WOTS
forest. The hypertree, the WOTS+C keys, the pruning, the deterministic signer and the SUF-CMA
statement are the same, so this file only records what FORS changes; the rest is in
[FOREST.md](FOREST.md) and [PROOF.md](PROOF.md).

## The few-time signature

FORS is `k` trees of `2^a` leaves (`Params.forsTrees`, `Params.forsHeight`); the library is generic
in `(k, a)` and only the certificates fix them: `a = 10` and `k = 24` in every configuration, so that
verification is the same for every pruning; 24 is the fewest trees whose cover attack reaches the
`2^(h+4)` signatures of each lifetime (`scripts/scheme.py`, `fors`). A leaf is the hash of one
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
| 20 | 17,440,000 | — | 325,200 | 167,400 | 86,200 | 22,790 | 6,029 | 17,440,000 |
| 22 | 71,490,000 | 19,030,000 | 354,500 | 182,200 | 93,560 | 24,770 | 6,547 | 71,490,000 |
| 24 | 292,300,000 | 20,740,000 | 385,300 | 198,000 | 101,700 | 26,860 | 7,099 | 292,300,000 |
| 26 | 1,182,000,000 | 22,590,000 | 418,900 | 215,200 | 110,500 | 29,130 | 7,677 | 1,182,000,000 |
| 28 | 4,731,000,000 | 24,540,000 | 454,500 | 233,300 | 119,800 | 31,600 | 8,313 | 4,731,000,000 |

As a share of the lifetime in the FORS cover model (the attack that covers every one of the `k`
trees; `scripts/scheme.py`, `fors_log2_lifetime`):

| h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 20 | 92.8% | — | 87.5% | 86.6% | 85.9% | 84.2% | 82.6% | 92.8% |
| 22 | 95.1% | 93.5% | 88.3% | 87.4% | 86.4% | 84.9% | 83.2% | 95.1% |
| 24 | 97.2% | 94.2% | 89.0% | 88.1% | 87.1% | 85.4% | 83.9% | 97.2% |
| 26 | 98.2% | 94.9% | 89.7% | 88.8% | 87.9% | 86.1% | 84.3% | 98.2% |
| 28 | 98.3% | 95.5% | 90.4% | 89.4% | 88.5% | 86.8% | 84.9% | 98.3% |

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
