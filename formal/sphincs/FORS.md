# FORS in Lean

`FORS` (`lakefile.toml`, namespace `FORS`) is the Lean library of the FORS variant. It is
`LeanForest` with one part replaced: the few-time signature is FORS instead of the two-level WOTS
forest. The hypertree, the WOTS+C keys, the pruning, the deterministic signer and the SUF-CMA
statement are the same, so this file only records what FORS changes; the rest is in
[FOREST.md](FOREST.md) and [PROOF.md](PROOF.md).

## The few-time signature

FORS is `k` trees of `2^a` leaves (`Params.forsTrees`, `Params.forsHeight`); the library is generic
in `(k, a)` and only the certificates fix them: `a = 10` and `k = 24`, the same for every pruning
of a height so that verification does not depend on it (24 is the fewest trees whose cover attack
reaches the `2^(h+4)` signatures of each lifetime), except the layered keys of the lifetimes `2^24`
and `2^26`, both at `h = 24`: 19 and 23 trees of height 9, the fewest of height 9 whose certificate
reaches `2^24` and `2^26` (18 trees do not even reach `2^24` in the cover attack). A leaf is the hash of one
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

The digest is `digestCalls = ⌈(h + k a) / 256⌉` calls of 256 bits: two with 24 trees of height 10,
one with 19 or 23 trees of height 9. Each call is its own hash domain (`HashDomain`, type byte 12,
the call number in `hi`), their outputs are concatenated low call first (`digestValue`) and the
result is truncated to `h + k a` bits (`truncateMessageDigest`). The index is the low `h` bits, so
it is read from the first call alone (`digestIndex`, `blockIndex`, `digestIndex_truncate`), and the
leaf of tree `κ` is bits `h + a κ ..` (`leafOffset`, `digestLeaves`). A fresh digest's kept view is
uniform (`Security.evalDist_digestBlock_uniform`).

## Proved lifetimes

Signature limits `N` with 127 bits, one theorem each in [Main.lean](FORS/Main.lean) (e.g.
`h24_pruned12`), collected by `requestedSecurity`; layered keys: 8 + 8 + 8, 10 + 8 + 8 and 10 + 9 + 9,
at `h = 24` also with 19 and 23 trees of height 9 (`h24_layered_k19`, `h24_layered_k23`).

| h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 20 | 17,650,000 | — | 327,400 | 168,300 | 86,430 | 22,850 | 6,036 | — |
| 22 | 72,220,000 | 19,240,000 | 356,000 | 182,800 | 93,890 | 24,790 | 6,547 | — |
| 24 | 293,000,000 | 20,920,000 | 387,200 | 198,700 | 101,900 | 26,860 | 7,099 | 293,000,000 |
| 26 | 1,182,000,000 | 22,750,000 | 419,700 | 215,400 | 110,500 | 29,130 | 7,677 | 1,182,000,000 |
| 28 | 4,731,000,000 | 24,710,000 | 455,600 | 233,500 | 119,800 | 31,600 | 8,313 | 4,731,000,000 |

As a share of the lifetime in the FORS cover model (the attack that covers every one of the `k`
trees; `scripts/scheme.py`, `fors_log2_lifetime`):

| h | full key (b = h) | b = 20 | b = 14 | b = 13 | b = 12 | b = 10 | b = 8 | layered |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 20 | 93.9% | — | 88.0% | 87.1% | 86.1% | 84.4% | 82.7% | — |
| 22 | 96.0% | 94.5% | 88.7% | 87.7% | 86.7% | 84.9% | 83.2% | — |
| 24 | 97.4% | 95.0% | 89.4% | 88.4% | 87.3% | 85.4% | 83.9% | 97.4% |
| 26 | 98.2% | 95.6% | 89.9% | 88.9% | 87.9% | 86.1% | 84.3% | 98.2% |
| 28 | 98.3% | 96.2% | 90.6% | 89.5% | 88.5% | 86.8% | 84.9% | 98.3% |

The layered keys with lighter FORS, at `h = 24` (8 + 8 + 8):

| FORS | lifetime | limit | cover attack | share |
| --- | ---: | ---: | ---: | ---: |
| 19 trees of height 9 | `2^24` | 16,777,216 | 19,630,036 | 85.5% |
| 23 trees of height 9 | `2^26` | 73,380,000 | 82,781,654 | 88.6% |

With 1 and 4.4 signatures per instance, their limits are a smaller share of the cover attack than
the 24×10 layered key of the same height (97.4%). Every limit, these two included, is a larger share of its
own cover attack than the forest's is of the forest's (60.0–97.8%, [README.md](README.md)).

**A third route for the 19×9 key.** The two routes of [PROOF.md](PROOF.md) certify the 19×9 key only up
to about 15.2 million signatures. The survival-weighted route ([SWRoute/](FORS/SWRoute),
`SWRoute.detSW`) closes the gap. It keeps the survival weight of the large route but raises it to a
state-dependent exponent: `ρ` until a marker, a contact or a near cover arms the run, then 2, more
after contacts. It applies to keys that keep every index (`b = h`) with `b + a ≥ 31` and one digest
call. `ForsPotential.det_bitsF3` combines the three routes: the small route up to `q_h ≈ 2^119.25`,
the SW route up to about `2^121.97`, the large route above. The SW route's certificate
([Certificates/H24SW](FORS/Certificates/H24SW.lean), `SWRoute.checkCoverSW`) is 7 entries, each with
its rate `ρ`, its cover and near options, and a certified tail of the near forecast.

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
[CoverBound/HTermOption.lean](FORS/CoverBound/HTermOption.lean) raises them to the k-th power. A
tighter option ([CoverBound/HTermOptionJ.lean](FORS/CoverBound/HTermOptionJ.lean)) splits by the number of
indices with many views (none, one, more; each with its own Chernoff parameter), bounds the cover
fraction by its support with `n` views, and at a few view counts uses the exact law of the trees with
no, one or more repeated leaves ([CoverBound/ClassLaw.lean](FORS/CoverBound/ClassLaw.lean)); each
certificate uses the option with the lower bound.
