# FORS in Lean

`LeanFors` (`lakefile.toml`, namespace `LeanFors`) is the Lean library of the vanilla variant. It is
`LeanForest` with one part replaced: the few-time signature is FORS instead of the two-level WOTS
forest. The hypertree, the WOTS+C keys, the pruning, the deterministic signer and the SUF-CMA
statement are the same, so this file only records what FORS changes; the rest is in
[FOREST.md](FOREST.md) and [PROOF.md](PROOF.md).

## The few-time signature

FORS is `k` trees of `2^a` leaves (`Params.forsTrees`, `Params.forsHeight`); the library is generic
in `(k, a)` and only the certificates fix them: `a = 10` everywhere, `k = 25` or `26`
(`scripts/scheme.py`, `fors`). A leaf is the hash of one secret, and one hash of the seed gives the
two secrets of a sibling pair (`leafPair`), as everywhere else in the scheme.

No tree has a root hash. A tree is hashed up to level `a - 1`, and the few-time key is the `2k`
nodes of that level themselves (`ForsKey`): no hash folds them, and the WOTS+C encoding of the
bottom layer absorbs them before its counter (`rootsPayload`, `nodePayload`). The address of a
tree's root exists and no algorithm uses it; a `forsNode` at level j is the node of tree level
j + 1 (`HashDomain`). FORS addresses pack the tree, the level and the node in `hi`
(`forsSlot`, `nodePosition`) and the instance in `lo`: type byte 15 for a leaf, 17 for a node.

An opening is one secret and its path of `a - 1` nodes per tree, so the signature carries `k`
openings (`signature_size`). Key generation costs `forsKeyCost` hashes and one opening costs
`treeOpenCost`.

## The digest

`h + k a` bits do not fit in one hash output, so the digest is `digestCalls = ⌈(h + k a) / 256⌉`
calls — two in every configuration. Each call is its own hash domain (`HashDomain`, type byte 12,
the call number in `hi`), their outputs are concatenated low call first (`digestValue`) and the
result is truncated to `h + k a` bits (`truncateMessageDigest`). The index is the low `h` bits, so
it is read from the first call alone (`digestIndex`, `blockIndex`, `digestIndex_truncate`), and the
leaf of tree `κ` is bits `h + a κ ..` (`leafOffset`, `digestLeaves`). A fresh digest's kept view is
uniform (`Security.evalDist_digestBlock_uniform`).

## What the proof changes

The route of [PROOF.md](PROOF.md) is unchanged. Two steps differ.

**The grinding signer reads its pair call by call.** A trial reads only the block that carries the
index and tests landing on it; the remaining calls of the pair are read later, in the final
assembly, and only if it landed. So the fair-share argument runs over the pair's whole tuple of
blocks ([ScanSigner/FairShare.lean](LeanFors/ScanSigner/FairShare.lean): `pblk`, `pcache`, `viewOf`,
`fresh_view_mean`), while landing and
the pool counts still rest on the first block alone (`blk`). `all_read_bound` is the ingredient: a
family of cached entries, read in order, is left untouched, so a value that only reads them is its
value at their cached answers. A pair that is fresh when a trial reads its first block has its
remaining calls presampled, so the whole tuple is uniform at once
([CoverPotential/Presample.lean](LeanFors/CoverPotential/Presample.lean), `interp_presample_new`).

**The cover bound is over `k` independent trees.** A forgery must open, in every tree, a leaf the
run has already revealed (`TreeCov`, `Covered`). The first two moments of that event have closed
forms in `A = 2^a` — `1 - (1 - 1/A)^n` and its second-moment companion
([CoverBound/FirstMoment.lean](LeanFors/CoverBound/FirstMoment.lean),
[CoverBound/SecondMoment.lean](LeanFors/CoverBound/SecondMoment.lean)) — which replace the forest's
codeword tables; [CoverBound/MomentBounds.lean](LeanFors/CoverBound/MomentBounds.lean) turns them
into kernel-checked rational tables and
[CoverBound/HTermOption.lean](LeanFors/CoverBound/HTermOption.lean) raises them to the k-th power.
