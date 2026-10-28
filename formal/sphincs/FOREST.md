# The two-level WOTS forest in Lean

`LeanForest` (`lakefile.toml`, namespace `LeanForest`) is the Lean library of the candidate. Its
few-time signature is a two-level WOTS forest: 8 trees of height 4; each leaf of a tree is the hash
of two subtrees of height 3 over WOTS keys. The digest picks, per tree, a leaf, a WOTS key in each of
its two subtrees and a codeword for each WOTS key (`lut`, entries in `{0..4}` summing to 5); the
signature opens each chain of the two WOTS keys at position `4 - d_i`.

No tree of the forest has a root hash. A subtree is hashed up to level 2 and a tree leaf is the hash of the four
level-2 nodes `m_0[0] ‖ m_0[1] ‖ m_1[0] ‖ m_1[1]` of its two subtrees; a tree is hashed up to level 3
and the few-time key is the sixteen level-3 nodes `t_0[0] ‖ t_0[1] ‖ … ‖ t_7[0] ‖ t_7[1]` themselves:
no hash folds them, and the WOTS+C encoding of the bottom layer absorbs them before its counter,
`Th(P, A(4, 0, leaf; layer 0, tree), t_0[0] ‖ … ‖ t_7[1] ‖ ctr)` (`Concrete.encode`, `ForestKey`). A key of
a higher layer signs the root of the tree below it (`rootPayload`, 16 bytes). The WOTS+C keys have 64
chains of 4 positions and target sum 128 (`targetSum`).
The signature is unchanged (3 path elements per subtree, 4 per tree): the last path element is the
other top node of its tree. The verifier folds 2 levels in a subtree and 3 in a tree and puts the node
it reached and the last path element in index order (`orderTops`: the reached node first when bit 2
of the WOTS-key index, bit 3 of the leaf index, is 0).

Final statement: `LeanForest.requestedSecurity` ([Main.lean](LeanForest/Main.lean)), 127 classical bits (SUF-CMA in the ROM)
for the deterministic Lean signer in every configuration of [README.md](README.md). At `h = 24`:

| b | proved N | cover attack | best known attack | proved / best known |
| ---: | ---: | ---: | ---: | ---: |
| 24 (full tree, and layered) | 336,700,000 | 3.59915e8 | 3.60e8 | 94% |
| 20 | 23,830,000 | 2.63862e7 | 2.62e7 | 91% |
| 14 | 441,500 | 5.18006e5 | 5.00e5 | 88% |
| 13 | 226,800 | 2.68735e5 | 2.56e5 | 89% |
| 12 | 116,600 | 1.39374e5 | 1.32e5 | 88% |
| 10 | 30,810 | 3.74550e4 | 3.49e4 | 88% |
| 8 | 8,154 | 1.00543e4 | 9.19e3 | 89% |

The cover attack column is the lifetime in the cover model: the number of signatures at which a
digest query covers a forest with probability `2^-127` (Poisson loads of the kept indices). The best
known attack also uses the WOTS+C unit-neighbour route, which applies unchanged: a forger that sees
the realized key takes the better of the cover rate `Y` and the rate `r` of that route, and the
lifetime is the largest `N` with `E[max(Y, r)] ≤ 1`. It is 100, 99, 96, 95, 95, 93 and 91% of the
cover lifetime (`b = 24 … 8`). `scripts/forest_attack.py` computes both columns
(`forest_attack.py cover H` the cover model at height `H`). `Y` comes from a
Monte Carlo of the realized key (loads, leaves, WOTS keys, codewords), with about 0.3% of noise on `N`
and 0.6% at `b = 8`: the column has three digits and the ratios are good to about a point. The rate is
`r = 0.9694`: a search of about `2^116` hashes for a neighbouring encoding, then one chain preimage at
`2 · 2^-128` per query, is at its best after about `2^122` queries. The FORS variant (`k = 24`) lasts
83–85% as long under its own cover attack ([FORS.md](FORS.md)).

## The codeword table

`lut` (`Scheme.lean`, `codewordCodes`) is a list of 256 codewords `d ∈ {0..4}^6` with digit sum 5; the
8-bit digest field of a WOTS key is the index. The table is a rule: sort the 246 codewords of digit sum
5 by decreasing `Σ d_i²`, then lexicographically; entry `t` is codeword number `t mod 214`
(`codewordRule`, and `codewordCodes_eq_rule`, checked by the kernel). It holds 214 codewords, and the
first 42 twice:

| digits of the codeword | `Σ d_i²` | codewords | in the table | entries |
| --- | ---: | ---: | --- | ---: |
| `{4,1}` | 17 | 30 | all, twice each | 60 |
| `{3,2}` | 13 | 30 | the first 12 twice, 18 once | 42 |
| `{3,1,1}` | 11 | 60 | all, once | 60 |
| `{2,2,1}` | 9 | 60 | all, once | 60 |
| `{2,1,1,1}` | 7 | 60 | the first 34, once | 34 |
| `{1,1,1,1,1}` | 5 | 6 | none | 0 |

With `f(t)` the probability that a uniform entry is covered by the componentwise maximum of `t`
uniform entries, `f(1..6)` = 0.005188, 0.067847, 0.172139, 0.280345, 0.376068, 0.456117: weight on
the codewords with few large digits costs a little at one signature (`f(1) = Σ w_d² / 256²`) and
gains from two on. At most 123 entries have a given digit at least one, which sets the reveal rate
of the contact bound.

Two earlier tables, for comparison (measured at `h = 26`, where the ratios were established):

- the 246 codewords in lexicographic order followed by the first 10 again: 7% below the rule;
- a table found by search, with the same number of entries per digit pattern as the rule but other
  codewords of `{3,2}` and `{2,1,1,1}` (reveal constant 117): 1% above the rule. The rule replaced it
  to make the table one sentence of the specification.

Every entry has digit sum 5 (`Completeness.lut_sum`, `Cost.lut_sum`), so a WOTS key is verified
with exactly 5 chain steps: the verification cost and the signature size below do not depend on the table. The
proof uses the table through that lemma, through `litCount_le_all` (`SmallBudget/Contact/RevealRate.lean`) and
through the counts `pmfT` of `CoverBound/CodewordTables.lean` (a fold over the 256 indices: a repeated codeword is a
count of 2); nothing uses that the entries are distinct. `scripts/forest_table.py` holds the table
and computes from it the Lean literal and the kernel-checked tables `fTab`, `f2Tab` (`CoverBound/CodewordSums.lean`),
`P1tab`, `P2tab` (`CoverBound/MomentTable.lean`) and `PHtab` (`CoverBound/NearMomentTable.lean`), stored as their numerators over 2^128
(`P1L`, `P2L`, `PHL`, which the certificates read); `scripts/forest_certificates.py` imports
it and refuses to run if the Lean sources hold other tables.

No `sorry`, no `native_decide`, no new axioms: `LeanForest/Axioms.lean` checks every declaration
(`propext`, `Classical.choice`, `Quot.sound` only). Certificates are exact rationals checked by the
kernel (`decide +kernel`). `Certificates/H*.lean` store only the scalars of each Poisson table
(`m`, `P`, `J`, `n1`), option (`c1`, `θ`, `s`, `cthr`) and near certificate: `Certificates/Build.lean`
rebuilds the tables and options from them in integers (`poisOf`, `buildOpt`, `buildOptN`) and proves
that what it builds passes the unchanged checkers. The options of a cover are checked one by one with their bound
`B` (`checkOptB`), and the chain of the cover is checked on these bounds (`checkCoverW_of`,
`checkCoverH_of`).

## Build

```
env LEAN_NUM_THREADS=1 nice -n 19 lake build LeanForest
```

Table: `python3 scripts/forest_table.py info` (composition), `check` (the Lean sources hold the tables
of the script), `write` (rewrite them). Certificates: `python3 scripts/forest_certificates.py emit`
(writes `LeanForest/Certificates/H*.lean` and `LeanForest/Lifetimes.lean`; the kernel checks one height
in about 30–50 s and 1 GB of memory);
`python3 scripts/forest_certificates.py check H SHAPE B N LX` checks one set in Python with the same exact
arithmetic; `maxn H SHAPE B N0 [STEP LXLO LXHI]` searches the largest `N` over a grid of splits `lx`.
The axiom guards (`LeanForest/Axioms.lean`) are part of the build.

## Hash inputs

Every hash input is `P ‖ A ‖ payload` (`Scheme.lean`: `tweakableHashInput`, `keygenHashInput`,
`randomizerHashInput`): the 16-byte public parameter, then the 16-byte address
`A = lo (4 bytes) ‖ hi (3 bytes) ‖ (type + 32·step) ‖ layer ‖ tree (4 bytes) ‖ 0^3` with `lo`, `hi`
and `tree` little endian (`fieldBytes`), then the payload, which starts at byte 32. The layer byte
counts the layers from the bottom (`layerByte`); the forest calls, the digest and the derivations
outside the trees have layer and tree 0, and so has every call of a one-layer key. There is no exception: the parameter
derivation (under `P = 0`), the randomizer base, the seed derivations and the surrogates have the same
address format. `Th` keeps the first 16 bytes of the hash. The public key is `root ‖ P`, 32 bytes.
Forest positions: tree `c < 8`, leaf `s < 16`, subtree `j < 2`, WOTS key `a < 8`, chain `i < 6`,
`idx` the `h`-bit instance. A seed derivation of chain starts is addressed by a pair of chains `t`
(chains `2t` and `2t + 1`): `t < 32` in a WOTS+C key, `t < 3` in a forest WOTS key.

| call | type | step | hi | lo | payload |
| --- | ---: | --- | --- | --- | --- |
| WOTS+C chain secrets `2t`, `2t + 1` (both halves of the hash) | 0 | 0 | `t` | leaf | seed |
| WOTS+C chain step onto position `to` | 1 | `to − 1` | chain | leaf | value |
| WOTS+C leaf | 2 | 0 | 0 | leaf | 64 chain ends |
| tree node | 3 | 0 | level | node | left ‖ right |
| WOTS+C encoding | 4 | 0 | 0 | leaf | bottom layer: `t_0[0] ‖ t_0[1] ‖ … ‖ t_7[0] ‖ t_7[1]` (the forest key, 256 bytes) ‖ counter (4 bytes); above: the root of the tree below (16 bytes) ‖ counter |
| parameter derivation, under `P = 0` | 5 | 0 | 0 | 0 | seed |
| randomizer base `R0` and step `δ` (both halves of the hash) | 7 | 0 | 0 | 0 | seed ‖ message |
| message digest | 12 | 0 | 0 | 0 | message ‖ randomizer |
| surrogate sibling | 13 | 0 | level | 0 | seed |
| forest chain secrets `2t`, `2t + 1` (both halves of the hash) | 14 | 0 | `c + 8s + 128j + 256a + 2048t` | `idx` | seed |
| forest chain step from position `t` | 15 | `t` | `c + 8s + 128j + 256a + 2048i` | `idx` | value |
| forest WOTS-key leaf | 16 | 0 | `c + 8s + 128j + 256a` | `idx` | 6 chain tops |
| subtree node, level 1 and 2 | 17 | 0 | `c + 8s + 128j + 256·level + 1024·node` | `idx` | left ‖ right |
| tree leaf | 18 | 0 | `c + 8s` | `idx` | `m_0[0] ‖ m_0[1] ‖ m_1[0] ‖ m_1[1]`, the level-2 nodes of the two subtrees (64 bytes) |
| forest tree node, level 1 to 3 | 19 | 0 | `c + 8·level + 64·node` | `idx` | left ‖ right |

With Keccak-256 a call of `n` bytes costs `n / 136 + 1` Keccak-f permutations: a chain step is 48 bytes,
a node 64, a forest WOTS-key leaf 128, a tree leaf 96 and the digest 80 (1 permutation each), the
encoding 292 (3: the counter falls in the last block, so the signer absorbs the key once and pays
one permutation per counter), a one-time leaf 1,056 (8). The addresses of a subtree root (type 17,
level 3), of a tree root (type 19, level 4) and of the former key hash (type 20, `roots`) exist in
`HashDomain` and no algorithm uses them.

One hash of the seed gives two chain starts: the hash output is 32 bytes, the start of chain `2t`
is bytes 0 to 15 and the start of chain `2t + 1` is bytes 16 to 31 (`deriveOutput`, `hashHalf`,
`Seeded.otsSecrets`, `Seeded.forestSecrets` in `Scheme.lean`). A one-time key takes 32 derivations
for its 64 chains and a forest WOTS key 3 for its 6 chains. The parameter and the surrogates are one
hash each and keep its first 16 bytes; so does every verification hash. The randomizer hash gives the
base `R0` (bytes 0 to 15) and the step `δ` (bytes 16 to 31 with the lowest bit set, `walkStep`).
`Seeded.otsStart`, `Seeded.forestStart` and `Seeded.chainValue` are the per-chain views (one
derivation each), used in statements only: the signer's values are theirs
(`Completeness.eval_otsSecrets`, `eval_forestSecrets`).

The signer derives the base `R0` and the step `δ` of a message from one hash,
`H(P ‖ A(7, 0, 0) ‖ seed ‖ message)` (one hash query), and attempt `i` uses the randomizer `R0 + i δ`
(arithmetic modulo `2^128`, `Seeded.signDigestLoop`); it keeps the first attempt whose digest index
lands in the kept subtree. `δ` is odd, so the scan does not come back within `2^128` attempts
(`walk_iterate_ne`, `GraphView.nextRand_pow_ne`), and secret, so a signature does not tell which
randomizers were rejected before it.
The randomizer comes last in the digest payload: a grinding attempt changes only the last block of
the digest hash. The digest input is 80 bytes, `P ‖ A ‖ message ‖ randomizer`, within one 136-byte
block. The root is not hashed (`P` binds the key); `messageDigestPayload` keeps its root argument for
its callers and ignores it.

### Digest fields

The digest is the first `h + 208` bits of the hash output (`truncateMessageDigest`), read as a little-endian
number; a field is `extractLsb'` at a bit offset (`Scheme.lean`: `wordOffset`, `indexOffset`,
`superOffset`, `childOffset`, `digestMarks`, `digestIndex`). With `c < 8` the tree and `j < 2` the
subtree:

| field | bits | bit offset |
| --- | ---: | --- |
| codeword-table index of WOTS key `(c, j)` | 8 | `8 (2c + j)`: byte `2c + j` of the digest |
| WOTS key of subtree `(c, j)` | 3 | `128 + 3 (2c + j)` |
| leaf of tree `c` | 4 | `176 + 4c` |
| instance index `idx` | `h` | 208, in the last 64-bit word (`h ≤ 28`) |

Bits `h + 208` to 255 are unused. No field lies across two 64-bit words: the children, the leaves and
the index are laid out in that order, which is what makes the three groups fall inside words.
The proof reads a digest as its
index and one 26-bit field per tree (`Scheme/DigestView.lean`): `coordField` gathers the 26 bits of a
tree from the three places that hold them (leaf, then per subtree WOTS key and table index), and
`fullDigestView_bijective` states that the index and the 8 fields are a bijection of the `h + 208` bits,
so a uniform digest gives a uniform index and 8 independent uniform fields
(`evalDist_fullDigestView_uniform`), each a uniform mark (`Concrete.markEquiv`). The index of a
uniform hash output is uniform (`evalDist_blockIndex_uniform`, from
`evalDist_hashOutput_extractAt_uniform`: the bits at any offset of a uniform output are uniform).

Separation is unconditional. An input determines its parameter, its address and its payload
(`fieldBytes_injective` in `Scheme/Bytes.lean`, `fieldInput_injective` in `Scheme/Domains.lean`), two
inputs of different types differ whatever their parameters (`fieldInput_ne_of_tag_ne_across` and
`keygenInput_ne_hashInput`, same file), and an address determines the call:
`hashFields_injective` and `Position.input_separated` (`GraphView/Position.lean`) for verification,
`deriveFields_injective` and `keygenInput_injective` for the seed derivations,
`randomizerHashInput_injective` (`Reduction/SeedElimination.lean`) for the randomizer base. The layer and the tree of a
call are part of its address (`layerByte_injective`, `fieldBytes_injective`), so the calls of distinct
trees of distinct layers are separated as well.

`Layout.signature_size`: a signature serializes to `2832 + 1028 d + 16 h` bytes (4,244 for one layer of
height 24). `Cost.verification_compressions`: an accepted signature costs exactly `verifyCost`
compressions of the hash, and no signature costs more (`verification_compressions_le`). With
Keccak-256 at `h = 24` and one layer that is 260 permutations: 1 for the 80-byte digest input, 160
for the forest, 99 for WOTS+C and the path (3 for the encoding of the key, 64 chain steps, 8 for the
leaf and 24 nodes). The forest is 20 per tree (`compressions_coordRecover`: in each of the two
subtrees 5 chain steps, 1 for the WOTS-key leaf and 2 folds; 1 for the tree leaf; 3 folds), times 8.
The key is not hashed. Each further layer adds 1 for the encoding of a root, 64 chain steps and 8 for
the leaf; the path nodes of all layers are `h` in total. `Configurations.lean` states the size
and the three costs of each of the 10 shapes.

Hash calls of the signer (`GraphView/HashCalls.lean`, `GraphView/Cost.lean`; exact
counts on any oracle):

| computation | hash calls |
| --- | ---: |
| one-time key (`hashCalls_oneTimePublicKey`) | `32 + 64 · 3 = 224` |
| tree node at level `l` (`hashCalls_treeNode`) | `226 · 2^l − 1` |
| key generation (`hashCalls_keygenFromSeed`), top layer of height `t`, kept height `k` | `226 · 2^k + 2 (t − k)` |
| forest WOTS key leaf (`hashCalls_childLeaf`) | `3 + 6 · 4 + 1 = 28` |
| subtree node at level `l ≤ 2` (`hashCalls_subNode`) | `29 · 2^l − 1` |
| tree leaf (`hashCalls_superNode`) | `2 · 2 · 115 + 1 = 461` |
| tree node at level `l ≤ 3` (`hashCalls_topNode`) | `462 · 2^l − 1` |
| forest key of an instance (`hashCalls_forestKey`) | `8 · 2 · 3,695 = 59,120` |
| opening of one tree (`hashCalls_coordOpen_exact`) | `2 · 222 + 6,926 = 7,370` |
| forest opening (`hashCalls_forestOpen_exact`) | 58,960 |
| WOTS+C values of a signature (`hashCalls_published_values`) | `32 + 128 = 160` |
| signature after the scan (`hashCalls_finishSign_exact`) | `1 + 58,960 + Σ_layers (message + counter search + 160 + path)` |

The message of the bottom key is the forest key (59,120 calls); the message of a key above is the root
of the tree below (`226 · 2^l − 1` calls for a lower layer of height `l`, 6 to 9). Without the root hashes a tree leaf costs 2 calls less and a tree 1 call less, and without the key
hash the key costs 1 call less: the forest key went from 59,385 to 59,120 calls, the opening from
59,200 to 58,960 and the fixed part of a signature from 118,586 to 118,081 (`1 + 58,960 + 59,120`; the
signer's tick is 118,080 after the digest call). A counter of the encoding search is one hash call,
as before; the expected search is 14,670 calls (`2^128` over the 23,195,210,617,839,120,199,658,819,909,693,679
codewords of digit sum 128, about `2^114.16`), 2,197 with the former sum 123.
These counts do not enter the certificates: only the key-generation credit does.

The Lean signer recomputes the forest instance for its key and again for the opening, and the tree
nodes of the path; these are the counts of that signer, and the budget `q` of the theorem counts
them.

## The proof

[PROOF.md](PROOF.md) gives the route; this section adds what is specific to the forest and to the
layers.

**Two secrets per derivation.** The seed is removed as before: the answers of all derivations are
sampled before the seed and programmed at the seed's inputs, and the adversary sees them only by
querying an input that contains the seed (`Seed/Guess.lean`, a `2^-256` guess per query). The
prepared material is unchanged: one independent uniform 256-bit value per secret
(`SeedModel.Material`), the secret being its first 16 bytes. What is programmed at the input of a
derivation is `SeedModel.derivedOutput`: the two secrets of its pair of chains side by side, or the
value of a surrogate. Distinct derivations have distinct inputs (`derivationInput_injective`, from
`keygenInput_injective`) and read distinct secrets, and every secret is the half of its derivation
that the signer takes (`secretHalf_derivedOutput`, `secret_prepared`). A table of answers comes from
the same number of materials whatever the table (`card_fiber_derivedOutput`: one free second half
per chain start), so uniform material programs independent uniform answers
(`SeedCoupling.evalDist_derivedOutput_uniform`), which is the law of the random oracle on these
inputs (`evalDist_prepareTable`, `evalDist_prepared_continuation`). Every module above the seed
model sees `truncateHash (material.2 position)` as before, and its statements are unchanged. The
key-generation credit of the certificates is `Prefix.keygenHashCost = 226 · 2^k + 2 (t − k)`
(`keygenCost`), passed to the checkers as `K`.

After the deterministic
signer is replaced by a seed-free one (`Reduction/*.lean`), a forgery is a first-order hit, a WOTS
second-order event, or one of the forest events of the refined classification
(`Classification/WinRefined.lean`): a contact without guess record, two contacts at different chains of one
index, a recorded contact at a chain opened at or below its step, a near cover with a recorded
contact, or a cover. Budgets are split at `qh ≈ 2^(128 + lx)`.

**No root hashes.** The graph of hashed values (`GraphView/Position.lean`) keeps its positions; only
the children of two kinds of position change: a tree leaf (`superChild`) reads the four level-2
nodes of its two subtrees and the position `roots` the sixteen level-3 nodes of the trees. The root
of a subtree, the root of a tree and `roots` remain positions that nothing reads (the key is not
hashed; `GraphCorrectness.keyLabels` reads it off the sixteen level-3 positions): the position set already
over-approximates what is hashed, every position is prepared, and an address still determines one
position, so a query has one target as before. The values a signature reveals are unchanged
(`GraphView.publicData`: the subtree path at levels 0 to 2 and the tree path at levels 0 to 3, the
last of each being the other top node, which was already a path element). In the forest witness
(`Classification/Forest.lean`) an opening gives two top nodes per tree, the one its fold reaches and
its last path element (`opSubTops`, `opTops`). An opening that recovers the honest key has the
sixteen honest level-3 nodes, since the key is those nodes (a different key is a different encoding
input, which the WOTS+C classification handles). So each tree has the honest last path element and its fold of 3
levels reaches an honest node (`Completeness.orderTops_eq_iff`), which is classified as a fold to
the root was (`top_fold_classification`: honest tree leaf and path, or a node match at levels 1 to
3); likewise for the four level-2 nodes of a tree leaf (`SuperMatch`, `sub_fold_classification`,
node matches at levels 1 and 2). The statements above the witness (`Forest.Opening`,
`recovered_classification`, the classification of a win) are unchanged.

### The scan signer `R = R0 + i δ`

After the seed is eliminated the randomizer hash of a message is uniform; its two halves are an
independent start and step (`Det.evalDist_rtable_split`). The proof fixes the steps of all messages
(the seed-free game takes them as a parameter, `PublicData.steps`, and is bounded for every table of
steps, as if the forger knew them) and averages the starts. The start `R0` of a message is uniform and
hidden, and the signature of a message uses the first landing randomizer of the scan
`R0, R0 + δ, …` (`GraphView.nextRand`). For one unsigned message a randomizer is
fresh, cached and rejected, or cached and landing; the law of the signed pair is the walk value of
`ScanSigner/LoopWalk.lean` over these statuses (`GraphView.scan_boundW`). A cached landed pair is selected
with a probability that depends on the cache (the run of rejected values before it), not `1/(n + R)`,
and one digest query raises the selection mass of the adversary's pairs by at most `(2 − p)/2^128`
(`LoopWalk.creation_le`, `p = 2^-(h−b)`; attained by scanning forward from random starts), against
`1/2^128` for independent attempts. The potentials therefore keep the cached pairs of each unsigned
message as one exclusive group (`LoopWalk.grp`, `ForestPotential.grpAll`) applied to the one-coin
future of the pairs still to come:

- a new pair is paid by one future coin (`LoopWalk.probe_step`, `termO_newPair`) as long as the
  group of its message keeps mass `1 − τ` on the identity; the witness is only monotone, so the
  coin is `(2 − p)/(2^128 p (1 − τ))` (`H0.wbarOf`, `FairS`), with `τ` from the numbers of cached
  digests and of cached landed pairs (`LoopWalk.mass_le`);
- the number of cached landed pairs of unsigned messages is capped by an exact martingale
  (`lam` in `CoverPotential/OneCoin.lean`): above the cap the bound is trivial, and the cap term is
  at most `(64/65)^(2^15)` at the start (`H0.lam_start`);
- a signing call is paid by one fresh slot and the group of its message (`sign_term`): no coupling
  and no fair share;
- for the largest budgets one message can hold almost all the mass (its signature is then a known
  pair with certainty). A message with more than half of the budget is *heavy* (`LargeBudget/HeavyTerm.lean`): it
  acts by the law of its signed view (`LoopWalk.sgn`, exact under its own digest queries) and uses
  one spare fresh slot; the other messages have at most half of the budget
  (`LargeBudget/HeavyPotential.lean`, `ForestPotential.det_largeH`, certificates with `N + 1` signatures in
  `Certificates/Closing.lean`).

### Small budgets (`q - keygenCost ≤ qh`)

- **Linear potential** (`SmallBudget/Linear/*.lean`). A forest step whose written
  coordinate is still unexposed is *latent*: it becomes a contact with chance `2^-128` when that
  coordinate is exposed. Contacts carry the weight `cw` (one if decided, `2^-128` while latent);
  exposures keep every multilinear expression of the weights in the mean (`mean_cw`, `mean_cw2`) and
  the final payoff is bounded through pinned completions (`completion_pin`, `prob_fct`). The potential
  pays guesses, first-order hits, WOTS second-order events, unrecorded forest contacts and pairs of
  contacts, and leaves `(ρ - 1 - x) 2^-128` per forest step query unused (`smallRoute_potentialF`).
- **One-coin cover potential** at baseline `ρ / 2^128` with the exact cover indicator as witness
  (`CoverPotential/OneCoin.lean`, `CoverPotential/OneCoinGame.lean`), and its H-term certificate (`CoverBound/*.lean`: Poissonization,
  splitting into independent indices, first and second moments of the per-tree cover fraction from
  the distribution of the componentwise maximum of codewords, `CoverBound/HTermOption.lean`).
- **Contact bound A4** (`SmallBudget/Contact/Potential.lean`, `SmallBudget/Contact/Signing.lean`, `SmallBudget/Contact/Bound.lean` on the game framework
  `SmallBudget/Contact/PaidPotential.lean`). A recorded contact is *settled* once a reveal opens its chain at or below its step;
  settled contacts pay one, unsettled ones pay the reveal rate of the remaining signatures, the coin
  part and the capped near potential:
  `Ψ = Σ_recorded cw · (settled ? 1 : sig + coin + min(1, potN(y))) + y 2^-128 coin + κ 2^-128 Σ_{j<y} potN(j)`.
  The weighted sums keep their mean through ordinary queries (`PotentialA.Ctx.wsum_ordinary`). Through a
  signing call (`sign_contact`): the signer asks no forest step input, so it records no forest step,
  keeps every step answer and exposes a written coordinate only by revealing its chain
  (`SmallBudget/Contact/RunFacts.lean`); a completed call reveals upward-closed chains (`closedRuns_loop`); a call opens
  a given chain at or below `min(t + 1, 3)` with chance at most `123 · 2^-b · 2^-15` plus `wbar` per
  cached pair of the message, over every run (`reveal_le_all`, `ScanSigner/ScanReveals.lean`, `SmallBudget/Contact/RevealRate.lean`:
  at most 123 of the 256 table entries have a given digit at least one; with the scan signer the second
  part is `hitMass`, the probability that the signature uses a cached landed pair, and the coin
  part of the potential is `ν (budget · offSum + C(budget, 2) · rateS)` with
  `rateS = (2 − p)/2^128`: a unit of budget is a contact attempt or a digest query, not both);
  a latent contact exposed by the
  call is decided with chance `2^-128` whatever the call does (`HiddenDebt.interp_value_le`).
  The near potential uses the subtree-free near witness (`SmallBudget/Contact/NearWitness.lean`, certificate `CoverBound/NearOption.lean`).
  A forest step query costs `2^-128 (N rate + 1 - κ)`, paid by the slack of the linear potential once
  `κ ≥ 2 - ρ + x + N rate` (`arm_paysF`).
- Assembly: `sample_boundF` (`SmallBudget/SampleBound.lean`), `det_smallF` and the closed form `small_closeFF`
  with the rational check `checkSmallF` (`SmallBudget/Closing.lean`).

### Large budgets

The one-coin bound at the survival-weighted baseline (`LargeBudget/*.lean`, `det_largeW`) with forest covers
(`H0.checkCoverW`, `CoverBound/HTermOption.lean`).

### Both routes

`ForestPotential.det_bitsFH`: 127 bits from the small-route table (rate at `qh`), the small-route
option, the near certificate, `checkSmallF` at `qh` (coin summand `(2 − p) qh / 2^129`), and a chain
of covers of `[qh + 1, 2^127)`, each with its own Poisson table: light covers (`checkCoverW`, coin
`wbarOf`) up to about `0.249 · 2^128`, then one heavy cover (`checkCoverH`, `N + 1` signatures, coin
`wbarH`). For `b = h` (the full key and the layered key) there is no grinding and one light cover
reaches `2^127`. The splits `lx` are in [PROOF.md](PROOF.md) (`PARAMS` and `LAYERED` in the script),
the best of a grid of step 1/8; the limits are the largest `N` both routes certify there, rounded
down to four significant digits. Every checker takes the total height `H`, the kept height `b` and
the keygen credit `K` as arguments, so one checker serves every configuration.
