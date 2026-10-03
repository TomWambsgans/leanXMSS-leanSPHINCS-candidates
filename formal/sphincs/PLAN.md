# Continuation checkpoint

The imported leanVM baseline was committed as 3289130; its original unverified numerical
planning notes are preserved in that commit. Current candidate work is in `LeanSphincs/`,
with proof status and mismatches in README.md and PROOF.md. Do not mistake a successful
legacy build for a candidate security theorem.

Completed: candidate scheme and independent-randomizer game; seeded correctness at all
pruning heights; correctness of assembly from a landed randomizer; exact target-sum code
count; fresh-input counter and collision-aware seeded grinding bounds; exact subtree
landing probability and fixed-disclosure FORS coverage; signature serialization length;
independently randomized grinding and full honest sign-and-verify completeness; exact
six-lifetime FORS arithmetic with monotonicity; actual fresh/cached-first digest laws and
an adaptive fresh-query coverage union bound; the actual verifier's 391-compression count;
independent FORS experiment bounds; exact conditional uniformity of actual grinding after
keygen; structural, WOTS and FORS query-witness extraction and composition, with reference
certificates obtained from honest signing; all-message completeness sum ≤2^-256; N complete
signing-call disclosure domination after actual keygen, including adaptive/repeated messages
and WOTS exhaustion; exact terminal coverage formula and all six signing/fresh-target lifetime
bounds; actual-game cached witness and signing-subrun extraction; independent prepared secret
model and adaptive hidden-seed guessing bound with explicit independence assumptions.
Also checked: actual-game eager-preparation equivalence preserving cost; exact stopped
ordinary-oracle coupling before seed hits; all four cached candidate laws and mixed-prefix
invariant auditing; reference-free two-edge witnesses; exact hidden-prefix table splits;
local cache-potential accounting against the actual shared query budget; ideal interleaved
digest-query/disclosure bounds for all six lifetimes; labelled actual source provenance and
weighted source-selection charging to actual grinding cost; full material-game equivalence
with virtual costs for privileged derivations; full randomized signing through a selected
chain cutoff with original costs; exact finite structural-address injection and canonical graph
preparation; supported preparation-cache cleanliness and exact surrogate-target addresses;
full seeded-game cache-change reduction with derivation-only loss and a shared-budget partition;
actual conditional prequeried-source selection, joint-pair forecasts, and exact pool mass balance.

## Paper proof of the target bound (checked by hand, 2026-10-03)

Goal: Adv(A) ≤ q/2^127 whenever every run of the experiment counts at most q hash calls
(adversary, signer, verifier, plus keygen's 258·2^b + 2(26-b) honest calls). If q ≥ 2^127 the
bound is trivial, so assume q < 2^127.

1. Seed. Replace the seed-derived secrets by independent uniform material; the runs differ only
   if some query names the seed: loss ≤ q/2^256. (Formal: `Reduce.forgeAdvantage_le_seedFree`.)
2. Hidden coordinates. Chain values at positions 0..2 of retained leaves and FORS secrets are
   independent uniform 128-bit coordinates, revealed only by signing. Stop the run at the first
   ordinary query that names a still-hidden coordinate; the stop is charged 2^-128 per row query
   in a forced-failure comparison run. (Formal: `forgeAdvantage_le_prep`,
   `HiddenOutside.table_stop_or_bad_bound`.)
3. Classification. In a non-stopped winning run, the accepted forgery is either
   (a) a tree/surrogate/WOTS-leaf/chain/FORS-node/encoding exception, i.e. some cached
   non-canonical answer hits the single target of its tweak (graph label or canonical encoding
   output, all fixed before the run once every leaf's encoding search is pre-run); or
   (b) a canonical opening of an unsigned (M, R) whose cached digest lands and whose 24 FORS
   openings were all revealed (resubmitting a signed (M, R) reproduces the signature, and an
   undisclosed secret or a chain value below the canonical word would have stopped the run).
4. Budget (common comparison run, per ordinary query): row input: stop 1 + target 1; structural
   or encoding input: target ≤ 1; message-digest input: no target, no stop, FORS budget 2;
   seed/other inputs: 0. Weights are in units of 2^-128, so the total is ≤ 2·(#ordinary queries)
   ≤ 2(q − K) with K the keygen tick. Hence Adv ≤ (2q − 2K)/2^128 + q/2^256 ≤ q/2^127, because
   q/2^256 ≤ 2K/2^128 for q < 2^127.
5. FORS term. Needed: Pr[(b)] ≤ 2^-127 · E[#message-digest queries]. Each unsigned landed
   candidate costs two adversary/verifier block queries (a landed signer trial is always
   signed), so a per-candidate hazard ≤ 2^-126 suffices. For a fresh digest against N signed
   digests drawn uniformly from the kept subtree the hazard is forsBound(b, N):
   0.956, 0.929, 0.837, 0.759, 0.898 × 2^-127 (full, b=20, 13, 14, 12) and 2^-231 (b=10).

   Pool bias: a signer's grinding trial may hit a pair (R, M_j) the adversary already queried;
   the selected digest is then a known one, and the adversary chooses M_j adaptively. Per
   signature, P(selected digest ∈ A | past) ≤ (1−π)·|A|/|kept| + w·|pool(M_j) ∩ A|, with
   w ≤ 2^(27−b−128) per cached landed point. The crude union over covering patterns and pool
   tuples inflates each covering signature by a factor (1 + q/2^127).
   * b=10, N=33: the inflation is at most 2^24 and the hazard stays below 2^-200 per candidate,
     so the crude argument proves the claim with enormous slack.
   * The other five: the crude argument only covers q up to roughly 2^119–2^123. The true
     adaptive gain is much smaller (with a single message the selected digest is exactly
     uniform; only the choice among message pools biases it), but proving that is a separate
     concentration argument that is not worked out. These five stay conditional for now.

## Remaining formal plan

R1. Finish `win_implies_bad` (step 3; all case lemmas are proved, only the assembly remains;
    split it further, since the one-piece proof stalls elaboration). Add the Valid-log
    condition (≤ N signatures) to `ForsCover`.
R2. Comparison-world target bound: initial prepared cache is clean for `compTable`;
    `weighted_output_bound` with per-input weight |targets| ≤ 1, charged to trace entries.
R3. Compose with the guess charge into Adv ≤ E[Σ entry weights]/2^128 + Pr[ForsCover] + q/2^256,
    state the FORS rate as an explicit hypothesis, and do the arithmetic of step 4. This gives
    all six claims conditional on one stated FORS-coverage hypothesis per instance.
R4. Prove the FORS hypothesis for b=10 (step 5, crude argument), preferably via a standalone
    adaptive FORS game and a simulation reduction from the comparison world.
R5. Leave the five tight FORS hypotheses explicit; record precisely what is open.
R6. Resolve the reference caching/query-count transfer before claiming security of Rust itself.

The bridge files `LeanSphincs/Bridge*.lean` implement steps 1–3 (branch
`leansphincs-lifetime-bridge`).

Preserve b=10,N=33 as literally requested. No threshold/MPC work, changes to the spec,
Rust or site, or pushes. Run Lake with nice -n 19 and LEAN_NUM_THREADS=2. Every public
candidate theorem must retain an axiom guard in LeanSphincs/Axioms.lean.
