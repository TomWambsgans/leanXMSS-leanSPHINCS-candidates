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

## Adaptive FORS/WOTS switching (2026-10-03)

A forger can collect its signatures and spend each hash call where it is best: on the FORS
search when the realised openings beat the per-call budget, on chain/tree/encoding searches
otherwise. Its rate is E[max(X, r)] where X is the realised FORS rate (units of 2^-127 per digest
query) and r the best other rate. Bounding only E[X] (the old lifetimes) is not enough; at b=12
and 125000 signatures the switching gain is about 12%. `scripts/adaptive_lifetime.py` computes
lifetimes that are provable with the current, crude per-call accounting (11–17% of the old ones).
The plan below aims at 82–97% of the old lifetimes.

## Paper proof (target)

Units: N = 2^128, x = q/N, h = 2^-127. Z = Psi(M)/h, where M is a multinomial word of Nbar
uniform kept-leaf proposals (Nbar = N + O(2^12)) and Psi(M) = 2^-266 sum_l P_iota(M_l) is the
count-based coverage price (P_iota(m) ~ m^24 with block weights iota(k) ~ 1 for k <= 8; it bounds
every realised coverage, collisions included).

F. FORS forecast domination (pool steering included). Every first-touch digest query's
   forecast F_t satisfies F_t <= E[Psi(M) | past]: a proposal bank coupled to the signer by
   rejection sampling (fair-share selection symmetry, Ville-type concentration of cached pools
   per message/leaf and per candidate/block), plus a witness count over tree-to-signature maps.
   Hence for any per-call rate r of the other attacks, by Jensen:
       Adv <= q E[max(Psi, r)] + Pr[Bad] + (other terms).
L. Large budgets (x >= x0 ~ 2^-13): crude hazards (hidden guess + target per call) composed
   multiplicatively through a pending-debt potential V = 1 - (1 - U(r)) (1 - 2^-128)^debt on the
   lazy-table comparison; digest queries pay the baseline (1 - 2x) h additively. Gives
   Adv <= 2x - 2x^2 + 2x E[(Z - 1 + 2x)^+] + exceptions; needs E[(Z - 1)^+] <~ x0/2.
S. Small budgets (x <= x0): refined chain analysis (leanVM's route): one-step contacts are not
   forgeries; prefix rate 3/2 (two-edge completions), encoding rate 1 + markers (4032 unit
   neighbours), other 1; FORS secret guesses need a near-covered digest. Gives
   Adv <= 2x E[max(Z, r/2)] + C x^2 with r ~ 1.56 at x0; closes for x <= ~2^-13.

Projected provable lifetimes (E[(Z-1)^+] <= 2^-13.5, Poisson upper model):
    full 1.16e9 (97%), b=20 21.9e6 (92%), b=14 402e3 (87%), b=13 202e3 (84%), b=12 103e3 (82%);
    b=10 keeps 33. Unproved exact-coverage references: 1.19e9, 22.3e6, 395e3, 202e3, 103e3.
Stage 1 alone (F + L, no S; tolerance 2^((b-118)/2) from keygen slack and x^2): about 40-60%.

## Formal plan

Done: seed removal, hidden-coordinate stop, lazy outside oracle, rich program, prepared
encoding searches (`forgeAdvantage_le_prep`); win implication on non-stopped runs
(`HiddenBridge.win_implies_bad`: target hit or FORS cover with <= N signing calls).

Stage 1 (large budgets; about 10-15K lines):
 1a. Saturating potential on the lazy-table comparison (`HiddenReveal.comparison`): guesses
     create debt resolved when the coordinate is sampled, target hits are first-hit events,
     digest queries pay the baseline. Reuse `SphincsSecurity...PrimitiveMessagePotential`.
 1b. Proposal bank and signer coupling: fair-share selection symmetry
     (`LifetimePoolGrinding.poolGrindRandomness_factor`), Ville-type pool concentration,
     rejection bridge (reuse leanVM's generic proposal-word kit), proposal-count exception.
 1c. Witness-count domination F_t <= E[Psi(M) | past]; Doob martingale; Jensen with the
     baseline; excess term q E[(Psi - b)^+].
 1d. Certified bounds on E[(Z - theta)^+] for the multinomial word (exact tails per leaf,
     Poisson comparison or direct multinomial bounds); closing arithmetic for x >= x0.
Stage 2 (small budgets; about 15-20K lines): port leanVM's refined route to the candidate:
 2a. Chains (generic, reuse) and our `SecurityPrefix*` (already ported) for contacts and
     two-edge completions; markers with the WOTS+C neighbour counts (b1 = 63, b2 = 4032).
 2b. Continuing secret-guess interpreter (reuse `Forced/SecretGuess*`), near-cover x guess and
     two-guess bounds for FORS secrets.
 2c. Primitive union with a shared query allocation; closing arithmetic for x <= x0.
Then: Statement numbers, six theorems, axiom guards, docs.

R6. Resolve the reference caching/query-count transfer before claiming security of Rust itself.

The bridge files `LeanSphincs/Bridge*.lean` implement steps 1–3 (branch
`leansphincs-lifetime-bridge`).

Preserve b=10,N=33 as literally requested. No threshold/MPC work, changes to the spec,
Rust or site, or pushes. Run Lake with nice -n 19 and LEAN_NUM_THREADS=2. Every public
candidate theorem must retain an axiom guard in LeanSphincs/Axioms.lean.
