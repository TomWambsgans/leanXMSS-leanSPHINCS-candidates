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
Stage 1 alone (F + L, no S): for every x, 2x E[(Z_x - beta(x))^+] <= x^2 + K h, with
beta(x) = (1 - 2x)/(1 - x) (the proved baseline) and Z_x at loads N/((1 - x) 2^b) (pool steering
dominated by independent coins on cached landed blocks). Estimated (Poisson loads, Chernoff
light part): b=12 48K, b=13 96K, b=14 189K, b=20 10.7M, b=26 541M (39-45% of the old values).
This is the first end-to-end target; S then lifts it to the projections above.

## Formal plan

Done: seed removal, hidden-coordinate stop, lazy outside oracle, rich program, prepared
encoding searches (`forgeAdvantage_le_prep`); win implication on non-stopped runs
(`HiddenBridge.win_implies_bad`: target hit or FORS cover with <= N signing calls).

Stage 1: DONE (2026-10-04). `Lifetimes.requestedSecurity` (StageOne.lean) proves the claims at
540000000 / 10650000 / 185000 / 93000 / 47000 / 12006 / 3046 signatures (b = 26/20/14/13/12/10/8;
b=10 and b=8 at their certified maxima, below the site's 33K and 9K).
 1a. Saturation: `BridgeSaturation.hit_bound_start`, `HiddenDebt.interp_hit_bound`.
 1b/1c. FORS potential instead of a proposal bank: witness counts over disclosed views, a virtual
     future (fresh uniform view per remaining signature, a coin per item, future pairs in front),
     signer fair share on the lazy run (`loop_bound`, `loop_bound_fresh`), domination by one
     virtual slot (`slot_ge`), presampled sibling blocks, failing-index candidates; through any
     adversary (`good_advProg`). Files Bridge{Domination,Virtual,Presample,Signer,SignerFors,
     SignerPost,InterpSupport,ForsPotential,ForsGame,Replay,ForsAssembly,Targeting}.
 1d. H0*.lean: Poisson factorial-moment domination, product-form moment majorant, exact rational
     covers checked by `decide +kernel`; tightest headroom ~0.001 bit at x ~ 2^-53 (b = 12-14).
Stage 2 (target: 80% of the best-known-attack lifetime N_att; revised 2026-10-04).
N_att (exact multinomial model, criterion E[max(X, 1/2)] <= 1): 1.203e9 / 23.80e6 / 466.9K /
242.3K / 125.7K / 33.8K / 9.07K for b = 26/20/14/13/12/10/8; stage 1 proves 0.34-0.45 of these.
Findings (scratchpad numerics, exact Poisson expectations of Z):
 - The stage-1 criterion is capped at 0.451 N_att for every b: at large x the pool coins of the
   virtual future (an independent coin per cached item in every remaining slot) inflate the loads
   to N/(1-x), and at x = 1/2 the criterion needs E[Z at 2N] <= 1/4. A fresh-randomizer signer can
   be asked to sign one message N times, which is what forces a coin per slot.
 - Small budgets need the refined route: a single chain or FORS-leaf contact is not a forgery.
 - Unit-neighbour encoding markers (<= 4032 per word, 63 per lowered chain) make the WOTS contact
   route first-order once a marker exists; a marker-state potential handles this up to x ~ 2^-7.
Decision (user, 2026-10-04): target the Rust signer, whose randomizers are derived from the seed
and the message, so a repeated request returns the same signature.
Plan, with the ideal (exact-expectation) result 0.90 / 0.90 / 0.88 / 0.87 / 0.86 / 0.84 / 0.82:
 C. Deterministic signer. New statement over `Seeded.sign`; reduce it to the fresh-randomizer game
    of the memoizing adversary (each message signed once; seed-named randomizer inputs join the
    seed-hit event). FORS potential with one coin per cached item instead of one per slot (valid
    for adversaries that never repeat a message); H0 loads N/2^b without the 1/(1-x) inflation.
 A. Linear route for x <= x_h (x_h ~ 2^-7.5 at b=8 ... 2^-19.5 at b=26). Expose the chain values
    at and above each prepared word at the start (they are only ever public). Stop at every correct
    guess (rate 1/2 per hidden row query). First-order: structural, encoding, forward-chain and
    FORS-node matches (1/2), two-edge completions (3/4 amortized via credits). Second order:
    contact x marker, contact first (63 markers), two contacts, FORS leaf contact x near cover.
    Marker-state potential W = max(r b0, V_u) with V_u' = max(3/2, 1 + 63y, 1 + 4032(2y - V_u)),
    so the non-FORS rate is r(x) = V_u(x)/(2x) in [3/4, 1). Criterion E[max(Z, r(x))] + o(1) <= 1.
    Large route (stage 1, no inflation) on [x_h, 1/2].
 D. Tighter H0 certificates (exact single-leaf Poisson sums above a cutoff, product majorant
    below), for both criteria; the current majorant loses 10-40x in E[(Z-1)^+] at 0.8 N_att.

Status (2026-10-04): stages 2 and 3 done for the deterministic signer. `LifetimesDet.requestedSecurityDet`
proves 127 bits at N = 1,156,000,000 / 22,380,000 / 412,500 / 211,900 / 108,700 / 28,600 / 7,530
(b = 26/20/14/13/12/10/8; 96.1/94.0/88.4/87.5/86.5/84.6/83.0% of N_att). Stage 3 added the
survival-weighted large-route baseline (BridgeSatW*), the FORS-leaf payment of the
contact-before-reveal term (BridgeFleaf*) and near covers arming the linear potential (BridgeArm*).
Against an attack model that includes the WOTS unit-neighbour attack (ceilings 100/99.7/97.0/96.2/
95.2/93.2/91.5% of N_att) the proved limits are 91–96% of the ceiling. Remaining losses: the k^24
price instead of distinct leaves (~2.5–3%), the coin part of the contact-before-reveal term, and the
large route's rate-1 charge for non-FORS queries at moderate budgets.

R6. Resolve the reference caching/query-count transfer before claiming security of Rust itself.

The bridge files `LeanSphincs/Bridge*.lean` implement steps 1–3 (branch
`leansphincs-lifetime-bridge`).

b=10 targets the site's 33K (the earlier literal 33 was a typo); stage 1 proves 12006. No threshold/MPC work, changes to the spec,
Rust or site, or pushes. Run Lake with nice -n 19 and LEAN_NUM_THREADS=2. Every public
candidate theorem must retain an axiom guard in LeanSphincs/Axioms.lean.
