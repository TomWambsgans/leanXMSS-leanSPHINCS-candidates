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
local cache-potential accounting against the actual shared query budget.

Next necessary work:
1. Bound the actual adversarial 24-tree disclosure process and its cached-query exceptions.
2. Substitute privileged honest derivations by prepared-material reads with virtual cost,
   then prove seed independence of the ordinary adversarial view before a seed hit.
3. Connect the checked WOTS/structural/FORS witnesses to primitive probability bounds and
   the seeded-to-independent-secret coupling, with reference-free leaves handled explicitly.
4. Combine the terms with the shared query budget and prove every exact N in
   Lifetimes.RequestedSecurity. All six are still open.
5. Resolve the reference caching/query-count transfer before claiming security of Rust itself.

Preserve b=10,N=33 as literally requested. No threshold/MPC work, changes to the spec,
Rust or site, or pushes. Run Lake with nice -n 19 and LEAN_NUM_THREADS=2. Every public
candidate theorem must retain an axiom guard in LeanSphincs/Axioms.lean.
