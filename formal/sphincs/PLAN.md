# Continuation checkpoint

The imported leanVM baseline was committed as 3289130; its original unverified numerical
planning notes are preserved in that commit. Current candidate work is in `LeanSphincs/`,
with proof status and mismatches in README.md and PROOF.md. Do not mistake a successful
legacy build for a candidate security theorem.

Completed: candidate scheme and independent-randomizer game; seeded correctness at all
pruning heights; correctness of assembly from a landed randomizer; exact target-sum code
count; fresh-input counter and collision-aware seeded grinding bounds; exact subtree
landing probability and fixed-disclosure FORS coverage; signature serialization length.

Next necessary work:
1. Connect the randomizer loop in Randomized.lean to a collision-aware probability bound.
2. Prove domain-separation freshness after keygen and compose an end-to-end completeness bound.
3. Bound the 24-tree distinct-disclosure process and its adaptive cached-query exceptions.
4. Port the WOTS/structural forgery witness and primitive bounds, including the surrogate spine.
5. Combine the terms with the shared query budget and prove every exact N in
   Lifetimes.RequestedSecurity. All six are still open.
6. Resolve the reference caching/query-count transfer before claiming security of Rust itself.

Preserve b=10,N=33 as literally requested. No threshold/MPC work, changes to the spec,
Rust or site, or pushes. Run Lake with nice -n 19 and LEAN_NUM_THREADS=2. Every public
candidate theorem must retain an axiom guard in LeanSphincs/Axioms.lean.
