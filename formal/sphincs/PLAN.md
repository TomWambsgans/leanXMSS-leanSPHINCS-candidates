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
an adaptive fresh-query coverage union bound; the actual verifier's 391-compression count.

Next necessary work:
1. Connect independent uniform disclosures to the checked binomial occupancy expression.
2. Bound the actual 24-tree disclosure process and its adaptive cached-query exceptions.
3. Port the WOTS/structural forgery witness and primitive bounds, including the surrogate spine
   and accepted signatures outside the retained subtree.
4. Combine the terms with the shared query budget and prove every exact N in
   Lifetimes.RequestedSecurity. All six are still open.
5. Resolve the reference caching/query-count transfer before claiming security of Rust itself.

Preserve b=10,N=33 as literally requested. No threshold/MPC work, changes to the spec,
Rust or site, or pushes. Run Lake with nice -n 19 and LEAN_NUM_THREADS=2. Every public
candidate theorem must retain an axiom guard in LeanSphincs/Axioms.lean.
