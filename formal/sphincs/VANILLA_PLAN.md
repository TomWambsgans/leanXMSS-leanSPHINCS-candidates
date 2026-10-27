# Vanilla (FORS) proofs: plan

Goal: `Secure127` (as in `LeanForest/Main.lean`, same counting) for the vanilla FTS in the 32
configurations, with the FORS of `scripts/scheme.py` (`fors(h, shape, b)`: `a = 9`, `k = 32..34`),
and the largest certifiable signature limit `N` of each.

**Layout.** A sibling library `LeanFors`, next to `LeanForest`. Both share:
- `LeanForest.Params` (the tree shape: height, layers, kept subtree, `N`);
- the scheme core (sizes, addresses, WOTS+C, trees), split out of `LeanForest/Scheme.lean` into
  `LeanForest/Scheme/Core.lean`;
- the modules that do not depend on the FTS (`Base`, the generic lazy-run interpreter, generic
  reduction lemmas), by import.

`LeanFors` holds only what depends on the FTS. The query-counting refactor (`count-by-source`) can
later be ported by applying its `LeanForest` diff to the copied modules.

**The FORS spec** (`LeanFors/Scheme.lean`):
- `k` is a field of a `ForsParams` extending `Params`, and `a = 9`;
- trees have no root hash, and the bottom WOTS+C key signs the `2k` nodes below the roots;
- one derivation hash gives two secrets;
- the digest is two calls: the index in call 0, the `k` leaf indices in the free 64-bit words of
  both calls, with no field across two words.

**Proof.** The current `LeanForest` pipeline with its FTS-specific modules redone for FORS. The
FORS-specific pieces come from the old FORS proof (`git show 767fa80^:formal/sphincs/LeanSphincs/`,
`k = 24`, `a = 10`, `h = 26`, one layer, also two digest calls):
- the two-block pairs (`pblk p 0/1`, "landed pairs have both blocks");
- the FORS cover potential and its H-term tables (`BridgeForsPotential*`, `H0*`);
- the FORS leaf contacts (`BridgeFleaf*`, `BridgeContact*`).

## Milestones

1. Scheme split; FORS spec, correctness, sizes and verification costs agree with `scheme.py`.
2. Statement, reduction, graph view and lazy run for FORS build.
3. Classification of an accepted FORS forgery.
4. Small- and large-budget potentials.
5. `fors_certificates.py` and the 32 certificates; lifetimes readable by `scheme.py`.
6. Main theorems, axiom guard, docs.
