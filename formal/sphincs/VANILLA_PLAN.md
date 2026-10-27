# Vanilla (FORS) proofs: plan and handoff status

Goal: `Secure127` (as in `LeanForest/Main.lean`, same counting) for the vanilla FTS (FORS) in the 32
configurations (h ∈ 22, 24, 26, 28; full key, pruned b ∈ 20, 14, 13, 12, 10, 8, layered 10+6+6,
12+6+6, 12+7+7, 12+8+8), each with the largest certifiable `N`, and lifetimes readable by
`scripts/scheme.py`. Same axiom guard as Main, no sorry, 0 warnings.

## Layout and parameters

- `LeanFors` is a sibling library of `LeanForest` (lakefile `[[lean_lib]] LeanFors`). It started as a
  copy with the namespace `LeanForest → LeanFors`, and the forest FTS is replaced by FORS. LeanForest
  is untouched. Splitting out a shared scheme core was dropped because `HashDomain` and `Signature`
  depend on the FTS.
- `Params` has the extension fields `forsTrees` (k ≤ 64) and `forsHeight` (a, 2..12). The library
  is generic in (k, a). The digest has `digestCalls = ⌈(h + k a)/256⌉` calls (≤ 4), `DigestCall`,
  and `firstCall`. Only certificates use concrete values: a = 10 everywhere; k = 25 for the full and
  layered keys and for h=22 b=20; k = 26 for the other pruned keys (scheme.py `fors(h, shape, b)`,
  fe57807). Every configuration has 2 digest calls.
- FORS spec (`Scheme.lean`): trees have no root hash, and the bottom WOTS+C key signs the 2k
  level-(a-1) nodes (`rootsPayload`). One derivation gives two secrets (`leafPair`). The index is the
  low h bits of call 0 (`blockIndex`); leaf κ is bits `h + aκ ..` of the concatenated digest
  (`digestLeaves`).

## Build status (2026-10-27, WIP commit on spicy-toggle)

**Builds:** Scheme/* (correctness, DigestView, sizes, verification costs = scheme.py),
Configurations, Seed/*, GraphView/* (CountedGame included), LazyRun/* (HiddenOracle, FixedRun,
ShortQueries included), Reduction/* (CostProgram, WinValue included), Statement,
Classification/{Forest (FORS), Tree, Signature, Hidden, Verifier, Chain, Wots, Encoding, Reference,
Accepted, Win}.

**Does not build yet (in order of the critical path):**
1. `Classification/SignedReveals`: `SignedRevealed.fchain_mem` must become `fors_mem`
   (`.fors (digestIndex d) κ (digestLeaves d κ) k ∈ reveals`, from `mem_treeReveals_of k`).
2. `ScanSigner/FairShare` (46 errors), then the rest of ScanSigner:
   - `coordCostSource` → `GraphView.treeCostSource`;
   - `avoids_coordCostSource` → a tree version;
   - the **two-call digest**: the signer's landing test reads only the block of `firstCall`, but
     the view and the disclosure need every call. Port the old LeanSphincs approach
     (`git show 767fa80^:formal/sphincs/LeanSphincs/BridgeForsPotential.lean`) generically over
     `DigestCall`.
3. `Classification/Targeting` (it imports FairShare). Then RefinedEvents, RecoveredForest, WinRefined
   and RefinedOutcome. RecoveredForest is forest-specific (chain matches): replace it with the plain
   FORS classification (`Fors.recover_classification`), since FORS has no structural chain walk.
   **Milestone for P2:** LazyRun/* (done) and Classification/{Accepted (done), Win (done),
   WinRefined, Targeting} build. Tell the coordinator when this is reached.
4. CoverPotential/* (except Price, which is ported: `TreeCovered`, `CoverAll`), with the pair shapes
   below. They use P2's `CoverPotential/Presample.lean` (`new_pair_bound`).
5. SmallBudget/Linear (except ForestSteps, which is P2's), SmallBudget/{SampleBound, SampleEvents,
   Closing}. SampleEvents: `revRate_eq` and `arm_paysF` change to the new `revRate` (below).
   SampleBound, SampleEvents and Closing still import the deleted `CoverBound/UniformMark`.
6. LargeBudget/*, Certificates/Closing, Lifetimes, Main, Axioms, docs (planned for P3).
7. Warning cleanup (0 warnings): for example, unused simp arguments at `LazyRun/GraphRows.lean:57`
   and in `GraphView/Pruned` simp calls.

**Helpers' modules (do not edit, theirs):**
- P1: CoverBound/*, `scripts/fors_certificates.py`, Certificates/{Build, H22..H28}.
- P2: SmallBudget/Contact/*, SmallBudget/Linear/ForestSteps.lean, CoverPotential/Presample.lean.

## Fixed interfaces

- **Graph.**
  - `Position.fleaf index κ leaf` (row: secret → leaf) and `Position.fnode index κ level node`
    (level ℓ is tree level ℓ+1).
  - `Coordinate.fors index κ leaf q`: q = 0 is the secret (input), q = 1 the leaf value (output).
  - `Address.fleaf`.
  - `IsRowPosition` = chain or fleaf.
  - `KnownCoordinate (.fors _ _ _ q) := q = 1`: leaf values are known, secrets hidden.
  - `IsPublicPosition` = everything but chain steps: the public data reads fleaf labels, since the
    level-0 path nodes are leaves. Lemmas: `cellKnown_fleaf`, `cellKnown_public`.
- **Signer.**
  - `GraphView.treeCostSource data index κ leaf` reveals q = 0 and q = 1 (both), and takes the path
    from `data.forsPath`.
  - `assembledFors`; `FixedRun.treeReveals index κ leaf` (`mem_treeReveals`, `mem_treeReveals_of`).
  - The signer's tick after the digest is `forsTrees * treeOpenCost`.
  - `finishHashCost = digestCalls + forsTrees * treeOpenCost + seqCost …`.
- **Digest.**
  - `Win.cachedDigest` = `allSome` over the calls, mapped through `truncateMessageDigest`.
  - `digestInputs_mem … call` and `message_not_row … payload call` take the call.
  - The signer's loop uses `messageDigestCall … firstCall`.
- **Cover.**
  - `DigestView.TreeCov revealed view κ := view.2 κ ∈ revealed view.1 κ`, and
    `Covered := ∀ κ, TreeCov`.
  - `Win.revealedSet reveals index κ := {leaf | .fors index κ leaf 0 ∈ reveals}`.
  - `reach_fors`; `queried_fleaf_revealed` (a queried honest secret was revealed).
  - `Accepted.forsException_hit`.

### Answers given to P2 (binding for my modules)
1. `Linear/Potential`:
   - `FIn = {index, κ, leaf, v : Digest}`;
   - `input p f = HiddenGraph.input p (.fleaf f.index f.κ f.leaf, f.v)`;
   - `inC = .fors index κ leaf 0`, `outC = .fors index κ leaf 1`;
   - lemma names keep the forest names, except fchain → fleaf (`fleaf_inj`, `msg_ne_fleaf`,
     `input_fleaf`, `step_fleaf`);
   - `Rel f g := f.index = g.index ∧ (f.κ, f.leaf) ≠ (g.κ, g.leaf)`.

   P2 renames its export IsFchainIn → IsFleafIn (used in SampleBound and SampleEvents).
2. ForestNearRecorded and A4: the contact is at tree κ, leaf `digestLeaves digest κ`, and
   `∀ κ' ≠ κ, TreeCov (revealedSet reveals) (fullDigestView digest) κ'`.
3. CoverPotential pairs:
   - `pblk p call`;
   - `viewOf (u : DigestCall → HashOutput)` = kept view of `truncateMessageDigest u`;
   - `pview s p = (allSome fun call => s.cache (pblk p call)).elim default viewOf`;
   - `LandedIn s p` = the `firstCall` block is cached and lands;
   - `PInv` = nodup, mem, `all` (landed → every call cached), `first` (`firstCall` uncached → every
     call uncached);
   - `withPair s p u` stores every call;
   - `addPair` tests `u firstCall`;
   - `pairE F = ∑' u, Pr[= u | $ᵗ (DigestCall → HashOutput)] * F u`;
   - one `hparse : ∀ p call, model.parse (pblk p call) = none`;
   - `View = Fin 2^subtreeHeight × (FTree → FLeaf)`.
4. ScanSigner:
   - `ForestOk digest x := ∀ i κ l q, x = .fors i κ l q → i = digestIndex digest ∧ l = digestLeaves digest κ`;
   - `DInv`: every revealed `.fors i κ l q` (any q) has `v ∈ d` with `v.1 = localIdx i ∧ v.2 κ = l`;
   - `localDigestView.2 = digestLeaves`.
5. FORS has no UpClosed. `Settled R f := f.inC ∈ R`. The signer reveals both positions, so rinv
   gives known ≠ none for both.
6. `revRate := ((2^subtreeHeight * 2^forsHeight : ℕ) : ℝ≥0∞)⁻¹`, with no factor 123.

## Risks

- **The two-call digest** in ScanSigner/FairShare and CoverPotential is the largest remaining
  piece:
  - an adversary query to any call of a new pair must presample the other calls (P2's
    `new_pair_bound`);
  - the fair share argument must treat the pair's block tuple, not one block.
- The Lean generalization (generic k, a, digestCalls) can make `decide`/`norm_num` steps slow. Keep
  concrete values in Certificates only.
- Disk: stop if `df -h /root` Used goes above 432G.
