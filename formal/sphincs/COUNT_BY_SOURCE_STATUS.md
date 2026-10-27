# Count by source: status (paused)

Goal: state the security theorem the way b-wagn's SLH-DSA proof does. The counted work is the
adversary's hash queries plus the verification hashes, optionally plus the signing requests. Key
generation and the signer are free. Target: the same 32 lifetimes, with the keygen credit `K`
removed.

## Done (on branch `count-by-source`)

- **Cost spec** (`LazyRun/Cost.lean`): the tick slot is replaced by an honest-query slot,
  `SourceCostSpec D R ι := SourceSpec + (Honest D →ₒ R)`.
  - Honest queries cost 0, are recorded as `.inr x` (`Entry D := D ⊕ D`), and are not touched.
  - `queryInput` gives the input of an ordinary or an honest query.
- **Graph-view signer** (`GraphView/CountedGame.lean`):
  - The walk digest, the finish digest and the WOTS+C counter search (`honestly`) are honest
    queries. There are no ticks.
  - `costGame` and `costGameX` have no keygen tick, and `costGameDet` has no randomizer tick.
- **Fixed-function bridge for the signer**:
  - `fixed_signCostDetLoop` and `signCostDet_correct` (`Reduction/CostProgram.lean`) now evaluate
    to `pure (evalWithAnswerFn f …)` at no cost.
  - `finishCostSource_correct` (`GraphView/CountedGame.lean`) does the same.
- **Honest queries handled throughout**: `UntilSeed` (`Hits` covers honest entries too),
  `UntilHidden`, `RunSupport`, `FixedRun`, `Saturation` (`costStep_honest_eq`), `Presample`
  (`costStep_honest`), `Interpreter`, `InterpreterFacts`, `LazySigner` (`interp_honest`,
  `avoids_honestLift`; `Avoids` now covers honest queries), `FairShare`, `AfterSigning`, `Scan`,
  `ScanReveals`, `SignedReveals`, `Win`/`WinRefined` (the run agreement covers honest inputs),
  `WinValue`, `PreparedRun` and `Replay`.
- **Seed elimination**: honest inputs are short tweakable inputs (`Short.IsHonest`, carried by
  `OnlyC`). No seed marks them (`not_marked_of_honest`, `honest_not_seedHit`). `marked_hit_le`
  takes this as a hypothesis, and `onlyC_costGameDet` supplies it.
- **Generic potential inductions**: these need honest queries that change nothing but a fresh
  message digest. That condition is the `Fine` predicate with `HonestOk` (`LazyRun/Interpreter.lean`).
  - `interp_potential2` (`Payments`), `saturationW` (`SurvivalWeight`) and
    `smallRoute_potentialF` (`ForestSteps`) now take a `Fine` hypothesis.
  - Their honest steps are proved: a cached read keeps the state; a fresh message digest uses
    `step_other` with `kindUnit = 0`.
  - `fine_honestLift_replay` (`Replay`) gives `Fine` for a prepared search, and `interp_fine_post`
    turns `Fine` into a support fact.
- **Count invariant**: `CountInv` (`CoverPotential/Basic.lean`) now covers live messages only and
  takes the log `L`. The callers of `sign_paramsS` are updated to pass `L`.

## Not done yet

The library does not build.

1. **Build failures at the pause**:
   - `CoverPotential/OneCoin.lean:1012` hits the max recursion depth in the new count part of
     `sign_paramsS`. The likely fix is to replace `congr 1; ext ρ` with `Finset.filter_congr` and
     `hother`.
   - `LargeBudget/WeightedScan.lean:159` fails an `assumption`, probably a leftover budget
     `- 1` after the honest rewrite of `trial_boundSW`.
   - `SmallBudget/Contact/RunFacts.lean` has honest cases still to add.
   - After these: the rest of `Contact/*`, `SampleEvents`, `SampleBound`, `Closing`,
     `LargeBudget/*` and `Certificates/Closing`.
2. **`Fine` for the actual program**: prove
   `Fine (sampleModel …) (HonestOk … IsMsgInput) (fun _ _ => True) (costGameX …) start` from
   states with `Prepared`. The proof goes by induction over the adversary program.
   - The signer's digests are message inputs with `parse = none`.
   - The searches are replays of the prepared ones (`preparation_parts`,
     `fine_honestLift_replay`, `not_row_encoding`).
   - Prepared is kept by `costStep` (`extends_costStep`).
   - Then pass this hypothesis in `SampleBound` and the large-budget routes.
3. **Remove the keygen credit** from `SampleBound`, `Closing`, `LargeBudget/Route`,
   `LargeBudget/HeavyRoute` and `Certificates/Closing`: `q - keygenCost` becomes `q`, and there
   are no `interp_tick_bind` steps. Check `FairS`/`Cmax`: it is still `Qtot + 2^32`, the walk's
   own attempts.
4. **Front end**:
   - `Statement.lean`: program-level counting, `QueryCap.counted` on the adversary's hash queries
     plus `countHashQueries` on verify. The experiment is the ROM run of that game.
   - Re-prove `budgetedWin_le_internalize`, `evalDist_experiment_fixed` and the bridge
     `costGameDet_correct` / `fixedCostSource_restDet` / `fixedCostSource_interactionDet`. These
     three are `sorry` in `Reduction/CostProgram.lean`. The bridge goes by induction over the
     adversary program: the adversary's hash queries count 1, signing is free and evaluates
     purely, and verification counts 1.
   - Decide whether to count signing requests: leaving them out gives a stronger statement.
5. **Clean-up**:
   - Dead exact-cost code: `GraphView/Cost.lean` section 2, `HashCalls` exact-cost lemmas,
     `keygenHashCost` in the proof, `Linear/Payments` `fleafCount_cons_inr`.
   - Regenerate the certificates with `scripts/forest_certificates.py` and `K = 0` (expect the
     same `N`).
   - Update the docs: `Main.lean` header, `Statement.lean`, `PROOF.md`, `README.md`.
   - Run the axiom guard and `scripts/doc_check.py`.

Build only with the scratchpad `lb.sh` (flock, MemoryMax=28G), in the worktree
`/root/sphincs-lean`.
