# P2: FORS leaf contacts (A4) and the FORS leaf-step payment — handoff

Package: `LeanFors/SmallBudget/Contact/*`, `LeanFors/SmallBudget/Linear/ForestSteps.lean`, and (by
the lead's request) the new shared module `LeanFors/CoverPotential/Presample.lean`.
Template: `LeanForest/SmallBudget/Contact/*`. FORS specifics come from the old proof
(`git show 767fa80^:formal/sphincs/LeanSphincs/{BridgeContact*,BridgeFleaf*,BridgeArm*,BridgePresample}.lean`).

## Statements (exported names are unchanged, except fchain → fleaf)

- `HiddenBridge.IsFleafIn p x := ∃ f : FIn, x = f.input p`. It was `IsFchainIn`; SampleBound and
  SampleEvents must rename it.
- `PotentialA.smallRoute_potentialF`: same shape. Every FORS leaf query (hash of a secret) is paid
  `(ρ - 1 - x)/2^128`.
- `ForestPotential.revRate := ((2^subtreeHeight * 2^forsHeight : ℕ) : ℝ≥0∞)⁻¹`. There is no 123
  factor. The lead adapts `revRate_eq` and `arm_paysF` in SampleEvents.
- `reveal_le_all … (index κ leaf) : E[1{∃ q, .fors index κ leaf q ∈ reveals}] ≤ revRate + hitMass`.
- `A4ev K root T s outcome R := (∃ index κ leaf, .fors index κ leaf 0 ∈ R ∧ RecordedContactAt s T K
  index κ leaf) ∨ ForestNearRecorded s T K root outcome R`, plus `finalA4`. `a4F_bound` has the same
  shape as in the forest. Its `hparse` and `hclean` are over `∀ p call`.
- Near: `NearSub target κ D := ∀ κ' ≠ κ, TreeCovered target κ' D`,
  `witnessNear := Σ_κ [NearSub]` (≤ forsTrees), `witnessNear_props`, `nearWitness_pos`, and
  `H0.priceNear_decomp : priceW witnessNear d = Σ_l κE * yN (marksAt l d)` (an equality).
- Rest as in the forest: `startNearF`, `rateS`, `expCount`, `psiF`, `BInvF` (without `rclosed`),
  `Settled R f := .fors f.index f.κ f.leaf 0 ∈ R`, `OpensF f L := ∃ q, .fors f.index f.κ f.leaf q ∈ L`
  (to be written in Signing).

## Interface answers received (decisions)

Lead (owns Linear/*, CoverPotential/Basic, OneCoinGame, ScanSigner, SampleEvents):
1. `FIn = {index, κ, leaf, v}`, `input p f = HiddenGraph.input p (.fleaf index κ leaf, v)`,
   `inC = .fors index κ leaf 0`, `outC = .fors index κ leaf 1`. Lemma names change fchain → fleaf:
   `fleaf_inj`, `msg_ne_fleaf`, `input_fleaf`, `step_fleaf`. `fin_eq_of_inC` keeps its name.
   `Rel f g := f.index = g.index ∧ (f.κ, f.leaf) ≠ (g.κ, g.leaf)`. Anchor has no FORS part.
2. `TreeCov (revealed) (view) κ := view.2 κ ∈ revealed view.1 κ`, and
   `revealedSet reveals index κ := univ.filter (.fors index κ · 0 ∈ reveals)`. ForestNearRecorded
   ends with `∃ κ, RecordedContactAt … (digestIndex digest) κ (digestLeaves digest κ) ∧
   ∀ κ' ≠ κ, TreeCov (revealedSet reveals) (fullDigestView digest) κ'`.
3. Pairs over digest calls: `pblk p call`; `viewOf (u : DigestCall → HashOutput)`; `pview`;
   `LandedIn s p := ∃ u0, s.cache (pblk p firstCall) = some u0 ∧ Landed (blockIndex u0)`;
   `PInv.{nodup, mem, all, first}`; `withPair s p u` stores every call;
   `addPair P p u := if Landed (blockIndex (u firstCall)) then p :: P else P`;
   `pairE F := ∑' u, Pr[= u | $ᵗ (DigestCall → HashOutput)] * F u`; `hparse : ∀ p call`.
   **Ask the lead to define `withPair s p u := storeAll (pblk p) u s`** (from Presample.lean),
   or to prove that equality.
4. `ForestOk digest x := ∀ i κ l q, x = .fors i κ l q → i = digestIndex digest ∧
   l = digestLeaves digest κ`. `DInv R d := ∀ i κ l q, .fors i κ l q ∈ R → ∃ v ∈ d,
   v.1 = localIdx i ∧ v.2 κ = l`. `localDigestView.2 = digestLeaves`. The signer queries no FORS
   leaf input, and its FORS opening reveals q = 0 and q = 1 (`treeCostSource`).
5. FORS needs no UpClosed or rclosed.

P1 (owns CoverBound): `CoverF t Xs := t ∈ Xs`, `φF`,
`nearFactor κ κ' Xs := freshAvg univ (fun t => if κ' = κ ∨ CoverF t Xs then 1 else 0)`,
`yN Ms := Σ_κ Π_κ' nearFactor κ κ' (Ms.map (· κ'))`, with no min. Also used from P1:
`mem_marks_map`, `marksAt`, `κE`, `H0Avg.freshAvg_prod`, `freshAvg_pi_prod`, `freshAvg_const'`.

## Status of the files

- `Linear/ForestSteps.lean`: drafted (FORS cases, `Address.fleaf`). It builds once Linear/* has
  the FIn and lemma names above.
- `Contact/RunFacts.lean`: Closed section removed and `IsFc` added for `.fors`. Open: Avoid section
  (`avoids_finishRest_fleaf`, `avoids_loop_fleaf`), which must follow the lead's multi-call
  `finishCostSource` and `finishRest` (`avoids_treeCostSource` is assumed).
- `Contact/NearWitness.lean`: drafted against P1's API.
- `Contact/RevealRate.lean`: leaf-hit part drafted (`opensAt`, `revRate`, `freshAvg_opensAt`). Open:
  the signing part still uses one block `u0` (`finish_reveals_ok`, `reveal_scan_all`); move it to
  `u : DigestCall → HashOutput` and `pblk p call` following the lead's `loop_boundV` and `pairWeight`.
- `Contact/PaidPotential.lean`: invariants without `rclosed`, multi-call `NewPairPaysF` and
  `OrdinaryPaysF`, and `binvF_withPair` against assumed `extends_withPair`, `Ctx.inv_withPair` and
  `pinv/minv/count_withPair`. Open: `goodXF_ordinary`'s new-pair case. It should use
  `PInv.first` and `interp_presample_new` with `x = pblk p`, `c` = the queried call, and `F` = final
  value + pay·count. Monotone under fresh stores: G must satisfy `hG` as in old BridgeFleafGame
  (`hGstore`); check that finalA4 is monotone (old `finalA_store`/`finalB_store`). Then `pairE`
  must be converted to `(card^n)⁻¹ Σ_u` (use `tsum_uniform_eq` at the function type).
- `Contact/Weights.lean`: not yet edited. It is mostly mechanical: case `Address.fchain` becomes
  `Address.fleaf index κ leaf`, and `fchain_inj` becomes `fleaf_inj`.
- `Contact/Potential.lean`: not yet edited. Change `Settled` to the definition above. In
  `not_settled_of_unknown`, drop `hclosed` and use `rinv` directly. The pair lemmas
  (`offMass_newPair`, `offMass_blocks`, `blk`) go multi-call with the lead's ScanSigner/Groups.
- `Contact/Signing.lean`: not yet edited. Define `OpensF` as above and drop `kTop`. In
  `sign_step_facts`, the exposure of outC comes only by reveal (no anchor case), so OpensF covers it.
  `writes_fleaf` covers `.fors` coordinates.
- `Contact/Bound.lean`: only renamed. Update `A4ev`, `potNF_ge_of_near` (multi-call cachedDigest,
  `pview` over all calls, `nearWitness_pos hB.dinv digest κ hcov`) and the `hsub` destructuring.
- `CoverPotential/Presample.lean` (new, shared, mine): ports BridgePresample and
  `interp_presample_le/eq`, and adds `storeAll`, `storeAll_perm`, `interp_presampleAll_le` and
  `interp_presample_new`. Last build had 5 errors:
  - lines 365–397 (`storeAll_cache_self`/`storeAll_perm`): `.cache y` rewrites fail ("function
    expected" under instance transparency), and one instance fails to synthesize at line 367.
    Restate them with `show` or `simp only [DebtState.store, QueryCache.cacheQuery…]`, or prove
    `cache` equalities through `Option` congr.
  - line 462: `rw [store_cache_ne]` fails on `Fin.tail x i`. Prefix it with
    `show (state.store (x 0) v).cache (x i.succ) = none`, as already done at line ~508.
  It also needs adding to `LeanFors.lean` (lead's file: ask the lead).

## Next steps

1. Fix Presample.lean (above) and build `LeanFors.CoverPotential.Presample`. It depends only on
   `LeanFors.LazyRun.Presample`, which builds now.
2. Once the lead signals that Linear/*, CoverPotential/Basic and ScanSigner build: build ForestSteps,
   then RunFacts → NearWitness → RevealRate → PaidPotential → Weights → Potential → Signing → Bound.
3. No sorry or axioms. Commit with explicit paths.
