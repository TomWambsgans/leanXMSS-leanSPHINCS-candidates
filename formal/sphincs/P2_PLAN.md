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

- `CoverPotential/Presample.lean`: **builds** (commit `17e5c6e`). It ports BridgePresample and
  `interp_presample_le/eq`, and adds `storeAll`, `storeAll_perm`, `interp_presampleAll_le` and
  `interp_presample_new`. Three traps, for the record: `DebtState.cache` is a `QueryCache`, so a
  cache application is not a function application under `instances` transparency — `rw`/`simp`
  inside its argument fails, and the cure is to state the fact with `have … : … = …` or to compose
  with `.trans` instead of rewriting; a pattern must match syntactically (`x ∘ σ`, not
  `fun i => x (σ i)`; `Fin.tail x i` needs a `show … (x i.succ) …` first); and `store_cache_ne`
  (LazyRun/Presample) keeps `[Params]`, so a lemma that `omit`s it must redo the step with
  `simp only [DebtState.store, QueryCache.cacheQuery_of_ne _ _ hne]`.
  **It still has to be added to `LeanFors.lean` (lead's file).**
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
- `Contact/Weights.lean`: drafted (unbuilt): `Address.fleaf index κ leaf` in `input_of_guess` and in
  `wsum_ordinary`'s new-step case.
- `Contact/Potential.lean`: drafted (unbuilt): `Settled R f := f.inC ∈ R` (that is
  `.fors f.index f.κ f.leaf 0 ∈ R`), and `not_settled_of_unknown` without `hclosed`. Open: the pair
  lemmas (`offMass_newPair`, `offMass_blocks`, `blk`), which go multi-call with the lead's
  ScanSigner/Groups.
- `Contact/Signing.lean`: drafted (unbuilt): `OpensF f reveals := ∃ q, .fors f.index f.κ f.leaf q ∈
  reveals` (no `kTop`), `writes_fleaf` over `Address.fleaf`, `sign_step_facts` without the anchor
  case (the exposure of outC is the revealed leaf value, `⟨1, h⟩`), `settled_append` by
  `List.mem_append_left`, and `hparse : ∀ p call` in `sign_contact` and `psiF_sign`.
- `Contact/Bound.lean`: drafted (unbuilt): `A4ev` as above, the `hsub` destructuring, and the
  ForestNearRecorded destructuring of `potNF_ge_of_near` (`nearWitness_pos hB.dinv _ κ hcov`).
  `hparse`/`hclean` are `∀ p call`, and the "no message input is a leaf input" argument assumes
  `msgInput_digestInput K.p root m ρ call` (**call last** — the lead confirms or I swap it). Open:
  `potNF_ge_of_near`'s `cachedDigest`/`pview` block, which is still one block `u0`.

## Next steps

1. ~~Fix Presample.lean~~ done, builds, committed. Waiting on the lead to import it from
   `LeanFors.lean`.
2. Everything else of mine is blocked on `LeanFors.ScanSigner.FairShare`, which is the first module
   to fail for every Contact target (and for ForestSteps, through RunFacts). Nothing of mine has
   been compiled since.
3. Once the lead signals that Linear/*, CoverPotential/Basic and ScanSigner build: build ForestSteps,
   then RunFacts → NearWitness → RevealRate → PaidPotential → Weights → Potential → Signing → Bound.
   The multi-call parts left open above (RevealRate's signing part, PaidPotential's new-pair case,
   Potential's pair lemmas, Bound's `potNF_ge_of_near`) need the lead's final `pblk p call`,
   `pview`, `withPair` and `loop_boundV`.
4. No sorry or axioms. Commit with explicit paths.
