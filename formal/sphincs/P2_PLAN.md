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

- `CoverPotential/Presample.lean`: **builds** (`17e5c6e`, `6e84bc7`). Ports BridgePresample and
  `interp_presample_le/eq`, and adds `storeAll`, `storeAll_perm`, `interp_presampleAll_le`,
  `interp_presample_new` (used by ScanReveals and by `withPair`), and the equality versions
  `interp_presample_fresh_eq`, `interp_presampleAll_eq`, `interp_presample_new_eq` for a value of
  the run alone (the expected query count), which is what lets the new-pair step keep its payment.
  Traps: a `QueryCache` application is not a function application under `instances` transparency, so
  state cache facts with `have … : … = …` and compose with `.trans` instead of rewriting inside
  `.cache _`; `rw` patterns must match syntactically (`x ∘ σ`, `Fin.tail x i` needs a `show`); and
  `store_cache_ne` keeps `[Params]`.
- `Linear/ForestSteps.lean`: **builds** unchanged on the lead's Linear/*.
- `Contact/RunFacts.lean`: **builds** (`5ca5a1d`). `IsFc` is the FORS class; the Avoid section
  follows the multi-call `finishCostSource_eq` (`avoids_sequenceFin` + `avoids_read`).
- `Contact/NearWitness.lean`: drafted against P1's API; **blocked** on `CoverPotential/OneCoin`
  (P6, still single-call `hparse : ∀ p`), which `GenericWitness` imports.
- `Contact/RevealRate.lean`: ported (unbuilt): `cached_reads_reveals` (reads of cached inputs keep
  the reveals, an aborted run reveals nothing), `finish_reveals_ok` over the block tuple `u`, and
  `reveal_scan_all`/`reveal_le_all` against the lead's new `loop_boundV` (extra `hkind` and
  `PairInv` arguments, `hVfin` over `u : DigestCall → HashOutput`).
- `Contact/PaidPotential.lean`: ported (unbuilt). The new-pair case of `goodXF_ordinary` queries one
  call `c` of the pair: `interp_presample_new` moves the final value to `withPair` (monotone by the
  new `hGstore`), `interp_presample_new_eq` moves the query count back, and `pairE` is converted
  with `tsum_uniform_eq` and `Fintype.card_fun`. New hypotheses threaded through
  `goodXF_{ordinary,liftHash,advProg}` and `final_le_startF`: `hmsg : ∀ x, IsMsgInput x →
  K.tg.kind x = .none` and `hGstore`.
- `Contact/Weights.lean`: ported (unbuilt): `Address.fleaf`, and `wsum_storeAll_other` for the
  digest blocks of a new pair stored at once.
- `Contact/Potential.lean`: ported (unbuilt): `Settled R f := f.inC ∈ R`, `not_settled_of_unknown`
  without `hclosed`, and the pair lemmas over `u : DigestCall → HashOutput` with the landing test at
  `firstCall`.
- `Contact/Signing.lean`: ported (unbuilt): `OpensF f reveals := ∃ q, .fors f.index f.κ f.leaf q ∈
  reveals` (no `kTop`), `sign_step_facts` without the anchor case, `hmsg` for `reveal_le_all`'s
  `hkind`, and `PairInv` built from `hB.pinv`.
- `Contact/Bound.lean`: ported (unbuilt): `A4ev` over a revealed secret, `cachedDigest_mono`,
  `a4ev_store` and `finalA4_store` (the `hGstore` of `finalA4`), `potNF_ge_of_near` over `pblocks`,
  and `hparse`/`hclean`/`hmsg` per call.

## Next steps

1. Presample, ForestSteps and RunFacts build and are committed.
2. The rest of the chain (NearWitness → RevealRate → PaidPotential → Weights → Potential → Signing
   → Bound) is blocked on `CoverPotential/OneCoin` (P6): it still takes the single-call
   `hparse : ∀ p, model.parse (pblk parameter data p) = none`, so `GenericWitness` and with it
   `Contact/NearWitness` do not build.
3. The lead owes nothing else; the two new obligations handed up are `hmsg` and `hGstore` on
   `a4F_bound` (`hGstore` is discharged inside Bound by `finalA4_store`, `hmsg` is the standard
   `∀ x, IsMsgInput x → tg.kind x = .none` of SampleBound).
4. No sorry or axioms. Commit each module as it builds, with explicit paths.
