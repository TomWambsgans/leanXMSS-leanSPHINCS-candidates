import LeanSphincs.BridgeStop
import LeanSphincs.SecurityHiddenMonitors

/-! The actual SUF-CMA advantage is at most the win probability of a seed-free, budget-capped
graph-view game averaged over independent material, graph labels and remaining answers, plus
q/2^256 for naming the hidden seed. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.Reduce

open Completeness SeedCoupling Internalize Eager Short SeedModel Graph Assembly Stop HiddenCost
  GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem programGraphCache_congr_base (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (positions : List Position)
    (labels : CanonicalGraphLabels) (base base' : QueryCache HashSpec) (input : HashInput)
    (h : base input = base' input) :
    programGraphCache parameter otsSecret ftsSecret positions labels base input =
      programGraphCache parameter otsSecret ftsSecret positions labels base' input := by
  induction positions generalizing base base' with
  | nil => exact h
  | cons first rest ih =>
      apply ih
      by_cases heq : input = canonicalGraphInput parameter otsSecret ftsSecret first labels
      · subst heq
        show (base.cacheQuery _ _) _ = (base'.cacheQuery _ _) _
        simp [QueryCache.cacheQuery_self]
      · show (base.cacheQuery _ _) input = (base'.cacheQuery _ _) input
        rw [QueryCache.cacheQuery_of_ne _ _ heq, QueryCache.cacheQuery_of_ne _ _ heq]
        exact h

noncomputable local instance : SampleableType CanonicalGraphLabels := graphLabelsSampleable

variable [Params]

/-- The canonical graph cache without any seed-addressed entry. -/
noncomputable def graphCache (material : Material) (answers : CanonicalGraphLabels) :
    QueryCache HashSpec :=
  programGraphCache (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) (graphOrder (PrunedGraph.active (parameter material)))
    (labelsOf material answers) ∅

noncomputable def graphFn (material : Material) (answers : CanonicalGraphLabels) (table : Eager.Table) :
    HashInput → HashOutput :=
  extend (graphCache material answers) table

noncomputable def graphCoordinates (material : Material) (answers : CanonicalGraphLabels) :
    HiddenGraph.Table :=
  HiddenGraph.coordinates (GraphCorrectness.materialOts material) (GraphCorrectness.materialFts material)
    (labelsOf material answers)

theorem sampleFn_agree (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) (input : HashInput) (hnot : ¬SeedGuess.SeedHit input seed) :
    sampleFn material seed answers table input = graphFn material answers table input := by
  simp only [sampleFn, graphFn, extend, preparedCache, graphCache]
  rw [programGraphCache_congr_base _ _ _ _ _ _ ∅ input (programCache_agreeOutside ∅ seed material input hnot)]

theorem sampleCoordinates_eq (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    sampleCoordinates material seed answers table = graphCoordinates material answers := by
  rw [sampleCoordinates, graphCoordinates,
    ← GraphCorrectness.materialOts_eq _ seed material (sample_agreement material seed answers table),
    ← GraphCorrectness.materialFts_eq _ seed material (sample_agreement material seed answers table)]

omit [Params] in
/-- Every realized capped trace respects the budget. -/
theorem costRun_cap_cost_le {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpec α) (budget : Nat)
    (result : Option α × List (Entry HashInput))
    (hresult : result ∈ support (costRun f table (cap computation budget))) :
    traceCost result.2 ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      rw [cap_pure', costRun_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      simp [traceCost]
  | query_bind input next ih =>
      rw [cap_query_bind'] at hresult
      split at hresult
      · rename_i hcost
        rw [costRun_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hmap⟩ := hresult
        rw [support_map] at hmap
        obtain ⟨tail, htail, rfl⟩ := hmap
        have h := ih answer (budget - sourceCost input) tail htail
        simp only [traceCost_append, recorded_cost]
        omega
      · rw [costRun_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst hresult
        simp [traceCost]

/-- One seed-free capped graph-view run. -/
noncomputable def seedFreeRun (adversary : Adversary) (q : Nat) (material : Material)
    (answers : CanonicalGraphLabels) (table : Eager.Table) :
    ProbComp (Option Bool × List (Entry HashInput)) :=
  costRun (graphFn material answers table) (graphCoordinates material answers)
    (cap (costGame (parameter material) (publicData (labelsOf material answers)) adversary) q)

noncomputable def seedFreeExperiment (adversary : Adversary) (q : Nat) :
    ProbComp (Option Bool × List (Entry HashInput)) := do
  let material ← sampleMaterial
  let answers ← $ᵗ CanonicalGraphLabels
  let table ← $ᵗ Eager.Table
  seedFreeRun adversary q material answers table

def Win (result : Option Bool × List (Entry HashInput)) : Prop :=
  ∃ value, result.1 = some value ∧ value = true

theorem sample_costRun (adversary : Adversary) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) :
    𝒟[simulateQ (fixedRom (extend (preparedCache material seed answers) table))
        (countHashQueries (gameAfterSeed (internalize adversary) seed))] =
      𝒟[(fun result => (result.1, traceCost result.2)) <$>
        costRun (sampleFn material seed answers table) (sampleCoordinates material seed answers table)
          (costGame (parameter material) (publicData (labelsOf material answers))
            (internalize adversary))] :=
  (sample_costGame adversary material seed answers table).trans
    ((evalDist_fixedCostSource _ _ _).trans rfl)

/-- One sample: capped win in the seeded game is at most the seed-free win plus a seed hit. -/
theorem per_sample (adversary : Adversary) (q : Nat) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) :
    Pr[fun result : Bool × Nat => result.1 = true ∧ result.2 ≤ q |
        simulateQ (fixedRom (extend (preparedCache material seed answers) table))
          (countHashQueries (gameAfterSeed (internalize adversary) seed))] ≤
      Pr[Win | seedFreeRun (internalize adversary) q material answers table] +
        Pr[fun result => Hits (fun input => SeedGuess.SeedHit input seed) result.2 |
          seedFreeRun (internalize adversary) q material answers table] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (sample_costRun adversary material seed answers table),
    probEvent_map]
  refine le_trans (le_of_eq ?_) (le_trans (probEvent_costRun_le_cap (sampleFn material seed answers table)
    (sampleCoordinates material seed answers table)
    (costGame (parameter material) (publicData (labelsOf material answers)) (internalize adversary))
    q (fun value => value = true)) ?_)
  · rfl
  · rw [sampleCoordinates_eq]
    exact probEvent_costRun_le (sampleFn material seed answers table) (graphFn material answers table)
      (graphCoordinates material answers) (fun input => SeedGuess.SeedHit input seed)
      (sampleFn_agree material seed answers table) _ Win

omit [Params] in
theorem probEvent_bind_le_add {α β γ δ : Type} (p : ProbComp α) (k : α → ProbComp β)
    (k₁ : α → ProbComp γ) (k₂ : α → ProbComp δ) (event : β → Prop) (event₁ : γ → Prop)
    (event₂ : δ → Prop) (h : ∀ a, Pr[event | k a] ≤ Pr[event₁ | k₁ a] + Pr[event₂ | k₂ a]) :
    Pr[event | p >>= k] ≤ Pr[event₁ | p >>= k₁] + Pr[event₂ | p >>= k₂] := by
  simp only [probEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun a => (mul_le_mul' le_rfl (h a)).trans_eq (mul_add ..)

omit [Params] in
theorem traceCharge_seed_le (entries : List (Entry HashInput)) :
    traceCharge seedWeight entries ≤ traceCost entries :=
  (Nat.le_add_right _ _).trans (traceCharge_add_le seedWeight nonseedWeight seed_nonseed_entry_le entries)

/-- Naming the hidden seed in a seed-independent capped run costs at most q/2^256. -/
theorem seed_hit_le (adversary : Adversary) (q : Nat) (material : Material)
    (answers : CanonicalGraphLabels) (table : Eager.Table) :
    Pr[fun pair : MasterSeed × (Option Bool × List (Entry HashInput)) =>
        Hits (fun input => SeedGuess.SeedHit input pair.1) pair.2.2 |
      sampleMasterSeed >>= fun seed =>
        (fun result => (seed, result)) <$> seedFreeRun adversary q material answers table] ≤
      q / (2 : ℝ≥0∞) ^ 256 := by
  let run := seedFreeRun adversary q material answers table
  have hevent : Pr[fun pair : MasterSeed × (Option Bool × List (Entry HashInput)) =>
        Hits (fun input => SeedGuess.SeedHit input pair.1) pair.2.2 |
      sampleMasterSeed >>= fun seed => (fun result => (seed, result)) <$> run] =
      Pr[= true | sampleMasterSeed >>= fun seed =>
        (fun result => decide (TraceSeedHit result.2 seed)) <$> run] := by
    rw [← probEvent_eq_eq_probOutput]
    simp only [probEvent_bind_eq_tsum, probEvent_map]
    refine tsum_congr fun seed => congrArg _ (probEvent_ext fun result _ => ?_)
    simp only [Function.comp_apply, decide_eq_true_eq, Hits, TraceSeedHit]
    constructor
    · rintro ⟨input, hmem, hhit⟩
      exact ⟨.inl input, hmem, hhit⟩
    · rintro ⟨entry, hmem, hhit⟩
      cases entry with
      | inl input => exact ⟨input, hmem, hhit⟩
      | inr amount => exact hhit.elim
  rw [hevent]
  refine (seed_monitor_bound run (fun result => result.2)).trans ?_
  refine ENNReal.div_le_div_right ?_ _
  unfold expectedTraceCharge
  calc
    _ ≤ ∑' result, Pr[= result | run] * (q : ℝ≥0∞) := by
      refine ENNReal.tsum_le_tsum fun result => ?_
      by_cases hr : result ∈ support run
      · refine mul_le_mul' le_rfl ?_
        exact_mod_cast (traceCharge_seed_le result.2).trans
          (costRun_cap_cost_le _ _ _ q result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr]
        simp
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

omit [Params] in
theorem probEvent_bind_le_of {α β : Type} (p : ProbComp α) (k : α → ProbComp β) (event : β → Prop)
    (bound : ℝ≥0∞) (h : ∀ a, Pr[event | k a] ≤ bound) : Pr[event | p >>= k] ≤ bound := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' a, Pr[= a | p] * bound := ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)
    _ ≤ bound := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

omit [Params] in
theorem probEvent_bind_mono {α β : Type} (p : ProbComp α) (k₁ k₂ : α → ProbComp β)
    (event : β → Prop) (h : ∀ a, Pr[event | k₁ a] ≤ Pr[event | k₂ a]) :
    Pr[event | p >>= k₁] ≤ Pr[event | p >>= k₂] := by
  simp only [probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (h a)

attribute [local irreducible] experiment sampleMasterSeed

/-- **Seed elimination.** The actual advantage is at most a seed-free capped win plus q/2^256. -/
theorem forgeAdvantage_le_seedFree (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary ≤
      Pr[Win | seedFreeExperiment (internalize adversary) q] + q / (2 : ℝ≥0∞) ^ 256 := by
  rw [← forgeAdvantage_internalize]
  have hbound' := hashQueryBound_internalize adversary q hbound
  unfold forgeAdvantage
  calc
    _ = Pr[fun result : Bool × Nat => result.1 = true ∧ result.2 ≤ q |
          experiment (internalize adversary)] :=
      probEvent_congr' (fun result hresult => ⟨fun h => ⟨h, hbound' result hresult⟩, And.left⟩) rfl
    _ = Pr[fun result : Bool × Nat => result.1 = true ∧ result.2 ≤ q | do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          simulateQ (fixedRom (extend (preparedCache material seed answers) table))
            (countHashQueries (gameAfterSeed (internalize adversary) seed))] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_experiment_fixed adversary)
    _ ≤ Pr[Win | do
          let material ← sampleMaterial
          let _seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          seedFreeRun (internalize adversary) q material answers table] +
        Pr[fun pair : MasterSeed × (Option Bool × List (Entry HashInput)) =>
            Hits (fun input => SeedGuess.SeedHit input pair.1) pair.2.2 | do
          let material ← sampleMaterial
          let seed ← sampleMasterSeed
          let answers ← $ᵗ CanonicalGraphLabels
          let table ← $ᵗ Eager.Table
          (fun result => (seed, result)) <$> seedFreeRun (internalize adversary) q material answers table] := by
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun material => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun seed => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun answers => ?_
      refine probEvent_bind_le_add _ _ _ _ _ _ _ fun table => ?_
      rw [probEvent_map]
      exact per_sample adversary q material seed answers table
    _ ≤ Pr[Win | seedFreeExperiment (internalize adversary) q] + q / (2 : ℝ≥0∞) ^ 256 := by
      refine add_le_add ?_ ?_
      · unfold seedFreeExperiment
        refine probEvent_bind_mono _ _ _ _ fun material => ?_
        exact probEvent_bind_le_of _ _ _ _ fun _ => le_rfl
      · refine probEvent_bind_le_of _ _ _ _ fun material => ?_
        rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_bind_bind_swap sampleMasterSeed
          ($ᵗ CanonicalGraphLabels) _)]
        refine probEvent_bind_le_of _ _ _ _ fun answers => ?_
        rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_bind_bind_swap sampleMasterSeed
          ($ᵗ Eager.Table) _)]
        refine probEvent_bind_le_of _ _ _ _ fun table => ?_
        exact seed_hit_le (internalize adversary) q material answers table

end LeanSphincs.Security.Reduce
