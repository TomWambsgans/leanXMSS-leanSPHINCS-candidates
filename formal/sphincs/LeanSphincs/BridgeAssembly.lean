import LeanSphincs.BridgeEager
import LeanSphincs.SecurityGraphCountedGame
import LeanSphincs.SecurityGraphSampling

/-! The actual experiment of a short-query adversary as an average over independent seed
material, canonical graph labels and a uniform table on all remaining short inputs. Each sample
is then a fixed answer function to which the graph-view game equality applies. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.Assembly

open Completeness SeedCoupling Internalize Eager Short SeedModel Graph

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

theorem OnlyW.counted {α : Type} (selected : OracleWorld.Domain → Prop) [DecidablePred selected]
    (oa : OracleComp OracleWorld α) (h : OnlyW oa) :
    OnlyW (SphincsSecurity.QueryCap.counted selected oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => exact OnlyW.pure' _
  | query_bind input next ih =>
      rw [OnlyW, isQueryBoundP_query_bind_iff] at h
      rw [SphincsSecurity.QueryCap.counted_query_bind, OnlyW, isQueryBoundP_query_bind_iff]
      refine ⟨h.1, fun answer => ?_⟩
      have hnext : OnlyW (next answer) := by
        have := h.2 answer
        split at this <;> simpa [OnlyW] using this
      have hbind : OnlyW (SphincsSecurity.QueryCap.counted selected (next answer) >>= fun result =>
          (pure (result.1, (if selected input then 1 else 0) + result.2) :
            OracleComp OracleWorld (α × Nat))) :=
        OnlyW.bind (ih answer hnext) (fun _ => OnlyW.pure' _)
      split <;> simpa [OnlyW] using hbind

/-- Two handlers with equal per-query distributions give equal simulated distributions. -/
theorem evalDist_simulateQ_congr {ι : Type} {spec : OracleSpec ι} {m₁ m₂ : Type → Type}
    [Monad m₁] [LawfulMonad m₁] [Monad m₂] [LawfulMonad m₂]
    [MonadLiftT m₁ SPMF] [LawfulMonadLiftT m₁ SPMF] [MonadLiftT m₂ SPMF] [LawfulMonadLiftT m₂ SPMF]
    (impl₁ : QueryImpl spec m₁) (impl₂ : QueryImpl spec m₂)
    (h : ∀ input, 𝒟[impl₁ input] = 𝒟[impl₂ input]) {α : Type} (oa : OracleComp spec α) :
    𝒟[simulateQ impl₁ oa] = 𝒟[simulateQ impl₂ oa] := by
  induction oa using OracleComp.inductionOn with
  | pure value => simp
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
        evalDist_bind, evalDist_bind, h input]
      exact congrArg _ (funext ih)

theorem evalDist_fixedRom_eq_fixedHashWorld (f : HashInput → HashOutput) {α : Type}
    (oa : OracleComp OracleWorld α) :
    𝒟[simulateQ (fixedRom f) oa] = 𝒟[simulateQ (Prefix.fixedHashWorld f) oa] := by
  refine evalDist_simulateQ_congr _ _ (fun input => ?_) oa
  cases input with
  | inl draw =>
      change 𝒟[(liftM (unifSpec.query draw) : ProbComp _)] = 𝒟[PMF.uniformOfFintype (Fin (draw + 1))]
      rw [evalDist_query]
  | inr bytes => simp [fixedRom, Prefix.fixedHashWorld]

noncomputable local instance : SampleableType CanonicalGraphLabels := graphLabelsSampleable

variable [Params]

/-- Canonical labels completed from independent answers and the boundary surrogates. -/
noncomputable def labelsOf (material : Material) (answers : CanonicalGraphLabels) : CanonicalGraphLabels :=
  completedLabels (graphOrder (PrunedGraph.active (parameter material)))
    (PrunedGraph.initialLabels (parameter material) (GraphCorrectness.materialSurrogates material)) answers

/-- The prepared cache: seed material, then every active canonical graph response. -/
noncomputable def preparedCache (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) : QueryCache HashSpec :=
  programGraphCache (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) (graphOrder (PrunedGraph.active (parameter material)))
    (labelsOf material answers) (programCache ∅ seed material)

theorem OnlyW.gameAfterSeed_internalize (adversary : Adversary) (seed : MasterSeed) :
    OnlyW (gameAfterSeed (internalize adversary) seed) := by
  rw [gameAfterSeed_eq]
  refine OnlyW.bind (OnlyW.liftHash (Short.Seeded.Only.keygenFromSeed seed)) (fun keys => ?_)
  refine OnlyW.bind ?_ (fun output => OnlyW.verifyPart _ _)
  exact OnlyW.gameImpl keys.2 _ (OnlyAdv.map _ (OnlyAdv.internal _ _))

/-- The internalized experiment as an average of fixed-function counted games. -/
theorem evalDist_experiment_fixed (adversary : Adversary) :
    𝒟[experiment (internalize adversary)] = 𝒟[do
      let material ← sampleMaterial
      let seed ← sampleMasterSeed
      let answers ← $ᵗ CanonicalGraphLabels
      let table ← $ᵗ Eager.Table
      simulateQ (fixedRom (extend (preparedCache material seed answers) table))
        (countHashQueries (gameAfterSeed (internalize adversary) seed))] := by
  rw [evalDist_experiment_prepared]
  unfold preparedExperiment
  refine evalDist_bind_congr' _ (fun material => evalDist_bind_congr' _ (fun seed => ?_))
  rw [← simulateQ_countHashQueries]
  change 𝒟[(simulateQ romImpl (countHashQueries (gameAfterSeed (internalize adversary) seed))).run'
    (programCache ∅ seed material)] = _
  rw [evalDist_graph_continuation (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) _ (PrunedGraph.active (parameter material))
    (PrunedGraph.initialLabels (parameter material) (GraphCorrectness.materialSurrogates material))
    _ (material_freshStructural (parameter material) seed material)]
  refine evalDist_bind_congr' _ (fun answers => ?_)
  exact evalDist_romImpl_eq_table _
    (OnlyW.counted _ _ (OnlyW.gameAfterSeed_internalize adversary seed)) _

/-! ### Every sample is a consistent fixed answer function -/

omit [Params] in
theorem extend_cached {cache : QueryCache HashSpec} {table : Eager.Table} {input : HashInput}
    {answer : HashOutput} (h : cache input = some answer) : extend cache table input = answer := by
  simp [extend, h]

theorem preparedCache_other (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (input : HashInput) (hmiss : ∀ position, input ≠ canonicalGraphInput (parameter material)
      (GraphCorrectness.materialOts material) (GraphCorrectness.materialFts material) position
      (labelsOf material answers)) :
    preparedCache material seed answers input = programCache ∅ seed material input :=
  HiddenGraph.programGraphCache_preserves_other _ _ _ _ _ _ _ (fun position _ => hmiss position)

theorem preparedCache_parameter (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels) :
    preparedCache material seed answers (parameterInput seed) = some material.1 := by
  rw [preparedCache_other material seed answers (parameterInput seed)
    (fun position => keygenInput_ne_hashInput _ _ _ _ _ _), programCache_parameter]

theorem preparedCache_secret (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (position : SecretPosition) :
    preparedCache material seed answers (secretInput seed material position) = some (material.2 position) := by
  rw [preparedCache_other material seed answers (secretInput seed material position)
    (fun other => keygenInput_ne_hashInput _ _ _ _ _ _), programCache_secret]

theorem preparedCache_label (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (position : Position) (hactive : PrunedGraph.active (parameter material) position) :
    preparedCache material seed answers (canonicalGraphInput (parameter material)
      (GraphCorrectness.materialOts material) (GraphCorrectness.materialFts material) position
      (labelsOf material answers)) = some (labelsOf material answers position) :=
  HiddenGraph.programGraphCache_label _ _ _ _ _ _ _ ((mem_graphOrder _ _).2 hactive)

/-- The answer function of one sample. -/
noncomputable def sampleFn (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) : QueryImpl HashSpec Id :=
  fun input => extend (preparedCache material seed answers) table input

theorem sample_agreement (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) : PreparedAgreement (sampleFn material seed answers table) seed material :=
  ⟨extend_cached (preparedCache_parameter material seed answers),
    fun position => extend_cached (preparedCache_secret material seed answers position)⟩

theorem sample_consistent (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    GraphCorrectness.Consistent (sampleFn material seed answers table) (parameter material) seed
      (labelsOf material answers) := by
  intro position hactive
  rw [← GraphCorrectness.materialOts_eq _ seed material (sample_agreement material seed answers table),
    ← GraphCorrectness.materialFts_eq _ seed material (sample_agreement material seed answers table)]
  exact (extend_cached (preparedCache_label material seed answers position hactive)).symm

theorem sample_boundary (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    GraphCorrectness.BoundaryCorrect (sampleFn material seed answers table) (parameter material) seed
      (labelsOf material answers) := by
  intro position value hboundary
  rw [← GraphCorrectness.materialSurrogates_eq _ seed material
    (sample_agreement material seed answers table)] at hboundary
  have hinactive := PrunedGraph.boundary_inactive _ _ position value hboundary
  have hnot : position ∉ graphOrder (PrunedGraph.active (parameter material)) :=
    fun hmem => hinactive ((mem_graphOrder _ _).1 hmem)
  simp only [labelsOf, completedLabels, hnot, ↓reduceIte]
  exact PrunedGraph.initialLabels_boundary _ _ position value hboundary

theorem sample_parameter (material : Material) (seed : MasterSeed) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    evalWithAnswerFn (sampleFn material seed answers table)
      (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter material := by
  simp only [deriveKey, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change truncateHash (sampleFn material seed answers table (parameterInput seed)) = _
  rw [show sampleFn material seed answers table (parameterInput seed) = material.1 from
    extend_cached (preparedCache_parameter material seed answers)]
  rfl

/-- Coordinates of one sample, read from its answer function. -/
noncomputable def sampleCoordinates (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) : HiddenGraph.Table :=
  HiddenGraph.coordinates
    (GraphCorrectness.otsSecrets (sampleFn material seed answers table) (parameter material) seed)
    (GraphCorrectness.ftsSecrets (sampleFn material seed answers table) (parameter material) seed)
    (labelsOf material answers)

theorem fixedHashWorld_countHashQueries (f : QueryImpl HashSpec Id) {α : Type}
    (oa : OracleComp OracleWorld α) :
    simulateQ (Prefix.fixedHashWorld f) (countHashQueries oa) =
      (simulateQ (Prefix.fixedWorldCost f) oa).run := by
  rw [countHashQueries, SphincsSecurity.QueryCap.simulate_withCost]
  congr 2
  funext input
  cases input <;> rfl

/-- Every sample of the internalized game equals the graph-view game for that sample. -/
theorem sample_costGame (adversary : Adversary) (material : Material) (seed : MasterSeed)
    (answers : CanonicalGraphLabels) (table : Eager.Table) :
    𝒟[simulateQ (fixedRom (extend (preparedCache material seed answers) table))
        (countHashQueries (gameAfterSeed (internalize adversary) seed))] =
      𝒟[(simulateQ (GraphView.fixedCostSource (sampleFn material seed answers table)
        (sampleCoordinates material seed answers table))
        (GraphView.costGame (parameter material) (GraphView.publicData (labelsOf material answers))
          (internalize adversary))).run] := by
  rw [show (extend (preparedCache material seed answers) table) =
      sampleFn material seed answers table from rfl,
    evalDist_fixedRom_eq_fixedHashWorld, fixedHashWorld_countHashQueries,
    GraphView.costGame_correct (sampleFn material seed answers table) (parameter material) seed
      (GraphView.publicData (labelsOf material answers)) (sampleCoordinates material seed answers table)
      (GraphView.publicData_correct _ _ _ _ (sample_consistent material seed answers table)
        (sample_boundary material seed answers table))
      (GraphView.coordinates_correct _ _ _ _ (sample_consistent material seed answers table))
      (sample_parameter material seed answers table)]

end LeanSphincs.Security.Assembly
