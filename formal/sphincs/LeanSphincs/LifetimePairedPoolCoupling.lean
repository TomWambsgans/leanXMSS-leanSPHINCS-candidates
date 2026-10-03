import LeanSphincs.LifetimePairedReification
import LeanSphincs.SecurityGameSupport

/-! A joint law for the actual adaptive paired transcript and the complete first-block table.
Both localization events can therefore be combined in one probability space. -/

namespace LeanSphincs.Lifetime.PairedReification
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType FirstPoolTable := firstPoolTableSampleableType

private theorem run_sequenceFin_known {n : Nat} (inputs : Fin n → HashInput)
    (outputs : Fin n → HashOutput) (cache : QueryCache HashSpec)
    (hknown : ∀ i, cache (inputs i) = some (outputs i)) :
    (simulateQ randomOracle (sequenceFin fun i =>
      (liftM (HashSpec.query (inputs i)) : OracleComp HashSpec HashOutput))).run cache =
      pure (outputs, cache) := by
  induction n with
  | zero =>
      simp only [sequenceFin, simulateQ_pure, StateT.run_pure]
      congr 1
      apply Prod.ext
      · funext i; exact i.elim0
      · rfl
  | succ n ih =>
      simp only [sequenceFin, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [QueryImpl.withCaching_run_some _ (hknown 0), pure_bind,
        ih (fun i => inputs i.succ) (fun i => outputs i.succ) (fun i => hknown i.succ), pure_bind]
      simp only [simulateQ_pure, StateT.run_pure]
      congr 1
      apply Prod.ext
      · funext i; cases i using Fin.cases <;> rfl
      · rfl

theorem run_queryTable_known {J : Type} [Fintype J] (inputs : J → HashInput)
    (outputs : J → HashOutput) (cache : QueryCache HashSpec)
    (hknown : ∀ j, cache (inputs j) = some (outputs j)) :
    (simulateQ randomOracle (queryTable inputs)).run cache = pure (outputs, cache) := by
  rw [queryTable, simulateQ_map, StateT.run_map,
    run_sequenceFin_known _ (fun i => outputs ((Fintype.equivFin J).symm i)) cache (fun _ => hknown _), map_pure]
  congr 1
  apply Prod.ext
  · funext j
    simp only [finTableEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
  · rfl

/-- The final table read is part of the output, never an independently coupled marginal. -/
noncomputable def poolJointProgram {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α) :
    OracleComp OracleWorld ((α × List QueryRecord × QueryCache HashSpec) × FirstPoolTable) := do
  let trace ← traceProgram sk program ∅
  let table ← (liftM (queryTable firstPoolInput) : OracleComp OracleWorld FirstPoolTable)
  pure (trace, table)

noncomputable def poolJointRun {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α) :
    ProbComp ((α × List QueryRecord × QueryCache HashSpec) × FirstPoolTable) :=
  (simulateQ romImpl (poolJointProgram sk program)).run' ∅

noncomputable def preparedPoolJointRun {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α) :
    ProbComp ((α × List QueryRecord × QueryCache HashSpec) × FirstPoolTable) := do
  let table ← $ᵗ FirstPoolTable
  let trace ← (simulateQ romImpl (traceProgram sk program ∅)).run' (firstPoolCache table)
  pure (trace, table)

theorem run'_poolJointProgram_prepared {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (table : FirstPoolTable) :
    (simulateQ romImpl (poolJointProgram sk program)).run' (firstPoolCache table) =
      (fun trace => (trace, table)) <$>
        (simulateQ romImpl (traceProgram sk program ∅)).run' (firstPoolCache table) := by
  simp only [poolJointProgram, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    map_bind, simulateQ_pure, StateT.run_pure, map_pure, Functor.map_map]
  apply bind_congr_of_forall_mem_support
  intro result hresult
  rw [simulate_lift_hash, run_queryTable_known firstPoolInput table result.2
    (fun position => world_support_cache_le _ _ _ _ hresult (firstPoolCache_apply table position)), pure_bind]
  rfl

/-- Exact joint lazy-to-prepared law. Source first-touch flags still use the separate local cache. -/
theorem evalDist_poolJointRun {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α) :
    𝒟[poolJointRun sk program] = 𝒟[preparedPoolJointRun sk program] := by
  rw [poolJointRun, evalDist_firstPool_continuation]
  simp_rw [run'_poolJointProgram_prepared]
  rfl

/-- Appending a table read preserves the paired transcript marginal. -/
theorem probEvent_poolJointRun_trace {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (event : (α × List QueryRecord × QueryCache HashSpec) → Prop) :
    Pr[fun result => event result.1 | poolJointRun sk program] =
      Pr[event | traceRun (pairedRom sk) program ∅] := by
  classical
  simp only [poolJointRun, poolJointProgram, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    map_bind, simulateQ_pure, StateT.run_pure, map_pure, run_traceProgram_same, bind_map_left,
    probEvent_bind_eq_tsum]
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  simp only [probEvent_pure, ← ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  split_ifs <;> simp only [mul_one, mul_zero, tsum_probOutput_of_liftM_PMF, tsum_zero]

/-- The same joint execution's table has the original uniform law. -/
theorem probEvent_poolJointRun_table {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (event : FirstPoolTable → Prop) :
    Pr[fun result => event result.2 | poolJointRun sk program] = Pr[event | ($ᵗ FirstPoolTable)] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_poolJointRun sk program)]
  classical
  simp only [preparedPoolJointRun, probEvent_bind_eq_tsum]
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro table
  simp only [probEvent_bind_eq_tsum, probEvent_pure, ← ENNReal.tsum_mul_right,
    tsum_probOutput_of_liftM_PMF, one_mul]
  split_ifs <;> simp only [mul_one, mul_zero, tsum_probOutput_of_liftM_PMF, tsum_zero]

variable [Params]

/-- Pool balance and rectangle sparsity hold jointly for the actual transcript, with the
sum of the two explicitly proved exceptional probabilities. -/
theorem probEvent_poolJointRun_bad {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' ∅), result.2 ≤ q) :
    Pr[fun result => ¬AllPoolsBalanced (firstPoolIndexes result.2) ∨
      ¬RectangleBankSparse sk.parameter (traceCandidateBank sk result.1.2.1)
        (fun candidate => cachedPairDigest sk candidate result.1.2.2) |
      poolJointRun sk program] ≤ (1 : ℝ≥0∞) / 2 ^ 400 + 1 / 2 ^ 400 := by
  classical
  calc
    _ ≤ Pr[fun result => ¬AllPoolsBalanced (firstPoolIndexes result.2) | poolJointRun sk program] +
        Pr[fun result => ¬RectangleBankSparse sk.parameter (traceCandidateBank sk result.1.2.1)
          (fun candidate => cachedPairDigest sk candidate result.1.2.2) | poolJointRun sk program] := by
      exact probEvent_or_le _ _ _
    _ ≤ _ := by
      rw [probEvent_poolJointRun_table sk program (fun table => ¬AllPoolsBalanced (firstPoolIndexes table)),
        probEvent_poolJointRun_trace sk program (fun trace => ¬RectangleBankSparse sk.parameter
          (traceCandidateBank sk trace.2.1) (fun candidate => cachedPairDigest sk candidate trace.2.2))]
      exact add_le_add probEvent_firstPool_unbalanced
        (probEvent_traceCandidateBank_not_sparse sk program ∅ (PairedCache.empty sk) q hq hbound)

end LeanSphincs.Lifetime.PairedReification
