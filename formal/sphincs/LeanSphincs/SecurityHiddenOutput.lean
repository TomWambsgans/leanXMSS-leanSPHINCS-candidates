import LeanSphincs.SecurityHiddenOutsideProgram
import LeanSphincs.SecurityCacheMatch

/-! Local fresh-output charging for the explicit outside ROM. Query weights are indexed by
raw input, so seed, message, and structural domains need not each consume the full budget. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenOutside
open HiddenCost
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

/-- Private draws are free; each raw hash address has its own monitor weight. -/
def outputCost (weight : HashInput → Nat) : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr input => weight input

def instrument {I α : Type} {spec : OracleSpec I} (cost : I → Nat)
    (computation : OracleComp spec α) : OracleComp spec (α × Nat) :=
  OracleComp.construct (fun value => pure (value, 0))
    (fun input _ next => liftM (spec.query input) >>= fun value =>
      (fun result => (result.1, cost input + result.2)) <$> next value) computation

theorem instrument_pure {I α : Type} {spec : OracleSpec I} (cost : I → Nat) (value : α) :
    instrument cost (pure value : OracleComp spec α) = pure (value, 0) := rfl

theorem instrument_query_bind {I α : Type} {spec : OracleSpec I} (cost : I → Nat)
    (input : I) (next : spec.Range input → OracleComp spec α) :
    instrument cost (liftM (spec.query input) >>= next) = liftM (spec.query input) >>= fun value =>
      (fun result => (result.1, cost input + result.2)) <$> instrument cost (next value) := rfl

theorem instrument_pays_support {I α : Type} {spec : OracleSpec I} (cost : I → Nat)
    (computation : OracleComp spec α) (credit : α → Nat) (spent : Nat)
    (h : Pays cost computation credit spent) (result : α × Nat)
    (hresult : result ∈ support (instrument cost computation)) : spent + result.2 ≤ credit result.1 := by
  induction computation using OracleComp.inductionOn generalizing spent result with
  | pure value =>
      rw [instrument_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact h
  | query_bind input next ih =>
      rw [pays_query_bind] at h
      rw [instrument_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨value, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      have ht := ih value _ (h value) tail htail
      dsimp only
      omega

theorem runRaw_query_bind {D R α : Type} [SampleableType R]
    (input : (RawWorld D R).Domain) (next : (RawWorld D R).Range input → OracleComp (RawWorld D R) α)
    (cache : Cache D R) :
    runRaw (liftM ((RawWorld D R).query input) >>= next) cache =
      (rawImpl input).run cache >>= fun first => runRaw (next first.1) first.2 := by
  simp only [runRaw, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem runRaw_support {D R α : Type} [SampleableType R]
    (computation : OracleComp (RawWorld D R) α) (cache : Cache D R) (result : α × Cache D R)
    (hresult : result ∈ support (runRaw computation cache)) : result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      rw [runRaw_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp
  | query_bind input next ih =>
      rw [runRaw_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨first, _, htail⟩ := hresult
      exact (mem_support_bind_iff _ _ _).mpr ⟨first.1, mem_support_query _ _, ih first.1 first.2 htail⟩

noncomputable def weightedRun {α : Type} (weight : HashInput → Nat)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    ProbComp ((α × Nat) × QueryCache HashSpec) :=
  runRaw (instrument (outputCost weight) computation) cache

theorem weightedRun_pure {α : Type} (weight : HashInput → Nat) (value : α) (cache : QueryCache HashSpec) :
    weightedRun weight (pure value) cache = pure ((value, 0), cache) := rfl

theorem weightedRun_query_bind {α : Type} (weight : HashInput → Nat) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    weightedRun weight (liftM (OracleWorld.query input) >>= next) cache =
      (rawImpl input).run cache >>= fun first =>
        (fun last => ((last.1.1, outputCost weight input + last.1.2), last.2)) <$>
          weightedRun weight (next first.1) first.2 := by
  rw [weightedRun, instrument_query_bind, runRaw_query_bind]
  congr 1
  funext first
  rw [runRaw_map]
  rfl

theorem weightedRun_value {α : Type} (weight : HashInput → Nat)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$> weightedRun weight computation cache =
      runRaw computation cache := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => rfl
  | query_bind input next ih =>
      rw [weightedRun_query_bind, runRaw_query_bind, map_bind]
      congr 1
      funext first
      simpa only [Functor.map_map, Function.comp_def] using ih first.1 first.2

noncomputable def expectedOutputCost {α : Type} (weight : HashInput → Nat)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∑' result, Pr[= result | weightedRun weight computation cache] * (result.1.2 : ℝ≥0∞)

theorem expectedOutputCost_pure {α : Type} (weight : HashInput → Nat) (value : α) (cache : QueryCache HashSpec) :
    expectedOutputCost weight (pure value) cache = 0 := by simp [expectedOutputCost, weightedRun_pure]

theorem expectedOutputCost_query_bind {α : Type} (weight : HashInput → Nat) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedOutputCost weight (liftM (OracleWorld.query input) >>= next) cache = outputCost weight input +
      ∑' first, Pr[= first | (rawImpl input).run cache] * expectedOutputCost weight (next first.1) first.2 := by
  rw [expectedOutputCost, weightedRun_query_bind, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, Nat.cast_add, mul_add, ENNReal.tsum_add,
    ENNReal.tsum_mul_right]
  have hmass {β : Type} (process : ProbComp β) : (∑' result, Pr[= result | process]) = 1 :=
    tsum_probOutput_eq_one' probFailure_eq_zero
  simp only [hmass, one_mul, expectedOutputCost, ENNReal.tsum_mul_right]

theorem expectedOutputCost_le_credit {α : Type} (weight : HashInput → Nat)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (credit : α → Nat) (h : Pays (outputCost weight) computation credit 0) :
    expectedOutputCost weight computation cache ≤
      ∑' result, Pr[= result | runRaw computation cache] * (credit result.1 : ℝ≥0∞) := by
  rw [← weightedRun_value weight computation cache, tsum_probOutput_map_mul]
  unfold expectedOutputCost
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (weightedRun weight computation cache)
  · have hs := runRaw_support (instrument (outputCost weight) computation) cache result hr
    have hb := instrument_pays_support (outputCost weight) computation credit 0 h result.1 hs
    simp only [Nat.zero_add] at hb
    dsimp only
    exact mul_le_mul' le_rfl (by exact_mod_cast hb)
  · rw [probOutput_eq_zero_of_not_mem_support hr]
    simp

/-- Only the target-set cardinality at the actual queried input is charged. -/
theorem local_output_query_bound (targets : HashInput → Finset Digest) (weight : HashInput → Nat)
    (hcard : ∀ input, (targets input).card ≤ weight input) (input : HashInput) (cache : QueryCache HashSpec) :
    Pr[fun result => CacheMatch.Bad targets result.2 | (randomOracle (spec := HashSpec) input).run cache] ≤
      CacheMatch.potential targets cache + (weight input : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  by_cases hbad : CacheMatch.Bad targets cache
  · exact probEvent_le_one.trans (by simp [CacheMatch.potential, hbad])
  · rw [CacheMatch.potential, if_neg hbad, zero_add]
    cases hcache : cache input with
    | some answer =>
        rw [QueryImpl.withCaching_run_some _ hcache]
        simp only [probEvent_pure, hbad, if_false]
        exact zero_le
    | none =>
        rw [QueryImpl.withCaching_run_none _ hcache, probEvent_map]
        have hevent :
            Pr[fun answer : HashOutput => CacheMatch.Bad targets (cache.cacheQuery input answer) |
              ($ᵗ HashOutput : ProbComp _)] =
            Pr[fun answer : HashOutput => truncateHash answer ∈ targets input |
              ($ᵗ HashOutput : ProbComp _)] :=
          probEvent_ext (fun answer _ => by simp only [CacheMatch.bad_cacheQuery_iff _ _ _ _ hcache, hbad, false_or])
        change Pr[fun answer : HashOutput => CacheMatch.Bad targets (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp _)] ≤ _
        rw [hevent, probEvent_uniform_truncateHash_mem]
        rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
        exact ENNReal.div_le_div_right (by exact_mod_cast hcard input) _

theorem local_output_step_bound (targets : HashInput → Finset Digest) (weight : HashInput → Nat)
    (hcard : ∀ input, (targets input).card ≤ weight input) (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (rawImpl input).run cache] * CacheMatch.potential targets result.2) ≤
      CacheMatch.potential targets cache + (outputCost weight input : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  rw [CacheMatch.expected_potential_eq_event]
  cases input with
  | inl draw =>
      change Pr[fun result => CacheMatch.Bad targets result.2 | ((unifFwdImpl HashSpec) draw).run cache] ≤ _
      have heq := unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec) (liftM (unifSpec.query draw) : ProbComp _) cache
      simp only [simulateQ_spec_query] at heq
      rw [heq]
      rw [probEvent_map]
      change Pr[fun _ => CacheMatch.Bad targets cache | (liftM (unifSpec.query draw) : ProbComp _)] ≤ _
      rw [probEvent_const]
      simp only [probFailure_eq_zero, tsub_zero, outputCost, Nat.cast_zero, ENNReal.zero_div, add_zero]
      by_cases hb : CacheMatch.Bad targets cache <;> simp [CacheMatch.potential, hb]
  | inr bytes =>
      have heq : (rawImpl (.inr bytes)).run cache = (randomOracle (spec := HashSpec) bytes).run cache := by
        exact congrArg
          (fun dec => (@randomOracle HashInput dec HashSpec (fun _ => inferInstance) bytes).run cache)
          (Subsingleton.elim _ _)
      rw [heq]
      exact local_output_query_bound targets weight hcard bytes cache

/-- The fixed-target outside-cache event is charged by its actual local domain count. -/
theorem weighted_output_bound {α : Type} (targets : HashInput → Finset Digest) (weight : HashInput → Nat)
    (hcard : ∀ input, (targets input).card ≤ weight input)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    Pr[fun result => CacheMatch.Bad targets result.2 | runRaw computation cache] ≤
      CacheMatch.potential targets cache + expectedOutputCost weight computation cache / (2 : ℝ≥0∞) ^ 128 := by
  rw [← CacheMatch.expected_potential_eq_event]
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [runRaw_pure, expectedOutputCost_pure]
  | query_bind input next ih =>
      rw [runRaw_query_bind, tsum_probOutput_bind_mul, expectedOutputCost_query_bind]
      calc
        _ ≤ ∑' first, Pr[= first | (rawImpl input).run cache] *
            (CacheMatch.potential targets first.2 + expectedOutputCost weight (next first.1) first.2 / (2 : ℝ≥0∞) ^ 128) :=
          ENNReal.tsum_le_tsum fun first => mul_le_mul' le_rfl (ih first.1 first.2)
        _ = (∑' first, Pr[= first | (rawImpl input).run cache] * CacheMatch.potential targets first.2) +
            (∑' first, Pr[= first | (rawImpl input).run cache] * expectedOutputCost weight (next first.1) first.2) /
              (2 : ℝ≥0∞) ^ 128 := by
          simp only [mul_add, ENNReal.tsum_add, div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right]
        _ ≤ _ := by
          rw [ENNReal.add_div, ← add_assoc]
          exact add_le_add (local_output_step_bound targets weight hcard input cache) le_rfl

/-- A terminal credit proved from the real raw program can be substituted for its query count.
This is the interface used to charge output matches to the original common source trace. -/
theorem output_bound_credit {α : Type} (targets : HashInput → Finset Digest) (weight : HashInput → Nat)
    (hcard : ∀ input, (targets input).card ≤ weight input)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hclean : ¬CacheMatch.Bad targets cache) (credit : α → Nat)
    (hpaid : Pays (outputCost weight) computation credit 0) :
    Pr[fun result => CacheMatch.Bad targets result.2 | runRaw computation cache] ≤
      (∑' result, Pr[= result | runRaw computation cache] * (credit result.1 : ℝ≥0∞)) / (2 : ℝ≥0∞) ^ 128 := by
  have h := weighted_output_bound targets weight hcard computation cache
  rw [CacheMatch.potential, if_neg hclean, zero_add] at h
  exact h.trans (ENNReal.div_le_div_right (expectedOutputCost_le_credit weight computation cache credit hpaid) _)

end LeanSphincs.Security.HiddenOutside
