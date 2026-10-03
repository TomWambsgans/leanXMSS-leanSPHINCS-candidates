import LeanSphincs.LifetimeForecast

/-! Exact target-bank accounting for adaptive queries to either message-digest block.
This stage handles the real lazy hash oracle and arbitrary cached-prefix selection. The digest
weight is fixed here; adapting the honest signing/disclosure transition is a separate step. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

noncomputable def uniformDigestForecast (weight : MessageDigest → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' digest, Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] * weight digest

noncomputable def digestBankValue (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ candidate ∈ bank, digestForecast sk candidate cache weight

/-- Every candidate with a queried block is recorded. This tracks partial candidates too. -/
def DigestQueriesRecorded (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ candidate, candidate ∉ bank → ∀ call, cache (candidateInput sk candidate call) = none

theorem expected_digestBankValue_query (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
      digestBankValue sk bank result.2 weight) = digestBankValue sk bank cache weight := by
  simp only [digestBankValue, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro candidate _
  exact expected_digestForecast_query sk candidate cache weight input

theorem query_other_cache_eq (input other : HashInput) (hne : other ≠ input)
    (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle (spec := HashSpec) input).run cache)) :
    result.2 other = cache other := by
  cases hc : cache input with
  | some answer =>
    rw [cached_run _ _ _ hc, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    rfl
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hresult
    obtain ⟨answer, _, rfl⟩ := hresult
    exact QueryCache.cacheQuery_of_ne cache answer hne

abbrev DigestBankState := Finset DigestCandidate × QueryCache HashSpec

noncomputable def digestBankStep (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (state : DigestBankState) : ProbComp DigestBankState :=
  (fun result => (insert candidate state.1, result.2)) <$>
    (randomOracle (spec := HashSpec) (candidateInput sk candidate call)).run state.2

theorem digestBankStep_preserves (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (state : DigestBankState) (hrecorded : DigestQueriesRecorded sk state.1 state.2)
    (result : DigestBankState) (hresult : result ∈ support (digestBankStep sk candidate call state)) :
    DigestQueriesRecorded sk result.1 result.2 := by
  rw [digestBankStep, support_map] at hresult
  obtain ⟨answer, hanswer, rfl⟩ := hresult
  intro other hother i
  have hne : other ≠ candidate := fun h => hother (h.symm ▸ Finset.mem_insert_self _ _)
  have hnot : other ∉ state.1 := fun h => hother (Finset.mem_insert_of_mem h)
  have hinput : candidateInput sk other i ≠ candidateInput sk candidate call :=
    fun h => hne (candidateInput_candidate_injective sk i call h)
  exact (query_other_cache_eq _ _ hinput state.2 answer hanswer).trans
    (hrecorded other hnot i)

/-- Only the first query to a new pair creates bank value. Completing an adaptively selected
cached prefix consumes a query but has zero expected increment in its existing forecast. -/
theorem expected_digestBankStep (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (state : DigestBankState) (hrecorded : DigestQueriesRecorded sk state.1 state.2)
    (weight : MessageDigest → ℝ≥0∞) :
    (∑' result, Pr[= result | digestBankStep sk candidate call state] *
      digestBankValue sk result.1 result.2 weight) =
      digestBankValue sk state.1 state.2 weight +
        if candidate ∈ state.1 then 0 else uniformDigestForecast weight := by
  rw [digestBankStep, tsum_probOutput_map_mul, expected_digestBankValue_query]
  by_cases hmem : candidate ∈ state.1
  · simp only [Finset.insert_eq_of_mem hmem, hmem, if_true, add_zero]
  · simp only [digestBankValue, Finset.sum_insert hmem, hmem, if_false]
    rw [fresh_digestForecast_uniform sk candidate state.2 weight (hrecorded candidate hmem)]
    exact add_comm _ _

theorem expected_digestBankStep_le (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (state : DigestBankState) (hrecorded : DigestQueriesRecorded sk state.1 state.2)
    (weight : MessageDigest → ℝ≥0∞) :
    (∑' result, Pr[= result | digestBankStep sk candidate call state] *
      digestBankValue sk result.1 result.2 weight) ≤
      digestBankValue sk state.1 state.2 weight + uniformDigestForecast weight := by
  rw [expected_digestBankStep sk candidate call state hrecorded weight]
  split_ifs
  · exact add_le_add le_rfl bot_le
  · exact le_rfl

noncomputable def adaptiveDigestBank {State : Type} (sk : Seeded.SecretKey)
    (choose : State → DigestBankState → ProbComp (DigestCandidate × Fin 2 × State)) :
    Nat → State → DigestBankState → ProbComp DigestBankState
  | 0, _, state => pure state
  | q + 1, privateState, state => do
      let choice ← choose privateState state
      let next ← digestBankStep sk choice.1 choice.2.1 state
      adaptiveDigestBank sk choose q choice.2.2 next

theorem expected_adaptiveDigestBank_le {State : Type} (sk : Seeded.SecretKey)
    (choose : State → DigestBankState → ProbComp (DigestCandidate × Fin 2 × State))
    (weight : MessageDigest → ℝ≥0∞) :
    ∀ q privateState state, DigestQueriesRecorded sk state.1 state.2 →
      (∑' result, Pr[= result | adaptiveDigestBank sk choose q privateState state] *
        digestBankValue sk result.1 result.2 weight) ≤
        digestBankValue sk state.1 state.2 weight + q * uniformDigestForecast weight := by
  intro q
  induction q with
  | zero =>
    intro privateState state _
    simp only [adaptiveDigestBank, tsum_probOutput_pure_mul, Nat.cast_zero, zero_mul, add_zero, le_rfl]
  | succ q ih =>
    intro privateState state hrecorded
    rw [adaptiveDigestBank, tsum_probOutput_bind_mul]
    have hstep (choice : DigestCandidate × Fin 2 × State) :
        (∑' result, Pr[= result | (digestBankStep sk choice.1 choice.2.1 state >>= fun next =>
          adaptiveDigestBank sk choose q choice.2.2 next)] * digestBankValue sk result.1 result.2 weight) ≤
        digestBankValue sk state.1 state.2 weight + (q + 1) * uniformDigestForecast weight := by
      rw [tsum_probOutput_bind_mul]
      calc
        _ ≤ ∑' next, Pr[= next | digestBankStep sk choice.1 choice.2.1 state] *
            (digestBankValue sk next.1 next.2 weight + q * uniformDigestForecast weight) := by
          apply ENNReal.tsum_le_tsum
          intro next
          by_cases hnext : next ∈ support (digestBankStep sk choice.1 choice.2.1 state)
          · exact mul_le_mul' le_rfl (ih choice.2.2 next
              (digestBankStep_preserves sk choice.1 choice.2.1 state hrecorded next hnext))
          · rw [probOutput_eq_zero_of_not_mem_support hnext, zero_mul, zero_mul]
        _ = (∑' next, Pr[= next | digestBankStep sk choice.1 choice.2.1 state] *
            digestBankValue sk next.1 next.2 weight) +
            (∑' next, Pr[= next | digestBankStep sk choice.1 choice.2.1 state]) *
              (q * uniformDigestForecast weight) := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ ≤ (digestBankValue sk state.1 state.2 weight + uniformDigestForecast weight) +
            q * uniformDigestForecast weight :=
          add_le_add (expected_digestBankStep_le sk choice.1 choice.2.1 state hrecorded weight)
            (mul_le_of_le_one_left' tsum_probOutput_le_one)
        _ = _ := by ring
    calc
      _ ≤ ∑' choice, Pr[= choice | choose privateState state] *
          (digestBankValue sk state.1 state.2 weight + (q + 1) * uniformDigestForecast weight) :=
        ENNReal.tsum_le_tsum fun choice => mul_le_mul' le_rfl (hstep choice)
      _ ≤ digestBankValue sk state.1 state.2 weight + (q + 1) * uniformDigestForecast weight := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one
      _ = _ := by rw [Nat.cast_add, Nat.cast_one]

end LeanSphincs.Lifetime
