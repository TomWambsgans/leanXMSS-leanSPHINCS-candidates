import LeanSphincs.LifetimeSecondBank

/-! Source-conditioned second-moment forecasts. The source is excluded from its own target
bank. Queries to either source block or any target block preserve the joint forecast exactly;
conditioning the source to be fresh or independent of the adversary's query transcript is
unnecessary. Disclosure updates that change the kernel are not part of this query lemma. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

attribute [local instance] Classical.propDecidable

theorem secondBankValue_congr_cache (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (before after : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞)
    (hcache : ∀ candidate ∈ bank, ∀ call,
      after (candidateInput sk candidate call) = before (candidateInput sk candidate call)) :
    secondBankValue sk bank after weight = secondBankValue sk bank before weight := by
  apply Finset.sum_congr rfl
  intro left hleft
  apply Finset.sum_congr rfl
  intro right hright
  simp only [targetSecondForecast, pairForecast_product,
    digestForecast_congr_cache sk left before after _ (hcache left hleft),
    digestForecast_congr_cache sk right before after _ (hcache right hright)]

noncomputable def jointSecondBankValue (sk : Seeded.SecretKey) (source : DigestCandidate)
    (bank : Finset DigestCandidate) (cache : QueryCache HashSpec)
    (weight : MessageDigest → MessageDigest → ℝ≥0∞) : ℝ≥0∞ :=
  digestForecast sk source cache (fun sourceDigest => secondBankValue sk bank cache (weight sourceDigest))

/-- This includes a source-first query that reveals the retained index and 23 selectors,
a source-second query that reveals the final selector, and all target/query cache orders. -/
theorem expected_jointSecondBankValue_query (sk : Seeded.SecretKey) (source : DigestCandidate)
    (bank : Finset DigestCandidate) (hsource : source ∉ bank) (cache : QueryCache HashSpec)
    (weight : MessageDigest → MessageDigest → ℝ≥0∞) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
      jointSecondBankValue sk source bank result.2 weight) =
        jointSecondBankValue sk source bank cache weight := by
  by_cases hinput : ∃ call, candidateInput sk source call = input
  · obtain ⟨call, rfl⟩ := hinput
    have hbank (result : HashOutput × QueryCache HashSpec)
        (hresult : result ∈ support ((randomOracle (spec := HashSpec) (candidateInput sk source call)).run cache))
        (digest : MessageDigest) : secondBankValue sk bank result.2 (weight digest) =
          secondBankValue sk bank cache (weight digest) := by
      apply secondBankValue_congr_cache
      intro target htarget i
      apply query_other_cache_eq _ _ _ cache result hresult
      intro heq
      have heq' := candidateInput_candidate_injective sk i call heq
      exact hsource (heq' ▸ htarget)
    calc
      _ = ∑' result, Pr[= result | (randomOracle (spec := HashSpec) (candidateInput sk source call)).run cache] *
          digestForecast sk source result.2 (fun digest => secondBankValue sk bank cache (weight digest)) := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support ((randomOracle (spec := HashSpec) (candidateInput sk source call)).run cache)
        · congr 1
          unfold jointSecondBankValue
          congr 1
          exact funext (hbank result hresult)
        · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      _ = _ := expected_digestForecast_query sk source cache _ _
  · have hne : ∀ call, candidateInput sk source call ≠ input := by
      intro call heq
      exact hinput ⟨call, heq⟩
    calc
      _ = ∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
          digestForecast sk source cache (fun digest => secondBankValue sk bank result.2 (weight digest)) := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support ((randomOracle (spec := HashSpec) input).run cache)
        · congr 1
          exact digestForecast_query_other sk source cache _ input hne result hresult
        · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      _ = _ := by
        rw [digestForecast_average]
        simp only [expected_secondBankValue_query, jointSecondBankValue]

/-- A target query can be charged after excluding the selected source; the bank still
includes every other partially cached candidate. This equality leaves the new-target
creation price explicit and does not assume a uniform cached source. -/
theorem expected_jointSecondBankStep (sk : Seeded.SecretKey) (source candidate : DigestCandidate)
    (hdistinct : source ≠ candidate) (call : Fin 2) (state : DigestBankState)
    (hsource : source ∉ state.1) (weight : MessageDigest → MessageDigest → ℝ≥0∞) :
    (∑' result, Pr[= result | digestBankStep sk candidate call state] *
      jointSecondBankValue sk source result.1 result.2 weight) =
        jointSecondBankValue sk source (insert candidate state.1) state.2 weight := by
  rw [digestBankStep, tsum_probOutput_map_mul]
  apply expected_jointSecondBankValue_query
  change source ∉ (insert candidate state.1 : Finset DigestCandidate)
  intro hmem
  rcases Finset.mem_insert.mp hmem with heq | hmem
  · exact hdistinct heq
  · exact hsource hmem

end LeanSphincs.Lifetime
