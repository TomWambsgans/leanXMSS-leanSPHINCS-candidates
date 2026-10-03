import LeanSphincs.LifetimeConditionalSources

/-! Joint conditional forecasts for distinct message/randomizer pairs. Revealing either
block of either pair preserves the joint forecast, including either partially cached order.
This is the cross-source term required when an adversarial prequery later becomes a signing
source; the two pairs must be distinct, since their own digest blocks are then disjoint. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

theorem digestForecast_congr_cache (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (before after : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞)
    (hcache : ∀ call, after (candidateInput sk candidate call) = before (candidateInput sk candidate call)) :
    digestForecast sk candidate after weight = digestForecast sk candidate before weight := by
  simp only [digestForecast, hcache]

theorem digestForecast_mono (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) {left right : MessageDigest → ℝ≥0∞}
    (hle : ∀ digest, left digest ≤ right digest) :
    digestForecast sk candidate cache left ≤ digestForecast sk candidate cache right := by
  simp only [digestForecast_eq_expected_messageDigest]
  exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (hle result.1)

noncomputable def pairForecast (sk : Seeded.SecretKey) (target source : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → MessageDigest → ℝ≥0∞) : ℝ≥0∞ :=
  digestForecast sk target cache (fun targetDigest =>
    digestForecast sk source cache (weight targetDigest))

theorem pairForecast_comm (sk : Seeded.SecretKey) (target source : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → MessageDigest → ℝ≥0∞) :
    pairForecast sk target source cache weight =
      pairForecast sk source target cache (fun sourceDigest targetDigest => weight targetDigest sourceDigest) := by
  simp only [pairForecast, digestForecast_eq_expected_messageDigest]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro sourceResult
  apply tsum_congr
  intro targetResult
  ring

theorem digestForecast_query_other (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) (input : HashInput)
    (hne : ∀ call, candidateInput sk candidate call ≠ input)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle (spec := HashSpec) input).run cache)) :
    digestForecast sk candidate result.2 weight = digestForecast sk candidate cache weight :=
  digestForecast_congr_cache sk candidate cache result.2 weight
    (fun call => query_other_cache_eq input _ (hne call) cache result hresult)

/-- A query cannot reveal blocks of two distinct source pairs. Its joint conditional mean
therefore remains unchanged even when the other pair has arbitrary cached blocks. -/
theorem expected_pairForecast_query (sk : Seeded.SecretKey) (target source : DigestCandidate)
    (hdistinct : target ≠ source) (cache : QueryCache HashSpec)
    (weight : MessageDigest → MessageDigest → ℝ≥0∞) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
      pairForecast sk target source result.2 weight) = pairForecast sk target source cache weight := by
  classical
  by_cases htarget : ∃ call, candidateInput sk target call = input
  · obtain ⟨call, rfl⟩ := htarget
    have hsource (i : Fin 2) : candidateInput sk source i ≠ candidateInput sk target call :=
      fun heq => hdistinct (candidateInput_candidate_injective sk i call heq).symm
    calc
      _ = ∑' result, Pr[= result | (randomOracle (spec := HashSpec) (candidateInput sk target call)).run cache] *
          digestForecast sk target result.2 (fun digest => digestForecast sk source cache (weight digest)) := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support ((randomOracle (spec := HashSpec) (candidateInput sk target call)).run cache)
        · congr 1
          unfold pairForecast
          congr 1
          funext digest
          exact digestForecast_query_other sk source cache (weight digest) _ hsource result hresult
        · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      _ = _ := expected_digestForecast_query sk target cache _ _
  · have htarget' : ∀ call, candidateInput sk target call ≠ input := by
      intro call heq
      exact htarget ⟨call, heq⟩
    calc
      _ = ∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
          digestForecast sk target cache (fun digest => digestForecast sk source result.2 (weight digest)) := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support ((randomOracle (spec := HashSpec) input).run cache)
        · congr 1
          exact digestForecast_query_other sk target cache _ input htarget' result hresult
        · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      _ = _ := by
        rw [digestForecast_average]
        simp only [expected_digestForecast_query, pairForecast]

theorem pairForecast_fresh_source (sk : Seeded.SecretKey) (target source : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → MessageDigest → ℝ≥0∞)
    (hfresh : ∀ call, cache (candidateInput sk source call) = none) :
    pairForecast sk target source cache weight = digestForecast sk target cache
      (fun digest => uniformDigestForecast (weight digest)) := by
  simp only [pairForecast, fresh_digestForecast_uniform sk source cache _ hfresh, uniformDigestForecast]

theorem pairForecast_fresh_target (sk : Seeded.SecretKey) (target source : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → MessageDigest → ℝ≥0∞)
    (hfresh : ∀ call, cache (candidateInput sk target call) = none) :
    pairForecast sk target source cache weight = digestForecast sk source cache
      (fun digest => uniformDigestForecast (fun targetDigest => weight targetDigest digest)) := by
  rw [pairForecast_comm, pairForecast_fresh_source sk source target cache _ hfresh]

end LeanSphincs.Lifetime
