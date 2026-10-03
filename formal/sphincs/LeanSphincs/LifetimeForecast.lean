import LeanSphincs.LifetimeCandidate

/-!
Conditional forecasts for the two-block digest. An adversary may reveal either block first
and choose subsequent queries from its answers. For any fixed nonnegative digest weight,
revealing an additional oracle answer preserves the conditional forecast in expectation.
This is the cache part of the target-bank method used by leanVM b7a107256, with the candidate's
actual two differently tweaked digest blocks rather than an atomic uniform digest.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

noncomputable def blockLaw : Option HashOutput → ProbComp HashOutput
  | none => $ᵗ HashOutput
  | some answer => pure answer

noncomputable def blockForecast (weight : HashOutput → HashOutput → ℝ≥0∞)
    (first second : Option HashOutput) : ℝ≥0∞ :=
  ∑' left, Pr[= left | blockLaw first] *
    ∑' right, Pr[= right | blockLaw second] * weight left right

theorem blockForecast_some_left (weight : HashOutput → HashOutput → ℝ≥0∞)
    (first : HashOutput) (second : Option HashOutput) :
    blockForecast weight (some first) second =
      ∑' right, Pr[= right | blockLaw second] * weight first right := by
  simp only [blockForecast, blockLaw, tsum_probOutput_pure_mul]

theorem blockForecast_some_right (weight : HashOutput → HashOutput → ℝ≥0∞)
    (first : Option HashOutput) (second : HashOutput) :
    blockForecast weight first (some second) =
      ∑' left, Pr[= left | blockLaw first] * weight left second := by
  simp only [blockForecast, blockLaw, tsum_probOutput_pure_mul]

theorem blockForecast_both (weight : HashOutput → HashOutput → ℝ≥0∞)
    (first second : HashOutput) : blockForecast weight (some first) (some second) = weight first second := by
  simp only [blockForecast_some_left, blockLaw, tsum_probOutput_pure_mul]

theorem blockForecast_reveal_left (weight : HashOutput → HashOutput → ℝ≥0∞)
    (second : Option HashOutput) :
    (∑' first, Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] *
      blockForecast weight (some first) second) = blockForecast weight none second := by
  simp_rw [blockForecast_some_left]
  rfl

theorem blockForecast_reveal_right (weight : HashOutput → HashOutput → ℝ≥0∞)
    (first : Option HashOutput) :
    (∑' second, Pr[= second | ($ᵗ HashOutput : ProbComp HashOutput)] *
      blockForecast weight first (some second)) = blockForecast weight first none := by
  simp_rw [blockForecast_some_right]
  rw [blockForecast]
  simp only [blockLaw]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro left
  apply tsum_congr
  intro right
  ring

/-- A message/randomizer pair identifies a candidate before either digest block is known. -/
abbrev DigestCandidate := Message × Randomness

def candidateInput (sk : Seeded.SecretKey) (candidate : DigestCandidate) (call : Fin 2) : HashInput :=
  Security.digestInput sk.parameter sk.root candidate.1 candidate.2 call

theorem candidateInput_candidate_injective (sk : Seeded.SecretKey)
    {left right : DigestCandidate} (i j : Fin 2)
    (h : candidateInput sk left i = candidateInput sk right j) : left = right := by
  obtain ⟨leftMessage, leftRandomness⟩ := left
  obtain ⟨rightMessage, rightRandomness⟩ := right
  have hm := digestInput_message_injective sk.parameter sk.root leftRandomness rightRandomness i j h
  change leftMessage = rightMessage at hm
  subst rightMessage
  have hi : i = j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim ((digestInput_calls_ne sk.parameter sk.root leftMessage rightRandomness leftRandomness) h.symm)
    · exact False.elim ((digestInput_calls_ne sk.parameter sk.root leftMessage leftRandomness rightRandomness) h)
    · rfl
  subst j
  have hr := digestInput_randomness_injective sk.parameter sk.root leftMessage i h
  exact Prod.ext rfl hr

noncomputable def digestForecast (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) : ℝ≥0∞ :=
  blockForecast (fun first second => weight (truncateMessageDigest first second))
    (cache (candidateInput sk candidate 0)) (cache (candidateInput sk candidate 1))

theorem digestForecast_fresh (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞)
    (hfresh : ∀ call, cache (candidateInput sk candidate call) = none) :
    digestForecast sk candidate cache weight =
      blockForecast (fun first second => weight (truncateMessageDigest first second)) none none := by
  simp only [digestForecast, hfresh]

/-- Every actual single hash query is a martingale step for a fixed candidate forecast.
This includes queries to the second block before the first, either cached block, and unrelated
hash domains. No freshness or independence hypothesis is imposed on the current cache. -/
theorem expected_digestForecast_query (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
      digestForecast sk candidate result.2 weight) = digestForecast sk candidate cache weight := by
  cases hc : cache input with
  | some answer => rw [cached_run _ _ _ hc, tsum_probOutput_pure_mul]
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ hc, tsum_probOutput_map_mul]
    by_cases hfirst : candidateInput sk candidate 0 = input
    · subst input
      have hne : candidateInput sk candidate 1 ≠ candidateInput sk candidate 0 :=
        digestInput_calls_ne sk.parameter sk.root candidate.1 candidate.2 candidate.2
      simp only [digestForecast, QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne cache _ hne, hc]
      exact blockForecast_reveal_left _ _
    · by_cases hsecond : candidateInput sk candidate 1 = input
      · subst input
        simp only [digestForecast, QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne cache _ hfirst, hc]
        exact blockForecast_reveal_right _ _
      · simp only [digestForecast, QueryCache.cacheQuery_of_ne cache _ hfirst,
          QueryCache.cacheQuery_of_ne cache _ hsecond]
        change (∑' answer : HashOutput, Pr[= answer | ($ᵗ HashOutput : ProbComp HashOutput)] *
          digestForecast sk candidate cache weight) = _
        rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (probFailure_uniformSample _), one_mul]
        rfl

theorem digestForecast_eq_expected_messageDigest (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) :
    digestForecast sk candidate cache weight =
      ∑' result, Pr[= result | (simulateQ randomOracle
        (messageDigest sk.parameter sk.root candidate.1 candidate.2 : OracleComp HashSpec MessageDigest)).run cache] *
          weight result.1 := by
  cases hfirst : cache (candidateInput sk candidate 0) with
  | none =>
    cases hsecond : cache (candidateInput sk candidate 1) with
    | none =>
      have hfresh : Security.DigestFresh sk.parameter sk.root candidate.1 candidate.2 cache := by
        intro call
        fin_cases call
        · exact hfirst
        · exact hsecond
      rw [Security.run_messageDigest_fresh sk.parameter sk.root candidate.1 candidate.2 cache hfresh]
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
        digestForecast, hfirst, hsecond, blockForecast, blockLaw]
    | some second =>
      rw [run_messageDigest_cached_second sk.parameter sk.root candidate.1 candidate.2 cache second hfirst hsecond]
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
        digestForecast, hfirst, hsecond, blockForecast_some_right, blockLaw]
  | some first =>
    cases hsecond : cache (candidateInput sk candidate 1) with
    | none =>
      rw [Security.run_messageDigest_cached_first sk.parameter sk.root candidate.1 candidate.2 cache first hfirst hsecond]
      simp only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul,
        digestForecast, hfirst, hsecond, blockForecast_some_left, blockLaw]
    | some second =>
      rw [run_messageDigest_cached_both sk.parameter sk.root candidate.1 candidate.2 cache first second hfirst hsecond]
      simp only [tsum_probOutput_pure_mul, digestForecast, hfirst, hsecond, blockForecast_both]

theorem fresh_digestForecast_uniform (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞)
    (hfresh : ∀ call, cache (candidateInput sk candidate call) = none) :
    digestForecast sk candidate cache weight =
      ∑' digest, Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] * weight digest := by
  rw [digestForecast_eq_expected_messageDigest]
  have heq := Security.evalDist_messageDigest_fresh sk.parameter sk.root candidate.1 candidate.2 cache hfresh
  have hp := fun digest => congrArg (fun distribution => distribution digest) heq
  calc
    _ = ∑' digest, Pr[= digest | Prod.fst <$> (simulateQ randomOracle
        (messageDigest sk.parameter sk.root candidate.1 candidate.2 : OracleComp HashSpec MessageDigest)).run cache] *
          weight digest := (tsum_probOutput_map_mul _ _ _).symm
    _ = _ := tsum_congr fun digest => congrArg (fun p => p * weight digest) (hp digest)

end LeanSphincs.Lifetime
