import LeanSphincs.LifetimeRectangles
import LeanSphincs.LifetimePriorMarginal

/-! The actual message-grinding/source transition with an arbitrary signing suffix.
This permits the structural forced-failure comparison to share the same disclosure history:
only the message prefix is fixed here. No independence of other hash domains is required. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness
attribute [local instance] Classical.propDecidable

variable [Params]

abbrev SigningSuffix := Randomness → MessageDigest → QueryCache HashSpec →
  ProbComp (Option Signature × QueryCache HashSpec)

noncomputable def signWithSourcesThen (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix) (state : SourcedState) : ProbComp (Option Signature × SourcedState) := do
  let loop ← (simulateQ romImpl (Randomized.signDigestLoop sk message digestAttemptLimit)).run state.2
  match loop.1 with
  | none => pure (none, (state.1, loop.2))
  | some randomness =>
    let digest ← (simulateQ randomOracle
      (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run loop.2
    let result ← suffix randomness digest.1 digest.2
    pure (result.1, (⟨(message, randomness), digest.1, result.1⟩ :: state.1, result.2))

theorem signWithSourcesThen_actual (sk : Seeded.SecretKey) (message : Message) (state : SourcedState) :
    signWithSourcesThen sk message (fun randomness digest cache =>
      (simulateQ randomOracle (finishSignBody sk randomness digest)).run cache) state =
      signWithSources sk message state := rfl

theorem signWithSourcesThen_record_shape (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix) (state : SourcedState) (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSourcesThen sk message suffix state)) :
    (result.1 = none ∧ result.2.1 = state.1) ∨
      ∃ randomness digest, result.2.1 = ⟨(message, randomness), digest, result.1⟩ :: state.1 := by
  rw [signWithSourcesThen, mem_support_bind_iff] at hresult
  obtain ⟨⟨loop, middle⟩, _, hresult⟩ := hresult
  cases loop with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact Or.inl ⟨rfl, rfl⟩
  | some randomness =>
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨digest, beforeBody⟩, _, hresult⟩ := hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨response, afterBody⟩, _, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact Or.inr ⟨randomness, digest, rfl⟩

/-- A suffix returning a result on every path retains total mass, even if its response is
`none` or its primitive equality checks are forced to return failure. -/
theorem signWithSourcesThen_mass (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix)
    (hmass : ∀ randomness digest cache, (∑' result, Pr[= result | suffix randomness digest cache]) = 1)
    (state : SourcedState) :
    (∑' result, Pr[= result | signWithSourcesThen sk message suffix state]) = 1 := by
  rw [← mul_one (∑' result, Pr[= result | signWithSourcesThen sk message suffix state]),
    ← ENNReal.tsum_mul_right, signWithSourcesThen, tsum_probOutput_bind_mul]
  have hinner (loop : Option Randomness × QueryCache HashSpec) :
      (∑' result, Pr[= result | (match loop.1 with
        | none => pure (none, (state.1, loop.2))
        | some randomness => do
          let digest ← (simulateQ randomOracle
            (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run loop.2
          let result ← suffix randomness digest.1 digest.2
          pure ((result.1, (({ source := (message, randomness), digest := digest.1, response := result.1 } : SourceRecord) :: state.1, result.2)) : Option Signature × SourcedState))] * (1 : ℝ≥0∞)) = 1 := by
    cases loop.1 with
    | none => simp only [tsum_probOutput_pure_mul]
    | some randomness =>
      have hsuffix (digest : MessageDigest × QueryCache HashSpec) :
          (∑' result, Pr[= result | (do
            let value ← suffix randomness digest.1 digest.2
            pure ((value.1, ((⟨(message, randomness), digest.1, value.1⟩ : SourceRecord) :: state.1, value.2)) : Option Signature × SourcedState))]) = 1 := by
        simpa only [bind_pure_comp, mul_one, hmass] using
          (tsum_probOutput_map_mul (suffix randomness digest.1 digest.2)
            (fun value => ((value.1, ((⟨(message, randomness), digest.1, value.1⟩ : SourceRecord) :: state.1, value.2)) : Option Signature × SourcedState))
            (fun _ => (1 : ℝ≥0∞)))
      rw [tsum_probOutput_bind_mul]
      simp only [mul_one, hsuffix]
      exact tsum_probOutput_eq_one' (probFailure_eq_zero' (neverFail_simulateQ_randomOracle_run
        (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest) loop.2))
  simp only [mul_one] at hinner
  simp only [mul_one, hinner]
  apply tsum_probOutput_eq_one'
  rw [← Security.erase_countedRun, probFailure_map, Security.countedRun_failure]

theorem signWithSourcesThen_future_gain (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix) (state : SourcedState) (n : Nat) (target : MessageDigest)
    (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSourcesThen sk message suffix state)) :
    futureCoverWeight sk.parameter n (sourcedPrior result.2.1) target =
      futureCoverWeight sk.parameter n (sourcedPrior state.1) target +
        newSourceDigestWeight state.1 (fun _ digest =>
          futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1 := by
  rcases signWithSourcesThen_record_shape sk message suffix state result hresult with
    ⟨_, hsame⟩ | ⟨randomness, digest, hcons⟩
  · simp only [hsame, newSourceDigestWeight_same, add_zero]
  · rw [hcons, sourcedPrior_cons, futureCoverWeight_insert]
    simp only [newSourceDigestWeight, if_true]

/-- The same centered identity holds in the common comparison history. All assumptions on
unrelated primitive-oracle behavior have been replaced by the suffix's total-mass fact. -/
theorem expected_signWithSourcesThen_centered_gain (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix)
    (hmass : ∀ randomness digest cache, (∑' result, Pr[= result | suffix randomness digest cache]) = 1)
    (state : SourcedState) (n : Nat) (target : MessageDigest) :
    (∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
      futureCoverWeight sk.parameter n (sourcedPrior result.2.1) target) +
        independentGainMean sk.parameter n (sourcedPrior state.1) target =
      futureCoverWeight sk.parameter (n + 1) (sourcedPrior state.1) target +
        ∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
          newSourceDigestWeight state.1 (fun _ digest =>
            futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1 := by
  have hgain : (∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
      futureCoverWeight sk.parameter n (sourcedPrior result.2.1) target) =
      futureCoverWeight sk.parameter n (sourcedPrior state.1) target +
        ∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
          newSourceDigestWeight state.1 (fun _ digest =>
            futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1 := by
    calc
      _ = ∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
          (futureCoverWeight sk.parameter n (sourcedPrior state.1) target +
            newSourceDigestWeight state.1 (fun _ digest =>
              futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1) := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (signWithSourcesThen sk message suffix state)
        · rw [signWithSourcesThen_future_gain sk message suffix state n target result hresult]
        · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      _ = _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          signWithSourcesThen_mass sk message suffix hmass state, one_mul]
  rw [hgain, futureCoverWeight_succ_gain]
  ac_rfl

/-- Selection still uses the exact actual randomized message grinding, regardless of the
suffix. Subprobability suffixes are allowed for this upper bound. -/
theorem expected_signWithSourcesThen_digest_weight_le (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix) (state : SourcedState) (weight : DigestCandidate → MessageDigest → ℝ≥0∞)
    (hweight : ∀ randomness, LandedWeight sk.parameter (weight (message, randomness))) :
    (∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
      newSourceDigestWeight state.1 weight result.2.1) ≤
      randomizerAverage (fun randomness => digestForecast sk (message, randomness) state.2 (weight (message, randomness))) *
        Security.expectedHashCost (Randomized.signDigestLoop sk message digestAttemptLimit) state.2 := by
  rw [signWithSourcesThen]
  refine (expected_bind_le_of_support _ _ _
    (selectedDigestForecast sk message (fun randomness => weight (message, randomness))) ?_).trans
      (expected_selectedDigestForecast_le sk message state.2 (fun randomness => weight (message, randomness))
        hweight digestAttemptLimit state.2 (RejectedGrindingPrefix.refl sk message state.2))
  rintro ⟨loop, middle⟩ _
  cases loop with
  | none => simp only [tsum_probOutput_pure_mul, newSourceDigestWeight_same, selectedDigestForecast, le_rfl]
  | some randomness =>
    change _ ≤ digestForecast sk (message, randomness) middle (weight (message, randomness))
    rw [digestForecast_eq_expected_messageDigest]
    apply expected_bind_le_of_support
    intro digest _
    apply expected_bind_le_constant
    intro result _
    simp only [tsum_probOutput_pure_mul, newSourceDigestWeight, if_true, le_rfl]

end LeanSphincs.Lifetime
