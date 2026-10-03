import LeanSphincs.LifetimeCachedSources

/-! Conditional digest forecasts pay for selected sources even when only one digest block
was prequeried. A rejected grinding prefix preserves all second blocks and adds only rejected
first blocks. Thus landed-digest forecasts decrease until the selected source is completed. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness
open Security (expectedHashCost)

variable [Params]

def LandedWeight (parameter : PublicParameter) (weight : MessageDigest → ℝ≥0∞) : Prop :=
  ∀ digest, ¬Landed parameter (digestIndex digest) → weight digest = 0

theorem digestForecast_rejected_eq_zero (sk : Seeded.SecretKey) (source : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞)
    (hweight : LandedWeight sk.parameter weight) (first : HashOutput)
    (hfirst : cache (candidateInput sk source 0) = some first)
    (hreject : ¬Landed sk.parameter (blockIndex first)) :
    digestForecast sk source cache weight = 0 := by
  rw [digestForecast, hfirst, blockForecast_some_left]
  have hzero (second : HashOutput) : weight (truncateMessageDigest first second) = 0 :=
    hweight _ (by simpa only [digestIndex_truncate] using hreject)
  simp only [hzero, mul_zero, tsum_zero]

structure RejectedGrindingPrefix (sk : Seeded.SecretKey) (message : Message)
    (before after : QueryCache HashSpec) : Prop where
  cache_le : before ≤ after
  second : ∀ randomness,
    after (candidateInput sk (message, randomness) 1) = before (candidateInput sk (message, randomness) 1)
  first : ∀ randomness answer, after (candidateInput sk (message, randomness) 0) = some answer →
    before (candidateInput sk (message, randomness) 0) = some answer ∨
      ¬Landed sk.parameter (blockIndex answer)

theorem RejectedGrindingPrefix.refl (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    RejectedGrindingPrefix sk message cache cache :=
  ⟨le_rfl, fun _ => rfl, fun _ _ h => Or.inl h⟩

theorem RejectedGrindingPrefix.query (sk : Seeded.SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (hprefix : RejectedGrindingPrefix sk message before after)
    (randomness : Randomness) (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle (spec := HashSpec) (msgInput sk message randomness)).run after))
    (hreject : ¬Landed sk.parameter (blockIndex result.1)) :
    RejectedGrindingPrefix sk message before result.2 := by
  obtain ⟨hgrowth, hcached⟩ := query_support_cached _ _ _ _ hresult
  refine ⟨hprefix.cache_le.trans hgrowth, ?_, ?_⟩
  · intro rho
    exact (query_other_cache_eq _ _
      (digestInput_calls_ne sk.parameter sk.root message rho randomness) after result hresult).trans
        (hprefix.second rho)
  · intro rho answer hanswer
    by_cases heq : rho = randomness
    · subst rho
      have heq' : result.1 = answer := Option.some.inj (hcached.symm.trans hanswer)
      exact Or.inr (heq' ▸ hreject)
    · have hne : candidateInput sk (message, rho) 0 ≠ msgInput sk message randomness :=
        fun h => heq (msgInput_inj sk message h)
      have hbefore := (query_other_cache_eq _ _ hne after result hresult).symm.trans hanswer
      exact hprefix.first rho answer hbefore

theorem RejectedGrindingPrefix.forecast_le (sk : Seeded.SecretKey) (message : Message)
    (before after : QueryCache HashSpec) (hprefix : RejectedGrindingPrefix sk message before after)
    (randomness : Randomness) (weight : MessageDigest → ℝ≥0∞)
    (hweight : LandedWeight sk.parameter weight) :
    digestForecast sk (message, randomness) after weight ≤
      digestForecast sk (message, randomness) before weight := by
  cases hfirst : after (candidateInput sk (message, randomness) 0) with
  | none =>
    have hbefore : before (candidateInput sk (message, randomness) 0) = none := by
      cases hb : before (candidateInput sk (message, randomness) 0) with
      | none => rfl
      | some answer =>
        have ha := hprefix.cache_le hb
        rw [hfirst] at ha
        contradiction
    simp only [digestForecast, hfirst, hbefore, hprefix.second, le_rfl]
  | some first =>
    rcases hprefix.first randomness first hfirst with hbefore | hreject
    · simp only [digestForecast, hfirst, hbefore, hprefix.second, le_rfl]
    · rw [digestForecast_rejected_eq_zero sk (message, randomness) after weight hweight first hfirst hreject]
      exact bot_le

noncomputable def selectedDigestForecast (sk : Seeded.SecretKey) (message : Message)
    (weight : Randomness → MessageDigest → ℝ≥0∞) (result : Option Randomness × QueryCache HashSpec) : ℝ≥0∞ :=
  match result.1 with
  | none => 0
  | some randomness => digestForecast sk (message, randomness) result.2 (weight randomness)

/-- Actual source selection, including partially cached candidates, charged to the initial
conditional forecast rather than pretending that a cached digest is uniform. -/
theorem expected_selectedDigestForecast_le (sk : Seeded.SecretKey) (message : Message)
    (before : QueryCache HashSpec) (weight : Randomness → MessageDigest → ℝ≥0∞)
    (hweight : ∀ randomness, LandedWeight sk.parameter (weight randomness)) :
    ∀ attempts after, RejectedGrindingPrefix sk message before after →
      (∑' result, Pr[= result | (simulateQ romImpl
        (Randomized.signDigestLoop sk message attempts)).run after] * selectedDigestForecast sk message weight result) ≤
      randomizerAverage (fun randomness => digestForecast sk (message, randomness) before (weight randomness)) *
        expectedHashCost (Randomized.signDigestLoop sk message attempts) after := by
  intro attempts
  induction attempts with
  | zero =>
    intro after _
    simp only [Randomized.signDigestLoop, simulateQ_pure, StateT.run_pure,
      tsum_probOutput_pure_mul, selectedDigestForecast, Security.expectedHashCost_pure, mul_zero, le_rfl]
  | succ attempts ih =>
    intro after hprefix
    let charge := randomizerAverage (fun randomness =>
      digestForecast sk (message, randomness) before (weight randomness))
    rw [run_randomizedDigest_succ, expectedHashCost_randomizedDigest_succ]
    change _ ≤ charge * _
    refine (expected_bind_le_of_support _ _ _ (fun randomness =>
      digestForecast sk (message, randomness) before (weight randomness) + charge *
        ∑' answer, Pr[= answer | (randomOracle (spec := HashSpec) (msgInput sk message randomness)).run after] *
          (if Landed sk.parameter (blockIndex answer.1) then 0 else
            expectedHashCost (Randomized.signDigestLoop sk message attempts) answer.2)) ?_).trans_eq ?_
    · intro randomness _
      refine (expected_bind_le_of_support _ _ _ (fun answer =>
        digestForecast sk (message, randomness) answer.2 (weight randomness) + charge *
          (if Landed sk.parameter (blockIndex answer.1) then 0 else
            expectedHashCost (Randomized.signDigestLoop sk message attempts) answer.2)) ?_).trans ?_
      · intro answer hanswer
        split
        · simp only [tsum_probOutput_pure_mul, selectedDigestForecast, mul_zero, add_zero, le_rfl]
        · exact (ih answer.2 (hprefix.query sk message before after randomness answer hanswer (by assumption))).trans le_add_self
      · simp only [mul_add, ENNReal.tsum_add]
        rw [expected_digestForecast_query]
        refine add_le_add (hprefix.forecast_le sk message before after randomness _ (hweight randomness)) (le_of_eq ?_)
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro answer
        ring
    · simp only [mul_add, ENNReal.tsum_add]
      change charge + _ = _
      rw [mul_one]
      congr 1
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro randomness
      ring

def newSourceDigestWeight (before : List SourceRecord)
    (weight : DigestCandidate → MessageDigest → ℝ≥0∞) (after : List SourceRecord) : ℝ≥0∞ :=
  match after with
  | [] => 0
  | record :: rest => if rest = before then weight record.source record.digest else 0

omit [Params] in
theorem newSourceDigestWeight_same (before : List SourceRecord)
    (weight : DigestCandidate → MessageDigest → ℝ≥0∞) : newSourceDigestWeight before weight before = 0 := by
  cases before with
  | nil => rfl
  | cons record rest =>
    rw [newSourceDigestWeight, if_neg]
    intro heq
    have := congrArg List.length heq
    simp only [List.length_cons] at this
    omega

/-- General actual-signer selection law for a source-dependent landed-digest weight. It
averages exactly over whichever digest bits were initially absent, preserving cached bias. -/
theorem expected_signWithSources_digest_weight_le (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (weight : DigestCandidate → MessageDigest → ℝ≥0∞)
    (hweight : ∀ randomness, LandedWeight sk.parameter (weight (message, randomness))) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      newSourceDigestWeight state.1 weight result.2.1) ≤
      randomizerAverage (fun randomness => digestForecast sk (message, randomness) state.2 (weight (message, randomness))) *
        expectedHashCost (Randomized.signDigestLoop sk message digestAttemptLimit) state.2 := by
  rw [signWithSources]
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

def PrequeriedSource (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (source : DigestCandidate) : Prop := ∃ call, cache (candidateInput sk source call) ≠ none

noncomputable def prequeriedUnrecordedWeight (sk : Seeded.SecretKey) (state : SourcedState)
    (weight : DigestCandidate → MessageDigest → ℝ≥0∞) (source : DigestCandidate) (digest : MessageDigest) : ℝ≥0∞ := by
  classical
  exact if ¬HasRecordedSource state.1 source ∧ PrequeriedSource sk state.2 source ∧
    Landed sk.parameter (digestIndex digest) then weight source digest else 0

/-- The cached-source contribution for the full actual signer, including cached first,
cached second, and both-cached pairs. Already recorded sources have zero charge. The explicit
conditional-forecast sum is what a target-bank accounting argument must pay; it is not assumed
to equal the independent-disclosure price. -/
theorem expected_prequeried_source_contribution_le (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (weight : DigestCandidate → MessageDigest → ℝ≥0∞) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      newSourceDigestWeight state.1 (prequeriedUnrecordedWeight sk state weight) result.2.1) ≤
      (((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ * ∑ randomness : Randomness,
        digestForecast sk (message, randomness) state.2
          (prequeriedUnrecordedWeight sk state weight (message, randomness))) *
            expectedHashCost (Randomized.signDigestLoop sk message digestAttemptLimit) state.2 := by
  have hland (randomness : Randomness) : LandedWeight sk.parameter
      (prequeriedUnrecordedWeight sk state weight (message, randomness)) := by
    intro digest hreject
    simp [prequeriedUnrecordedWeight, hreject]
  simpa only [randomizerAverage_card] using
    expected_signWithSources_digest_weight_le sk message state (prequeriedUnrecordedWeight sk state weight) hland

end LeanSphincs.Lifetime
