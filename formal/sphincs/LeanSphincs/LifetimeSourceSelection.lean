import LeanSphincs.LifetimeSources

/-! Weighted selection prices for the actual 128-bit randomizer loop. We retain the actual
pruning test, cache, and repeated randomizer draws. The weight can charge only selected
prequeried sources; cache defects that are never selected incur no charge. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

noncomputable def randomizerAverage (weight : Randomness → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' randomness, Pr[= randomness | ($ᵗ Randomness : ProbComp Randomness)] * weight randomness

def selectedRandomizerWeight (weight : Randomness → ℝ≥0∞) : Option Randomness → ℝ≥0∞
  | none => 0
  | some randomness => weight randomness

theorem randomizerAverage_card (weight : Randomness → ℝ≥0∞) :
    randomizerAverage weight = ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ * ∑ randomness : Randomness, weight randomness := by
  rw [randomizerAverage]
  simp only [probOutput_uniformSample, card_bitVec, Randomness, digestBits]
  rw [ENNReal.tsum_mul_left, tsum_fintype]

variable [Params]

/-- A direct bound for the actual loop, not an independence assumption about accepted
digests. Only the randomizer sampled on a trial is uniform; the acceptance rule may be biased
by arbitrary previous hash queries. Every repeated draw consumes another actual trial. -/
theorem expected_randomizedDigest_source_weight (sk : Seeded.SecretKey) (message : Message)
    (weight : Randomness → ℝ≥0∞) :
    ∀ attempts cache,
      (∑' result, Pr[= result | (simulateQ romImpl
        (Randomized.signDigestLoop sk message attempts)).run cache] *
          selectedRandomizerWeight weight result.1) ≤ attempts * randomizerAverage weight := by
  intro attempts
  induction attempts with
  | zero =>
    intro cache
    simp only [Randomized.signDigestLoop, simulateQ_pure, StateT.run_pure,
      tsum_probOutput_pure_mul, selectedRandomizerWeight, Nat.cast_zero, zero_mul, le_rfl]
  | succ attempts ih =>
    intro cache
    rw [run_randomizedDigest_succ]
    refine (expected_bind_le_of_support _ _ _ (fun randomness =>
      weight randomness + attempts * randomizerAverage weight) ?_).trans ?_
    · intro randomness _
      apply expected_bind_le_constant
      intro answer _
      split
      · simp only [tsum_probOutput_pure_mul, selectedRandomizerWeight]
        exact le_self_add
      · exact (ih answer.2).trans le_add_self
    · simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      rw [tsum_probOutput_eq_one' (probFailure_uniformSample _), one_mul]
      change randomizerAverage weight + attempts * randomizerAverage weight ≤ _
      rw [Nat.cast_add, Nat.cast_one]
      exact le_of_eq (by ring)

theorem expected_randomizedDigest_source_weight_bits (sk : Seeded.SecretKey) (message : Message)
    (weight : Randomness → ℝ≥0∞) (attempts : Nat) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (simulateQ romImpl
      (Randomized.signDigestLoop sk message attempts)).run cache] *
        selectedRandomizerWeight weight result.1) ≤
      (attempts : ℝ≥0∞) / 2 ^ 128 * ∑ randomness : Randomness, weight randomness := by
  refine (expected_randomizedDigest_source_weight sk message weight attempts cache).trans_eq ?_
  rw [randomizerAverage_card, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_assoc]

/-- Weight only records created by this call, identified by their newly prepended position.
The accepted record exists even if assembly returns `none`. -/
def newSourceRecordWeight (before : List SourceRecord) (weight : DigestCandidate → ℝ≥0∞)
    (after : List SourceRecord) : ℝ≥0∞ :=
  match after with
  | [] => 0
  | record :: rest => if rest = before then weight record.source else 0

omit [Params] in
theorem newSourceRecordWeight_same (before : List SourceRecord) (weight : DigestCandidate → ℝ≥0∞) :
    newSourceRecordWeight before weight before = 0 := by
  cases before with
  | nil => rfl
  | cons record rest =>
    rw [newSourceRecordWeight, if_neg]
    intro heq
    have := congrArg List.length heq
    simp only [List.length_cons] at this
    omega

omit [Params] in
theorem newSourceRecordWeight_cons (before : List SourceRecord) (weight : DigestCandidate → ℝ≥0∞)
    (record : SourceRecord) : newSourceRecordWeight before weight (record :: before) = weight record.source := by
  simp only [newSourceRecordWeight, if_true]

/-- The weighted charge for the new source of a complete actual signing call is paid by its
128-bit randomizer draws. Exhausted assembly cannot increase this expectation. -/
theorem expected_signWithSources_source_weight (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (weight : DigestCandidate → ℝ≥0∞) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      newSourceRecordWeight state.1 weight result.2.1) ≤
        (digestAttemptLimit : ℝ≥0∞) / 2 ^ 128 *
          ∑ randomness : Randomness, weight (message, randomness) := by
  rw [signWithSources]
  refine (expected_bind_le_of_support _ _ _
    (fun loop => selectedRandomizerWeight (fun randomness => weight (message, randomness)) loop.1) ?_).trans
      (expected_randomizedDigest_source_weight_bits sk message (fun randomness => weight (message, randomness))
        digestAttemptLimit state.2)
  rintro ⟨loop, middle⟩ _
  cases loop with
  | none => simp only [tsum_probOutput_pure_mul, newSourceRecordWeight_same, selectedRandomizerWeight, le_rfl]
  | some randomness =>
    apply expected_bind_le_constant
    intro digest _
    apply expected_bind_le_constant
    intro result _
    simp only [tsum_probOutput_pure_mul, newSourceRecordWeight_cons, selectedRandomizerWeight, le_rfl]

end LeanSphincs.Lifetime
