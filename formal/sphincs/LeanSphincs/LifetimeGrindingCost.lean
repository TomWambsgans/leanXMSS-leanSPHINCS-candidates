import LeanSphincs.LifetimeSourceSelection
import LeanSphincs.SecurityQueryCharge

/-! Weighted randomizer-source selection charged to the actual number of grinding hash calls,
not to the maximum loop length. Pruning and repeated randomizers keep their actual cost. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness
open Security (expectedHashCost)

theorem expectedHashCost_bind {α β : Type} (oa : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    expectedHashCost (oa >>= next) cache = expectedHashCost oa cache +
      ∑' first, Pr[= first | (simulateQ romImpl oa).run cache] * expectedHashCost (next first.1) first.2 := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp only [pure_bind, Security.expectedHashCost_pure, simulateQ_pure, StateT.run_pure,
      tsum_probOutput_pure_mul, zero_add]
  | query_bind input rest ih =>
    simp only [bind_assoc, Security.expectedHashCost_query_bind, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
    simp_rw [ih]
    simp only [mul_add, ENNReal.tsum_add, add_assoc]

theorem expectedHashCost_lift_prob {α : Type} (sample : ProbComp α) (cache : QueryCache HashSpec) :
    expectedHashCost (liftM sample : OracleComp OracleWorld α) cache = 0 := by
  induction sample using OracleComp.inductionOn generalizing cache with
  | pure value => simp [Security.expectedHashCost_pure]
  | query_bind input next ih =>
    rw [liftM_bind]
    change expectedHashCost ((liftM (OracleWorld.query (.inl input)) : OracleComp OracleWorld _) >>= fun answer =>
      (liftM (next answer) : OracleComp OracleWorld α)) cache = 0
    rw [Security.expectedHashCost_query_bind]
    simp only [Security.queryCost, Nat.cast_zero, zero_add, ih, mul_zero, tsum_zero]

theorem expectedHashCost_private_bind {α β : Type} (sample : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    expectedHashCost ((liftM sample : OracleComp OracleWorld α) >>= next) cache =
      ∑' value, Pr[= value | sample] * expectedHashCost (next value) cache := by
  rw [expectedHashCost_bind, expectedHashCost_lift_prob, zero_add, run_lift_prob,
    tsum_probOutput_map_mul]

variable [Params]

theorem expectedHashCost_randomizedDigest_succ (sk : Seeded.SecretKey) (message : Message)
    (attempts : Nat) (cache : QueryCache HashSpec) :
    expectedHashCost (Randomized.signDigestLoop sk message (attempts + 1)) cache = 1 +
      ∑' randomness, Pr[= randomness | ($ᵗ Randomness : ProbComp Randomness)] *
        ∑' answer, Pr[= answer | (randomOracle (spec := HashSpec) (msgInput sk message randomness)).run cache] *
          (if Landed sk.parameter (blockIndex answer.1) then 0 else
            expectedHashCost (Randomized.signDigestLoop sk message attempts) answer.2) := by
  rw [Randomized.signDigestLoop, expectedHashCost_private_bind]
  simp only [Seeded.signAttempt, messageDigestCall, oracleHash, HasQuery.query,
    liftM_bind, bind_assoc]
  simp only [apply_ite, liftM_pure, ite_bind, pure_bind]
  change (∑' randomness, Pr[= randomness | ($ᵗ Randomness : ProbComp Randomness)] *
    expectedHashCost ((liftM (OracleWorld.query (.inr (msgInput sk message randomness))) : OracleComp OracleWorld _) >>= fun answer =>
      if Landed sk.parameter (blockIndex answer) then pure (some randomness)
      else Randomized.signDigestLoop sk message attempts) cache) = _
  simp_rw [Security.expectedHashCost_query_bind]
  have hnext (randomness : Randomness) (answer : HashOutput × QueryCache HashSpec) :
      expectedHashCost (if Landed sk.parameter (blockIndex answer.1) then pure (some randomness)
        else Randomized.signDigestLoop sk message attempts) answer.2 =
        if Landed sk.parameter (blockIndex answer.1) then 0 else
          expectedHashCost (Randomized.signDigestLoop sk message attempts) answer.2 := by
    split_ifs <;> simp only [Security.expectedHashCost_pure]
  simp only [Security.queryCost, Nat.cast_one, hnext, mul_add, mul_one, ENNReal.tsum_add,
    tsum_probOutput_eq_one' (probFailure_uniformSample _)]
  simp only [← mul_ite]
  rfl

/-- Each actual grinding hash call pays exactly the uniform average of the fixed source
weights. This is sharper than charging the maximum attempt limit and needs no lower bound on
acceptance or assumption that the cached candidates themselves are uniform. -/
theorem expected_randomizedDigest_weight_le_hashCost (sk : Seeded.SecretKey) (message : Message)
    (weight : Randomness → ℝ≥0∞) : ∀ attempts cache,
    (∑' result, Pr[= result | (simulateQ romImpl
      (Randomized.signDigestLoop sk message attempts)).run cache] *
        selectedRandomizerWeight weight result.1) ≤
      randomizerAverage weight * expectedHashCost (Randomized.signDigestLoop sk message attempts) cache := by
  intro attempts
  induction attempts with
  | zero =>
    intro cache
    simp only [Randomized.signDigestLoop, simulateQ_pure, StateT.run_pure,
      tsum_probOutput_pure_mul, selectedRandomizerWeight, Security.expectedHashCost_pure, mul_zero, le_rfl]
  | succ attempts ih =>
    intro cache
    rw [run_randomizedDigest_succ, expectedHashCost_randomizedDigest_succ]
    refine (expected_bind_le_of_support _ _ _ (fun randomness => weight randomness +
      randomizerAverage weight * ∑' answer,
        Pr[= answer | (randomOracle (spec := HashSpec) (msgInput sk message randomness)).run cache] *
          (if Landed sk.parameter (blockIndex answer.1) then 0 else
            expectedHashCost (Randomized.signDigestLoop sk message attempts) answer.2)) ?_).trans_eq ?_
    · intro randomness _
      refine (expected_bind_le_of_support _ _ _ (fun answer => weight randomness +
        randomizerAverage weight * (if Landed sk.parameter (blockIndex answer.1) then 0 else
          expectedHashCost (Randomized.signDigestLoop sk message attempts) answer.2)) ?_).trans_eq ?_
      · intro answer _
        split
        · simp only [tsum_probOutput_pure_mul, selectedRandomizerWeight, mul_zero, add_zero, le_rfl]
        · exact (ih answer.2).trans le_add_self
      · simp only [mul_add, ENNReal.tsum_add]
        rw [ENNReal.tsum_mul_right]
        have hmass : (∑' answer, Pr[= answer |
            (randomOracle (spec := HashSpec) (msgInput sk message randomness)).run cache]) = 1 :=
          Security.world_query_mass (.inr (msgInput sk message randomness)) cache
        rw [hmass, one_mul]
        congr 1
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro answer
        ring
    · simp only [mul_add, ENNReal.tsum_add]
      change randomizerAverage weight + _ = _
      rw [mul_one]
      congr 1
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro randomness
      ring

theorem expected_signWithSources_weight_le_grinding_cost (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (weight : DigestCandidate → ℝ≥0∞) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      newSourceRecordWeight state.1 weight result.2.1) ≤
      randomizerAverage (fun randomness => weight (message, randomness)) *
        expectedHashCost (Randomized.signDigestLoop sk message digestAttemptLimit) state.2 := by
  rw [signWithSources]
  refine (expected_bind_le_of_support _ _ _
    (fun loop => selectedRandomizerWeight (fun randomness => weight (message, randomness)) loop.1) ?_).trans
      (expected_randomizedDigest_weight_le_hashCost sk message (fun randomness => weight (message, randomness))
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

theorem expected_signWithSources_weight_le_sign_cost (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (weight : DigestCandidate → ℝ≥0∞) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      newSourceRecordWeight state.1 weight result.2.1) ≤
      randomizerAverage (fun randomness => weight (message, randomness)) *
        expectedHashCost (Randomized.sign sk message) state.2 := by
  refine (expected_signWithSources_weight_le_grinding_cost sk message state weight).trans ?_
  apply mul_le_mul' le_rfl
  rw [Randomized.sign, expectedHashCost_bind]
  exact le_self_add

end LeanSphincs.Lifetime
