import LeanSphincs.LifetimePairForecast

/-! A second-moment bank for a fixed source-insertion kernel. Its distinct-target terms
retain the product of two conditional forecasts; replacing this sum by the number of targets
times its diagonal would lose a factor in the hash-query bound. This module concerns a fixed
kernel. Transferring it through capped, adaptive signing disclosures remains separate. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

attribute [local instance] Classical.propDecidable

theorem pairForecast_product (sk : Seeded.SecretKey) (target source : DigestCandidate)
    (cache : QueryCache HashSpec) (left right : MessageDigest → ℝ≥0∞) :
    pairForecast sk target source cache (fun first second => left first * right second) =
      digestForecast sk target cache left * digestForecast sk source cache right := by
  simp only [pairForecast, digestForecast_eq_expected_messageDigest]
  simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro result
  apply tsum_congr
  intro other
  ring

noncomputable def targetSecondForecast (sk : Seeded.SecretKey) (left right : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) : ℝ≥0∞ :=
  if left = right then digestForecast sk left cache (fun digest => weight digest ^ 2)
  else pairForecast sk left right cache (fun first second => weight first * weight second)

noncomputable def secondBankValue (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ left ∈ bank, ∑ right ∈ bank, targetSecondForecast sk left right cache weight

theorem targetSecondForecast_comm (sk : Seeded.SecretKey) (left right : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) :
    targetSecondForecast sk left right cache weight = targetSecondForecast sk right left cache weight := by
  by_cases heq : left = right
  · subst right; rfl
  · simp only [targetSecondForecast, heq, Ne.symm heq, if_false, pairForecast_product, mul_comm]

theorem expected_targetSecondForecast_query (sk : Seeded.SecretKey) (left right : DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
      targetSecondForecast sk left right result.2 weight) = targetSecondForecast sk left right cache weight := by
  by_cases heq : left = right
  · simp only [targetSecondForecast, heq, if_true]
    exact expected_digestForecast_query sk _ cache _ input
  · simp only [targetSecondForecast, heq, if_false]
    exact expected_pairForecast_query sk left right heq cache _ input

/-- Cached or fresh queries to either digest block preserve all existing diagonal and
distinct-target second-moment forecasts exactly. -/
theorem expected_secondBankValue_query (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) (input : HashInput) :
    (∑' result, Pr[= result | (randomOracle (spec := HashSpec) input).run cache] *
      secondBankValue sk bank result.2 weight) = secondBankValue sk bank cache weight := by
  simp only [secondBankValue, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro left _
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro right _
  exact expected_targetSecondForecast_query sk left right cache weight input

theorem secondBankValue_insert (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (candidate : DigestCandidate) (hnew : candidate ∉ bank) (cache : QueryCache HashSpec)
    (weight : MessageDigest → ℝ≥0∞) :
    secondBankValue sk (insert candidate bank) cache weight =
      secondBankValue sk bank cache weight + digestForecast sk candidate cache (fun digest => weight digest ^ 2) +
        2 * digestForecast sk candidate cache weight * digestBankValue sk bank cache weight := by
  have hrow : (∑ right ∈ bank, targetSecondForecast sk candidate right cache weight) =
      digestForecast sk candidate cache weight * digestBankValue sk bank cache weight := by
    rw [digestBankValue, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right hright
    have hne : candidate ≠ right := fun heq => hnew (heq.symm ▸ hright)
    simp only [targetSecondForecast, hne, if_false, pairForecast_product]
  have hcolumn : (∑ left ∈ bank, targetSecondForecast sk left candidate cache weight) =
      digestForecast sk candidate cache weight * digestBankValue sk bank cache weight := by
    simpa only [targetSecondForecast_comm sk _ candidate cache weight] using hrow
  rw [secondBankValue, Finset.sum_insert hnew]
  simp only [Finset.sum_insert hnew, Finset.sum_add_distrib]
  rw [hrow, hcolumn]
  simp only [targetSecondForecast, if_true]
  change _ = _ + _ + _
  unfold secondBankValue targetSecondForecast
  ring

/-- Revealing a new target creates only its diagonal mean and two cross terms with the
existing first-moment bank. The fresh target's conditional second moment is retained exactly. -/
theorem expected_secondBankStep (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (state : DigestBankState) (hrecorded : DigestQueriesRecorded sk state.1 state.2)
    (weight : MessageDigest → ℝ≥0∞) :
    (∑' result, Pr[= result | digestBankStep sk candidate call state] *
      secondBankValue sk result.1 result.2 weight) =
        secondBankValue sk state.1 state.2 weight + if candidate ∈ state.1 then 0 else
          uniformDigestForecast (fun digest => weight digest ^ 2) +
            2 * uniformDigestForecast weight * digestBankValue sk state.1 state.2 weight := by
  rw [digestBankStep, tsum_probOutput_map_mul, expected_secondBankValue_query]
  by_cases hmem : candidate ∈ state.1
  · simp only [Finset.insert_eq_of_mem hmem, hmem, if_true, add_zero]
  · rw [secondBankValue_insert sk state.1 candidate hmem state.2 weight]
    simp only [hmem, if_false,
      fresh_digestForecast_uniform sk candidate state.2 _ (hrecorded candidate hmem), uniformDigestForecast]
    ring

theorem uniformDigestForecast_square_le (weight : MessageDigest → ℝ≥0∞)
    (hbound : ∀ digest, weight digest ≤ 1) :
    uniformDigestForecast (fun digest => weight digest ^ 2) ≤ uniformDigestForecast weight := by
  apply ENNReal.tsum_le_tsum
  intro digest
  apply mul_le_mul' le_rfl
  change weight digest ^ 2 ≤ weight digest
  rw [pow_two]
  exact mul_le_of_le_one_right' (hbound digest)

/-- The localized price: one new target costs at most its fresh mean plus twice the
localized source measure times the existing first-moment bank. -/
theorem expected_secondBankStep_le (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (state : DigestBankState) (hrecorded : DigestQueriesRecorded sk state.1 state.2)
    (weight : MessageDigest → ℝ≥0∞) (hbound : ∀ digest, weight digest ≤ 1)
    (cap : ℝ≥0∞) (hcap : uniformDigestForecast weight ≤ cap) :
    (∑' result, Pr[= result | digestBankStep sk candidate call state] *
      secondBankValue sk result.1 result.2 weight) ≤
        secondBankValue sk state.1 state.2 weight + uniformDigestForecast weight +
          2 * cap * digestBankValue sk state.1 state.2 weight := by
  rw [expected_secondBankStep sk candidate call state hrecorded weight]
  split_ifs
  · simpa only [add_zero, add_assoc] using
      (le_self_add : secondBankValue sk state.1 state.2 weight ≤ secondBankValue sk state.1 state.2 weight +
        (uniformDigestForecast weight + 2 * cap * digestBankValue sk state.1 state.2 weight))
  · rw [add_assoc]
    exact add_le_add le_rfl (add_le_add (uniformDigestForecast_square_le weight hbound)
      (mul_le_mul' (mul_le_mul' le_rfl hcap) le_rfl))

noncomputable def secondBankEnvelope (sk : Seeded.SecretKey) (queries : Nat)
    (state : DigestBankState) (weight : MessageDigest → ℝ≥0∞) (cap : ℝ≥0∞) : ℝ≥0∞ :=
  secondBankValue sk state.1 state.2 weight +
    2 * queries * cap * digestBankValue sk state.1 state.2 weight +
      (queries * uniformDigestForecast weight +
        ((queries * (queries - 1) : Nat) : ℝ≥0∞) * cap * uniformDigestForecast weight)

theorem expected_secondBankEnvelope_step (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (state : DigestBankState) (hrecorded : DigestQueriesRecorded sk state.1 state.2)
    (weight : MessageDigest → ℝ≥0∞) (hbound : ∀ digest, weight digest ≤ 1)
    (cap : ℝ≥0∞) (hcap : uniformDigestForecast weight ≤ cap) (queries : Nat) :
    (∑' result, Pr[= result | digestBankStep sk candidate call state] *
      secondBankEnvelope sk queries result weight cap) ≤
        secondBankEnvelope sk (queries + 1) state weight cap := by
  let coefficient : ℝ≥0∞ := 2 * queries * cap
  let constant : ℝ≥0∞ := queries * uniformDigestForecast weight +
    ((queries * (queries - 1) : Nat) : ℝ≥0∞) * cap * uniformDigestForecast weight
  have hlinear : (∑' result, Pr[= result | digestBankStep sk candidate call state] *
      (coefficient * digestBankValue sk result.1 result.2 weight)) ≤
        coefficient * (digestBankValue sk state.1 state.2 weight + uniformDigestForecast weight) := by
    calc
      _ = coefficient * ∑' result, Pr[= result | digestBankStep sk candidate call state] *
          digestBankValue sk result.1 result.2 weight := by
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro result
        ring
      _ ≤ _ := mul_le_mul' le_rfl (expected_digestBankStep_le sk candidate call state hrecorded weight)
  have hconstant : (∑' result, Pr[= result | digestBankStep sk candidate call state] * constant) ≤ constant := by
    rw [ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left' tsum_probOutput_le_one
  change (∑' result, Pr[= result | digestBankStep sk candidate call state] *
    (secondBankValue sk result.1 result.2 weight +
      coefficient * digestBankValue sk result.1 result.2 weight + constant)) ≤ _
  simp only [mul_add, ENNReal.tsum_add]
  refine (add_le_add (add_le_add
    (expected_secondBankStep_le sk candidate call state hrecorded weight hbound cap hcap)
      hlinear) hconstant).trans_eq ?_
  have hpairs : (queries + 1) * ((queries + 1) - 1) = queries * (queries - 1) + 2 * queries := by
    cases queries with
    | zero => rfl
    | succ q => simp only [Nat.succ_sub_one]; ring
  simp only [secondBankEnvelope, hpairs, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    coefficient, constant]
  ring

/-- Fully adaptive two-block target queries obey the localized second-moment envelope.
The chooser may inspect the entire current cache, including either partial digest block. -/
theorem expected_adaptiveSecondBank_le {State : Type} (sk : Seeded.SecretKey)
    (choose : State → DigestBankState → ProbComp (DigestCandidate × Fin 2 × State))
    (weight : MessageDigest → ℝ≥0∞) (hbound : ∀ digest, weight digest ≤ 1)
    (cap : ℝ≥0∞) (hcap : uniformDigestForecast weight ≤ cap) :
    ∀ queries privateState state, DigestQueriesRecorded sk state.1 state.2 →
      (∑' result, Pr[= result | adaptiveDigestBank sk choose queries privateState state] *
        secondBankValue sk result.1 result.2 weight) ≤ secondBankEnvelope sk queries state weight cap := by
  intro queries
  induction queries with
  | zero =>
    intro privateState state _
    simp only [adaptiveDigestBank, tsum_probOutput_pure_mul, secondBankEnvelope,
      Nat.cast_zero, mul_zero, zero_mul, add_zero]
    exact le_rfl
  | succ queries ih =>
    intro privateState state hrecorded
    rw [adaptiveDigestBank]
    apply expected_bind_le_constant
    intro choice _
    refine (expected_bind_le_of_support _ _ _ (fun next => secondBankEnvelope sk queries next weight cap) ?_).trans
      (expected_secondBankEnvelope_step sk choice.1 choice.2.1 state hrecorded weight hbound cap hcap queries)
    intro next hnext
    exact ih choice.2.2 next (digestBankStep_preserves sk choice.1 choice.2.1 state hrecorded next hnext)

/-- Starting with an empty target bank gives the desired diagonal-plus-off-diagonal law:
`q * mean + q*(q-1) * cap * mean`, with no additional factor of the target count. -/
theorem expected_adaptiveSecondBank_empty_le {State : Type} (sk : Seeded.SecretKey)
    (choose : State → DigestBankState → ProbComp (DigestCandidate × Fin 2 × State))
    (weight : MessageDigest → ℝ≥0∞) (hbound : ∀ digest, weight digest ≤ 1)
    (cap : ℝ≥0∞) (hcap : uniformDigestForecast weight ≤ cap) (queries : Nat) (privateState : State)
    (cache : QueryCache HashSpec) (hfresh : DigestQueriesRecorded sk ∅ cache) :
    (∑' result, Pr[= result | adaptiveDigestBank sk choose queries privateState (∅, cache)] *
      secondBankValue sk result.1 result.2 weight) ≤
        queries * uniformDigestForecast weight + ((queries * (queries - 1) : Nat) : ℝ≥0∞) *
          cap * uniformDigestForecast weight := by
  simpa only [secondBankEnvelope, secondBankValue, digestBankValue, Finset.sum_empty, mul_zero,
    zero_add] using expected_adaptiveSecondBank_le sk choose weight hbound cap hcap queries privateState (∅, cache) hfresh

theorem digestForecast_cachedSource (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (digest : MessageDigest) (hcached : CachedSource sk cache candidate digest)
    (weight : MessageDigest → ℝ≥0∞) : digestForecast sk candidate cache weight = weight digest := by
  obtain ⟨first, second, hfirst, hsecond, rfl⟩ := hcached
  simp only [digestForecast, hfirst, hsecond, blockForecast_both]

/-- Once the candidate blocks are resolved, the bank is the actual square of their total
kernel contribution. Thus the preceding adaptive bound is a second moment, not merely a
formal polynomial upper bound on unobserved target values. -/
theorem secondBankValue_resolved (sk : Seeded.SecretKey) (bank : Finset DigestCandidate)
    (cache : QueryCache HashSpec) (digest : DigestCandidate → MessageDigest)
    (hresolved : ∀ candidate ∈ bank, CachedSource sk cache candidate (digest candidate))
    (weight : MessageDigest → ℝ≥0∞) : secondBankValue sk bank cache weight =
      (∑ candidate ∈ bank, weight (digest candidate)) ^ 2 := by
  calc
    _ = ∑ left ∈ bank, ∑ right ∈ bank, weight (digest left) * weight (digest right) := by
      apply Finset.sum_congr rfl
      intro left hleft
      apply Finset.sum_congr rfl
      intro right hright
      by_cases heq : left = right
      · subst right
        simp only [targetSecondForecast, if_true, digestForecast_cachedSource sk left cache _
          (hresolved left hleft), pow_two]
      · simp only [targetSecondForecast, heq, if_false, pairForecast_product,
          digestForecast_cachedSource sk left cache _ (hresolved left hleft),
          digestForecast_cachedSource sk right cache _ (hresolved right hright)]
    _ = _ := by rw [pow_two, Finset.sum_mul]; simp only [Finset.mul_sum]

end LeanSphincs.Lifetime
