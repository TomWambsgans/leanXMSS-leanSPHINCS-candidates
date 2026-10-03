import LeanSphincs.LifetimePairForecast

/-! Exact finite randomizer-pool balance. Prequeried sources replace a portion of the fresh
pool; adding their contribution while charging a full fresh pool double-counts that portion.
The balanced equality below retains this cancellation before any concentration estimate.
It is valid with first-only, second-only, or completely cached message digests. -/

namespace LeanSphincs.Lifetime

set_option maxRecDepth 2048

open OracleComp OracleSpec ENNReal Concrete Completeness

attribute [local instance] Classical.propDecidable

noncomputable def messageRandomizers (bank : Finset DigestCandidate) (message : Message) : Finset Randomness :=
  Finset.univ.filter (fun randomness => (message, randomness) ∈ bank)

theorem mem_messageRandomizers (bank : Finset DigestCandidate) (message : Message) (randomness : Randomness) :
    randomness ∈ messageRandomizers bank message ↔ (message, randomness) ∈ bank := by
  simp only [messageRandomizers, Finset.mem_filter, Finset.mem_univ, true_and]

theorem randomizer_forecast_sum_split (sk : Seeded.SecretKey) (message : Message)
    (bank : Finset DigestCandidate) (cache : QueryCache HashSpec)
    (hrecorded : DigestQueriesRecorded sk bank cache) (weight : MessageDigest → ℝ≥0∞) :
    (∑ randomness : Randomness, digestForecast sk (message, randomness) cache weight) =
      (∑ randomness ∈ messageRandomizers bank message, digestForecast sk (message, randomness) cache weight) +
        ((messageRandomizers bank message)ᶜ.card : ℝ≥0∞) * uniformDigestForecast weight := by
  rw [← Finset.sum_add_sum_compl (messageRandomizers bank message)
    (fun randomness => digestForecast sk (message, randomness) cache weight)]
  apply congrArg (fun value =>
    (∑ randomness ∈ messageRandomizers bank message, digestForecast sk (message, randomness) cache weight) + value)
  calc
    _ = ∑ _randomness ∈ (messageRandomizers bank message)ᶜ, uniformDigestForecast weight := by
      apply Finset.sum_congr rfl
      intro randomness hmem
      have hnot : (message, randomness) ∉ bank := by
        simpa only [Finset.mem_compl, mem_messageRandomizers] using hmem
      exact fresh_digestForecast_uniform sk (message, randomness) cache weight
        (hrecorded (message, randomness) hnot)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Exact fresh-plus-cached decomposition, without replacing the fresh pool's mass by one. -/
theorem randomizerAverage_forecast_split (sk : Seeded.SecretKey) (message : Message)
    (bank : Finset DigestCandidate) (cache : QueryCache HashSpec)
    (hrecorded : DigestQueriesRecorded sk bank cache) (weight : MessageDigest → ℝ≥0∞) :
    randomizerAverage (fun randomness => digestForecast sk (message, randomness) cache weight) =
      (((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ * ((messageRandomizers bank message)ᶜ.card : ℝ≥0∞)) *
        uniformDigestForecast weight +
      ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ *
        ∑ randomness ∈ messageRandomizers bank message, digestForecast sk (message, randomness) cache weight := by
  rw [randomizerAverage_card, randomizer_forecast_sum_split sk message bank cache hrecorded weight]
  ring

/-- A subtraction-free exact cancellation identity. A centered fluctuation bound must
compare the cached sum to `cachedCount * uniformPrice`; its mean is already paid by the
fresh mass it replaced, so charging it again introduces an artificial query-count inflation. -/
theorem randomizerAverage_forecast_balance (sk : Seeded.SecretKey) (message : Message)
    (bank : Finset DigestCandidate) (cache : QueryCache HashSpec)
    (hrecorded : DigestQueriesRecorded sk bank cache) (weight : MessageDigest → ℝ≥0∞) :
    ((2 ^ 128 : Nat) : ℝ≥0∞) *
        randomizerAverage (fun randomness => digestForecast sk (message, randomness) cache weight) +
      ((messageRandomizers bank message).card : ℝ≥0∞) * uniformDigestForecast weight =
        ((2 ^ 128 : Nat) : ℝ≥0∞) * uniformDigestForecast weight +
          ∑ randomness ∈ messageRandomizers bank message, digestForecast sk (message, randomness) cache weight := by
  rw [randomizerAverage_card, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul,
    randomizer_forecast_sum_split sk message bank cache hrecorded weight]
  have hcard : ((messageRandomizers bank message)ᶜ.card : ℝ≥0∞) +
      ((messageRandomizers bank message).card : ℝ≥0∞) = ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    rw [← Nat.cast_add, Finset.card_compl_add_card]
    simp only [Randomness, digestBits, card_bitVec]
  calc
    _ = (((messageRandomizers bank message)ᶜ.card : ℝ≥0∞) +
        ((messageRandomizers bank message).card : ℝ≥0∞)) * uniformDigestForecast weight +
          ∑ randomness ∈ messageRandomizers bank message, digestForecast sk (message, randomness) cache weight := by ring
    _ = _ := by rw [hcard]

end LeanSphincs.Lifetime
