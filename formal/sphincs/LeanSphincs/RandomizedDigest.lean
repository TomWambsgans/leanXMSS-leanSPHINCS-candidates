import LeanSphincs.World
import LeanSphincs.Digest

/-! Grinding with truly independent randomizers, including repeated-randomizer cache hits. -/

open OracleComp OracleSpec ENNReal Finset

namespace LeanSphincs.Completeness

open Concrete

variable [Params]

/-- Exact operational law of one randomized grinding trial. The randomizer is sampled for free;
its digest is answered by the same consistent random oracle as all other computations. -/
theorem run_randomizedDigest_succ (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (Randomized.signDigestLoop sk message (n + 1))).run cache =
      ($ᵗ Randomness : ProbComp Randomness) >>= fun ρ =>
        (randomOracle (spec := HashSpec) (msgInput sk message ρ)).run cache >>= fun r =>
          if Landed sk.parameter (blockIndex r.1) then pure (some ρ, r.2)
          else (simulateQ romImpl (Randomized.signDigestLoop sk message n)).run r.2 := by
  rw [Randomized.signDigestLoop, simulateQ_bind, StateT.run_bind, run_lift_prob]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply bind_congr
  intro ρ
  rw [simulateQ_bind, StateT.run_bind, simulate_lift_hash]
  simp only [Seeded.signAttempt, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro r
  split <;> simp [simulateQ_pure, StateT.run_pure]

omit [Params] in
theorem tsum_randomness_ite (P : Randomness → Prop) [DecidablePred P] (x y : ℝ≥0∞) :
    ∑' ρ : Randomness, (Fintype.card Randomness : ℝ≥0∞)⁻¹ * (if P ρ then x else y) =
      x * Pr[P | ($ᵗ Randomness : ProbComp Randomness)] +
        y * Pr[fun ρ => ¬P ρ | ($ᵗ Randomness : ProbComp Randomness)] := by
  rw [probEvent_eq_tsum_ite ($ᵗ Randomness : ProbComp Randomness) P,
    probEvent_eq_tsum_ite ($ᵗ Randomness : ProbComp Randomness) (fun ρ => ¬P ρ),
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun ρ => ?_
  rw [probOutput_uniformSample]
  by_cases h : P ρ <;> simp [h, mul_comm]

omit [Params] in
theorem probEvent_randomness_mem_le (R : Finset Randomness) (hR : R.card ≤ 2 ^ 32) :
    Pr[fun ρ => ρ ∈ R | ($ᵗ Randomness : ProbComp Randomness)] ≤
      (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128 := by
  rw [probEvent_uniformSample, Finset.filter_univ_mem,
    show Fintype.card Randomness = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hcast : (R.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 32 := by exact_mod_cast hR
  exact ENNReal.div_le_div_right hcast _

/-- Uniform randomizers satisfy the same collision-aware bound as fresh seed-derived ones.
The only cache hypothesis concerns digest inputs, not any randomizer derivation domain. -/
theorem probEvent_randomizedDigest (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n t : Nat) (cache : QueryCache HashSpec) (R : Finset Randomness),
      t + n ≤ 2 ^ 32 → R.card ≤ t →
      (∀ ρ, ρ ∉ R → cache (msgInput sk message ρ) = none) →
      Pr[fun r => r.1 = none |
        (simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache]
      ≤ digestFactor sk.parameter ^ n := by
  intro n
  induction n with
  | zero => intro t cache R _ _ _; simp [Randomized.signDigestLoop]
  | succ n ih =>
      intro t cache R hbound hcard hmsg
      rw [run_randomizedDigest_succ, probEvent_bind_eq_tsum]
      simp only [probOutput_uniformSample]
      refine (ENNReal.tsum_le_tsum (g := fun ρ => (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
        (if ρ ∈ R then digestFactor sk.parameter ^ n
          else digestReject sk.parameter * digestFactor sk.parameter ^ n))
        fun ρ => mul_le_mul_right ?_ _).trans ?_
      · cases hc : cache (msgInput sk message ρ) with
        | some answer =>
            have hρ : ρ ∈ R := by
              by_contra hnot
              have := hmsg ρ hnot
              simp [hc] at this
            rw [if_pos hρ, cached_run _ _ _ hc, pure_bind]
            split
            · simp
            · exact ih (t + 1) cache R (by omega) (by omega) hmsg
        | none =>
            rw [fresh_run _ _ hc]
            refine (ENNReal.tsum_le_tsum (g := fun answer => (Fintype.card HashOutput : ℝ≥0∞)⁻¹ *
              (if Landed sk.parameter (blockIndex answer) then 0
                else digestFactor sk.parameter ^ n))
              fun answer => mul_le_mul_right ?_ _).trans ?_
            · split
              · simp
              · refine ih (t + 1) _ (insert ρ R) (by omega)
                  ((Finset.card_insert_le _ _).trans (by omega)) ?_
                intro ρ' hρ'
                rw [Finset.mem_insert, not_or] at hρ'
                exact (QueryCache.cacheQuery_of_ne cache answer
                  (fun h => hρ'.1 (msgInput_inj sk message h))).trans (hmsg ρ' hρ'.2)
            · rw [tsum_uniform_ite]
              simp only [zero_mul, zero_add]
              change digestFactor sk.parameter ^ n * digestReject sk.parameter ≤ _
              by_cases hρ : ρ ∈ R
              · rw [if_pos hρ]
                exact mul_le_of_le_one_right' (digestReject_le_one sk.parameter)
              · rw [if_neg hρ, mul_comm]
      · rw [tsum_randomness_ite]
        have hcoll := probEvent_randomness_mem_le R (by omega)
        calc
          _ ≤ digestFactor sk.parameter ^ n * ((2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128) +
            digestReject sk.parameter * digestFactor sk.parameter ^ n * 1 :=
              add_le_add (mul_le_mul_right hcoll _) (mul_le_mul_right probEvent_le_one _)
          _ = digestFactor sk.parameter ^ (n + 1) := by
            have hF : digestFactor sk.parameter = digestReject sk.parameter +
                (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128 := rfl
            generalize (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128 = C at hF ⊢
            rw [pow_succ, hF]
            ring

/-- The requested independently randomized grinding loop exhausts its full budget with
probability at most `2^(-2^(b+5))` from a cache with no message-digest inputs. -/
theorem randomized_digest_exhaustion_bound (sk : Seeded.SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfresh : ∀ ρ, cache (msgInput sk message ρ) = none) :
    Pr[fun r => r.1 = none |
      (simulateQ romImpl (Randomized.signDigestLoop sk message digestAttemptLimit)).run cache]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) := by
  exact (probEvent_randomizedDigest sk message digestAttemptLimit 0 cache ∅
    (by simp [digestAttemptLimit]) (by simp) (fun ρ _ => hfresh ρ)).trans
    (digestFactor_pow_bound sk.parameter)

end LeanSphincs.Completeness
