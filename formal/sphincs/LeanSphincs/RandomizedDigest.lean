import LeanSphincs.World
import LeanSphincs.Digest

/-! Grinding with truly independent randomizers, including repeated-randomizer cache hits. -/

open OracleComp OracleSpec ENNReal Finset

namespace LeanSphincs.Completeness

open Concrete

variable [Params]

/-- Exact operational law of one grinding trial of the walk. -/
theorem run_walk_succ (sk : Seeded.SecretKey) (message : Message) (step : Randomness) (n : Nat)
    (ρ : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle (Seeded.signDigestLoop sk message step (n + 1) ρ :
        OracleComp HashSpec (Option (Randomness × Index)))).run cache =
      (randomOracle (spec := HashSpec) (msgInput sk message ρ)).run cache >>= fun r =>
        if Landed sk.parameter (blockIndex r.1) then pure (some (ρ, blockIndex r.1), r.2)
        else (simulateQ randomOracle (Seeded.signDigestLoop sk message step n (ρ + step) :
          OracleComp HashSpec (Option (Randomness × Index)))).run r.2 := by
  rw [Seeded.signDigestLoop]
  simp only [Seeded.signAttempt, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro r
  split <;> simp [simulateQ_pure, StateT.run_pure]

omit [Params] in
/-- The randomizers of a walk with an odd step are distinct below the wrap. -/
theorem add_ofNat_ne (half ρ : Randomness) {j : Nat} (hj : j + 1 < 2 ^ 128) :
    ρ + walkStep half + BitVec.ofNat digestBits j * walkStep half ≠ ρ := by
  have h := walk_iterate_ne half ρ j hj
  rwa [walk_iterate, BitVec.natCast_eq_ofNat] at h

omit [Params] in
theorem add_ofNat_succ (step ρ : Randomness) (j : Nat) :
    ρ + BitVec.ofNat digestBits (j + 1) * step = ρ + step + BitVec.ofNat digestBits j * step := by
  rw [← BitVec.natCast_eq_ofNat, ← BitVec.natCast_eq_ofNat]
  push_cast
  ring

/-- The walk from a randomizer whose next `n` digest inputs are fresh fails with probability at
most the `n`-th power of the rejection share: its trials are distinct, hence independent. -/
theorem probEvent_walk (sk : Seeded.SecretKey) (message : Message) (half : Randomness) :
    ∀ (n : Nat) (ρ : Randomness) (cache : QueryCache HashSpec), n < 2 ^ 128 →
      (∀ j, j < n → cache (msgInput sk message (ρ + BitVec.ofNat digestBits j * walkStep half)) = none) →
      Pr[fun r => r.1 = none |
        (simulateQ randomOracle (Seeded.signDigestLoop sk message (walkStep half) n ρ :
          OracleComp HashSpec (Option (Randomness × Index)))).run cache]
      ≤ digestReject sk.parameter ^ n := by
  intro n
  induction n with
  | zero => intro ρ cache _ _; simp [Seeded.signDigestLoop]
  | succ n ih =>
      intro ρ cache hn hfresh
      have h0 : cache (msgInput sk message ρ) = none := by
        have := hfresh 0 (Nat.succ_pos n)
        rwa [BitVec.zero_mul, BitVec.add_zero] at this
      rw [run_walk_succ, fresh_run _ _ h0]
      refine (ENNReal.tsum_le_tsum (g := fun answer => (Fintype.card HashOutput : ℝ≥0∞)⁻¹ *
        (if Landed sk.parameter (blockIndex answer) then 0 else digestReject sk.parameter ^ n))
        fun answer => mul_le_mul_right ?_ _).trans ?_
      · split
        · simp
        · refine ih (ρ + walkStep half) _ (by omega) ?_
          intro j hj
          show cache.cacheQuery (msgInput sk message ρ) answer
            (msgInput sk message (ρ + walkStep half + BitVec.ofNat digestBits j * walkStep half)) = none
          rw [QueryCache.cacheQuery_of_ne cache answer
            (fun h => add_ofNat_ne half ρ (by omega : j + 1 < 2 ^ 128) (msgInput_inj sk message h)),
            ← add_ofNat_succ]
          exact hfresh (j + 1) (by omega)
      · rw [tsum_uniform_ite]
        simp only [zero_mul, zero_add]
        change digestReject sk.parameter ^ n * digestReject sk.parameter ≤ _
        rw [pow_succ]

/-- The randomized loop is the walk from a uniform base randomizer with a uniform step half. -/
theorem run_randomizedDigest (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache =
      ($ᵗ Randomness : ProbComp Randomness) >>= fun base =>
        ($ᵗ Randomness : ProbComp Randomness) >>= fun half =>
          (simulateQ randomOracle (Seeded.signDigestLoop sk message (walkStep half) n base :
            OracleComp HashSpec (Option (Randomness × Index)))).run cache >>= fun x =>
              pure (Option.map Prod.fst x.1, x.2) := by
  rw [Randomized.signDigestLoop, simulateQ_bind, StateT.run_bind, run_lift_prob]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun base => ?_
  rw [simulateQ_bind, StateT.run_bind, run_lift_prob]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  refine bind_congr fun half => ?_
  rw [simulateQ_bind, StateT.run_bind, simulate_lift_hash]
  simp only [simulateQ_pure, StateT.run_pure]

theorem digestReject_le_digestFactor (parameter : PublicParameter) :
    digestReject parameter ≤ digestFactor parameter := le_self_add

omit [Params] in
theorem probEvent_none_map_fst (X : ProbComp (Option (Randomness × Index) × QueryCache HashSpec)) :
    Pr[fun r => r.1 = none | X >>= fun x => pure (Option.map Prod.fst x.1, x.2)] =
      Pr[fun r => r.1 = none | X] := by
  rw [show (X >>= fun x => pure (Option.map Prod.fst x.1, x.2)) =
    (fun x : Option (Randomness × Index) × QueryCache HashSpec =>
      (Option.map Prod.fst x.1, x.2)) <$> X from (map_eq_bind_pure_comp _ _ _).symm, probEvent_map]
  congr 1
  funext r
  simp [Function.comp]

/-- The grinding loop from a uniform base randomizer exhausts its full budget with probability at
most `2^(-2^(b+5))` from a cache with no message-digest inputs. -/
theorem randomized_digest_exhaustion_bound (sk : Seeded.SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfresh : ∀ ρ, cache (msgInput sk message ρ) = none) :
    Pr[fun r => r.1 = none |
      (simulateQ romImpl (Randomized.signDigestLoop sk message digestAttemptLimit)).run cache]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) := by
  have hloop : ∀ half base : Randomness,
      Pr[fun r => r.1 = none |
        (simulateQ randomOracle (Seeded.signDigestLoop sk message (walkStep half) digestAttemptLimit base :
          OracleComp HashSpec (Option (Randomness × Index)))).run cache]
        ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) := fun half base =>
    (probEvent_walk sk message half digestAttemptLimit base cache
      (by simp [digestAttemptLimit]) (fun j _ => hfresh _)).trans
      ((pow_le_pow_left₀ (by positivity) (digestReject_le_digestFactor sk.parameter) _).trans
        (digestFactor_pow_bound sk.parameter))
  rw [run_randomizedDigest, probEvent_bind_eq_tsum]
  calc _ ≤ ∑' base : Randomness, Pr[= base | ($ᵗ Randomness : ProbComp Randomness)] *
          (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) := by
        refine ENNReal.tsum_le_tsum fun base => mul_le_mul_right ?_ _
        rw [probEvent_bind_eq_tsum]
        calc _ ≤ ∑' half : Randomness, Pr[= half | ($ᵗ Randomness : ProbComp Randomness)] *
              (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) := by
              refine ENNReal.tsum_le_tsum fun half => mul_le_mul_right ?_ _
              rw [probEvent_none_map_fst]
              exact hloop half base
          _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]

end LeanSphincs.Completeness
