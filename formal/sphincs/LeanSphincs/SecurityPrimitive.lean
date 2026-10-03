import LeanSphincs.Uniform

/-!
Adaptive preimage bounds for fresh random-oracle inputs. Targets and inputs may be chosen jointly
from all prior information and private random samples, but they are fixed before the current hash
answer is drawn. Cached trials are explicitly excluded from the monitored event. These are generic
probability bounds, not a reduction from the leanSPHINCS forgery experiment.
-/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.Primitive

/-- A fresh lazy-oracle query hits a previously selected truncated digest with probability 2^-128. -/
theorem fresh_preimage_probability (input : HashInput) (target : Digest)
    (cache : QueryCache HashSpec) (hfresh : cache input = none) :
    Pr[fun result => truncateHash result.1 = target |
      (randomOracle (spec := HashSpec) input).run cache] = (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  rw [QueryImpl.withCaching_run_none uniformSampleImpl hfresh, probEvent_map]
  change Pr[fun output : HashOutput => truncateHash output = target |
    ($ᵗ HashOutput : ProbComp HashOutput)] = _
  rw [probEvent_uniform_truncateHash_eq]
  rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow,
    Nat.cast_ofNat, ENNReal.inv_pow]

/-- Simultaneous preimages for a target set fixed before the fresh draw have its exact density. -/
theorem fresh_targetSet_probability (input : HashInput) (targets : Finset Digest)
    (cache : QueryCache HashSpec) (hfresh : cache input = none) :
    Pr[fun result => truncateHash result.1 ∈ targets |
      (randomOracle (spec := HashSpec) input).run cache] =
        (targets.card : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  rw [QueryImpl.withCaching_run_none uniformSampleImpl hfresh, probEvent_map]
  change Pr[fun output : HashOutput => truncateHash output ∈ targets |
    ($ᵗ HashOutput : ProbComp HashOutput)] = _
  rw [probEvent_uniform_truncateHash_mem]
  rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow,
    Nat.cast_ofNat]

/-- The success event counts only a new oracle answer, never a cache hit. -/
def FreshHit (cache : QueryCache HashSpec) (input : HashInput) (targets : Finset Digest)
    (answer : HashOutput) : Prop := cache input = none ∧ truncateHash answer ∈ targets

instance (cache : QueryCache HashSpec) (input : HashInput) (targets : Finset Digest)
    (answer : HashOutput) : Decidable (FreshHit cache input targets answer) :=
  inferInstanceAs (Decidable (cache input = none ∧ truncateHash answer ∈ targets))

/-- The exact one-query probability includes an explicit zero branch for cached inputs. -/
theorem freshHit_probability (input : HashInput) (targets : Finset Digest)
    (cache : QueryCache HashSpec) :
    Pr[fun result => FreshHit cache input targets result.1 |
      (randomOracle (spec := HashSpec) input).run cache] =
        if cache input = none then (targets.card : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 else 0 := by
  by_cases hfresh : cache input = none
  · simpa only [FreshHit, hfresh, true_and, ↓reduceIte] using
      fresh_targetSet_probability input targets cache hfresh
  · simp only [FreshHit, hfresh, false_and, ↓reduceIte, probEvent_False]

theorem freshHit_probability_le (input : HashInput) (targets : Finset Digest)
    (cache : QueryCache HashSpec) (k : Nat) (hcard : targets.card ≤ k) :
    Pr[fun result => FreshHit cache input targets result.1 |
      (randomOracle (spec := HashSpec) input).run cache] ≤
        (k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  rw [freshHit_probability]
  split
  · exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _
  · exact bot_le

/-- One adaptive query: input and target set are selected before the answer; the continuation
may record every answer and arbitrary private state for subsequent choices. -/
structure Trial (σ : Type) where
  input : HashInput
  targets : Finset Digest
  next : HashOutput → σ

/-- A private randomized strategy sees its state and the complete past cache. Returning `none`
stops early. It cannot access the next hash answer while selecting that query's target set. -/
abbrev Strategy (σ : Type) := σ → QueryCache HashSpec → ProbComp (Option (Trial σ))

/-- Monitor at most `q` adaptive hash queries, stopping as soon as a fresh answer hits its target
set. The actual lazy oracle answers every selected query, including cache hits. -/
noncomputable def monitor {σ : Type} (choose : Strategy σ) :
    Nat → σ → QueryCache HashSpec → ProbComp Bool
  | 0, _, _ => pure false
  | q + 1, state, cache => do
      let some trial ← choose state cache | return false
      let result ← (randomOracle (spec := HashSpec) trial.input).run cache
      if FreshHit cache trial.input trial.targets result.1 then return true
      else monitor choose q (trial.next result.1) result.2

/-- Every target set reachable when a query is selected contains at most `k` digests. -/
def TargetBound {σ : Type} (choose : Strategy σ) (k : Nat) : Prop :=
  ∀ state cache trial, some trial ∈ support (choose state cache) → trial.targets.card ≤ k

/-- Union bound for adaptive, privately randomized queries with up to `k` prior targets each.
Both the next input and the target set can depend on the entire transcript and cache. -/
theorem monitor_bound {σ : Type} (choose : Strategy σ) (k : Nat)
    (hbound : TargetBound choose k) : ∀ (q : Nat) (state : σ) (cache : QueryCache HashSpec),
    Pr[fun hit => hit = true | monitor choose q state cache] ≤
      (q : ℝ≥0∞) * k / (2 : ℝ≥0∞) ^ 128 := by
  intro q
  induction q with
  | zero => intro state cache; simp [monitor]
  | succ q ih =>
      intro state cache
      rw [monitor]
      apply probEvent_bind_le_of_forall_le
      intro selection hselection
      cases selection with
      | none => simp
      | some trial =>
          calc
            _ ≤ Pr[fun result => FreshHit cache trial.input trial.targets result.1 |
                (randomOracle (spec := HashSpec) trial.input).run cache] +
                  (q : ℝ≥0∞) * k / (2 : ℝ≥0∞) ^ 128 := by
              apply probEvent_bind_le_probEvent_add
              intro result _ hnot
              rw [if_neg hnot]
              exact ih _ _
            _ ≤ (k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 +
                (q : ℝ≥0∞) * k / (2 : ℝ≥0∞) ^ 128 :=
              add_le_add (freshHit_probability_le _ _ _ k (hbound _ _ _ hselection)) le_rfl
            _ = ((q + 1 : Nat) : ℝ≥0∞) * k / (2 : ℝ≥0∞) ^ 128 := by
              rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ENNReal.add_div]
              exact add_comm _ _

/-- A single adaptively chosen prior digest per query gives the 128-bit preimage bound. -/
theorem single_target_monitor_bound {σ : Type} (choose : Strategy σ)
    (hbound : TargetBound choose 1) (q : Nat) (state : σ) (cache : QueryCache HashSpec) :
    Pr[fun hit => hit = true | monitor choose q state cache] ≤
      (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  simpa using monitor_bound choose 1 hbound q state cache

/-- Two prior digests per query share one query budget and give the 127-bit bound. -/
theorem two_target_monitor_bound {σ : Type} (choose : Strategy σ)
    (hbound : TargetBound choose 2) (q : Nat) (state : σ) (cache : QueryCache HashSpec) :
    Pr[fun hit => hit = true | monitor choose q state cache] ≤
      (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 127 := by
  have h := monitor_bound choose 2 hbound q state cache
  have hcost : (q : ℝ≥0∞) * 2 / (2 : ℝ≥0∞) ^ 128 =
      (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 127 := by
    rw [show (2 : ℝ≥0∞) ^ 128 = (2 : ℝ≥0∞) ^ 127 * 2 from pow_succ _ _]
    exact ENNReal.mul_div_mul_right _ _ (by norm_num) (by simp)
  simpa only [Nat.cast_ofNat, hcost] using h

/-- The bound also holds when the initial state and cache are jointly sampled or adaptive. -/
theorem initialized_monitor_bound {σ : Type} (choose : Strategy σ) (k : Nat)
    (hbound : TargetBound choose k) (q : Nat) (initial : ProbComp (σ × QueryCache HashSpec)) :
    Pr[fun hit => hit = true | initial >>= fun state => monitor choose q state.1 state.2] ≤
      (q : ℝ≥0∞) * k / (2 : ℝ≥0∞) ^ 128 :=
  probEvent_bind_le_of_forall_le (fun state _ => monitor_bound choose k hbound q state.1 state.2)

end LeanSphincs.Security.Primitive
