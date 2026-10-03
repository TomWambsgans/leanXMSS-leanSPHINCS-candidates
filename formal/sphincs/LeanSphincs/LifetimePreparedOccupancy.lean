import LeanSphincs.LifetimePreparedSigning

/-! Adaptive occupancy for complete actual signing calls with arbitrary private/random-oracle
interleaving between requests. A cache invariant suffices; selectors need not be independent. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

noncomputable def guardedIndexStep {State : Type} (invariant : State → Prop)
    (step : Nat → State → ProbComp (Option Index × State)) (n : Nat) (state : State) :
    ProbComp (Option Index × State) :=
  @ite _ (invariant state) (Classical.propDecidable _) (step n state) (pure (none, state))

theorem adaptiveIndexTrace_guarded {State : Type} (invariant : State → Prop)
    (step : Nat → State → ProbComp (Option Index × State))
    (hpreserve : ∀ n state, invariant state → ∀ result ∈ support (step n state), invariant result.2)
    (n : Nat) (state : State) (hstate : invariant state) :
    adaptiveIndexTrace (guardedIndexStep invariant step) n state = adaptiveIndexTrace step n state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [adaptiveIndexTrace, guardedIndexStep, if_pos hstate]
      apply bind_congr_of_forall_mem_support
      intro result hresult
      rw [ih result.2 (hpreserve n state hstate result hresult)]

theorem adaptiveIndexTrace_tail_of_invariant {State : Type} (invariant : State → Prop)
    (step : Nat → State → ProbComp (Option Index × State))
    (hpreserve : ∀ n state, invariant state → ∀ result ∈ support (step n state), invariant result.2)
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hstep : ∀ n state, invariant state → ∀ index,
      Pr[fun result => result.1 = some index | step n state] ≤ ENNReal.ofReal rate)
    (n : Nat) (hmean : (n : ℝ) * rate ≤ 32) (state : State) (hstate : invariant state) :
    Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) | adaptiveIndexTrace step n state] ≤
      1 / (2 : ℝ≥0∞) ^ 294 := by
  rw [← adaptiveIndexTrace_guarded invariant step hpreserve n state hstate]
  apply adaptiveIndexTrace_tail _ rate hrate _ n hmean state
  intro remaining current index
  by_cases hcurrent : invariant current
  · rw [guardedIndexStep, if_pos hcurrent]
    exact hstep remaining current hcurrent index
  · rw [guardedIndexStep, if_neg hcurrent]
    simp only [probEvent_pure, reduceCtorEq, if_false]
    exact bot_le

variable [Params]

/-- An arbitrary actual-world interlude selects the next message and private state, followed
by the complete actual signer. Only a proof-side accepted-index field is added. -/
noncomputable def interleavedIndexStep {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State)
    (n : Nat) (state : State × QueryCache HashSpec) : ProbComp (Option Index × (State × QueryCache HashSpec)) := do
  let request ← (simulateQ romImpl (interlude n state.1)).run state.2
  let signed ← indexedSign sk request.1.1 request.2
  pure (signed.1, update request.1.2 signed.2.1, signed.2.2)

/-- Dropping the index field leaves the actual interlude and actual randomized signing call. -/
theorem interleavedIndexStep_erase {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat) (state : State × QueryCache HashSpec) :
    Prod.snd <$> interleavedIndexStep sk interlude update n state = (do
      let request ← (simulateQ romImpl (interlude n state.1)).run state.2
      let signed ← (simulateQ romImpl (Randomized.sign sk request.1.1)).run request.2
      pure (update request.1.2 signed.1, signed.2)) := by
  simp only [interleavedIndexStep, map_bind, map_pure]
  apply bind_congr
  intro request
  rw [← indexedSign_erase, bind_map_left]

theorem interleavedIndexStep_cache_le {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat) (state : State × QueryCache HashSpec)
    (result : Option Index × (State × QueryCache HashSpec))
    (hresult : result ∈ support (interleavedIndexStep sk interlude update n state)) : state.2 ≤ result.2.2 := by
  simp only [interleavedIndexStep, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨request, hrequest, signed, hsigned, rfl⟩ := hresult
  exact (world_support_cache_le _ _ _ _ hrequest).trans (indexedSign_cache_le _ _ _ _ hsigned)

theorem interleavedIndexStep_prepared_bound {State : Type} (table : FirstPoolTable)
    (hbalanced : AllPoolsBalanced (firstPoolIndexes table)) (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat) (state : State × QueryCache HashSpec)
    (hcache : firstPoolCache table ≤ state.2) (index : Index) :
    Pr[fun result => result.1 = some index | interleavedIndexStep sk interlude update n state] ≤
      ENNReal.ofReal ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ subtreeHeight) := by
  rw [interleavedIndexStep, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' request, Pr[= request | (simulateQ romImpl (interlude n state.1)).run state.2] *
        ENNReal.ofReal ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ subtreeHeight) := by
      apply ENNReal.tsum_le_tsum
      intro request
      by_cases hrequest : request ∈ support ((simulateQ romImpl (interlude n state.1)).run state.2)
      · apply mul_le_mul_right
        simp only [bind_pure_comp, probEvent_map, Function.comp_def]
        exact indexedSign_prepared_bound table hbalanced sk request.1.1 request.2
          (hcache.trans (world_support_cache_le _ _ _ _ hrequest)) index
      · rw [probOutput_eq_zero_of_not_mem_support hrequest, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

/-- All six requested lifetimes have fewer than256 accepted positions at every leaf except
with probability2^-294, even with arbitrary intervening oracle computations. -/
theorem interleaved_signing_occupancy {State : Type} (table : FirstPoolTable)
    (hbalanced : AllPoolsBalanced (firstPoolIndexes table)) (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State × QueryCache HashSpec)
    (hcache : firstPoolCache table ≤ state.2) :
    Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) |
      adaptiveIndexTrace (interleavedIndexStep sk interlude update) n state] ≤ 1 / (2 : ℝ≥0∞) ^ 294 := by
  apply adaptiveIndexTrace_tail_of_invariant (fun state : State × QueryCache HashSpec => firstPoolCache table ≤ state.2)
    (interleavedIndexStep sk interlude update)
    (fun remaining current hcurrent result hresult => hcurrent.trans
      (interleavedIndexStep_cache_le sk interlude update remaining current result hresult))
    ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ subtreeHeight) (by positivity)
    (fun remaining current hcurrent index =>
      interleavedIndexStep_prepared_bound table hbalanced sk interlude update remaining current hcurrent index)
    n (requested_pool_occupancy_mean hpair) state hcache

end LeanSphincs.Lifetime
