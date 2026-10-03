import LeanSphincs.LifetimePoolPreparation
import LeanSphincs.LifetimeAdaptiveOccupancy
import LeanSphincs.LifetimeVarianceBudget

/-! Position-count localization for a common adaptive disclosure trace. The transition may
switch from actual private grinding to independent uniform draws at any deterministic point;
the same conditional index bound is sufficient. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness
set_option exponentiation.threshold 1024

noncomputable def adaptiveIndexTrace {State : Type}
    (step : Nat → State → ProbComp (Option Index × State)) : Nat → State → ProbComp (List (Option Index))
  | 0, _ => pure []
  | n + 1, state => do
      let next ← step n state
      let rest ← adaptiveIndexTrace step n next.2
      return next.1 :: rest

noncomputable def indexHitStep {State : Type}
    (step : Nat → State → ProbComp (Option Index × State)) (index : Index)
    (n : Nat) (state : State) : ProbComp (Bool × State) :=
  (fun next => (decide (next.1 = some index), next.2)) <$> step n state

theorem indexHitStep_probability {State : Type}
    (step : Nat → State → ProbComp (Option Index × State)) (index : Index)
    (n : Nat) (state : State) :
    Pr[fun next => next.1 | indexHitStep step index n state] =
      Pr[fun next => next.1 = some index | step n state] := by
  simp only [indexHitStep, probEvent_map, Function.comp_def, decide_eq_true_eq]

theorem adaptiveIndexTrace_count {State : Type}
    (step : Nat → State → ProbComp (Option Index × State)) (index : Index)
    (n : Nat) (state : State) :
    (fun trace => trace.count (some index)) <$> adaptiveIndexTrace step n state =
      adaptiveHitCount (indexHitStep step index) n state := by
  induction n generalizing state with
  | zero => simp [adaptiveIndexTrace, adaptiveHitCount]
  | succ n ih =>
      simp only [adaptiveIndexTrace, adaptiveHitCount, indexHitStep, map_bind, map_pure,
        bind_map_left]
      apply bind_congr
      intro next
      rw [← ih]
      simp only [bind_pure_comp, Functor.map_map]
      congr 1
      funext rest
      simp only [Function.comp_def, List.count_cons, beq_iff_eq, decide_eq_true_eq]

theorem adaptiveIndexTrace_tail {State : Type}
    (step : Nat → State → ProbComp (Option Index × State))
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hstep : ∀ n state index, Pr[fun next => next.1 = some index | step n state] ≤ ENNReal.ofReal rate)
    (n : Nat) (hmean : (n : ℝ) * rate ≤ 32) (state : State) :
    Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) | adaptiveIndexTrace step n state] ≤
      1 / (2 : ℝ≥0∞) ^ 294 := by
  apply global_occupancy_tail
  intro index
  have h := adaptiveHitCount_tail_256 (indexHitStep step index) rate hrate
    (fun n state => (indexHitStep_probability step index n state).trans_le (hstep n state index))
    n hmean state
  rw [← adaptiveIndexTrace_count] at h
  simpa only [probEvent_map, Function.comp_def] using h

theorem requested_pool_occupancy_mean {b n : Nat} (hpair : (b, n) ∈ requestedLifetimePairs) :
    (n : ℝ) * ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ b) ≤ 32 := by
  simp only [requestedLifetimePairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- All six exact lifetimes fit the same position-count localization bound. -/
theorem requested_adaptive_occupancy_tail {State : Type}
    (step : Nat → State → ProbComp (Option Index × State)) {b n : Nat}
    (hpair : (b, n) ∈ requestedLifetimePairs)
    (hstep : ∀ remaining state index,
      Pr[fun next => next.1 = some index | step remaining state] ≤
        ENNReal.ofReal ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ b)) (state : State) :
    Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) | adaptiveIndexTrace step n state] ≤
      1 / (2 : ℝ≥0∞) ^ 294 :=
  adaptiveIndexTrace_tail step _ (by positivity) hstep n (requested_pool_occupancy_mean hpair) state

end LeanSphincs.Lifetime
