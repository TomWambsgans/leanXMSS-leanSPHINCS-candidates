import LeanSphincs.LifetimeFullViewTrace

/-! Factoring the localized hybrid at its switch: a complete actual signing past followed
by `uniformDisclosureSet`. The resulting bound is exactly the expected futureOverflow term. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable [Params]

def discloseFullView (prior : Finset KeptDigestView) (view : Option FullDigestView) : Finset KeptDigestView :=
  match view with
  | none => prior
  | some value => insert (localFullView value) prior

noncomputable def fullViewDisclosure {State : Type}
    (step : Nat → State → ProbComp (Option FullDigestView × State)) :
    Nat → State → Finset KeptDigestView → ProbComp (Finset KeptDigestView)
  | 0, _, prior => pure prior
  | n + 1, state, prior => do
      let next ← step n state
      fullViewDisclosure step n next.2 (discloseFullView prior next.1)

/-- Full view traces and the accumulated disclosure set are exactly the same experiment. -/
theorem fullViewDisclosure_eq_trace {State : Type}
    (step : Nat → State → ProbComp (Option FullDigestView × State))
    (n : Nat) (state : State) (prior : Finset KeptDigestView) :
    fullViewDisclosure step n state prior =
      (fun trace => (fullViewLocals trace).toFinset ∪ prior) <$> fullViewTrace step n state := by
  induction n generalizing state prior with
  | zero => simp only [fullViewDisclosure, fullViewTrace, map_pure, fullViewLocals,
      List.filterMap_nil, List.toFinset_nil, Finset.empty_union]
  | succ n ih =>
      simp only [fullViewDisclosure, fullViewTrace, map_bind, map_pure]
      apply bind_congr
      intro next
      rw [ih]
      simp only [bind_pure_comp]
      congr 1
      funext rest
      cases hnext : next.1 with
      | none => simp only [hnext, discloseFullView, fullViewLocals, List.filterMap_cons, Option.map_none]
      | some view =>
          simp only [hnext, discloseFullView, fullViewLocals, List.filterMap_cons, Option.map_some, List.toFinset_cons]
          ext value
          simp only [Finset.mem_union, Finset.mem_insert]
          tauto

theorem fullViewDisclosure_ideal_suffix {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (suffix n : Nat) (hn : n ≤ suffix)
    (state : State × QueryCache HashSpec) (prior : Finset KeptDigestView) :
    fullViewDisclosure (fullViewStep sk interlude update (fun remaining => decide (suffix ≤ remaining)))
      n state prior = uniformDisclosureSet n prior := by
  induction n generalizing state prior with
  | zero => exact (uniformDisclosureSet_zero prior).symm
  | succ n ih =>
      have hfalse : ¬suffix ≤ n := by omega
      rw [fullViewDisclosure, fullViewStep, if_neg (by simpa only [decide_eq_true_eq] using hfalse),
        bind_map_left, uniformDisclosureSet_succ]
      apply bind_congr
      intro view
      rw [ih (by omega)]
      simp only [discloseFullView, local_keptView]

/-- Actual past transitions retain private state, actual signature responses, full accepted
views and the shared ROM cache. The transition number includes the independent suffix size. -/
noncomputable def acceptedPrefix {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (suffix : Nat) :
    Nat → (State × QueryCache HashSpec) → Finset KeptDigestView → ProbComp (Finset KeptDigestView)
  | 0, _, prior => pure prior
  | n + 1, state, prior => do
      let next ← fullViewStep sk interlude update (fun _ => true) (n + suffix) state
      acceptedPrefix sk interlude update suffix n next.2 (discloseFullView prior next.1)

/-- The independent tail factors after the actual past, preserving its entire prior. -/
theorem fullViewDisclosure_prefix_suffix {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (suffix past : Nat)
    (state : State × QueryCache HashSpec) (prior : Finset KeptDigestView) :
    fullViewDisclosure (fullViewStep sk interlude update (fun remaining => decide (suffix ≤ remaining)))
      (past + suffix) state prior =
        acceptedPrefix sk interlude update suffix past state prior >>= uniformDisclosureSet suffix := by
  induction past generalizing state prior with
  | zero =>
      simp only [Nat.zero_add, acceptedPrefix, pure_bind]
      exact fullViewDisclosure_ideal_suffix sk interlude update suffix suffix le_rfl state prior
  | succ past ih =>
      rw [Nat.succ_add, fullViewDisclosure, acceptedPrefix, bind_assoc]
      have hstep : fullViewStep sk interlude update (fun remaining => decide (suffix ≤ remaining)) (past + suffix) state =
          fullViewStep sk interlude update (fun _ => true) (past + suffix) state := by
        simp only [fullViewStep, Nat.le_add_left, decide_true, ↓reduceIte]
      rw [hstep]
      apply bind_congr
      intro next
      exact ih next.2 (discloseFullView prior next.1)

/-- This is the overflow expectation required by the future-coverage localization. -/
theorem expected_futureOverflow_actual_prefix {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (suffix past : Nat)
    (hpair : (subtreeHeight, past + suffix) ∈ requestedLifetimePairs) (state : State) :
    (∑' prior, Pr[= prior | acceptedPrefix sk interlude update suffix past (state, ∅) ∅] *
      futureOverflow suffix prior) ≤ 1 / (2 : ℝ≥0∞) ^ 400 + 1 / 2 ^ 294 := by
  have h := actual_hybrid_view_overflow sk interlude update (fun remaining => decide (suffix ≤ remaining))
    (past + suffix) hpair state
  rw [show (fun trace => ¬ViewCap 255 (fullViewLocals trace).toFinset) =
      (fun views => ¬ViewCap 255 views) ∘ (fun trace => (fullViewLocals trace).toFinset ∪ ∅) by
        funext trace; rw [Function.comp_apply, Finset.union_empty],
    ← probEvent_map, ← fullViewDisclosure_eq_trace, fullViewDisclosure_prefix_suffix,
    probEvent_bind_eq_tsum] at h
  exact h

/-- Sum every actual-past futureOverflow term, keeping the exact requested total lifetime. -/
theorem expected_futureOverflow_all_prefixes {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State) :
    (∑ suffix : Fin (n + 1), ∑' prior,
      Pr[= prior | acceptedPrefix sk interlude update suffix.val (n - suffix.val) (state, ∅) ∅] *
        futureOverflow suffix.val prior) ≤ 1 / (2 : ℝ≥0∞) ^ 263 := by
  calc
    _ ≤ ∑ _suffix : Fin (n + 1), ((1 : ℝ≥0∞) / 2 ^ 400 + 1 / 2 ^ 294) := by
      apply Finset.sum_le_sum
      intro suffix _
      apply expected_futureOverflow_actual_prefix sk interlude update suffix.val (n - suffix.val) _ state
      have hs : suffix.val ≤ n := by omega
      simpa only [Nat.sub_add_cancel hs] using hpair
    _ = ((n + 1 : Nat) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 400 + 1 / 2 ^ 294) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := requested_hybrid_union_budget hpair

end LeanSphincs.Lifetime
