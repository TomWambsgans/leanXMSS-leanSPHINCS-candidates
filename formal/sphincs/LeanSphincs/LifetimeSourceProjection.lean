import LeanSphincs.LifetimeFutureOverflow

/-! The occupancy observer and the existing source-record process have exactly the same
accepted disclosure history, including the record made before a WOTS exhaustion. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable [Params]

theorem viewedSign_disclosures (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec) :
    (fun result => (result.2.1, discloseFullView prior result.1, result.2.2)) <$>
      viewedSign sk message cache = signWithDisclosures sk message (prior, cache) := by
  simp only [viewedSign, signWithSources, signWithDisclosures, Functor.map_map, map_bind]
  apply bind_congr
  rintro ⟨loop, middle⟩
  cases loop with
  | none => rfl
  | some rho =>
      simp only [map_bind, map_pure]
      rfl

/-- Full source-record histories project to the very same accumulated view transition. -/
theorem signWithSources_viewedSign (sk : Seeded.SecretKey) (message : Message)
    (records : List SourceRecord) (cache : QueryCache HashSpec) :
    (fun result => (result.1, sourcedPrior result.2.1, result.2.2)) <$>
      signWithSources sk message (records, cache) =
      (fun result => (result.2.1, discloseFullView (sourcedPrior records) result.1, result.2.2)) <$>
        viewedSign sk message cache := by
  rw [viewedSign_disclosures]
  exact signWithSources_forget_sources sk message (records, cache)

noncomputable def sourceInterleavedStep {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat)
    (state : State × SourcedState) : ProbComp (State × SourcedState) := do
  let request ← (simulateQ romImpl (interlude n state.1)).run state.2.2
  let signed ← signWithSources sk request.1.1 (state.2.1, request.2)
  pure (update request.1.2 signed.1, signed.2)

theorem sourceInterleavedStep_views {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat) (state : State × SourcedState) :
    (fun result => (result.1, sourcedPrior result.2.1, result.2.2)) <$>
      sourceInterleavedStep sk interlude update n state =
      (fun result => (result.2.1, discloseFullView (sourcedPrior state.2.1) result.1, result.2.2)) <$>
        fullViewStep sk interlude update (fun _ => true) n (state.1, state.2.2) := by
  simp only [sourceInterleavedStep, fullViewStep, ↓reduceIte, map_bind, map_pure]
  apply bind_congr
  intro request
  have h := congrArg (Functor.map (fun result : Option Signature × Finset KeptDigestView × QueryCache HashSpec =>
      (update request.1.2 result.1, result.2.1, result.2.2)))
    (signWithSources_viewedSign sk request.1.1 state.2.1 request.2)
  simpa only [Functor.map_map, Function.comp_def, bind_pure_comp] using h

noncomputable def sourcePrefix {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (suffix : Nat) : Nat → (State × SourcedState) → ProbComp (State × SourcedState)
  | 0, state => pure state
  | n + 1, state => do
      let next ← sourceInterleavedStep sk interlude update (n + suffix) state
      sourcePrefix sk interlude update suffix n next

/-- The full source prefix and the accepted-view prefix are coupled exactly, not merely bounded. -/
theorem sourcePrefix_views {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (suffix n : Nat) (state : State × SourcedState) :
    (fun result => sourcedPrior result.2.1) <$> sourcePrefix sk interlude update suffix n state =
      acceptedPrefix sk interlude update suffix n (state.1, state.2.2) (sourcedPrior state.2.1) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sourcePrefix, map_bind]
      simp_rw [ih]
      have h := congrArg (fun computation : ProbComp (State × Finset KeptDigestView × QueryCache HashSpec) =>
          computation >>= fun next => acceptedPrefix sk interlude update suffix n (next.1, next.2.2) next.2.1)
        (sourceInterleavedStep_views sk interlude update (n + suffix) state)
      simpa only [bind_map_left, acceptedPrefix] using h

/-- The localization term now refers directly to the actual accumulated SourceRecord list. -/
theorem expected_futureOverflow_source_prefix {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (suffix past : Nat)
    (hpair : (subtreeHeight, past + suffix) ∈ requestedLifetimePairs) (state : State) :
    (∑' result, Pr[= result | sourcePrefix sk interlude update suffix past (state, [], ∅)] *
      futureOverflow suffix (sourcedPrior result.2.1)) ≤ 1 / (2 : ℝ≥0∞) ^ 400 + 1 / 2 ^ 294 := by
  have h := expected_futureOverflow_actual_prefix sk interlude update suffix past hpair state
  have hproj := sourcePrefix_views sk interlude update suffix past (state, [], ∅)
  simp only [sourcedPrior, List.map_nil, List.toFinset_nil] at hproj
  rw [← hproj, tsum_probOutput_map_mul] at h
  exact h

/-- The all-prefix bound is unchanged after retaining every real source record and response. -/
theorem expected_futureOverflow_source_all_prefixes {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State) :
    (∑ suffix : Fin (n + 1), ∑' result,
      Pr[= result | sourcePrefix sk interlude update suffix.val (n - suffix.val) (state, [], ∅)] *
        futureOverflow suffix.val (sourcedPrior result.2.1)) ≤ 1 / (2 : ℝ≥0∞) ^ 263 := by
  have h := expected_futureOverflow_all_prefixes sk interlude update n hpair state
  have heq (suffix : Fin (n + 1)) :
      (∑' prior, Pr[= prior | acceptedPrefix sk interlude update suffix.val (n - suffix.val) (state, ∅) ∅] *
        futureOverflow suffix.val prior) =
      ∑' result, Pr[= result | sourcePrefix sk interlude update suffix.val (n - suffix.val) (state, [], ∅)] *
        futureOverflow suffix.val (sourcedPrior result.2.1) := by
    have hproj := sourcePrefix_views sk interlude update suffix.val (n - suffix.val) (state, [], ∅)
    simp only [sourcedPrior, List.map_nil, List.toFinset_nil] at hproj
    rw [← hproj, tsum_probOutput_map_mul]
    rfl
  simp_rw [heq] at h
  exact h

end LeanSphincs.Lifetime
