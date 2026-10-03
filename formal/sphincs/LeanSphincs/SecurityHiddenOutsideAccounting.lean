import LeanSphincs.SecurityHiddenOutside
import LeanSphincs.SecurityHiddenDomainAllocation

/-! The original-cost trace and all local monitor charges survive lazy outside-oracle
sampling. Every bound below refers to one joint execution with its actual outside cache. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenOutside
open HiddenCost
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance : DecidableEq D := Classical.decEq _
noncomputable local instance : DecidableEq ι := Classical.decEq _

theorem privateLift_pays_bind {α β : Type} (computation : ProbComp α)
    (next : α → OracleComp (HiddenReveal.ViewSpec ι) β) (credit : β → Nat) (spent : Nat)
    (h : ∀ value, Pays guessCost (next value) credit spent) :
    Pays guessCost (privateLift computation >>= next) credit spent := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [privateLift_pure, pure_bind] using h value
  | query_bind draw continuation ih =>
      rw [privateLift, simulateQ_bind, simulateQ_spec_query]
      change Pays guessCost
        ((liftM ((HiddenReveal.ViewSpec ι).query (.inl draw)) >>= fun value => privateLift (continuation value)) >>= next) credit spent
      rw [bind_assoc, pays_query_bind]
      exact fun value => ih value

theorem compile_pays_rows {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R)
    (credit : α → Nat) (spent : Nat) (h : Pays (rowSourceCost model) computation credit spent) :
    Pays guessCost (compile model computation known cache) (fun result => credit result.1) spent := by
  induction computation using OracleComp.inductionOn generalizing known cache spent with
  | pure value => exact h
  | query_bind input next ih =>
      rw [pays_query_bind] at h
      cases input with
      | inl draw =>
          rw [compile_private, pays_query_bind]
          exact fun value => ih value known cache spent (h value)
      | inr input => cases input with
        | inr coordinate =>
            rw [compile_reveal, pays_query_bind]
            exact fun value => ih value _ cache spent (h value)
        | inl bytes =>
            rw [compile_hash]
            cases hp : model.parse bytes with
            | none =>
                simp only [hp]
                apply privateLift_pays_bind
                intro result
                apply ih result.1 known result.2 spent
                simpa only [rowSourceCost, hp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                  Nat.add_zero] using h result.1
            | some query =>
                simp only [hp]
                have ht (value : R) : Pays (rowSourceCost model) (next value) credit (spent + 1) := by
                  simpa only [rowSourceCost, hp, Option.isSome_some, ↓reduceIte] using h value
                cases hk : known (model.incoming query.1) with
                | none =>
                    simp only [hk]
                    rw [pays_query_bind]
                    intro _
                    apply privateLift_pays_bind
                    exact fun result => ih _ known result.2 (spent + 1) (ht _)
                | some canonical =>
                    simp only [hk]
                    have ht' (value : R) : Pays (rowSourceCost model) (next value) credit spent :=
                      pays_mono _ _ credit credit (spent + 1) spent (fun _ => le_rfl) (Nat.le_succ _) (ht value)
                    split_ifs
                    · rw [pays_query_bind]
                      exact fun successor => ih _ _ cache spent (ht' _)
                    · apply privateLift_pays_bind
                      exact fun result => ih _ known result.2 spent (ht' _)

theorem compile_support {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R)
    (result : α × Cache D R) (hresult : result ∈ support (compile model computation known cache)) :
    result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing known cache result with
  | pure value =>
      change result ∈ support (pure (value, cache) : OracleComp (HiddenReveal.ViewSpec ι) _) at hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp
  | query_bind input next ih =>
      apply (mem_support_bind_iff _ _ _).mpr
      cases input with
      | inl draw =>
          rw [compile_private, mem_support_bind_iff] at hresult
          obtain ⟨value, _, htail⟩ := hresult
          exact ⟨value, mem_support_query _ _, ih value known cache result htail⟩
      | inr input => cases input with
        | inr coordinate =>
            rw [compile_reveal, mem_support_bind_iff] at hresult
            obtain ⟨value, _, htail⟩ := hresult
            exact ⟨value, mem_support_query _ _, ih value _ cache result htail⟩
        | inl bytes =>
            rw [compile_hash] at hresult
            cases hp : model.parse bytes with
            | none =>
                simp only [hp] at hresult
                rw [mem_support_bind_iff] at hresult
                obtain ⟨answer, _, htail⟩ := hresult
                exact ⟨answer.1, mem_support_query _ _, ih _ known answer.2 result htail⟩
            | some query =>
                simp only [hp] at hresult
                cases hk : known (model.incoming query.1) with
                | none =>
                    simp only [hk] at hresult
                    rw [mem_support_bind_iff] at hresult
                    obtain ⟨_, _, htail⟩ := hresult
                    rw [mem_support_bind_iff] at htail
                    obtain ⟨answer, _, htail⟩ := htail
                    exact ⟨answer.1, mem_support_query _ _, ih _ known answer.2 result htail⟩
                | some canonical =>
                    simp only [hk] at hresult
                    split_ifs at hresult
                    · rw [mem_support_bind_iff] at hresult
                      obtain ⟨successor, _, htail⟩ := hresult
                      exact ⟨model.combine query.1 successor, mem_support_query _ _, ih _ _ cache result htail⟩
                    · rw [mem_support_bind_iff] at hresult
                      obtain ⟨answer, _, htail⟩ := hresult
                      exact ⟨answer.1, mem_support_query _ _, ih _ known answer.2 result htail⟩

/-- One joint trace containing the source result, raw/virtual original work, outside cache,
and hidden-input guess count. Its raw answers are generated by an actual lazy ROM. -/
noncomputable def comparison {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    ProbComp (((α × List (Entry D)) × Cache D R) × Nat) :=
  HiddenReveal.comparison (compile model (erase (trace computation)) known cache) known

theorem comparison_guess_le_rows {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R)
    (result : ((α × List (Entry D)) × Cache D R) × Nat)
    (hresult : result ∈ support (comparison model computation known cache)) :
    result.2 ≤ traceCharge (rowWeight model) result.1.1.2 := by
  have htrace := trace_pays_rows model computation 0
  have herase := erase_pays_rows model (trace computation) _ 0 htrace
  have hcompile := compile_pays_rows model (erase (trace computation)) known cache _ 0 herase
  simpa only [Nat.zero_add] using revealComparison_pays _ known _ 0 hcompile result hresult

theorem comparison_cost_le {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) (budget : Nat)
    (hbound : Bounded computation budget) (result : ((α × List (Entry D)) × Cache D R) × Nat)
    (hresult : result ∈ support (comparison model computation known cache)) :
    traceCost result.1.1.2 ≤ budget := by
  have hc := revealComparison_support _ known result hresult
  have hs := compile_support model (erase (trace computation)) known cache result.1 hc
  exact trace_support_cost_le computation budget hbound result.1.1 (erase_support _ hs)

theorem capped_comparison_cost_le {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) (budget : Nat)
    (result : ((Option α × List (Entry D)) × Cache D R) × Nat)
    (hresult : result ∈ support (comparison model (cap computation budget) known cache)) :
    traceCost result.1.1.2 ≤ budget :=
  comparison_cost_le model _ known cache budget (cap_bounded computation budget) result hresult

theorem common_stop_or_bad_bound {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R)
    (bad : (α × List (Entry D)) × Cache D R → Prop) :
    Pr[HiddenReveal.StopOr bad | stoppedExperiment model (erase (trace computation)) known cache] ≤
      expectedTraceCharge (comparison model computation known cache) (fun result => result.1.1.2)
        (rowWeight model) / (2 : ℝ≥0∞) ^ 128 +
      Pr[fun result => bad result.1 | comparison model computation known cache] := by
  refine (stop_or_bad_bound model _ known cache bad).trans ?_
  apply add_le_add _ le_rfl
  apply ENNReal.div_le_div_right
  unfold HiddenReveal.expectedGuessCharge expectedTraceCharge
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (comparison model computation known cache)
  · exact mul_le_mul' le_rfl (by exact_mod_cast comparison_guess_le_rows model computation known cache result hr)
  · change Pr[= result | comparison model computation known cache] * _ ≤ _
    rw [probOutput_eq_zero_of_not_mem_support hr]
    simp

theorem common_seed_bound {α : Type} (model : HiddenRows.Model HashInput R A ι)
    (computation : OracleComp (SourceCostSpec HashInput R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache HashInput R) :
    Pr[= true | sampleMasterSeed >>= fun seed =>
      (fun result => decide (TraceSeedHit result.1.1.2 seed)) <$> comparison model computation known cache] ≤
      expectedTraceCharge (comparison model computation known cache) (fun result => result.1.1.2)
        seedWeight / (2 : ℝ≥0∞) ^ 256 :=
  seed_monitor_bound _ _

theorem capped_rate_allocation {α κ : Type} [Fintype κ]
    (model : HiddenRows.Model D R A ι) (computation : OracleComp (SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R)
    (weights : κ → Entry D → Nat) (rates : κ → ℝ≥0∞) (allowance : ℝ≥0∞)
    (hlocal : ∀ entry, (∑ monitor, (weights monitor entry : ℝ≥0∞) * rates monitor) ≤
      (entryCost entry : ℝ≥0∞) * allowance) (budget : Nat) :
    (∑ monitor, expectedTraceCharge (comparison model (cap computation budget) known cache)
      (fun result => result.1.1.2) (weights monitor) * rates monitor) ≤
      (budget : ℝ≥0∞) * allowance :=
  expected_rate_allocation _ _ weights rates allowance hlocal budget
    (capped_comparison_cost_le model computation known cache budget)

end LeanSphincs.Security.HiddenOutside
