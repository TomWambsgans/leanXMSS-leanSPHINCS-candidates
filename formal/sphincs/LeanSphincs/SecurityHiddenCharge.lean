import LeanSphincs.SecurityHiddenReveal

/-! The first-hidden-coordinate loss charged to the common comparison execution. Guesses
in this execution return unit even on equality; reveals and private randomness are real.
Thus prior failed guesses are never used to assert a false conditional uniformity claim. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenReveal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq ι

/-- The comparison executes every guess as a failed check and records the number of guesses
made while their coordinates are unexposed. It retains the result to permit joint accounting
with other query-domain monitors on this very execution. -/
noncomputable def comparison {α : Type} (computation : OracleComp (ViewSpec ι) α) :
    Knowledge ι → ProbComp (α × Nat) :=
  OracleComp.construct (fun value _ => pure (value, 0))
    (fun input _ next known => match input with
      | .inl draw => do
          let value ← liftM (unifSpec.query draw)
          next value known
      | .inr (.inl coordinate) => do
          let (value, known') ← (randomOracle (spec := ι →ₒ Digest) coordinate).run known
          next value known'
      | .inr (.inr guess) =>
          (fun result => (result.1, (if known guess.1 = none then 1 else 0) + result.2)) <$>
            next () known) computation

noncomputable def expectedGuessCharge {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) : ℝ≥0∞ :=
  ∑' result, Pr[= result | comparison computation known] * (result.2 : ℝ≥0∞)

theorem charge_pure {α : Type} (value : α) (known : Knowledge ι) :
    expectedGuessCharge (pure value) known = 0 := by
  simp [expectedGuessCharge, comparison, tsum_probOutput_pure_mul]

theorem charge_private {α : Type} (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    expectedGuessCharge (liftM ((ViewSpec ι).query (.inl draw)) >>= next) known =
      ∑' value, Pr[= value | (liftM (unifSpec.query draw) : ProbComp _)] *
        expectedGuessCharge (next value) known := by
  exact tsum_probOutput_bind_mul _ _ _

theorem charge_reveal {α : Type} (coordinate : ι)
    (next : Digest → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    expectedGuessCharge (liftM ((ViewSpec ι).query (.inr (.inl coordinate))) >>= next) known =
      ∑' result, Pr[= result | (randomOracle (spec := ι →ₒ Digest) coordinate).run known] *
        expectedGuessCharge (next result.1) result.2 := by
  exact tsum_probOutput_bind_mul _ _ _

theorem charge_guess {α : Type} (guess : ι × Digest)
    (next : Unit → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    expectedGuessCharge (liftM ((ViewSpec ι).query (.inr (.inr guess))) >>= next) known =
      (if known guess.1 = none then 1 else 0) + expectedGuessCharge (next ()) known := by
  unfold expectedGuessCharge
  change (∑' result, Pr[= result | (fun result : α × Nat =>
    (result.1, (if known guess.1 = none then 1 else 0) + result.2)) <$>
      comparison (next ()) known] * (result.2 : ℝ≥0∞)) = _
  rw [tsum_probOutput_map_mul]
  simp only [Nat.cast_add, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  rw [tsum_probOutput_eq_one' (by simp)]
  split <;> simp

private theorem randomOracle_cache_of_support (known : Knowledge ι) (coordinate : ι)
    (result : Digest × Knowledge ι)
    (hr : result ∈ support ((randomOracle (spec := ι →ₒ Digest) coordinate).run known)) :
    result.2 = known.cacheQuery coordinate result.1 := by
  cases hc : known coordinate with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨value, _, rfl⟩ := hr
      rfl
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
      subst result
      apply QueryCache.ext
      intro other
      by_cases ho : other = coordinate
      · subst other; simp [hc]
      · simp [QueryCache.cacheQuery_of_ne _ _ ho]

/-- A shared-budget form: charge only hidden guesses in the full comparison run, including
its actual adaptive disclosures and private randomness. Other monitors may use complementary
charges on that same run; a separate experiment's expected count cannot be substituted. -/
theorem adaptive_guess_bound_charge {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) :
    Pr[= none | experiment computation known] ≤
      expectedGuessCharge computation known / (2 : ℝ≥0∞) ^ 128 := by
  induction computation using OracleComp.inductionOn generalizing known with
  | pure value => simp [experiment, run_pure, charge_pure]
  | query_bind input next ih =>
      cases input with
      | inl draw =>
          rw [charge_private]
          simp only [experiment, run_private]
          rw [probOutput_bind_bind_swap, probOutput_bind_eq_tsum]
          simp only [div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_assoc]
          apply ENNReal.tsum_le_tsum
          intro value
          exact mul_le_mul' le_rfl (ih value known)
      | inr input =>
          cases input with
          | inl coordinate =>
              rw [charge_reveal]
              simp only [experiment, run_reveal]
              rw [probOutput_congr rfl (completion_reveal known coordinate
                (fun value table => run table (next value) (known.cacheQuery coordinate value)))]
              rw [probOutput_bind_eq_tsum]
              simp only [div_eq_mul_inv, ← ENNReal.tsum_mul_right, mul_assoc]
              apply ENNReal.tsum_le_tsum
              intro result
              by_cases hr : result ∈ support
                  ((randomOracle (spec := ι →ₒ Digest) coordinate).run known)
              · have hc := randomOracle_cache_of_support known coordinate result hr
                rw [hc]
                exact mul_le_mul' le_rfl (ih result.1 _)
              · rw [probOutput_eq_zero_of_not_mem_support hr]
                simp
          | inr guess =>
              rw [charge_guess, ENNReal.add_div]
              rw [experiment]
              simp only [run_guess]
              calc
                _ ≤ (if known guess.1 = none then 1 / (2 : ℝ≥0∞) ^ 128 else 0) +
                    Pr[= none | experiment (next ()) known] := by
                  by_cases hu : known guess.1 = none
                  · have hp := completion_guess known guess.1 guess.2 hu
                    simp only [experiment]
                    rw [if_pos hu, ← hp, probEvent_eq_tsum_ite, probOutput_bind_eq_tsum,
                      probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
                    apply ENNReal.tsum_le_tsum
                    intro table
                    by_cases hh : table guess.1 = guess.2 <;>
                      simp only [hu, hh, true_and, ↓reduceIte] <;> simp
                  · simp [hu, experiment]
                _ ≤ _ := by
                  simp only [ite_div, zero_div]
                  exact add_le_add (by split <;> simp) (ih () known)

theorem comparison_charge_le {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) (q : Nat) (hbound : computation.IsQueryBoundP IsGuess q)
    (result : α × Nat) (hresult : result ∈ support (comparison computation known)) :
    result.2 ≤ q := by
  induction computation using OracleComp.inductionOn generalizing known q result with
  | pure value =>
      simp only [comparison, OracleComp.construct_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | inl draw =>
          simp only [IsGuess, not_false_eq_true, true_or, ↓reduceIte] at hbound
          rw [comparison, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨value, _, hvalue⟩ := hresult
          exact ih value known q (hbound.2 value) result hvalue
      | inr input =>
          cases input with
          | inl coordinate =>
              simp only [IsGuess, not_false_eq_true, true_or, ↓reduceIte] at hbound
              rw [comparison, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨⟨value, known'⟩, _, hvalue⟩ := hresult
              exact ih value known' q (hbound.2 value) result hvalue
          | inr guess =>
              simp only [IsGuess, not_true_eq_false, false_or, ↓reduceIte] at hbound
              rw [comparison, OracleComp.construct_query_bind, support_map] at hresult
              obtain ⟨result', hr, rfl⟩ := hresult
              have h := ih () known (q - 1) (hbound.2 ()) result' hr
              split <;> simp only [Prod.snd] <;> omega

theorem expectedGuessCharge_le {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) (q : Nat) (hbound : computation.IsQueryBoundP IsGuess q) :
    expectedGuessCharge computation known ≤ q := by
  unfold expectedGuessCharge
  calc
    _ ≤ ∑' result, Pr[= result | comparison computation known] * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support (comparison computation known)
      · exact mul_le_mul' le_rfl (by exact_mod_cast comparison_charge_le computation known q hbound result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr]
        simp
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

end LeanSphincs.Security.HiddenReveal
