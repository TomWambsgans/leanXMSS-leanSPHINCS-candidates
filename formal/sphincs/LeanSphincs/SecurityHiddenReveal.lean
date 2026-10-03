import LeanSphincs.Uniform
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import SphincsSecurity.Proof.Base.QueryCap

/-! Adaptive reveal/guess security for independently sampled candidate digest coordinates.
A guess is monitored before exposure and stops on its first hidden-coordinate match. Failed
checks supply no answer-dependent information. Reveals return the actual selected coordinate.
The proof uses exact uniform completion of the exposed cache, rather than assuming that a
coordinate remains uniform after conditioning on previous failed guesses. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenReveal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq ι
noncomputable local instance tableSampleable : SampleableType (ι → Digest) := SampleableType.ofFintype _

abbrev Knowledge (ι : Type) := QueryCache (ι →ₒ Digest)
abbrev ViewSpec (ι : Type) := unifSpec + ((ι →ₒ Digest) + ((ι × Digest) →ₒ Unit))

noncomputable def completion (known : Knowledge ι) : ProbComp (ι → Digest) :=
  tableExtending known <$> ($ᵗ (ι → Digest) : ProbComp (ι → Digest))

theorem completion_known (known : Knowledge ι) (coordinate : ι) (value : Digest)
    (hknown : known coordinate = some value) (table : ι → Digest) :
    tableExtending known table coordinate = value := by simp [tableExtending, hknown]

/-- Revealing any selected coordinate commutes with sampling the remaining uniform table.
This includes the full residual table, so arbitrary adaptive continuations may follow. -/
theorem completion_reveal {α : Type} (known : Knowledge ι) (coordinate : ι)
    (next : Digest → (ι → Digest) → ProbComp α) :
    𝒟[completion known >>= fun table => next (table coordinate) table] =
      𝒟[do
        let (value, known') ← (randomOracle (spec := ι →ₒ Digest) coordinate).run known
        completion known' >>= next value] := by
  cases hc : known coordinate with
  | some value =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
      simp only [completion, bind_map_left, completion_known known coordinate value hc]
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      simp only [completion, bind_map_left]
      let continuation := fun table : ι → Digest =>
        next (tableExtending known table coordinate) (tableExtending known table)
      change 𝒟[($ᵗ (ι → Digest)) >>= continuation] = _
      rw [evalDist_bind, ← evalDist_uniformSample_bind_update (D := ι) (R := Digest) coordinate,
        ← evalDist_bind]
      simp only [bind_assoc, pure_bind]
      apply evalDist_bind_congr'
      intro value
      apply evalDist_bind_congr'
      intro table
      have heq : tableExtending known (Function.update table coordinate value) =
          tableExtending (known.cacheQuery coordinate value) table := by
        rw [tableExtending_cacheQuery, tableExtending_update_of_none known table hc]
      simp only [continuation, heq, tableExtending, hc, Function.update_self, Option.getD_none,
        QueryCache.cacheQuery_self, Option.getD_some]

/-- One guessed value at an unexposed coordinate has exact probability 2^-128. -/
theorem completion_guess (known : Knowledge ι) (coordinate : ι) (value : Digest)
    (hunknown : known coordinate = none) :
    Pr[fun table => table coordinate = value | completion known] = 1 / (2 : ℝ≥0∞) ^ 128 := by
  rw [completion, probEvent_map]
  change Pr[fun table : ι → Digest => (known coordinate).getD (table coordinate) = value |
    ($ᵗ (ι → Digest) : ProbComp (ι → Digest))] = _
  simp only [hunknown, Option.getD_none]
  change Pr[(fun x : Digest => x = value) ∘ (fun table : ι → Digest => table coordinate) |
    ($ᵗ (ι → Digest) : ProbComp (ι → Digest))] = _
  rw [← probEvent_map]
  have h := evalDist_uniformSample_bind_update (D := ι) (R := Digest) coordinate
  have hmap := evalDist_map_eq_of_evalDist_eq h (fun table : ι → Digest => table coordinate)
  simp only [map_bind, map_pure, Function.update_self] at hmap
  have hdist : 𝒟[(fun table : ι → Digest => table coordinate) <$> ($ᵗ (ι → Digest))] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
    rw [← hmap]
    apply evalDist_ext
    intro target
    trans Pr[= target | (($ᵗ Digest : ProbComp Digest) >>= fun value => pure value)]
    · apply probOutput_bind_congr'
      intro answer
      simp
    · simp
  rw [probEvent_congr' (fun _ _ => Iff.rfl) hdist, probEvent_eq_eq_probOutput,
    probOutput_uniformSample]
  rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  simp only [one_div]

def IsGuess : (ViewSpec ι).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

noncomputable def run {α : Type} (table : ι → Digest) (computation : OracleComp (ViewSpec ι) α) :
    Knowledge ι → ProbComp (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun input _ next known =>
      match input with
      | .inl draw => do
          let value ← liftM (unifSpec.query draw)
          next value known
      | .inr (.inl coordinate) => next (table coordinate)
          (known.cacheQuery coordinate (table coordinate))
      | .inr (.inr guess) =>
          if known guess.1 = none ∧ table guess.1 = guess.2 then pure none
          else next () known) computation

theorem run_pure {α : Type} (table : ι → Digest) (value : α) (known : Knowledge ι) :
    run table (pure value) known = pure (some value) := rfl

theorem run_private {α : Type} (table : ι → Digest) (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    run table (liftM ((ViewSpec ι).query (.inl draw)) >>= next) known =
      (liftM (unifSpec.query draw) >>= fun value => run table (next value) known) := rfl

theorem run_reveal {α : Type} (table : ι → Digest) (coordinate : ι)
    (next : Digest → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    run table (liftM ((ViewSpec ι).query (.inr (.inl coordinate))) >>= next) known =
      run table (next (table coordinate)) (known.cacheQuery coordinate (table coordinate)) := rfl

theorem run_guess {α : Type} (table : ι → Digest) (guess : ι × Digest)
    (next : Unit → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    run table (liftM ((ViewSpec ι).query (.inr (.inr guess))) >>= next) known =
      if known guess.1 = none ∧ table guess.1 = guess.2 then pure none
      else run table (next ()) known := rfl

noncomputable def experiment {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) : ProbComp (Option α) :=
  completion known >>= fun table => run table computation known

private theorem guess_then_continue_le {α : Type} (known : Knowledge ι)
    (guess : ι × Digest) (tail : (ι → Digest) → ProbComp (Option α)) :
    Pr[= none | completion known >>= fun table =>
      if known guess.1 = none ∧ table guess.1 = guess.2 then pure none else tail table] ≤
        (if known guess.1 = none then 1 / (2 : ℝ≥0∞) ^ 128 else 0) +
          Pr[= none | completion known >>= tail] := by
  by_cases hu : known guess.1 = none
  · have hp := completion_guess known guess.1 guess.2 hu
    rw [if_pos hu, ← hp, probEvent_eq_tsum_ite, probOutput_bind_eq_tsum,
      probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro table
    by_cases hh : table guess.1 = guess.2 <;> simp only [hu, hh, true_and, ↓reduceIte]
    · simp
    · simp
  · simp [hu]

/-- Any adaptive sequence of reveals, private draws and at most `q` ordinary equality guesses
hits a still-hidden digest coordinate with probability at most q/2^128. -/
theorem adaptive_guess_bound {α : Type} (computation : OracleComp (ViewSpec ι) α)
    (known : Knowledge ι) (q : Nat) (hbound : computation.IsQueryBoundP IsGuess q) :
    Pr[= none | experiment computation known] ≤ q / (2 : ℝ≥0∞) ^ 128 := by
  induction computation using OracleComp.inductionOn generalizing known q with
  | pure value => simp [experiment, run_pure]
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | inl draw =>
          simp only [IsGuess, not_false_eq_true, true_or, ↓reduceIte] at hbound
          simp only [experiment, run_private]
          rw [probOutput_bind_bind_swap]
          rw [← probEvent_eq_eq_probOutput]
          apply probEvent_bind_le_of_forall_le
          intro answer _
          simpa only [experiment, probEvent_eq_eq_probOutput] using ih answer known q (hbound.2 answer)
      | inr input =>
          cases input with
          | inl coordinate =>
              simp only [IsGuess, not_false_eq_true, true_or, ↓reduceIte] at hbound
              simp only [experiment, run_reveal]
              rw [probOutput_congr rfl (completion_reveal known coordinate
                (fun value table => run table (next value) (known.cacheQuery coordinate value)))]
              rw [← probEvent_eq_eq_probOutput]
              apply probEvent_bind_le_of_forall_le
              intro result hresult
              have hcache : result.2 = known.cacheQuery coordinate result.1 := by
                cases hc : known coordinate with
                | none =>
                    rw [QueryImpl.withCaching_run_none _ hc, support_map] at hresult
                    obtain ⟨value, _, rfl⟩ := hresult
                    rfl
                | some value =>
                    rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hresult
                    subst result
                    apply QueryCache.ext
                    intro other
                    by_cases ho : other = coordinate
                    · subst other; simp [hc]
                    · simp [QueryCache.cacheQuery_of_ne _ _ ho]
              rcases result with ⟨value, known'⟩
              simp only at hcache
              subst known'
              simpa only [experiment, probEvent_eq_eq_probOutput] using
                ih value (known.cacheQuery coordinate value) q (hbound.2 value)
          | inr guess =>
              simp only [IsGuess, not_true_eq_false, false_or, ↓reduceIte] at hbound
              rw [experiment]
              simp only [run_guess]
              calc
                _ ≤ (if known guess.1 = none then 1 / (2 : ℝ≥0∞) ^ 128 else 0) +
                    Pr[= none | experiment (next ()) known] := guess_then_continue_le known guess _
                _ ≤ 1 / (2 : ℝ≥0∞) ^ 128 + (q - 1 : Nat) / (2 : ℝ≥0∞) ^ 128 := by
                  exact add_le_add (by split <;> simp) (ih () known (q - 1) (hbound.2 ()))
                _ = _ := by
                  rw [← ENNReal.add_div, ← Nat.cast_one, ← Nat.cast_add]
                  congr 2
                  omega

end LeanSphincs.Security.HiddenReveal
