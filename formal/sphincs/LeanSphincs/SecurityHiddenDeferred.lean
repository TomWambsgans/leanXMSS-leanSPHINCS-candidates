import LeanSphincs.SecurityHiddenOutsideAccounting

/-! Deferred sampling for the finite hidden-coordinate table in the common comparison.
Outside ROM sampling remains genuine private randomness of the compiled program; only the
finite digest table is moved earlier. This permits conditioning on canonical output targets. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenReveal
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq _

/-- The forced-failure comparison with a fixed finite hidden table. Private randomness,
including every outside ROM draw, is still executed normally. -/
noncomputable def fixedComparison {α : Type} (table : ι → Digest)
    (computation : OracleComp (ViewSpec ι) α) : Knowledge ι → ProbComp (α × Nat) :=
  OracleComp.construct (fun value _ => pure (value, 0))
    (fun input _ next known => match input with
      | .inl draw => do
          let value ← liftM (unifSpec.query draw)
          next value known
      | .inr (.inl coordinate) =>
          next (table coordinate) (known.cacheQuery coordinate (table coordinate))
      | .inr (.inr guess) =>
          (fun result => (result.1, (if known guess.1 = none then 1 else 0) + result.2)) <$>
            next () known) computation

theorem fixedComparison_pure {α : Type} (table : ι → Digest) (value : α) (known : Knowledge ι) :
    fixedComparison table (pure value) known = pure (value, 0) := rfl

theorem fixedComparison_private {α : Type} (table : ι → Digest) (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    fixedComparison table (liftM ((ViewSpec ι).query (.inl draw)) >>= next) known =
      liftM (unifSpec.query draw) >>= fun value => fixedComparison table (next value) known := rfl

theorem fixedComparison_reveal {α : Type} (table : ι → Digest) (coordinate : ι)
    (next : Digest → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    fixedComparison table (liftM ((ViewSpec ι).query (.inr (.inl coordinate))) >>= next) known =
      fixedComparison table (next (table coordinate)) (known.cacheQuery coordinate (table coordinate)) := rfl

theorem fixedComparison_guess {α : Type} (table : ι → Digest) (guess : ι × Digest)
    (next : Unit → OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    fixedComparison table (liftM ((ViewSpec ι).query (.inr (.inr guess))) >>= next) known =
      (fun result => (result.1, (if known guess.1 = none then 1 else 0) + result.2)) <$>
        fixedComparison table (next ()) known := rfl

private theorem revealed_cache (known : Knowledge ι) (coordinate : ι)
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

/-- Exact distributional equivalence, including the program result and actual guess count.
There is no assumed independence invariant on the real game cache. -/
theorem evalDist_completion_fixedComparison {α : Type}
    (computation : OracleComp (ViewSpec ι) α) (known : Knowledge ι) :
    𝒟[completion known >>= fun table => fixedComparison table computation known] =
      𝒟[comparison computation known] := by
  induction computation using OracleComp.inductionOn generalizing known with
  | pure value =>
      apply evalDist_ext
      intro target
      simp [fixedComparison_pure, comparison]
  | query_bind input next ih =>
      cases input with
      | inl draw =>
          simp only [fixedComparison_private]
          rw [evalDist_bind_bind_swap]
          change 𝒟[liftM (unifSpec.query draw) >>= _] =
            𝒟[liftM (unifSpec.query draw) >>= fun value => comparison (next value) known]
          apply evalDist_bind_congr'
          exact fun value => ih value known
      | inr input => cases input with
        | inl coordinate =>
            simp only [fixedComparison_reveal]
            rw [completion_reveal known coordinate
              (fun value table => fixedComparison table (next value) (known.cacheQuery coordinate value))]
            change 𝒟[(randomOracle (spec := ι →ₒ Digest) coordinate).run known >>= _] =
              𝒟[(randomOracle (spec := ι →ₒ Digest) coordinate).run known >>=
                fun result => comparison (next result.1) result.2]
            apply evalDist_bind_congr
            rintro ⟨value, known'⟩ hr
            dsimp only
            have hc := revealed_cache known coordinate (value, known') hr
            dsimp only at hc
            rw [hc]
            exact ih value _
        | inr guess =>
            simp only [fixedComparison_guess]
            rw [← map_bind]
            exact evalDist_map_eq_of_evalDist_eq (ih () known) _

end LeanSphincs.Security.HiddenReveal

namespace LeanSphincs.Security.HiddenOutside
set_option backward.isDefEq.respectTransparency false

/-- Private outside-cache reads retain their exact law when the finite hidden table is fixed. -/
theorem fixedComparison_privateLift_bind {ι α β : Type} [Fintype ι] (table : ι → Digest)
    (computation : ProbComp α) (next : α → OracleComp (HiddenReveal.ViewSpec ι) β)
    (known : HiddenReveal.Knowledge ι) :
    HiddenReveal.fixedComparison table (privateLift computation >>= next) known =
      computation >>= fun value => HiddenReveal.fixedComparison table (next value) known := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [privateLift_pure, pure_bind]
  | query_bind draw continuation ih =>
      rw [privateLift, simulateQ_bind, simulateQ_spec_query]
      change HiddenReveal.fixedComparison table
        ((liftM ((HiddenReveal.ViewSpec ι).query (.inl draw)) >>= fun value => privateLift (continuation value)) >>= next) known = _
      rw [bind_assoc, HiddenReveal.fixedComparison_private, bind_assoc]
      exact congrArg (fun k => liftM (unifSpec.query draw) >>= k) (funext ih)

theorem evalDist_comparison_finite_table {D R A ι α : Type} [Fintype ι] [SampleableType R]
    (model : HiddenRows.Model D R A ι) (computation : OracleComp (HiddenCost.SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    𝒟[comparison model computation known cache] =
      𝒟[HiddenReveal.completion known >>= fun table =>
        HiddenReveal.fixedComparison table
          (compile model (HiddenCost.erase (HiddenCost.trace computation)) known cache) known] :=
  (HiddenReveal.evalDist_completion_fixedComparison _ known).symm

end LeanSphincs.Security.HiddenOutside
