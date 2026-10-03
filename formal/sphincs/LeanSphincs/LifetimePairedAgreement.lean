import LeanSphincs.LifetimePairedPoolCoupling

/-! The reified observer stores genuine oracle answers. Its local cache remains a subcache
of the physical oracle even when the latter was prepared with an unobserved full table. -/

namespace LeanSphincs.Lifetime.PairedReification
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType FirstPoolTable := firstPoolTableSampleableType

theorem observedHash_support_agrees (input : HashInput) (observed physical : QueryCache HashSpec)
    (hagree : observed ≤ physical)
    (result : (HashOutput × QueryCache HashSpec) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl ((observedHash input).run observed)).run physical)) :
    result.1.2 ≤ result.2 := by
  cases hc : observed input with
  | some answer =>
      rw [observedHash, QueryImpl.withCaching_run_some _ hc, simulateQ_pure,
        StateT.run_pure, mem_support_pure_iff] at hresult
      cases hresult
      exact hagree
  | none =>
      rw [observedHash, QueryImpl.withCaching_run_none _ hc, simulateQ_map,
        StateT.run_map, support_map] at hresult
      obtain ⟨first, hfirst, rfl⟩ := hresult
      simp only [simulateQ_spec_query] at hfirst
      have hquery : first ∈ support ((randomOracle (spec := HashSpec) input).run physical) := hfirst
      obtain ⟨hext, hknown⟩ := query_support_cached input physical first.1 first.2 hquery
      intro other value hvalue
      dsimp only at hvalue ⊢
      by_cases heq : other = input
      · subst other
        rw [QueryCache.cacheQuery_self] at hvalue
        cases Option.some.inj hvalue
        exact hknown
      · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hvalue
        exact hext (hagree hvalue)

theorem observedPairedHash_support_agrees (sk : Seeded.SecretKey) (input : HashInput)
    (observed physical : QueryCache HashSpec) (hagree : observed ≤ physical)
    (result : (HashOutput × QueryCache HashSpec) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl ((observedPairedHash sk input).run observed)).run physical)) :
    result.1.2 ≤ result.2 := by
  simp only [observedPairedHash, StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hrest⟩ := hresult
  have hmid := observedHash_support_agrees input observed physical hagree first hfirst
  cases hp : decodeCandidateInput sk input with
  | none =>
      simp only [hp, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hrest
      cases hrest
      exact hmid
  | some position =>
      simp only [hp, StateT.run_bind, simulateQ_bind, mem_support_bind_iff,
        StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hrest
      obtain ⟨second, hsecond, rfl⟩ := hrest
      exact observedHash_support_agrees _ first.1.2 first.2 hmid second hsecond

theorem observedRom_support_agrees (sk : Seeded.SecretKey) (input : OracleWorld.Domain)
    (observed physical : QueryCache HashSpec) (hagree : observed ≤ physical)
    (result : (OracleWorld.Range input × QueryCache HashSpec) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl ((observedRom sk input).run observed)).run physical)) :
    result.1.2 ≤ result.2 := by
  cases input with
  | inr input => exact observedPairedHash_support_agrees sk input observed physical hagree result hresult
  | inl input =>
      change result ∈ support ((fun answer => ((answer, observed), physical)) <$>
        (liftM (unifSpec.query input) : ProbComp _)) at hresult
      rw [support_map] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      exact hagree

/-- No preparation can make the observer invent an answer inconsistent with the shared ROM. -/
theorem traceProgram_support_agrees {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (observed physical : QueryCache HashSpec)
    (hagree : observed ≤ physical)
    (result : (α × List QueryRecord × QueryCache HashSpec) × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ romImpl (traceProgram sk program observed)).run physical)) :
    result.1.2.2 ≤ result.2 := by
  induction program using OracleComp.inductionOn generalizing observed physical result with
  | pure value =>
      simp only [traceProgram_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      cases hresult
      exact hagree
  | query_bind input next ih =>
      simp only [traceProgram_query_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
        simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      obtain ⟨first, hfirst, last, hlast, rfl⟩ := hresult
      exact ih first.1.1 first.1.2 first.2
        (observedRom_support_agrees sk input observed physical hagree first hfirst) last hlast

/-- Every observed first-block value is precisely the corresponding prepared-table value. -/
theorem prepared_trace_firstPool_agrees {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (table : FirstPoolTable)
    (trace : α × List QueryRecord × QueryCache HashSpec)
    (htrace : trace ∈ support ((simulateQ romImpl (traceProgram sk program ∅)).run' (firstPoolCache table)))
    (position : FirstPoolPosition) (answer : HashOutput)
    (hanswer : trace.2.2 (firstPoolInput position) = some answer) : answer = table position := by
  rw [StateT.run'_eq, support_map] at htrace
  obtain ⟨result, hresult, rfl⟩ := htrace
  have hobserved := traceProgram_support_agrees sk program ∅ (firstPoolCache table) (by
    intro input value h; cases h) result hresult
  have hphysical := world_support_cache_le _ _ _ _ hresult (firstPoolCache_apply table position)
  exact Option.some.inj ((hobserved hanswer).symm.trans hphysical)

/-- The joint output retains this agreement, together with its trace and table marginals. -/
theorem poolJointRun_firstPool_agrees {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α)
    (result : (α × List QueryRecord × QueryCache HashSpec) × FirstPoolTable)
    (hresult : result ∈ support (poolJointRun sk program))
    (position : FirstPoolPosition) (answer : HashOutput)
    (hanswer : result.1.2.2 (firstPoolInput position) = some answer) : answer = result.2 position := by
  have hprepared : result ∈ support (preparedPoolJointRun sk program) := by
    exact (mem_support_iff_of_evalDist_eq (evalDist_poolJointRun sk program) _).mp hresult
  simp only [preparedPoolJointRun, mem_support_bind_iff, mem_support_pure_iff] at hprepared
  obtain ⟨table, _, trace, htrace, rfl⟩ := hprepared
  exact prepared_trace_firstPool_agrees sk program table trace htrace position answer hanswer

end LeanSphincs.Lifetime.PairedReification
