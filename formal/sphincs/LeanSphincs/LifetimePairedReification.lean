import LeanSphincs.LifetimePairedBankInclusion
import LeanSphincs.LifetimePoolPreparation

/-! Reifying the paired interpreter as an actual oracle program with a separate observed
cache. Presampling the physical oracle cannot change which candidate the trace first touches.
The complete trace and any subsequently queried table are retained in the joint output. -/

namespace LeanSphincs.Lifetime.PairedReification
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false

/-- The observed cache is distinct from the underlying oracle cache. -/
noncomputable def observedHash : QueryImpl HashSpec (StateT (QueryCache HashSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withCaching (spec := HashSpec)
    (fun input => (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld HashOutput))

noncomputable def observedPairedHash (sk : Seeded.SecretKey) :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) (OracleComp OracleWorld)) := fun input => do
  let answer ← observedHash input
  match decodeCandidateInput sk input with
  | none => pure answer
  | some position =>
      let _ ← observedHash (candidateInput sk position.1 (otherDigestCall position.2))
      pure answer

noncomputable def observedRom (sk : Seeded.SecretKey) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) (OracleComp OracleWorld)) := fun input =>
  match input with
  | .inl input => fun cache => (fun answer => (answer, cache)) <$> (liftM (OracleWorld.query (.inl input)))
  | .inr input => observedPairedHash sk input

/-- A trace of source-level calls, whose cache fields are only the locally observed entries. -/
noncomputable def traceProgram {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) : QueryCache HashSpec →
      OracleComp OracleWorld (α × List QueryRecord × QueryCache HashSpec) :=
  OracleComp.construct (fun value cache => pure (value, [], cache))
    (fun input _ next cache => do
      let first ← (observedRom sk input).run cache
      let last ← next first.1 first.2
      pure (last.1, ⟨input, cache, first.1, first.2⟩ :: last.2.1, last.2.2)) program

theorem traceProgram_pure {α : Type} (sk : Seeded.SecretKey) (value : α) (cache : QueryCache HashSpec) :
    traceProgram sk (pure value) cache = pure (value, [], cache) := rfl

theorem traceProgram_query_bind {α : Type} (sk : Seeded.SecretKey) (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    traceProgram sk (liftM (OracleWorld.query input) >>= next) cache = (do
      let first ← (observedRom sk input).run cache
      let last ← traceProgram sk (next first.1) first.2
      pure (last.1, ⟨input, cache, first.1, first.2⟩ :: last.2.1, last.2.2)) := rfl

theorem run_observedHash_same (input : HashInput) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((observedHash input).run cache)).run cache =
      (fun result => ((result.1, result.2), result.2)) <$>
        (randomOracle (spec := HashSpec) input).run cache := by
  cases hc : cache input with
  | some answer =>
      rw [observedHash, QueryImpl.withCaching_run_some _ hc,
        QueryImpl.withCaching_run_some _ hc]
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | none =>
      rw [observedHash, QueryImpl.withCaching_run_none _ hc]
      simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query]
      change _ <$> (randomOracle (spec := HashSpec) input).run cache = _
      rw [QueryImpl.withCaching_run_none _ hc, Functor.map_map, Functor.map_map]

theorem run_observedPairedHash_same (sk : Seeded.SecretKey) (input : HashInput)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((observedPairedHash sk input).run cache)).run cache =
      (fun result => ((result.1, result.2), result.2)) <$> (pairedHash sk input).run cache := by
  simp only [observedPairedHash, pairedHash, StateT.run_bind, simulateQ_bind, map_bind,
    run_observedHash_same, bind_map_left]
  apply bind_congr
  intro first
  cases hp : decodeCandidateInput sk input with
  | none => simp only [hp, StateT.run_pure, simulateQ_pure, map_pure]
  | some position =>
      simp only [hp, StateT.run_bind, simulateQ_bind, run_observedHash_same, bind_map_left,
        StateT.run_pure, simulateQ_pure, map_bind, map_pure]

theorem run_observedRom_same (sk : Seeded.SecretKey) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((observedRom sk input).run cache)).run cache =
      (fun result => ((result.1, result.2), result.2)) <$> (pairedRom sk input).run cache := by
  cases input with
  | inr input => exact run_observedPairedHash_same sk input cache
  | inl input =>
      simp only [observedRom, StateT.run, simulateQ_map, simulateQ_spec_query, StateT.run_map]
      rfl

/-- With equal initial caches, reification reproduces the exact paired trace and final cache. -/
theorem run_traceProgram_same {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (traceProgram sk program cache)).run cache =
      (fun result => (result, result.2.2)) <$> traceRun (pairedRom sk) program cache := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [traceProgram_pure, traceRun_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind input next ih =>
      simp only [traceProgram_query_bind, traceRun_query_bind, simulateQ_bind, StateT.run_bind,
        run_observedRom_same, bind_map_left, map_bind]
      apply bind_congr
      intro first
      rw [ih]
      simp only [bind_map_left, simulateQ_pure, StateT.run_pure, map_pure]

theorem run'_traceProgram_same {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (traceProgram sk program cache)).run' cache =
      traceRun (pairedRom sk) program cache := by
  rw [StateT.run'_eq, run_traceProgram_same, Functor.map_map]
  exact id_map _

end LeanSphincs.Lifetime.PairedReification
