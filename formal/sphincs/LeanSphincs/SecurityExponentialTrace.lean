import LeanSphincs.SecurityExponentialCharge

/-! One common query-transition trace for all exponential monitors. Event-specific counts
are deterministic projections, so finite-class union bounds concern a single execution law. -/

namespace LeanSphincs.Security.ExponentialCharge
open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

abbrev QueryRecord := (input : OracleWorld.Domain) ×
  (QueryCache HashSpec × OracleWorld.Range input × QueryCache HashSpec)

def recordCost (record : QueryRecord) : Nat := queryCost record.1

def recordHit (hit : HitTest) (record : QueryRecord) : Nat :=
  if hit record.1 record.2.1 record.2.2.1 record.2.2.2 then 1 else 0

def traceCost (trace : List QueryRecord) : Nat := (trace.map recordCost).sum

def traceHits (hit : HitTest) (trace : List QueryRecord) : Nat := (trace.map (recordHit hit)).sum

noncomputable def traceRun {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (program : OracleComp OracleWorld α) : QueryCache HashSpec → ProbComp (α × List QueryRecord × QueryCache HashSpec) :=
  OracleComp.construct (fun value cache => pure (value, [], cache))
    (fun input _ next cache => do
      let first ← (impl input).run cache
      let last ← next first.1 first.2
      pure (last.1, ⟨input, cache, first.1, first.2⟩ :: last.2.1, last.2.2)) program

theorem traceRun_pure {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (value : α) (cache : QueryCache HashSpec) :
    traceRun impl (pure value) cache = pure (value, [], cache) := rfl

theorem traceRun_query_bind {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    traceRun impl (liftM (OracleWorld.query input) >>= next) cache = (do
      let first ← (impl input).run cache
      let last ← traceRun impl (next first.1) first.2
      pure (last.1, ⟨input, cache, first.1, first.2⟩ :: last.2.1, last.2.2)) := rfl

/-- All monitor choices observe the same latent-cache trace distribution. -/
theorem run_eq_trace_map {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)) (hit : HitTest)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    run impl hit program cache =
      (fun result => (result.1, traceCost result.2.1, traceHits hit result.2.1, result.2.2)) <$>
        traceRun impl program cache := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [run_pure, traceRun_pure, map_pure, traceCost, traceHits,
      List.map_nil, List.sum_nil]
  | query_bind input next ih =>
      simp only [run_query_bind, traceRun_query_bind, map_bind, map_pure]
      apply bind_congr
      intro first
      rw [ih]
      simp only [bind_map_left]
      apply bind_congr
      intro last
      rfl

/-- The common trace also retains the exact source-level hash count. -/
theorem traceRun_erase {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp))
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => ((result.1, traceCost result.2.1), result.2.2)) <$> traceRun impl program cache =
      (simulateQ impl (SeedCoupling.countHashQueries program)).run cache := by
  have h := run_erase impl (fun _ _ _ _ => false) program cache
  rw [run_eq_trace_map, Functor.map_map] at h
  exact h

end LeanSphincs.Security.ExponentialCharge
