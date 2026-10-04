import LeanSphincs.BridgeInterpSupport

/-! Replaying a recorded hash computation: once every answer of a lazily sampled run is cached,
the interpreter returns the same result. Applied to the prepared encoding searches, a failed
final assembly happens only at an index whose prepared search failed. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- A lazily sampled run only grows its cache. -/
theorem randomOracle_run_grows [DecidableEq D] {α : Type} (c : OracleComp (D →ₒ R) α) :
    ∀ (cache0 : QueryCache (D →ₒ R)), ∀ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) c).run cache0),
      ∀ x v, cache0 x = some v → r.2 x = some v := by
  induction c using OracleComp.inductionOn with
  | pure a =>
      intro cache0 r hr x v hx
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]; exact hx
  | query_bind t next ih =>
      intro cache0 r hr x v hx
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at hr
      obtain ⟨a, ha, hr⟩ := Set.mem_iUnion₂.1 hr
      change a ∈ support ((randomOracle (spec := D →ₒ R) t).run cache0) at ha
      cases hc : cache0 t with
      | some u =>
          rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact ih u cache0 r hr x v hx
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc, support_map] at ha
          obtain ⟨u, _, rfl⟩ := ha
          refine ih u _ r hr x v ?_
          by_cases hxt : x = t
          · subst hxt; rw [hc] at hx; cases hx
          · show (cache0.cacheQuery t u) x = some v
            rw [QueryCache.cacheQuery_of_ne _ _ hxt]; exact hx

/-- **Replay.** The interpreter returns the recorded result once all answers are cached. -/
theorem interp_liftHash_replay [DecidableEq D] {α : Type} (c : OracleComp (D →ₒ R) α)
    (hrow : c.IsQueryBoundP (fun x => model.parse x ≠ none) 0) :
    ∀ (cache0 : QueryCache (D →ₒ R)), ∀ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) c).run cache0),
      ∀ budget (s : DebtState D R ι), (∀ x v, r.2 x = some v → s.cache x = some v) →
        ∀ out ∈ support (interp tg initial model (liftM c : OracleComp (SourceCostSpec D R ι) α) budget s),
          ∀ v, out.1.1 = some v → v = r.1 := by
  induction c using OracleComp.inductionOn with
  | pure a =>
      intro cache0 r hr budget s _ out hout v hv
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [liftM_pure, interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout] at hv
      cases hv
      rw [hr]
  | query_bind t next ih =>
      intro cache0 r hr budget s hcache out hout v hv
      rw [isQueryBoundP_query_bind_iff] at hrow
      have hparse : model.parse t = none := by
        rcases hrow.1 with h | h
        · exact Classical.not_not.mp h
        · exact absurd h (lt_irrefl 0)
      have hnext : ∀ u, (next u).IsQueryBoundP (fun x => model.parse x ≠ none) 0 := by
        intro u
        have := hrow.2 u
        split_ifs at this with hq
        · exact absurd hparse hq
        · exact this
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, support_bind] at hr
      obtain ⟨a, ha, hr⟩ := Set.mem_iUnion₂.1 hr
      change a ∈ support ((randomOracle (spec := D →ₒ R) t).run cache0) at ha
      -- the answer and the cache after the query
      have hans : a.2 t = some a.1 := by
        cases hc : cache0 t with
        | some u =>
            rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at ha
            subst ha; exact hc
        | none =>
            rw [QueryImpl.withCaching_run_none _ hc, support_map] at ha
            obtain ⟨u, _, rfl⟩ := ha
            simp
      have hst : s.cache t = some a.1 := hcache t a.1 (randomOracle_run_grows (next a.1) a.2 r hr t a.1 hans)
      rw [liftM_bind] at hout
      change out ∈ support (interp tg initial model
        (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl t)))) >>= fun u => liftM (next u)) budget s) at hout
      rw [interp_ordinary] at hout
      split_ifs at hout with h1
      · rw [ordinaryStep, hparse] at hout
        simp only at hout
        rw [readOutside_cached t s a.1 hst, pure_bind, support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        exact ih a.1 (hnext a.1) a.2 r hr (budget - 1) s hcache o ho v hv
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hv
        cases hv

/-- Every part of a recorded sequence was recorded from some cache, inside the final cache. -/
theorem sequenceFin_parts [DecidableEq D] {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (D →ₒ R) α) (cache0 : QueryCache (D →ₒ R)),
      ∀ res ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) (Concrete.sequenceFin f)).run cache0),
        ∀ i, ∃ c0, ∃ r ∈ support ((simulateQ (randomOracle (spec := D →ₒ R)) (f i)).run c0),
          r.1 = res.1 i ∧ ∀ x v, r.2 x = some v → res.2 x = some v
  | 0, f, cache0, res, _, i => i.elim0
  | n + 1, f, cache0, res, hres, i => by
      unfold Concrete.sequenceFin at hres
      simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hres
      obtain ⟨h, hh, t, ht, rfl⟩ := hres
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨cache0, h, hh, rfl, fun x v hx => randomOracle_run_grows _ _ t ht x v hx⟩
      · obtain ⟨c0, r, hr, h1, h2⟩ := sequenceFin_parts (fun j : Fin n => f j.succ) h.2 t ht j
        exact ⟨c0, r, hr, h1, h2⟩

end LeanSphincs.Security.HiddenDebt
