import LeanSphincs.SecurityMaterialGameCoupling
import SphincsSecurity.Proof.Base.QueryCapAccounting

/-! Seed-hit loss for the seed-independent material frontend, with virtual derivations retained
in the query budget. The stopped trace argument is adapted from leanVM b7a107256. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.SeedLoss
open SeedModel PreparedScheme MaterialGameCoupling
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000
set_option maxRecDepth 10000
attribute [local irreducible] programCache materialGame experiment
attribute [local instance] Classical.propDecidable

abbrev CostInput := PreparedHashSpec.Domain

def selected (input : PreparedWorld.Domain) : Prop := input matches .inr _

instance : DecidablePred selected := fun input => by unfold selected; infer_instance

def QueryBound {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (q : Nat) : Prop :=
  ∀ result ∈ support ((simulateQ preparedRom (countPreparedQueries computation)).run' cache), result.2 ≤ q

theorem countPreparedQueries_query_bind {α : Type} (input : PreparedWorld.Domain)
    (next : PreparedWorld.Range input → OracleComp PreparedWorld α) :
    countPreparedQueries (liftM (PreparedWorld.query input) >>= next) = (do
      let answer ← liftM (PreparedWorld.query input)
      let result ← countPreparedQueries (next answer)
      pure (result.1, (if selected input then 1 else 0) + result.2)) := rfl

theorem countPreparedQueries_pure {α : Type} (value : α) :
    countPreparedQueries (pure value) = pure (value, 0) := rfl

noncomputable def stopBefore {α : Type} (bad : PreparedWorld.Domain → Prop)
    [DecidablePred bad] (computation : OracleComp PreparedWorld α) :
    OracleComp PreparedWorld (Option α) :=
  OracleComp.construct (fun value => pure (some value))
    (fun input _ next => if bad input then pure none else do
      let answer ← liftM (PreparedWorld.query input)
      next answer) computation

theorem stopBefore_pure {α : Type} (bad : PreparedWorld.Domain → Prop)
    [DecidablePred bad] (value : α) :
    stopBefore bad (pure value) = pure (some value) := rfl

theorem stopBefore_query_bind {α : Type} (bad : PreparedWorld.Domain → Prop)
    [DecidablePred bad] (input : PreparedWorld.Domain)
    (next : PreparedWorld.Range input → OracleComp PreparedWorld α) :
    stopBefore bad (liftM (PreparedWorld.query input) >>= next) =
      (if bad input then pure none else do
        let answer ← liftM (PreparedWorld.query input)
        stopBefore bad (next answer)) := rfl

theorem run'_query_bind {α : Type} (input : PreparedWorld.Domain)
    (next : PreparedWorld.Range input → OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) :
    (simulateQ preparedRom (liftM (PreparedWorld.query input) >>= next)).run' cache =
      ((preparedRom input).run cache >>= fun result =>
        (simulateQ preparedRom (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]

theorem probEvent_stopBefore_le {α : Type} (bad : PreparedWorld.Domain → Prop)
    [DecidablePred bad] (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[fun value => ∃ a, value = some a ∧ event a |
      (simulateQ preparedRom (stopBefore bad computation)).run' cache] ≤
        Pr[event | (simulateQ preparedRom computation).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      split
      · simp
      · simp only [run'_query_bind, probEvent_bind_eq_tsum]
        exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (ih result.1 result.2)

theorem probEvent_le_stopBefore_add_failure {α : Type} (bad : PreparedWorld.Domain → Prop)
    [DecidablePred bad] (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (event : α → Prop) :
    Pr[event | (simulateQ preparedRom computation).run' cache] ≤
      Pr[fun value => ∃ a, value = some a ∧ event a |
        (simulateQ preparedRom (stopBefore bad computation)).run' cache] +
      Pr[= none | (simulateQ preparedRom (stopBefore bad computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      split
      · simp
      · simp only [run'_query_bind, probEvent_bind_eq_tsum, probOutput_bind_eq_tsum,
          ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum fun result =>
          (mul_le_mul' le_rfl (ih result.1 result.2)).trans_eq (mul_add ..)


def hashBad (bad : CostInput → Prop) : PreparedWorld.Domain → Prop
  | .inl _ => False
  | .inr input => bad input

def prependHash (input : PreparedWorld.Domain) (inputs : List CostInput) : List CostInput :=
  match input with
  | .inl _ => inputs
  | .inr input => input :: inputs

noncomputable def traceHashes {α : Type} (computation : OracleComp PreparedWorld α) :
    OracleComp PreparedWorld (α × List CostInput) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let answer ← liftM (PreparedWorld.query input)
      let result ← next answer
      return (result.1, prependHash input result.2)) computation

theorem traceHashes_pure {α : Type} (value : α) :
    traceHashes (pure value) = pure (value, []) := rfl

theorem traceHashes_query_bind {α : Type} (input : PreparedWorld.Domain)
    (next : PreparedWorld.Range input → OracleComp PreparedWorld α) :
    traceHashes (liftM (PreparedWorld.query input) >>= next) = (do
      let answer ← liftM (PreparedWorld.query input)
      let result ← traceHashes (next answer)
      return (result.1, prependHash input result.2)) := rfl

theorem traceHashes_length {α : Type} (computation : OracleComp PreparedWorld α) :
    (fun result => (result.1, result.2.length)) <$> traceHashes computation =
      countPreparedQueries computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [traceHashes_query_bind, countPreparedQueries_query_bind, map_bind, map_pure]
      congr 1
      funext answer
      rw [← ih answer]
      simp only [bind_pure_comp, Functor.map_map]
      congr 1
      funext result
      cases input <;> simp [prependHash, Nat.add_comm, selected]

theorem traceHashes_length_le {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : QueryBound computation cache q)
    (result : α × List CostInput)
    (hresult : result ∈ support ((simulateQ preparedRom (traceHashes computation)).run' cache)) :
    result.2.length ≤ q := by
  apply hbound (result.1, result.2.length)
  rw [← traceHashes_length, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, support_map]
  rw [StateT.run'_eq, support_map] at hresult
  obtain ⟨record, hrecord, rfl⟩ := hresult
  exact ⟨record, hrecord, rfl⟩

def TraceHits (bad : CostInput → Prop) (inputs : List CostInput) : Prop :=
  ∃ input ∈ inputs, bad input

theorem traceHits_prepend (bad : CostInput → Prop) (input : PreparedWorld.Domain)
    (inputs : List CostInput) :
    TraceHits bad (prependHash input inputs) ↔ hashBad bad input ∨ TraceHits bad inputs := by
  cases input <;> simp [TraceHits, prependHash, hashBad]

theorem probOutput_stopBefore_none {α : Type} (bad : CostInput → Prop) [DecidablePred bad]
    (computation : OracleComp PreparedWorld α) (cache : QueryCache HashSpec) :
    Pr[= none | (simulateQ preparedRom (stopBefore (hashBad bad) computation)).run' cache] =
      Pr[fun result => TraceHits bad result.2 |
        (simulateQ preparedRom (traceHashes computation)).run' cache] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp [stopBefore_pure, traceHashes_pure, TraceHits]
  | query_bind input next ih =>
      rw [stopBefore_query_bind, traceHashes_query_bind]
      by_cases hbad : hashBad bad input
      · rw [if_pos hbad, run'_query_bind]
        simp [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map]
        intro a b answer cache' _ a' inputs cache'' _ _ hb
        rw [← hb, traceHits_prepend]
        exact Or.inl hbad
      · rw [if_neg hbad, run'_query_bind, run'_query_bind]
        simp only [probOutput_bind_eq_tsum, probEvent_bind_eq_tsum]
        apply tsum_congr
        intro result
        rw [ih result.1 result.2]
        simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
          Functor.map_map, probEvent_map, Function.comp_def, traceHits_prepend, hbad, false_or]


/-- Virtual derivations count but cannot name a master seed. -/
def entryHit : CostInput → MasterSeed → Prop
  | .inl input => SeedGuess.SeedHit input
  | .inr _ => fun _ => False

theorem entryHit_probability_le (input : CostInput) :
    Pr[entryHit input | sampleMasterSeed] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  cases input with
  | inl input => exact SeedGuess.seedHit_probability_le input
  | inr input => simp [entryHit]

theorem traceHits_probability_le (inputs : List CostInput) :
    Pr[fun seed => TraceHits (fun input => entryHit input seed) inputs | sampleMasterSeed] ≤
      (inputs.length : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  induction inputs with
  | nil => simp [TraceHits]
  | cons input inputs ih =>
      have hevent : (fun seed => TraceHits (fun input => entryHit input seed) (input :: inputs)) =
          fun seed => entryHit input seed ∨ TraceHits (fun input => entryHit input seed) inputs := by
        funext seed
        simp [TraceHits]
      rw [hevent]
      calc
        _ ≤ Pr[entryHit input | sampleMasterSeed] +
            Pr[fun seed => TraceHits (fun input => entryHit input seed) inputs | sampleMasterSeed] :=
          probEvent_or_le _ _ _
        _ ≤ 1 / (2 : ℝ≥0∞) ^ 256 + (inputs.length : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 :=
          add_le_add (entryHit_probability_le input) ih
        _ = _ := by simp [List.length_cons, Nat.cast_add, ENNReal.add_div, add_comm]

/-- Adaptive ordinary hashes, private draws and virtual derivations are included in the trace;
only ordinary hashes can hit the independently sampled master seed. -/
theorem probOutput_stopBefore_seed_le {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : QueryBound computation cache q) :
    Pr[= none | sampleMasterSeed >>= fun seed =>
      (simulateQ preparedRom (stopBefore (hashBad (fun input => entryHit input seed)) computation)).run' cache] ≤
        q / (2 : ℝ≥0∞) ^ 256 := by
  let trace := (simulateQ preparedRom (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleMasterSeed >>= fun seed =>
        (fun result => decide (TraceHits (fun input => entryHit input seed) result.2)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, probOutput_stopBefore_none, probOutput_map, decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun seed => decide (TraceHits (fun input => entryHit input seed) result.2)) <$> sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ _ := by
      rw [← probEvent_eq_eq_probOutput]
      apply probEvent_bind_le_of_forall_le
      intro result hresult
      simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
      exact (traceHits_probability_le result.2).trans
        (ENNReal.div_le_div
          (by exact_mod_cast traceHashes_length_le computation cache q hbound result hresult) le_rfl)

/-- A syntactic bound always gives the corresponding semantic bound in this stateful ROM. -/
theorem queryBound_of_isQueryBound {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (q : Nat) (hbound : computation.IsQueryBoundP selected q) :
    QueryBound computation cache q := by
  intro result hresult
  exact SphincsSecurity.QueryCap.counted_le_of_queryBound selected computation q hbound result
    (support_simulateQ_run'_subset preparedRom (countPreparedQueries computation) cache hresult)

noncomputable def cap {α : Type} (computation : OracleComp PreparedWorld α) (q : Nat) :
    OracleComp PreparedWorld (Option (α × Nat)) := SphincsSecurity.QueryCap.run selected computation q

theorem cap_queryBound {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (q : Nat) : QueryBound (cap computation q) cache q :=
  queryBound_of_isQueryBound _ _ _ (SphincsSecurity.QueryCap.run_queryBound selected computation q)

/-- The cap supplies its budget under the independent cache without transferring an unproved
budget assumption from the seed-dependent cache. -/
theorem capped_seed_hit_bound {α : Type} (computation : OracleComp PreparedWorld α)
    (cache : QueryCache HashSpec) (q : Nat) :
    Pr[= none | sampleMasterSeed >>= fun seed =>
      (simulateQ preparedRom (stopBefore (hashBad (fun input => entryHit input seed))
        (cap computation q))).run' cache] ≤ q / (2 : ℝ≥0∞) ^ 256 :=
  probOutput_stopBefore_seed_le _ _ _ (cap_queryBound computation cache q)

theorem agreeOutside_cacheQuery {seed : MasterSeed} {left right : QueryCache HashSpec}
    (h : AgreeOutsideSeed seed left right) (input : HashInput) (answer : HashOutput) :
    AgreeOutsideSeed seed (left.cacheQuery input answer) (right.cacheQuery input answer) := by
  intro other hother
  by_cases heq : other = input
  · subst other; simp
  · simpa only [QueryCache.cacheQuery_of_ne _ _ heq] using h other hother

/-- The stopped material frontend has identical output on caches differing only at the seed. -/
theorem run'_stopBefore_seed_eq {α : Type} (seed : MasterSeed)
    (computation : OracleComp PreparedWorld α) (left right : QueryCache HashSpec)
    (h : AgreeOutsideSeed seed left right) :
    (simulateQ preparedRom (stopBefore (hashBad (fun input => entryHit input seed)) computation)).run' left =
      (simulateQ preparedRom (stopBefore (hashBad (fun input => entryHit input seed)) computation)).run' right := by
  induction computation using OracleComp.inductionOn generalizing left right with
  | pure value => simp [stopBefore_pure]
  | query_bind input next ih =>
      rw [stopBefore_query_bind]
      by_cases hbad : hashBad (fun input => entryHit input seed) input
      · simp only [if_pos hbad, simulateQ_pure]
        rfl
      · simp only [if_neg hbad, run'_query_bind]
        cases input with
        | inl input =>
            dsimp [PreparedWorld] at next ih ⊢
            change ((fun answer => (answer, left)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _) =
              ((fun answer => (answer, right)) <$> (liftM (unifSpec.query input) : ProbComp _) >>= _)
            simp only [bind_map_left]
            apply bind_congr
            intro answer
            exact ih answer left right h
        | inr input =>
            cases input with
            | inl input =>
                dsimp [PreparedWorld, PreparedHashSpec] at next ih ⊢
                change ((randomOracle input).run left >>= _) = ((randomOracle input).run right >>= _)
                have heq := h input hbad
                cases hleft : left input with
                | none =>
                    have hright : right input = none := heq.symm.trans hleft
                    rw [QueryImpl.withCaching_run_none _ hleft, QueryImpl.withCaching_run_none _ hright]
                    simp only [bind_map_left]
                    apply bind_congr
                    intro answer
                    exact ih answer _ _ (agreeOutside_cacheQuery h input answer)
                | some answer =>
                    have hright : right input = some answer := heq.symm.trans hleft
                    rw [QueryImpl.withCaching_run_some _ hleft, QueryImpl.withCaching_run_some _ hright]
                    simp only [pure_bind]
                    exact ih answer left right h
            | inr input =>
                change (pure ((), left) >>= _) = (pure ((), right) >>= _)
                simp only [pure_bind]
                exact ih () left right h

theorem probEvent_cache_change_le {α : Type} (seed : MasterSeed)
    (computation : OracleComp PreparedWorld α) (left right : QueryCache HashSpec)
    (h : AgreeOutsideSeed seed left right) (event : α → Prop) :
    Pr[event | (simulateQ preparedRom computation).run' left] ≤
      Pr[event | (simulateQ preparedRom computation).run' right] +
      Pr[= none | (simulateQ preparedRom
        (stopBefore (hashBad (fun input => entryHit input seed)) computation)).run' right] := by
  have hbound := probEvent_le_stopBefore_add_failure
    (hashBad (fun input => entryHit input seed)) computation left event
  rw [run'_stopBefore_seed_eq seed computation left right h] at hbound
  exact hbound.trans (add_le_add
    (probEvent_stopBefore_le _ computation right event) le_rfl)

/-- Generic cache-change bound for a seed-independent program with its budget justified under
the independent cache. A capped program always supplies this hypothesis. -/
theorem probEvent_random_cache_change_le {α : Type} (computation : OracleComp PreparedWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutsideSeed seed (initial seed) cache)
    (q : Nat) (hbound : QueryBound computation cache q) (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun seed => (simulateQ preparedRom computation).run' (initial seed)] ≤
      Pr[event | (simulateQ preparedRom computation).run' cache] + q / (2 : ℝ≥0∞) ^ 256 := by
  let stopped := fun seed =>
    (simulateQ preparedRom (stopBefore (hashBad (fun input => entryHit input seed)) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleMasterSeed >>= fun _ => (simulateQ preparedRom computation).run' cache] +
        Pr[= none | sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le seed computation (initial seed) cache
          (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add
        (le_refl (Pr[event | (simulateQ preparedRom computation).run' cache]))
        (probOutput_stopBefore_seed_le computation cache q hbound)

/-- Generic cap/complete-count equality after discarding the final cache; applies to arbitrary
stateful probabilistic interpreters, with no assumption about independence of their state. -/
theorem evalDist_run_cap {I S α : Type} {spec : OracleSpec I}
    (predicate : I → Prop) [DecidablePred predicate] (impl : QueryImpl spec (StateT S ProbComp))
    (computation : OracleComp spec α) (budget : Nat) (state : S) :
    𝒟[Prod.fst <$> (simulateQ impl (SphincsSecurity.QueryCap.run predicate computation budget)).run state] =
      𝒟[(fun result => SphincsSecurity.QueryCap.finish budget result.1) <$>
        (simulateQ impl (SphincsSecurity.QueryCap.counted predicate computation)).run state] := by
  induction computation using OracleComp.inductionOn generalizing budget state with
  | pure result =>
      simp only [SphincsSecurity.QueryCap.run_pure, SphincsSecurity.QueryCap.counted_pure,
        simulateQ_pure, StateT.run_pure, map_pure, SphincsSecurity.QueryCap.finish,
        Nat.zero_le, if_true, Nat.sub_zero]
  | query_bind input next ih =>
      rw [SphincsSecurity.QueryCap.run_query_bind, SphincsSecurity.QueryCap.counted_query_bind]
      by_cases hs : predicate input
      · rw [if_pos hs]
        cases budget with
        | zero =>
            apply evalDist_ext
            intro result
            simp [simulateQ_bind, StateT.run_bind,
              SphincsSecurity.QueryCap.finish, hs]
            trans Pr[= result | (impl input).run state >>= fun _ => pure none]
            · simp
            · apply probOutput_bind_congr'
              intro middle
              simp
        | succ budget =>
            simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure,
              StateT.run_pure, map_bind, map_pure]
            apply evalDist_bind_congr'
            intro middle
            rw [ih middle.1 budget middle.2]
            simp only [bind_pure_comp, SphincsSecurity.QueryCap.finish, hs, if_true,
              Nat.add_comm 1, Nat.add_le_add_iff_right, Nat.add_sub_add_right]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          simulateQ_pure, StateT.run_pure, map_bind, map_pure]
        apply evalDist_bind_congr'
        intro middle
        rw [ih middle.1 budget middle.2]
        simp only [bind_pure_comp, SphincsSecurity.QueryCap.finish, Nat.zero_add]


/-- A cap succeeds only when the original computation wins within its allowed total cost. -/
def CapWin (result : Option (Bool × Nat)) : Prop :=
  ∃ remaining, result = some (true, remaining)

theorem capWin_finish (budget : Nat) (result : Bool × Nat) :
    CapWin (SphincsSecurity.QueryCap.finish budget result) ↔
      result.1 = true ∧ result.2 ≤ budget := by
  unfold SphincsSecurity.QueryCap.finish CapWin
  split <;> simp_all

theorem probEvent_cap (computation : OracleComp PreparedWorld Bool)
    (cache : QueryCache HashSpec) (q : Nat) :
    Pr[CapWin | (simulateQ preparedRom (cap computation q)).run' cache] =
      Pr[fun result => result.1 = true ∧ result.2 ≤ q |
        (simulateQ preparedCountedOracle computation).run.run' cache] := by
  have h := evalDist_run_cap selected preparedRom computation q cache
  change 𝒟[(simulateQ preparedRom (cap computation q)).run' cache] =
    𝒟[(fun result => SphincsSecurity.QueryCap.finish q result.1) <$>
      (simulateQ preparedRom (countPreparedQueries computation)).run cache] at h
  rw [simulateQ_countPreparedQueries] at h
  have hp := probEvent_congr' (p := CapWin) (q := CapWin) (fun _ _ => Iff.rfl) h
  simp only [StateT.run'_eq, probEvent_map, Function.comp_def, capWin_finish] at hp ⊢
  exact hp

/-- Only complete ordinary derivation inputs consume the seed-guess charge. -/
noncomputable def entryCharge : CostInput → Nat
  | .inl input => if (SeedGuess.parseSeed input).isSome then 1 else 0
  | .inr _ => 0

@[simp] theorem entryCharge_virtual (input : Unit) : entryCharge (.inr input) = 0 := rfl

@[simp] theorem entryCharge_verifier (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    entryCharge (.inl (tweakableHashInput parameter domain payload)) = 0 := by
  simp [entryCharge, SeedGuess.parseSeed_verifier]

@[simp] theorem entryCharge_keygen (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : entryCharge (.inl (keygenHashInput parameter domain seed)) = 1 := by
  simp [entryCharge, SeedGuess.parseSeed_keygen]

theorem entryCharge_le_one (input : CostInput) : entryCharge input ≤ 1 := by
  cases input <;> simp [entryCharge]
  split <;> omega

theorem entryHit_probability_le_charge (input : CostInput) :
    Pr[entryHit input | sampleMasterSeed] ≤ (entryCharge input : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  cases input with
  | inr input => simp [entryHit]
  | inl input =>
      cases hp : SeedGuess.parseSeed input with
      | some seed => simpa only [entryCharge, hp, Option.isSome_some, ↓reduceIte, Nat.cast_one, entryHit] using SeedGuess.seedHit_probability_le input
      | none =>
          have hevent : entryHit (.inl input) = fun _ => False := by
            funext seed
            apply propext
            constructor
            · intro h
              have heq := (SeedGuess.parseSeed_eq_some_iff input seed).2 h
              rw [hp] at heq
              cases heq
            · exact False.elim
          simp [hevent, entryCharge, hp]

noncomputable def traceCharge (inputs : List CostInput) : Nat :=
  (inputs.map entryCharge).sum

theorem traceCharge_le_length (inputs : List CostInput) : traceCharge inputs ≤ inputs.length := by
  induction inputs with
  | nil => simp [traceCharge]
  | cons input inputs ih =>
      simpa [traceCharge, Nat.add_comm] using Nat.add_le_add (entryCharge_le_one input) ih

theorem traceHits_probability_le_charge (inputs : List CostInput) :
    Pr[fun seed => TraceHits (fun input => entryHit input seed) inputs | sampleMasterSeed] ≤
      (traceCharge inputs : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  induction inputs with
  | nil => simp [TraceHits, traceCharge]
  | cons input inputs ih =>
      have hevent : (fun seed => TraceHits (fun input => entryHit input seed) (input :: inputs)) =
          fun seed => entryHit input seed ∨ TraceHits (fun input => entryHit input seed) inputs := by
        funext seed
        simp [TraceHits]
      rw [hevent]
      calc
        _ ≤ Pr[entryHit input | sampleMasterSeed] +
            Pr[fun seed => TraceHits (fun input => entryHit input seed) inputs | sampleMasterSeed] :=
          probEvent_or_le _ _ _
        _ ≤ (entryCharge input : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 +
            (traceCharge inputs : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 :=
          add_le_add (entryHit_probability_le_charge input) ih
        _ = _ := by simp [traceCharge, Nat.cast_add, ENNReal.add_div]

/-- Expected ordinary derivation-domain calls; verifier calls and privileged ticks contribute
zero. This is evaluated under the seed-independent cache and program. -/
noncomputable def expectedDerivationQueries {α : Type}
    (computation : OracleComp PreparedWorld α) (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∑' result, Pr[= result | (simulateQ preparedRom (traceHashes computation)).run' cache] *
    (traceCharge result.2 : ℝ≥0∞)

/-- The seed-hit loss charges only derivation-domain queries in the adaptive ordinary trace. -/
theorem probOutput_stopBefore_seed_le_charge {α : Type}
    (computation : OracleComp PreparedWorld α) (cache : QueryCache HashSpec) :
    Pr[= none | sampleMasterSeed >>= fun seed =>
      (simulateQ preparedRom (stopBefore (hashBad (fun input => entryHit input seed)) computation)).run' cache] ≤
        expectedDerivationQueries computation cache / (2 : ℝ≥0∞) ^ 256 := by
  let trace := (simulateQ preparedRom (traceHashes computation)).run' cache
  calc
    _ = Pr[= true | sampleMasterSeed >>= fun seed =>
        (fun result => decide (TraceHits (fun input => entryHit input seed) result.2)) <$> trace] := by
      simp only [probOutput_bind_eq_tsum, probOutput_stopBefore_none, probOutput_map, decide_eq_true_eq]
      rfl
    _ = Pr[= true | trace >>= fun result =>
        (fun seed => decide (TraceHits (fun input => entryHit input seed) result.2)) <$> sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ ∑' result, Pr[= result | trace] *
        ((traceCharge result.2 : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256) := by
      simp only [probOutput_bind_eq_tsum, probOutput_map, decide_eq_true_eq]
      exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl
        (traceHits_probability_le_charge result.2)
    _ = _ := by
      simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right,
        expectedDerivationQueries, trace]

theorem expectedDerivationQueries_le {α : Type}
    (computation : OracleComp PreparedWorld α) (cache : QueryCache HashSpec)
    (q : Nat) (hbound : QueryBound computation cache q) :
    expectedDerivationQueries computation cache ≤ q := by
  unfold expectedDerivationQueries
  calc
    _ ≤ ∑' result, Pr[= result | (simulateQ preparedRom (traceHashes computation)).run' cache] *
        (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ preparedRom (traceHashes computation)).run' cache)
      · apply mul_le_mul' le_rfl
        exact_mod_cast (traceCharge_le_length result.2).trans
          (traceHashes_length_le computation cache q hbound result hr)
      · rw [probOutput_eq_zero_of_not_mem_support hr]
        simp
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

/-- Cache replacement with a charge restricted to ordinary derivation-domain inputs. -/
theorem probEvent_random_cache_change_le_charge {α : Type}
    (computation : OracleComp PreparedWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutsideSeed seed (initial seed) cache) (event : α → Prop) :
    Pr[event | sampleMasterSeed >>= fun seed => (simulateQ preparedRom computation).run' (initial seed)] ≤
      Pr[event | (simulateQ preparedRom computation).run' cache] +
        expectedDerivationQueries computation cache / (2 : ℝ≥0∞) ^ 256 := by
  let stopped := fun seed =>
    (simulateQ preparedRom (stopBefore (hashBad (fun input => entryHit input seed)) computation)).run' cache
  calc
    _ ≤ Pr[event | sampleMasterSeed >>= fun _ => (simulateQ preparedRom computation).run' cache] +
        Pr[= none | sampleMasterSeed >>= stopped] := by
      simp only [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum fun seed =>
        (mul_le_mul' le_rfl (probEvent_cache_change_le seed computation (initial seed) cache
          (hagree seed) event)).trans_eq (mul_add ..)
    _ ≤ _ := by
      simpa [stopped] using add_le_add
        (le_refl (Pr[event | (simulateQ preparedRom computation).run' cache]))
        (probOutput_stopBefore_seed_le_charge computation cache)

/-- Complementary cost: every verifier-domain call and virtual derivation tick, plus malformed
ordinary inputs. Together with the seed charge this is exactly the original total cost. -/
noncomputable def expectedOtherQueries {α : Type}
    (computation : OracleComp PreparedWorld α) (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∑' result, Pr[= result | (simulateQ preparedRom (traceHashes computation)).run' cache] *
    ((result.2.length - traceCharge result.2 : Nat) : ℝ≥0∞)

theorem expected_partition_le {α : Type}
    (computation : OracleComp PreparedWorld α) (cache : QueryCache HashSpec)
    (q : Nat) (hbound : QueryBound computation cache q) :
    expectedDerivationQueries computation cache + expectedOtherQueries computation cache ≤ q := by
  unfold expectedDerivationQueries expectedOtherQueries
  rw [← ENNReal.tsum_add]
  calc
    _ = ∑' result, Pr[= result | (simulateQ preparedRom (traceHashes computation)).run' cache] *
        (result.2.length : ℝ≥0∞) := by
      apply tsum_congr
      intro result
      rw [← mul_add, ← Nat.cast_add, Nat.add_sub_of_le (traceCharge_le_length result.2)]
    _ ≤ ∑' result, Pr[= result | (simulateQ preparedRom (traceHashes computation)).run' cache] *
        (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support ((simulateQ preparedRom (traceHashes computation)).run' cache)
      · apply mul_le_mul' le_rfl
        exact_mod_cast traceHashes_length_le computation cache q hbound result hr
      · rw [probOutput_eq_zero_of_not_mem_support hr]
        simp
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

variable [Params]

/-- Independent material, private signer randomizers and a shared lazy ROM; the cap counts both
ordinary hash calls and privileged derivation ticks. -/
noncomputable def cappedMaterialExperiment (adversary : Adversary) (q : Nat) :
    ProbComp (Option (Bool × Nat)) := do
  let material ← sampleMaterial
  (simulateQ preparedRom (cap (materialGame material adversary) q)).run' ∅

/-- The actual SUF-CMA advantage equals its capped material experiment on the programmed cache.
The cost assumption is used only under the actual experiment where it was supplied. -/
theorem forgeAdvantage_eq_programmed_cap (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary = Pr[CapWin | do
      let material ← sampleMaterial
      let seed ← sampleMasterSeed
      (simulateQ preparedRom (cap (materialGame material adversary) q)).run'
        (programCache ∅ seed material)] := by
  unfold forgeAdvantage
  calc
    _ = Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] :=
      probEvent_congr' (fun result hresult => by
        constructor
        · intro h; exact ⟨h, hbound result hresult⟩
        · exact And.left) rfl
    _ = _ := by
      rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_experiment_material adversary)]
      simp only [probEvent_bind_eq_tsum]
      apply tsum_congr
      intro material
      congr 1
      apply tsum_congr
      intro seed
      rw [probEvent_cap]
      rfl

/-- Concrete reduction from the real seeded game to the seed-independent capped material game.
No independence of honest seed-bearing oracle inputs is assumed: they were substituted by the
privileged compiler, while ordinary queries stop before guessing the seed. -/
theorem forgeAdvantage_le_cappedMaterial (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary ≤
      Pr[CapWin | cappedMaterialExperiment adversary q] + q / (2 : ℝ≥0∞) ^ 256 := by
  rw [forgeAdvantage_eq_programmed_cap adversary q hbound]
  unfold cappedMaterialExperiment
  apply probEvent_bind_congr_le_add
  intro material _
  exact probEvent_random_cache_change_le (cap (materialGame material adversary) q)
    (fun seed => programCache ∅ seed material) ∅
    (fun seed => programCache_agreeOutside ∅ seed material) q
    (cap_queryBound _ _ _) CapWin

/-- Average derivation-domain charge in the independent capped material game. -/
noncomputable def materialDerivationQueries (adversary : Adversary) (q : Nat) : ℝ≥0∞ :=
  ∑' material, Pr[= material | sampleMaterial] *
    expectedDerivationQueries (cap (materialGame material adversary) q) ∅

theorem materialDerivationQueries_le (adversary : Adversary) (q : Nat) :
    materialDerivationQueries adversary q ≤ q := by
  unfold materialDerivationQueries
  calc
    _ ≤ ∑' material, Pr[= material | sampleMaterial] * (q : ℝ≥0∞) := by
      exact ENNReal.tsum_le_tsum fun material => mul_le_mul' le_rfl
        (expectedDerivationQueries_le _ _ q (cap_queryBound _ _ _))
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

/-- Sharper real-game reduction: only ordinary derivation-domain calls pay the seed-guess loss.
This allows a shared query budget to assign verifier-domain calls to their own security events. -/
theorem forgeAdvantage_le_cappedMaterial_charge (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) :
    forgeAdvantage adversary ≤ Pr[CapWin | cappedMaterialExperiment adversary q] +
      materialDerivationQueries adversary q / (2 : ℝ≥0∞) ^ 256 := by
  rw [forgeAdvantage_eq_programmed_cap adversary q hbound]
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' material, Pr[= material | sampleMaterial] *
        (Pr[CapWin | (simulateQ preparedRom (cap (materialGame material adversary) q)).run' ∅] +
          expectedDerivationQueries (cap (materialGame material adversary) q) ∅ /
            (2 : ℝ≥0∞) ^ 256) := by
      exact ENNReal.tsum_le_tsum fun material => mul_le_mul' le_rfl
        (probEvent_random_cache_change_le_charge (cap (materialGame material adversary) q)
          (fun seed => programCache ∅ seed material) ∅
          (fun seed => programCache_agreeOutside ∅ seed material) CapWin)
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, div_eq_mul_inv, ← mul_assoc,
        ENNReal.tsum_mul_right, materialDerivationQueries, cappedMaterialExperiment,
        probEvent_bind_eq_tsum]

noncomputable def materialOtherQueries (adversary : Adversary) (q : Nat) : ℝ≥0∞ :=
  ∑' material, Pr[= material | sampleMaterial] *
    expectedOtherQueries (cap (materialGame material adversary) q) ∅

/-- The two domain charges share the one original total-hash budget. -/
theorem material_partition_le (adversary : Adversary) (q : Nat) :
    materialDerivationQueries adversary q + materialOtherQueries adversary q ≤ q := by
  unfold materialDerivationQueries materialOtherQueries
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' material, Pr[= material | sampleMaterial] * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro material
      rw [← mul_add]
      exact mul_le_mul' le_rfl (expected_partition_le _ _ q (cap_queryBound _ _ _))
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

/-- A remaining, explicitly assumed material-game bound at the complementary domain charge
suffices for the requested rate. This theorem only handles the seeded-to-material reduction. -/
theorem forgeAdvantage_le_of_material_charge (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q)
    (hmaterial : Pr[CapWin | cappedMaterialExperiment adversary q] ≤
      materialOtherQueries adversary q / (2 : ℝ≥0∞) ^ 127) :
    forgeAdvantage adversary ≤ q / (2 : ℝ≥0∞) ^ 127 := by
  calc
    _ ≤ Pr[CapWin | cappedMaterialExperiment adversary q] +
        materialDerivationQueries adversary q / (2 : ℝ≥0∞) ^ 256 :=
      forgeAdvantage_le_cappedMaterial_charge adversary q hbound
    _ ≤ materialOtherQueries adversary q / (2 : ℝ≥0∞) ^ 127 +
        materialDerivationQueries adversary q / (2 : ℝ≥0∞) ^ 127 := by
      exact add_le_add hmaterial (ENNReal.div_le_div le_rfl (by norm_num))
    _ = (materialDerivationQueries adversary q + materialOtherQueries adversary q) /
        (2 : ℝ≥0∞) ^ 127 := by rw [ENNReal.add_div, add_comm]
    _ ≤ _ := ENNReal.div_le_div (material_partition_le adversary q) le_rfl

end LeanSphincs.Security.SeedLoss
