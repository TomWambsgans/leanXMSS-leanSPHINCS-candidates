import LeanSphincs.SecurityHiddenStopping

/-! The programmed-row compiler with an actual lazy outside random oracle. Raw inputs may
be infinite (in the candidate, arbitrary byte lists). Outside responses are sampled on demand
and cached; no probability distribution over full infinite answer functions is assumed. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenOutside
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

abbrev Cache (D R : Type) := QueryCache (D →ₒ R)

noncomputable def privateLift {ι α : Type} (computation : ProbComp α) :
    OracleComp (HiddenReveal.ViewSpec ι) α :=
  simulateQ (fun draw => liftM ((HiddenReveal.ViewSpec ι).query (.inl draw))) computation

theorem privateLift_pure {ι α : Type} (value : α) :
    privateLift (ι := ι) (pure value) = pure value := rfl

theorem privateLift_bind {ι α β : Type} (computation : ProbComp α) (next : α → ProbComp β) :
    privateLift (ι := ι) (computation >>= next) = privateLift computation >>= fun value => privateLift (next value) :=
  simulateQ_bind _ _ _

theorem run_privateLift_bind {ι α β : Type} [Fintype ι] (table : ι → Digest)
    (computation : ProbComp α) (next : α → OracleComp (HiddenReveal.ViewSpec ι) β)
    (known : HiddenReveal.Knowledge ι) :
    HiddenReveal.run table (privateLift computation >>= next) known =
      computation >>= fun value => HiddenReveal.run table (next value) known := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [privateLift_pure, pure_bind]
  | query_bind draw continuation ih =>
      rw [privateLift, simulateQ_bind, simulateQ_spec_query]
      change HiddenReveal.run table
        ((liftM ((HiddenReveal.ViewSpec ι).query (.inl draw)) >>= fun value => privateLift (continuation value)) >>= next) known = _
      rw [bind_assoc, HiddenReveal.run_private, bind_assoc]
      exact congrArg (fun k => liftM (unifSpec.query draw) >>= k) (funext ih)

section Compiler
variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance : DecidableEq D := Classical.decEq _
noncomputable local instance : DecidableEq ι := Classical.decEq _

noncomputable def outsideRead (input : D) (cache : Cache D R) : ProbComp (R × Cache D R) :=
  (randomOracle (spec := D →ₒ R) input).run cache

noncomputable def compileStep {α : Type} (model : HiddenRows.Model D R A ι)
    (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → HiddenReveal.Knowledge ι →
      Cache D R → OracleComp (HiddenReveal.ViewSpec ι) (α × Cache D R))
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    OracleComp (HiddenReveal.ViewSpec ι) (α × Cache D R) :=
  match input with
  | .inl draw => do
      let value ← liftM ((HiddenReveal.ViewSpec ι).query (.inl draw))
      next value known cache
  | .inr (.inr coordinate) => do
      let value ← liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inl coordinate)))
      next value (known.cacheQuery coordinate value) cache
  | .inr (.inl bytes) =>
      let ordinary := do
        let result ← privateLift (outsideRead bytes cache)
        next result.1 known result.2
      match model.parse bytes with
      | none => ordinary
      | some query => match known (model.incoming query.1) with
          | none => do
              let _ ← liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inr (model.incoming query.1, query.2))))
              ordinary
          | some canonical =>
              if query.2 = canonical then do
                let successor ← liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inl (model.outgoing query.1))))
                next (model.combine query.1 successor)
                  (known.cacheQuery (model.outgoing query.1) successor) cache
              else ordinary

noncomputable def compile {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) :
    HiddenReveal.Knowledge ι → Cache D R → OracleComp (HiddenReveal.ViewSpec ι) (α × Cache D R) :=
  OracleComp.construct (fun value _ cache => pure (value, cache))
    (fun input _ next => compileStep model input next) computation

noncomputable def stoppedStep {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → HiddenReveal.Knowledge ι →
      Cache D R → ProbComp (Option (α × Cache D R)))
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) : ProbComp (Option (α × Cache D R)) :=
  match input with
  | .inl draw => do
      let value ← liftM (unifSpec.query draw)
      next value known cache
  | .inr (.inr coordinate) =>
      next (table coordinate) (known.cacheQuery coordinate (table coordinate)) cache
  | .inr (.inl bytes) =>
      let ordinary := do
        let result ← outsideRead bytes cache
        next result.1 known result.2
      match model.parse bytes with
      | none => ordinary
      | some query =>
          if known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1) then pure none
          else if query.2 = table (model.incoming query.1) then
            next (model.combine query.1 (table (model.outgoing query.1)))
              (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1))) cache
          else ordinary

/-- Actual programmed row evaluation uses the real canonical successor. All noncanonical
inputs use the actual lazy outside cache, and a hidden input match stops before exposure. -/
noncomputable def stopped {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) :
    HiddenReveal.Knowledge ι → Cache D R → ProbComp (Option (α × Cache D R)) :=
  OracleComp.construct (fun value _ cache => pure (some (value, cache)))
    (fun input _ next => stoppedStep model table input next) computation

theorem compile_private {α : Type} (model : HiddenRows.Model D R A ι) (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    compile model (liftM ((HiddenRows.SourceSpec D R ι).query (.inl draw)) >>= next) known cache =
      liftM ((HiddenReveal.ViewSpec ι).query (.inl draw)) >>= fun value => compile model (next value) known cache := rfl

theorem compile_reveal {α : Type} (model : HiddenRows.Model D R A ι) (coordinate : ι)
    (next : Digest → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    compile model (liftM ((HiddenRows.SourceSpec D R ι).query (.inr (.inr coordinate))) >>= next) known cache =
      liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inl coordinate))) >>= fun value =>
        compile model (next value) (known.cacheQuery coordinate value) cache := rfl

theorem compile_hash {α : Type} (model : HiddenRows.Model D R A ι) (bytes : D)
    (next : R → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    compile model (liftM ((HiddenRows.SourceSpec D R ι).query (.inr (.inl bytes))) >>= next) known cache =
      (let ordinary := privateLift (outsideRead bytes cache) >>= fun result =>
        compile model (next result.1) known result.2
      match model.parse bytes with
      | none => ordinary
      | some query => match known (model.incoming query.1) with
          | none => liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inr (model.incoming query.1, query.2)))) >>= fun _ => ordinary
          | some canonical => if query.2 = canonical then
              liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inl (model.outgoing query.1)))) >>= fun successor =>
                compile model (next (model.combine query.1 successor))
                  (known.cacheQuery (model.outgoing query.1) successor) cache
            else ordinary) := by
  unfold compile
  rw [OracleComp.construct_query_bind]
  rfl

theorem run_compile {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) (hagrees : HiddenRows.KnownAgrees table known) :
    HiddenReveal.run table (compile model computation known cache) known =
      stopped model table computation known cache := by
  induction computation using OracleComp.inductionOn generalizing known cache with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl draw =>
          rw [compile_private, HiddenReveal.run_private]
          change (liftM (unifSpec.query draw) >>= _) = liftM (unifSpec.query draw) >>= _
          exact congrArg (fun k => liftM (unifSpec.query draw) >>= k) (funext fun value => ih value known cache hagrees)
      | inr input => cases input with
        | inr coordinate =>
            rw [compile_reveal, HiddenReveal.run_reveal]
            exact ih _ _ cache (hagrees.reveal coordinate)
        | inl bytes =>
            rw [compile_hash]
            change HiddenReveal.run table _ known = stoppedStep model table (.inr (.inl bytes))
              (fun value => stopped model table (next value)) known cache
            unfold stoppedStep
            cases hp : model.parse bytes with
            | none =>
                simp only [hp]
                rw [run_privateLift_bind]
                exact congrArg (fun k => outsideRead bytes cache >>= k) (funext fun result => ih result.1 known result.2 hagrees)
            | some query =>
                simp only [hp]
                cases hk : known (model.incoming query.1) with
                | none =>
                    simp only [hk]
                    rw [HiddenReveal.run_guess]
                    by_cases hh : query.2 = table (model.incoming query.1)
                    · simp [hk, hh]
                    · simp only [hk, hh, Ne.symm hh, true_and, and_false, ↓reduceIte]
                      rw [run_privateLift_bind]
                      exact congrArg (fun k => outsideRead bytes cache >>= k)
                        (funext fun result => ih result.1 known result.2 hagrees)
                | some canonical =>
                    have hc := hagrees (model.incoming query.1) canonical hk
                    simp only [hk, Option.some_ne_none, false_and, ↓reduceIte, hc]
                    split_ifs with heq
                    · rw [HiddenReveal.run_reveal]
                      exact ih _ _ cache (hagrees.reveal (model.outgoing query.1))
                    · rw [run_privateLift_bind]
                      exact congrArg (fun k => outsideRead bytes cache >>= k)
                        (funext fun result => ih result.1 known result.2 hagrees)

noncomputable def stoppedExperiment {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) : ProbComp (Option (α × Cache D R)) :=
  HiddenReveal.completion known >>= fun table => stopped model table computation known cache

theorem stoppedExperiment_eq {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    stoppedExperiment model computation known cache =
      HiddenReveal.experiment (compile model computation known cache) known := by
  simp only [stoppedExperiment, HiddenReveal.experiment, HiddenReveal.completion, bind_map_left]
  congr 1
  funext table
  exact (run_compile model _ computation known cache (HiddenRows.knownAgrees_completion known table)).symm

theorem stop_or_bad_bound {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) (bad : α × Cache D R → Prop) :
    Pr[HiddenReveal.StopOr bad | stoppedExperiment model computation known cache] ≤
      HiddenReveal.comparisonRisk (compile model computation known cache) known bad := by
  rw [stoppedExperiment_eq]
  exact HiddenReveal.stop_or_bad_bound _ _ _

end Compiler
end LeanSphincs.Security.HiddenOutside
