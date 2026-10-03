import LeanSphincs.SecurityHiddenDeferred

/-! Reification of the finite-table comparison as an ordinary lazy-ROM program. Canonical
coordinates are fixed for this conditional experiment; every other hash query remains an
explicit raw-oracle call, allowing fresh-output and message monitors to use its actual cache. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenOutside
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

abbrev RawWorld (D R : Type) := unifSpec + (D →ₒ R)

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
noncomputable local instance : DecidableEq D := Classical.decEq _
noncomputable local instance : DecidableEq ι := Classical.decEq _

noncomputable def rawImpl : QueryImpl (RawWorld D R) (StateT (Cache D R) ProbComp)
  | .inl draw => (unifFwdImpl (D →ₒ R)) draw
  | .inr bytes => randomOracle (spec := D →ₒ R) bytes

noncomputable def runRaw {α : Type} (computation : OracleComp (RawWorld D R) α) (cache : Cache D R) :
    ProbComp (α × Cache D R) := (simulateQ rawImpl computation).run cache

theorem runRaw_pure {α : Type} (value : α) (cache : Cache D R) :
    runRaw (pure value) cache = pure (value, cache) := rfl

theorem runRaw_private {α : Type} (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (RawWorld D R) α) (cache : Cache D R) :
    runRaw (liftM ((RawWorld D R).query (.inl draw)) >>= next) cache =
      liftM (unifSpec.query draw) >>= fun value => runRaw (next value) cache := by
  simp only [runRaw, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

theorem runRaw_hash {α : Type} (bytes : D)
    (next : R → OracleComp (RawWorld D R) α) (cache : Cache D R) :
    runRaw (liftM ((RawWorld D R).query (.inr bytes)) >>= next) cache =
      outsideRead bytes cache >>= fun result => runRaw (next result.1) result.2 := by
  simp only [runRaw, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rfl

theorem runRaw_map {α β : Type} (f : α → β) (computation : OracleComp (RawWorld D R) α)
    (cache : Cache D R) :
    runRaw (f <$> computation) cache = (fun result => (f result.1, result.2)) <$> runRaw computation cache := by
  simp only [runRaw, simulateQ_map, StateT.run_map]

noncomputable def programStep {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (input : (HiddenRows.SourceSpec D R ι).Domain)
    (next : (HiddenRows.SourceSpec D R ι).Range input → HiddenReveal.Knowledge ι →
      OracleComp (RawWorld D R) (α × Nat)) (known : HiddenReveal.Knowledge ι) :
    OracleComp (RawWorld D R) (α × Nat) :=
  match input with
  | .inl draw => do
      let value ← liftM ((RawWorld D R).query (.inl draw))
      next value known
  | .inr (.inr coordinate) =>
      next (table coordinate) (known.cacheQuery coordinate (table coordinate))
  | .inr (.inl bytes) =>
      let ordinary := do
        let value ← liftM ((RawWorld D R).query (.inr bytes))
        next value known
      match model.parse bytes with
      | none => ordinary
      | some query => match known (model.incoming query.1) with
          | none => (fun result => (result.1, 1 + result.2)) <$> ordinary
          | some canonical =>
              if query.2 = canonical then
                next (model.combine query.1 (table (model.outgoing query.1)))
                  (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1)))
              else ordinary

noncomputable def program {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) :
    HiddenReveal.Knowledge ι → OracleComp (RawWorld D R) (α × Nat) :=
  OracleComp.construct (fun value _ => pure (value, 0))
    (fun input _ next => programStep model table input next) computation

def reorder {α : Type} (result : (α × Nat) × Cache D R) : (α × Cache D R) × Nat :=
  ((result.1.1, result.2), result.1.2)

theorem program_private {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (draw : unifSpec.Domain) (next : unifSpec.Range draw → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) :
    program model table (liftM ((HiddenRows.SourceSpec D R ι).query (.inl draw)) >>= next) known =
      liftM ((RawWorld D R).query (.inl draw)) >>= fun value => program model table (next value) known := rfl

theorem program_reveal {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (coordinate : ι) (next : Digest → OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) :
    program model table (liftM ((HiddenRows.SourceSpec D R ι).query (.inr (.inr coordinate))) >>= next) known =
      program model table (next (table coordinate)) (known.cacheQuery coordinate (table coordinate)) := rfl

theorem program_hash {α : Type} (model : HiddenRows.Model D R A ι) (table : ι → Digest)
    (bytes : D) (next : R → OracleComp (HiddenRows.SourceSpec D R ι) α) (known : HiddenReveal.Knowledge ι) :
    program model table (liftM ((HiddenRows.SourceSpec D R ι).query (.inr (.inl bytes))) >>= next) known =
      (let ordinary := liftM ((RawWorld D R).query (.inr bytes)) >>= fun value => program model table (next value) known
      match model.parse bytes with
      | none => ordinary
      | some query => match known (model.incoming query.1) with
          | none => (fun result => (result.1, 1 + result.2)) <$> ordinary
          | some canonical => if query.2 = canonical then
              program model table (next (model.combine query.1 (table (model.outgoing query.1))))
                (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1)))
            else ordinary) := by
  unfold program
  rw [OracleComp.construct_query_bind]
  rfl

/-- Conditional on the finite table, the common comparison is precisely an ordinary
lazy-cache program. The equality retains the original result, raw cache, and hidden count. -/
theorem fixedComparison_compile_eq_program {α : Type} (model : HiddenRows.Model D R A ι)
    (table : ι → Digest) (computation : OracleComp (HiddenRows.SourceSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    HiddenReveal.fixedComparison table (compile model computation known cache) known =
      reorder <$> runRaw (program model table computation known) cache := by
  induction computation using OracleComp.inductionOn generalizing known cache with
  | pure value => rfl
  | query_bind input next ih =>
      cases input with
      | inl draw =>
          rw [compile_private, HiddenReveal.fixedComparison_private, program_private, runRaw_private, map_bind]
          exact congrArg (fun k => liftM (unifSpec.query draw) >>= k) (funext fun value => ih value known cache)
      | inr input => cases input with
        | inr coordinate =>
            rw [compile_reveal, HiddenReveal.fixedComparison_reveal, program_reveal]
            exact ih _ _ cache
        | inl bytes =>
            rw [compile_hash, program_hash]
            cases hp : model.parse bytes with
            | none =>
                simp only [hp]
                rw [fixedComparison_privateLift_bind, runRaw_hash, map_bind]
                exact congrArg (fun k => outsideRead bytes cache >>= k) (funext fun result => ih result.1 known result.2)
            | some query =>
                simp only [hp]
                cases hk : known (model.incoming query.1) with
                | none =>
                    simp only [hk]
                    rw [HiddenReveal.fixedComparison_guess]
                    simp only [hk, ↓reduceIte]
                    rw [fixedComparison_privateLift_bind, runRaw_map, runRaw_hash, Functor.map_map, map_bind, map_bind]
                    apply congrArg (fun k => outsideRead bytes cache >>= k)
                    funext result
                    rw [ih result.1 known result.2, Functor.map_map]
                    rfl
                | some canonical =>
                    simp only [hk]
                    split_ifs
                    · rw [HiddenReveal.fixedComparison_reveal]
                      exact ih _ _ cache
                    · rw [fixedComparison_privateLift_bind, runRaw_hash, map_bind]
                      exact congrArg (fun k => outsideRead bytes cache >>= k) (funext fun result => ih result.1 known result.2)

/-- Exact common-comparison law as finite hidden-table sampling followed by an ordinary ROM
program. The outside domain itself need not be finite. -/
theorem evalDist_comparison_program {α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (HiddenCost.SourceCostSpec D R ι) α)
    (known : HiddenReveal.Knowledge ι) (cache : Cache D R) :
    𝒟[comparison model computation known cache] =
      𝒟[HiddenReveal.completion known >>= fun table =>
        reorder <$> runRaw (program model table (HiddenCost.erase (HiddenCost.trace computation)) known) cache] := by
  rw [evalDist_comparison_finite_table]
  apply evalDist_bind_congr'
  intro table
  rw [fixedComparison_compile_eq_program]

end LeanSphincs.Security.HiddenOutside
