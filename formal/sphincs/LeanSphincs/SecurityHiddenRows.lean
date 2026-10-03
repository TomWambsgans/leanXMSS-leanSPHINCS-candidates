import LeanSphincs.SecurityHiddenCharge

/-! Generic stopped coupling for an oracle whose canonical rows read one hidden digest
coordinate and expose one successor. Instantiating the parser later keeps all byte layouts
explicit without making the kernel unfold concrete cryptographic types in this proof. -/
open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenRows
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

structure Model (D R A ι : Type) where
  parse : D → Option (A × Digest)
  incoming : A → ι
  outgoing : A → ι
  combine : A → Digest → R

variable {D R A ι : Type} [Fintype ι]
noncomputable local instance : DecidableEq ι := Classical.decEq _


/-- The high half of every canonical answer remains explicit and adversary visible. -/
noncomputable def answer (model : Model D R A ι) (table : (ι → Digest)) (outside : D → R) : D → R :=
  fun bytes => (model.parse bytes).elim (outside bytes) fun query =>
    if query.2 = table (model.incoming query.1) then
      model.combine query.1 (table (model.outgoing query.1))
    else outside bytes

def KnownAgrees (table : (ι → Digest)) (known : (HiddenReveal.Knowledge ι)) : Prop :=
  ∀ coordinate value, known coordinate = some value → table coordinate = value

theorem knownAgrees_completion (known : (HiddenReveal.Knowledge ι)) (table : (ι → Digest)) :
    KnownAgrees (tableExtending known table) known :=
  fun coordinate value hvalue => HiddenReveal.completion_known known coordinate value hvalue table

theorem KnownAgrees.reveal {table : (ι → Digest)} {known : (HiddenReveal.Knowledge ι)} (h : KnownAgrees table known)
    (coordinate : ι) :
    KnownAgrees table (known.cacheQuery coordinate (table coordinate)) := by
  intro other value hvalue
  by_cases heq : other = coordinate
  · subst other
    simpa only [QueryCache.cacheQuery_self, Option.some.injEq] using hvalue
  · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hvalue
    exact h other value hvalue

/-- Privileged disclosures are explicit operations, so honest calls can reveal a signature's
frontier or FORS secret without being mistaken for an adversarial equality guess. -/
abbrev SourceSpec (D R ι : Type) := unifSpec + ((D →ₒ R) + (ι →ₒ Digest))
def IsOrdinary : (SourceSpec D R ι).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

noncomputable def compileStep {α : Type} (model : Model D R A ι) (outside : D → R)
    (source : (SourceSpec D R ι).Domain)
    (next : (SourceSpec D R ι).Range source → (HiddenReveal.Knowledge ι) → OracleComp (HiddenReveal.ViewSpec ι) α)
    (known : (HiddenReveal.Knowledge ι)) : OracleComp (HiddenReveal.ViewSpec ι) α :=
  match source with
      | .inl draw => do
          let value ← liftM ((HiddenReveal.ViewSpec ι).query (.inl draw))
          next value known
      | .inr (.inr coordinate) => do
          let value ← liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inl coordinate)))
          next value (known.cacheQuery coordinate value)
      | .inr (.inl bytes) =>
          match model.parse bytes with
          | none => next (outside bytes) known
          | some query =>
              let address := query.1
              let value := query.2
              match known (model.incoming address) with
              | none => do
                  let _ ← liftM ((HiddenReveal.ViewSpec ι).query
                    (.inr (.inr ((model.incoming address), value))))
                  next (outside bytes) known
              | some canonical =>
                  if value = canonical then do
                    let successor ← liftM ((HiddenReveal.ViewSpec ι).query
                      (.inr (.inl (model.outgoing address))))
                    next (model.combine address successor)
                      (known.cacheQuery (model.outgoing address) successor)
                  else next (outside bytes) known

noncomputable def compile {α : Type} (model : Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) : (HiddenReveal.Knowledge ι) → OracleComp (HiddenReveal.ViewSpec ι) α :=
  OracleComp.construct (fun value _ => pure value)
    (fun source _ next => compileStep model outside source next) computation

/-- Execute the actual programmed oracle, stopping immediately before an ordinary query
guesses any still-hidden canonical input. This is a concrete experiment, not an independence
assumption about the transcript. -/
noncomputable def stoppedStep {α : Type} (model : Model D R A ι)
    (table : (ι → Digest)) (outside : D → R)
    (source : (SourceSpec D R ι).Domain) (next : (SourceSpec D R ι).Range source → (HiddenReveal.Knowledge ι) → ProbComp (Option α))
    (known : (HiddenReveal.Knowledge ι)) : ProbComp (Option α) :=
  match source with
      | .inl draw => do
          let value ← liftM (unifSpec.query draw)
          next value known
      | .inr (.inr coordinate) =>
          next (table coordinate) (known.cacheQuery coordinate (table coordinate))
      | .inr (.inl bytes) =>
          match model.parse bytes with
          | none => next (answer model table outside bytes) known
          | some query =>
              let address := query.1
              let value := query.2
              if known (model.incoming address) = none ∧ value = table (model.incoming address) then
                pure none
              else if value = table (model.incoming address) then
                next (answer model table outside bytes)
                  (known.cacheQuery (model.outgoing address) (table (model.outgoing address)))
              else next (answer model table outside bytes) known

noncomputable def stopped {α : Type} (model : Model D R A ι) (table : (ι → Digest)) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) : (HiddenReveal.Knowledge ι) → ProbComp (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun source _ next => stoppedStep model table outside source next) computation

set_option maxHeartbeats 100000
section Equations
variable {α : Type} (model : Model D R A ι)
  (table : (ι → Digest)) (outside : D → R)
  (known : (HiddenReveal.Knowledge ι))

theorem compile_private (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (SourceSpec D R ι) α) :
    compile model outside (liftM ((SourceSpec D R ι).query (.inl draw)) >>= next) known =
      (liftM ((HiddenReveal.ViewSpec ι).query (.inl draw)) >>= fun value =>
        compile model outside (next value) known) := rfl

theorem compile_reveal (coordinate : ι) (next : Digest → OracleComp (SourceSpec D R ι) α) :
    compile model outside
      (liftM ((SourceSpec D R ι).query (.inr (.inr coordinate))) >>= next) known =
      (liftM ((HiddenReveal.ViewSpec ι).query (.inr (.inl coordinate))) >>= fun value =>
        compile model outside (next value) (known.cacheQuery coordinate value)) := rfl

theorem compile_hash (bytes : D) (next : R → OracleComp (SourceSpec D R ι) α) :
    compile model outside (liftM ((SourceSpec D R ι).query (.inr (.inl bytes))) >>= next) known =
      match model.parse bytes with
      | none => compile model outside (next (outside bytes)) known
      | some query =>
          match known (model.incoming query.1) with
          | none => liftM ((HiddenReveal.ViewSpec ι).query
              (.inr (.inr ((model.incoming query.1), query.2)))) >>= fun _ =>
                compile model outside (next (outside bytes)) known
          | some canonical =>
              if query.2 = canonical then
                liftM ((HiddenReveal.ViewSpec ι).query
                  (.inr (.inl (model.outgoing query.1)))) >>= fun successor =>
                    compile model outside
                      (next (model.combine query.1 successor))
                      (known.cacheQuery (model.outgoing query.1) successor)
              else compile model outside (next (outside bytes)) known := by
  unfold compile
  rw [OracleComp.construct_query_bind]
  dsimp only [compileStep]
  cases hp : model.parse bytes with
  | none => rfl
  | some query =>
      dsimp only
      cases hk : known (model.incoming query.1) with
      | none => rfl
      | some canonical =>
          dsimp only

theorem stopped_private (draw : unifSpec.Domain)
    (next : unifSpec.Range draw → OracleComp (SourceSpec D R ι) α) :
    stopped model table outside (liftM ((SourceSpec D R ι).query (.inl draw)) >>= next) known =
      (liftM (unifSpec.query draw) >>= fun value =>
        stopped model table outside (next value) known) := rfl

theorem stopped_reveal (coordinate : ι) (next : Digest → OracleComp (SourceSpec D R ι) α) :
    stopped model table outside
      (liftM ((SourceSpec D R ι).query (.inr (.inr coordinate))) >>= next) known =
      stopped model table outside (next (table coordinate))
        (known.cacheQuery coordinate (table coordinate)) := rfl

theorem stopped_hash (bytes : D) (next : R → OracleComp (SourceSpec D R ι) α) :
    stopped model table outside (liftM ((SourceSpec D R ι).query (.inr (.inl bytes))) >>= next) known =
      match model.parse bytes with
      | none => stopped model table outside
          (next (answer model table outside bytes)) known
      | some query =>
          if known (model.incoming query.1) = none ∧ query.2 = table (model.incoming query.1) then
            pure none
          else if query.2 = table (model.incoming query.1) then
            stopped model table outside
              (next (answer model table outside bytes))
              (known.cacheQuery (model.outgoing query.1) (table (model.outgoing query.1)))
          else stopped model table outside
            (next (answer model table outside bytes)) known := by
  unfold stopped
  rw [OracleComp.construct_query_bind]
  rfl

end Equations

theorem run_compile {α : Type} (model : Model D R A ι) (table : (ι → Digest)) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) (known : (HiddenReveal.Knowledge ι)) (hknown : KnownAgrees table known) :
    HiddenReveal.run table (compile model outside computation known) known =
      stopped model table outside computation known := by
  induction computation using OracleComp.inductionOn generalizing known with
  | pure value => rfl
  | query_bind source next ih =>
      cases source with
      | inl draw =>
          rw [compile_private, HiddenReveal.run_private, stopped_private]
          congr 1; funext value
          exact ih value known hknown
      | inr source =>
          cases source with
          | inr coordinate =>
              rw [compile_reveal, HiddenReveal.run_reveal, stopped_reveal]
              exact ih (table coordinate) _ (hknown.reveal coordinate)
          | inl bytes =>
              rw [compile_hash, stopped_hash]
              cases hp : model.parse bytes with
              | none =>
                  simp only [hp, answer, Option.elim_none]
                  exact ih _ known hknown
              | some query =>
                  rcases query with ⟨address, value⟩
                  cases hk : known (model.incoming address) with
                  | none =>
                      simp only [hp, hk, HiddenReveal.run_guess, answer, Option.elim_some]
                      by_cases heq : value = table (model.incoming address)
                      · simp [heq]
                      · simp only [heq, Ne.symm heq, and_false, ↓reduceIte]
                        exact ih _ known hknown
                  | some canonical =>
                      have hc := hknown _ _ hk
                      simp only [hp, hk, answer, Option.elim_some, hc,
                        Option.some_ne_none, false_and, ↓reduceIte]
                      by_cases heq : value = canonical
                      · simp only [heq, ↓reduceIte, HiddenReveal.run_reveal]
                        exact ih _ _ (hknown.reveal (model.outgoing address))
                      · simp only [heq, ↓reduceIte]
                        exact ih _ known hknown

theorem compile_queryBound {α : Type} (model : Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) (known : (HiddenReveal.Knowledge ι)) (q : Nat)
    (hbound : computation.IsQueryBoundP (IsOrdinary (R := R)) q) :
    (compile model outside computation known).IsQueryBoundP HiddenReveal.IsGuess q := by
  induction computation using OracleComp.inductionOn generalizing known q with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind source next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      cases source with
      | inl draw =>
          simp only [IsOrdinary, not_false_eq_true, true_or, ↓reduceIte] at hbound
          rw [compile_private, isQueryBoundP_query_bind_iff]
          simp only [HiddenReveal.IsGuess, not_false_eq_true, true_or, ↓reduceIte, true_and]
          exact fun value => ih value known q (hbound.2 value)
      | inr source =>
          cases source with
          | inr coordinate =>
              simp only [IsOrdinary, not_false_eq_true, true_or, ↓reduceIte] at hbound
              rw [compile_reveal, isQueryBoundP_query_bind_iff]
              simp only [HiddenReveal.IsGuess, not_false_eq_true, true_or, ↓reduceIte, true_and]
              exact fun value => ih value _ q (hbound.2 value)
          | inl bytes =>
              simp only [IsOrdinary, not_true_eq_false, false_or, ↓reduceIte] at hbound
              rw [compile_hash]
              cases hp : model.parse bytes with
              | none => exact (ih _ known (q - 1) (hbound.2 _)).mono (Nat.sub_le _ _)
              | some query =>
                  dsimp only
                  cases hk : known (model.incoming query.1) with
                  | none =>
                      dsimp only
                      rw [isQueryBoundP_query_bind_iff]
                      simp only [HiddenReveal.IsGuess, not_true_eq_false, false_or, ↓reduceIte]
                      exact ⟨hbound.1, fun _ => ih _ known (q - 1) (hbound.2 _)⟩
                  | some canonical =>
                      dsimp only
                      split
                      · rw [isQueryBoundP_query_bind_iff]
                        simp only [HiddenReveal.IsGuess, not_false_eq_true, true_or, ↓reduceIte, true_and]
                        exact fun value => (ih _ _ (q - 1) (hbound.2 _)).mono (Nat.sub_le _ _)
                      · exact (ih _ known (q - 1) (hbound.2 _)).mono (Nat.sub_le _ _)

noncomputable def stoppedExperiment {α : Type} (model : Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) (known : (HiddenReveal.Knowledge ι)) : ProbComp (Option α) :=
  HiddenReveal.completion known >>= fun table => stopped model table outside computation known

/-- Literal coupling with the concrete programmed graph, including every ordinary hash
answer up to the first hidden-input guess and every privileged disclosure. -/
theorem stoppedExperiment_eq {α : Type} (model : Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) (known : (HiddenReveal.Knowledge ι)) :
    stoppedExperiment model outside computation known =
      HiddenReveal.experiment (compile model outside computation known) known := by
  simp only [stoppedExperiment, HiddenReveal.experiment, HiddenReveal.completion, bind_map_left]
  congr 1
  funext table
  exact (run_compile model _ outside computation known
    (knownAgrees_completion known table)).symm

theorem stopped_hidden_input_bound_charge {α : Type} (model : Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) (known : (HiddenReveal.Knowledge ι)) :
    Pr[= none | stoppedExperiment model outside computation known] ≤
      HiddenReveal.expectedGuessCharge (compile model outside computation known) known /
        (2 : ℝ≥0∞) ^ 128 := by
  rw [stoppedExperiment_eq]
  exact HiddenReveal.adaptive_guess_bound_charge _ _

theorem stopped_hidden_input_bound {α : Type} (model : Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceSpec D R ι) α) (known : (HiddenReveal.Knowledge ι)) (q : Nat)
    (hbound : computation.IsQueryBoundP (IsOrdinary (R := R)) q) :
    Pr[= none | stoppedExperiment model outside computation known] ≤
      q / (2 : ℝ≥0∞) ^ 128 := by
  rw [stoppedExperiment_eq]
  exact HiddenReveal.adaptive_guess_bound _ _ q
    (compile_queryBound model outside computation known q hbound)


end LeanSphincs.Security.HiddenRows
