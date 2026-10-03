import LeanSphincs.SecurityHiddenMonitors

/-! Deterministic accounting for hidden-coordinate guesses on the common comparison trace.
The compiler can emit a guess only at a parsed canonical row, and emits at most one there.
This is proved through the actual compiler, not assumed as a query-budget certificate. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenCost
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

/-- Every branch pays its accumulated instruction cost in the terminal credit. -/
def Pays {I : Type} {spec : OracleSpec I} {α : Type} (cost : spec.Domain → Nat)
    (computation : OracleComp spec α) (credit : α → Nat) : Nat → Prop :=
  OracleComp.construct (fun value spent => spent ≤ credit value)
    (fun input _ next spent => ∀ value, next value (spent + cost input)) computation

theorem pays_pure {I : Type} {spec : OracleSpec I} {α : Type} (cost : spec.Domain → Nat)
    (value : α) (credit : α → Nat) (spent : Nat) :
    Pays cost (pure value) credit spent ↔ spent ≤ credit value := Iff.rfl

theorem pays_query_bind {I : Type} {spec : OracleSpec I} {α : Type} (cost : spec.Domain → Nat)
    (input : spec.Domain) (next : spec.Range input → OracleComp spec α)
    (credit : α → Nat) (spent : Nat) :
    Pays cost (liftM (spec.query input) >>= next) credit spent ↔
      ∀ value, Pays cost (next value) credit (spent + cost input) := Iff.rfl

theorem pays_mono {I : Type} {spec : OracleSpec I} {α : Type} (cost : spec.Domain → Nat)
    (computation : OracleComp spec α) (credit credit' : α → Nat) (spent spent' : Nat)
    (hcredit : ∀ value, credit value ≤ credit' value) (hspent : spent' ≤ spent)
    (h : Pays cost computation credit spent) : Pays cost computation credit' spent' := by
  induction computation using OracleComp.inductionOn generalizing spent spent' with
  | pure value => exact hspent.trans (h.trans (hcredit value))
  | query_bind input next ih =>
      exact fun value => ih value _ _ (Nat.add_le_add_right hspent _) (h value)

theorem pays_map {I : Type} {spec : OracleSpec I} {α β : Type} (cost : spec.Domain → Nat)
    (computation : OracleComp spec α) (f : α → β) (credit : β → Nat) (spent : Nat) :
    Pays cost (f <$> computation) credit spent ↔ Pays cost computation (credit ∘ f) spent := by
  induction computation using OracleComp.inductionOn generalizing spent with
  | pure value => simp only [map_pure]; rfl
  | query_bind input next ih =>
      rw [map_bind, pays_query_bind, pays_query_bind]
      exact forall_congr' fun value => ih value _

noncomputable def rowWeight {D R A ι : Type} (model : HiddenRows.Model D R A ι) : Entry D → Nat
  | .inl input => if (model.parse input).isSome then 1 else 0
  | .inr _ => 0

noncomputable def rowSourceCost {D R A ι : Type} (model : HiddenRows.Model D R A ι) :
    (HiddenRows.SourceSpec D R ι).Domain → Nat
  | .inr (.inl input) => if (model.parse input).isSome then 1 else 0
  | _ => 0

noncomputable def rowCost {D R A ι : Type} (model : HiddenRows.Model D R A ι) :
    (SourceCostSpec D R ι).Domain → Nat
  | .inl input => rowSourceCost model input
  | .inr _ => 0

theorem traceCharge_append {D : Type} (weight : Entry D → Nat) (left right : List (Entry D)) :
    traceCharge weight (left ++ right) = traceCharge weight left + traceCharge weight right := by
  simp [traceCharge]

theorem rowCost_recorded {D R A ι : Type} (model : HiddenRows.Model D R A ι)
    (input : (SourceCostSpec D R ι).Domain) :
    traceCharge (rowWeight model) (recorded input) = rowCost model input := by
  cases input with
  | inl input => cases input with
    | inl draw => rfl
    | inr input => cases input <;> simp [traceCharge, recorded, rowCost, rowSourceCost, rowWeight]
  | inr amount => simp [traceCharge, recorded, rowCost, rowWeight]

theorem trace_pays_rows {D R A ι α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (SourceCostSpec D R ι) α) (spent : Nat) :
    Pays (rowCost model) (trace computation)
      (fun result => spent + traceCharge (rowWeight model) result.2) spent := by
  induction computation using OracleComp.inductionOn generalizing spent with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [trace_query_bind, pays_query_bind]
      intro value
      rw [pays_map]
      have h := ih value (spent + rowCost model input)
      convert h using 1
      funext result
      simp only [Function.comp_apply, traceCharge_append, rowCost_recorded]
      omega

theorem erase_pays_rows {D R A ι α : Type} (model : HiddenRows.Model D R A ι)
    (computation : OracleComp (SourceCostSpec D R ι) α) (credit : α → Nat) (spent : Nat)
    (h : Pays (rowCost model) computation credit spent) :
    Pays (rowSourceCost model) (erase computation) credit spent := by
  induction computation using OracleComp.inductionOn generalizing spent with
  | pure value => exact h
  | query_bind input next ih =>
      rw [erase, simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl input =>
          change Pays (rowSourceCost model)
            (liftM ((HiddenRows.SourceSpec D R ι).query input) >>= fun value => erase (next value)) credit spent
          exact fun value => ih value _ (h value)
      | inr amount =>
          change Pays (rowSourceCost model) (pure () >>= fun value => erase (next value)) credit spent
          rw [pure_bind]
          exact ih () spent (h ())

noncomputable def guessCost {ι : Type} : (HiddenReveal.ViewSpec ι).Domain → Nat
  | .inr (.inr _) => 1
  | _ => 0

theorem compile_pays_rows {D R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (known : HiddenReveal.Knowledge ι)
    (credit : α → Nat) (spent : Nat) (h : Pays (rowSourceCost model) computation credit spent) :
    Pays guessCost (HiddenRows.compile model outside computation known) credit spent := by
  induction computation using OracleComp.inductionOn generalizing known spent with
  | pure value => exact h
  | query_bind input next ih =>
      rw [pays_query_bind] at h
      cases input with
      | inl draw =>
          rw [HiddenRows.compile_private, pays_query_bind]
          exact fun value => ih value known spent (h value)
      | inr input => cases input with
        | inr coordinate =>
            rw [HiddenRows.compile_reveal, pays_query_bind]
            exact fun value => ih value _ spent (h value)
        | inl bytes =>
            rw [HiddenRows.compile_hash]
            cases hp : model.parse bytes with
            | none =>
                simp only [hp]
                apply ih _ known spent
                simpa only [rowSourceCost, hp, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
                  Nat.add_zero] using h (outside bytes)
            | some query =>
                simp only [hp]
                have ht (value : R) : Pays (rowSourceCost model) (next value) credit (spent + 1) := by
                  simpa only [rowSourceCost, hp, Option.isSome_some, ↓reduceIte] using h value
                cases hk : known (model.incoming query.1) with
                | none =>
                    simp only [hk]
                    rw [pays_query_bind]
                    exact fun _ => ih _ known (spent + 1) (ht _)
                | some canonical =>
                    simp only [hk]
                    have ht' (value : R) : Pays (rowSourceCost model) (next value) credit spent :=
                      pays_mono _ _ credit credit (spent + 1) spent (fun _ => le_rfl) (Nat.le_succ _) (ht value)
                    split_ifs
                    · rw [pays_query_bind]
                      exact fun successor => ih _ _ spent (ht' _)
                    · exact ih _ known spent (ht' _)

/-- Interpreter support cannot spend more guess instructions than the source trace pays for.
Known-coordinate checks cost zero in the actual comparison, strengthening this bound. -/
theorem revealComparison_pays {ι α : Type} [Fintype ι]
    (computation : OracleComp (HiddenReveal.ViewSpec ι) α) (known : HiddenReveal.Knowledge ι)
    (credit : α → Nat) (spent : Nat) (h : Pays guessCost computation credit spent)
    (result : α × Nat) (hresult : result ∈ support (HiddenReveal.comparison computation known)) :
    spent + result.2 ≤ credit result.1 := by
  induction computation using OracleComp.inductionOn generalizing known spent result with
  | pure value =>
      simp only [HiddenReveal.comparison, OracleComp.construct_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact h
  | query_bind input next ih =>
      rw [pays_query_bind] at h
      cases input with
      | inl draw =>
          rw [HiddenReveal.comparison, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨value, _, htail⟩ := hresult
          exact ih value known spent (h value) result htail
      | inr input => cases input with
        | inl coordinate =>
            rw [HiddenReveal.comparison, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
            obtain ⟨⟨value, known'⟩, _, htail⟩ := hresult
            exact ih value known' spent (h value) result htail
        | inr guess =>
            rw [HiddenReveal.comparison, OracleComp.construct_query_bind, support_map] at hresult
            obtain ⟨tail, htail, rfl⟩ := hresult
            have ht := ih () known (spent + 1) (h ()) tail htail
            split_ifs <;> dsimp only <;> omega

theorem comparison_guess_le_rows {D R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceCostSpec D R ι) α) (known : HiddenReveal.Knowledge ι)
    (result : (α × List (Entry D)) × Nat)
    (hresult : result ∈ support (comparison model outside computation known)) :
    result.2 ≤ traceCharge (rowWeight model) result.1.2 := by
  have htrace := trace_pays_rows model computation 0
  have herase := erase_pays_rows model (trace computation) _ 0 htrace
  have hcompile := compile_pays_rows model outside (erase (trace computation)) known _ 0 herase
  simpa only [Nat.zero_add] using revealComparison_pays _ known _ 0 hcompile result hresult

theorem common_hidden_input_bound {D R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceCostSpec D R ι) α) (known : HiddenReveal.Knowledge ι) :
    Pr[= none | HiddenRows.stoppedExperiment model outside (erase (trace computation)) known] ≤
      expectedTraceCharge (comparison model outside computation known) (fun result => result.1.2)
        (rowWeight model) / (2 : ℝ≥0∞) ^ 128 := by
  refine (HiddenRows.stopped_hidden_input_bound_charge model outside _ known).trans ?_
  simp only [div_eq_mul_inv]
  apply mul_le_mul' _ le_rfl
  unfold HiddenReveal.expectedGuessCharge expectedTraceCharge
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ support (comparison model outside computation known)
  · exact mul_le_mul' le_rfl (by exact_mod_cast comparison_guess_le_rows model outside computation known result hr)
  · change Pr[= result | comparison model outside computation known] * _ ≤ _
    rw [probOutput_eq_zero_of_not_mem_support hr]
    simp

end LeanSphincs.Security.HiddenCost
