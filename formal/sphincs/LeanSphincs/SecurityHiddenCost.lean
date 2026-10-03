import LeanSphincs.SecurityHiddenRows

/-! Original-cost instrumentation for the common hidden-coordinate comparison. Virtual
honest work has an explicit natural-number cost; ordinary raw queries each cost one, while
private draws and privileged disclosures are free. Every monitor can inspect this same trace. -/

open OracleComp OracleSpec
namespace LeanSphincs.Security.HiddenCost
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

abbrev SourceCostSpec (D R ι : Type) := HiddenRows.SourceSpec D R ι + (Nat →ₒ Unit)
abbrev Entry (D : Type) := D ⊕ Nat

def sourceCost {D R ι : Type} : (SourceCostSpec D R ι).Domain → Nat
  | .inl (.inr (.inl _)) => 1
  | .inr amount => amount
  | _ => 0

def recorded {D R ι : Type} : (SourceCostSpec D R ι).Domain → List (Entry D)
  | .inl (.inr (.inl input)) => [.inl input]
  | .inr amount => [.inr amount]
  | _ => []

def entryCost {D : Type} : Entry D → Nat
  | .inl _ => 1
  | .inr amount => amount

def traceCost {D : Type} (entries : List (Entry D)) : Nat := (entries.map entryCost).sum

theorem traceCost_append {D : Type} (left right : List (Entry D)) :
    traceCost (left ++ right) = traceCost left + traceCost right := by simp [traceCost]

theorem recorded_cost {D R ι : Type} (input : (SourceCostSpec D R ι).Domain) :
    traceCost (recorded input) = sourceCost input := by
  cases input with
  | inl input => cases input with
    | inl draw => rfl
    | inr input => cases input <;> rfl
  | inr amount => simp [traceCost, recorded, entryCost, sourceCost]

def tick {D R ι : Type} (amount : Nat) : OracleComp (SourceCostSpec D R ι) Unit :=
  liftM ((SourceCostSpec D R ι).query (.inr amount))

def ordinary {D R ι : Type} (input : D) : OracleComp (SourceCostSpec D R ι) R :=
  liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl input))))

def reveal {D R ι : Type} (coordinate : ι) : OracleComp (SourceCostSpec D R ι) Digest :=
  liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inr coordinate))))

def eraseQuery {D R ι : Type} :
    QueryImpl (SourceCostSpec D R ι) (OracleComp (HiddenRows.SourceSpec D R ι))
  | .inl input => liftM ((HiddenRows.SourceSpec D R ι).query input)
  | .inr _ => pure ()

def erase {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    OracleComp (HiddenRows.SourceSpec D R ι) α := simulateQ eraseQuery computation

theorem erase_tick {D R ι : Type} (amount : Nat) :
    erase (tick (D := D) (R := R) (ι := ι) amount) = pure () := by
  rw [erase, tick, simulateQ_spec_query]
  rfl

theorem erase_ordinary {D R ι : Type} (input : D) :
    erase (ordinary (R := R) (ι := ι) input) =
      liftM ((HiddenRows.SourceSpec D R ι).query (.inr (.inl input))) := by
  rw [erase, ordinary, simulateQ_spec_query]
  rfl

theorem erase_reveal {D R ι : Type} (coordinate : ι) :
    erase (reveal (D := D) (R := R) coordinate) =
      liftM ((HiddenRows.SourceSpec D R ι).query (.inr (.inr coordinate))) := by
  rw [erase, reveal, simulateQ_spec_query]
  rfl

def trace {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    OracleComp (SourceCostSpec D R ι) (α × List (Entry D)) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => do
      let value ← liftM ((SourceCostSpec D R ι).query input)
      let result ← next value
      return (result.1, recorded input ++ result.2)) computation

theorem trace_pure {D R ι α : Type} (value : α) :
    trace (pure value : OracleComp (SourceCostSpec D R ι) α) = pure (value, []) := rfl

theorem trace_query_bind {D R ι α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) :
    trace (liftM ((SourceCostSpec D R ι).query input) >>= next) =
      (liftM ((SourceCostSpec D R ι).query input) >>= fun value =>
        (fun result => (result.1, recorded input ++ result.2)) <$> trace (next value)) := rfl

/-- A weighted cap stops before any query or compressed honest-work tick exceeds the
remaining original budget. This is used on the common comparison execution. -/
def cap {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    Nat → OracleComp (SourceCostSpec D R ι) (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun input _ next budget =>
      if sourceCost input ≤ budget then do
        let value ← liftM ((SourceCostSpec D R ι).query input)
        next value (budget - sourceCost input)
      else pure none) computation

def Bounded {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) : Nat → Prop :=
  OracleComp.construct (fun _ _ => True)
    (fun input _ next budget => sourceCost input ≤ budget ∧
      ∀ value, next value (budget - sourceCost input)) computation

theorem bounded_pure {D R ι α : Type} (value : α) (budget : Nat) :
    Bounded (pure value : OracleComp (SourceCostSpec D R ι) α) budget := trivial

theorem bounded_query_bind {D R ι α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α) (budget : Nat) :
    Bounded (liftM ((SourceCostSpec D R ι).query input) >>= next) budget ↔
      sourceCost input ≤ budget ∧ ∀ value, Bounded (next value) (budget - sourceCost input) := Iff.rfl

theorem cap_bounded {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : Nat) : Bounded (cap computation budget) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind input next ih =>
      change Bounded (if sourceCost input ≤ budget then
        liftM ((SourceCostSpec D R ι).query input) >>= fun value => cap (next value) (budget - sourceCost input)
        else pure none) budget
      split
      · exact ⟨by assumption, fun value => ih value _⟩
      · trivial

/-- Joint result, original-cost trace, and hidden-guess count from ONE forced-failure
comparison run. Seed/output/message monitors must use this trace, not another experiment. -/
noncomputable def comparison {D R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceCostSpec D R ι) α) (known : HiddenReveal.Knowledge ι) :
    ProbComp ((α × List (Entry D)) × Nat) :=
  HiddenReveal.comparison (HiddenRows.compile model outside (erase (trace computation)) known) known

theorem trace_support_cost_le {D R ι α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : Nat)
    (hbound : Bounded computation budget) (result : α × List (Entry D))
    (hresult : result ∈ support (trace computation)) : traceCost result.2 ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      rw [trace_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [bounded_query_bind] at hbound
      rw [trace_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨value, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      have h := ih value _ (hbound.2 value) tail htail
      rw [traceCost_append, recorded_cost]
      omega

theorem erase_support {D R ι α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    support (erase computation) ⊆ support computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [erase]
  | query_bind input next ih =>
      intro result hresult
      rw [erase, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at hresult
      obtain ⟨value, _, htail⟩ := hresult
      exact (mem_support_bind_iff _ _ _).mpr ⟨value, mem_support_query input value, ih value htail⟩

theorem compile_support {D R A ι α : Type} [Fintype ι] (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (HiddenRows.SourceSpec D R ι) α) (known : HiddenReveal.Knowledge ι) :
    support (HiddenRows.compile model outside computation known) ⊆ support computation := by
  induction computation using OracleComp.inductionOn generalizing known with
  | pure value => exact Set.Subset.rfl
  | query_bind input next ih =>
      intro result hresult
      apply (mem_support_bind_iff _ _ _).mpr
      cases input with
      | inl draw =>
          rw [HiddenRows.compile_private, mem_support_bind_iff] at hresult
          obtain ⟨value, _, htail⟩ := hresult
          exact ⟨value, mem_support_query _ _, ih value known htail⟩
      | inr input =>
          cases input with
          | inr coordinate =>
              rw [HiddenRows.compile_reveal, mem_support_bind_iff] at hresult
              obtain ⟨value, _, htail⟩ := hresult
              exact ⟨value, mem_support_query _ _, ih value _ htail⟩
          | inl bytes =>
              rw [HiddenRows.compile_hash] at hresult
              cases hp : model.parse bytes with
              | none =>
                  simp only [hp] at hresult
                  exact ⟨outside bytes, mem_support_query _ _, ih _ known hresult⟩
              | some query =>
                  simp only [hp] at hresult
                  cases hk : known (model.incoming query.1) with
                  | none =>
                      simp only [hk] at hresult
                      rw [mem_support_bind_iff] at hresult
                      obtain ⟨_, _, htail⟩ := hresult
                      exact ⟨outside bytes, mem_support_query _ _, ih _ known htail⟩
                  | some value =>
                      simp only [hk] at hresult
                      split_ifs at hresult with heq
                      · rw [mem_support_bind_iff] at hresult
                        obtain ⟨successor, _, htail⟩ := hresult
                        exact ⟨model.combine query.1 successor, mem_support_query _ _, ih _ _ htail⟩
                      · exact ⟨outside bytes, mem_support_query _ _, ih _ known hresult⟩

theorem revealComparison_support {ι α : Type} [Fintype ι]
    (computation : OracleComp (HiddenReveal.ViewSpec ι) α) (known : HiddenReveal.Knowledge ι)
    (result : α × Nat) (hresult : result ∈ support (HiddenReveal.comparison computation known)) :
    result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing known result with
  | pure value =>
      simp only [HiddenReveal.comparison, OracleComp.construct_pure, support_pure,
        Set.mem_singleton_iff] at hresult ⊢
      exact congrArg Prod.fst hresult
  | query_bind input next ih =>
      apply (mem_support_bind_iff _ _ _).mpr
      cases input with
      | inl draw =>
          rw [HiddenReveal.comparison, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨value, _, htail⟩ := hresult
          exact ⟨value, mem_support_query _ _, ih value known result htail⟩
      | inr input =>
          cases input with
          | inl coordinate =>
              rw [HiddenReveal.comparison, OracleComp.construct_query_bind, mem_support_bind_iff] at hresult
              obtain ⟨⟨value, known'⟩, _, htail⟩ := hresult
              exact ⟨value, mem_support_query _ _, ih value known' result htail⟩
          | inr guess =>
              rw [HiddenReveal.comparison, OracleComp.construct_query_bind, support_map] at hresult
              obtain ⟨tail, htail, rfl⟩ := hresult
              exact ⟨(), mem_support_query _ _, ih () known tail htail⟩

/-- Every realized common comparison trace respects the original weighted source budget. -/
theorem comparison_cost_le {D R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceCostSpec D R ι) α) (known : HiddenReveal.Knowledge ι)
    (budget : Nat) (hbound : Bounded computation budget)
    (result : (α × List (Entry D)) × Nat) (hresult : result ∈ support (comparison model outside computation known)) :
    traceCost result.1.2 ≤ budget := by
  have hc := revealComparison_support _ known result hresult
  have hs := compile_support model outside (erase (trace computation)) known hc
  exact trace_support_cost_le computation budget hbound result.1 (erase_support _ hs)

theorem capped_comparison_cost_le {D R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model D R A ι) (outside : D → R)
    (computation : OracleComp (SourceCostSpec D R ι) α) (known : HiddenReveal.Knowledge ι)
    (budget : Nat) (result : (Option α × List (Entry D)) × Nat)
    (hresult : result ∈ support (comparison model outside (cap computation budget) known)) :
    traceCost result.1.2 ≤ budget :=
  comparison_cost_le model outside _ known budget (cap_bounded computation budget) result hresult

end LeanSphincs.Security.HiddenCost
