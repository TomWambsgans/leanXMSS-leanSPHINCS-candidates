import LeanForest.LazyRun.Rows

/-! Cost instrumentation for the common hidden-coordinate comparison. Ordinary raw queries (the
adversary's and the verifier's) each cost one; honest queries (the signer's) are answered by the
same oracle and are free, as are private draws and privileged disclosures. Every monitor can
inspect this same trace. -/

open OracleComp OracleSpec
namespace LeanForest.Security.HiddenCost

variable [Params]
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

/-- An honest query's input (a wrapper, so that no lift of ordinary queries lands on it). -/
structure Honest (D : Type) where
  input : D

/-- The sources and the honest queries: an honest query is answered like an ordinary one. -/
abbrev SourceCostSpec (D R ι : Type) := HiddenRows.SourceSpec D R ι + (Honest D →ₒ R)
/-- A trace entry: an ordinary input or an honest input. -/
abbrev Entry (D : Type) := D ⊕ D

def sourceCost {D R ι : Type} : (SourceCostSpec D R ι).Domain → Nat
  | .inl (.inr (.inl _)) => 1
  | _ => 0

def recorded {D R ι : Type} : (SourceCostSpec D R ι).Domain → List (Entry D)
  | .inl (.inr (.inl input)) => [.inl input]
  | .inr honest => [.inr honest.input]
  | _ => []

/-- The input that an ordinary or an honest query reads from the oracle. -/
def queryInput {D R ι : Type} : (SourceCostSpec D R ι).Domain → Option D
  | .inl (.inr (.inl input)) => some input
  | .inr honest => some honest.input
  | _ => none

def entryCost {D : Type} : Entry D → Nat
  | .inl _ => 1
  | .inr _ => 0

def traceCost {D : Type} (entries : List (Entry D)) : Nat := (entries.map entryCost).sum

theorem traceCost_append {D : Type} (left right : List (Entry D)) :
    traceCost (left ++ right) = traceCost left + traceCost right := by simp [traceCost]

theorem recorded_cost {D R ι : Type} (input : (SourceCostSpec D R ι).Domain) :
    traceCost (recorded input) = sourceCost input := by
  cases input with
  | inl input => cases input with
    | inl draw => rfl
    | inr input => cases input <;> rfl
  | inr input => simp [traceCost, recorded, entryCost, sourceCost]

/-- An honest query: answered by the oracle, free. -/
def honest {D R ι : Type} (input : D) : OracleComp (SourceCostSpec D R ι) R :=
  liftM ((SourceCostSpec D R ι).query (.inr ⟨input⟩))

def reveal {D R ι : Type} (coordinate : ι) : OracleComp (SourceCostSpec D R ι) Digest :=
  liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inr coordinate))))

def eraseQuery {D R ι : Type} :
    QueryImpl (SourceCostSpec D R ι) (OracleComp (HiddenRows.SourceSpec D R ι))
  | .inl input => liftM ((HiddenRows.SourceSpec D R ι).query input)
  | .inr honest => liftM ((HiddenRows.SourceSpec D R ι).query (.inr (.inl honest.input)))

def erase {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    OracleComp (HiddenRows.SourceSpec D R ι) α := simulateQ eraseQuery computation

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

/-- A cap stops before an ordinary query exceeds the remaining budget. This is used on the common
comparison execution. -/
def cap {D R ι α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    Nat → OracleComp (SourceCostSpec D R ι) (Option α) :=
  OracleComp.construct (fun value _ => pure (some value))
    (fun input _ next budget =>
      if sourceCost input ≤ budget then do
        let value ← liftM ((SourceCostSpec D R ι).query input)
        next value (budget - sourceCost input)
      else pure none) computation

end LeanForest.Security.HiddenCost
