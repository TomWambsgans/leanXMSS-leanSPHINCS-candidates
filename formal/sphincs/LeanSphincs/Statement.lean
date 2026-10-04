import LeanSphincs.Randomized
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
The candidate SUF-CMA target, adapted from leanVM b7a107256 to pruning and genuinely random
randomizers. This module states the target; it does not prove the lifetime security claims.
All hash calls in the experiment count, including repeated calls and honest-party calls.
-/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs

structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

abbrev SigningSpec := Message →ₒ Option Signature

variable [Params]

namespace SigningTranscript

def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace Security

structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

noncomputable def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => liftM (Randomized.sign sk request)

noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]

def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

namespace Lifetimes

/-! Signature limits proved for this candidate game against adaptive FORS/WOTS switching
(stage 1: saturation, FORS forecast domination, certified excess bound). -/
abbrev full : Params := ⟨26, 540000000, by decide⟩
abbrev pruned20 : Params := ⟨20, 10650000, by decide⟩
abbrev pruned13 : Params := ⟨13, 93000, by decide⟩
abbrev pruned14 : Params := ⟨14, 185000, by decide⟩
abbrev pruned12 : Params := ⟨12, 47000, by decide⟩
/-- The site advertises 33000 at b=10; 12006 is the largest limit the stage-1 argument certifies. -/
abbrev pruned10 : Params := ⟨10, 12006, by decide⟩
/-- The site advertises 9000 at b=8; 3046 is the largest limit the stage-1 argument certifies. -/
abbrev pruned8 : Params := ⟨8, 3046, by decide⟩
/-- The earlier literal b=10 target (33), kept only for the legacy non-adaptive summaries. -/
abbrev legacyPruned10 : Params := ⟨10, 33, by decide⟩

/-- The requested claims for this candidate game; proved by `Lifetimes.requestedSecurity`
(StageOne.lean). -/
def RequestedSecurity : Prop :=
  @Security.HasClassicalSecurityBits full 127 ∧
  @Security.HasClassicalSecurityBits pruned20 127 ∧
  @Security.HasClassicalSecurityBits pruned13 127 ∧
  @Security.HasClassicalSecurityBits pruned14 127 ∧
  @Security.HasClassicalSecurityBits pruned12 127 ∧
  @Security.HasClassicalSecurityBits pruned10 127 ∧
  @Security.HasClassicalSecurityBits pruned8 127

end Lifetimes

end LeanSphincs
