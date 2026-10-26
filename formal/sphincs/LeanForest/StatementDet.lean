import LeanForest.Scheme
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
The SUF-CMA game of the security target, adapted from leanVM b7a107256 to pruning: forgeries,
signing transcripts and their tests, adversaries, and the counted experiment with the signer of the
Rust implementation, `Seeded.sign`, whose randomizers are derived from the master seed and the
message (a repeated request returns the same signature). Every hash call counts, including
repeated calls and the calls of the honest parties. The module ends with the forgery advantage, the
hash-query budget and the security-bits target.
-/

open OracleComp OracleSpec ENNReal

namespace LeanForest

variable [Params]

structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

abbrev SigningSpec := Message →ₒ Option Signature

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

noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

end Security

end LeanForest

namespace LeanForest.Security.Det

variable [Params]

noncomputable def signingOracleDet (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request : OracleComp HashSpec (Option Signature))

noncomputable def gameCoreDet (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld
      (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracleDet sk)
      (adversary.main pk)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def experimentDet (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCoreDet adversary)).run.run' ∅

noncomputable def forgeAdvantageDet (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experimentDet adversary]

def HasHashQueryBoundDet (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experimentDet adversary), result.2 ≤ q

def HasClassicalSecurityBitsDet (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBoundDet adversary q →
    forgeAdvantageDet adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end LeanForest.Security.Det
