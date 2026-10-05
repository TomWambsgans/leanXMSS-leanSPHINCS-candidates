import LeanSphincs.Scheme

/-!
The signer variant with truly uniform independent randomizers. Key derivation and surrogate
derivation still use the master seed and the same shared hash oracle as the reference scheme.
This is distinct from Rust's seed-derived randomizers; no equivalence is assumed.
-/

open OracleComp OracleSpec

namespace LeanSphincs.Randomized

open Concrete

variable [Params]

/-- Each trial samples a new independent randomizer, with replacement. Its digest query may repeat. -/
noncomputable def signDigestLoop (sk : Seeded.SecretKey) (message : Message) :
    Nat → OracleComp OracleWorld (Option Randomness)
  | 0 => pure none
  | attempts + 1 => do
      let randomness ← liftM ($ᵗ Randomness : ProbComp Randomness)
      let result ← liftM (Seeded.signAttempt sk message randomness
        : OracleComp HashSpec (Option Index))
      match result with
      | some _ => pure (some randomness)
      | none => signDigestLoop sk message attempts

/-- Assemble the signature after a randomizer lands, using the reference hash layouts. -/
def finishSign (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    OracleComp HashSpec (Option Signature) := do
  let digest ← messageDigest sk.parameter sk.root message randomness
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let secrets ← sequenceFin fun tree =>
    deriveKey sk.parameter (.fts index tree (leaves (ftsIndexOf tree))) sk.seed
  let ftsPath ← Seeded.ftsOpen sk.parameter index leaves sk.seed
  let some layers ← sequenceLayers (fun lay => Seeded.signLayer sk index lay) | return none
  return some ⟨randomness, secrets, ftsPath, layers⟩

/-- The stateless signer with truly random randomizers and an explicit exhaustion result. -/
noncomputable def sign (sk : Seeded.SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  let some randomness ← signDigestLoop sk message digestAttemptLimit | return none
  liftM (finishSign sk message randomness)

end LeanSphincs.Randomized
