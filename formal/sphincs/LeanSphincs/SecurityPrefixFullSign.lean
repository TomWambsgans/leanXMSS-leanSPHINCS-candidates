import LeanSphincs.SecurityPrefixSignLayer
import LeanSphincs.SecurityPrefixExecution

/-! Whole-signer factoring through one disclosed chain frontier. The independent randomizer
samples are retained as random samples; only deterministic hash-only computations are evaluated.
This equality does not assert independence of seed-derived material or erase its query cost. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.signLayer
  Seeded.ftsOpen Seeded.ftsKey sequenceFin chainWalk

theorem messageDigestCall_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) :
    evalWithAnswerFn (answer segment tables high outside)
      (messageDigestCall segment.parameter root message randomness call : OracleComp HashSpec HashOutput) =
    evalWithAnswerFn outside
      (messageDigestCall segment.parameter root message randomness call : OracleComp HashSpec HashOutput) := by
  exact answer_outside segment tables high outside _
    (parse_other_domain segment (.message call) _ (by change (12 : BitVec 8) ≠ 1; decide))

theorem messageDigest_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (root : Digest) (message : Message) (randomness : Randomness) :
    evalWithAnswerFn (answer segment tables high outside)
      (messageDigest segment.parameter root message randomness : OracleComp HashSpec MessageDigest) =
    evalWithAnswerFn outside
      (messageDigest segment.parameter root message randomness : OracleComp HashSpec MessageDigest) := by
  simp only [messageDigest, evalWithAnswerFn_bind, messageDigestCall_answer, evalWithAnswerFn_pure]

/-- Hash-only evaluation inside the private-sampling interpreter is deterministic. -/
theorem fixedHashWorld_lift_hash (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      PMF.pure (evalWithAnswerFn f computation) := by
  have hlift : simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      simulateQ (fun bytes => PMF.pure (f bytes) : QueryImpl HashSpec PMF) computation :=
    QueryImpl.simulateQ_liftComp_right_eq_of_apply (fixedHashWorld f)
      (fun bytes => PMF.pure (f bytes)) (fun _ => rfl) computation
  rw [hlift]
  clear hlift
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evalWithAnswerFn_pure]; rfl
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from simulateQ_spec_query f input,
        ← PMF.monad_pure_eq_pure, pure_bind]
      exact ih (f input)

/-- The distribution of private samples does not depend on the fixed hash function. -/
theorem fixedHashWorld_lift_prob (f g : QueryImpl HashSpec Id) {α : Type}
    (computation : ProbComp α) :
    simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      simulateQ (fixedHashWorld g) (liftM computation : OracleComp OracleWorld α) := by
  trans simulateQ (fun input => PMF.uniformOfFintype (unifSpec.Range input) :
    QueryImpl unifSpec PMF) computation
  · exact QueryImpl.simulateQ_liftComp_left_eq_of_apply (fixedHashWorld f)
      (fun input => PMF.uniformOfFintype (unifSpec.Range input)) (fun _ => rfl) computation
  · symm
    exact QueryImpl.simulateQ_liftComp_left_eq_of_apply (fixedHashWorld g)
      (fun input => PMF.uniformOfFintype (unifSpec.Range input)) (fun _ => rfl) computation

variable [Params]

theorem signAttempt_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (hparameter : sk.parameter = segment.parameter) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) =
    evalWithAnswerFn outside
      (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) := by
  simp only [Seeded.signAttempt, evalWithAnswerFn_bind, hparameter, messageDigestCall_answer]
  split <;> rfl

/-- Exact equality of the actual grinding distribution, including repeated randomizers and
finite exhaustion, without replacing the randomizer sequence by a deterministic trace. -/
theorem signDigestLoop_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (hparameter : sk.parameter = segment.parameter) (attempts : Nat) :
    simulateQ (fixedHashWorld (answer segment tables high outside))
      (Randomized.signDigestLoop sk message attempts) =
    simulateQ (fixedHashWorld outside) (Randomized.signDigestLoop sk message attempts) := by
  induction attempts with
  | zero => simp only [Randomized.signDigestLoop, simulateQ_pure]
  | succ attempts ih =>
      simp only [Randomized.signDigestLoop, simulateQ_bind, fixedHashWorld_lift_hash,
        signAttempt_answer segment tables high outside sk message _ hparameter,
        fixedHashWorld_lift_prob (answer segment tables high outside) outside]
      apply bind_congr
      intro randomness
      apply bind_congr
      intro result
      cases result <;> simp only [simulateQ_pure, ih]

/-- The hash-only signature assembly receives only the selected chain frontier; FORS secrets,
FORS openings, and all other chains are evaluated using the outside function. -/
noncomputable def publicFinishSign (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (seed : MasterSeed) (root : Digest) (message : Message) (randomness : Randomness) : Option Signature :=
  let digest := evalWithAnswerFn outside
    (messageDigest segment.parameter root message randomness : OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let ftsSecrets := fun tree => evalWithAnswerFn outside
    (deriveKey segment.parameter (.fts index tree (leaves (ftsIndexOf tree))) seed : OracleComp HashSpec Digest)
  let path := evalWithAnswerFn outside (Seeded.ftsOpen segment.parameter index leaves seed :
    OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest))
  let layer := publicLayer segment outside secrets frontier surrogates index topLayer
    (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index seed : OracleComp HashSpec Digest))
  layer.map fun top => ⟨randomness, ftsSecrets, path, Fin.cases top (fun i => Fin.elim0 i)⟩

theorem publicFinishSign_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (surrogates : Nat → Digest)
    (seed : MasterSeed) (root : Digest) (message : Message) (randomness : Randomness) :
    publicFinishSign segment outside (replaceSecret segment secrets replacement) frontier surrogates
      seed root message randomness =
    publicFinishSign segment outside secrets frontier surrogates seed root message randomness := by
  simp only [publicFinishSign, publicLayer_replaceSecret]

theorem finishSign_from_referenceCutoff (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (hparameter : sk.parameter = segment.parameter) (hcutoff : ReferenceCutoff segment outside sk.seed) :
    evalWithAnswerFn (answer segment tables high outside) (Randomized.finishSign sk message randomness) =
    publicFinishSign segment outside (derivedSecrets outside segment.parameter sk.seed)
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (derivedSecrets outside segment.parameter sk.seed (address segment)))
      (fun level => evalWithAnswerFn outside
        (Seeded.surrogate segment.parameter sk.seed level : OracleComp HashSpec Digest))
      sk.seed sk.root message randomness := by
  simp only [Randomized.finishSign, evalWithAnswerFn_bind, hparameter, messageDigest_answer,
    Completeness.eval_sequenceFin, eval_derive_answer, ftsOpen_answer, sequenceLayers,
    signLayer_from_referenceCutoff segment tables high outside sk _ _ hparameter hcutoff,
    publicFinishSign]
  cases publicLayer segment outside (derivedSecrets outside segment.parameter sk.seed)
    (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
      (derivedSecrets outside segment.parameter sk.seed (address segment)))
    (fun level => evalWithAnswerFn outside
      (Seeded.surrogate segment.parameter sk.seed level : OracleComp HashSpec Digest))
    (digestIndex (evalWithAnswerFn outside
      (messageDigest segment.parameter sk.root message randomness : OracleComp HashSpec MessageDigest))) topLayer
    (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter
      (digestIndex (evalWithAnswerFn outside
        (messageDigest segment.parameter sk.root message randomness : OracleComp HashSpec MessageDigest))) sk.seed :
        OracleComp HashSpec Digest)) <;>
    simp only [evalWithAnswerFn_pure, Option.map_none, Option.map_some]

/-- A probabilistic endpoint-only signer. Its randomizer sampler remains the actual sampler. -/
noncomputable def publicSign (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (sk : Seeded.SecretKey) (message : Message) : PMF (Option Signature) := do
  let result ← simulateQ (fixedHashWorld outside)
    (Randomized.signDigestLoop sk message digestAttemptLimit)
  match result with
  | none => pure none
  | some randomness => pure (publicFinishSign segment outside secrets frontier surrogates
      sk.seed sk.root message randomness)

theorem publicSign_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (surrogates : Nat → Digest)
    (sk : Seeded.SecretKey) (message : Message) :
    publicSign segment outside (replaceSecret segment secrets replacement) frontier surrogates sk message =
    publicSign segment outside secrets frontier surrogates sk message := by
  simp only [publicSign, publicFinishSign_replaceSecret]

/-- Full signing equality for the candidate byte layout and genuinely random randomizers. -/
theorem sign_from_referenceCutoff (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (hparameter : sk.parameter = segment.parameter) (hcutoff : ReferenceCutoff segment outside sk.seed) :
    simulateQ (fixedHashWorld (answer segment tables high outside)) (Randomized.sign sk message) =
    publicSign segment outside (derivedSecrets outside segment.parameter sk.seed)
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (derivedSecrets outside segment.parameter sk.seed (address segment)))
      (fun level => evalWithAnswerFn outside
        (Seeded.surrogate segment.parameter sk.seed level : OracleComp HashSpec Digest)) sk message := by
  simp only [Randomized.sign, simulateQ_bind, publicSign,
    signDigestLoop_answer segment tables high outside sk message hparameter]
  apply bind_congr
  intro result
  cases result with
  | none => simp only [simulateQ_pure]
  | some randomness =>
    rw [fixedHashWorld_lift_hash,
      finishSign_from_referenceCutoff segment tables high outside sk message randomness hparameter hcutoff]
    rfl

end LeanSphincs.Security.Prefix
