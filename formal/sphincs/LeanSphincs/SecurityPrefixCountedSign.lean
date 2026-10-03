import LeanSphincs.SecurityPrefixCost

/-! The complete frontier simulation retains the original hash-query cost, including work
performed inside the honest signer. Private randomizer draws contribute zero hash calls. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete SphincsSecurity.QueryCap

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Randomized.finishSign
  Seeded.signAttempt
set_option backward.isDefEq.respectTransparency false

theorem counted_lift_hash {α : Type} (computation : OracleComp HashSpec α) :
    counted SourceHash (liftM computation : OracleComp OracleWorld α) =
    (liftM (counted (fun _ => True) computation) : OracleComp OracleWorld (α × Nat)) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, counted_pure]
  | query_bind input next ih =>
      simp only [liftM_bind]
      change counted SourceHash (liftM (OracleWorld.query (.inr input)) >>= fun output => liftM (next output)) = _
      simp only [counted_query_bind, SourceHash, if_true, ih, liftM_bind, liftM_pure]
      rfl

theorem counted_lift_prob {α : Type} (computation : ProbComp α) :
    counted SourceHash (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, 0)) <$> (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, counted_pure, map_pure]
  | query_bind input next ih =>
      simp only [liftM_bind, map_bind]
      change counted SourceHash (liftM (OracleWorld.query (.inl input)) >>= fun output => liftM (next output)) = _
      simp only [counted_query_bind, SourceHash, if_false, zero_add, ih, bind_map_left,
        bind_pure_comp, Prod.mk.eta]
      rfl

theorem eval_counted_hash {α : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) :
    evalWithAnswerFn f (counted (fun _ => True) computation) =
      (evalWithAnswerFn f computation, hashCalls f computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [counted_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from simulateQ_spec_query f input,
        ih, if_true]
      change (_, 1 + hashCalls f (next (f input))) = (_, (input :: queriedInputs f (next (f input))).length)
      simp only [List.length_cons, hashCalls, Nat.add_comm]

theorem fixedHashWorld_counted_lift_hash {α : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (counted SourceHash (liftM computation : OracleComp OracleWorld α)) =
      PMF.pure (evalWithAnswerFn f computation, hashCalls f computation) := by
  rw [counted_lift_hash, fixedHashWorld_lift_hash, eval_counted_hash]

variable [Params]

/-- The complete grinding loop has the same joint distribution of result and number of hash
calls under the outside oracle and the hidden-prefix oracle. -/
theorem counted_signDigestLoop_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (hparameter : sk.parameter = segment.parameter) (attempts : Nat) :
    simulateQ (fixedHashWorld (answer segment tables high outside))
      (counted SourceHash (Randomized.signDigestLoop sk message attempts)) =
    simulateQ (fixedHashWorld outside) (counted SourceHash (Randomized.signDigestLoop sk message attempts)) := by
  induction attempts with
  | zero => simp only [Randomized.signDigestLoop, counted_pure, simulateQ_pure]
  | succ attempts ih =>
      simp only [Randomized.signDigestLoop, counted_bind, counted_lift_prob, simulateQ_bind,
        simulateQ_map, fixedHashWorld_counted_lift_hash, hashCalls_signAttempt,
        signAttempt_answer segment tables high outside sk message _ hparameter,
        fixedHashWorld_lift_prob (answer segment tables high outside) outside]
      apply bind_congr
      intro sample
      simp only [← PMF.monad_pure_eq_pure, pure_bind, simulateQ_pure]
      cases evalWithAnswerFn outside (Seeded.signAttempt sk message sample.1 :
        OracleComp HashSpec (Option Index)) <;> simp only [counted_pure, simulateQ_pure, ih]

/-- The original assembly cost is evaluated using the outside function. Cost invariance
ensures that no hidden table or selected chain secret is needed to compute it. -/
noncomputable def publicSignWithCost (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (sk : Seeded.SecretKey) (message : Message) : PMF (Option Signature × Nat) := do
  let loop ← simulateQ (fixedHashWorld outside)
    (counted SourceHash (Randomized.signDigestLoop sk message digestAttemptLimit))
  match loop.1 with
  | none => pure (none, loop.2)
  | some randomness => pure (publicFinishSign segment outside secrets frontier surrogates sk.seed sk.root message randomness,
        loop.2 + hashCalls outside (Randomized.finishSign sk message randomness))

theorem publicSignWithCost_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (surrogates : Nat → Digest)
    (sk : Seeded.SecretKey) (message : Message) :
    publicSignWithCost segment outside (replaceSecret segment secrets replacement) frontier surrogates sk message =
    publicSignWithCost segment outside secrets frontier surrogates sk message := by
  simp only [publicSignWithCost, publicFinishSign_replaceSecret]

theorem counted_sign_from_referenceCutoff (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (hparameter : sk.parameter = segment.parameter) (hcutoff : ReferenceCutoff segment outside sk.seed) :
    simulateQ (fixedHashWorld (answer segment tables high outside))
      (counted SourceHash (Randomized.sign sk message)) =
    publicSignWithCost segment outside (derivedSecrets outside segment.parameter sk.seed)
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (derivedSecrets outside segment.parameter sk.seed (address segment)))
      (fun level => evalWithAnswerFn outside
        (Seeded.surrogate segment.parameter sk.seed level : OracleComp HashSpec Digest)) sk message := by
  simp only [Randomized.sign, counted_bind, simulateQ_bind, publicSignWithCost,
    counted_signDigestLoop_answer segment tables high outside sk message hparameter]
  apply bind_congr
  rintro ⟨result, cost⟩
  cases result with
  | none => simp only [counted_pure, simulateQ_pure, pure_bind, Nat.add_zero]
  | some randomness =>
    rw [fixedHashWorld_counted_lift_hash,
      finishSign_from_referenceCutoff segment tables high outside sk message randomness hparameter hcutoff,
      hashCalls_finishSign_answer segment tables high outside sk message randomness hparameter]
    simp only [← PMF.monad_pure_eq_pure, pure_bind, simulateQ_pure]

end LeanSphincs.Security.Prefix
