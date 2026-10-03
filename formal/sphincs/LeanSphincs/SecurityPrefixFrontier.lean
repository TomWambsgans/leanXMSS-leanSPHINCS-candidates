import LeanSphincs.SecurityPrefixTrace

/-! Candidate chain reconstruction above a hidden prefix. Honest values at or above the
declared disclosure frontier can be computed from that frontier and the outside oracle,
without querying or disclosing the lower prefix. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete

theorem parse_later_chain (segment : Segment) (position : ChainStep) (value : Digest)
    (hlater : segment.digit.val ≤ position.val) :
    parse segment (tweakableHashInput segment.parameter
      (.chain segment.lay segment.tree segment.leaf segment.chainIdx position) (bytesLE 16 value)) = none := by
  cases hparse : parse segment (tweakableHashInput segment.parameter
      (.chain segment.lay segment.tree segment.leaf segment.chainIdx position) (bytesLE 16 value)) with
  | none => rfl
  | some query =>
      have hinput := (parse_some_iff segment _ query).mp hparse
      have hstep := (Chain.chain_input_address_injective segment.parameter segment.lay segment.tree
        segment.leaf value query.2 hinput).2
      have heq : position.val = query.1.val :=
        congrArg (fun step : ChainStep => step.val) hstep
      have := query.1.isLt
      omega

/-- This trace-level invariant holds for any suffix beginning at or above the declared frontier. -/
theorem avoids_chainWalk (segment : Segment) (f : QueryImpl HashSpec Id)
    (start steps : Nat) (value : Digest) (hstart : segment.digit.val ≤ start) :
    Avoids segment f (chainWalk segment.parameter segment.lay segment.tree segment.leaf
      segment.chainIdx start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => intro bytes hbytes; simp [chainWalk] at hbytes
  | succ steps ih =>
      intro bytes hbytes
      rw [chainWalk, queriedInputs_bind] at hbytes
      rcases List.mem_append.mp hbytes with hbefore | hlast
      · exact ih bytes hbefore
      · split at hlast
        next hstep =>
          rw [queriedInputs_tweakableHash, List.mem_singleton] at hlast
          subst bytes
          exact parse_later_chain segment ⟨start + steps, hstep⟩ _
            (by change segment.digit.val ≤ start + steps; omega)
        next => simp only [queriedInputs_pure, List.not_mem_nil] at hlast

/-- Replacing every lower-prefix row leaves the suffix computation unchanged. -/
theorem chainWalk_above_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (start steps : Nat) (value : Digest)
    (hstart : segment.digit.val ≤ start) :
    evalWithAnswerFn (answer segment tables high outside)
      (chainWalk segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx
        start steps value : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside
      (chainWalk segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx
        start steps value : OracleComp HashSpec Digest) :=
  eval_answer_of_avoids segment tables high outside _
    (avoids_chainWalk segment outside start steps value hstart)

/-- Any honestly disclosed value at or above the cutoff depends on the hidden rows and secret
only through the frontier endpoint. The selected secret is absent from the right-hand suffix. -/
theorem disclosed_value_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (secret : Digest) (position : Nat)
    (hposition : segment.digit.val ≤ position) :
    evalWithAnswerFn (answer segment tables high outside)
      (chainWalk segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx
        0 position secret : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside
      (chainWalk segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx
        segment.digit.val (position - segment.digit.val)
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables secret) :
        OracleComp HashSpec Digest) := by
  have hsplit := Completeness.walk_add (answer segment tables high outside) segment.parameter
    segment.lay segment.tree segment.leaf segment.chainIdx 0 segment.digit.val
    (position - segment.digit.val) secret
  simp only [Completeness.walk, Nat.add_sub_of_le hposition, Nat.zero_add] at hsplit
  rw [hsplit, evaluate_answer]
  exact chainWalk_above_answer segment tables high outside _ _ _ le_rfl

/-- In particular the public WOTS endpoint can be reconstructed without its hidden prefix. -/
theorem endpoint_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (secret : Digest) :
    evalWithAnswerFn (answer segment tables high outside)
      (chainWalk segment.parameter segment.lay segment.tree segment.leaf segment.chainIdx
        0 (chainLength - 1) secret : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside (recoverChain segment.parameter segment.lay segment.tree segment.leaf
      segment.chainIdx segment.digit
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables secret)) :=
  disclosed_value_from_frontier segment tables high outside secret (chainLength - 1)
    (Nat.le_pred_of_lt segment.digit.isLt)

end LeanSphincs.Security.Prefix
