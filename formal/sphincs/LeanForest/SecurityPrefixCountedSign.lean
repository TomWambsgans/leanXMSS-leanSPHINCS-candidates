import LeanForest.SecurityPrefixCost

/-! Counting the hash queries of lifted hash computations: on a fixed answer function, counting
returns the value together with its `hashCalls`. Private randomizer draws contribute zero hash
calls. -/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix

variable [Params]
open Concrete QueryCap

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.finishSign
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

end LeanForest.Security.Prefix
