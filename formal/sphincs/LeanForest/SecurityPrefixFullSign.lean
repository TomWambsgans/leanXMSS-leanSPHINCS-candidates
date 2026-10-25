import LeanForest.SecurityPrefixSigning
import LeanForest.SecurityPrefixExecution

/-! Hash-only evaluation inside the private-sampling interpreter is deterministic. -/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix

variable [Params]
open Concrete
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.signLayer
  Seeded.forestOpen Seeded.forestKey sequenceFin chainWalk

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


end LeanForest.Security.Prefix
