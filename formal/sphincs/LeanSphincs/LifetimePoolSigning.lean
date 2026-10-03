import LeanSphincs.LifetimePoolGrinding
import LeanSphincs.SecurityPrefixFullSign

/-! The pool sampler is exactly the scheme's private randomizer loop when the shared hash
function is fixed. This identity retains the independent private samples and finite exhaustion. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec Concrete Security.Prefix
variable [Params]

noncomputable def oracleIndexPool (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) : IndexPool := fun rho => blockIndex (evalWithAnswerFn f
      (messageDigestCall sk.parameter sk.root message rho 0 : OracleComp HashSpec HashOutput))

theorem fixed_signDigestLoop_eq_poolGrindRandomness (f : QueryImpl HashSpec Id)
    (sk : Seeded.SecretKey) (message : Message) (attempts : Nat) :
    simulateQ (fixedHashWorld f) (Randomized.signDigestLoop sk message attempts) =
      simulateQ (fun input => PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF)
        (poolGrindRandomness sk.parameter (oracleIndexPool f sk message) attempts) := by
  induction attempts with
  | zero => simp only [Randomized.signDigestLoop, poolGrindRandomness, simulateQ_pure,
      simulateQ_pure]
  | succ attempts ih =>
      simp only [Randomized.signDigestLoop, poolGrindRandomness, simulateQ_bind,
        fixedHashWorld_lift_hash, Seeded.signAttempt, evalWithAnswerFn_bind]
      have hs : simulateQ (fixedHashWorld f) (liftM ($ᵗ Randomness : ProbComp Randomness) :
          OracleComp OracleWorld Randomness) = simulateQ (fun input => PMF.uniformOfFintype (unifSpec.Range input) : QueryImpl unifSpec PMF)
          ($ᵗ Randomness : ProbComp Randomness) := by
        rfl
      rw [hs]
      apply bind_congr
      intro rho
      by_cases hland : Landed sk.parameter (oracleIndexPool f sk message rho)
      · simp only [oracleIndexPool] at hland
        simp only [oracleIndexPool, hland, if_true, evalWithAnswerFn_pure, ← PMF.monad_pure_eq_pure,
          pure_bind, simulateQ_pure, simulateQ_pure]
      · simp only [oracleIndexPool] at hland
        simp only [oracleIndexPool, hland, if_false, evalWithAnswerFn_pure, ← PMF.monad_pure_eq_pure,
          pure_bind, ih]

end LeanSphincs.Lifetime
