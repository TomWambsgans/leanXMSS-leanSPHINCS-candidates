import LeanForest.SecurityPrefixCountedSign
import SphincsSecurity.Proof.Reference.QueryAllocation
import SphincsSecurity.Proof.Chains.AdaptiveChainCapCost
import LeanForest.SecurityMaterialGameCoupling

/-! The chain secrets read from prepared material (`materialSecrets`). -/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix
open Concrete SeedModel PreparedScheme SeedCoupling

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] programCache digestAttemptLimit encodingAttemptLimit
  Randomized.sign Randomized.finishSign

def materialSecrets (material : Material) : Secrets :=
  fun chain => truncateHash (material.2 (.inl chain))

end LeanForest.Security.Prefix
