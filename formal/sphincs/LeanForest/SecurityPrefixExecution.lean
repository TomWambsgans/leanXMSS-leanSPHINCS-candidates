import LeanForest.SecurityPrefixSampling

/-!
The predicate that counts source hash calls and the fixed-function source world (`fixedHashWorld`:
fresh private draws and a supplied hash function).
-/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Security.Prefix

variable [Params]
set_option backward.isDefEq.respectTransparency false

/-- Source-side hash calls, excluding private uniform samples. -/
def SourceHash : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance (input : OracleWorld.Domain) : Decidable (SourceHash input) := by
  cases input <;> unfold SourceHash <;> infer_instance

/-- Fresh private uniform sampling together with a supplied fixed hash function. -/
noncomputable def fixedHashWorld (outside : QueryImpl HashSpec Id) : QueryImpl OracleWorld PMF
  | .inl _sample => PMF.uniformOfFintype _
  | .inr bytes => PMF.pure (outside bytes)

end LeanForest.Security.Prefix
