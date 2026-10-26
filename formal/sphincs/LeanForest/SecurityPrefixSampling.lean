import LeanForest.SecurityPrefixOracle

/-!
Chain addresses, secret tables indexed by them, the address of a selected prefix segment, and
secret tables whose selected coordinate is erased. Adapted from leanVM's OtsPrefixSecretSampling.
-/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix

variable [Params]
open UniformTableSplit

attribute [local instance] Classical.propDecidable

abbrev ChainAddress := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev Secrets := ChainAddress → Digest

end LeanForest.Security.Prefix
