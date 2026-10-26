import LeanForest.StatementDet
import LeanForest.SecuritySignatureWitness
import LeanForest.SecurityDomains
import LeanForest.Base.Prelude

/-!
A hash output as its low 128 bits (the digest the scheme keeps) and its unused high bits
(`combine`, `split_combine`, `combine_split`), so a sampled output can be split without losing the
part the adversary sees. Adapted from leanVM's OtsPrefixOracle.
-/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix

variable [Params]
open Concrete

abbrev High := BitVec (hashOutputBits - digestBits)

noncomputable def combine (low : Digest) (high : High) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)

theorem split_combine (low : Digest) (high : High) :
    splitHashOutput digestBits (combine low high) = (low, high) :=
  (splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high)

theorem truncate_combine (low : Digest) (high : High) : truncateHash (combine low high) = low :=
  congrArg Prod.fst (split_combine low high)

theorem combine_split (output : HashOutput) :
    combine (truncateHash output) (splitHashOutput digestBits output).2 = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output

end LeanForest.Security.Prefix
