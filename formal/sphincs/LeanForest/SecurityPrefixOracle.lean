import LeanForest.StatementDet
import LeanForest.SecuritySignatureWitness
import LeanForest.SecurityDomains
import LeanForest.Base.Prelude

/-!
An exact candidate-byte oracle split for one hidden WOTS prefix. Adapted from leanVM's
OtsPrefixOracle; the candidate has 64 chains and three hash steps per chain. Outside queries
and the unused high 128 output bits remain explicit, so erasure cannot silently discard
adversary-visible information.
-/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix

variable [Params]
open Concrete

structure Segment where
  parameter : PublicParameter
  lay : Layer
  tree : TreeIndex
  leaf : LeafIndex
  chainIdx : ChainIndex
  digit : Digit

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
