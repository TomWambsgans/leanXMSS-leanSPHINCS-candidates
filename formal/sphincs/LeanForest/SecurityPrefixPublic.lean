import LeanForest.SecurityPrefixExecution

/-! The chain secrets derived from the seed, as a table indexed by chain addresses. -/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix

variable [Params]
open Concrete

def derivedSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) : Secrets :=
  fun (lay, tree, leaf, chain) =>
    evalWithAnswerFn f (Seeded.otsStart parameter lay tree leaf chain seed : OracleComp HashSpec Digest)

end LeanForest.Security.Prefix
