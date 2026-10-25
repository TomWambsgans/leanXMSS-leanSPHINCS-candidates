import LeanForest.SecurityReferenceChoice
import LeanForest.SecuritySignatureWitness

/-! The reference WOTS word and counter chosen by the actual canonical encoding search at each key
of an index's path, defined also for unsigned keys and exhausted searches. -/

open OracleComp OracleSpec

namespace LeanForest.Security.SignatureWitness

variable [Params]
open Concrete

attribute [local irreducible] messageDigest forestRecover otsLeaf treeFold
  Seeded.forestKey Seeded.treeRoot Seeded.treePath chainWalk encode

/-- The reference word of the key of layer `lay` on the path of `leaf`. -/
noncomputable def chosenWord (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) (lay : Layer) : Encoding :=
  ReferenceChoice.word f parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
    (canonicalMessage f parameter seed leaf lay)

/-- The reference counter of the key of layer `lay` on the path of `leaf`. -/
noncomputable def chosenCounter (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) (lay : Layer) : Option Counter :=
  (ReferenceChoice.selection f parameter lay (keyTree leaf lay) (keyLeaf leaf lay)
    (canonicalMessage f parameter seed leaf lay)).map Prod.fst

end LeanForest.Security.SignatureWitness
