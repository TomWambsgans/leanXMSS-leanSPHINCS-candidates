import LeanSphincs.SecurityReferenceSignature

/-! An accepted randomizer whose honest assembly fails has an exhausted canonical WOTS
search. Every accepted signature at that index then has a primitive exceptional witness.
This avoids a separate probabilistic loss for failed signing records in the lifetime bank. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.SignatureWitness
open Concrete Completeness Prefix
variable [Params]
attribute [local irreducible] firstEncoding encodingAttemptLimit Seeded.ftsKey Seeded.ftsOpen
  Seeded.treePath Seeded.signLayer chainWalk sequenceFin encode
set_option backward.isDefEq.respectTransparency false

theorem finishSign_none_iff_selection_none (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) :
    evalWithAnswerFn f (Randomized.finishSign sk message randomness) = none ↔
      ReferenceChoice.selection f sk.parameter topLayer rootTree
        (digestIndex (evalWithAnswerFn f
          (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)))
        (canonicalFors f sk.parameter sk.seed (digestIndex (evalWithAnswerFn f
          (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)))) = none := by
  simp only [Randomized.finishSign, evalWithAnswerFn_bind, sequenceLayers,
    Seeded.signLayer, Seeded.layerMessage, treeIndexAt_eq, leafIndexAt_eq, Seeded.otsSign,
    otsSignFrom_eq_firstEncoding, ReferenceChoice.selection, canonicalFors]
  cases hs : firstEncoding f sk.parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f
        (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)))
      (evalWithAnswerFn f (Seeded.ftsKey sk.parameter
        (digestIndex (evalWithAnswerFn f
          (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)))
        sk.seed : OracleComp HashSpec Digest)) encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, evalWithAnswerFn_pure, evalWithAnswerFn_bind,
      reduceCtorEq]

/-- The failed message need not equal the forgery message: exhaustion rules out every
canonical accepted opening at the same index. No exhaustion probability is assumed. -/
theorem accepted_after_failed_finishSign (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (failedMessage : Message) (failedRandomness : Randomness)
    (message : Message) (signature : Signature) (hb : 0 < subtreeHeight)
    (hroot : sk.root = evalWithAnswerFn f
      (Seeded.treeRoot sk.parameter topLayer rootTree sk.seed : OracleComp HashSpec Digest))
    (hfailed : evalWithAnswerFn f (Randomized.finishSign sk failedMessage failedRandomness) = none)
    (hindex : index f ⟨sk.root, sk.parameter⟩ message signature =
      digestIndex (evalWithAnswerFn f
        (messageDigest sk.parameter sk.root failedMessage failedRandomness : OracleComp HashSpec MessageDigest)))
    (hverified : evalWithAnswerFn f (Concrete.verify ⟨sk.root, sk.parameter⟩ message signature :
      OracleComp HashSpec Bool) = true) :
    ChosenException f ⟨sk.root, sk.parameter⟩ sk.seed message signature := by
  rcases accepted_chosen_classification f ⟨sk.root, sk.parameter⟩ sk.seed message signature
      hb hroot hverified with ⟨counter, hcounter, _⟩ | hexception
  · have hnone := (finishSign_none_iff_selection_none f sk failedMessage failedRandomness).mp hfailed
    simp only [chosenCounter, hindex, hnone, Option.map_none, reduceCtorEq] at hcounter
  · exact hexception

end LeanSphincs.Security.SignatureWitness
