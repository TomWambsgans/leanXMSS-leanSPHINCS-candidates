import LeanSphincs.SecurityGameWitness

/-!
Reference-free WOTS extraction. A valid 64-digit encoding of sum 120 has a digit at most one,
so canonical endpoint recovery forces two linked chain queries. This requires no successful
honest encoding at the leaf. The extraction holds for all signatures, including honest ones;
an unused-leaf/disclosure invariant and query-order analysis are still needed to assign a
probability to the resulting witness.
-/

open OracleComp OracleSpec
open scoped BigOperators

namespace LeanSphincs.Security.Unsigned
open Concrete Chain

attribute [local irreducible] chainWalk Finset.univ

/-- A sum-120 word cannot have all 64 digits at least two. -/
theorem valid_has_two_step_digit (word : Encoding) (hvalid : TargetSum.Valid word) :
    ∃ index, (word index).val ≤ 1 := by
  by_contra hnone
  push Not at hnone
  have hsum : (∑ _index : ChainIndex, 2) ≤ TargetSum.sum word :=
    Finset.sum_le_sum (fun index _ => by have := hnone index; omega)
  have hvalue : TargetSum.sum word = 120 := hvalid
  rw [hvalue] at hsum
  norm_num [Finset.sum_const, numChains] at hsum

/-- The terminal chain position, used as a reference without needing an encoding certificate. -/
def endpointDigit : Digit := ⟨chainLength - 1, by decide⟩

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest)

/-- Two linked queries ending at one canonical chain endpoint. -/
def EndpointTwoEdge (trace : List HashInput) : Prop :=
  ∃ index, TwoEdge f parameter lay tree leaf index endpointDigit
    (honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)) trace

/-- Canonical endpoint recovery alone suffices for the linked-query witness. -/
theorem endpoints_twoEdge (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (candidate : Encoding) (trace : List HashInput)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hendpoints : ∀ index, evalWithAnswerFn f
      (recoverChain parameter lay tree leaf index (candidate index) (values index)) =
        honestChain f parameter lay tree leaf index (secret index) (chainLength - 1)) :
    EndpointTwoEdge f parameter lay tree leaf secret trace := by
  have hvalid := EncodingCode.decode_valid
    (Wots.decode_of_encode f parameter lay tree leaf message counter candidate hencode)
  obtain ⟨index, hlow⟩ := valid_has_two_step_digit candidate hvalid
  refine ⟨index, recover_twoEdge f parameter lay tree leaf index endpointDigit
    (candidate index) (values index) _ trace ?_ ?_ ?_⟩
  · change (candidate index).val + 2 ≤ 3
    omega
  · exact hendpoints index
  · exact Wots.otsLeaf_chain_run f parameter lay tree leaf message counter values candidate
      trace hencode hrun index

/-- Without any honest encoding reference, canonical WOTS-leaf recovery gives a leaf hash
match or two linked queries to a canonical endpoint. -/
theorem otsLeaf_classification (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (candidate : Encoding) (trace : List HashInput)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter :
      OracleComp HashSpec (Option Encoding)) = some candidate)
    (hrun : ContainsRun f trace (otsLeaf parameter lay tree leaf message counter values))
    (hleaf : evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values :
      OracleComp HashSpec (Option Digest)) = some (Wots.canonicalLeaf f parameter lay tree leaf secret)) :
    Wots.LeafOutputMatch f parameter lay tree leaf secret trace ∨
      EndpointTwoEdge f parameter lay tree leaf secret trace := by
  let endpoints := fun index => evalWithAnswerFn f
    (recoverChain parameter lay tree leaf index (candidate index) (values index))
  have heval : evalWithAnswerFn f (leafHash parameter lay tree leaf endpoints) =
      Wots.canonicalLeaf f parameter lay tree leaf secret := by
    simpa only [otsLeaf, evalWithAnswerFn_bind, hencode, Completeness.eval_sequenceFin,
      evalWithAnswerFn_pure, Option.some.injEq, endpoints] using hleaf
  by_cases hp : leafPayload endpoints = leafPayload
      (fun index => honestChain f parameter lay tree leaf index (secret index) (chainLength - 1))
  · exact Or.inr (endpoints_twoEdge f parameter lay tree leaf secret message counter values
      candidate trace hencode hrun (fun index => congrFun (Wots.leafPayload_injective hp) index))
  · refine Or.inl ⟨endpoints, hp, ?_, ?_⟩
    · exact hrun _ (Wots.otsLeaf_leaf_query_mem f parameter lay tree leaf message counter
        values candidate hencode)
    · simpa only [leafHash, Completeness.eval_tweakableHash] using heval

variable [Params]

/-- The complete verifier's reference-free structural alternatives. The tree branch retains
the actual recovered value and its query subrun. The linked-edge branch alone does not assert
that either edge was fresh or absent from prior honest signatures. -/
def SignatureEvent (pk : PublicKey) (seed : MasterSeed) (message : Message)
    (signature : Signature) : Prop :=
  let index := digestIndex (verificationDigest f pk message signature)
  let trace := queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool)
  (∃ value,
    evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree index
      (verificationFors f pk message signature) (signature.layers topLayer).counter
      (signature.layers topLayer).chainValues : OracleComp HashSpec (Option Digest)) = some value ∧
    TreeException f pk.parameter seed index (signaturePath signature topLayer) value ∧
    ContainsRun f trace (treeFold pk.parameter topLayer rootTree index
      (signaturePath signature topLayer) totalHeight value : OracleComp HashSpec Digest)) ∨
  Wots.LeafOutputMatch f pk.parameter topLayer rootTree index
    (Completeness.otsSecret f pk.parameter topLayer rootTree index seed) trace ∨
  EndpointTwoEdge f pk.parameter topLayer rootTree index
    (Completeness.otsSecret f pk.parameter topLayer rootTree index seed) trace

/-- Every accepted signature at a generated root has a reference-free structural witness.
This theorem does not posit an encoding certificate for an unsigned leaf. -/
theorem accepted_classification (pk : PublicKey) (seed : MasterSeed) (message : Message)
    (signature : Signature) (hb : 0 < subtreeHeight)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    SignatureEvent f pk seed message signature := by
  obtain ⟨value, hleaf, htree⟩ := verified_pruned_tree f pk seed message signature hb hroot hverified
  obtain ⟨actual, hactual, _, hrunWots, hrunTree⟩ := verified_tree f pk message signature hverified
  have heq : actual = value := Option.some.inj (hactual.symm.trans hleaf)
  subst actual
  rcases htree with hopen | hexception
  · refine Or.inr ?_
    have hcanonical : evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f pk message signature)) (verificationFors f pk message signature)
        (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
        OracleComp HashSpec (Option Digest)) =
        some (Wots.canonicalLeaf f pk.parameter topLayer rootTree
          (digestIndex (verificationDigest f pk message signature))
          (Completeness.otsSecret f pk.parameter topLayer rootTree
            (digestIndex (verificationDigest f pk message signature)) seed)) :=
      hleaf.trans (congrArg some (hopen.2.1.trans
        (SignatureWitness.canonical_wots_leaf f pk.parameter seed _)))
    obtain ⟨candidate, hencode⟩ : ∃ candidate, evalWithAnswerFn f
        (encode pk.parameter topLayer rootTree (digestIndex (verificationDigest f pk message signature))
          (verificationFors f pk message signature) (signature.layers topLayer).counter :
          OracleComp HashSpec (Option Encoding)) = some candidate := by
      cases henc : evalWithAnswerFn f (encode pk.parameter topLayer rootTree
          (digestIndex (verificationDigest f pk message signature))
          (verificationFors f pk message signature) (signature.layers topLayer).counter :
          OracleComp HashSpec (Option Encoding)) with
      | none => simp only [otsLeaf, evalWithAnswerFn_bind, henc,
          evalWithAnswerFn_pure, reduceCtorEq] at hcanonical
      | some candidate => exact ⟨candidate, rfl⟩
    exact otsLeaf_classification f pk.parameter topLayer rootTree
      (digestIndex (verificationDigest f pk message signature)) _
      (verificationFors f pk message signature) (signature.layers topLayer).counter
      (signature.layers topLayer).chainValues candidate _ hencode hrunWots hcanonical
  · exact Or.inl ⟨value, hleaf, hexception, hrunTree⟩

end LeanSphincs.Security.Unsigned

namespace LeanSphincs.Security
open Concrete Completeness

attribute [local irreducible] Seeded.keygenFromSeed Seeded.treeRoot Seeded.treeNode
  Randomized.sign Randomized.finishSign digestAttemptLimit encodingAttemptLimit sampleMasterSeed

variable [Params]

/-- Supported actual success always feeds the reference-free verifier classification, with
every verifier input present in the final shared ROM cache. -/
theorem SuccessWitness.reference_free_classification {adversary : Adversary}
    {finalCache : QueryCache HashSpec} (witness : SuccessWitness)
    (h : witness.Supported adversary finalCache) (hb : 0 < subtreeHeight)
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    Unsigned.SignatureEvent f witness.pk witness.seed witness.forgery.message witness.forgery.signature ∧
    ∀ input ∈ queriedInputs f (Concrete.verify witness.pk witness.forgery.message
      witness.forgery.signature : OracleComp HashSpec Bool), finalCache input = some (f input) := by
  obtain ⟨hkey, hverified⟩ := witness.replay_with h f hf
  exact ⟨Unsigned.accepted_classification f witness.pk witness.seed witness.forgery.message
    witness.forgery.signature hb (keygen_root f witness.seed witness.pk witness.sk hkey) hverified,
    witness.verifier_inputs_cached h f hf⟩

end LeanSphincs.Security
