import LeanSphincs.SecurityReferenceChoice
import LeanSphincs.SecuritySignatureWitness

/-! Complete accepted-signature extraction using the actual canonical encoding search,
including unsigned leaves and exhausted searches. No honest reference certificate is assumed. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.SignatureWitness
open Concrete

attribute [local irreducible] messageDigest ftsRecover otsLeaf treeFold
  Seeded.ftsKey Seeded.treeRoot Seeded.treePath chainWalk encode

noncomputable def chosenWord (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : Encoding :=
  ReferenceChoice.word f parameter topLayer rootTree leaf (canonicalFors f parameter seed leaf)

noncomputable def chosenCounter (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (leaf : Index) : Option Counter :=
  (ReferenceChoice.selection f parameter topLayer rootTree leaf
    (canonicalFors f parameter seed leaf)).map Prod.fst

variable [Params]

def ChosenException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  let leaf := index f pk message signature
  let inputs := trace f pk message signature
  (∃ value, TreeException f pk.parameter seed leaf (signaturePath signature topLayer) value) ∨
  ReferenceChoice.EncodingMatch f pk.parameter topLayer rootTree leaf
    (canonicalFors f pk.parameter seed leaf) inputs ∨
  Wots.LeafOutputMatch f pk.parameter topLayer rootTree leaf
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  Wots.ChainException f pk.parameter topLayer rootTree leaf (chosenWord f pk.parameter seed leaf)
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  ForsException f pk seed message signature

/-- Every accepted signature is the chosen canonical opening or gives a concrete exceptional
query. This also covers a leaf whose canonical WOTS encoding search never succeeds. -/
theorem accepted_chosen_classification (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (seed : MasterSeed) (message : Message) (signature : Signature) (hb : 0 < subtreeHeight)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    (∃ counter, chosenCounter f pk.parameter seed (index f pk message signature) = some counter ∧
      CanonicalOpening f pk seed message signature counter
        (chosenWord f pk.parameter seed (index f pk message signature))) ∨
    ChosenException f pk seed message signature := by
  obtain ⟨value, hleaf, htree⟩ := verified_pruned_tree f pk seed message signature hb hroot hverified
  rcases htree with hopen | hexception
  · obtain ⟨_, _, _, hrun, _⟩ := verified_tree f pk message signature hverified
    have hcanonical : evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
        (index f pk message signature) (verificationFors f pk message signature)
        (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
        OracleComp HashSpec (Option Digest)) =
      some (Wots.canonicalLeaf f pk.parameter topLayer rootTree (index f pk message signature)
        (Completeness.otsSecret f pk.parameter topLayer rootTree (index f pk message signature) seed)) :=
      hleaf.trans (congrArg some (hopen.2.1.trans (canonical_wots_leaf f pk.parameter seed _)))
    obtain ⟨candidate, hencode⟩ : ∃ candidate, evalWithAnswerFn f
        (encode pk.parameter topLayer rootTree (index f pk message signature)
          (verificationFors f pk message signature) (signature.layers topLayer).counter :
          OracleComp HashSpec (Option Encoding)) = some candidate := by
      cases henc : evalWithAnswerFn f
          (encode pk.parameter topLayer rootTree (index f pk message signature)
            (verificationFors f pk message signature) (signature.layers topLayer).counter :
            OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [otsLeaf, evalWithAnswerFn_bind, henc, evalWithAnswerFn_pure,
            reduceCtorEq] at hcanonical
      | some candidate => exact ⟨candidate, rfl⟩
    rcases ReferenceChoice.otsLeaf_classification f pk.parameter topLayer rootTree
        (index f pk message signature) (canonicalFors f pk.parameter seed (index f pk message signature))
        (Completeness.otsSecret f pk.parameter topLayer rootTree (index f pk message signature) seed)
        (verificationFors f pk message signature) (signature.layers topLayer).counter
        (signature.layers topLayer).chainValues candidate (trace f pk message signature)
        hencode hrun hcanonical with
      ⟨counter, hselected, hfors, hcounter, hvalues⟩ | hencoding | hleafMatch | hchain
    · rcases Fors.recover_classification f pk.parameter (index f pk message signature) seed
          (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath
          hfors with hforsOpening | hforsException
      · refine Or.inl ⟨counter, ?_, hopen.1, hcounter, funext hvalues, ?_, hforsOpening⟩
        · simp only [chosenCounter, hselected, Option.map_some]
        · funext level
          have hp := hopen.2.2 level.val level.isLt
          simpa only [index, signaturePath, canonicalTreePath, dif_pos level.isLt] using hp
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hforsException, ?_⟩))))
        obtain ⟨input, canonicalInput, hinput, hne, hout⟩ :=
          Fors.Exception.queried_output_match f pk.parameter (index f pk message signature) seed
            (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath
            hforsException
        exact ⟨input, canonicalInput, verification_fors_run f pk message signature input hinput, hne, hout⟩
    · exact Or.inr (Or.inr (Or.inl hencoding))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hleafMatch)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hchain))))
  · exact Or.inr (Or.inl ⟨value, hexception⟩)

end LeanSphincs.Security.SignatureWitness
