import LeanSphincs.BridgeClassify

/-! Accepted-signature classification keeping the recovered FORS key. An accepted signature is a
canonical WOTS and tree opening at a retained leaf whose FORS part recovers the canonical FORS
key, a tree hit, or a WOTS exception at a retained leaf. A recovered canonical FORS key is a
match at the key hash (another list of top nodes), a node match below a top node, or every tree is
canonical or a leaf match. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Fors
open Concrete

/-- **Per-tree classification of a recovered canonical FORS key.** -/
theorem recovered_classification (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (hrecover : evalWithAnswerFn f (ftsRecover parameter index leaves secrets paths :
      OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest)) :
    TopsMatch f parameter index seed leaves secrets paths ∨
    (∃ tree level, level < ftsTopLevel ∧
      NodeMatch f parameter index tree seed (leaves tree) (secrets tree) (paths tree) level) ∨
    ∀ tree, (secrets tree = Completeness.ftsSecret f parameter index tree (leaves tree) seed ∧
        paths tree = canonicalPath f parameter index tree seed (leaves tree)) ∨
      LeafMatch f parameter index tree seed (leaves tree) (secrets tree) := by
  classical
  by_cases hpayload : ftsTopsPayload (tops f parameter index leaves secrets paths) =
      ftsTopsPayload (canonicalTops f parameter index seed)
  · have htops := ftsTopsPayload_injective hpayload
    by_cases hnode : ∃ tree level, level < ftsTopLevel ∧
        NodeMatch f parameter index tree seed (leaves tree) (secrets tree) (paths tree) level
    · exact Or.inr (Or.inl hnode)
    · refine Or.inr (Or.inr fun tree => ?_)
      rcases tree_classification f parameter index tree seed (leaves tree) (secrets tree)
        (paths tree) (congrFun htops tree) with hopen | hleaf | ⟨level, hlevel, hmatch⟩
      · exact Or.inl hopen
      · exact Or.inr hleaf
      · exact (hnode ⟨tree, level, hlevel, hmatch⟩).elim
  · refine Or.inl ⟨hpayload, ?_⟩
    rwa [← eval_ftsRecover]

end LeanSphincs.Security.Fors

namespace LeanSphincs.Security.SignatureWitness
open Concrete

attribute [local irreducible] messageDigest ftsRecover otsLeaf treeFold
  Seeded.ftsKey Seeded.treeRoot Seeded.treePath chainWalk encode

variable [Params]

/-- The three WOTS exceptions at a retained leaf. -/
def WotsException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  let leaf := index f pk message signature
  let inputs := trace f pk message signature
  ReferenceChoice.EncodingMatch f pk.parameter topLayer rootTree leaf
    (canonicalFors f pk.parameter seed leaf) inputs ∨
  Wots.LeafOutputMatch f pk.parameter topLayer rootTree leaf
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs ∨
  Wots.ChainException f pk.parameter topLayer rootTree leaf (chosenWord f pk.parameter seed leaf)
    (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) inputs

/-- A canonical WOTS and tree opening at a retained leaf whose FORS part recovers the canonical
FORS key. -/
def RecoveredOpening (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (referenceCounter : Counter) : Prop :=
  let leaf := index f pk message signature
  Landed pk.parameter leaf ∧
    (signature.layers topLayer).counter = referenceCounter ∧
    (signature.layers topLayer).chainValues = Wots.frontier f pk.parameter topLayer rootTree leaf
      (chosenWord f pk.parameter seed leaf) (Completeness.otsSecret f pk.parameter topLayer rootTree leaf seed) ∧
    (signature.layers topLayer).path = evalWithAnswerFn f
      (Seeded.treePath pk.parameter topLayer rootTree seed leaf :
        OracleComp HashSpec (Fin (layerHeight topLayer) → Digest)) ∧
    verificationFors f pk message signature = canonicalFors f pk.parameter seed leaf

/-- A recovered opening whose FORS part is the canonical opening is a canonical opening. -/
theorem RecoveredOpening.canonical {f : QueryImpl HashSpec Id} {pk : PublicKey} {seed : MasterSeed}
    {message : Message} {signature : Signature} {counter : Counter}
    (h : RecoveredOpening f pk seed message signature counter)
    (hopening : Fors.Opening f pk.parameter (index f pk message signature) seed
      (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath) :
    CanonicalOpening f pk seed message signature counter
      (chosenWord f pk.parameter seed (index f pk message signature)) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hopening⟩

/-- **Recovered canonical FORS key, a tree hit, or a WOTS exception at a retained leaf.** -/
theorem accepted_recovered_classification (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (seed : MasterSeed) (message : Message) (signature : Signature) (hb : 0 < subtreeHeight)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    (∃ counter, chosenCounter f pk.parameter seed (index f pk message signature) = some counter ∧
      RecoveredOpening f pk seed message signature counter) ∨
    TreeHit f pk seed message signature ∨
    (Landed pk.parameter (index f pk message signature) ∧
      WotsException f pk seed message signature) := by
  obtain ⟨value, hleaf, hfold, hrunLeaf, hrunTree⟩ := verified_tree f pk message signature hverified
  have hfold' := hfold.trans hroot
  by_cases hland : Landed pk.parameter (index f pk message signature)
  · rcases inside_subtree_treeFold_witness f pk.parameter topLayer rootTree seed
        (index f pk message signature) (signaturePath signature topLayer) value hland hfold' with
      hopen | hmatch
    · have hcanonical : evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
          (index f pk message signature) (verificationFors f pk message signature)
          (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
          OracleComp HashSpec (Option Digest)) =
        some (Wots.canonicalLeaf f pk.parameter topLayer rootTree (index f pk message signature)
          (Completeness.otsSecret f pk.parameter topLayer rootTree (index f pk message signature) seed)) :=
        hleaf.trans (congrArg some (hopen.1.trans (canonical_wots_leaf f pk.parameter seed _)))
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
          hencode hrunLeaf hcanonical with
        ⟨counter, hselected, hfors, hcounter, hvalues⟩ | hencoding | hleafMatch | hchain
      · refine Or.inl ⟨counter, ?_, hland, hcounter, funext hvalues, ?_, hfors⟩
        · simp only [chosenCounter, hselected, Option.map_some]
        · funext level
          have hp := hopen.2 level.val level.isLt
          simpa only [index, signaturePath, canonicalTreePath, dif_pos level.isLt] using hp
      · exact Or.inr (Or.inr ⟨hland, Or.inl hencoding⟩)
      · exact Or.inr (Or.inr ⟨hland, Or.inr (Or.inl hleafMatch)⟩)
      · exact Or.inr (Or.inr ⟨hland, Or.inr (Or.inr hchain)⟩)
    · exact Or.inr (Or.inl ⟨value, hleaf, hrunTree,
        Or.inl ⟨index f pk message signature, hland, hmatch⟩⟩)
  · let reference := keptLeafEquiv pk.parameter ⟨0, Nat.two_pow_pos _⟩
    rcases outside_witness_address f pk.parameter seed (index f pk message signature) reference.val
        (signaturePath signature topLayer) value hb reference.property hland hfold' with
      hmatch | hsurrogate
    · exact Or.inr (Or.inl ⟨value, hleaf, hrunTree, Or.inl ⟨reference.val, reference.property, hmatch⟩⟩)
    · exact Or.inr (Or.inl ⟨value, hleaf, hrunTree, Or.inr hsurrogate⟩)

/-- **The refined FORS case.** A recovered canonical FORS key is a match at the key hash, a node
match at some tree below its top node, or every tree is canonical (secret and path) or a leaf
match. -/
theorem RecoveredOpening.fors_classification {f : QueryImpl HashSpec Id} {pk : PublicKey}
    {seed : MasterSeed} {message : Message} {signature : Signature} {counter : Counter}
    (h : RecoveredOpening f pk seed message signature counter) :
    Fors.TopsMatch f pk.parameter (index f pk message signature) seed
        (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath ∨
    (∃ tree level, level < ftsTopLevel ∧
      Fors.NodeMatch f pk.parameter (index f pk message signature) tree seed
        (digestLeaves (verificationDigest f pk message signature) tree) (signature.ftsSecret tree)
        (signature.ftsPath tree) level) ∨
    ∀ tree, (signature.ftsSecret tree = Completeness.ftsSecret f pk.parameter (index f pk message signature)
          tree (digestLeaves (verificationDigest f pk message signature) tree) seed ∧
        signature.ftsPath tree = Fors.canonicalPath f pk.parameter (index f pk message signature) tree seed
          (digestLeaves (verificationDigest f pk message signature) tree)) ∨
      Fors.LeafMatch f pk.parameter (index f pk message signature) tree seed
        (digestLeaves (verificationDigest f pk message signature) tree) (signature.ftsSecret tree) :=
  Fors.recovered_classification f pk.parameter (index f pk message signature) seed
    (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath h.2.2.2.2

end LeanSphincs.Security.SignatureWitness
