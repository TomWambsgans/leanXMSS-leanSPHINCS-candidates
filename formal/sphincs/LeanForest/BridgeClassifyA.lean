import LeanForest.BridgeClassify

/-! Accepted-signature classification keeping the recovered forest key. An accepted signature is a
canonical WOTS and tree opening at a retained leaf whose forest part recovers the canonical forest
key, a tree hit, or a WOTS exception at a retained leaf. A recovered canonical forest key is a
structural match (WOTS-key leaf, subtree node, tree leaf, tree node or roots), or every path is
canonical and every opened chain value is canonical or walks into its chain through a match. -/

open OracleComp OracleSpec

namespace LeanForest.Security.Forest
open Concrete

section Refined

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (seed : MasterSeed)

/-- The exceptional branches other than a chain match: a WOTS-key leaf, a subtree node, a tree leaf,
a tree node or the roots. -/
def StructException (marks : Coord → CoordMark) (opening : Coord → CoordOpening) : Prop :=
  (∃ c j, ChildLeafMatch f parameter index seed c (marks c) j ((opening c).sub j).values) ∨
  (∃ c j level, level < subHeight ∧ SubNodeMatch f parameter index seed c (marks c) j ((opening c).sub j) level) ∨
  (∃ c, SuperMatch f parameter index seed c (marks c) (opening c)) ∨
  (∃ c level, level < topHeight ∧ TopNodeMatch f parameter index seed c (marks c) (opening c) level) ∨
  RootsMatch f parameter index seed marks opening

/-- One subtree with the canonical root: a WOTS-key leaf match, a node match, or a canonical path
with every chain canonical or a chain match. -/
theorem sub_refined (c : Coord) (mark : CoordMark) (j : SubIdx) (opening : SubOpening)
    (hroot : opSubRoot f parameter index c mark j opening =
      Completeness.subNodeValue f parameter index c mark.super j seed subHeight 0) :
    ChildLeafMatch f parameter index seed c mark j opening.values ∨
    (∃ level, level < subHeight ∧ SubNodeMatch f parameter index seed c mark j opening level) ∨
    (opening.path = canonicalSubPath f parameter index seed c mark.super j (mark.child j) ∧
      ∀ i, opening.values i = Completeness.chainValueOf f parameter index c mark.super j (mark.child j) i seed
          (chainTop - (lut (mark.word j) i).val) ∨
        ChainMatch f parameter index seed c mark j opening.values i) := by
  classical
  have hfold : merkleValue f parameter (subDomain index c mark.super j) (mark.child j).val
      (subPathExt opening.path) (opLeaf f parameter index c mark j opening.values) subHeight =
    merkleValue f parameter (subDomain index c mark.super j) (mark.child j).val
      (subPathExt (canonicalSubPath f parameter index seed c mark.super j (mark.child j)))
      (Completeness.childLeafValue f parameter index c mark.super j seed (mark.child j)) subHeight :=
    hroot.trans (canonical_sub_root f parameter index seed c mark.super j (mark.child j)).symm
  rcases merkleFold_same_index f parameter _ (mark.child j).val _ _ _ _ subHeight hfold with
    ⟨hleaf, hpath⟩ | ⟨level, hlevel, hmatch⟩
  · have hpath' : opening.path = canonicalSubPath f parameter index seed c mark.super j (mark.child j) := by
      funext level
      have hp := hpath level.val level.isLt
      simpa only [subPathExt, dif_pos level.isLt] using hp
    by_cases hends : opEnds f parameter index c mark j opening.values =
        Completeness.childEnds f parameter index c mark.super j seed (mark.child j)
    · refine Or.inr (Or.inr ⟨hpath', fun i => ?_⟩)
      by_cases hi : opening.values i = Completeness.chainValueOf f parameter index c mark.super j
          (mark.child j) i seed (chainTop - (lut (mark.word j) i).val)
      · exact Or.inl hi
      · refine Or.inr ?_
        have hd : (lut (mark.word j) i).val ≤ chainTop := Nat.le_of_lt_succ (lut (mark.word j) i).isLt
        have hwalk : walkValue f parameter index c mark.super j (mark.child j) i
            (chainTop - (lut (mark.word j) i).val) (opening.values i) (lut (mark.word j) i).val =
          honestChain f parameter index c mark.super j (mark.child j) i
            (Completeness.forestSecret f parameter index c mark.super j (mark.child j) i seed)
            (chainTop - (lut (mark.word j) i).val + (lut (mark.word j) i).val) := by
          rw [Nat.sub_add_cancel hd]
          exact congrFun hends i
        rcases forestWalk_extract_above f parameter index c mark.super j (mark.child j) i
            (Completeness.forestSecret f parameter index c mark.super j (mark.child j) i seed)
            (chainTop - (lut (mark.word j) i).val) (opening.values i) (lut (mark.word j) i).val 0
            (by omega) (Nat.zero_le _) hwalk with h0 | ⟨offset, hoffset, _, hlt, hhit⟩
        · exact False.elim (hi (by simpa only [walkValue, forestWalk, evalWithAnswerFn_pure,
            Nat.add_zero, chainValueOf_eq_honest] using h0))
        · exact ⟨offset, hoffset, hlt, hhit⟩
    · exact Or.inl ⟨hends, hleaf⟩
  · exact Or.inr (Or.inl ⟨level, hlevel, hmatch⟩)

/-- One tree with the canonical root: a tree-leaf match, a tree-node match, or a canonical top path
with both subtree roots canonical. -/
theorem coord_refined (c : Coord) (mark : CoordMark) (opening : CoordOpening)
    (hroot : opRoot f parameter index c mark opening = Completeness.topNodeValue f parameter index c seed topHeight 0) :
    SuperMatch f parameter index seed c mark opening ∨
    (∃ level, level < topHeight ∧ TopNodeMatch f parameter index seed c mark opening level) ∨
    (opening.top = canonicalTopPath f parameter index seed c mark.super ∧
      ∀ j, opSubRoot f parameter index c mark j (opening.sub j) =
        Completeness.subNodeValue f parameter index c mark.super j seed subHeight 0) := by
  classical
  have hfold : merkleValue f parameter (topDomain index c) mark.super.val (topPathExt opening.top)
      (opSuper f parameter index c mark opening) topHeight =
    merkleValue f parameter (topDomain index c) mark.super.val
      (topPathExt (canonicalTopPath f parameter index seed c mark.super))
      (Completeness.superValue f parameter index c seed mark.super) topHeight :=
    hroot.trans (canonical_top_root f parameter index seed c mark.super).symm
  rcases merkleFold_same_index f parameter _ mark.super.val _ _ _ _ topHeight hfold with
    ⟨hsuper, hpath⟩ | ⟨level, hlevel, hmatch⟩
  · have hpath' : opening.top = canonicalTopPath f parameter index seed c mark.super := by
      funext level
      have hp := hpath level.val level.isLt
      simpa only [topPathExt, dif_pos level.isLt] using hp
    by_cases hpayload : nodePayload (opSubRoot f parameter index c mark 0 (opening.sub 0))
        (opSubRoot f parameter index c mark 1 (opening.sub 1)) =
      nodePayload (Completeness.subNodeValue f parameter index c mark.super 0 seed subHeight 0)
        (Completeness.subNodeValue f parameter index c mark.super 1 seed subHeight 0)
    · obtain ⟨h0, h1⟩ := nodePayload_injective hpayload
      refine Or.inr (Or.inr ⟨hpath', fun j => ?_⟩)
      fin_cases j
      · exact h0
      · exact h1
    · exact Or.inl ⟨hpayload, hsuper⟩
  · exact Or.inr (Or.inl ⟨level, hlevel, hmatch⟩)

/-- **Chain-by-chain classification of a recovered canonical forest key.** -/
theorem recovered_classification (marks : Coord → CoordMark) (opening : Coord → CoordOpening)
    (hrecover : evalWithAnswerFn f (forestRecover parameter index marks opening : OracleComp HashSpec Digest) =
      evalWithAnswerFn f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest)) :
    StructException f parameter index seed marks opening ∨
    ∀ c, (opening c).top = canonicalTopPath f parameter index seed c (marks c).super ∧
      (∀ j, ((opening c).sub j).path = canonicalSubPath f parameter index seed c (marks c).super j ((marks c).child j)) ∧
      ∀ j i, ((opening c).sub j).values i = Completeness.chainValueOf f parameter index c (marks c).super j
          ((marks c).child j) i seed (chainTop - (lut ((marks c).word j) i).val) ∨
        ChainMatch f parameter index seed c (marks c) j ((opening c).sub j).values i := by
  classical
  by_cases hS : StructException f parameter index seed marks opening
  · exact Or.inl hS
  right
  unfold StructException at hS
  push Not at hS
  obtain ⟨hleafS, hsubS, hsuperS, htopS, hrootsS⟩ := hS
  have hpayload : rootsPayload (roots f parameter index marks opening) =
      rootsPayload (canonicalRoots f parameter index seed) := by
    by_contra hne
    exact hrootsS ⟨hne, by rwa [← eval_forestRecover]⟩
  have hroots := rootsPayload_injective hpayload
  intro c
  have hroot : opRoot f parameter index c (marks c) (opening c) =
      Completeness.topNodeValue f parameter index c seed topHeight 0 := congrFun hroots c
  rcases coord_refined f parameter index seed c (marks c) (opening c) hroot with hsup | ⟨level, hlevel, htop⟩ |
      ⟨htop, hsubs⟩
  · exact (hsuperS c hsup).elim
  · exact (htopS c level hlevel htop).elim
  have hsub : ∀ j, ((opening c).sub j).path = canonicalSubPath f parameter index seed c (marks c).super j
      ((marks c).child j) ∧ ∀ i, ((opening c).sub j).values i = Completeness.chainValueOf f parameter index c
        (marks c).super j ((marks c).child j) i seed (chainTop - (lut ((marks c).word j) i).val) ∨
      ChainMatch f parameter index seed c (marks c) j ((opening c).sub j).values i := by
    intro j
    rcases sub_refined f parameter index seed c (marks c) j ((opening c).sub j) (hsubs j) with hl | ⟨level, hlevel, hn⟩ | h
    · exact (hleafS c j hl).elim
    · exact (hsubS c j level hlevel hn).elim
    · exact h
  exact ⟨htop, fun j => (hsub j).1, fun j => (hsub j).2⟩

end Refined

end LeanForest.Security.Forest


namespace LeanForest.Security.SignatureWitness
open Concrete

attribute [local irreducible] messageDigest forestRecover otsLeaf treeFold
  Seeded.forestKey Seeded.treeRoot Seeded.treePath chainWalk encode

variable [Params]

/-- The three WOTS exceptions at a retained leaf. -/
def WotsException (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) : Prop :=
  let leaf := index f pk message signature
  let inputs := trace f pk message signature
  ReferenceChoice.EncodingMatch f pk.parameter topLayer rootTree leaf
    (canonicalForest f pk.parameter seed leaf) inputs ∨
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
    verificationForest f pk message signature = canonicalForest f pk.parameter seed leaf

/-- A recovered opening whose FORS part is the canonical opening is a canonical opening. -/
theorem RecoveredOpening.canonical {f : QueryImpl HashSpec Id} {pk : PublicKey} {seed : MasterSeed}
    {message : Message} {signature : Signature} {counter : Counter}
    (h : RecoveredOpening f pk seed message signature counter)
    (hopening : Forest.Opening f pk.parameter (index f pk message signature) seed
      (digestMarks (verificationDigest f pk message signature)) signature.forest) :
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
          (index f pk message signature) (verificationForest f pk message signature)
          (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
          OracleComp HashSpec (Option Digest)) =
        some (Wots.canonicalLeaf f pk.parameter topLayer rootTree (index f pk message signature)
          (Completeness.otsSecret f pk.parameter topLayer rootTree (index f pk message signature) seed)) :=
        hleaf.trans (congrArg some (hopen.1.trans (canonical_wots_leaf f pk.parameter seed _)))
      obtain ⟨candidate, hencode⟩ : ∃ candidate, evalWithAnswerFn f
          (encode pk.parameter topLayer rootTree (index f pk message signature)
            (verificationForest f pk message signature) (signature.layers topLayer).counter :
            OracleComp HashSpec (Option Encoding)) = some candidate := by
        cases henc : evalWithAnswerFn f
            (encode pk.parameter topLayer rootTree (index f pk message signature)
              (verificationForest f pk message signature) (signature.layers topLayer).counter :
              OracleComp HashSpec (Option Encoding)) with
        | none =>
            simp only [otsLeaf, evalWithAnswerFn_bind, henc, evalWithAnswerFn_pure,
              reduceCtorEq] at hcanonical
        | some candidate => exact ⟨candidate, rfl⟩
      rcases ReferenceChoice.otsLeaf_classification f pk.parameter topLayer rootTree
          (index f pk message signature) (canonicalForest f pk.parameter seed (index f pk message signature))
          (Completeness.otsSecret f pk.parameter topLayer rootTree (index f pk message signature) seed)
          (verificationForest f pk message signature) (signature.layers topLayer).counter
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

/-- **The refined forest case.** -/
theorem RecoveredOpening.forest_classification {f : QueryImpl HashSpec Id} {pk : PublicKey}
    {seed : MasterSeed} {message : Message} {signature : Signature} {counter : Counter}
    (h : RecoveredOpening f pk seed message signature counter) :
    Forest.StructException f pk.parameter (index f pk message signature) seed
        (digestMarks (verificationDigest f pk message signature)) signature.forest ∨
    ∀ c, (signature.forest c).top = Forest.canonicalTopPath f pk.parameter (index f pk message signature) seed c
        (digestMarks (verificationDigest f pk message signature) c).super ∧
      (∀ j, ((signature.forest c).sub j).path = Forest.canonicalSubPath f pk.parameter (index f pk message signature)
        seed c (digestMarks (verificationDigest f pk message signature) c).super j
        ((digestMarks (verificationDigest f pk message signature) c).child j)) ∧
      ∀ j i, ((signature.forest c).sub j).values i = Completeness.chainValueOf f pk.parameter
          (index f pk message signature) c (digestMarks (verificationDigest f pk message signature) c).super j
          ((digestMarks (verificationDigest f pk message signature) c).child j) i seed
          (chainTop - (lut ((digestMarks (verificationDigest f pk message signature) c).word j) i).val) ∨
        Forest.ChainMatch f pk.parameter (index f pk message signature) seed c
          (digestMarks (verificationDigest f pk message signature) c) j ((signature.forest c).sub j).values i :=
  Forest.recovered_classification f pk.parameter (index f pk message signature) seed
    (digestMarks (verificationDigest f pk message signature)) signature.forest h.2.2.2.2

end LeanForest.Security.SignatureWitness
