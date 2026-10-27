import LeanFors.GraphView.EncodingPreparation
import LeanFors.LazyRun.GraphRows
import LeanFors.GraphView.Correctness

/-! Signature assembly from public structural labels and explicit coordinate disclosures.
This file establishes the exact output view; preservation of the original internal hash cost
is a separate obligation when composing the complete monitored game.

The forest opening reveals, for every tree, subtree and chain of the selected WOTS keys, the chain
values at and above the opened position `4 - d_i` (everything the signature lets anyone compute);
the subtree and tree paths are public structural labels. -/

open OracleComp OracleSpec

namespace LeanFors.Security.GraphView

variable [Params]
open Concrete Completeness Graph GraphCorrectness HiddenGraph Prefix PrunedGraph

attribute [local irreducible] firstEncoding encodingAttemptLimit Seeded.forestKey Seeded.forestOpen
  Seeded.treePath Seeded.signLayer chainWalk forestWalk sequenceFin encode
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The values the graph view fixes: the public key, the roots and paths of the layers' trees, the
forest keys and paths, and the step halves of the randomizer walks (`steps m` gives the step
`walkStep (steps m)` of message `m`). The steps are secret in the scheme; the proof bounds the game
for every table of steps. -/
structure PublicData where
  root : Digest
  forestKey : Index → ForestKey
  treeRoot : Layer → TreeIndex → Digest
  treePath : (lay : Layer) → TreeIndex → LeafIndex → Fin (layerHeight lay) → Digest
  subPath : Index → Coord → SuperIdx → SubIdx → ChildIdx → Fin subHeight → Digest
  topPath : Index → Coord → SuperIdx → Fin topHeight → Digest
  steps : Message → Randomness

/-- The message of the key at leaf `leaf` of tree `tree` of layer `lay`, read from the public data:
the root of the tree below, or the forest key at the bottom layer. -/
def PublicData.keyMessage (data : PublicData) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    HashInput :=
  if hbelow : lay.val + 1 < numLayers then
    rootPayload (data.treeRoot ⟨lay.val + 1, hbelow⟩ (childTree lay tree leaf))
  else rootsPayload (data.forestKey (childTree lay tree leaf))

def publicData (labels : CanonicalGraphLabels) (steps : Message → Randomness) : PublicData where
  steps := steps
  root := truncateHash (labels (treePosition topLayer rootTree (layerHeight topLayer)
    (layerHeight_le _) ⟨0, Nat.two_pow_pos _⟩))
  forestKey := fun index => keyLabels labels index
  treeRoot := fun lay tree => truncateHash (labels (treePosition lay tree (layerHeight lay)
    (layerHeight_le lay) ⟨0, Nat.two_pow_pos _⟩))
  treePath := fun lay tree leaf level => truncateHash (labels
    (treePosition lay tree level.val (Nat.le_of_lt (level.isLt.trans_le (layerHeight_le lay)))
      ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt) one_lt_leaf_capacity⟩))
  subPath := fun index c s j a level => truncateHash (labels
    (subPosition index c s j level.val (Nat.le_of_lt level.isLt)
      ⟨Nat.xor (a.val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt a.isLt) (by decide)⟩))
  topPath := fun index c s level => truncateHash (labels
    (topPosition index c level.val (Nat.le_of_lt level.isLt)
      ⟨Nat.xor (s.val / 2 ^ level.val) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt s.isLt) (by decide)⟩))

structure DataCorrect (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) : Prop where
  root : data.root = evalWithAnswerFn f
    (Seeded.treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest)
  forestKey : ∀ index, data.forestKey index = evalWithAnswerFn f
    (Seeded.forestKey parameter index seed : OracleComp HashSpec ForestKey)
  treeRoot : ∀ lay tree, TreeActive parameter lay tree → data.treeRoot lay tree = evalWithAnswerFn f
    (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest)
  treePath : ∀ lay tree leaf, KeyActive parameter lay tree leaf → data.treePath lay tree leaf =
    evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest))
  subPath : ∀ index c s j a, data.subPath index c s j a = Forest.canonicalSubPath f parameter index seed c s j a
  topPath : ∀ index c s, data.topPath index c s = Forest.canonicalTopPath f parameter index seed c s

theorem publicData_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels)
    (hconsistent : Consistent f parameter seed labels)
    (hboundary : BoundaryCorrect f parameter seed labels) (steps : Message → Randomness) :
    DataCorrect f parameter seed (publicData labels steps) := by
  constructor
  · exact tree_root_value f parameter seed labels hconsistent hboundary topLayer rootTree
      (treeActive_rootTree parameter)
  · exact forest_key_value f parameter seed labels hconsistent
  · intro lay tree htree
    exact tree_root_value f parameter seed labels hconsistent hboundary lay tree htree
  · intro lay tree leaf hactive
    funext level
    simpa only [publicData, canonicalTreePath, dif_pos level.isLt] using
      tree_path_sibling f parameter seed labels hconsistent hboundary lay tree
        leaf hactive level.val level.isLt
  · intro index c s j a
    funext level
    have h := sub_path_sibling f parameter seed labels hconsistent index c s j a level.val level.isLt
    simpa only [publicData, Forest.subPathExt, dif_pos level.isLt] using h
  · intro index c s
    funext level
    have h := top_path_sibling f parameter seed labels hconsistent index c s level.val level.isLt
    simpa only [publicData, Forest.topPathExt, dif_pos level.isLt] using h

/-- The public message of a retained key is the message the signer computes. -/
theorem DataCorrect.keyMessage {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
    {seed : MasterSeed} {data : PublicData} (hdata : DataCorrect f parameter seed data)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (hactive : KeyActive parameter lay tree leaf) :
    data.keyMessage lay tree leaf = evalWithAnswerFn f
      (Seeded.keyMessage parameter seed lay tree leaf : OracleComp HashSpec HashInput) := by
  unfold PublicData.keyMessage Seeded.keyMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow, dif_pos hbelow,
      hdata.treeRoot _ _ (treeActive_child parameter lay tree leaf hactive hbelow)]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  · rw [dif_neg hbelow, dif_neg hbelow, hdata.forestKey]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]

def CoordinatesCorrect (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (table : HiddenGraph.Table) : Prop :=
  (∀ lay tree leaf, KeyActive parameter lay tree leaf → ∀ chain position,
    table (.chain lay tree leaf chain position) =
      Chain.honestChain f parameter lay tree leaf chain
        (Completeness.otsSecret f parameter lay tree leaf seed chain) position.val) ∧
  (∀ index c s j a i (position : FPos), table (.fchain index c s j a i position) =
    Completeness.chainValueOf f parameter index c s j a i seed position.val)

theorem coordinates_correct (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (labels : CanonicalGraphLabels)
    (hconsistent : Consistent f parameter seed labels) :
    CoordinatesCorrect f parameter seed
      (coordinates (otsSecrets f parameter seed) (ftsSecrets f parameter seed) labels) := by
  constructor
  · intro lay tree leaf hactive chain position
    by_cases hz : position.val = 0
    · simp only [coordinates, hz, ↓reduceDIte, Chain.honestChain, chainWalk]
      rfl
    · rw [coordinates, dif_neg hz]
      have hstep : position.val - 1 < chainLength - 1 := by have := position.isLt; omega
      have h := chain_value f parameter seed labels hconsistent lay tree leaf hactive
        chain ⟨position.val - 1, hstep⟩
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ position.val), otsSecrets] using h
  · intro index c s j a i position
    by_cases hz : position.val = 0
    · simp only [coordinates, hz, ↓reduceDIte, Completeness.chainValueOf, Completeness.fwalk, forestWalk]
      rfl
    · rw [coordinates, dif_neg hz]
      have hstep : position.val - 1 < chainTop := by have := position.isLt; omega
      have h := fchain_value f parameter seed labels hconsistent index c s j a i ⟨position.val - 1, hstep⟩
      rw [Nat.sub_add_cancel (by omega : 1 ≤ position.val)] at h
      exact h

abbrev HashViewSpec := HashSpec + (Coordinate →ₒ Digest)

def reveal (coordinate : Coordinate) : OracleComp HashViewSpec Digest :=
  liftM ((Coordinate →ₒ Digest).query coordinate)

def fixedView (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table) : QueryImpl HashViewSpec Id :=
  f + (show QueryImpl (Coordinate →ₒ Digest) Id from table)

/-- The opened position of chain `i` of sub-tree `j`. -/
def openedPos (mark : CoordMark) (j : SubIdx) (i : FChain) : FPos :=
  ⟨chainTop - (lut (mark.word j) i).val, by simp only [chainTop]; omega⟩

/-- Reveal the chain values of one opened chain at and above its opened position. -/
def revealChain (index : Index) (c : Coord) (mark : CoordMark) (j : SubIdx) (i : FChain) :
    OracleComp HashViewSpec (FPos → Digest) :=
  sequenceFin fun k : FPos =>
    if (openedPos mark j i).val ≤ k.val then
      reveal (.fchain index c mark.super j (mark.child j) i k)
    else pure 0

/-- One tree's opening from the revealed chain values and the public paths. -/
def coordSource (data : PublicData) (index : Index) (c : Coord) (mark : CoordMark) :
    OracleComp HashViewSpec CoordOpening := do
  let sub ← sequenceFin fun j => do
    let cols ← sequenceFin fun i => revealChain index c mark j i
    return (⟨fun i => cols i (openedPos mark j i),
      data.subPath index c mark.super j (mark.child j)⟩ : SubOpening)
  return ⟨sub, data.topPath index c mark.super⟩

/-- The counter search of the key of layer `lay` on the path of `index`, on its public message. -/
def layerSearch (parameter : PublicParameter) (data : PublicData) (index : Index) (lay : Layer) :
    OracleComp HashSpec (Option (Counter × Encoding)) :=
  ReferenceChoice.search parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0

/-- The counter searches of every layer, stopping at the first failure. -/
def layersSearch (parameter : PublicParameter) (data : PublicData) (index : Index) :
    OracleComp HashSpec (Option (Layer → Counter × Encoding)) :=
  sequenceDep (α := fun _ => Counter × Encoding) fun lay => layerSearch parameter data index lay

/-- The layer signatures from the found counters and words, the revealed chain values and the
public paths. -/
def layerSignatures (data : PublicData) (index : Index) (found : Layer → Counter × Encoding)
    (values : Layer → ChainIndex → Digest) : (lay : Layer) → LayerSignature lay := fun lay =>
  ⟨(found lay).1, values lay, data.treePath lay (treeIndexAt index lay) (leafIndexAt index lay)⟩

/-- No coordinate is revealed when a WOTS encoding fails. On success only the 64 frontiers of every
layer and the opened forest chains are read; all path values are public structural labels. -/
def finishSource (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) : OracleComp HashViewSpec (Option Signature) := do
  let digest ← liftM (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  let some found ← liftM (layersSearch parameter data index) | return none
  let values ← sequenceFin fun lay : Layer => sequenceFin fun chain =>
    reveal (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain ((found lay).2 chain))
  let opening ← sequenceFin fun c => coordSource data index c (digestMarks digest c)
  return some ⟨randomness, opening, layerSignatures data index found values⟩

/-- The forest opening read from a coordinate table. -/
def assembledForest (data : PublicData) (table : HiddenGraph.Table) (index : Index)
    (marks : Coord → CoordMark) : Coord → CoordOpening :=
  fun c => ⟨fun j => ⟨fun i => table (.fchain index c (marks c).super j ((marks c).child j) i
      (openedPos (marks c) j i)), data.subPath index c (marks c).super j ((marks c).child j)⟩,
    data.topPath index c (marks c).super⟩

/-- The first successful encodings of every layer's key, on the public messages. -/
noncomputable def assembledEncodings (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (index : Index) : Option (Layer → Counter × Encoding) :=
  allSome fun lay => firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0

/-- The chain values of every layer read from a coordinate table at the found words. -/
def assembledValues (table : HiddenGraph.Table) (index : Index) (found : Layer → Counter × Encoding) :
    Layer → ChainIndex → Digest := fun lay chain =>
  table (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain ((found lay).2 chain))

noncomputable def assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (table : HiddenGraph.Table) (message : Message) (randomness : Randomness) :
    Option Signature :=
  let digest := evalWithAnswerFn f (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  (assembledEncodings f parameter data index).map fun found =>
    ⟨randomness, assembledForest data table index (digestMarks digest),
      layerSignatures data index found (assembledValues table index found)⟩

theorem eval_forestOpen_assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data)
    (htable : CoordinatesCorrect f parameter seed table) (index : Index) (marks : Coord → CoordMark) :
    evalWithAnswerFn f (Seeded.forestOpen parameter index marks seed :
      OracleComp HashSpec (Coord → CoordOpening)) = assembledForest data table index marks := by
  funext c
  simp only [Seeded.forestOpen, eval_sequenceFin, eval_coordOpen, assembledForest, htable.2, hdata.subPath,
    hdata.topPath, openedPos]
  rfl

theorem eval_signLayer_assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data)
    (htable : CoordinatesCorrect f parameter seed table) (root : Digest) (index : Index)
    (hland : Landed parameter index) (lay : Layer) :
    evalWithAnswerFn f (Seeded.signLayer ⟨seed, parameter, root⟩ index lay :
      OracleComp HashSpec (Option (LayerSignature lay))) =
    (firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0).map
      fun pair => (⟨pair.1, fun chain => table (.chain lay (treeIndexAt index lay) (leafIndexAt index lay)
        chain (pair.2 chain)), data.treePath lay (treeIndexAt index lay) (leafIndexAt index lay)⟩ :
          LayerSignature lay) := by
  have hactive : KeyActive parameter lay (treeIndexAt index lay) (leafIndexAt index lay) :=
    ⟨index, hland, rfl, rfl⟩
  have hchains (word : Encoding) :
      (fun chain => table (.chain lay (treeIndexAt index lay) (leafIndexAt index lay) chain (word chain))) =
      (fun chain => evalWithAnswerFn f (chainWalk parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) chain 0 (word chain).val
          (Completeness.otsSecret f parameter lay (treeIndexAt index lay) (leafIndexAt index lay) seed chain) :
            OracleComp HashSpec Digest)) := by
    funext chain
    exact htable.1 _ _ _ hactive chain (word chain)
  simp only [Seeded.signLayer, Seeded.layerMessage, evalWithAnswerFn_bind, Seeded.otsSign,
    otsSignFrom_eq_firstEncoding, ← hdata.keyMessage lay _ _ hactive, hdata.treePath _ _ _ hactive, hchains]
  cases firstEncoding f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (data.keyMessage lay (treeIndexAt index lay) (leafIndexAt index lay)) encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, evalWithAnswerFn_pure, evalWithAnswerFn_bind,
      derivedSecrets, Completeness.otsSecret]

theorem eval_finishSign_assembled (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (table : HiddenGraph.Table)
    (hdata : DataCorrect f parameter seed data)
    (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (randomness : Randomness)
    (hland : Landed parameter (digestIndex (evalWithAnswerFn f
      (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest)))) :
    evalWithAnswerFn f (Seeded.finishSign ⟨seed, parameter, data.root⟩ message randomness) =
      assembled f parameter data table message randomness := by
  simp only [Seeded.finishSign, assembled, evalWithAnswerFn_bind, sequenceLayers,
    Completeness.eval_sequenceDep,
    eval_signLayer_assembled f parameter seed data table hdata htable _ _ hland,
    Completeness.allSome_map, eval_forestOpen_assembled f parameter seed data table hdata htable,
    assembledEncodings]
  cases allSome fun lay : Layer => firstEncoding f parameter lay
      (treeIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest))) lay)
      (leafIndexAt (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest))) lay)
      (data.keyMessage lay _ _) encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, evalWithAnswerFn_pure]
  rfl

end LeanFors.Security.GraphView
