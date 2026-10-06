import LeanForest.SecurityGraphSigner
import LeanForest.SecurityPrefixErasedKeygen
import LeanForest.SecurityHiddenCost

/-! Exact original honest hash costs for the graph-reveal signer. The simulation retains
ordinary message/encoding queries and represents the remaining internal work by explicit
natural-number ticks, including work performed before a failed WOTS search. -/

open OracleComp OracleSpec

namespace LeanForest.Security.GraphView
open Concrete Completeness Prefix
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] firstEncoding ReferenceChoice.search encodingAttemptLimit
  Seeded.forestKey Seeded.forestOpen Seeded.treePath Seeded.otsSignFrom Seeded.signLayer
  chainWalk forestWalk sequenceFin encode

theorem hashCalls_forsKey_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) :
    hashCalls f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest) = 65529 :=
  hashCalls_forestKey f parameter index seed

/-- Opening one tree costs 8168 calls: 25 chain calls and 221 subtree-path calls per subtree (the
opened positions sum to `6 · 4 - 5`), and 7676 tree-path calls. -/
theorem hashCalls_coordOpen_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (c : Coord) (mark : CoordMark) (seed : MasterSeed) :
    hashCalls f (Seeded.coordOpen parameter index c mark seed : OracleComp HashSpec CoordOpening) = 8168 := by
  rw [Seeded.coordOpen, hashCalls_bind, hashCalls_bind, hashCalls_sequenceFin, hashCalls_sequenceFin]
  simp only [hashCalls_bind, hashCalls_sequenceFin, hashCalls_pure, Nat.add_zero]
  have hchain : ∀ (j : SubIdx) (i : FChain),
      hashCalls f (Seeded.chainValue parameter index c mark.super j (mark.child j) i seed
        (chainTop - (lut (mark.word j) i).val) : OracleComp HashSpec Digest) =
        1 + (chainTop - (lut (mark.word j) i).val) := fun j i =>
    hashCalls_chainValue f parameter index c _ j _ i seed _ (Nat.sub_le _ _)
  have hsum : ∀ j : SubIdx, ∑ i : FChain, (1 + (chainTop - (lut (mark.word j) i).val)) = 25 := by
    intro j
    have hle : ∀ i : FChain, (lut (mark.word j) i).val ≤ chainTop := fun i =>
      Nat.le_of_lt_succ (lut (mark.word j) i).isLt
    have hs := Completeness.lut_sum (mark.word j)
    have : ∑ i : FChain, (1 + (chainTop - (lut (mark.word j) i).val)) + ∑ i, (lut (mark.word j) i).val =
        ∑ i : FChain, (1 + chainTop) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by have := hle i; omega
    rw [hs] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, chainTop,
      codewordSum, childChains] at this ⊢
    omega
  have hsub : ∀ (j : SubIdx) (level : Fin subHeight),
      hashCalls f (Seeded.subNode parameter index c mark.super j seed level.val
        (Nat.xor ((mark.child j).val / 2 ^ level.val) 1) : OracleComp HashSpec Digest) =
        32 * 2 ^ level.val - 1 := fun j level =>
    hashCalls_subNode f parameter index c _ j seed _ _ (Nat.le_of_lt level.isLt)
  have htop : ∀ level : Fin topHeight,
      hashCalls f (Seeded.topNode parameter index c seed level.val
        (Nat.xor (mark.super.val / 2 ^ level.val) 1) : OracleComp HashSpec Digest) =
        512 * 2 ^ level.val - 1 := fun level =>
    hashCalls_topNode f parameter index c seed _ _ (Nat.le_of_lt level.isLt)
  simp only [hchain, hsum, hsub, htop]
  decide

theorem hashCalls_forsOpen_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (marks : Coord → CoordMark) (seed : MasterSeed) :
    hashCalls f (Seeded.forestOpen parameter index marks seed :
      OracleComp HashSpec (Coord → CoordOpening)) = 65344 := by
  simp only [Seeded.forestOpen, hashCalls_sequenceFin, hashCalls_coordOpen_exact]
  decide

theorem hashCalls_published_values (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (word : Encoding)
    (hword : TargetSum.Valid word) :
    hashCalls f (sequenceFin fun chain => do
      let secret ← (deriveKey parameter (.ots lay tree leaf chain) seed : OracleComp HashSpec Digest)
      chainWalk parameter lay tree leaf chain 0 (word chain).val secret) = 184 := by
  simp only [hashCalls_sequenceFin, hashCalls_bind, hashCalls_deriveKey]
  have hwalk (chain : ChainIndex) (value : Digest) :
      hashCalls f (chainWalk parameter lay tree leaf chain 0 (word chain).val value :
        OracleComp HashSpec Digest) = (word chain).val :=
    hashCalls_chainWalk f parameter lay tree leaf chain 0 (word chain).val value
      (by have := (word chain).isLt; omega)
  simp only [hwalk, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  change numChains + TargetSum.sum word = 184
  rw [show TargetSum.sum word = targetSum from hword]
  rfl

theorem hashCalls_otsSignFrom_search (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : Digest)
    (attempts start : Nat) :
    hashCalls f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
      hashCalls f (ReferenceChoice.search parameter lay tree leaf message attempts start) +
        if (firstEncoding f parameter lay tree leaf message attempts start).isSome then 184 else 0 := by
  induction attempts generalizing start with
  | zero => simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding, hashCalls_pure,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  | succ attempts ih =>
      cases he : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, ih]
          omega
      | some word =>
          have hvalid := EncodingCode.decode_valid (Wots.decode_of_encode f parameter lay tree leaf
            message (BitVec.ofNat counterBits start) word he)
          simp only [Seeded.otsSignFrom, ReferenceChoice.search, firstEncoding,
            hashCalls_bind, hashCalls_encode, he, hashCalls_pure,
            hashCalls_published_values f parameter lay tree leaf seed word hvalid,
            Option.isSome_some, ↓reduceIte, Nat.add_zero]

variable [Params]

def treePathCost : Nat :=
  ∑ level : Fin totalHeight, if level.val < subtreeHeight then 258 * 2 ^ level.val - 1 else 1

theorem hashCalls_treePath_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.treePath parameter lay tree seed leaf :
      OracleComp HashSpec (Fin (layerHeight lay) → Digest)) = treePathCost := by
  simp only [Seeded.treePath, hashCalls_sequenceFin, treePathCost]
  apply Finset.sum_congr rfl
  intro level _
  split
  · exact hashCalls_treeNode f parameter lay tree seed _ _
  · have hlevel : level.val < totalHeight := level.isLt
    simp only [Seeded.surrogate, dif_pos hlevel, hashCalls_deriveKey]

theorem hashCalls_signLayer_exact (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (index : Index) (lay : Layer) :
    hashCalls f (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) =
      65529 + hashCalls f (ReferenceChoice.search sk.parameter lay rootTree index
        (evalWithAnswerFn f (Seeded.forestKey sk.parameter index sk.seed : OracleComp HashSpec Digest))
        encodingAttemptLimit 0) +
      if (firstEncoding f sk.parameter lay rootTree index
        (evalWithAnswerFn f (Seeded.forestKey sk.parameter index sk.seed : OracleComp HashSpec Digest))
        encodingAttemptLimit 0).isSome then 184 + treePathCost else 0 := by
  simp only [Seeded.signLayer, Seeded.layerMessage, hashCalls_bind, hashCalls_forsKey_exact,
    treeIndexAt_eq, leafIndexAt_eq, Seeded.otsSign, hashCalls_otsSignFrom_search,
    otsSignFrom_eq_firstEncoding]
  cases hs : firstEncoding f sk.parameter lay rootTree index
      (evalWithAnswerFn f (Seeded.forestKey sk.parameter index sk.seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 <;>
    simp only [Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
      Bool.false_eq_true, ↓reduceIte, hashCalls_pure, hashCalls_bind, hashCalls_treePath_exact,
      Nat.add_zero]
  omega

noncomputable def finishHashCost (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (data : PublicData) (message : Message) (randomness : Randomness) : Nat :=
  let index := digestIndex (evalWithAnswerFn f
    (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))
  130874 + hashCalls f (ReferenceChoice.search parameter topLayer rootTree index
    (data.forestKey index) encodingAttemptLimit 0) +
    if (firstEncoding f parameter topLayer rootTree index (data.forestKey index)
      encodingAttemptLimit 0).isSome then 184 + treePathCost else 0

/-- The 130874 calls include the digest block, the forest opening (chain values and all subtree
and tree authentication nodes) and the canonical forest-key computation, even when WOTS fails. -/
theorem hashCalls_finishSign_exact (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData) (hdata : DataCorrect f parameter seed data)
    (message : Message) (randomness : Randomness) :
    hashCalls f (Randomized.finishSign ⟨seed, parameter, data.root⟩ message randomness) =
      finishHashCost f parameter data message randomness := by
  simp only [Randomized.finishSign, hashCalls_bind, hashCalls_messageDigest, hashCalls_forsOpen_exact,
    hashCalls_sequenceLayers, hashCalls_signLayer_exact, finishHashCost, hdata.forestKey]
  cases hLayer : evalWithAnswerFn f (sequenceLayers fun lay =>
      Seeded.signLayer ⟨seed, parameter, data.root⟩
        (digestIndex (evalWithAnswerFn f
          (messageDigest parameter data.root message randomness : OracleComp HashSpec MessageDigest))) lay) <;>
    simp only [hashCalls_pure] <;> omega

end LeanForest.Security.GraphView
