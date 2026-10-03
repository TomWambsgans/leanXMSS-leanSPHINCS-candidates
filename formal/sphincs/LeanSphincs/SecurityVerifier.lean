import LeanSphincs.SecurityChainWitness
import LeanSphincs.Correctness

/-! The actual one-layer verifier exposes its WOTS leaf and Merkle fold in its query trace. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security
open Concrete

attribute [local semireducible] Concrete.verify
attribute [local irreducible] messageDigest ftsRecover otsLeaf treeFold

theorem verify_eq_single_layer (pk : PublicKey) (message : Message) (signature : Signature) :
    (Concrete.verify pk message signature : OracleComp HashSpec Bool) = (do
      let digest ← messageDigest pk.parameter pk.root message signature.randomness
      let index := digestIndex digest
      let fts ← ftsRecover pk.parameter index (digestLeaves digest) signature.ftsSecret signature.ftsPath
      let some value ← otsLeaf pk.parameter topLayer rootTree index fts
        (signature.layers topLayer).counter (signature.layers topLayer).chainValues | return false
      let root ← treeFold pk.parameter topLayer rootTree index (signaturePath signature topLayer)
        totalHeight value
      return decide (root = pk.root)) := by
  simp only [Concrete.verify, numLayers, verifyLayers]
  simp only [show (0 : Nat) < 1 by decide, ↓reduceDIte, Completeness.treeIndexAt_eq,
    Completeness.leafIndexAt_eq, bind_assoc]
  apply bind_congr
  intro digest
  apply bind_congr
  intro fts
  apply bind_congr
  intro result
  cases result with
  | none => simp
  | some value =>
      simp only [bind_assoc, pure_bind]
      rfl

/-- Digest used by the verifier, with its complete two-call hash layout. -/
def verificationDigest (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : MessageDigest :=
  evalWithAnswerFn f (messageDigest pk.parameter pk.root message signature.randomness :
    OracleComp HashSpec MessageDigest)

/-- The candidate FORS key recovered before WOTS verification. -/
def verificationFors (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) : Digest :=
  let digest := verificationDigest f pk message signature
  evalWithAnswerFn f (ftsRecover pk.parameter (digestIndex digest) (digestLeaves digest)
    signature.ftsSecret signature.ftsPath : OracleComp HashSpec Digest)

theorem verification_fors_run (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (ftsRecover pk.parameter (digestIndex (verificationDigest f pk message signature))
        (digestLeaves (verificationDigest f pk message signature)) signature.ftsSecret signature.ftsPath) := by
  have hrun : ContainsRun f
      (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) := fun _ hi => hi
  rw [verify_eq_single_layer] at hrun
  simpa only [← verify_eq_single_layer pk message signature, verificationDigest] using
    hrun.bind_right.bind_left

/-- Successful verification contains a WOTS recovery and a root-matching Merkle fold. -/
theorem verified_tree (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature)
    (hverified : evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    ∃ value,
      evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f pk message signature))
        (verificationFors f pk message signature)
        (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
        OracleComp HashSpec (Option Digest)) = some value ∧
      evalWithAnswerFn f (treeFold pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f pk message signature)) (signaturePath signature topLayer)
        totalHeight value : OracleComp HashSpec Digest) = pk.root ∧
      ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
        (otsLeaf pk.parameter topLayer rootTree (digestIndex (verificationDigest f pk message signature))
          (verificationFors f pk message signature)
          (signature.layers topLayer).counter (signature.layers topLayer).chainValues) ∧
      ContainsRun f (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
        (treeFold pk.parameter topLayer rootTree (digestIndex (verificationDigest f pk message signature))
          (signaturePath signature topLayer) totalHeight value) := by
  have hrun : ContainsRun f
      (queriedInputs f (Concrete.verify pk message signature : OracleComp HashSpec Bool))
      (Concrete.verify pk message signature : OracleComp HashSpec Bool) := fun _ hi => hi
  rw [verify_eq_single_layer] at hrun hverified
  simp only [evalWithAnswerFn_bind] at hverified
  have htail := hrun.bind_right.bind_right
  change ContainsRun f _ (otsLeaf pk.parameter topLayer rootTree
    (digestIndex (verificationDigest f pk message signature))
    (verificationFors f pk message signature)
    (signature.layers topLayer).counter (signature.layers topLayer).chainValues >>= _) at htail
  cases hleaf : evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
      (digestIndex (verificationDigest f pk message signature)) (verificationFors f pk message signature)
      (signature.layers topLayer).counter (signature.layers topLayer).chainValues : OracleComp HashSpec _) with
  | none =>
      have hleaf' := hleaf
      simp only [verificationDigest, verificationFors] at hleaf'
      simp only [hleaf', evalWithAnswerFn_pure, Bool.false_eq_true] at hverified
  | some value =>
      refine ⟨value, rfl, ?_, ?_, ?_⟩
      · have hleaf' := hleaf
        simp only [verificationDigest, verificationFors] at hleaf'
        simpa only [verificationDigest, hleaf', evalWithAnswerFn_bind,
          evalWithAnswerFn_pure, decide_eq_true_eq] using hverified
      · simpa only [← verify_eq_single_layer pk message signature] using htail.bind_left
      · have hrest := htail.bind_right
        rw [hleaf] at hrest
        simpa only [← verify_eq_single_layer pk message signature, verificationDigest] using hrest.bind_left

variable [Params]

/-- The exact generated-key invariant consumed by the structural extraction. -/
theorem keygen_root (f : QueryImpl HashSpec Id) (seed : MasterSeed) (pk : PublicKey)
    (sk : Seeded.SecretKey)
    (hkey : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, sk)) :
    pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest) := by
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    Prod.mk.injEq] at hkey
  rw [← hkey.1]

theorem keygen_secret_fields (f : QueryImpl HashSpec Id) (seed : MasterSeed) (pk : PublicKey)
    (sk : Seeded.SecretKey)
    (hkey : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, sk)) :
    sk.seed = seed ∧ sk.parameter = pk.parameter ∧ sk.root = pk.root := by
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    Prod.mk.injEq] at hkey
  rw [← hkey.1, ← hkey.2]
  exact ⟨rfl, rfl, rfl⟩

/-- The canonical retained-leaf opening, including its authentication path. -/
def TreeOpening (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) : Prop :=
  Landed parameter leaf ∧ value = Completeness.node f parameter topLayer rootTree seed 0 leaf.val ∧
    ∀ level, level < totalHeight →
      path level = canonicalTreePath f parameter topLayer rootTree seed leaf level

/-- All structural exceptions at the single pruned Merkle layer. -/
def TreeException (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) : Prop :=
  (∃ reference : LeafIndex, Landed parameter reference ∧ ∃ level, level < totalHeight ∧
    MerkleMatch f parameter (fun height index => .node topLayer rootTree height index)
      leaf.val reference.val path (canonicalTreePath f parameter topLayer rootTree seed reference)
      value (Completeness.node f parameter topLayer rootTree seed 0 reference.val) level) ∨
  ∃ level, level < totalHeight ∧
    SurrogatePreimage f parameter topLayer rootTree seed leaf path value level

/-- Accepted verification yields an exact retained-tree opening or an explicit structural event.
The root hypothesis is the key-generation invariant, not a cryptographic assumption. -/
theorem verified_pruned_tree (f : QueryImpl HashSpec Id) (pk : PublicKey) (seed : MasterSeed)
    (message : Message) (signature : Signature) (hb : 0 < subtreeHeight)
    (hroot : pk.root = evalWithAnswerFn f
      (Seeded.treeRoot pk.parameter topLayer rootTree seed : OracleComp HashSpec Digest))
    (hverified : evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true) :
    ∃ value,
      evalWithAnswerFn f (otsLeaf pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f pk message signature)) (verificationFors f pk message signature)
        (signature.layers topLayer).counter (signature.layers topLayer).chainValues :
        OracleComp HashSpec (Option Digest)) = some value ∧
      (TreeOpening f pk.parameter seed (digestIndex (verificationDigest f pk message signature))
        (signaturePath signature topLayer) value ∨
       TreeException f pk.parameter seed (digestIndex (verificationDigest f pk message signature))
        (signaturePath signature topLayer) value) := by
  obtain ⟨value, hleaf, hfold, _, _⟩ := verified_tree f pk message signature hverified
  refine ⟨value, hleaf, ?_⟩
  let index := digestIndex (verificationDigest f pk message signature)
  by_cases hland : Landed pk.parameter index
  · rcases inside_subtree_treeFold_witness f pk.parameter topLayer rootTree seed index
      (signaturePath signature topLayer) value hland (hfold.trans hroot) with hopen | hmatch
    · exact Or.inl ⟨hland, hopen⟩
    · exact Or.inr (Or.inl ⟨index, hland, hmatch⟩)
  · let reference := keptLeafEquiv pk.parameter ⟨0, Nat.two_pow_pos _⟩
    rcases outside_subtree_treeFold_witness f pk.parameter topLayer rootTree seed index reference.val
      (signaturePath signature topLayer) value hb reference.property hland (hfold.trans hroot)
      with hmatch | hsurrogate
    · exact Or.inr (Or.inl ⟨reference.val, reference.property, hmatch⟩)
    · exact Or.inr (Or.inr hsurrogate)

end LeanSphincs.Security
