import LeanSphincs.SecurityPrefixSeparation

/-! The actual public one-time keys and pruned Merkle root/path factor through one selected
chain frontier. The reconstructed functions never read the selected coordinate of the secret
table. Their oracle is the outside oracle, with all lower-prefix rows removed. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete

attribute [local instance] Classical.propDecidable
attribute [local irreducible] Seeded.treeNode

def derivedSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) : Secrets :=
  fun (lay, tree, leaf, chain) =>
    evalWithAnswerFn f (deriveKey parameter (.ots lay tree leaf chain) seed : OracleComp HashSpec Digest)

noncomputable def publicEndpoints (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) : ChainIndex → Digest := fun chain =>
  if (lay, tree, leaf, chain) = address segment then
    evalWithAnswerFn outside (recoverChain segment.parameter lay tree leaf chain segment.digit frontier)
  else
    evalWithAnswerFn outside (chainWalk segment.parameter lay tree leaf chain 0 (chainLength - 1)
      (secrets (lay, tree, leaf, chain)) : OracleComp HashSpec Digest)

theorem publicEndpoints_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    publicEndpoints segment outside (replaceSecret segment secrets replacement) frontier lay tree leaf =
      publicEndpoints segment outside secrets frontier lay tree leaf := by
  funext chain
  by_cases haddr : (lay, tree, leaf, chain) = address segment
  · simp only [publicEndpoints, haddr, ↓reduceIte]
  · simp only [publicEndpoints, haddr, ↓reduceIte, replaceSecret, Function.update_of_ne haddr]

/-- The secret-table identification is exact evaluation, not an assumption of secrecy. -/
theorem oneTimePublicKey_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.oneTimePublicKey segment.parameter lay tree leaf seed :
        OracleComp HashSpec (ChainIndex → Digest)) =
      publicEndpoints segment outside (derivedSecrets outside segment.parameter seed)
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (derivedSecrets outside segment.parameter seed (address segment))) lay tree leaf := by
  rw [Seeded.oneTimePublicKey, Completeness.eval_sequenceFin]
  funext chain
  rw [evalWithAnswerFn_bind, eval_derive_answer]
  unfold publicEndpoints
  by_cases haddr : (lay, tree, leaf, chain) = address segment
  · rw [if_pos haddr]
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      (show lay = segment.lay ∧ tree = segment.tree ∧ leaf = segment.leaf ∧ chain = segment.chainIdx by
        simpa only [address, Prod.mk.injEq] using haddr)
    exact endpoint_from_frontier segment tables high outside _
  · rw [if_neg haddr]
    exact eval_other_chain_answer segment tables high outside lay tree leaf chain 0
      (chainLength - 1) _ haddr

noncomputable def publicNode (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex) : Nat → Nat → Digest
  | 0, nodeIdx => evalWithAnswerFn outside (leafHash segment.parameter lay tree (leafOfNat nodeIdx)
      (publicEndpoints segment outside secrets frontier lay tree (leafOfNat nodeIdx)))
  | level + 1, nodeIdx => evalWithAnswerFn outside
      (tweakableHash segment.parameter (.node lay tree (level + 1) nodeIdx)
        (nodePayload (publicNode segment outside secrets frontier lay tree level (2 * nodeIdx))
          (publicNode segment outside secrets frontier lay tree level (2 * nodeIdx + 1))) :
        OracleComp HashSpec Digest)

theorem publicNode_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    publicNode segment outside (replaceSecret segment secrets replacement) frontier lay tree level nodeIdx =
      publicNode segment outside secrets frontier lay tree level nodeIdx := by
  induction level generalizing nodeIdx with
  | zero => simp only [publicNode, publicEndpoints_replaceSecret]
  | succ level ih => simp only [publicNode, ih]

theorem treeNode_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (level nodeIdx : Nat) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.treeNode segment.parameter lay tree seed level nodeIdx : OracleComp HashSpec Digest) =
      publicNode segment outside (derivedSecrets outside segment.parameter seed)
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (derivedSecrets outside segment.parameter seed (address segment))) lay tree level nodeIdx := by
  induction level generalizing nodeIdx with
  | zero =>
      simp only [Seeded.treeNode, evalWithAnswerFn_bind, oneTimePublicKey_from_frontier,
        publicNode, leafHash]
      exact eval_other_hash_answer segment tables high outside _ _ (by change (2 : BitVec 8) ≠ 1; decide)
  | succ level ih =>
      simp only [Seeded.treeNode, evalWithAnswerFn_bind, ih, publicNode]
      exact eval_other_hash_answer segment tables high outside _ _ (by change (3 : BitVec 8) ≠ 1; decide)

variable [Params]

omit [Params] in
theorem surrogate_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (level : Nat) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.surrogate segment.parameter seed level : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside (Seeded.surrogate segment.parameter seed level : OracleComp HashSpec Digest) := by
  unfold Seeded.surrogate
  split
  next => exact eval_derive_answer segment tables high outside _ _ _
  next => rfl

noncomputable def publicSpine (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest) (lay : Layer)
    (tree : TreeIndex) : Nat → Digest
  | 0 => publicNode segment outside secrets frontier lay tree subtreeHeight (subtreePosition segment.parameter)
  | steps + 1 =>
      let below := publicSpine segment outside secrets frontier surrogates lay tree steps
      let sibling := surrogates (subtreeHeight + steps)
      let nodeIdx := subtreePosition segment.parameter / 2 ^ steps
      evalWithAnswerFn outside (tweakableHash segment.parameter
        (.node lay tree (subtreeHeight + steps + 1) (nodeIdx / 2))
        (if nodeIdx.testBit 0 then nodePayload sibling below else nodePayload below sibling) :
        OracleComp HashSpec Digest)

theorem publicSpine_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (surrogates : Nat → Digest)
    (lay : Layer) (tree : TreeIndex) (steps : Nat) :
    publicSpine segment outside (replaceSecret segment secrets replacement) frontier surrogates lay tree steps =
      publicSpine segment outside secrets frontier surrogates lay tree steps := by
  induction steps with
  | zero => exact publicNode_replaceSecret segment outside secrets frontier replacement lay tree _ _
  | succ steps ih => simp only [publicSpine, ih]

theorem spineNode_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (steps : Nat) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.spineNode segment.parameter lay tree seed steps : OracleComp HashSpec Digest) =
      publicSpine segment outside (derivedSecrets outside segment.parameter seed)
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (derivedSecrets outside segment.parameter seed (address segment)))
        (fun level => evalWithAnswerFn outside
          (Seeded.surrogate segment.parameter seed level : OracleComp HashSpec Digest)) lay tree steps := by
  induction steps with
  | zero => exact treeNode_from_frontier segment tables high outside seed lay tree _ _
  | succ steps ih =>
      simp only [Seeded.spineNode, evalWithAnswerFn_bind, ih, surrogate_answer, publicSpine]
      split <;>
        exact eval_other_hash_answer segment tables high outside _ _ (by change (3 : BitVec 8) ≠ 1; decide)

theorem treeRoot_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.treeRoot segment.parameter lay tree seed : OracleComp HashSpec Digest) =
      publicSpine segment outside (derivedSecrets outside segment.parameter seed)
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (derivedSecrets outside segment.parameter seed (address segment)))
        (fun level => evalWithAnswerFn outside
          (Seeded.surrogate segment.parameter seed level : OracleComp HashSpec Digest))
        lay tree (totalHeight - subtreeHeight) :=
  spineNode_from_frontier segment tables high outside seed lay tree _

noncomputable def publicPath (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Fin (layerHeight lay) → Digest :=
  fun level => if level.val < subtreeHeight then
    publicNode segment outside secrets frontier lay tree level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  else surrogates level.val

theorem publicPath_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (surrogates : Nat → Digest)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    publicPath segment outside (replaceSecret segment secrets replacement) frontier surrogates lay tree leaf =
      publicPath segment outside secrets frontier surrogates lay tree leaf := by
  funext level
  simp only [publicPath, publicNode_replaceSecret]

theorem treePath_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.treePath segment.parameter lay tree seed leaf : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) =
      publicPath segment outside (derivedSecrets outside segment.parameter seed)
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (derivedSecrets outside segment.parameter seed (address segment)))
        (fun level => evalWithAnswerFn outside
          (Seeded.surrogate segment.parameter seed level : OracleComp HashSpec Digest)) lay tree leaf := by
  funext level
  rw [Completeness.eval_treePath]
  unfold publicPath
  split
  next => exact treeNode_from_frontier segment tables high outside seed lay tree _ _
  next => exact surrogate_answer segment tables high outside seed _

end LeanSphincs.Security.Prefix
