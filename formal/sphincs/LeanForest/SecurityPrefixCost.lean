import LeanForest.SecurityPrefixFullSign

/-! Exact hash-call counts (`hashCalls`) of the honest seeded computations on a fixed answer
function: wrappers, chains, one-time keys, tree and forest nodes, encodings, message digests and
signing attempts. -/

open OracleComp OracleSpec

namespace LeanForest.Security.Prefix
open Concrete

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.treeNode
  Seeded.subNode Seeded.topNode Seeded.forestKey Seeded.forestOpen Seeded.treePath Seeded.signLayer chainWalk
  forestWalk
  deriveKey
set_option backward.isDefEq.respectTransparency false

def hashCalls {α : Type} (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) : Nat :=
  (queriedInputs f computation).length

@[simp] theorem hashCalls_pure {α : Type} (f : QueryImpl HashSpec Id) (value : α) :
    hashCalls f (pure value) = 0 := rfl

theorem hashCalls_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (computation : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    hashCalls f (computation >>= next) = hashCalls f computation +
      hashCalls f (next (evalWithAnswerFn f computation)) := by
  simp only [hashCalls, queriedInputs_bind, List.length_append]

@[simp] theorem hashCalls_oracleHash (f : QueryImpl HashSpec Id) (input : HashInput) :
    hashCalls f (oracleHash input : OracleComp HashSpec HashOutput) = 1 := rfl

@[simp] theorem hashCalls_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    hashCalls f (tweakableHash parameter domain payload : OracleComp HashSpec Digest) = 1 := by
  simp only [hashCalls, queriedInputs_tweakableHash, List.length_singleton]

@[simp] theorem hashCalls_deriveKey (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    hashCalls f (deriveKey parameter domain seed : OracleComp HashSpec Digest) = 1 := by
  simp only [deriveKey, hashCalls_bind, hashCalls_oracleHash, hashCalls_pure, Nat.add_zero]

theorem hashCalls_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    hashCalls f (sequenceFin computation) = ∑ i, hashCalls f (computation i) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      simp only [sequenceFin, hashCalls_bind, hashCalls_pure, Nat.add_zero, ih,
        Fin.sum_univ_succ]

theorem hashCalls_chainWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    hashCalls f (chainWalk parameter lay tree leaf chain start steps value : OracleComp HashSpec Digest) = steps := by
  induction steps generalizing start value with
  | zero => simp only [chainWalk, hashCalls_pure]
  | succ steps ih =>
      rw [chainWalk, hashCalls_bind, dif_pos (by omega), hashCalls_tweakableHash, ih _ _ (by omega)]

theorem hashCalls_oneTimePublicKey (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) :
    hashCalls f (Seeded.oneTimePublicKey parameter lay tree leaf seed :
      OracleComp HashSpec (ChainIndex → Digest)) = 256 := by
  simp only [Seeded.oneTimePublicKey, hashCalls_sequenceFin, hashCalls_bind, hashCalls_deriveKey]
  have walk (chain : ChainIndex) (value : Digest) :
      hashCalls f (chainWalk parameter lay tree leaf chain 0 (chainLength - 1) value :
        OracleComp HashSpec Digest) = chainLength - 1 :=
    hashCalls_chainWalk f parameter lay tree leaf chain 0 (chainLength - 1) value (by omega)
  simp only [walk]
  decide

theorem hashCalls_treeNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (level nodeIdx : Nat) :
    hashCalls f (Seeded.treeNode parameter lay tree seed level nodeIdx : OracleComp HashSpec Digest) =
      258 * 2 ^ level - 1 := by
  induction level generalizing nodeIdx with
  | zero => simp [Seeded.treeNode, hashCalls_bind, hashCalls_oneTimePublicKey, leafHash]
  | succ level ih =>
      simp only [Seeded.treeNode, hashCalls_bind, ih, hashCalls_tweakableHash]
      have hpos : 0 < 2 ^ level := Nat.two_pow_pos level
      rw [pow_succ]
      omega

theorem hashCalls_forestWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainTop) :
    hashCalls f (forestWalk parameter index c s j a i start steps value : OracleComp HashSpec Digest) = steps := by
  induction steps generalizing start value with
  | zero => simp only [forestWalk, hashCalls_pure]
  | succ steps ih =>
      rw [forestWalk, hashCalls_bind, dif_pos (by omega), hashCalls_tweakableHash, ih _ _ (by omega)]

theorem hashCalls_chainValue (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (seed : MasterSeed) (pos : Nat) (hpos : pos ≤ chainTop) :
    hashCalls f (Seeded.chainValue parameter index c s j a i seed pos : OracleComp HashSpec Digest) = 1 + pos := by
  rw [Seeded.chainValue, hashCalls_bind, hashCalls_deriveKey, hashCalls_forestWalk f _ _ _ _ _ _ _ _ _ _ (by omega)]

theorem hashCalls_childLeaf (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (seed : MasterSeed) :
    hashCalls f (Seeded.childLeaf parameter index c s j a seed : OracleComp HashSpec Digest) = 31 := by
  rw [Seeded.childLeaf, hashCalls_bind, hashCalls_sequenceFin, childLeafHash, hashCalls_tweakableHash]
  simp only [hashCalls_chainValue f parameter index c s j a _ seed chainTop le_rfl]
  decide

theorem hashCalls_subNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (seed : MasterSeed) (level node : Nat)
    (hlevel : level ≤ subHeight) :
    hashCalls f (Seeded.subNode parameter index c s j seed level node : OracleComp HashSpec Digest) =
      32 * 2 ^ level - 1 := by
  induction level generalizing node with
  | zero => rw [Seeded.subNode, hashCalls_childLeaf]; rfl
  | succ level ih =>
      rw [Seeded.subNode, hashCalls_bind, hashCalls_bind, dif_pos (by omega), hashCalls_tweakableHash,
        ih _ (by omega), ih _ (by omega)]
      have hp : 0 < 2 ^ level := Nat.two_pow_pos level
      rw [pow_succ]
      omega

theorem hashCalls_superNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (c : Coord) (s : SuperIdx) (seed : MasterSeed) :
    hashCalls f (Seeded.superNode parameter index c s seed : OracleComp HashSpec Digest) = 511 := by
  rw [Seeded.superNode, hashCalls_bind, hashCalls_sequenceFin, superHash, hashCalls_tweakableHash]
  simp only [hashCalls_subNode f parameter index c s _ seed subHeight 0 le_rfl]
  decide

theorem hashCalls_topNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (c : Coord) (seed : MasterSeed) (level node : Nat) (hlevel : level ≤ topHeight) :
    hashCalls f (Seeded.topNode parameter index c seed level node : OracleComp HashSpec Digest) =
      512 * 2 ^ level - 1 := by
  induction level generalizing node with
  | zero => rw [Seeded.topNode, hashCalls_superNode]; rfl
  | succ level ih =>
      rw [Seeded.topNode, hashCalls_bind, hashCalls_bind, dif_pos (by omega), hashCalls_tweakableHash,
        ih _ (by omega), ih _ (by omega)]
      have hp : 0 < 2 ^ level := Nat.two_pow_pos level
      rw [pow_succ]
      omega

/-- Building the forest key costs `8 · (512 · 16 - 1) + 1 = 65529` hash calls. -/
theorem hashCalls_forestKey (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) :
    hashCalls f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest) = 65529 := by
  rw [Seeded.forestKey, hashCalls_bind, hashCalls_sequenceFin, hashCalls_tweakableHash]
  simp only [hashCalls_topNode f parameter index _ seed topHeight 0 le_rfl]
  decide

theorem hashCalls_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    hashCalls f (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) = 1 := by
  simp only [encode, hashCalls_bind, hashCalls_tweakableHash, hashCalls_pure, Nat.add_zero]

variable [Params]

omit [Params] in
theorem hashCalls_sequenceLayers {α : Layer → Type} (f : QueryImpl HashSpec Id)
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay))) :
    hashCalls f (sequenceLayers computation) = hashCalls f (computation topLayer) := by
  rw [sequenceLayers, hashCalls_bind]
  cases evalWithAnswerFn f (computation topLayer) <;> simp only [hashCalls_pure, Nat.add_zero]

omit [Params] in
theorem hashCalls_messageDigestCall (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) :
    hashCalls f (messageDigestCall parameter root message randomness : OracleComp HashSpec HashOutput) = 1 := rfl

omit [Params] in
theorem hashCalls_messageDigest (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) :
    hashCalls f (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) = 1 := by
  simp only [messageDigest, hashCalls_bind, hashCalls_messageDigestCall, hashCalls_pure]

theorem hashCalls_signAttempt (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) :
    hashCalls f (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) = 1 := by
  rw [Seeded.signAttempt, hashCalls_bind, hashCalls_messageDigestCall]
  split <;> rfl

end LeanForest.Security.Prefix
