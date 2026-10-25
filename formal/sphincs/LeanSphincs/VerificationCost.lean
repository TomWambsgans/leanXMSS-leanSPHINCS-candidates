import LeanSphincs.Layout
import LeanSphincs.Code
import LeanSphincs.Correctness

/-!
Keccak-f permutation counts for the actual verifier's logged hash-input bytes. A hash of `n` bytes
costs `n / 136 + 1` (rounded down), the Keccak-256 accounting used by `crates/sphincs/src/hash.rs` and
`scripts/scheme.py`. The oracle's answers remain arbitrary; only the byte lengths are counted.
-/

open OracleComp OracleSpec Finset

namespace LeanSphincs.Cost

open Concrete

/-- Keccak-256 permutations: the rate is 136 bytes and the padding takes at least one byte. -/
def blocks (bytes : Nat) : Nat := bytes / 136 + 1

/-- Actual hash inputs on the execution selected by an arbitrary answer function. -/
def hashTrace {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) :
    List HashInput := ((simulateQ f.withLogging oa).run).2.map Sigma.fst

/-- Permutation count of the actual execution, with input lengths including parameter and address. -/
def permutations {α : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec α) : Nat :=
  ((hashTrace f oa).map (fun input => blocks input.length)).sum

@[simp] theorem hashTrace_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    hashTrace f (pure x) = [] := rfl

@[simp] theorem hashTrace_query_bind {α : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec α) :
    hashTrace f (liftM (HashSpec.query input) >>= next) =
      input :: hashTrace f (next (f input)) := rfl

theorem hashTrace_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    hashTrace f (oa >>= next) = hashTrace f oa ++
      hashTrace f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, hashTrace_query_bind, hashTrace_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]

@[simp] theorem permutations_pure {α : Type} (f : QueryImpl HashSpec Id) (x : α) :
    permutations f (pure x) = 0 := rfl

theorem permutations_bind {α β : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    permutations f (oa >>= next) = permutations f oa +
      permutations f (next (evalWithAnswerFn f oa)) := by
  simp [permutations, hashTrace_bind]

@[simp] theorem permutations_oracleHash (f : QueryImpl HashSpec Id) (input : HashInput) :
    permutations f (oracleHash input : OracleComp HashSpec HashOutput) = blocks input.length := rfl

theorem tweakableHashInput_length (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 32 + payload.length := by
  simp [tweakableHashInput, tweakBytes, fieldBytes, bytesLE_length]
  omega

@[simp] theorem permutations_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    permutations f (Concrete.tweakableHash parameter domain payload) = blocks (32 + payload.length) := by
  rw [Concrete.tweakableHash, permutations_bind, permutations_oracleHash,
    permutations_pure, Nat.add_zero, tweakableHashInput_length]

theorem permutations_sequenceFin {α : Type} {n : Nat} (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec α) :
    permutations f (sequenceFin computation) = ∑ i : Fin n, permutations f (computation i) := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, permutations_bind]
      simp only [permutations_bind, permutations_pure, Nat.add_zero, ih, Fin.sum_univ_succ]

theorem permutations_chainWalk (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    permutations f (chainWalk parameter lay tree leaf chain start steps value) = steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [chainWalk, permutations_bind, dif_pos (by omega), permutations_tweakableHash,
        bytesLE_length, ih (by omega)]
      rfl

@[simp] theorem permutations_recoverChain (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) (digit : Digit) (value : Digest) :
    permutations f (recoverChain parameter lay tree leaf chain digit value) =
      chainLength - 1 - digit.val := by
  apply permutations_chainWalk
  have := digit.isLt
  omega

@[simp] theorem permutations_leafHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    permutations f (leafHash parameter lay tree leaf endpoints) = 8 := by
  rw [leafHash, permutations_tweakableHash, leafPayload, digest_vector_length]
  rfl

/-- The FORS tops the encoding absorbs: `2 k = 48` values, 768 bytes. -/
theorem ftsTopsPayload_length (tops : FtsTree → Digest × Digest) :
    (ftsTopsPayload tops).length = 768 := by
  rw [ftsTopsPayload, List.length_flatMap]
  simp [nodePayload, bytesLE_length, ftsTrees]

@[simp] theorem permutations_encode (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : FtsTops) (counter : Counter) :
    permutations f (encode parameter lay tree leaf message counter) = 6 := by
  simp only [encode, permutations_bind, permutations_tweakableHash, List.length_append,
    ftsTopsPayload_length, bytesLE_length, permutations_pure]
  rfl

theorem permutations_treeFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest)
    (levels : Nat) (value : Digest) :
    permutations f (treeFold parameter lay tree leaf path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [treeFold, permutations_bind, ih]
      dsimp only
      split <;> simp [permutations_tweakableHash, nodePayload, bytesLE_length, blocks]

@[simp] theorem permutations_ftsLeafHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (secret : Digest) : permutations f (ftsLeafHash parameter index tree leaf secret) = 1 := by
  rw [ftsLeafHash, permutations_tweakableHash, bytesLE_length]
  rfl

theorem permutations_ftsFold (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest)
    (levels : Nat) (value : Digest) :
    permutations f (ftsFold parameter index tree leaf path levels value) = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [ftsFold, permutations_bind, ih]
      dsimp only
      split <;> simp [permutations_tweakableHash, nodePayload, bytesLE_length, blocks]

@[simp] theorem permutations_ftsRecover (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) :
    permutations f (ftsRecover parameter index leaves secrets paths) = 240 := by
  rw [ftsRecover, permutations_sequenceFin]
  simp only [permutations_bind, permutations_ftsLeafHash, permutations_ftsFold,
    permutations_pure, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rfl

@[simp] theorem permutations_messageDigestCall (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) :
    permutations f (messageDigestCall parameter root message randomness call) = 1 := by
  simp only [messageDigestCall, permutations_oracleHash, tweakableHashInput_length,
    messageDigestPayload, List.length_append, bytesLE_length]
  rfl

@[simp] theorem permutations_messageDigest (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    permutations f (messageDigest parameter root message randomness) = 2 := by
  simp only [messageDigest, permutations_bind, permutations_messageDigestCall,
    permutations_pure]

theorem encode_valid (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : FtsTops)
    (counter : Counter) (word : Encoding)
    (hword : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) = some word) : TargetSum.Valid word := by
  simp only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hword
  unfold TargetSum.decodeDigest at hword
  split at hword
  next hvalid =>
    cases Option.some.inj hword
    exact hvalid
  next => simp at hword

/-- Recovery spends 86 permutations after an admissible encoding (6 for the encoding of the tops and
the counter, 72 chain steps, 8 for the leaf), or the encoding's 6 on rejection. -/
theorem permutations_otsLeaf (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : FtsTops)
    (counter : Counter) (values : ChainIndex → Digest) :
    permutations f (otsLeaf parameter lay tree leaf message counter values) =
      if (evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values
        : OracleComp HashSpec (Option Digest))).isSome then 86 else 6 := by
  cases henc : evalWithAnswerFn f (encode parameter lay tree leaf message counter
      : OracleComp HashSpec (Option Encoding)) with
  | none =>
      simp only [otsLeaf, permutations_bind, permutations_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        permutations_pure, Nat.add_zero]
  | some word =>
      have hvalid := encode_valid f parameter lay tree leaf message counter word henc
      simp only [otsLeaf, permutations_bind, permutations_encode, evalWithAnswerFn_bind,
        henc, evalWithAnswerFn_pure, Option.isSome_some, ↓reduceIte,
        permutations_sequenceFin, permutations_recoverChain, permutations_leafHash,
        permutations_pure, Nat.add_zero, Completeness.verification_chain_steps word hvalid]

attribute [local irreducible] otsLeaf encode sequenceFin chainWalk recoverChain leafHash
  ftsRecover treeFold messageDigest

/-- The one tree layer costs 112 permutations, or 6 if its encoding is rejected. -/
theorem permutations_verifyLayer (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) (message : FtsTops) :
    permutations f (verifyLayer parameter index signature message) =
      if (evalWithAnswerFn f (verifyLayer parameter index signature message
        : OracleComp HashSpec (Option Digest))).isSome then 112 else 6 := by
  rw [verifyLayer]
  simp only [permutations_bind, evalWithAnswerFn_bind]
  rw [permutations_otsLeaf]
  cases hleaf : evalWithAnswerFn f (otsLeaf parameter topLayer (treeIndexAt index topLayer)
      (leafIndexAt index topLayer) message (signature.layers topLayer).counter
      (signature.layers topLayer).chainValues : OracleComp HashSpec (Option Digest)) <;>
    simp only [topLayer] at hleaf
  all_goals simp only [hleaf, permutations_bind, permutations_treeFold,
    evalWithAnswerFn_bind, evalWithAnswerFn_pure, permutations_pure, Nat.add_zero,
    Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rfl

attribute [local semireducible] Concrete.verify

/-- Every accepted signature causes exactly 354 Keccak-f permutations in the verifier execution. -/
theorem verification_permutations (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature)
    (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    permutations f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = 354 := by
  rw [Concrete.verify, permutations_bind, permutations_messageDigest,
    permutations_bind, permutations_ftsRecover, permutations_bind, permutations_verifyLayer]
  simp only [Concrete.verify, evalWithAnswerFn_bind] at haccept
  split at haccept
  next root hroot =>
    rw [hroot]
    rfl
  next => simp at haccept

/-- Malformed signatures cannot make verification exceed its accepted-signature cost. -/
theorem verification_permutations_le (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (message : Message) (signature : Signature) :
    permutations f (Concrete.verify pk message signature : OracleComp HashSpec Bool) ≤ 354 := by
  rw [Concrete.verify, permutations_bind, permutations_messageDigest,
    permutations_bind, permutations_ftsRecover, permutations_bind, permutations_verifyLayer]
  split <;> split <;> simp [permutations_pure]

end LeanSphincs.Cost
