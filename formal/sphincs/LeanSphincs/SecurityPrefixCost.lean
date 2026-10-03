import LeanSphincs.SecurityPrefixFullSign

/-! Exact hash-call cost of the frontier-factored signer. Internal hidden-prefix edges may be
omitted from the simulated transcript, but their original cost remains charged. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.treeNode
  Seeded.ftsNode Seeded.ftsKey Seeded.ftsOpen Seeded.treePath Seeded.signLayer chainWalk
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

theorem hashCalls_ftsNode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (tree : FtsTree) (seed : MasterSeed) (level nodeIdx : Nat) :
    hashCalls f (Seeded.ftsNode parameter index tree seed level nodeIdx : OracleComp HashSpec Digest) =
      3 * 2 ^ level - 1 := by
  induction level generalizing nodeIdx with
  | zero => simp [Seeded.ftsNode, hashCalls_bind, ftsLeafHash]
  | succ level ih =>
      simp only [Seeded.ftsNode, hashCalls_bind, ih, hashCalls_tweakableHash]
      have hpos : 0 < 2 ^ level := Nat.two_pow_pos level
      rw [pow_succ]
      omega

theorem hashCalls_ftsKey (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (seed : MasterSeed) :
    hashCalls f (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) =
    hashCalls g (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) := by
  simp only [Seeded.ftsKey, hashCalls_bind, hashCalls_sequenceFin, hashCalls_ftsNode,
    hashCalls_tweakableHash]

theorem hashCalls_ftsOpen (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (leaves : IndexGroup → FtsLeaf) (seed : MasterSeed) :
    hashCalls f (Seeded.ftsOpen parameter index leaves seed :
      OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) =
    hashCalls g (Seeded.ftsOpen parameter index leaves seed :
      OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) := by
  simp only [Seeded.ftsOpen, hashCalls_sequenceFin, hashCalls_ftsNode]

theorem hashCalls_encode (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    hashCalls f (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) = 1 := by
  simp only [encode, hashCalls_bind, hashCalls_tweakableHash, hashCalls_pure, Nat.add_zero]

theorem hashCalls_otsSignFrom_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (attempts counter : Nat) :
    hashCalls (answer segment tables high outside)
      (Seeded.otsSignFrom segment.parameter lay tree leaf seed message attempts counter :
        OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
    hashCalls outside
      (Seeded.otsSignFrom segment.parameter lay tree leaf seed message attempts counter :
        OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) := by
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
      simp only [Seeded.otsSignFrom, hashCalls_bind, hashCalls_encode, encode_answer]
      cases evalWithAnswerFn outside (encode segment.parameter lay tree leaf message
        (BitVec.ofNat counterBits counter) : OracleComp HashSpec (Option Encoding)) with
      | none => rw [ih]
      | some word =>
          simp only [hashCalls_bind, hashCalls_sequenceFin, hashCalls_deriveKey,
            hashCalls_pure, Nat.add_zero]
          apply congrArg (fun value => 1 + value)
          apply Finset.sum_congr rfl
          intro chain _
          have hsteps : 0 + (word chain).val ≤ chainLength - 1 := by
            have := (word chain).isLt
            omega
          rw [hashCalls_chainWalk _ _ _ _ _ _ _ _ _ hsteps,
            hashCalls_chainWalk _ _ _ _ _ _ _ _ _ hsteps]

variable [Params]

omit [Params] in
theorem hashCalls_surrogate (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (seed : MasterSeed) (level : Nat) :
    hashCalls f (Seeded.surrogate parameter seed level : OracleComp HashSpec Digest) =
    hashCalls g (Seeded.surrogate parameter seed level : OracleComp HashSpec Digest) := by
  unfold Seeded.surrogate
  split <;> simp only [hashCalls_deriveKey, hashCalls_pure]

theorem hashCalls_treePath (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex) :
    hashCalls f (Seeded.treePath parameter lay tree seed leaf : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) =
    hashCalls g (Seeded.treePath parameter lay tree seed leaf : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) := by
  simp only [Seeded.treePath, hashCalls_sequenceFin]
  apply Finset.sum_congr rfl
  intro level _
  split
  · simp only [hashCalls_treeNode]
  · exact hashCalls_surrogate f g parameter seed level.val

theorem hashCalls_signLayer_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hparameter : sk.parameter = segment.parameter) :
    hashCalls (answer segment tables high outside)
      (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) =
    hashCalls outside
      (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) := by
  simp only [Seeded.signLayer, Seeded.layerMessage, hashCalls_bind, hparameter, ftsKey_answer,
    Seeded.otsSign, hashCalls_otsSignFrom_answer, otsSignFrom_eq_firstEncoding, firstEncoding_answer]
  rw [hashCalls_ftsKey (answer segment tables high outside) outside]
  cases firstEncoding outside segment.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index sk.seed : OracleComp HashSpec Digest))
    encodingAttemptLimit 0 with
  | none => simp only [Option.map_none, hashCalls_pure]
  | some pair =>
      simp only [Option.map_some, hashCalls_bind, hashCalls_pure, Nat.add_zero]
      rw [hashCalls_treePath (answer segment tables high outside) outside]

omit [Params] in
theorem hashCalls_sequenceLayers {α : Layer → Type} (f : QueryImpl HashSpec Id)
    (computation : (lay : Layer) → OracleComp HashSpec (Option (α lay))) :
    hashCalls f (sequenceLayers computation) = hashCalls f (computation topLayer) := by
  rw [sequenceLayers, hashCalls_bind]
  cases evalWithAnswerFn f (computation topLayer) <;> simp only [hashCalls_pure, Nat.add_zero]

omit [Params] in
theorem hashCalls_messageDigestCall (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) (call : Fin 2) :
    hashCalls f (messageDigestCall parameter root message randomness call : OracleComp HashSpec HashOutput) = 1 := rfl

omit [Params] in
theorem hashCalls_messageDigest (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (root : Digest) (message : Message) (randomness : Randomness) :
    hashCalls f (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) = 2 := by
  simp only [messageDigest, hashCalls_bind, hashCalls_messageDigestCall, hashCalls_pure]

theorem hashCalls_signAttempt (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey)
    (message : Message) (randomness : Randomness) :
    hashCalls f (Seeded.signAttempt sk message randomness : OracleComp HashSpec (Option Index)) = 1 := by
  rw [Seeded.signAttempt, hashCalls_bind, hashCalls_messageDigestCall]
  split <;> rfl

theorem hashCalls_finishSign_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (hparameter : sk.parameter = segment.parameter) :
    hashCalls (answer segment tables high outside) (Randomized.finishSign sk message randomness) =
    hashCalls outside (Randomized.finishSign sk message randomness) := by
  simp only [Randomized.finishSign, hashCalls_bind, hashCalls_messageDigest, hparameter,
    messageDigest_answer, hashCalls_sequenceFin, hashCalls_deriveKey, hashCalls_sequenceLayers]
  simp only [hashCalls_ftsOpen (answer segment tables high outside) outside,
    hashCalls_signLayer_answer segment tables high outside sk _ _ hparameter]
  cases evalWithAnswerFn (answer segment tables high outside)
    (sequenceLayers fun lay => Seeded.signLayer sk
      (digestIndex (evalWithAnswerFn outside
        (messageDigest segment.parameter sk.root message randomness : OracleComp HashSpec MessageDigest))) lay)
  <;> cases evalWithAnswerFn outside
    (sequenceLayers fun lay => Seeded.signLayer sk
      (digestIndex (evalWithAnswerFn outside
        (messageDigest segment.parameter sk.root message randomness : OracleComp HashSpec MessageDigest))) lay)
  <;> simp only [hashCalls_pure]

end LeanSphincs.Security.Prefix
