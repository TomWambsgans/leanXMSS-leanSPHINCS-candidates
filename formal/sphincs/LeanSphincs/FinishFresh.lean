import LeanSphincs.Fresh
import LeanSphincs.RandomizedSupport

/-!
Signature assembly after its two digest calls preserves the whole message-hashing domain.
This applies to successful and exhausted WOTS searches and to arbitrary initial oracle caches.
-/

open OracleComp OracleSpec

namespace LeanSphincs.Completeness

open Concrete

namespace PreservesFresh

variable {target : HashInput} (hs : StructuralFresh target)
include hs

theorem otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest)
    (hencoding : ∀ c, encodeInput parameter lay tree leaf message c ≠ target)
    (attempts counter : Nat) :
    PreservesFresh target (Seeded.otsSignFrom parameter lay tree leaf seed message attempts counter
      : OracleComp HashSpec _) := by
  induction attempts generalizing counter with
  | zero => exact pure' _ _
  | succ attempts ih =>
      rw [Seeded.otsSignFrom]
      refine bind ?_ (fun result => ?_)
      · rw [Concrete.encode]
        exact bind (tweakableHash _ _ _ _ (hencoding counter)) (fun _ => pure' _ _)
      · cases result with
        | none => exact ih _
        | some encoding =>
          exact bind (sequenceFin _ _ (fun _ =>
            bind (deriveKey _ _ _ _ (hs.derive _ _ _))
              (fun _ => chainWalk hs _ _ _ _ _ _ _ _))) (fun _ => pure' _ _)

variable [Params]

theorem treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) :
    PreservesFresh target (Seeded.treePath parameter lay tree seed leaf
      : OracleComp HashSpec _) := by
  rw [Seeded.treePath]
  apply sequenceFin
  intro level
  split
  · exact treeNode hs _ _ _ _ _ _
  · exact surrogate hs _ _ _

attribute [local irreducible] encodingAttemptLimit

theorem signLayer (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hencoding : ∀ message c,
      encodeInput sk.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message c ≠ target) :
    PreservesFresh target (Seeded.signLayer sk index lay : OracleComp HashSpec _) := by
  rw [Seeded.signLayer]
  refine bind (ftsKey hs _ _ _) (fun message => ?_)
  refine bind (otsSignFrom hs _ _ _ _ _ _ (hencoding message) _ _) (fun result => ?_)
  cases result with
  | none => exact pure' _ _
  | some pair => exact bind (treePath hs _ _ _ _ _) (fun _ => pure' _ _)

end PreservesFresh

variable [Params]

/-- The actual assembly suffix, after both message-digest blocks have been queried. -/
def finishSignBody (sk : Seeded.SecretKey) (randomness : Randomness) (digest : MessageDigest) :
    OracleComp HashSpec (Option Signature) := do
  let index := digestIndex digest
  let leaves := digestLeaves digest
  let secrets ← sequenceFin fun tree =>
    deriveKey sk.parameter (.fts index tree (leaves (ftsIndexOf tree))) sk.seed
  let path ← Seeded.ftsOpen sk.parameter index leaves sk.seed
  let some layers ← sequenceLayers (fun lay => Seeded.signLayer sk index lay) | return none
  return some ⟨randomness, secrets, path, layers⟩

theorem finishSign_eq_digest_body (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) :
    Randomized.finishSign sk message randomness =
      messageDigest sk.parameter sk.root message randomness >>= finishSignBody sk randomness := rfl

attribute [local irreducible] Concrete.sequenceFin Seeded.ftsOpen Seeded.signLayer

/-- The assembly suffix never populates any previously unused message input, including inputs
for another message, randomizer, or key. -/
theorem finishSignBody_preserves_message (sk : Seeded.SecretKey) (randomness : Randomness)
    (digest : MessageDigest) (parameter : PublicParameter) (root : Digest)
    (message : Message) (targetRandomness : Randomness) (block : Fin 2) :
    PreservesFresh (tweakableHashInput parameter (.message block)
      (messageDigestPayload root message targetRandomness))
      (finishSignBody sk randomness digest) := by
  have hs := structuralFresh_message parameter root message targetRandomness block
  rw [finishSignBody]
  refine PreservesFresh.bind (PreservesFresh.sequenceFin _ _ (fun _ =>
    PreservesFresh.deriveKey _ _ _ _ (hs.derive _ _ _))) (fun _ => ?_)
  refine PreservesFresh.bind (PreservesFresh.ftsOpen hs _ _ _ _) (fun _ => ?_)
  rw [Concrete.sequenceLayers]
  simp only [bind_assoc]
  refine PreservesFresh.bind (PreservesFresh.signLayer hs _ _ _ (fun m c =>
    Ne.symm (messageInput_ne_encoding parameter root message targetRandomness block
      sk.parameter _ _ _ m c))) (fun result => ?_)
  cases result <;> simp only [pure_bind] <;> exact PreservesFresh.pure' _ _

omit [Params] in
/-- Cache growth plus preservation of freshness gives exact agreement at an untouched input. -/
theorem PreservesFresh.cache_eq {α : Type} {target : HashInput} {oa : OracleComp HashSpec α}
    (h : PreservesFresh target oa) (cache : QueryCache HashSpec)
    (r : α × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ randomOracle oa).run cache)) : r.2 target = cache target := by
  cases heq : cache target with
  | none => exact h cache r hr heq
  | some answer => exact hash_support_cache_le oa cache r.1 r.2 hr heq

/-- Assembly preserves all existing and absent message-domain entries exactly. -/
theorem finishSignBody_message_cache_eq (sk : Seeded.SecretKey) (randomness : Randomness)
    (digest : MessageDigest) (cache : QueryCache HashSpec)
    (r : Option Signature × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ randomOracle (finishSignBody sk randomness digest)).run cache))
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (targetRandomness : Randomness) (block : Fin 2) :
    r.2 (tweakableHashInput parameter (.message block)
      (messageDigestPayload root message targetRandomness)) =
    cache (tweakableHashInput parameter (.message block)
      (messageDigestPayload root message targetRandomness)) :=
  PreservesFresh.cache_eq
    (finishSignBody_preserves_message sk randomness digest parameter root message targetRandomness block)
    cache r hr

end LeanSphincs.Completeness
