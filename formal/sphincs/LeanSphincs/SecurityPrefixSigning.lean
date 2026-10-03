import LeanSphincs.SecurityPrefixPublic

/-! Honest signing factors through a selected hidden-chain frontier whenever the first
successful encoding discloses at or above that frontier. Encoding counters and the canonical
FORS message are kept exactly; this is an evaluation equality, with cost handled separately. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete

attribute [local instance] Classical.propDecidable
attribute [local irreducible] encodingAttemptLimit Seeded.treePath Seeded.ftsNode chainWalk

theorem encode_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    evalWithAnswerFn (answer segment tables high outside)
      (encode segment.parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) =
    evalWithAnswerFn outside
      (encode segment.parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
  simp only [encode, evalWithAnswerFn_bind]
  rw [eval_other_hash_answer segment tables high outside _ _ (by change (4 : BitVec 8) ≠ 1; decide)]
  rfl

/-- The actual least successful encoding search; its counter remains a 32-bit value. -/
noncomputable def firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) :
    Nat → Nat → Option (Counter × Encoding)
  | 0, _ => none
  | attempts + 1, counter =>
      match evalWithAnswerFn f (encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) :
          OracleComp HashSpec (Option Encoding)) with
      | some word => some (BitVec.ofNat counterBits counter, word)
      | none => firstEncoding f parameter lay tree leaf message attempts (counter + 1)

theorem firstEncoding_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (attempts start : Nat) :
    firstEncoding (answer segment tables high outside) segment.parameter lay tree leaf message attempts start =
      firstEncoding outside segment.parameter lay tree leaf message attempts start := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih => simp only [firstEncoding, encode_answer, ih]

theorem otsSignFrom_eq_firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : Digest)
    (attempts start : Nat) :
    evalWithAnswerFn f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
    (firstEncoding f parameter lay tree leaf message attempts start).map (fun pair =>
      (pair.1, fun chain => evalWithAnswerFn f (chainWalk parameter lay tree leaf chain 0
        (pair.2 chain).val (derivedSecrets f parameter seed (lay, tree, leaf, chain)) :
        OracleComp HashSpec Digest))) := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leaf message (BitVec.ofNat counterBits start) :
            OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode]
          exact ih (start + 1)
      | some word =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode,
            Completeness.eval_sequenceFin, evalWithAnswerFn_pure, Option.map_some, derivedSecrets]

/-- Only the selected chain is subject to this disclosure restriction. -/
def DisclosesAbove (segment : Segment) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (word : Encoding) : Prop :=
  ∀ chain, (lay, tree, leaf, chain) = address segment → segment.digit.val ≤ (word chain).val

noncomputable def publicValues (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (word : Encoding) : ChainIndex → Digest := fun chain =>
  if (lay, tree, leaf, chain) = address segment then
    evalWithAnswerFn outside (chainWalk segment.parameter lay tree leaf chain segment.digit.val
      ((word chain).val - segment.digit.val) frontier : OracleComp HashSpec Digest)
  else
    evalWithAnswerFn outside (chainWalk segment.parameter lay tree leaf chain 0 (word chain).val
      (secrets (lay, tree, leaf, chain)) : OracleComp HashSpec Digest)

theorem publicValues_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (word : Encoding) :
    publicValues segment outside (replaceSecret segment secrets replacement) frontier lay tree leaf word =
      publicValues segment outside secrets frontier lay tree leaf word := by
  funext chain
  by_cases haddr : (lay, tree, leaf, chain) = address segment
  · simp only [publicValues, haddr, ↓reduceIte]
  · simp only [publicValues, haddr, ↓reduceIte, replaceSecret, Function.update_of_ne haddr]

theorem signing_values_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (word : Encoding) (habove : DisclosesAbove segment lay tree leaf word) :
    (fun chain => evalWithAnswerFn (answer segment tables high outside)
      (chainWalk segment.parameter lay tree leaf chain 0 (word chain).val
        (derivedSecrets (answer segment tables high outside) segment.parameter seed
          (lay, tree, leaf, chain)) : OracleComp HashSpec Digest)) =
    publicValues segment outside (derivedSecrets outside segment.parameter seed)
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (derivedSecrets outside segment.parameter seed (address segment))) lay tree leaf word := by
  funext chain
  simp only [derivedSecrets, eval_derive_answer]
  unfold publicValues
  by_cases haddr : (lay, tree, leaf, chain) = address segment
  · rw [if_pos haddr]
    have hposition := habove chain haddr
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      (show lay = segment.lay ∧ tree = segment.tree ∧ leaf = segment.leaf ∧ chain = segment.chainIdx by
        simpa only [address, Prod.mk.injEq] using haddr)
    exact disclosed_value_from_frontier segment tables high outside _ _ hposition
  · rw [if_neg haddr]
    exact eval_other_chain_answer segment tables high outside lay tree leaf chain 0 _ _ haddr

theorem otsSignFrom_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (attempts start : Nat)
    (hsafe : ∀ counter word, firstEncoding outside segment.parameter lay tree leaf message attempts start =
      some (counter, word) → DisclosesAbove segment lay tree leaf word) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.otsSignFrom segment.parameter lay tree leaf seed message attempts start :
        OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
    (firstEncoding outside segment.parameter lay tree leaf message attempts start).map (fun pair =>
      (pair.1, publicValues segment outside (derivedSecrets outside segment.parameter seed)
        (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
          (derivedSecrets outside segment.parameter seed (address segment))) lay tree leaf pair.2)) := by
  rw [otsSignFrom_eq_firstEncoding, firstEncoding_answer]
  cases hsearch : firstEncoding outside segment.parameter lay tree leaf message attempts start with
  | none => rfl
  | some pair =>
      simp only [Option.map_some]
      rw [signing_values_from_frontier segment tables high outside seed lay tree leaf pair.2
        (hsafe pair.1 pair.2 hsearch)]

end LeanSphincs.Security.Prefix
