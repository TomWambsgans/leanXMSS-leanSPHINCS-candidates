import LeanSphincs.SecurityPrefixFrontier

/-! Exact separation of the selected candidate prefix from other chains and all other hash
domains. These facts allow public tree computations to be rebuilt after the prefix is erased. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete

theorem chainInput_address {parameter : PublicParameter} {lay lay' : Layer}
    {tree tree' : TreeIndex} {leaf leaf' : LeafIndex} {chain chain' : ChainIndex}
    {position position' : ChainStep} {value value' : Digest}
    (h : tweakableHashInput parameter (.chain lay tree leaf chain position) (bytesLE 16 value) =
      tweakableHashInput parameter (.chain lay' tree' leaf' chain' position') (bytesLE 16 value')) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ chain = chain' ∧ position = position' := by
  have hfields := (tweakableInput_injective h).1
  change tweakFields 1 lay.val tree.val (chainLength * chain.val + position.val) leaf.val =
    tweakFields 1 lay'.val tree'.val (chainLength * chain'.val + position'.val) leaf'.val at hfields
  obtain ⟨_, hlay, htree, hposition, hleaf⟩ :=
    (show _ ∧ _ ∧ _ ∧ _ ∧ _ from by simpa only [tweakFields, TweakFields.mk.injEq] using hfields)
  have hl : lay = lay' := Fin.ext (ofNat_inj_of_lt
    (lay.isLt.trans_le (by decide)) (lay'.isLt.trans_le (by decide)) hlay)
  have ht : tree = tree' := Fin.ext (ofNat_inj_of_lt
    (tree.isLt.trans_le (by decide)) (tree'.isLt.trans_le (by decide)) htree)
  have he : leaf = leaf' := Fin.ext (ofNat_inj_of_lt
    (leaf.isLt.trans_le (by decide)) (leaf'.isLt.trans_le (by decide)) hleaf)
  subst lay'; subst tree'; subst leaf'
  obtain ⟨hc, hs⟩ := Chain.chain_input_address_injective parameter lay tree leaf value value' h
  exact ⟨rfl, rfl, rfl, hc, hs⟩

theorem parse_other_chain (segment : Segment) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (position : ChainStep) (value : Digest)
    (hother : (lay, tree, leaf, chain) ≠ address segment) :
    parse segment (tweakableHashInput segment.parameter (.chain lay tree leaf chain position)
      (bytesLE 16 value)) = none := by
  cases hparse : parse segment (tweakableHashInput segment.parameter
      (.chain lay tree leaf chain position) (bytesLE 16 value)) with
  | none => rfl
  | some query =>
      have hinput := (parse_some_iff segment _ query).mp hparse
      obtain ⟨rfl, rfl, rfl, rfl, _⟩ := chainInput_address hinput
      exact False.elim (hother rfl)

theorem parse_other_domain (segment : Segment) (domain : HashDomain) (payload : HashInput)
    (htag : (hashDomainFields domain).tag ≠ BitVec.ofNat 8 1) :
    parse segment (tweakableHashInput segment.parameter domain payload) = none := by
  cases hparse : parse segment (tweakableHashInput segment.parameter domain payload) with
  | none => rfl
  | some query =>
      have hinput := (parse_some_iff segment _ query).mp hparse
      exact False.elim (htag (congrArg TweakFields.tag (tweakableInput_injective hinput).1))

theorem parse_derive (segment : Segment) (parameter : PublicParameter)
    (domain : KeygenDomain) (seed : MasterSeed) :
    parse segment (keygenHashInput parameter domain seed) = none := by
  cases hparse : parse segment (keygenHashInput parameter domain seed) with
  | none => rfl
  | some query =>
      exact False.elim (keygenInput_ne_hashInput parameter segment.parameter domain _ seed _
        ((parse_some_iff segment _ query).mp hparse))

theorem eval_derive_answer (segment : Segment) (tables : Fin segment.digit.val → Digest → Digest)
    (high : Query segment → High) (outside : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    evalWithAnswerFn (answer segment tables high outside)
      (deriveKey parameter domain seed : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside (deriveKey parameter domain seed : OracleComp HashSpec Digest) := by
  rw [Completeness.eval_deriveKey, Completeness.eval_deriveKey,
    answer_outside segment tables high outside _ (parse_derive segment parameter domain seed)]

theorem eval_other_hash_answer (segment : Segment) (tables : Fin segment.digit.val → Digest → Digest)
    (high : Query segment → High) (outside : QueryImpl HashSpec Id)
    (domain : HashDomain) (payload : HashInput)
    (htag : (hashDomainFields domain).tag ≠ BitVec.ofNat 8 1) :
    evalWithAnswerFn (answer segment tables high outside)
      (tweakableHash segment.parameter domain payload : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside (tweakableHash segment.parameter domain payload : OracleComp HashSpec Digest) := by
  rw [Completeness.eval_tweakableHash, Completeness.eval_tweakableHash,
    answer_outside segment tables high outside _ (parse_other_domain segment domain payload htag)]

theorem eval_other_chain_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (start steps : Nat) (value : Digest)
    (hother : (lay, tree, leaf, chain) ≠ address segment) :
    evalWithAnswerFn (answer segment tables high outside)
      (chainWalk segment.parameter lay tree leaf chain start steps value : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside
      (chainWalk segment.parameter lay tree leaf chain start steps value : OracleComp HashSpec Digest) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [chainWalk, evalWithAnswerFn_bind, ih]
      split
      next hstep =>
        rw [Completeness.eval_tweakableHash, Completeness.eval_tweakableHash,
          answer_outside segment tables high outside _ (parse_other_chain segment lay tree leaf chain
            ⟨start + steps, hstep⟩ _ hother)]
      next => rfl

end LeanSphincs.Security.Prefix
