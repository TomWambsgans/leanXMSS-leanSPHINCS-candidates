import LeanSphincs.SecurityPrefixSigning

/-! Factoring the actual single-layer signer through the selected chain frontier. FORS and
encoding queries are outside the hidden chain prefix; the first successful counter and the
pruned authentication path are preserved exactly. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete

attribute [local irreducible] encodingAttemptLimit Seeded.ftsNode Seeded.treePath chainWalk

theorem ftsNode_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (index : Index) (tree : FtsTree) (seed : MasterSeed)
    (level nodeIdx : Nat) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.ftsNode segment.parameter index tree seed level nodeIdx : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside
      (Seeded.ftsNode segment.parameter index tree seed level nodeIdx : OracleComp HashSpec Digest) := by
  induction level generalizing nodeIdx with
  | zero =>
      simp only [Seeded.ftsNode, evalWithAnswerFn_bind, eval_derive_answer, ftsLeafHash]
      exact eval_other_hash_answer segment tables high outside _ _ (by change (9 : BitVec 8) ≠ 1; decide)
  | succ level ih =>
      simp only [Seeded.ftsNode, evalWithAnswerFn_bind, ih]
      exact eval_other_hash_answer segment tables high outside _ _ (by change (10 : BitVec 8) ≠ 1; decide)

theorem ftsKey_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (index : Index) (seed : MasterSeed) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.ftsKey segment.parameter index seed : OracleComp HashSpec Digest) =
    evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index seed : OracleComp HashSpec Digest) := by
  simp only [Seeded.ftsKey, evalWithAnswerFn_bind, Completeness.eval_sequenceFin, ftsNode_answer]
  exact eval_other_hash_answer segment tables high outside _ _ (by change (11 : BitVec 8) ≠ 1; decide)

theorem ftsOpen_answer (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (index : Index) (leaves : IndexGroup → FtsLeaf) (seed : MasterSeed) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.ftsOpen segment.parameter index leaves seed :
        OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) =
    evalWithAnswerFn outside
      (Seeded.ftsOpen segment.parameter index leaves seed :
        OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) := by
  simp only [Seeded.ftsOpen, Completeness.eval_sequenceFin, ftsNode_answer]

variable [Params]

noncomputable def publicLayer (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier : Digest) (surrogates : Nat → Digest)
    (index : Index) (lay : Layer) (message : Digest) : Option (LayerSignature lay) :=
  (firstEncoding outside segment.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      message encodingAttemptLimit 0).map fun pair =>
    ⟨pair.1,
      publicValues segment outside secrets frontier lay (treeIndexAt index lay) (leafIndexAt index lay) pair.2,
      publicPath segment outside secrets frontier surrogates lay (treeIndexAt index lay) (leafIndexAt index lay)⟩

theorem publicLayer_replaceSecret (segment : Segment) (outside : QueryImpl HashSpec Id)
    (secrets : Secrets) (frontier replacement : Digest) (surrogates : Nat → Digest)
    (index : Index) (lay : Layer) (message : Digest) :
    publicLayer segment outside (replaceSecret segment secrets replacement) frontier surrogates index lay message =
      publicLayer segment outside secrets frontier surrogates index lay message := by
  simp only [publicLayer, publicValues_replaceSecret, publicPath_replaceSecret]

/-- The full actual signLayer output is an endpoint-only computation whenever its selected
successful encoding discloses above the frontier. Failed counter searches are preserved too. -/
theorem signLayer_from_frontier (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hparameter : sk.parameter = segment.parameter)
    (hsafe : ∀ counter word,
      firstEncoding outside segment.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index sk.seed : OracleComp HashSpec Digest))
        encodingAttemptLimit 0 = some (counter, word) →
      DisclosesAbove segment lay (treeIndexAt index lay) (leafIndexAt index lay) word) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) =
    publicLayer segment outside (derivedSecrets outside segment.parameter sk.seed)
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (derivedSecrets outside segment.parameter sk.seed (address segment)))
      (fun level => evalWithAnswerFn outside
        (Seeded.surrogate segment.parameter sk.seed level : OracleComp HashSpec Digest)) index lay
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index sk.seed : OracleComp HashSpec Digest)) := by
  simp only [Seeded.signLayer, Seeded.layerMessage, evalWithAnswerFn_bind, hparameter, ftsKey_answer]
  rw [Seeded.otsSign, otsSignFrom_from_frontier segment tables high outside sk.seed lay
    (treeIndexAt index lay) (leafIndexAt index lay) _ encodingAttemptLimit 0 hsafe]
  unfold publicLayer
  cases hsearch : firstEncoding outside segment.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index sk.seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 with
  | none => simp only [Option.map_none, evalWithAnswerFn_pure]
  | some pair =>
      simp only [Option.map_some, evalWithAnswerFn_bind, treePath_from_frontier, evalWithAnswerFn_pure]

/-- The single selected leaf's first successful encoding determines the permitted cutoff.
If that leaf has no successful encoding, the condition is vacuous. -/
def ReferenceCutoff (segment : Segment) (outside : QueryImpl HashSpec Id) (seed : MasterSeed) : Prop :=
  ∀ counter word,
    firstEncoding outside segment.parameter segment.lay segment.tree segment.leaf
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter segment.leaf seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 = some (counter, word) → segment.digit.val ≤ (word segment.chainIdx).val

omit [Params] in
theorem referenceCutoff_of_selected (segment : Segment) (outside : QueryImpl HashSpec Id)
    (seed : MasterSeed) (counter : Counter) (word : Encoding)
    (hselected : firstEncoding outside segment.parameter segment.lay segment.tree segment.leaf
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter segment.leaf seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 = some (counter, word))
    (hcutoff : segment.digit.val ≤ (word segment.chainIdx).val) :
    ReferenceCutoff segment outside seed := by
  intro counter' word' hselected'
  have hword : word' = word := congrArg Prod.snd (Option.some.inj (hselected'.symm.trans hselected))
  rwa [hword]

omit [Params] in
theorem referenceCutoff_of_none (segment : Segment) (outside : QueryImpl HashSpec Id)
    (seed : MasterSeed)
    (hselected : firstEncoding outside segment.parameter segment.lay segment.tree segment.leaf
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter segment.leaf seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 = none) : ReferenceCutoff segment outside seed := by
  intro counter word hselected'
  rw [hselected] at hselected'
  cases hselected'

omit [Params] in
/-- Because the scheme has one tree and each leaf signs its own fixed FORS key, the selected
leaf's cutoff works for every signing request. Other leaves do not expose the chosen chain. -/
theorem referenceCutoff_safe (segment : Segment) (outside : QueryImpl HashSpec Id)
    (seed : MasterSeed) (hcutoff : ReferenceCutoff segment outside seed)
    (index : Index) (lay : Layer) (counter : Counter) (word : Encoding)
    (hselected : firstEncoding outside segment.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index seed : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 = some (counter, word)) :
    DisclosesAbove segment lay (treeIndexAt index lay) (leafIndexAt index lay) word := by
  intro chain haddr
  obtain ⟨hlay, htree, hleaf, hchain⟩ :=
    (show lay = segment.lay ∧ treeIndexAt index lay = segment.tree ∧
        leafIndexAt index lay = segment.leaf ∧ chain = segment.chainIdx by
      simpa only [address, Prod.mk.injEq] using haddr)
  have hindex : index = segment.leaf := by
    apply Fin.ext
    have hv := congrArg (fun value : LeafIndex => value.val) hleaf
    simpa only [Completeness.leafIndexAt_eq] using hv
  have hreference := hselected
  rw [htree, hleaf, hlay, hindex] at hreference
  rw [hchain]
  exact hcutoff counter word hreference

/-- Endpoint-only factoring for every signLayer call from one selected-leaf cutoff certificate. -/
theorem signLayer_from_referenceCutoff (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (hparameter : sk.parameter = segment.parameter)
    (hcutoff : ReferenceCutoff segment outside sk.seed) :
    evalWithAnswerFn (answer segment tables high outside)
      (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay))) =
    publicLayer segment outside (derivedSecrets outside segment.parameter sk.seed)
      (SphincsSecurity.Concrete.PartialChainEndpoint.evaluate tables
        (derivedSecrets outside segment.parameter sk.seed (address segment)))
      (fun level => evalWithAnswerFn outside
        (Seeded.surrogate segment.parameter sk.seed level : OracleComp HashSpec Digest)) index lay
      (evalWithAnswerFn outside (Seeded.ftsKey segment.parameter index sk.seed : OracleComp HashSpec Digest)) :=
  signLayer_from_frontier segment tables high outside sk index lay hparameter
    (referenceCutoff_safe segment outside sk.seed hcutoff index lay)

end LeanSphincs.Security.Prefix
