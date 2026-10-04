import LeanSphincs.BridgeEventsA
import LeanSphincs.BridgeLogGood
import LeanSphincs.BridgeClassifyA

/-! Deterministic core of the refined classification: a winning non-stopped run of the rich
program, started from knowledge that also exposes the chain values at and above the prepared
word of every landed leaf, yields a cached first-order hit or one of the paired events of
`badA`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.HiddenBridge

open Concrete Completeness Graph GraphCorrectness TargetAssignment HiddenGraph Assembly SeedModel Reduce Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### First-order inputs -/

/-- A second-order tweakable input is a root-tree chain input below the word or a FORS leaf input. -/
theorem secondOrder_tweakable {parameter : PublicParameter} {results : Index → Option (Counter × Encoding)}
    {domain : HashDomain} {payload : HashInput}
    (h : SecondOrderInput parameter results (tweakableHashInput parameter domain payload)) :
    (∃ leaf chain step, domain = .chain topLayer rootTree leaf chain step ∧
      ¬(Landed parameter leaf ∧ (preparedWord results leaf chain).val ≤ step.val)) ∨
    ∃ index tree leaf, domain = .ftsLeaf index tree leaf := by
  rcases h with ⟨leaf, chain, step, payload', heq, hnot⟩ | ⟨index, tree, leaf, secret, heq⟩
  · unfold chainInput at heq
    have hf := (tweakableInput_injective heq).1
    left
    refine ⟨leaf, chain, step, ?_, hnot⟩
    cases domain with
    | chain => exact hashFields_injective trivial trivial hf
    | _ => simp [hashDomainFields, tweakFields] at hf
  · unfold forsLeafInput at heq
    have hf := (tweakableInput_injective heq).1
    right
    refine ⟨index, tree, leaf, ?_⟩
    cases domain with
    | ftsLeaf => exact hashFields_injective trivial trivial hf
    | _ => simp [hashDomainFields, tweakFields] at hf

/-- A tweakable input outside the chain and FORS leaf domains is first order. -/
theorem not_secondOrder (parameter : PublicParameter) (results : Index → Option (Counter × Encoding))
    (domain : HashDomain) (payload : HashInput)
    (hchain : ∀ lay tree leaf chain step, domain ≠ .chain lay tree leaf chain step)
    (hfts : ∀ index tree leaf, domain ≠ .ftsLeaf index tree leaf) :
    ¬SecondOrderInput parameter results (tweakableHashInput parameter domain payload) := by
  intro h
  rcases secondOrder_tweakable h with ⟨leaf, chain, step, heq, -⟩ | ⟨index, tree, leaf, heq⟩
  · exact hchain _ _ _ _ _ heq
  · exact hfts _ _ _ heq

/-- A root-tree chain input at or above the prepared word of a landed leaf is first order. -/
theorem not_secondOrder_chain (parameter : PublicParameter) (results : Index → Option (Counter × Encoding))
    (leaf : Index) (chain : ChainIndex) (step : ChainStep) (payload : Digest)
    (h : Landed parameter leaf ∧ (preparedWord results leaf chain).val ≤ step.val) :
    ¬SecondOrderInput parameter results (chainInput parameter leaf chain step payload) := by
  intro hs
  rcases secondOrder_tweakable (domain := .chain topLayer rootTree leaf chain step) hs with
    ⟨leaf', chain', step', heq, hnot⟩ | ⟨index, tree, leaf', heq⟩
  · simp only [HashDomain.chain.injEq] at heq
    obtain ⟨-, -, rfl, rfl, rfl⟩ := heq
    exact hnot h
  · cases heq

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (table : HiddenGraph.Table)

/-- A first-order target hit at a recorded, non-canonical query is a cached first-order hit. -/
theorem cached_hitA (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : Index → Option (Counter × Encoding)) (cacheF : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (input : HashInput) (hentry : Sum.inl input ∈ entries)
    (hmem : truncateHash (f input) ∈ targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results) input)
    (hfirst : ¬SecondOrderInput (truncateHash parameterOutput) results input) :
    CacheMatch.Bad (targetsA (truncateHash parameterOutput) results
      (compTable parameterOutput fixed highs remaining table results)) cacheF := by
  have hnot := not_canonicalRow_of_target parameterOutput fixed highs remaining table htable
    results input ⟨_, hmem⟩
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hcached input hentry hnot)
  have hfin := finalFn_unparsed parameterOutput highs table cacheF input hnot
  rw [hanswer] at hfin
  refine ⟨input, answer, hanswer, ?_⟩
  have hvalue : f input = answer := (hagree input hentry).trans hfin
  unfold targetsA
  rw [if_neg hfirst, ← hvalue]
  exact hmem

/-- A recorded query that is not a correct guess is cached with its answer. -/
theorem cached_read (cacheF : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (input : HashInput) (hentry : Sum.inl input ∈ entries)
    (hnot : ∀ query, (sampleModel parameterOutput highs).parse input = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1)) :
    cacheF input = some (f input) := by
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hcached input hentry hnot)
  have hfin := finalFn_unparsed parameterOutput highs table cacheF input hnot
  rw [hanswer] at hfin
  rw [hanswer, (hagree input hentry).trans hfin]
  rfl

/-- A chain input whose payload is not the table value is not a correct guess. -/
theorem chain_not_row (leaf : Index) (hland : Landed (truncateHash parameterOutput) leaf)
    (chain : ChainIndex) (step : ChainStep) (payload : Digest)
    (hne : payload ≠ table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩)) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (chainInput (truncateHash parameterOutput) leaf chain step payload) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse hmatch
  have hp : (sampleModel parameterOutput highs).parse
      (chainInput (truncateHash parameterOutput) leaf chain step payload) =
      some (.chain topLayer rootTree leaf chain step, payload) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.chain topLayer rootTree leaf chain step, payload) hland
  rw [hp, Option.some.injEq] at hparse
  subst hparse
  rw [sampleModel_incoming] at hmatch
  exact hne hmatch

/-- A FORS leaf input whose secret is not the table value is not a correct guess. -/
theorem ftsLeaf_not_row (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (secret : Digest)
    (hne : secret ≠ table (.ftsSecret index tree leaf)) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (forsLeafInput (truncateHash parameterOutput) index tree leaf secret) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse hmatch
  have hp : (sampleModel parameterOutput highs).parse
      (forsLeafInput (truncateHash parameterOutput) index tree leaf secret) =
      some (.ftsLeaf index tree leaf, secret) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.ftsLeaf index tree leaf, secret) trivial
  rw [hp, Option.some.injEq] at hparse
  subst hparse
  rw [sampleModel_incoming] at hmatch
  exact hne hmatch

end Sample

/-! ### Reachable coordinates from exposed knowledge -/

section Reach

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (results : Index → Option (Counter × Encoding)) (known : HiddenReveal.Knowledge Coordinate)
  (hknown : ∀ c v, known c = some v →
    knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) results c)

include hknown in
/-- A coordinate reachable from exposed knowledge is reachable from the fixed knowledge and the
reveals together with the above-word coordinates. -/
theorem reach_expose (reveals : List Coordinate) {coordinate : Coordinate}
    (h : Reach (sampleModel parameterOutput highs) known reveals coordinate) :
    Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      (reveals ++ aboveList (truncateHash parameterOutput) results) coordinate :=
  reach_mono _ (fun c v hc => by
      rcases hknown c v hc with h | h
      · exact .known c v h
      · exact .reveal c (List.mem_append_right _ (mem_aboveList.mpr h)))
    (fun c hc => .reveal c (List.mem_append_left _ hc)) h

include hknown in
/-- A queried canonical FORS secret was revealed: exposure adds no FORS secrets. -/
theorem queried_ftsSecret_revealedA (table : HiddenGraph.Table) (reveals : List Coordinate)
    (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (hmem : Sum.inl (tweakableHashInput (truncateHash parameterOutput) (.ftsLeaf index tree leaf)
      (bytesLE 16 (table (.ftsSecret index tree leaf)))) ∈ entries) :
    Coordinate.ftsSecret index tree leaf ∈ reveals := by
  have hparse : (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.ftsLeaf index tree leaf)
        (bytesLE 16 (table (.ftsSecret index tree leaf)))) =
      some (.ftsLeaf index tree leaf, table (.ftsSecret index tree leaf)) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.ftsLeaf index tree leaf, table (.ftsSecret index tree leaf)) trivial
  have hreach := hguess _ hmem _ hparse (by rw [sampleModel_incoming]; rfl)
  rw [sampleModel_incoming] at hreach
  have h := reach_ftsSecret parameterOutput highs fixed _ _
    (reach_expose parameterOutput fixed highs results known hknown reveals hreach) index tree leaf rfl
  rcases List.mem_append.mp h with h | h
  · exact h
  · exact False.elim (mem_aboveList.mp h)

include hknown in
/-- A queried canonical chain value of a landed leaf is at or above its prepared word. -/
theorem queried_chain_reachA (table : HiddenGraph.Table) (reveals : List Coordinate)
    (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
    (leaf : LeafIndex) (hland : Landed (truncateHash parameterOutput) leaf)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain topLayer rootTree leaf chain position ∈ reveals →
        (preparedWord results leaf chain).val ≤ position.val)
    (chain : ChainIndex) (step : ChainStep)
    (hmem : Sum.inl (tweakableHashInput (truncateHash parameterOutput) (.chain topLayer rootTree leaf chain step)
      (bytesLE 16 (table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩)))) ∈
        entries) :
    (preparedWord results leaf chain).val ≤ step.val := by
  have hparse : (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.chain topLayer rootTree leaf chain step)
        (bytesLE 16 (table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩)))) =
      some (.chain topLayer rootTree leaf chain step,
        table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩)) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.chain topLayer rootTree leaf chain step, _) hland
  have hreach := hguess _ hmem _ hparse (by rw [sampleModel_incoming]; rfl)
  rw [sampleModel_incoming] at hreach
  refine reach_chain parameterOutput highs fixed _ leaf hland (preparedWord results leaf) ?_ _
    (reach_expose parameterOutput fixed highs results known hknown reveals hreach) chain _ rfl
  intro chain' position hposition
  rcases List.mem_append.mp hposition with h | h
  · exact hreveals chain' position h
  · exact (mem_aboveList.mp h).2.2.2

include hknown in
/-- A recorded chain query below the prepared word of a landed leaf is not a correct guess. -/
theorem chain_below_ne (table : HiddenGraph.Table) (reveals : List Coordinate)
    (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
    (leaf : LeafIndex) (hland : Landed (truncateHash parameterOutput) leaf)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain topLayer rootTree leaf chain position ∈ reveals →
        (preparedWord results leaf chain).val ≤ position.val)
    (chain : ChainIndex) (step : ChainStep) (payload : Digest)
    (hlt : step.val < (preparedWord results leaf chain).val)
    (hmem : Sum.inl (chainInput (truncateHash parameterOutput) leaf chain step payload) ∈ entries) :
    payload ≠ table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩) := by
  intro heq
  rw [heq] at hmem
  have hle := queried_chain_reachA parameterOutput fixed highs results known hknown table reveals entries
    hguess leaf hland hreveals chain step hmem
  omega

end Reach

/-! ### First-order hits at explicit inputs -/

section Hits

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
  (labels : CanonicalGraphLabels) (hconsistent : Consistent f parameter seed labels)

include hconsistent in
/-- A tree hit at a queried node input, which is first order. -/
theorem treeHit_hitA (hboundary : BoundaryCorrect f parameter seed labels) (pk : PublicKey)
    (hparameter : pk.parameter = parameter) (message : Message) (signature : Signature)
    (h : SignatureWitness.TreeHit f pk seed message signature) :
    ∃ input ∈ SignatureWitness.trace f pk message signature,
      truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input ∧
      ∀ results, ¬SecondOrderInput parameter results input := by
  subst hparameter
  obtain ⟨value, -, hrun, hcase⟩ := h
  generalize hleaf : SignatureWitness.index f pk message signature = leaf at hrun hcase
  generalize hpath : signaturePath signature topLayer = path at hrun hcase
  have hmem : ∀ level, level < totalHeight →
      merkleInput f pk.parameter (fun height index => .node topLayer rootTree height index) leaf.val path
        value level ∈ SignatureWitness.trace f pk message signature := by
    intro level hlevel
    apply hrun
    rw [← merkleFold_treeFold]
    exact merkleInput_mem f pk.parameter _ leaf.val path value totalHeight level hlevel
  have hnode : ∀ level results, ¬SecondOrderInput pk.parameter results
      (merkleInput f pk.parameter (fun height index => .node topLayer rootTree height index) leaf.val path
        value level) := fun level results => by
    unfold merkleInput
    exact not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  rcases hcase with ⟨reference, hreference, level, hlevel, hparent, hne, hout⟩ |
    ⟨level, hlevel, ⟨hlower, hpositive, hsurrogate⟩, haddress⟩
  · refine ⟨_, hmem level hlevel, ?_, hnode level⟩
    have hpos := active_hit f pk.parameter seed labels
      (treePosition topLayer rootTree (level + 1) hlevel
        ⟨reference.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt reference.isLt⟩)
      (tree_path_active pk.parameter topLayer rootTree reference hreference (level + 1) hlevel)
      (orderedPayload (leaf.val.testBit level)
        (merkleValue f pk.parameter (fun height index => .node topLayer rootTree height index) leaf.val
          path value level) (path level))
      (by
        rw [tree_path_input f pk.parameter seed labels hconsistent hboundary topLayer rootTree reference
          hreference level hlevel]
        intro heq
        apply hne
        unfold merkleInput
        rw [hparent]
        exact heq)
      (by
        rw [tree_path_value f pk.parameter seed labels hconsistent hboundary topLayer rootTree reference
          hreference (level + 1) hlevel]
        change truncateHash (f (tweakableHashInput pk.parameter
          (.node topLayer rootTree (level + 1) (reference.val / 2 ^ (level + 1))) _)) = _
        rw [← hparent]
        exact hout)
    unfold merkleInput
    rw [hparent]
    exact hpos
  · refine ⟨_, hmem (level - 1) (by omega), ?_, hnode (level - 1)⟩
    have hentry := PrunedGraph.referenceTable_surrogate pk.parameter (otsSecrets f pk.parameter seed)
      (ftsSecrets f pk.parameter seed) (surrogates f pk.parameter seed) labels topLayer rootTree
      ⟨level, hlevel⟩ hpositive hlower
    have hinput : merkleInput f pk.parameter (fun height index => .node topLayer rootTree height index)
        leaf.val path value (level - 1) =
        tweakableHashInput pk.parameter (.node topLayer rootTree level (boundaryIndex pk.parameter level))
          (orderedPayload (leaf.val.testBit (level - 1))
            (merkleValue f pk.parameter (fun height index => .node topLayer rootTree height index)
              leaf.val path value (level - 1)) (path (level - 1))) := by
      simp only [merkleInput, Nat.sub_add_cancel hpositive, haddress]
    rw [hinput]
    unfold graphTable
    rw [targets_at_entry _ _ _ _ _ hentry]
    simp only [reduceCtorEq, ↓reduceIte, Finset.mem_singleton]
    rw [← hinput]
    exact hsurrogate

include hconsistent in
/-- A FORS roots match hits at its roots input. -/
theorem rootsMatch_hit (index : Index) (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest)
    (h : Fors.RootsMatch f parameter index seed leaves secrets paths) :
    truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
        (ftsRootsPayload (Fors.roots f parameter index leaves secrets paths)))) ∈
      targets parameter (graphTable f parameter seed labels)
        (tweakableHashInput parameter (.ftsRoots index)
          (ftsRootsPayload (Fors.roots f parameter index leaves secrets paths))) := by
  obtain ⟨hne, heq⟩ := h
  refine active_hit f parameter seed labels (.ftsRoots index) trivial _ ?_ ?_
  · rw [fors_roots_input f parameter seed labels hconsistent index]
    intro hinput
    exact hne (tweakableInput_injective hinput).2.2
  · change truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
      (ftsRootsPayload (Fors.roots f parameter index leaves secrets paths)))) = _
    rw [heq, fors_key_value f parameter seed labels hconsistent index]

include hconsistent in
/-- A FORS node match hits at its node input. -/
theorem nodeMatch_hit (index : Index) (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin ftsTreeHeight → Digest) (tree : FtsTree) (level : Nat)
    (hlevel : level < ftsTreeHeight)
    (hnode : Fors.NodeMatch f parameter index tree seed (leaves tree) (secrets tree) (paths tree) level) :
    truncateHash (f (merkleInput f parameter (fun height position => .ftsNode index tree height position)
        (leaves tree).val (Fors.extendPath (paths tree))
        (Fors.leafValue f parameter index tree (leaves tree) (secrets tree)) level)) ∈
      targets parameter (graphTable f parameter seed labels)
        (merkleInput f parameter (fun height position => .ftsNode index tree height position)
          (leaves tree).val (Fors.extendPath (paths tree))
          (Fors.leafValue f parameter index tree (leaves tree) (secrets tree)) level) := by
  obtain ⟨hparent, hneq, hout⟩ := hnode
  have hpos := active_hit f parameter seed labels
    (forsPosition index tree (level + 1) hlevel
      ⟨(leaves tree).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (leaves tree).isLt⟩) trivial
    (orderedPayload ((leaves tree).val.testBit level)
      (merkleValue f parameter (fun height position => .ftsNode index tree height position)
        (leaves tree).val (Fors.extendPath (paths tree))
        (Fors.leafValue f parameter index tree (leaves tree) (secrets tree)) level)
      (Fors.extendPath (paths tree) level))
    (by
      rw [fors_path_input f parameter seed labels hconsistent index tree (leaves tree) level hlevel]
      exact hneq)
    (by
      rw [fors_path_value f parameter seed labels hconsistent index tree (leaves tree) (level + 1) hlevel]
      exact hout)
  exact hpos

end Hits

/-! ### FORS leaf contacts -/

/-- The canonical FORS leaf answer truncates to the table's leaf value. -/
theorem ftsLeaf_canonical_value (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (seed : MasterSeed) (outside : Eager.Table) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    truncateHash (sampleFn (materialT parameterOutput fixed highs remaining table) seed
        (answersT parameterOutput fixed highs remaining table) outside
        (tweakableHashInput (truncateHash parameterOutput) (.ftsLeaf index tree leaf)
          (bytesLE 16 (table (.ftsSecret index tree leaf))))) =
      table (.ftsValue index tree leaf) := by
  rw [sampleFn_answer parameterOutput fixed highs remaining table htable seed outside _
    (tweakable_not_seedHit _ _ _ seed)]
  unfold sampleModel
  rw [rowModel_answer]
  rw [show tweakableHashInput (truncateHash parameterOutput) (.ftsLeaf index tree leaf)
      (bytesLE 16 (table (.ftsSecret index tree leaf))) =
    HiddenGraph.input (truncateHash parameterOutput)
      (.ftsLeaf index tree leaf, table (Address.ftsLeaf index tree leaf).inputCoordinate) from rfl]
  rw [HiddenGraph.answer_canonical _ _ _ _ _ (.ftsLeaf index tree leaf) trivial]
  exact Prefix.truncate_combine _ _

/-- A FORS leaf match at a recorded input is a FORS contact. -/
theorem leafMatch_contact (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (cacheF : QueryCache HashSpec) (f : QueryImpl HashSpec Id) (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (seed : MasterSeed) (hcoord : GraphView.CoordinatesCorrect f (truncateHash parameterOutput) seed table)
    (hvalue : ∀ index tree leaf, truncateHash (f (tweakableHashInput (truncateHash parameterOutput)
      (.ftsLeaf index tree leaf) (bytesLE 16 (table (.ftsSecret index tree leaf))))) =
        table (.ftsValue index tree leaf))
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (secret : Digest)
    (hmatch : Fors.LeafMatch f (truncateHash parameterOutput) index tree seed leaf secret)
    (hmem : Sum.inl (forsLeafInput (truncateHash parameterOutput) index tree leaf secret) ∈ entries) :
    FContactAt (truncateHash parameterOutput) table cacheF index tree leaf := by
  obtain ⟨hne, heq⟩ := hmatch
  have hne' : secret ≠ table (.ftsSecret index tree leaf) := by rw [hcoord.2]; exact hne
  refine ⟨secret, f (forsLeafInput (truncateHash parameterOutput) index tree leaf secret), hne',
    cached_read parameterOutput highs table cacheF f entries hagree hcached _ hmem
      (ftsLeaf_not_row parameterOutput highs table index tree leaf secret hne'), ?_⟩
  have h1 : Fors.leafValue f (truncateHash parameterOutput) index tree leaf secret =
      truncateHash (f (forsLeafInput (truncateHash parameterOutput) index tree leaf secret)) := by
    simp only [Fors.leafValue, ftsLeafHash, Completeness.eval_tweakableHash]
    rfl
  have h2 : Fors.leafValue f (truncateHash parameterOutput) index tree leaf
      (Completeness.ftsSecret f (truncateHash parameterOutput) index tree leaf seed) =
      table (.ftsValue index tree leaf) := by
    rw [← hcoord.2, ← hvalue index tree leaf]
    simp only [Fors.leafValue, ftsLeafHash, Completeness.eval_tweakableHash]
  rw [← h1, heq, h2]

/-! ### The refined case analysis -/

attribute [local irreducible] ReferenceChoice.selection encodingAttemptLimit

set_option maxHeartbeats 1000000 in
/-- **Refined case analysis.** For any answer function consistent with the sample and agreeing
with the final cache on the run's queries, an accepted fresh forgery yields a cached first-order
hit, a WOTS event at a landed leaf, a FORS contact at a revealed leaf, two FORS contacts at one
instance, a near cover, or a cover of a cached, landed, unsigned digest. -/
theorem badA_of_accepted (hb : 0 < subtreeHeight) (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : Index → Option (Counter × Encoding)) (cacheF : QueryCache HashSpec)
    (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (hcons : GraphCorrectness.Consistent f (truncateHash parameterOutput) seed
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)))
    (hbound : GraphCorrectness.BoundaryCorrect f (truncateHash parameterOutput) seed
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)))
    (hdata : GraphView.DataCorrect f (truncateHash parameterOutput) seed
      (sampleData parameterOutput fixed highs remaining))
    (hcoord : GraphView.CoordinatesCorrect f (truncateHash parameterOutput) seed table)
    (hfors : ∀ leaf : Index, SignatureWitness.canonicalFors f (truncateHash parameterOutput) seed leaf =
      (sampleData parameterOutput fixed highs remaining).forsKey leaf)
    (hfull : fullTable f (truncateHash parameterOutput) seed
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table)) =
      compTable parameterOutput fixed highs remaining table results)
    (hword : ∀ leaf : Index, SignatureWitness.chosenWord f (truncateHash parameterOutput) seed leaf =
      preparedWord results leaf)
    (hvalue : ∀ index tree leaf, truncateHash (f (tweakableHashInput (truncateHash parameterOutput)
      (.ftsLeaf index tree leaf) (bytesLE 16 (table (.ftsSecret index tree leaf))))) =
        table (.ftsValue index tree leaf))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (known : HiddenReveal.Knowledge Coordinate)
    (hknown : ∀ c v, known c = some v → knownOf (truncateHash parameterOutput) fixed c = some v ∨
      AboveWord (truncateHash parameterOutput) results c)
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
    (forgery : Forgery) (log : QueryLog SigningSpec)
    (htrace : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature, Sum.inl input ∈ entries)
    (hgood : LogGood f (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining)
      log reveals)
    (hsigned : SignedRevealed f (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
      log reveals)
    (hverify : evalWithAnswerFn f (Concrete.verify ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature : OracleComp HashSpec Bool) = true)
    (hvalid : SigningTranscript.Valid log) (hnotContains : ¬SigningTranscript.Contains log forgery) :
    badA parameterOutput fixed highs remaining results table
      (((some (forgery, log, true), reveals), entries), cacheF) := by
  -- first-order hits
  have hfirstFull : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature,
      truncateHash (f input) ∈ targets (truncateHash parameterOutput)
        (fullTable f (truncateHash parameterOutput) seed
          (labelsOf (materialT parameterOutput fixed highs remaining table)
            (answersT parameterOutput fixed highs remaining table))) input →
      ¬SecondOrderInput (truncateHash parameterOutput) results input →
      badA parameterOutput fixed highs remaining results table
        (((some (forgery, log, true), reveals), entries), cacheF) := by
    intro input hinput hmem hnot
    left
    rw [hfull] at hmem
    exact cached_hitA parameterOutput fixed highs remaining table htable results cacheF f entries hagree hcached
      input (htrace input hinput) hmem hnot
  have hfirst : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature,
      truncateHash (f input) ∈ targets (truncateHash parameterOutput)
        (graphTable f (truncateHash parameterOutput) seed
          (labelsOf (materialT parameterOutput fixed highs remaining table)
            (answersT parameterOutput fixed highs remaining table))) input →
      ¬SecondOrderInput (truncateHash parameterOutput) results input →
      badA parameterOutput fixed highs remaining results table
        (((some (forgery, log, true), reveals), entries), cacheF) :=
    fun input hinput hmem => hfirstFull input hinput (graph_targets_subset _ _ _ _ _ hmem)
  -- revealed chain values are at or above the word, so chain queries below it are not guesses
  have hreveals : ∀ (leaf : Index) (chain : ChainIndex) (position : Digit),
      Coordinate.chain topLayer rootTree leaf chain position ∈ reveals →
        (preparedWord results leaf chain).val ≤ position.val := by
    intro leaf chain position h
    rw [← hword]
    exact revealed_chain_word f _ seed _ log reveals hgood hfors leaf chain position h
  have hbelow : ∀ leaf, Landed (truncateHash parameterOutput) leaf →
      ∀ (chain : ChainIndex) (step : ChainStep) (payload : Digest),
      step.val < (preparedWord results leaf chain).val →
      Sum.inl (chainInput (truncateHash parameterOutput) leaf chain step payload) ∈ entries →
      payload ≠ table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩) ∧
      cacheF (chainInput (truncateHash parameterOutput) leaf chain step payload) =
        some (f (chainInput (truncateHash parameterOutput) leaf chain step payload)) := by
    intro leaf hland chain step payload hlt hmem
    have hne := chain_below_ne parameterOutput fixed highs results known hknown table reveals entries hguess
      leaf hland (hreveals leaf) chain step payload hlt hmem
    exact ⟨hne, cached_read parameterOutput highs table cacheF f entries hagree hcached _ hmem
      (chain_not_row parameterOutput highs table leaf hland chain step payload hne)⟩
  set pk : PublicKey := ⟨(sampleData parameterOutput fixed highs remaining).root,
    truncateHash parameterOutput⟩ with hpk
  rcases SignatureWitness.accepted_recovered_classification f pk seed forgery.message forgery.signature hb
      hdata.root hverify with
    ⟨counter, hchosen, hrec⟩ | htree | ⟨hland, hwots⟩
  · -- the FORS part recovers the canonical key
    set index := SignatureWitness.index f pk forgery.message forgery.signature with hindex
    set leaves := digestLeaves (verificationDigest f pk forgery.message forgery.signature) with hleaves
    have hleafMem : ∀ tree, Sum.inl (forsLeafInput (truncateHash parameterOutput) index tree (leaves tree)
        (forgery.signature.ftsSecret tree)) ∈ entries := fun tree =>
      htrace _ (SignatureWitness.verification_fors_run f pk forgery.message forgery.signature _
        (Fors.leafInput_mem f _ _ _ _ _ tree))
    have hcanonRevealed : ∀ tree, forgery.signature.ftsSecret tree =
        Completeness.ftsSecret f (truncateHash parameterOutput) index tree (leaves tree) seed →
        leaves tree ∈ revealedSet reveals index tree := by
      intro tree hsec
      have hmem := hleafMem tree
      rw [hsec, ← hcoord.2] at hmem
      simp only [revealedSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact queried_ftsSecret_revealedA parameterOutput fixed highs results known hknown table reveals entries
        hguess _ _ _ hmem
    have hcontact : ∀ tree, Fors.LeafMatch f (truncateHash parameterOutput) index tree seed (leaves tree)
        (forgery.signature.ftsSecret tree) →
        FContactAt (truncateHash parameterOutput) table cacheF index tree (leaves tree) := fun tree hm =>
      leafMatch_contact parameterOutput highs table cacheF f entries hagree hcached seed hcoord hvalue _ _ _ _
        hm (hleafMem tree)
    rcases hrec.fors_classification with hroots | ⟨tree, level, hlevel, hnode⟩ | htrees
    · exact hfirst _ (SignatureWitness.verification_fors_run f pk _ _ _ (Fors.rootsInput_mem f _ _ _ _ _))
        (rootsMatch_hit f _ seed _ hcons _ _ _ _ hroots)
        (not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
    · refine hfirst _ (SignatureWitness.verification_fors_run f pk _ _ _
        (Fors.nodeInput_mem f _ _ _ _ _ tree level hlevel))
        (nodeMatch_hit f _ seed _ hcons _ _ _ _ tree level hlevel hnode) ?_
      unfold merkleInput
      exact not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
    · by_cases hrc : ∃ tree, Fors.LeafMatch f (truncateHash parameterOutput) index tree seed (leaves tree)
          (forgery.signature.ftsSecret tree) ∧ leaves tree ∈ revealedSet reveals index tree
      · obtain ⟨tree, hm, hr⟩ := hrc
        exact Or.inr (Or.inr (Or.inl ⟨index, tree, leaves tree, hr, hcontact tree hm⟩))
      have hunrevealed : ∀ tree, Fors.LeafMatch f (truncateHash parameterOutput) index tree seed (leaves tree)
          (forgery.signature.ftsSecret tree) → leaves tree ∉ revealedSet reveals index tree :=
        fun tree hm hr => hrc ⟨tree, hm, hr⟩
      by_cases hsignedPair : ∃ entry ∈ log, ∃ honest, entry.2 = some honest ∧ entry.1 = forgery.message ∧
          honest.randomness = forgery.signature.randomness
      · exfalso
        obtain ⟨entry, hentry, honest, hhonest, hmessage, hrandomness⟩ := hsignedPair
        have hall : ∀ tree, leaves tree ∈ revealedSet reveals index tree := by
          intro tree
          have h := SignedRevealed.ftsSecret_mem f hsigned entry hentry honest hhonest tree
          rw [hmessage, hrandomness] at h
          simp only [revealedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h
        have hopen : Fors.Opening f (truncateHash parameterOutput) index seed leaves forgery.signature.ftsSecret
            forgery.signature.ftsPath := fun tree =>
          (htrees tree).resolve_right fun hm => hunrevealed tree hm (hall tree)
        obtain ⟨randomness, hlandR, hfinish⟩ := hgood.1 entry hentry honest hhonest
        rw [hmessage] at hlandR hfinish
        have heq := canonical_signed_eq f ⟨seed, truncateHash parameterOutput,
          (sampleData parameterOutput fixed highs remaining).root⟩ forgery.message randomness
          forgery.signature honest hlandR hfinish hrandomness counter hchosen (hrec.canonical hopen)
        apply hnotContains
        exact ⟨entry, hentry, hmessage, by rw [hhonest, heq]⟩
      have hunsigned : ∀ entry ∈ log, ∀ signature, entry.2 = some signature →
          ¬(entry.1 = forgery.message ∧ signature.randomness = forgery.signature.randomness) :=
        fun entry hentry honest hhonest hpair => hsignedPair ⟨entry, hentry, honest, hhonest, hpair.1, hpair.2⟩
      have hdigest := cachedDigest_eq parameterOutput highs table cacheF f entries hagree hcached _
        forgery.message forgery.signature htrace
      by_cases htwo : ∃ tree tree', tree ≠ tree' ∧
          Fors.LeafMatch f (truncateHash parameterOutput) index tree seed (leaves tree)
            (forgery.signature.ftsSecret tree) ∧
          Fors.LeafMatch f (truncateHash parameterOutput) index tree' seed (leaves tree')
            (forgery.signature.ftsSecret tree')
      · obtain ⟨tree, tree', hne, hm, hm'⟩ := htwo
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨index, tree, tree', leaves tree, leaves tree', hne, hcontact tree hm, hcontact tree' hm'⟩)))
      by_cases hone : ∃ tree, Fors.LeafMatch f (truncateHash parameterOutput) index tree seed (leaves tree)
          (forgery.signature.ftsSecret tree)
      · obtain ⟨tree, hm⟩ := hone
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨(forgery, log, true), rfl, Or.inl
          ⟨hvalid, _, hdigest, hrec.1, hunsigned, tree, hcontact tree hm, fun other hother => ?_⟩⟩)))
        rcases htrees other with hcan | hm'
        · exact hcanonRevealed other hcan.1
        · exact (htwo ⟨tree, other, fun h => hother h.symm, hm, hm'⟩).elim
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨(forgery, log, true), rfl, Or.inr
          ⟨hvalid, _, hdigest, hrec.1, hunsigned, fun tree => ?_⟩⟩)))
        rcases htrees tree with hcan | hm
        · exact hcanonRevealed tree hcan.1
        · exact (hone ⟨tree, hm⟩).elim
  · obtain ⟨input, hinput, hmem, hnot⟩ := treeHit_hitA f (truncateHash parameterOutput) seed _ hcons hbound pk rfl
      forgery.message forgery.signature htree
    exact hfirst input hinput hmem (hnot results)
  · set leaf := SignatureWitness.index f pk forgery.message forgery.signature with hleaf
    rcases hwots with henc | hleafMatch | hchain
    · obtain ⟨message, counter, hexempt, hmem, hout⟩ := henc
      obtain ⟨input, hinput, hhit⟩ := encodingMatch_hit f (truncateHash parameterOutput) seed
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table)) leaf
        [Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf message counter]
        ⟨message, counter, hexempt, List.mem_singleton_self _, hout⟩
      rw [List.mem_singleton] at hinput
      subst hinput
      exact hfirstFull _ hmem hhit
        (not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
    · obtain ⟨endpoints, hne, hmem, hout⟩ := hleafMatch
      obtain ⟨input, hinput, hhit⟩ := leafOutput_hit f (truncateHash parameterOutput) seed _ hcons leaf hland
        [tweakableHashInput (truncateHash parameterOutput) (.leaf topLayer rootTree leaf) (leafPayload endpoints)]
        ⟨endpoints, hne, List.mem_singleton_self _, hout⟩
      rw [List.mem_singleton] at hinput
      subst hinput
      exact hfirst _ hmem hhit
        (not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
    · have hfrontier : ∀ chain, Wots.frontier f (truncateHash parameterOutput) topLayer rootTree leaf
          (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed leaf)
          (Completeness.otsSecret f (truncateHash parameterOutput) topLayer rootTree leaf seed) chain =
          frontierValue results table leaf chain := by
        intro chain
        unfold Wots.frontier frontierValue chainValue
        rw [hcoord.1 _ hland chain, hword]
      have hcontactAt : ∀ chain, Chain.Contact f (truncateHash parameterOutput) topLayer rootTree leaf chain
          (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed leaf chain)
          (Wots.frontier f (truncateHash parameterOutput) topLayer rootTree leaf
            (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed leaf)
            (Completeness.otsSecret f (truncateHash parameterOutput) topLayer rootTree leaf seed) chain)
          (SignatureWitness.trace f pk forgery.message forgery.signature) →
          ContactAt (truncateHash parameterOutput) results table cacheF leaf chain := by
        rintro chain ⟨step, payload, hstep, hmem, hout⟩
        have hstep' : step.val + 1 = (preparedWord results leaf chain).val := by rw [← hword]; exact hstep
        obtain ⟨hne, hc⟩ := hbelow leaf hland chain step payload (by omega) (htrace _ hmem)
        exact ⟨step, payload, _, hstep', hne, hc, hout.trans (hfrontier chain)⟩
      rcases hchain with ⟨chain, step, payload, hle, hmem, hhit⟩ |
        ⟨chain, first, second, payload, middle, hfs, hsw, hmem1, hmem2, hmid, hfront⟩ |
        ⟨left, right, hne, hcl, hcr⟩ | ⟨chain, ⟨message, counter, candidate, hmemE, hdecode, hneighbor⟩, hcontact⟩
      · obtain ⟨input, hinput, hhit'⟩ := chainOutput_hit f (truncateHash parameterOutput) seed _ hcons leaf hland
          [chainInput (truncateHash parameterOutput) leaf chain step payload]
          ⟨chain, step, payload, List.mem_singleton_self _, hhit⟩
        rw [List.mem_singleton] at hinput
        subst hinput
        exact hfirst _ hmem hhit' (not_secondOrder_chain _ _ _ _ _ _ ⟨hland, by rw [← hword]; exact hle⟩)
      · have hsw' : second.val + 1 = (preparedWord results leaf chain).val := by rw [← hword]; exact hsw
        obtain ⟨-, hc1⟩ := hbelow leaf hland chain first payload (by omega) (htrace _ hmem1)
        obtain ⟨-, hc2⟩ := hbelow leaf hland chain second middle (by omega) (htrace _ hmem2)
        have hmid' : truncateHash (f (chainInput (truncateHash parameterOutput) leaf chain first payload)) =
          middle := hmid
        refine Or.inr (Or.inl ⟨leaf, hland, Or.inl ⟨chain, first, second, payload,
          f (chainInput (truncateHash parameterOutput) leaf chain first payload),
          f (chainInput (truncateHash parameterOutput) leaf chain second middle), hfs, hsw', hc1, ?_,
          hfront.trans (hfrontier chain)⟩⟩)
        rw [hmid']
        exact hc2
      · exact Or.inr (Or.inl ⟨leaf, hland, Or.inr (Or.inr
          ⟨left, right, hne, hcontactAt left hcl, hcontactAt right hcr⟩)⟩)
      · have hmarker : MarkerAt (truncateHash parameterOutput) results cacheF leaf chain :=
          ⟨message, counter, _, candidate,
            cached_read parameterOutput highs table cacheF f entries hagree hcached _ (htrace _ hmemE)
              (encoding_not_row parameterOutput highs table leaf message counter),
            hdecode, by rw [← hword]; exact hneighbor⟩
        exact Or.inr (Or.inl ⟨leaf, hland, Or.inr (Or.inl ⟨chain, hcontactAt chain hcontact, hmarker⟩)⟩)

/-! ### The win implication -/

/-- **Refined win implication.** In every non-stopped lazy run of the rich program from
knowledge that contains the fixed knowledge and otherwise only above-word chain values, a
winning outcome yields the refined bad event of the table. -/
theorem win_implies_badA (hb : 0 < subtreeHeight) (adversary : Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : HiddenReveal.Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c)
    (table : HiddenGraph.Table) (htable : tableExtending known table = table)
    (outcome : Outcome) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (cacheF : QueryCache HashSpec)
    (hstop : some (((some outcome, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (HiddenCost.erase (HiddenCost.trace (richProgram (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining))))
        known prepared.2))
    (hwin : outcomeWins outcome = true) :
    badA parameterOutput fixed highs remaining prepared.1 table (((some outcome, reveals), entries), cacheF) := by
  have htable' : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table := by
    have hag := (ForsPotential.agrees_iff_extending known table).2 htable
    exact (ForsPotential.agrees_iff_extending _ table).1 fun c v hc => hag c v (hknownOf c v hc)
  obtain ⟨hgrow, hrun, hguess⟩ := lazy_support (sampleModel parameterOutput highs) table _
    known prepared.2 cacheF _ entries hstop
  obtain ⟨-, hcached⟩ := lazy_cached (sampleModel parameterOutput highs) table _
    known prepared.2 cacheF _ entries hstop
  have hOnly : OnlyC (richProgram (Internalize.internalize adversary) q (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining)) :=
    OnlyC.withReveals (OnlyC.cap (OnlyC.costGameX _ _ adversary) q)
  have hshortE := costRun_entries_short _ table _ hOnly _ hrun
  have hcost := costRun_withReveals_cap_cost _ table _ q _ hrun
  obtain ⟨seed, hseed⟩ := exists_seed_avoiding
    (entries.filterMap fun entry => match entry with | .inl input => some input | .inr _ => none)
    (lt_of_le_of_lt ((ordinary_length_le_cost entries).trans hcost) hq)
  have hseed' : ∀ input, Sum.inl input ∈ entries → ¬SeedGuess.SeedHit input seed :=
    fun input hinput => hseed input (List.mem_filterMap.mpr ⟨_, hinput, rfl⟩)
  have hstructPrep := (preparation_support _ _ _ prepared hprepared
    (preferCache prepared.2 (sampleFn (materialT parameterOutput fixed highs remaining table) seed
      (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)))
    (preferCache_agrees _ _))
  have hstruct : ∀ input answer, structCache (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed) input = some answer → cacheF input = some answer :=
    fun input answer h => hgrow input answer (hstructPrep.1 h)
  have hagreeAll := sampleFn_final parameterOutput fixed highs remaining table htable' cacheF seed hstruct
  have hagree : ∀ input, Sum.inl input ∈ entries →
      sampleFn (materialT parameterOutput fixed highs remaining table) seed
        (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF) input =
      finalFn (sampleModel parameterOutput highs) table cacheF input :=
    fun input hinput => hagreeAll input (hshortE input hinput) (hseed' input hinput)
  set f' := sampleFn (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF) with hf'
  have hrun' := costRun_support_congr _ f' table _ _ hrun (fun input hinput => (hagree input hinput).symm)
  have hagreement := sample_agreement (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hcons := sample_consistent (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hbound := sample_boundary (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hdata : GraphView.DataCorrect f' (truncateHash parameterOutput) seed
      (sampleData parameterOutput fixed highs remaining) := by
    have h := GraphView.publicData_correct f' _ seed _ hcons hbound
    rwa [publicData_T] at h
  have hcoord : GraphView.CoordinatesCorrect f' (truncateHash parameterOutput) seed table := by
    have h := GraphView.coordinates_correct f' _ seed _ hcons
    have heq := (Reduce.sampleCoordinates_eq (materialT parameterOutput fixed highs remaining table) seed
      (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)).trans
      (graphCoordinates_T parameterOutput fixed highs remaining table htable')
    unfold Assembly.sampleCoordinates at heq
    rwa [heq] at h
  obtain ⟨hverified, htrace, hgood⟩ := rich_support f' table (Internalize.internalize adversary) q
    (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining) hdata hcoord
    outcome reveals entries hrun'
  have hsigned := rich_revealed f' table (Internalize.internalize adversary) q (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining) outcome reveals entries hrun'
  have hfors : ∀ leaf : Index, SignatureWitness.canonicalFors f' (truncateHash parameterOutput) seed leaf =
      (sampleData parameterOutput fixed highs remaining).forsKey leaf := fun leaf => (hdata.forsKey leaf).symm
  have hencAgree : ∀ (leaf : Index) (counter : Counter),
      f' (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forsKey leaf) counter) =
      preferCache prepared.2 f' (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forsKey leaf) counter) :=
    fun leaf counter => encoding_preferCache parameterOutput highs table cacheF prepared.2 f' seed
      (fun input hshort hnot => hagreeAll input hshort hnot) hgrow leaf _ counter
  have hselection := selection_of_agree (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining).forsKey prepared.1 f' (preferCache prepared.2 f')
    hstructPrep.2 hencAgree
  have hfull := fullTable_eq parameterOutput fixed highs remaining table prepared.1 f' seed hagreement
    hfors hselection
  have hword : ∀ leaf : Index, SignatureWitness.chosenWord f' (truncateHash parameterOutput) seed leaf =
      preparedWord prepared.1 leaf := by
    intro leaf
    unfold SignatureWitness.chosenWord ReferenceChoice.word preparedWord
    rw [hfors leaf, hselection leaf]
  have hvalue : ∀ index tree leaf, truncateHash (f' (tweakableHashInput (truncateHash parameterOutput)
      (.ftsLeaf index tree leaf) (bytesLE 16 (table (.ftsSecret index tree leaf))))) =
        table (.ftsValue index tree leaf) := fun index tree leaf =>
    ftsLeaf_canonical_value parameterOutput fixed highs remaining table htable' seed _ index tree leaf
  obtain ⟨forgery, log, verified⟩ := outcome
  simp only [outcomeWins, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨hvalid, hnotContains⟩, rfl⟩ := hwin
  exact badA_of_accepted hb parameterOutput fixed highs remaining table htable' prepared.1 cacheF reveals entries
    f' seed hcons hbound hdata hcoord hfors hfull hword hvalue hagree hcached known hknown hguess forgery log
    htrace hgood hsigned hverified.symm hvalid hnotContains

/-! ### Exposed knowledge -/

section ExposeSupport

variable {ι : Type}
noncomputable local instance exposeSupportDecEq : DecidableEq ι := Classical.decEq _

omit [Params] in
/-- Sampling a known coordinate returns its value and keeps the knowledge. -/
theorem randomOracle_run_some (known : HiddenReveal.Knowledge ι) (c : ι) (value : Digest)
    (hc : known c = some value) (r : Digest × HiddenReveal.Knowledge ι)
    (hr : r ∈ support ((randomOracle (spec := ι →ₒ Digest) c).run known)) : r = (value, known) := by
  rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
  exact hr

omit [Params] in
/-- Sampling an unknown coordinate changes the knowledge only there. -/
theorem randomOracle_run_none (known : HiddenReveal.Knowledge ι) (c : ι) (hc : known c = none)
    (r : Digest × HiddenReveal.Knowledge ι)
    (hr : r ∈ support ((randomOracle (spec := ι →ₒ Digest) c).run known)) :
    ∀ c', c' ≠ c → r.2 c' = known c' := by
  rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
  obtain ⟨value, _, rfl⟩ := hr
  intro c' hne
  exact QueryCache.cacheQuery_of_ne _ _ hne

omit [Params] in
/-- Exposing a list of coordinates keeps the base knowledge and adds only listed coordinates. -/
theorem exposeR_known_support (P : ι → Prop) :
    ∀ (cs : List ι) (base known k : HiddenReveal.Knowledge ι),
      (∀ c ∈ cs, P c) →
      (∀ c v, base c = some v → known c = some v) →
      (∀ c v, known c = some v → base c = some v ∨ P c) →
      k ∈ support (exposeR cs known) →
      (∀ c v, base c = some v → k c = some v) ∧ (∀ c v, k c = some v → base c = some v ∨ P c)
  | [], base, known, k, _, h1, h2, hk => by
      rw [exposeR, support_pure, Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨h1, h2⟩
  | c :: cs, base, known, k, hP, h1, h2, hk => by
      rw [exposeR, mem_support_bind_iff] at hk
      obtain ⟨r, hr, hk⟩ := hk
      have hrest : ∀ c' ∈ cs, P c' := fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')
      cases hc : known c with
      | none =>
          have hr' := randomOracle_run_none known c hc r hr
          refine exposeR_known_support P cs base r.2 k hrest (fun c' v hv => ?_) (fun c' v hv => ?_) hk
          · have hne : c' ≠ c := by
              rintro rfl
              rw [h1 c' v hv] at hc
              cases hc
            rw [hr' c' hne]
            exact h1 c' v hv
          · by_cases hne : c' = c
            · subst hne
              exact Or.inr (hP c' List.mem_cons_self)
            · rw [hr' c' hne] at hv
              exact h2 c' v hv
      | some value =>
          have hr' := randomOracle_run_some known c value hc r hr
          subst hr'
          exact exposeR_known_support P cs base known k hrest h1 h2 hk

end ExposeSupport

/-- **The above-word exposure satisfies the knowledge hypotheses.** -/
theorem expose_known_support (parameter : PublicParameter) (fixed : HiddenGraph.Table)
    (results : Index → Option (Counter × Encoding)) (k : HiddenReveal.Knowledge Coordinate)
    (hk : k ∈ support (exposeR (aboveList parameter results) (knownOf parameter fixed))) :
    (∀ c v, knownOf parameter fixed c = some v → k c = some v) ∧
      (∀ c v, k c = some v → knownOf parameter fixed c = some v ∨ AboveWord parameter results c) :=
  exposeR_known_support _ _ _ _ k (fun _ hc => mem_aboveList.mp hc) (fun _ _ h => h)
    (fun _ _ h => Or.inl h) hk

omit [Params] in
/-- A completed table extends its knowledge. -/
theorem completion_extending (k : HiddenReveal.Knowledge Coordinate) (table : HiddenGraph.Table)
    (htable : table ∈ support (HiddenReveal.completion k)) : tableExtending k table = table := by
  unfold HiddenReveal.completion at htable
  rw [support_map] at htable
  obtain ⟨t, _, rfl⟩ := htable
  funext c
  simp only [tableExtending]
  cases k c <;> rfl

end LeanSphincs.Security.HiddenBridge

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- One table: the stopped run from exposed knowledge against the comparison run. -/
theorem stopped_table_leA (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c)
    (table : Coordinate → Digest) (hagree : Agrees known table) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        known prepared.2] ≤
      Pr[fun r => CorrectGuess table r.2 ∨
          badA parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
        fixedRun (sampleModel parameterOutput highs) table
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (DebtState.start prepared.2 known)] := by
  have htable := (agrees_iff_extending _ table).1 hagree
  refine le_trans (probEvent_mono fun r hr hwin => ?_)
    (stopped_le_fixedRun (sampleModel parameterOutput highs) table _ _
      (DebtState.start prepared.2 known) hagree)
  rcases r with _ | ⟨⟨⟨res, reveals⟩, entries⟩, cacheF⟩
  · trivial
  · obtain ⟨outcome, hres, hw⟩ := hwin
    simp only at hres
    subst hres
    exact win_implies_badA hb adversary q hq parameterOutput fixed highs remaining prepared hprepared known
      hknownOf hknown table htable outcome reveals entries cacheF hr hw

set_option maxRecDepth 100000 in
/-- **From the stopped experiment with exposed knowledge to the interpreted run.** -/
theorem stopped_le_interpA (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate)
    (known : Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        known prepared.2] ≤
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨
          badA parameterOutput fixed highs remaining prepared.1 x.1
            (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known] := by
  unfold HiddenOutside.stoppedExperiment
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr[= table | completion known] *
        Pr[fun r => CorrectGuess table r.2 ∨
            badA parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
          fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 known)] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion known)
        · have hag : Agrees known table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have := stopped_table_leA hb adversary q hq parameterOutput fixed highs remaining prepared
            hprepared known hknownOf hknown table hag
          exact mul_le_mul_right this _
        · rw [probOutput_eq_zero_of_not_mem_support htab, zero_mul, zero_mul]
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badA parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          withTable (fun table => fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 known)) known] := by
        unfold withTable
        rw [probEvent_bind_eq_tsum]
        refine tsum_congr fun table => ?_
        rw [probEvent_map]
        rfl
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badA parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          lazyRun (sampleModel parameterOutput highs)
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 known) >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (withTable_fixedRun _ _ _)
    _ = _ := by
        unfold richProgram
        rw [lazyRun_wrapped tg prepared.2]
        have hcomp : ((fun out : Run HashInput Coordinate HiddenBridge.Outcome × State =>
              (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
            interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 known)) >>=
              (fun result => (fun table => (table, result)) <$> completion result.2.known) =
            (fun x : (Coordinate → Digest) × (Run HashInput Coordinate HiddenBridge.Outcome × State) =>
              (x.1, (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2))) <$>
            (interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 known) >>=
              fun result => (fun table => (table, result)) <$> completion result.2.known) := by
          rw [bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rw [Functor.map_map]
        rw [hcomp, probEvent_map]
        rfl

set_option maxRecDepth 100000 in
/-- **From the stopped experiment with the above-word exposure to the interpreted run.** -/
theorem stopped_le_interp_expose (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed))) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        known prepared.2] ≤
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨
          badA parameterOutput fixed highs remaining prepared.1 x.1
            (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known] :=
  stopped_le_interpA hb adversary q hq parameterOutput fixed highs remaining prepared hprepared tg known
    (expose_known_support _ fixed prepared.1 known hk).1 (expose_known_support _ fixed prepared.1 known hk).2

end LeanSphincs.Security.ForsPotential
