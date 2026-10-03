import LeanSphincs.BridgeClassify
import LeanSphincs.BridgeSupport

/-! Deterministic core: a winning non-stopped run of the rich program yields a cached hit of
a fixed target or a covered FORS digest. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.HiddenBridge

open Concrete Completeness Graph GraphCorrectness TargetAssignment HiddenGraph Assembly SeedModel Reduce Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### The honest counter is the canonical one -/

omit [Params] in
theorem otsSignFrom_firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) :
    ∀ (attempts start : Nat) {counter : Counter} {values : ChainIndex → Digest},
      evalWithAnswerFn f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start
          : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) = some (counter, values) →
      ∃ word, Prefix.firstEncoding f parameter lay tree leaf message attempts start = some (counter, word) := by
  intro attempts
  induction attempts with
  | zero => intro start counter values h; simp [Seeded.otsSignFrom] at h
  | succ attempts ih =>
      intro start counter values h
      rw [Seeded.otsSignFrom, evalWithAnswerFn_bind] at h
      cases hencode : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          rw [hencode] at h
          obtain ⟨word, hword⟩ := ih (start + 1) h
          exact ⟨word, by simp only [Prefix.firstEncoding, hencode, hword]⟩
      | some encoding =>
          rw [hencode] at h
          simp only [eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨encoding, by simp only [Prefix.firstEncoding, hencode]⟩

theorem honest_counter (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (signature : Signature)
    (hland : Landed sk.parameter (digestIndex (Completeness.digestValue f sk message randomness)))
    (hsign : evalWithAnswerFn f (Randomized.finishSign sk message randomness) = some signature) :
    SignatureWitness.chosenCounter f sk.parameter sk.seed
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) =
        some (signature.layers topLayer).counter := by
  obtain ⟨-, -, -, hlayers⟩ := Completeness.finishSign_spec f sk message randomness hland hsign
  obtain ⟨hots, -⟩ := Completeness.signLayer_spec f sk _ topLayer (hlayers topLayer)
  simp only [Completeness.treeIndexAt_eq, Completeness.leafIndexAt_eq] at hots
  obtain ⟨word, hword⟩ := otsSignFrom_firstEncoding f sk.parameter topLayer rootTree _ sk.seed _
    encodingAttemptLimit 0 hots
  have hindex : SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature =
      digestIndex (Completeness.digestValue f sk message signature.randomness) := rfl
  rw [hindex]
  simp only [SignatureWitness.chosenCounter, ReferenceChoice.selection]
  rw [show SignatureWitness.canonicalFors f sk.parameter sk.seed
      (digestIndex (Completeness.digestValue f sk message signature.randomness)) =
    Completeness.layerMessageValue f sk
      (digestIndex (Completeness.digestValue f sk message signature.randomness)) topLayer from rfl, hword]
  rfl

/-! ### The fixed comparison-world events -/

section Events

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs)

/-- Material of the sample whose hidden coordinates are the table's. -/
noncomputable def materialT (table : HiddenGraph.Table) : SeedModel.Material :=
  splitMaterial parameterOutput highs remaining (mix (truncateHash parameterOutput) fixed table)

noncomputable def answersT (table : HiddenGraph.Table) : CanonicalGraphLabels :=
  splitAnswers highs remaining (mix (truncateHash parameterOutput) fixed table)

/-- Encoding targets fixed by the preparation's search results. -/
noncomputable def encTable (parameter : PublicParameter) (forsKey : Index → Digest)
    (results : Index → Option (Counter × Encoding)) : TargetAssignment.Table := fun fields =>
  (encodingAt fields).map fun leaf =>
    ⟨(results leaf).map (fun pair => Wots.encodingInput parameter topLayer rootTree leaf (forsKey leaf) pair.1),
      Completeness.pack (((results leaf).map Prod.snd).getD ReferenceChoice.dummyWord)⟩

/-- All fixed targets of one sample, hidden table and preparation. -/
noncomputable def compTable (table : HiddenGraph.Table) (results : Index → Option (Counter × Encoding)) :
    TargetAssignment.Table := fun fields =>
  match positionAt fields with
  | some _ => referenceTable (truncateHash parameterOutput)
      (materialOts (materialT parameterOutput fixed highs remaining table))
      (materialFts (materialT parameterOutput fixed highs remaining table))
      (PrunedGraph.active (truncateHash parameterOutput))
      (PrunedGraph.boundary (truncateHash parameterOutput)
        (materialSurrogates (materialT parameterOutput fixed highs remaining table)))
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)) fields
  | none => encTable (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining).forsKey results fields

end Events

/-- The verifier's message digest of a forgery, read from a cache. -/
def cachedDigest (cache : QueryCache HashSpec) (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) : Option MessageDigest := do
  let first ← cache (tweakableHashInput parameter (.message 0) (messageDigestPayload root message randomness))
  let second ← cache (tweakableHashInput parameter (.message 1) (messageDigestPayload root message randomness))
  return truncateMessageDigest first second

/-- FORS secrets revealed by the run. -/
noncomputable def revealedSet (reveals : List HiddenGraph.Coordinate) : Disclosures := fun index tree =>
  Finset.univ.filter fun leaf => HiddenGraph.Coordinate.ftsSecret index tree leaf ∈ reveals

/-- A cached, landed digest of an unsigned message-randomizer pair whose FORS openings were all
revealed by the run. -/
def ForsCover (parameter : PublicParameter) (root : Digest) (outcome : Outcome)
    (reveals : List HiddenGraph.Coordinate) (cache : QueryCache HashSpec) : Prop :=
  ∃ digest, cachedDigest cache parameter root outcome.1.message outcome.1.signature.randomness = some digest ∧
    Landed parameter (digestIndex digest) ∧
    (∀ entry ∈ outcome.2.1, ∀ signature, entry.2 = some signature →
      ¬(entry.1 = outcome.1.message ∧ signature.randomness = outcome.1.signature.randomness)) ∧
    Covered (revealedSet reveals) (fullDigestView digest)

/-! ### Auxiliary facts for one sample -/

section Aux

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs)

theorem mix_agree_fixed (table : HiddenGraph.Table) :
    ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      mix (truncateHash parameterOutput) fixed table coordinate = fixed coordinate :=
  fun coordinate h => mix_known _ fixed table coordinate h

theorem graphCoordinates_T (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table) :
    graphCoordinates (materialT parameterOutput fixed highs remaining table)
      (answersT parameterOutput fixed highs remaining table) = table := by
  unfold materialT answersT
  rw [graphCoordinates_split, masked_mix, htable]

theorem publicData_T (table : HiddenGraph.Table) :
    GraphView.publicData (labelsOf (materialT parameterOutput fixed highs remaining table)
      (answersT parameterOutput fixed highs remaining table)) =
      sampleData parameterOutput fixed highs remaining :=
  publicData_agree parameterOutput highs remaining _ fixed (mix_agree_fixed parameterOutput fixed table)

theorem structCache_T (table : HiddenGraph.Table) :
    structCache (materialT parameterOutput fixed highs remaining table)
      (answersT parameterOutput fixed highs remaining table) =
      structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed) :=
  structCache_agree parameterOutput highs remaining _ fixed (mix_agree_fixed parameterOutput fixed table)

/-- Away from the chosen seed's derivations, the consistent preparation is the hidden-row oracle. -/
theorem sampleFn_answer (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (seed : MasterSeed) (outside : Eager.Table) (input : HashInput)
    (hnot : ¬SeedGuess.SeedHit input seed) :
    sampleFn (materialT parameterOutput fixed highs remaining table) seed
        (answersT parameterOutput fixed highs remaining table) outside input =
      HiddenRows.answer (sampleModel parameterOutput highs) table
        (outsideFn (splitMaterial parameterOutput highs remaining fixed)
          (splitAnswers highs remaining fixed) outside) input := by
  rw [Reduce.sampleFn_agree _ _ _ _ _ hnot, graphFn_eq_answer,
    graphCoordinates_T parameterOutput fixed highs remaining table htable]
  unfold sampleModel
  rw [rowModel_answer]
  have hparameter : parameter (materialT parameterOutput fixed highs remaining table) =
      truncateHash parameterOutput := rfl
  rw [hparameter]
  unfold materialT answersT
  rw [answer_congr_high _ _ _ _ (fun address => highs address.outputCoordinate) _
    (fun address hactive => highHalves_split parameterOutput highs remaining _ address hactive)]
  unfold outsideFn
  rw [structCache_agree parameterOutput highs remaining _ fixed (mix_agree_fixed parameterOutput fixed table)]

end Aux

omit [Params] in
/-- The hidden-row oracle over the structural cache and a table read off a final cache is the
final-cache oracle, on every short input. -/
theorem answer_extend_final {A : Type} (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
    (table : HiddenGraph.Table) (base cacheF : QueryCache HashSpec)
    (hbase : ∀ input answer, base input = some answer → cacheF input = some answer)
    (input : HashInput) (hshort : Short.IsShort input) :
    HiddenRows.answer model table (extend base (fun short => finalFn model table cacheF short.val)) input =
      finalFn model table cacheF input := by
  have houtside : extend base (fun short => finalFn model table cacheF short.val) input =
      (cacheF input).getD 0 ∨ ∃ query, model.parse input = some query ∧
        query.2 = table (model.incoming query.1) := by
    unfold extend
    cases hb : base input with
    | some answer => left; rw [hbase _ _ hb]; rfl
    | none =>
        simp only [Option.getD_none, hshort, ↓reduceDIte]
        unfold finalFn HiddenRows.answer
        cases hp : model.parse input with
        | none => left; rfl
        | some query =>
            by_cases hmatch : query.2 = table (model.incoming query.1)
            · right; exact ⟨query, rfl, hmatch⟩
            · left; simp [hmatch]
  unfold finalFn HiddenRows.answer
  cases hp : model.parse input with
  | none =>
      rcases houtside with h | ⟨query, hq, _⟩
      · exact h
      · rw [hp] at hq; cases hq
  | some query =>
      simp only [Option.elim_some]
      split_ifs with hmatch
      · rfl
      · rcases houtside with h | ⟨query', hq, hmatch'⟩
        · exact h
        · rw [hp] at hq
          cases hq
          exact absurd hmatch' hmatch

omit [Params] in
/-- Preparation facts: the structural cache persists, and every leaf's encoding search result is
the one recorded, for any function agreeing with the prepared cache. -/
theorem preparation_support (parameter : PublicParameter) (forsKey : Index → Digest)
    (base : QueryCache HashSpec) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ randomOracle (searchAll parameter forsKey)).run base))
    (f : QueryImpl HashSpec Id) (hf : prepared.2.AgreesWithFn f) :
    base ≤ prepared.2 ∧ ∀ leaf, Prefix.firstEncoding f parameter topLayer rootTree leaf (forsKey leaf)
      encodingAttemptLimit 0 = prepared.1 leaf := by
  obtain ⟨hle, heval⟩ := replay_hash_support _ base prepared.1 prepared.2 hprepared f hf
  refine ⟨hle, fun leaf => ?_⟩
  rw [← heval, searchAll, eval_sequenceFin, ← ReferenceChoice.eval_search]

/-! ### Runs: short entries, cost, seed choice and support transfer -/

omit [Params] in
theorem OnlyC.withReveals {α : Type} {computation : OracleComp GraphView.CostSpec α}
    (h : OnlyC computation) : OnlyC (withReveals computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      rw [withReveals_query_bind']
      exact OnlyC.bind (OnlyC.query hinput) (fun value => OnlyC.map _ (ih value (hnext value)))

omit [Params] in
theorem costRun_entries_short {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp GraphView.CostSpec α) (h : OnlyC computation)
    (result : α × List (HiddenCost.Entry HashInput)) (hresult : result ∈ support (Stop.costRun f table computation)) :
    ∀ input, Sum.inl input ∈ result.2 → Short.IsShort input := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [Stop.costRun_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      intro input hinput
      simp at hinput
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      rw [Stop.costRun_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      intro bytes hbytes
      rcases List.mem_append.mp hbytes with hrec | hrest
      · rcases input with (draw | (other | coordinate)) | amount <;> simp [HiddenCost.recorded] at hrec
        subst hrec
        by_contra hlong
        exact hinput hlong
      · exact ih answer (hnext answer) tail htail bytes hrest

omit [Params] in
theorem costRun_withReveals_cap_cost {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp GraphView.CostSpec α) (budget : Nat)
    (result : (Option α × List HiddenGraph.Coordinate) × List (HiddenCost.Entry HashInput))
    (hresult : result ∈ support (Stop.costRun f table (withReveals (HiddenCost.cap computation budget)))) :
    HiddenCost.traceCost result.2 ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      change result ∈ support (Stop.costRun f table (withReveals
        (pure (some value) : OracleComp GraphView.CostSpec _))) at hresult
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp [HiddenCost.traceCost]
  | query_bind input next ih =>
      rw [cap_query_bind_gen] at hresult
      split at hresult
      · rename_i hcost
        rw [costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        rw [support_map] at hresult
        obtain ⟨tail, htail, rfl⟩ := hresult
        have h := ih answer _ tail htail
        rw [HiddenCost.traceCost_append, HiddenCost.recorded_cost]
        omega
      · rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        simp [HiddenCost.traceCost]

omit [Params] in
theorem ordinary_length_le_cost (entries : List (HiddenCost.Entry HashInput)) :
    (entries.filterMap fun entry => match entry with
      | .inl input => some input
      | .inr _ => none).length ≤ HiddenCost.traceCost entries := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      cases entry with
      | inl input =>
          simp only [List.filterMap_cons, List.length_cons, HiddenCost.traceCost, List.map_cons,
            List.sum_cons, HiddenCost.entryCost] at ih ⊢
          omega
      | inr amount =>
          simp only [List.filterMap_cons, HiddenCost.traceCost, List.map_cons, List.sum_cons] at ih ⊢
          omega

omit [Params] in
/-- A seed named by none of fewer than 2^256 inputs. -/
theorem exists_seed_avoiding (inputs : List HashInput) (hlength : inputs.length < 2 ^ 256) :
    ∃ seed : MasterSeed, ∀ input ∈ inputs, ¬SeedGuess.SeedHit input seed := by
  let named : Finset MasterSeed := (inputs.filterMap SeedGuess.parseSeed).toFinset
  have hcard : named.card < (Finset.univ : Finset MasterSeed).card := by
    rw [Finset.card_univ]
    calc named.card ≤ (inputs.filterMap SeedGuess.parseSeed).length := List.toFinset_card_le _
      _ ≤ inputs.length := List.length_filterMap_le _ _
      _ < 2 ^ 256 := hlength
      _ = Fintype.card MasterSeed := by simp
  obtain ⟨seed, -, hseed⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨seed, fun input hinput hhit => hseed ?_⟩
  have hparse := (SeedGuess.parseSeed_eq_some_iff input seed).mpr hhit
  simp only [named, List.mem_toFinset, List.mem_filterMap]
  exact ⟨input, hinput, hparse⟩

omit [Params] in
/-- A fixed-function run depends only on the function at its recorded ordinary inputs. -/
theorem costRun_support_congr {α : Type} (f g : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp GraphView.CostSpec α) (result : α × List (HiddenCost.Entry HashInput))
    (hresult : result ∈ support (Stop.costRun f table computation))
    (hagree : ∀ input, Sum.inl input ∈ result.2 → f input = g input) :
    result ∈ support (Stop.costRun g table computation) := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value => simpa [Stop.costRun_pure] using hresult
  | query_bind input next ih =>
      rw [Stop.costRun_query_bind, mem_support_bind_iff] at hresult ⊢
      obtain ⟨answer, hanswer, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      have htailAgree : ∀ x, Sum.inl x ∈ tail.2 → f x = g x :=
        fun x hx => hagree x (List.mem_append_right _ hx)
      refine ⟨answer, ?_, by rw [support_map]; exact ⟨tail, ih answer tail htail htailAgree, rfl⟩⟩
      rcases input with (draw | (bytes | coordinate)) | amount
      · exact hanswer
      · have hb := hagree bytes (by simp [HiddenCost.recorded])
        simpa [Stop.fixedCostP, hb] using hanswer
      · exact hanswer
      · exact hanswer

/-! ### Reachable coordinates of the sample model -/

theorem knownOf_known (parameter : PublicParameter) (fixed : HiddenGraph.Table) (coordinate : Coordinate)
    (value : Digest) (h : knownOf parameter fixed coordinate = some value) :
    KnownCoordinate parameter coordinate := by
  unfold knownOf at h
  split at h
  · assumption
  · cases h

theorem reach_ftsSecret (parameterOutput : HashOutput) (highs : CoordinateHighs) (fixed : HiddenGraph.Table)
    (reveals : List Coordinate) (coordinate : Coordinate)
    (h : Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      reveals coordinate) :
    ∀ index tree leaf, coordinate = .ftsSecret index tree leaf → coordinate ∈ reveals := by
  induction h with
  | known coordinate value hvalue =>
      intro index tree leaf heq
      subst heq
      exact (knownOf_known _ fixed _ value hvalue).elim
  | reveal coordinate hmem => intro _ _ _ _; exact hmem
  | succ address _ _ =>
      intro index tree leaf heq
      cases address <;> simp [sampleModel, rowModel, Address.outputCoordinate] at heq

theorem reach_chain (parameterOutput : HashOutput) (highs : CoordinateHighs) (fixed : HiddenGraph.Table)
    (reveals : List Coordinate) (leaf : LeafIndex) (hland : Landed (truncateHash parameterOutput) leaf)
    (word : Encoding)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain topLayer rootTree leaf chain position ∈ reveals → (word chain).val ≤ position.val)
    (coordinate : Coordinate)
    (h : Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      reveals coordinate) :
    ∀ (chain : ChainIndex) (position : Digit),
      coordinate = .chain topLayer rootTree leaf chain position → (word chain).val ≤ position.val := by
  induction h with
  | known coordinate value hvalue =>
      intro chain position heq
      subst heq
      rcases knownOf_known _ fixed _ value hvalue with htop | hout
      · have := (word chain).isLt
        simp only [chainLength, winternitzBits] at this htop ⊢
        omega
      · exact (hout hland).elim
  | reveal coordinate hmem =>
      intro chain position heq
      subst heq
      exact hreveals chain position hmem
  | succ address _ ih =>
      intro chain position heq
      cases address with
      | chain lay tree leaf' chainIdx step =>
          simp only [sampleModel, rowModel, Address.outputCoordinate, Coordinate.chain.injEq] at heq
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
          have hprev := ih chainIdx ⟨step.val, by have := step.isLt; omega⟩ rfl
          simp only at hprev ⊢
          omega
      | ftsLeaf index tree leaf' =>
          simp [sampleModel, rowModel, Address.outputCoordinate] at heq

end LeanSphincs.Security.HiddenBridge
