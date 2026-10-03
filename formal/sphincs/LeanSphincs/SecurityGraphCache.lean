import LeanSphincs.SecurityGraph
import LeanSphincs.SecuritySeedCoupling

/-! A prepared canonical graph gives an initially clean structural-target cache.
Canonical inputs are exempt; omitted positions may instead carry surrogate targets.
The statement applies to the actual lazy random-oracle preparation, including its cache. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.Graph

open Concrete Completeness TargetAssignment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512
set_option maxHeartbeats 400000
attribute [local irreducible] canonicalGraphInput canonicalGraphSlots

noncomputable def positionAt (fields : TweakFields) : Option Position :=
  @dite (Option Position) (∃ position : Position, hashDomainFields position.domain = fields)
    (Classical.propDecidable _) (fun h => some h.choose) (fun _ => none)

theorem positionAt_some_iff (fields : TweakFields) (position : Position) :
    positionAt fields = some position ↔ hashDomainFields position.domain = fields := by
  rw [positionAt]
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro hp; exact Position.fields_injective (h.choose_spec.trans hp.symm)
  · rename_i h
    constructor
    · intro heq; cases heq
    · intro hp; exact False.elim (h ⟨position, hp⟩)

attribute [local irreducible] positionAt

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

/-- Active nodes have their canonical input exempted. Boundary nodes have no such input. -/
noncomputable def referenceTable (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) : Table := fun fields =>
  match positionAt fields with
  | none => none
  | some position =>
      if active position then
        some ⟨some (canonicalGraphInput parameter otsSecret ftsSecret position labels),
          truncateHash (labels position)⟩
      else (boundary position).map fun value => ⟨none, value⟩

theorem referenceTable_active (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) (position : Position) (hactive : active position) :
    referenceTable parameter otsSecret ftsSecret active boundary labels
      (hashDomainFields position.domain) =
        some ⟨some (canonicalGraphInput parameter otsSecret ftsSecret position labels),
          truncateHash (labels position)⟩ := by
  unfold referenceTable
  rw [(positionAt_some_iff _ position).2 rfl]
  exact if_pos hactive

theorem referenceTable_boundary (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) (position : Position) (hactive : ¬active position)
    (value : Digest) (hboundary : boundary position = some value) :
    referenceTable parameter otsSecret ftsSecret active boundary labels
      (hashDomainFields position.domain) = some ⟨none, value⟩ := by
  unfold referenceTable
  rw [(positionAt_some_iff _ position).2 rfl]
  simp only [if_neg hactive, hboundary, Option.map_some]

theorem canonical_target_empty (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) (position : Position) (hactive : active position) :
    targets parameter (referenceTable parameter otsSecret ftsSecret active boundary labels)
      (canonicalGraphInput parameter otsSecret ftsSecret position labels) = ∅ := by
  rw [canonicalGraphInput, targets_at_entry _ _ _ _ _
    (referenceTable_active parameter otsSecret ftsSecret active boundary labels position hactive)]
  simp [canonicalGraphInput]

theorem target_has_position (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) (input : HashInput) (value : Digest)
    (hmem : value ∈ targets parameter
      (referenceTable parameter otsSecret ftsSecret active boundary labels) input) :
    ∃ position : Position, ∃ payload : HashInput,
      input = tweakableHashInput parameter position.domain payload := by
  unfold targets at hmem
  cases hf : parseFields parameter input with
  | none => simp [hf] at hmem
  | some fields =>
      simp only [hf] at hmem
      cases hp : positionAt fields with
      | none =>
          unfold referenceTable at hmem
          rw [hp] at hmem
          exact False.elim (Finset.notMem_empty _ hmem)
      | some position =>
          obtain ⟨payload, hinput⟩ := (parseFields_some_iff parameter input fields).1 hf
          have hfields := (positionAt_some_iff fields position).1 hp
          refine ⟨position, payload, ?_⟩
          simpa only [tweakableHashInput, tweakBytes, hfields] using hinput

/-- Preparation starts with no structural addresses populated; seed material satisfies this
because its serialized domain tags are disjoint. -/
def FreshStructural (cache : QueryCache HashSpec) : Prop :=
  ∀ (position : Position) (payload : HashInput),
    cache (tweakableHashInput parameter position.domain payload) = none

theorem freshStructural_clean (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) (cache : QueryCache HashSpec)
    (hfresh : FreshStructural parameter cache) :
    ¬CacheMatch.Bad (targets parameter
      (referenceTable parameter otsSecret ftsSecret active boundary labels)) cache := by
  rintro ⟨input, answer, hcache, hmem⟩
  obtain ⟨position, payload, rfl⟩ := target_has_position parameter otsSecret ftsSecret
    active boundary labels input (truncateHash answer) hmem
  rw [hfresh position payload] at hcache
  cases hcache

omit parameter otsSecret ftsSecret in
theorem query_cache_origin (queried input : HashInput) (cache : QueryCache HashSpec)
    (answer : HashOutput) (cache' : QueryCache HashSpec)
    (hmem : (answer, cache') ∈ support ((randomOracle (spec := HashSpec) queried).run cache))
    (value : HashOutput) (hentry : cache' input = some value) :
    cache input = some value ∨ input = queried := by
  cases hc : cache queried with
  | some old =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact Or.inl hentry
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, support_map] at hmem
      obtain ⟨sample, _, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := heq
      by_cases hi : input = queried
      · exact Or.inr hi
      · exact Or.inl (by rwa [QueryCache.cacheQuery_of_ne _ _ hi] at hentry)

omit parameter otsSecret ftsSecret in
/-- Every final cache entry either existed initially or occurs in this supported run's trace. -/
theorem hash_cache_origin {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (result : α) (cache' : QueryCache HashSpec)
    (hmem : (result, cache') ∈ support ((simulateQ randomOracle oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f)
    (input : HashInput) (value : HashOutput) (hentry : cache' input = some value) :
    cache input = some value ∨ input ∈ queriedInputs f oa := by
  induction oa using OracleComp.inductionOn generalizing cache result cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact Or.inl hentry
  | query_bind queried next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, mid⟩, hquery, hnext⟩ := hmem
      obtain ⟨_, hcached⟩ := query_support_cached queried cache answer mid hquery
      have hle := hash_support_cache_le _ mid result cache' hnext
      have hanswer : f queried = answer := hf (hle hcached)
      rw [queriedInputs_query_bind, hanswer]
      rcases ih answer mid result cache' hnext hf hentry with hold | htrace
      · rcases query_cache_origin queried input cache answer mid hquery value hold with hold | rfl
        · exact Or.inl hold
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ htrace)

/-- The actual prepared cache contains no exceptional structural match. This remains true
with arbitrary boundary targets, provided only active positions were queried. -/
theorem prepare_cache_clean (active : Position → Prop) (boundary : Position → Option Digest)
    (initial labels : CanonicalGraphLabels) (cache cache' : QueryCache HashSpec)
    (hfresh : FreshStructural parameter cache)
    (hmem : (labels, cache') ∈ support ((simulateQ randomOracle
      (prepare parameter otsSecret ftsSecret (graphOrder active) initial)).run cache)) :
    ¬CacheMatch.Bad (targets parameter
      (referenceTable parameter otsSecret ftsSecret active boundary labels)) cache' := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn cache'
  have heval := (replay_hash_support _ cache labels cache' hmem f hf).2
  rw [eval_prepare] at heval
  rintro ⟨input, answer, hcache, htarget⟩
  rcases hash_cache_origin _ cache labels cache' hmem f hf input answer hcache with hold | htrace
  · exact freshStructural_clean parameter otsSecret ftsSecret active boundary labels cache hfresh
      ⟨input, answer, hold, htarget⟩
  · rw [prepare_queriedInputs parameter otsSecret ftsSecret f _ initial (graphOrder_sorted active),
      heval, List.mem_map] at htrace
    obtain ⟨position, hposition, rfl⟩ := htrace
    rw [canonical_target_empty parameter otsSecret ftsSecret active boundary labels position
      ((mem_graphOrder active position).1 hposition)] at htarget
    exact Finset.notMem_empty _ htarget

/-- All programmed seed material is disjoint from structural graph addresses. -/
theorem material_freshStructural (seed : MasterSeed) (material : SeedModel.Material) :
    FreshStructural parameter (SeedModel.programCache ∅ seed material) := by
  intro position payload
  exact SeedModel.programCache_verifier ∅ seed material parameter position.domain payload

/-- Prepared labels at active positions equal their cached canonical-query responses. -/
theorem prepare_labels_consistent (active : Position → Prop)
    (initial labels : CanonicalGraphLabels) (cache cache' : QueryCache HashSpec)
    (hmem : (labels, cache') ∈ support ((simulateQ randomOracle
      (prepare parameter otsSecret ftsSecret (graphOrder active) initial)).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f)
    (position : Position) (hactive : active position) :
    labels position = f (canonicalGraphInput parameter otsSecret ftsSecret position labels) := by
  have heval := (replay_hash_support _ cache labels cache' hmem f hf).2
  rw [eval_prepare] at heval
  rw [← heval]
  exact readCanonicalGraph_consistent parameter otsSecret ftsSecret f (graphOrder active)
    (graphOrder_nodup active) (graphOrder_sorted active) initial position
    ((mem_graphOrder active position).2 hactive)

/-- Nodes omitted by pruning keep their initial labels. -/
theorem prepare_labels_boundary (active : Position → Prop)
    (initial labels : CanonicalGraphLabels) (cache cache' : QueryCache HashSpec)
    (hmem : (labels, cache') ∈ support ((simulateQ randomOracle
      (prepare parameter otsSecret ftsSecret (graphOrder active) initial)).run cache))
    (position : Position) (hinactive : ¬active position) : labels position = initial position := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn cache'
  have heval := (replay_hash_support _ cache labels cache' hmem f hf).2
  rw [eval_prepare] at heval
  rw [← heval]
  exact readCanonicalGraph_preserves parameter otsSecret ftsSecret f (graphOrder active)
    initial position (fun h => hinactive ((mem_graphOrder active position).1 h))

/-- A supported prepared graph supplies the clean cache required by the actual-query bound. -/
theorem prepared_structural_target_bound {α : Type} (active : Position → Prop)
    (boundary : Position → Option Digest) (initial labels : CanonicalGraphLabels)
    (cache cache' : QueryCache HashSpec) (hfresh : FreshStructural parameter cache)
    (hmem : (labels, cache') ∈ support ((simulateQ randomOracle
      (prepare parameter otsSecret ftsSecret (graphOrder active) initial)).run cache))
    (oa : OracleComp OracleWorld α) (q : Nat)
    (hbound : ∀ result ∈ support (countedRun oa cache'), result.1.2 ≤ q) :
    Pr[fun result => CacheMatch.Bad (targets parameter
      (referenceTable parameter otsSecret ftsSecret active boundary labels)) result.2 |
        (simulateQ romImpl oa).run cache'] ≤ (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 :=
  counted_structural_target_bound parameter
    (referenceTable parameter otsSecret ftsSecret active boundary labels) oa cache'
    (prepare_cache_clean parameter otsSecret ftsSecret active boundary initial labels cache cache'
      hfresh hmem) q hbound

end LeanSphincs.Security.Graph
