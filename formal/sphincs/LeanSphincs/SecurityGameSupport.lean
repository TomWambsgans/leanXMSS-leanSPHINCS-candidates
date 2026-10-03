import LeanSphincs.Statement
import LeanSphincs.RandomizedSupport
import LeanSphincs.SecurityTreeWitness

/-!
Support and cost-erasure bridges for the actual candidate SUF-CMA experiment. Private sampling
remains probabilistic. Only the hash-only key generation and verification subruns are replayed
against a common total answer function extending the final shared oracle cache.

The instrumentation erasure and replay arguments follow leanVM b7a107256 and VCVio's cost/logging
semantics. No security bound is assumed in this module.
-/

open OracleComp OracleSpec

namespace LeanSphincs.Security
open Completeness

attribute [local irreducible] Seeded.keygenFromSeed Seeded.treeRoot Seeded.treeNode
  Randomized.sign Randomized.finishSign digestAttemptLimit encodingAttemptLimit sampleMasterSeed

noncomputable def countedRun {α : Type} (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : ProbComp ((α × Nat) × QueryCache HashSpec) :=
  (simulateQ countedOracle oa).run.run cache

/-- Erasing cost preserves both the result and final cache as an equality of computations. -/
theorem erase_countedRun {α : Type} (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$> countedRun oa cache =
      (simulateQ romImpl oa).run cache := by
  have h := QueryImpl.fst_map_run_withCost (ω := Multiplicative Nat) romImpl
    (fun | .inl _ => Multiplicative.ofAdd (0 : Nat) | .inr _ => Multiplicative.ofAdd 1) oa
  have hr := congrArg (fun computation => computation.run cache) h
  have hcost : countedOracle = romImpl.withCost (ω := Multiplicative Nat)
      (fun | .inl _ => Multiplicative.ofAdd (0 : Nat) | .inr _ => Multiplicative.ofAdd 1) := by
    funext input
    cases input <;> rfl
  simp only [StateT.run_map] at hr
  rw [countedRun, hcost]
  simpa only [OracleWorld, AddWriterT, Multiplicative] using hr

theorem mem_support_uncounted_iff {α : Type} (oa : OracleComp OracleWorld α)
    (cache cache' : QueryCache HashSpec) (result : α) :
    (result, cache') ∈ support ((simulateQ romImpl oa).run cache) ↔
      ∃ cost : Nat, ((result, cost), cache') ∈ support (countedRun oa cache) := by
  rw [← erase_countedRun, support_map]
  constructor
  · rintro ⟨⟨⟨actual, cost⟩, finalCache⟩, hmem, heq⟩
    cases heq
    exact ⟨cost, hmem⟩
  · rintro ⟨cost, hmem⟩
    exact ⟨((result, cost), cache'), hmem, rfl⟩

variable [Params]

/-- Dropping the cache from the fully counted run recovers the exact public experiment. -/
theorem experiment_eq_countedRun (adversary : Adversary) :
    experiment adversary = Prod.fst <$> countedRun (gameCore adversary) ∅ := rfl

/-- The security advantage is unchanged when the cost counter is erased. -/
theorem erase_experiment (adversary : Adversary) :
    Prod.fst <$> experiment adversary =
      Prod.fst <$> (simulateQ romImpl (gameCore adversary)).run ∅ := by
  rw [experiment_eq_countedRun, ← erase_countedRun, Functor.map_map, Functor.map_map]

theorem forgeAdvantage_eq_uncounted (adversary : Adversary) :
    forgeAdvantage adversary =
      Pr[fun result => result.1 = true | (simulateQ romImpl (gameCore adversary)).run ∅] := by
  change Pr[(fun result : Bool => result = true) ∘ Prod.fst | experiment adversary] = _
  rw [← probEvent_map, erase_experiment, probEvent_map]
  rfl

theorem hashQueryBound_full_run (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) (result : Bool) (cost : Nat)
    (cache : QueryCache HashSpec)
    (hmem : ((result, cost), cache) ∈ support (countedRun (gameCore adversary) ∅)) : cost ≤ q := by
  apply hbound (result, cost)
  rw [experiment_eq_countedRun, support_map]
  exact ⟨((result, cost), cache), hmem, rfl⟩

omit [Params] in
/-- Uniform-sampling and hash queries both preserve every earlier cache entry. -/
theorem world_query_support_cache_le (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (answer : OracleWorld.Range input) (cache' : QueryCache HashSpec)
    (hmem : (answer, cache') ∈ support ((romImpl input).run cache)) : cache ≤ cache' := by
  cases input with
  | inl query =>
      have hforward : ((unifFwdImpl HashSpec) query).run cache =
          (fun answer => (answer, cache)) <$> (liftM (unifSpec.query query) : ProbComp _) := by
        simpa only [simulateQ_spec_query] using
          unifFwdImpl.simulateQ_run (liftM (unifSpec.query query) : ProbComp _) cache
      change (answer, cache') ∈ support (((unifFwdImpl HashSpec) query).run cache) at hmem
      rw [hforward, support_map] at hmem
      obtain ⟨_, _, heq⟩ := hmem
      cases heq
      exact le_rfl
  | inr query => exact (query_support_cached query cache answer cache' hmem).1

omit [Params] in
theorem world_support_cache_le {α : Type} (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : α) (cache' : QueryCache HashSpec)
    (hmem : (result, cache') ∈ support ((simulateQ romImpl oa).run cache)) : cache ≤ cache' := by
  induction oa using OracleComp.inductionOn generalizing cache result cache' with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact le_rfl
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      exact (world_query_support_cache_le input cache answer cacheMid hquery).trans
        (ih answer cacheMid result cache' hrest)

/-- The actual adversary/signing phase, including logging of every signing response. -/
noncomputable def adversaryPhase (adversary : Adversary) (pk : PublicKey) (sk : Seeded.SecretKey) :
    OracleComp OracleWorld (Forgery × QueryLog SigningSpec) :=
  (simulateQ (QueryImpl.ofLift OracleWorld
    (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk)
    (adversary.main pk)).run

theorem run_gameCore (adversary : Adversary) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (gameCore adversary)).run cache = (do
      let seed ← sampleMasterSeed
      let keys ← (simulateQ randomOracle
        (Seeded.keygenFromSeed seed : OracleComp HashSpec (PublicKey × Seeded.SecretKey))).run cache
      let adversaryResult ← (simulateQ romImpl
        (adversaryPhase adversary keys.1.1 keys.1.2)).run keys.2
      let verified ← (simulateQ randomOracle
        (Concrete.verify keys.1.1 adversaryResult.1.1.message adversaryResult.1.1.signature :
          OracleComp HashSpec Bool)).run adversaryResult.2
      pure (decide (SigningTranscript.Valid adversaryResult.1.2 ∧
        ¬SigningTranscript.Contains adversaryResult.1.2 adversaryResult.1.1) && verified.1,
        verified.2)) := by
  simp only [gameCore, simulateQ_bind, StateT.run_bind, run_lift_prob, simulate_lift_hash,
    map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind, simulateQ_pure, StateT.run_pure]
  rfl

/-- Every field comes from supported subruns of the actual game, with the same shared cache. -/
structure SuccessWitness where
  seed : MasterSeed
  pk : PublicKey
  sk : Seeded.SecretKey
  keyCache : QueryCache HashSpec
  forgeryCache : QueryCache HashSpec
  forgery : Forgery
  log : QueryLog SigningSpec

/-- These support predicates are kept outside the data record so the kernel never unfolds the
large executable algorithms while checking positivity of a new inductive type. -/
def SuccessWitness.Supported (witness : SuccessWitness) (adversary : Adversary)
    (finalCache : QueryCache HashSpec) : Prop :=
  witness.seed ∈ support sampleMasterSeed ∧
  ((witness.pk, witness.sk), witness.keyCache) ∈ support ((simulateQ randomOracle
    (Seeded.keygenFromSeed witness.seed : OracleComp HashSpec (PublicKey × Seeded.SecretKey))).run ∅) ∧
  ((witness.forgery, witness.log), witness.forgeryCache) ∈ support
    ((simulateQ romImpl (adversaryPhase adversary witness.pk witness.sk)).run witness.keyCache) ∧
  (true, finalCache) ∈ support ((simulateQ randomOracle
    (Concrete.verify witness.pk witness.forgery.message witness.forgery.signature :
      OracleComp HashSpec Bool)).run witness.forgeryCache) ∧
  SigningTranscript.Valid witness.log ∧ ¬SigningTranscript.Contains witness.log witness.forgery

theorem success_witness (adversary : Adversary) (finalCache : QueryCache HashSpec)
    (hmem : (true, finalCache) ∈ support ((simulateQ romImpl (gameCore adversary)).run ∅)) :
    ∃ witness : SuccessWitness, witness.Supported adversary finalCache := by
  rw [run_gameCore, mem_support_bind_iff] at hmem
  obtain ⟨seed, hseed, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨pk, sk⟩, keyCache⟩, hkeys, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨forgery, log⟩, forgeryCache⟩, hadversary, hmem⟩ := hmem
  rw [mem_support_bind_iff] at hmem
  obtain ⟨⟨verified, verifyCache⟩, hverify, hmem⟩ := hmem
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  obtain ⟨htrue, rfl⟩ := hmem
  have hcheck : (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) ∧
      verified = true := by simpa using htrue.symm
  cases hcheck.2
  exact ⟨⟨seed, pk, sk, keyCache, forgeryCache, forgery, log⟩,
    hseed, hkeys, hadversary, hverify, hcheck.1.1, hcheck.1.2⟩

/-- A supported successful result keeps its real hash cost and a complete game witness. -/
theorem experiment_success_witness (adversary : Adversary) (cost : Nat)
    (hmem : (true, cost) ∈ support (experiment adversary)) :
    ∃ finalCache, ((true, cost), finalCache) ∈ support (countedRun (gameCore adversary) ∅) ∧
      ∃ witness : SuccessWitness, witness.Supported adversary finalCache := by
  rw [experiment_eq_countedRun, support_map] at hmem
  obtain ⟨⟨⟨result, actualCost⟩, finalCache⟩, hrun, heq⟩ := hmem
  cases heq
  refine ⟨finalCache, hrun, success_witness adversary finalCache ?_⟩
  exact (mem_support_uncounted_iff _ _ _ _).2 ⟨cost, hrun⟩

theorem SuccessWitness.cache_le {adversary : Adversary} {finalCache : QueryCache HashSpec}
    (witness : SuccessWitness) (h : witness.Supported adversary finalCache) :
    witness.keyCache ≤ witness.forgeryCache ∧ witness.forgeryCache ≤ finalCache :=
  ⟨world_support_cache_le _ _ _ _ h.2.2.1,
    hash_support_cache_le _ _ _ _ h.2.2.2.1⟩

/-- One fixed answer function replays the generated key and accepted verifier. It is not used
to replace the adversary's private random sampling or the randomized signer. -/
theorem SuccessWitness.replay {adversary : Adversary} {finalCache : QueryCache HashSpec}
    (witness : SuccessWitness) (h : witness.Supported adversary finalCache) :
    ∃ f : QueryImpl HashSpec Id, finalCache.AgreesWithFn f ∧
      evalWithAnswerFn f (Seeded.keygenFromSeed witness.seed :
        OracleComp HashSpec (PublicKey × Seeded.SecretKey)) = (witness.pk, witness.sk) ∧
      evalWithAnswerFn f (Concrete.verify witness.pk witness.forgery.message witness.forgery.signature :
        OracleComp HashSpec Bool) = true := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn finalCache
  have hkey : witness.keyCache.AgreesWithFn f := by
    intro input answer hentry
    exact hf ((witness.cache_le h).2 ((witness.cache_le h).1 hentry))
  exact ⟨f, hf, (replay_hash_support _ _ _ _ h.2.1 f hkey).2,
    (replay_hash_support _ _ _ _ h.2.2.2.1 f hf).2⟩

omit [Params] in
/-- All inputs of a fixed-function replay occur with the corresponding answer in the actual
run's final cache. This connects deterministic extraction to the lazy-oracle execution. -/
theorem hash_support_queriedInputs_cached {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (result : α) (cache' : QueryCache HashSpec)
    (hmem : (result, cache') ∈ support ((simulateQ randomOracle oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f) :
    ∀ input ∈ queriedInputs f oa, cache' input = some (f input) := by
  induction oa using OracleComp.inductionOn generalizing cache result cache' with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      have hqueryCached := (query_support_cached query cache answer cacheMid hquery).2
      have hcached : cache' query = some answer :=
        hash_support_cache_le _ _ _ _ hrest hqueryCached
      have hanswer : f query = answer := hf hcached
      intro input hinput
      rw [queriedInputs_query_bind, hanswer, List.mem_cons] at hinput
      rcases hinput with rfl | hinput
      · exact hcached.trans (congrArg some hanswer.symm)
      · exact ih answer cacheMid result cache' hrest hf input hinput

theorem SuccessWitness.verifier_inputs_cached {adversary : Adversary}
    {finalCache : QueryCache HashSpec} (witness : SuccessWitness)
    (h : witness.Supported adversary finalCache) (f : QueryImpl HashSpec Id)
    (hf : finalCache.AgreesWithFn f) :
    ∀ input ∈ queriedInputs f (Concrete.verify witness.pk witness.forgery.message
      witness.forgery.signature : OracleComp HashSpec Bool), finalCache input = some (f input) :=
  hash_support_queriedInputs_cached _ _ _ _ h.2.2.2.1 f hf

end LeanSphincs.Security
