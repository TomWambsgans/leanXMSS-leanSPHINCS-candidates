import LeanSphincs.SecurityGameSupport
import LeanSphincs.SecuritySignatureWitness

/-!
Extraction from supported executions of the actual candidate SUF-CMA game. References to an
honest WOTS encoding remain explicit; unsigned leaves are not assumed to have certificates.
The signing-log bridge retains private random sampling and replays only the hash-only finishing
phase against a total answer function extending the final cache.
-/

open OracleComp OracleSpec

namespace LeanSphincs.Security
open Concrete Completeness

attribute [local irreducible] Seeded.keygenFromSeed Seeded.treeRoot Seeded.treeNode
  Randomized.sign Randomized.finishSign digestAttemptLimit encodingAttemptLimit sampleMasterSeed

variable [Params]

/-- Any total function extending the final cache, rather than only one selected extension,
replays the supported generated key and accepted verifier. -/
theorem SuccessWitness.replay_with {adversary : Adversary} {finalCache : QueryCache HashSpec}
    (witness : SuccessWitness) (h : witness.Supported adversary finalCache)
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    evalWithAnswerFn f (Seeded.keygenFromSeed witness.seed :
      OracleComp HashSpec (PublicKey × Seeded.SecretKey)) = (witness.pk, witness.sk) ∧
    evalWithAnswerFn f (Concrete.verify witness.pk witness.forgery.message witness.forgery.signature :
      OracleComp HashSpec Bool) = true := by
  have hkey : witness.keyCache.AgreesWithFn f := by
    intro input answer hentry
    exact hf ((witness.cache_le h).2 ((witness.cache_le h).1 hentry))
  exact ⟨(replay_hash_support _ _ _ _ h.2.1 f hkey).2,
    (replay_hash_support _ _ _ _ h.2.2.2.1 f hf).2⟩

/-- Actual success is canonical or exceptional whenever an explicit reference certificate is
available. Every query in the verifier trace is also recorded in the actual final cache. -/
theorem SuccessWitness.reference_classification {adversary : Adversary}
    {finalCache : QueryCache HashSpec} (witness : SuccessWitness)
    (h : witness.Supported adversary finalCache) (hb : 0 < subtreeHeight)
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f)
    (counter : Counter) (word : Encoding)
    (href : SignatureWitness.ReferenceCertificate f witness.pk.parameter witness.seed
      (SignatureWitness.index f witness.pk witness.forgery.message witness.forgery.signature)
      counter word) :
    (SignatureWitness.CanonicalOpening f witness.pk witness.seed witness.forgery.message
      witness.forgery.signature counter word ∨
      SignatureWitness.Exception f witness.pk witness.seed witness.forgery.message
        witness.forgery.signature counter word) ∧
    ∀ input ∈ SignatureWitness.trace f witness.pk witness.forgery.message witness.forgery.signature,
      finalCache input = some (f input) := by
  obtain ⟨hkey, hverified⟩ := witness.replay_with h f hf
  exact ⟨SignatureWitness.accepted_classification f witness.pk witness.seed witness.forgery.message
      witness.forgery.signature counter word hb
      (keygen_root f witness.seed witness.pk witness.sk hkey) href hverified,
    witness.verifier_inputs_cached h f hf⟩

/-- This statement is directly about the public counted experiment. The actual cost is retained,
and classification is conditional on a certificate rather than asserting that one exists. -/
theorem experiment_reference_classification (adversary : Adversary) (q cost : Nat)
    (hbound : HasHashQueryBound adversary q) (hb : 0 < subtreeHeight)
    (hsuccess : (true, cost) ∈ support (experiment adversary)) :
    cost ≤ q ∧ ∃ (finalCache : QueryCache HashSpec) (witness : SuccessWitness)
      (f : QueryImpl HashSpec Id),
      ((true, cost), finalCache) ∈ support (countedRun (gameCore adversary) ∅) ∧
      witness.Supported adversary finalCache ∧ finalCache.AgreesWithFn f ∧
      (∀ input ∈ SignatureWitness.trace f witness.pk witness.forgery.message witness.forgery.signature,
        finalCache input = some (f input)) ∧
      ∀ counter word,
        SignatureWitness.ReferenceCertificate f witness.pk.parameter witness.seed
          (SignatureWitness.index f witness.pk witness.forgery.message witness.forgery.signature)
          counter word →
        SignatureWitness.CanonicalOpening f witness.pk witness.seed witness.forgery.message
            witness.forgery.signature counter word ∨
          SignatureWitness.Exception f witness.pk witness.seed witness.forgery.message
            witness.forgery.signature counter word := by
  obtain ⟨finalCache, hcount, witness, hwitness⟩ := experiment_success_witness adversary cost hsuccess
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn finalCache
  refine ⟨hbound _ hsuccess, finalCache, witness, f, hcount, hwitness, hf,
    witness.verifier_inputs_cached hwitness f hf, ?_⟩
  intro counter word href
  exact (witness.reference_classification hwitness hb f hf counter word href).1

/-- The logging interpreter used by the actual adversary phase, generalized to any return type
so its query recursion can be analyzed. -/
noncomputable def loggedProgram {α : Type} (sk : Seeded.SecretKey)
    (oa : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp OracleWorld (α × QueryLog SigningSpec) :=
  (simulateQ (QueryImpl.ofLift OracleWorld
    (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) + signingOracle sk) oa).run

theorem loggedProgram_pure {α : Type} (sk : Seeded.SecretKey) (result : α) :
    loggedProgram sk (pure result) = pure (result, []) := rfl

theorem loggedProgram_world_query {α : Type} (sk : Seeded.SecretKey)
    (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp (OracleWorld + SigningSpec) α) :
    loggedProgram sk (liftM ((OracleWorld + SigningSpec).query (.inl input)) >>= next) =
      (do let answer ← liftM (OracleWorld.query input); loggedProgram sk (next answer)) := by
  simp only [loggedProgram, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl,
    QueryImpl.ofLift_apply, WriterT.run_bind']
  change (((fun answer : OracleWorld.Range input => (answer, ([] : QueryLog SigningSpec))) <$>
      (liftM (OracleWorld.query input) : OracleComp OracleWorld _)) >>=
      fun x : OracleWorld.Range input × QueryLog SigningSpec =>
        Prod.map id (x.2 ++ ·) <$> loggedProgram sk (next x.1)) = _
  simp
  congr 1
  funext answer
  exact id_map _

theorem loggedProgram_sign_query {α : Type} (sk : Seeded.SecretKey) (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α) :
    loggedProgram sk (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) =
      (do
        let answer ← Randomized.sign sk message
        let result ← loggedProgram sk (next answer)
        pure (result.1, ⟨message, answer⟩ :: result.2)) := by
  simp only [loggedProgram, simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr,
    signingOracle, WriterT.run_bind', map_eq_bind_pure_comp, Function.comp_def]
  simp [Prod.map]

/-- A logged response was produced by a supported honest signing subrun. Its starting and ending
caches lie between the overall starting and ending caches, allowing final-cache replay. -/
theorem logged_response_support {α : Type} (sk : Seeded.SecretKey)
    (oa : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec)
    (result : α) (log : QueryLog SigningSpec) (cache' : QueryCache HashSpec)
    (hmem : ((result, log), cache') ∈ support ((simulateQ romImpl (loggedProgram sk oa)).run cache)) :
    ∀ entry ∈ log, ∃ before after : QueryCache HashSpec,
      cache ≤ before ∧ after ≤ cache' ∧
      (entry.2, after) ∈ support ((simulateQ romImpl (Randomized.sign sk entry.1)).run before) := by
  induction oa using OracleComp.inductionOn generalizing cache result log cache' with
  | pure value =>
      simp only [loggedProgram_pure, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmem
      simp
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedProgram_world_query] at hmem
          simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
          have hfirst : cache ≤ cacheMid := world_support_cache_le _ _ _ _ hquery
          intro entry hentry
          obtain ⟨before, after, hbefore, hafter, hsign⟩ :=
            ih answer cacheMid result log cache' hrest entry hentry
          exact ⟨before, after, hfirst.trans hbefore, hafter, hsign⟩
      | inr message =>
          rw [loggedProgram_sign_query] at hmem
          simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨answer, cacheMid⟩, hsign, ⟨⟨⟨tailResult, tailLog⟩, tailCache⟩, hrest, hpure⟩⟩ := hmem
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hpure
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpure
          intro entry hentry
          rcases List.mem_cons.mp hentry with rfl | htail
          · exact ⟨cache, cacheMid, le_rfl, world_support_cache_le _ _ _ _ hrest, hsign⟩
          · obtain ⟨before, after, hbefore, hafter, hresponse⟩ :=
              ih answer cacheMid result tailLog cache' hrest entry htail
            exact ⟨before, after, (world_support_cache_le _ _ _ _ hsign).trans hbefore,
              hafter, hresponse⟩

/-- The signing-log extraction specialized to the supported actual game. -/
theorem SuccessWitness.logged_response_support {adversary : Adversary}
    {finalCache : QueryCache HashSpec} (witness : SuccessWitness)
    (h : witness.Supported adversary finalCache)
    (entry : (input : SigningSpec.Domain) × SigningSpec.Range input)
    (hentry : entry ∈ witness.log) :
    ∃ before after : QueryCache HashSpec,
      witness.keyCache ≤ before ∧ after ≤ witness.forgeryCache ∧
      (entry.2, after) ∈ support
        ((simulateQ romImpl (Randomized.sign witness.sk entry.1)).run before) :=
  Security.logged_response_support witness.sk (adversary.main witness.pk) _ _ _ _ h.2.2.1 entry hentry

/-- Successful logged signatures replay their hash-only assembly phase using the final cache.
The sampled randomizer is extracted from a supported private-randomness execution. -/
theorem SuccessWitness.logged_signature_replay {adversary : Adversary}
    {finalCache : QueryCache HashSpec} (witness : SuccessWitness)
    (h : witness.Supported adversary finalCache)
    (message : Message) (honest : Signature)
    (hlogged : ⟨message, some honest⟩ ∈ witness.log)
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    ∃ randomness,
      Landed witness.sk.parameter
        (digestIndex (Completeness.digestValue f witness.sk message randomness)) ∧
      evalWithAnswerFn f (Randomized.finishSign witness.sk message randomness) = some honest := by
  obtain ⟨before, after, _, hafter, hsign⟩ := witness.logged_response_support h _ hlogged
  have hagree : after.AgreesWithFn f := by
    intro input answer hentry
    exact hf ((witness.cache_le h).2 (hafter hentry))
  exact (Completeness.randomized_sign_replay witness.sk message honest before after hsign f hagree).2

attribute [local irreducible] SignatureWitness.Exception SignatureWitness.ReferenceCertificate
  SignatureWitness.index SignatureWitness.CanonicalOpening

/-- A same-message, same-randomizer strong forgery is exceptional relative to the certificate
extracted from the actual logged signing run. -/
theorem SuccessWitness.same_randomness_exception {adversary : Adversary}
    {finalCache : QueryCache HashSpec} (witness : SuccessWitness)
    (h : witness.Supported adversary finalCache) (hb : 0 < subtreeHeight)
    (honest : Signature) (hlogged : ⟨witness.forgery.message, some honest⟩ ∈ witness.log)
    (hrandomness : witness.forgery.signature.randomness = honest.randomness)
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    ∃ word,
      SignatureWitness.ReferenceCertificate f witness.pk.parameter witness.seed
        (SignatureWitness.index f witness.pk witness.forgery.message witness.forgery.signature)
        (honest.layers topLayer).counter word ∧
      SignatureWitness.Exception f witness.pk witness.seed witness.forgery.message
        witness.forgery.signature (honest.layers topLayer).counter word := by
  obtain ⟨hkey, hverified⟩ := witness.replay_with h f hf
  obtain ⟨hseed, hparameter, hroot⟩ := keygen_secret_fields f witness.seed witness.pk witness.sk hkey
  have hpk : witness.pk = ⟨witness.sk.root, witness.sk.parameter⟩ := by
    rw [hroot, hparameter]
  have htree := keygen_root f witness.seed witness.pk witness.sk hkey
  obtain ⟨randomness, hland, hsign⟩ :=
    witness.logged_signature_replay h witness.forgery.message honest hlogged f hf
  have hne : witness.forgery.signature ≠ honest := by
    intro heq
    apply h.2.2.2.2.2
    exact ⟨⟨witness.forgery.message, some honest⟩, hlogged, rfl, congrArg some heq.symm⟩
  have hexception := SignatureWitness.strong_forgery_same_randomness f witness.sk
    witness.forgery.message randomness honest witness.forgery.signature hb
    (by simpa only [hroot, hparameter, hseed] using htree) hland hsign hrandomness hne
    (by simpa only [← hpk] using hverified)
  rw [← hpk] at hexception
  simpa only [hseed, hparameter] using hexception

/-- Tree classification retains the actual WOTS-recovered value and puts every query in that
specific tree run into the final cache. In particular an exceptional value is not selected
independently of the supported verifier. No reference encoding certificate is needed here. -/
theorem SuccessWitness.cached_tree_classification {adversary : Adversary}
    {finalCache : QueryCache HashSpec} (witness : SuccessWitness)
    (h : witness.Supported adversary finalCache) (hb : 0 < subtreeHeight)
    (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    ∃ value,
      evalWithAnswerFn f (otsLeaf witness.pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f witness.pk witness.forgery.message witness.forgery.signature))
        (verificationFors f witness.pk witness.forgery.message witness.forgery.signature)
        (witness.forgery.signature.layers topLayer).counter
        (witness.forgery.signature.layers topLayer).chainValues :
        OracleComp HashSpec (Option Digest)) = some value ∧
      (TreeOpening f witness.pk.parameter witness.seed
          (digestIndex (verificationDigest f witness.pk witness.forgery.message witness.forgery.signature))
          (signaturePath witness.forgery.signature topLayer) value ∨
        TreeException f witness.pk.parameter witness.seed
          (digestIndex (verificationDigest f witness.pk witness.forgery.message witness.forgery.signature))
          (signaturePath witness.forgery.signature topLayer) value) ∧
      ∀ input ∈ queriedInputs f (treeFold witness.pk.parameter topLayer rootTree
        (digestIndex (verificationDigest f witness.pk witness.forgery.message witness.forgery.signature))
        (signaturePath witness.forgery.signature topLayer) totalHeight value :
        OracleComp HashSpec Digest), finalCache input = some (f input) := by
  obtain ⟨hkey, hverified⟩ := witness.replay_with h f hf
  obtain ⟨value, hleaf, htree⟩ := verified_pruned_tree f witness.pk witness.seed
    witness.forgery.message witness.forgery.signature hb
    (keygen_root f witness.seed witness.pk witness.sk hkey) hverified
  obtain ⟨actual, hactual, _, _, hrun⟩ :=
    verified_tree f witness.pk witness.forgery.message witness.forgery.signature hverified
  have heq : actual = value := Option.some.inj (hactual.symm.trans hleaf)
  subst actual
  refine ⟨value, hleaf, htree, ?_⟩
  intro input hinput
  exact witness.verifier_inputs_cached h f hf input (hrun input hinput)

/-- A tree exception backed by a cached run gives a concrete cached distinct-input hash match
or a cached query that produces a derived surrogate. This is a support statement; freshness
and the time at which the target is fixed remain obligations of the probability reduction. -/
theorem TreeException.cached_witness (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (seed : MasterSeed) (leaf : LeafIndex)
    (path : Nat → Digest) (value : Digest)
    (hexception : TreeException f parameter seed leaf path value)
    (hcache : ∀ input ∈ queriedInputs f (treeFold parameter topLayer rootTree leaf path
      totalHeight value : OracleComp HashSpec Digest), cache input = some (f input)) :
    ∃ input, cache input = some (f input) ∧
      ((∃ canonicalInput, input ≠ canonicalInput ∧
          truncateHash (f input) = truncateHash (f canonicalInput)) ∨
       ∃ level, subtreeHeight ≤ level ∧ level < totalHeight ∧
          truncateHash (f input) = evalWithAnswerFn f
            (Seeded.surrogate parameter seed level : OracleComp HashSpec Digest)) := by
  rcases hexception with ⟨reference, _, level, hlevel, hmatch⟩ | ⟨level, hlevel, hsurrogate⟩
  · refine ⟨merkleInput f parameter (fun height index => .node topLayer rootTree height index)
      leaf.val path value level, ?_, Or.inl ?_⟩
    · apply hcache
      rw [← merkleFold_treeFold]
      exact merkleInput_mem f parameter _ leaf.val path value totalHeight level hlevel
    · refine ⟨merkleInput f parameter (fun height index => .node topLayer rootTree height index)
        reference.val (canonicalTreePath f parameter topLayer rootTree seed reference)
        (Completeness.node f parameter topLayer rootTree seed 0 reference.val) level,
        hmatch.2.1, ?_⟩
      exact hmatch.2.2.trans (merkleValue_succ f parameter _ reference.val _ _ level)
  · refine ⟨merkleInput f parameter (fun height index => .node topLayer rootTree height index)
      leaf.val path value (level - 1), ?_, Or.inr ⟨level, hsurrogate.1, hlevel, hsurrogate.2.2⟩⟩
    exact hcache _ (surrogatePreimage_queried f parameter topLayer rootTree leaf path value level hlevel)

end LeanSphincs.Security
