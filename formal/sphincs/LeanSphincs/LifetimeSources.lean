import LeanSphincs.LifetimeIdealInterleaving

/-!
Actual signing disclosures labelled by their message/randomizer source. Accepted digest
records and successful responses are kept distinct: an exhausted WOTS search records its
accepted digest for the earlier upper bound, but supplies no successful signing source.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

structure SourceRecord where
  source : DigestCandidate
  digest : MessageDigest
  response : Option Signature
deriving DecidableEq

def CachedSource (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (source : DigestCandidate) (digest : MessageDigest) : Prop :=
  ∃ first second, cache (candidateInput sk source 0) = some first ∧
    cache (candidateInput sk source 1) = some second ∧ digest = truncateMessageDigest first second

theorem CachedSource.mono (sk : Seeded.SecretKey) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) (source : DigestCandidate) (digest : MessageDigest)
    (hsource : CachedSource sk before source digest) : CachedSource sk after source digest := by
  obtain ⟨first, second, hfirst, hsecond, hdigest⟩ := hsource
  exact ⟨first, second, hcache hfirst, hcache hsecond, hdigest⟩

theorem CachedSource.unique (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (source : DigestCandidate) (left right : MessageDigest)
    (hleft : CachedSource sk cache source left) (hright : CachedSource sk cache source right) : left = right := by
  obtain ⟨first, second, hfirst, hsecond, rfl⟩ := hleft
  obtain ⟨otherFirst, otherSecond, hotherFirst, hotherSecond, rfl⟩ := hright
  rw [hfirst] at hotherFirst
  rw [hsecond] at hotherSecond
  cases Option.some.inj hotherFirst
  cases Option.some.inj hotherSecond
  rfl

theorem messageDigest_support_source (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (result : MessageDigest × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ randomOracle
      (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run cache)) :
    cache ≤ result.2 ∧ CachedSource sk result.2 (message, randomness) result.1 := by
  simp only [messageDigest, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨⟨first, middle⟩, hfirst, ⟨⟨second, last⟩, hsecond, hresult⟩⟩ := hresult
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  obtain ⟨hbefore, hcfirst⟩ := query_support_cached _ _ _ _ hfirst
  obtain ⟨hafter, hcsecond⟩ := query_support_cached _ _ _ _ hsecond
  exact ⟨hbefore.trans hafter, first, second, hafter hcfirst, hcsecond, rfl⟩

variable [Params]

def SourceRecordConsistent (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (record : SourceRecord) : Prop :=
  CachedSource sk cache record.source record.digest ∧
    Landed sk.parameter (digestIndex record.digest) ∧
    ∀ signature, record.response = some signature → signature.randomness = record.source.2

def SourcesConsistent (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (records : List SourceRecord) : Prop := ∀ record ∈ records, SourceRecordConsistent sk cache record

theorem sourcesConsistent_mono (sk : Seeded.SecretKey) (before after : QueryCache HashSpec)
    (hcache : before ≤ after) (records : List SourceRecord)
    (hrecords : SourcesConsistent sk before records) : SourcesConsistent sk after records := by
  intro record hmem
  obtain ⟨hsource, hrest⟩ := hrecords record hmem
  exact ⟨hsource.mono sk before after hcache record.source record.digest, hrest⟩

def sourcedPrior (records : List SourceRecord) : Finset KeptDigestView :=
  (records.map (fun record => localDigestView record.digest)).toFinset

theorem sourcedPrior_cons (record : SourceRecord) (records : List SourceRecord) :
    sourcedPrior (record :: records) = insert (localDigestView record.digest) (sourcedPrior records) := by
  simp only [sourcedPrior, List.map_cons, List.toFinset_cons]

abbrev SourcedState := List SourceRecord × QueryCache HashSpec

def forgetSources (state : SourcedState) : DisclosureState := (sourcedPrior state.1, state.2)

noncomputable def signWithSources (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) : ProbComp (Option Signature × SourcedState) := do
  let loop ← (simulateQ romImpl (Randomized.signDigestLoop sk message digestAttemptLimit)).run state.2
  match loop.1 with
  | none => pure (none, (state.1, loop.2))
  | some randomness =>
    let digest ← (simulateQ randomOracle
      (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run loop.2
    let result ← (simulateQ randomOracle (finishSignBody sk randomness digest.1)).run digest.2
    pure (result.1, (⟨(message, randomness), digest.1, result.1⟩ :: state.1, result.2))

theorem signWithSources_forget_sources (sk : Seeded.SecretKey) (message : Message) (state : SourcedState) :
    (fun result => (result.1, forgetSources result.2)) <$> signWithSources sk message state =
      signWithDisclosures sk message (forgetSources state) := by
  rw [signWithSources, signWithDisclosures, map_bind]
  apply bind_congr
  rintro ⟨loop, cache⟩
  cases loop with
  | none => rfl
  | some randomness =>
    simp only [map_bind, map_pure]
    apply bind_congr
    intro digest
    apply bind_congr
    intro result
    simp only [forgetSources, sourcedPrior_cons]

/-- Erasing the source records yields exactly the actual randomized signer and final cache. -/
theorem signWithSources_forget (sk : Seeded.SecretKey) (message : Message) (state : SourcedState) :
    (fun result => (result.1, result.2.2)) <$> signWithSources sk message state =
      (simulateQ romImpl (Randomized.sign sk message)).run state.2 := by
  have h := congrArg (Functor.map (fun result : Option Signature × DisclosureState =>
    (result.1, result.2.2))) (signWithSources_forget_sources sk message state)
  simpa only [Functor.map_map, Function.comp_def, forgetSources, signWithDisclosures_forget] using h

theorem finishSignBody_support_randomness (sk : Seeded.SecretKey) (randomness : Randomness)
    (digest : MessageDigest) (cache after : QueryCache HashSpec) (signature : Signature)
    (hresult : (some signature, after) ∈ support
      ((simulateQ randomOracle (finishSignBody sk randomness digest)).run cache)) :
    signature.randomness = randomness := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn after
  have h := (replay_hash_support _ _ _ _ hresult f hf).2
  rw [finishSignBody, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind] at h
  split at h
  · simp only [evalWithAnswerFn_pure, Option.some.injEq] at h
    subst signature
    rfl
  · simp at h

/-- The label is attached to the digest actually used by signing, including assembly failure.
The supported result always retains old cached answers and every old source record. -/
theorem signWithSources_preserves (sk : Seeded.SecretKey) (message : Message) (state : SourcedState)
    (hrecords : SourcesConsistent sk state.2 state.1) (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSources sk message state)) :
    state.2 ≤ result.2.2 ∧ state.1.Sublist result.2.1 ∧ SourcesConsistent sk result.2.2 result.2.1 := by
  rw [signWithSources, mem_support_bind_iff] at hresult
  obtain ⟨⟨loop, middle⟩, hloop, hresult⟩ := hresult
  obtain ⟨hloopLe, hland⟩ := randomizedDigest_support sk message _ _ _ _ hloop
  cases loop with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact ⟨hloopLe, List.Sublist.refl _, sourcesConsistent_mono sk _ _ hloopLe _ hrecords⟩
  | some randomness =>
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨digest, beforeBody⟩, hdigest, hresult⟩ := hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨response, afterBody⟩, hbody, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    obtain ⟨hdigestLe, hsource⟩ := messageDigest_support_source sk message randomness middle
      (digest, beforeBody) hdigest
    have hbodyLe := hash_support_cache_le _ _ _ _ hbody
    have hwhole := hloopLe.trans (hdigestLe.trans hbodyLe)
    refine ⟨hwhole, List.sublist_cons_self _ _, ?_⟩
    intro record hrecord
    rcases List.mem_cons.mp hrecord with rfl | hrecord
    · refine ⟨hsource.mono sk beforeBody afterBody hbodyLe _ _, ?_, ?_⟩
      · obtain ⟨first, hfirst, hlanding⟩ := hland randomness rfl
        obtain ⟨sourceFirst, second, hsfirst, _, hd⟩ := hsource
        have heq := hdigestLe hfirst
        change beforeBody (candidateInput sk (message, randomness) 0) = some first at heq
        have heq' : sourceFirst = first := Option.some.inj (hsfirst.symm.trans heq)
        cases heq'
        change digest = truncateMessageDigest first second at hd
        change Landed sk.parameter (digestIndex digest)
        simpa only [hd, digestIndex_truncate] using hlanding
      · intro signature hsignature
        change response = some signature at hsignature
        subst response
        exact finishSignBody_support_randomness sk randomness digest beforeBody afterBody signature hbody
    · exact sourcesConsistent_mono sk state.2 afterBody hwhole state.1 hrecords record hrecord

theorem sources_same_pair_same_digest (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (records : List SourceRecord) (hrecords : SourcesConsistent sk cache records)
    (left right : SourceRecord) (hleft : left ∈ records) (hright : right ∈ records)
    (hsource : left.source = right.source) : left.digest = right.digest := by
  apply CachedSource.unique sk cache left.source left.digest right.digest
  · exact (hrecords left hleft).1
  · simpa only [hsource] using (hrecords right hright).1

/-- Reusing a previously recorded message/randomizer pair cannot add a new digest view,
even if the earlier record was an exhausted signing attempt. -/
theorem sourcedPrior_duplicate (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (record : SourceRecord) (records : List SourceRecord)
    (hrecords : SourcesConsistent sk cache (record :: records))
    (hsource : ∃ previous ∈ records, previous.source = record.source) :
    sourcedPrior (record :: records) = sourcedPrior records := by
  obtain ⟨previous, hprevious, heq⟩ := hsource
  have hdigest := sources_same_pair_same_digest sk cache (record :: records) hrecords previous record
    (List.mem_cons_of_mem _ hprevious) (List.mem_cons_self) heq
  rw [sourcedPrior_cons]
  apply Finset.insert_eq_of_mem
  rw [sourcedPrior, List.mem_toFinset]
  exact List.mem_map.mpr ⟨previous, hprevious, congrArg localDigestView hdigest⟩

theorem signWithSources_record_shape (sk : Seeded.SecretKey) (message : Message) (state : SourcedState)
    (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSources sk message state)) :
    (result.1 = none ∧ result.2.1 = state.1) ∨
      ∃ randomness digest, result.2.1 = ⟨(message, randomness), digest, result.1⟩ :: state.1 := by
  rw [signWithSources, mem_support_bind_iff] at hresult
  obtain ⟨⟨loop, middle⟩, _, hresult⟩ := hresult
  cases loop with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact Or.inl ⟨rfl, rfl⟩
  | some randomness =>
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨digest, beforeBody⟩, _, hresult⟩ := hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨response, afterBody⟩, _, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact Or.inr ⟨randomness, digest, rfl⟩

/-- Only actual successful responses enter this relation with the signing transcript. -/
def SourcesLogged (records : List SourceRecord) (log : QueryLog SigningSpec) : Prop :=
  ∀ record ∈ records, ∀ signature, record.response = some signature →
    ⟨record.source.1, some signature⟩ ∈ log

theorem signWithSources_logged (sk : Seeded.SecretKey) (message : Message) (state : SourcedState)
    (log : QueryLog SigningSpec) (hlogged : SourcesLogged state.1 log)
    (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSources sk message state)) :
    SourcesLogged result.2.1 (⟨message, result.1⟩ :: log) := by
  rcases signWithSources_record_shape sk message state result hresult with
    ⟨_, hrecords⟩ | ⟨randomness, digest, hrecords⟩
  · rw [hrecords]
    intro record hrecord signature hsignature
    exact List.mem_cons_of_mem _ (hlogged record hrecord signature hsignature)
  · rw [hrecords]
    intro record hrecord signature hsignature
    rcases List.mem_cons.mp hrecord with rfl | hrecord
    · change result.1 = some signature at hsignature
      simp only [hsignature, List.mem_cons_self]
    · exact List.mem_cons_of_mem _ (hlogged record hrecord signature hsignature)

def HasSuccessfulSource (records : List SourceRecord) (source : DigestCandidate) : Prop :=
  ∃ record ∈ records, record.source = source ∧ record.response.isSome

def successfulViews (records : List SourceRecord) : Finset KeptDigestView :=
  ((records.toFinset.filter (fun record => record.response.isSome)).image
    (fun record => localDigestView record.digest))

def sourceExcludedViews (source : DigestCandidate) (records : List SourceRecord) : Finset KeptDigestView :=
  ((records.toFinset.filter (fun record => record.source ≠ source ∧ record.response.isSome)).image
    (fun record => localDigestView record.digest))

theorem sourceExcludedViews_subset (source : DigestCandidate) (records : List SourceRecord) :
    sourceExcludedViews source records ⊆ successfulViews records := by
  apply Finset.image_subset_image
  intro record hrecord
  obtain ⟨hmem, _, hsome⟩ := Finset.mem_filter.mp hrecord
  exact Finset.mem_filter.mpr ⟨hmem, hsome⟩

theorem successfulViews_subset_sourcedPrior (records : List SourceRecord) :
    successfulViews records ⊆ sourcedPrior records := by
  intro view hview
  obtain ⟨record, hrecord, rfl⟩ := Finset.mem_image.mp hview
  rw [sourcedPrior, List.mem_toFinset]
  exact List.mem_map.mpr ⟨record, List.mem_toFinset.mp (Finset.mem_filter.mp hrecord).1, rfl⟩

theorem sourceExcludedViews_eq_of_no_success (source : DigestCandidate) (records : List SourceRecord)
    (hnone : ¬HasSuccessfulSource records source) : sourceExcludedViews source records = successfulViews records := by
  apply Finset.Subset.antisymm (sourceExcludedViews_subset source records)
  apply Finset.image_subset_image
  intro record hrecord
  obtain ⟨hmem, hsome⟩ := Finset.mem_filter.mp hrecord
  refine Finset.mem_filter.mpr ⟨hmem, ?_, hsome⟩
  intro heq
  exact hnone ⟨record, List.mem_toFinset.mp hmem, heq, hsome⟩

/-- Inserting a successful response from the target itself adds no eligible disclosure. -/
theorem sourceExcludedViews_same_source (source : DigestCandidate) (record : SourceRecord)
    (records : List SourceRecord) (hsource : record.source = source) :
    sourceExcludedViews source (record :: records) = sourceExcludedViews source records := by
  simp only [sourceExcludedViews, List.toFinset_cons, Finset.filter_insert,
    hsource, ne_eq, not_true_eq_false, false_and, if_false]

theorem successfulSource_logged (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (records : List SourceRecord) (hrecords : SourcesConsistent sk cache records)
    (log : QueryLog SigningSpec) (hlogged : SourcesLogged records log)
    (source : DigestCandidate) (hsource : HasSuccessfulSource records source) :
    ∃ signature, ⟨source.1, some signature⟩ ∈ log ∧ signature.randomness = source.2 := by
  obtain ⟨record, hrecord, heq, hsome⟩ := hsource
  cases hresponse : record.response with
  | none => simp [hresponse] at hsome
  | some signature =>
    exact ⟨signature, heq ▸ hlogged record hrecord signature hresponse,
      heq ▸ (hrecords record hrecord).2.2 signature hresponse⟩

end LeanSphincs.Lifetime
