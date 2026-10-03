import LeanSphincs.LifetimeDisclosure

/-! The actual grinding prefix retains its random-oracle cache, and records every accepted
digest in the proof-side disclosure set before any later WOTS computation. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

theorem digestInput_message_injective (parameter : PublicParameter) (root : Digest)
    {left right : Message} (rho sigma : Randomness) (i j : Fin 2)
    (h : Security.digestInput parameter root left rho i =
      Security.digestInput parameter root right sigma j) : left = right := by
  simp only [Security.digestInput, tweakableHashInput, messageDigestPayload, ← List.append_assoc] at h
  obtain ⟨_, hmessage⟩ := List.append_inj' h (by simp [bytesLE_length])
  exact bytesLE_injective hmessage

theorem digestInput_randomness_injective (parameter : PublicParameter) (root : Digest)
    (message : Message) (call : Fin 2) {rho sigma : Randomness}
    (h : Security.digestInput parameter root message rho call =
      Security.digestInput parameter root message sigma call) : rho = sigma := by
  simp only [Security.digestInput, tweakableHashInput, messageDigestPayload] at h
  have hpayload := List.append_cancel_left h
  exact bytesLE_injective (List.append_cancel_right (List.append_cancel_right hpayload))

variable [Params]

def GlobalReuseInvariant (sk : Seeded.SecretKey) (prior : Finset KeptDigestView)
    (cache : QueryCache HashSpec) : Prop := ∀ message, ReuseInvariant sk message prior cache

theorem reuseInvariant_other_message_query (sk : Seeded.SecretKey)
    (message queried : Message) (hneq : message ≠ queried)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : ReuseInvariant sk message prior cache) (randomness : Randomness)
    (call : Fin 2) (answer : HashOutput) :
    ReuseInvariant sk message prior
      (cache.cacheQuery (Security.digestInput sk.parameter sk.root queried randomness call) answer) := by
  have hagree (rho : Randomness) (i : Fin 2) :
      (cache.cacheQuery (Security.digestInput sk.parameter sk.root queried randomness call) answer)
        (Security.digestInput sk.parameter sk.root message rho i) =
          cache (Security.digestInput sk.parameter sk.root message rho i) :=
    QueryCache.cacheQuery_of_ne cache answer (fun h => hneq
      (digestInput_message_injective sk.parameter sk.root rho randomness i call h))
  constructor
  · intro rho first hfirst hland
    rw [hagree rho 0] at hfirst
    obtain ⟨second, hsecond, hprior⟩ := hcache.accepted rho first hfirst hland
    exact ⟨second, (hagree rho 1).trans hsecond, hprior⟩
  · intro rho hfirst
    rw [hagree rho 0] at hfirst
    exact (hagree rho 1).trans (hcache.freshSecond rho hfirst)

theorem globalReuseInvariant_rejected_query (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (randomness : Randomness)
    (first : HashOutput) (hreject : ¬Landed sk.parameter (blockIndex first)) :
    GlobalReuseInvariant sk prior (cache.cacheQuery (msgInput sk message randomness) first) := by
  intro other
  by_cases heq : other = message
  · subst other
    exact reuseInvariant_rejected_cacheQuery sk message prior cache (hcache message) randomness first hreject
  · exact reuseInvariant_other_message_query sk other message heq prior cache (hcache other)
      randomness 0 first

def completedDigestCache (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (first second : HashOutput) : QueryCache HashSpec :=
  (cache.cacheQuery (msgInput sk message randomness) first).cacheQuery
    (Security.digestInput sk.parameter sk.root message randomness 1) second

omit [Params] in
theorem completedDigestCache_first (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (first second : HashOutput) :
    completedDigestCache sk message randomness cache first second (msgInput sk message randomness) =
      some first := by
  rw [completedDigestCache, QueryCache.cacheQuery_of_ne (cache.cacheQuery (msgInput sk message randomness) first) second
    (Ne.symm (digestInput_calls_ne sk.parameter sk.root message randomness randomness)),
    QueryCache.cacheQuery_self]

omit [Params] in
theorem completedDigestCache_second (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (first second : HashOutput) :
    completedDigestCache sk message randomness cache first second
      (Security.digestInput sk.parameter sk.root message randomness 1) = some second :=
  QueryCache.cacheQuery_self _ _ _

omit [Params] in
theorem completedDigestCache_other_randomness (sk : Seeded.SecretKey) (message : Message)
    (randomness rho : Randomness) (hneq : rho ≠ randomness)
    (cache : QueryCache HashSpec) (first second : HashOutput) (call : Fin 2) :
    completedDigestCache sk message randomness cache first second
      (Security.digestInput sk.parameter sk.root message rho call) =
        cache (Security.digestInput sk.parameter sk.root message rho call) := by
  have hcall : call = 0 ∨ call = 1 := by fin_cases call <;> simp
  rcases hcall with rfl | rfl
  · rw [completedDigestCache, QueryCache.cacheQuery_of_ne (cache.cacheQuery (msgInput sk message randomness) first) second
      (Ne.symm (digestInput_calls_ne sk.parameter sk.root message randomness rho)),
      QueryCache.cacheQuery_of_ne cache first
        (fun h => hneq (digestInput_randomness_injective sk.parameter sk.root message 0 h))]
  · rw [completedDigestCache, QueryCache.cacheQuery_of_ne (cache.cacheQuery (msgInput sk message randomness) first) second
      (fun h => hneq (digestInput_randomness_injective sk.parameter sk.root message 1 h)),
      QueryCache.cacheQuery_of_ne cache first
        (digestInput_calls_ne sk.parameter sk.root message rho randomness)]

/-- Completing both blocks and recording the digest restores the reuse invariant even if a
later WOTS search fails and the signing oracle returns no signature. -/
theorem reuseInvariant_completed_digest (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : ReuseInvariant sk message prior cache) (randomness : Randomness)
    (first second : HashOutput) :
    ReuseInvariant sk message (insert (localDigestView (truncateMessageDigest first second)) prior)
      (completedDigestCache sk message randomness cache first second) := by
  constructor
  · intro rho other hfirst hland
    by_cases heq : rho = randomness
    · subst rho
      rw [completedDigestCache_first] at hfirst
      cases Option.some.inj hfirst
      exact ⟨second, completedDigestCache_second _ _ _ _ _ _, Finset.mem_insert_self _ _⟩
    · rw [completedDigestCache_other_randomness sk message randomness rho heq cache first second 0] at hfirst
      obtain ⟨last, hlast, hprior⟩ := hcache.accepted rho other hfirst hland
      exact ⟨last, (completedDigestCache_other_randomness sk message randomness rho heq cache first second 1).trans hlast,
        Finset.mem_insert_of_mem hprior⟩
  · intro rho hfirst
    have heq : rho ≠ randomness := by
      intro h
      subst rho
      rw [completedDigestCache_first] at hfirst
      contradiction
    rw [completedDigestCache_other_randomness sk message randomness rho heq cache first second 0] at hfirst
    exact (completedDigestCache_other_randomness sk message randomness rho heq cache first second 1).trans
      (hcache.freshSecond rho hfirst)

theorem globalReuseInvariant_completed_digest (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (randomness : Randomness)
    (first second : HashOutput) :
    GlobalReuseInvariant sk (insert (localDigestView (truncateMessageDigest first second)) prior)
      (completedDigestCache sk message randomness cache first second) := by
  intro other
  by_cases heq : other = message
  · subst other
    exact reuseInvariant_completed_digest sk message prior cache (hcache message) randomness first second
  · apply ReuseInvariant.mono_prior sk other
      (completedDigestCache sk message randomness cache first second) _ (Finset.subset_insert _ _)
    exact reuseInvariant_other_message_query sk other message heq prior _
      (reuseInvariant_other_message_query sk other message heq prior cache (hcache other) randomness 0 first)
      randomness 1 second

noncomputable def grindDigestState (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) : ProbComp (Option MessageDigest × QueryCache HashSpec) := do
  let result ← (simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache
  match result.1 with
  | none => pure (none, result.2)
  | some randomness =>
    (fun r => (some r.1, r.2)) <$> (simulateQ randomOracle
      (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run result.2

theorem grindDigestState_fst (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) :
    Prod.fst <$> grindDigestState sk message n cache = grindDigest sk message n cache := by
  rw [grindDigestState, grindDigest, map_bind]
  apply bind_congr
  rintro ⟨result, nextCache⟩
  cases result <;> simp only [map_pure, Functor.map_map, Function.comp_def]

theorem grindDigestState_zero (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    grindDigestState sk message 0 cache = pure (none, cache) := by
  simp [grindDigestState, Randomized.signDigestLoop]

theorem grindDigestState_succ (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) :
    grindDigestState sk message (n + 1) cache = (do
      let randomness ← ($ᵗ Randomness : ProbComp Randomness)
      let answer ← (randomOracle (spec := HashSpec) (msgInput sk message randomness)).run cache
      if Landed sk.parameter (blockIndex answer.1) then
        (fun r => (some r.1, r.2)) <$> (simulateQ randomOracle
          (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run answer.2
      else grindDigestState sk message n answer.2) := by
  rw [grindDigestState, run_randomizedDigest_succ]
  simp only [bind_assoc]
  apply bind_congr
  intro randomness
  apply bind_congr
  intro answer
  split <;> simp [grindDigestState]

/-- Every accepted digest is entered into the proof-side set immediately. This invariant is
global across messages, so future requests may be selected adaptively or repeated. -/
theorem grindDigestState_preserves_global (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n : Nat) (prior : Finset KeptDigestView) (cache : QueryCache HashSpec),
      GlobalReuseInvariant sk prior cache →
      ∀ result ∈ support (grindDigestState sk message n cache),
        GlobalReuseInvariant sk (disclosedViewsAfter prior result.1) result.2 := by
  intro n
  induction n with
  | zero =>
    intro prior cache hcache result hresult
    rw [grindDigestState_zero, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact hcache
  | succ n ih =>
    intro prior cache hcache result hresult
    rw [grindDigestState_succ, mem_support_bind_iff] at hresult
    obtain ⟨randomness, _, hresult⟩ := hresult
    cases hc : cache (msgInput sk message randomness) with
    | some first =>
      rw [cached_run _ _ _ hc, pure_bind] at hresult
      by_cases hland : Landed sk.parameter (blockIndex first)
      · rw [if_pos hland] at hresult
        obtain ⟨second, hsecond, hprior⟩ := (hcache message).accepted randomness first hc hland
        rw [run_messageDigest_cached_both sk.parameter sk.root message randomness cache first second hc hsecond,
          map_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        simpa only [Function.comp_def, disclosedViewsAfter, Finset.insert_eq_of_mem hprior] using hcache
      · rw [if_neg hland] at hresult
        exact ih prior cache hcache result hresult
    | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp, bind_assoc] at hresult
      simp only [Function.comp_def, pure_bind, mem_support_bind_iff] at hresult
      obtain ⟨first, _, hresult⟩ := hresult
      by_cases hland : Landed sk.parameter (blockIndex first)
      · rw [if_pos hland] at hresult
        have hsecond := (QueryCache.cacheQuery_of_ne cache first
          (digestInput_calls_ne sk.parameter sk.root message randomness randomness)).trans
            ((hcache message).freshSecond randomness hc)
        rw [Security.run_messageDigest_cached_first sk.parameter sk.root message randomness _ first
          (QueryCache.cacheQuery_self _ _ _) hsecond] at hresult
        simp only [bind_pure_comp, Functor.map_map, support_map] at hresult
        obtain ⟨second, _, hresult⟩ := hresult
        subst result
        exact globalReuseInvariant_completed_digest sk message prior cache hcache randomness first second
      · rw [if_neg hland] at hresult
        exact ih prior _ (globalReuseInvariant_rejected_query sk message prior cache hcache
          randomness first hland) result hresult

abbrev DisclosureState := Finset KeptDigestView × QueryCache HashSpec

noncomputable def grindDisclosureStep (sk : Seeded.SecretKey)
    (request : DisclosureState → Message) (attempts : Nat) (state : DisclosureState) :
    ProbComp DisclosureState :=
  (fun result => (disclosedViewsAfter state.1 result.1, result.2)) <$>
    grindDigestState sk (request state) attempts state.2

theorem grindDisclosureStep_preserves (sk : Seeded.SecretKey) (request : DisclosureState → Message)
    (attempts : Nat) (state : DisclosureState) (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (next : DisclosureState) (hnext : next ∈ support (grindDisclosureStep sk request attempts state)) :
    GlobalReuseInvariant sk next.1 next.2 := by
  rw [grindDisclosureStep, support_map] at hnext
  obtain ⟨result, hresult, rfl⟩ := hnext
  exact grindDigestState_preserves_global sk (request state) attempts state.1 state.2 hinvariant result hresult

theorem grindDisclosureStep_le_uniform (sk : Seeded.SecretKey) (request : DisclosureState → Message)
    (attempts : Nat) (state : DisclosureState) (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (event : Finset KeptDigestView → Prop) [DecidablePred event] (hmono : Monotone event) :
    Pr[fun next => event next.1 | grindDisclosureStep sk request attempts state] ≤
      Pr[fun view => event (insert view state.1) | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  rw [grindDisclosureStep, probEvent_map]
  change Pr[(fun result => event (disclosedViewsAfter state.1 result)) ∘ Prod.fst |
    grindDigestState sk (request state) attempts state.2] ≤ _
  rw [← probEvent_map, grindDigestState_fst]
  exact grindDigest_disclosure_step_le_uniform sk (request state) attempts state.1 state.2
    (hinvariant (request state)) event hmono

/-- Actual grinding for N adaptively chosen requests is dominated by N independent uniform
insertions. The proof-side record includes every accepted digest, whether or not later WOTS
work succeeds. No adversarial oracle interleaving is included in this process. -/
theorem grinding_disclosures_le_uniform (sk : Seeded.SecretKey) (request : DisclosureState → Message)
    (attempts n : Nat) (state : DisclosureState) (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (event : Finset KeptDigestView → Prop) [DecidablePred event] (hmono : Monotone event) :
    Pr[event | disclosureProcess (grindDisclosureStep sk request attempts) Prod.fst n state] ≤
      Pr[event | uniformDisclosureSet n state.1] :=
  disclosureProcess_le_uniform (grindDisclosureStep sk request attempts) Prod.fst
    (fun state => GlobalReuseInvariant sk state.1 state.2)
    (grindDisclosureStep_preserves sk request attempts)
    (grindDisclosureStep_le_uniform sk request attempts) n state hinvariant event hmono

theorem globalReuseInvariant_after_keygen (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hsupport : result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅)) :
    GlobalReuseInvariant result.1.2 ∅ result.2 := by
  intro message
  exact reuseInvariant_of_fresh result.1.2 message ∅ result.2
    (keygen_message_inputs_fresh seed result hsupport message)

theorem grinding_disclosures_after_keygen_le_uniform (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hsupport : result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅))
    (request : DisclosureState → Message) (attempts n : Nat)
    (event : Finset KeptDigestView → Prop) [DecidablePred event] (hmono : Monotone event) :
    Pr[event | disclosureProcess (grindDisclosureStep result.1.2 request attempts) Prod.fst n (∅, result.2)] ≤
      Pr[event | uniformDisclosureSet n ∅] :=
  grinding_disclosures_le_uniform result.1.2 request attempts n (∅, result.2)
    (globalReuseInvariant_after_keygen seed result hsupport) event hmono

end LeanSphincs.Lifetime
