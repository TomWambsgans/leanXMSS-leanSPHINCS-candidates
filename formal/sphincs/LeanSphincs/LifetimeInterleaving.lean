import LeanSphincs.LifetimeSigningDisclosure

/-!
The reuse invariant under adversarial hash interleavings. The exceptions below concern the
proof-side cache discipline, not cryptographic failure: a first-block query lands with the
subtree probability, and querying a second block before its first breaks the discipline with
probability one. Cached prefixes must therefore retain their actual conditional digest law.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

variable [Params]

/-- An accepted first block whose final ten digest bits have not yet been sampled. -/
def PendingAccepted (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) : Prop :=
  ∃ first, cache (msgInput sk message randomness) = some first ∧
    Landed sk.parameter (blockIndex first) ∧
    cache (Security.digestInput sk.parameter sk.root message randomness 1) = none

/-- A second block chosen before the first block: the last FORS selector is already fixed. -/
def OrphanSecond (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) : Prop :=
  cache (msgInput sk message randomness) = none ∧
    ∃ second, cache (Security.digestInput sk.parameter sk.root message randomness 1) = some second

/-- A complete accepted digest which has not been entered in the honest disclosure record. -/
def UnrecordedAccepted (sk : Seeded.SecretKey) (message : Message) (randomness : Randomness)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec) : Prop :=
  ∃ first second, cache (msgInput sk message randomness) = some first ∧
    cache (Security.digestInput sk.parameter sk.root message randomness 1) = some second ∧
    Landed sk.parameter (blockIndex first) ∧
    localDigestView (truncateMessageDigest first second) ∉ prior

theorem globalReuseInvariant_iff_no_defects (sk : Seeded.SecretKey)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec) :
    GlobalReuseInvariant sk prior cache ↔ ∀ message randomness,
      ¬PendingAccepted sk message randomness cache ∧
      ¬OrphanSecond sk message randomness cache ∧
      ¬UnrecordedAccepted sk message randomness prior cache := by
  constructor
  · intro h message randomness
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨first, hfirst, hland, hsecond⟩
      obtain ⟨second, hcached, _⟩ := (h message).accepted randomness first hfirst hland
      rw [hsecond] at hcached
      contradiction
    · rintro ⟨hfirst, second, hsecond⟩
      rw [(h message).freshSecond randomness hfirst] at hsecond
      contradiction
    · rintro ⟨first, second, hfirst, hsecond, hland, hmissing⟩
      obtain ⟨other, hother, hprior⟩ := (h message).accepted randomness first hfirst hland
      rw [hsecond] at hother
      cases Option.some.inj hother
      exact hmissing hprior
  · intro h message
    constructor
    · intro randomness first hfirst hland
      cases hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) with
      | none => exact False.elim ((h message randomness).1 ⟨first, hfirst, hland, hsecond⟩)
      | some second =>
        refine ⟨second, rfl, ?_⟩
        by_contra hmissing
        exact (h message randomness).2.2 ⟨first, second, hfirst, hsecond, hland, hmissing⟩
    · intro randomness hfirst
      cases hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) with
      | none => rfl
      | some second => exact False.elim ((h message randomness).2.1 ⟨hfirst, second, hsecond⟩)

theorem globalReuseInvariant_unrelated_query (sk : Seeded.SecretKey)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (input : HashInput) (answer : HashOutput)
    (hunrelated : ∀ message randomness call,
      Security.digestInput sk.parameter sk.root message randomness call ≠ input) :
    GlobalReuseInvariant sk prior (cache.cacheQuery input answer) :=
  globalReuseInvariant_of_message_cache_eq sk prior cache _ hcache
    (fun message randomness call => QueryCache.cacheQuery_of_ne cache answer
      (hunrelated message randomness call))

/-- Under the invariant a fresh first block has no second block, so landing is precisely
the event that leaves an accepted but incomplete adversarial candidate. -/
theorem globalReuseInvariant_fresh_first_iff (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (randomness : Randomness)
    (hfresh : cache (msgInput sk message randomness) = none) (first : HashOutput) :
    GlobalReuseInvariant sk prior (cache.cacheQuery (msgInput sk message randomness) first) ↔
      ¬Landed sk.parameter (blockIndex first) := by
  constructor
  · intro h hland
    obtain ⟨second, hsecond, _⟩ := (h message).accepted randomness first
      (QueryCache.cacheQuery_self _ _ _) hland
    rw [QueryCache.cacheQuery_of_ne cache first
      (digestInput_calls_ne sk.parameter sk.root message randomness randomness),
      (hcache message).freshSecond randomness hfresh] at hsecond
    contradiction
  · exact globalReuseInvariant_rejected_query sk message prior cache hcache randomness first

theorem reuseInvariant_rejected_second_query (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : ReuseInvariant sk message prior cache) (randomness : Randomness)
    (first second : HashOutput) (hfirst : cache (msgInput sk message randomness) = some first)
    (hreject : ¬Landed sk.parameter (blockIndex first)) :
    ReuseInvariant sk message prior
      (cache.cacheQuery (Security.digestInput sk.parameter sk.root message randomness 1) second) := by
  have hfirst_eq (rho : Randomness) :
      (cache.cacheQuery (Security.digestInput sk.parameter sk.root message randomness 1) second)
        (msgInput sk message rho) = cache (msgInput sk message rho) :=
    QueryCache.cacheQuery_of_ne cache second
      (Ne.symm (digestInput_calls_ne sk.parameter sk.root message randomness rho))
  constructor
  · intro rho value hvalue hland
    rw [hfirst_eq] at hvalue
    have hneq : rho ≠ randomness := by
      intro h
      subst rho
      rw [hfirst] at hvalue
      cases Option.some.inj hvalue
      exact hreject hland
    obtain ⟨last, hlast, hprior⟩ := hcache.accepted rho value hvalue hland
    refine ⟨last, ?_, hprior⟩
    exact (QueryCache.cacheQuery_of_ne cache second (fun h => hneq
      (digestInput_randomness_injective sk.parameter sk.root message 1 h))).trans hlast
  · intro rho hnone
    rw [hfirst_eq] at hnone
    have hneq : rho ≠ randomness := by
      intro h
      subst rho
      rw [hfirst] at hnone
      contradiction
    exact (QueryCache.cacheQuery_of_ne cache second (fun h => hneq
      (digestInput_randomness_injective sk.parameter sk.root message 1 h))).trans
        (hcache.freshSecond rho hnone)

/-- A fresh second-block query is safe for this invariant exactly when its first block
already exists. An accepted first cannot occur here under a good prefix. -/
theorem globalReuseInvariant_fresh_second_iff (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (randomness : Randomness)
    (hfresh : cache (Security.digestInput sk.parameter sk.root message randomness 1) = none)
    (second : HashOutput) :
    GlobalReuseInvariant sk prior
      (cache.cacheQuery (Security.digestInput sk.parameter sk.root message randomness 1) second) ↔
      cache (msgInput sk message randomness) ≠ none := by
  constructor
  · intro h hnone
    have hfirst := (QueryCache.cacheQuery_of_ne cache second
      (Ne.symm (digestInput_calls_ne sk.parameter sk.root message randomness randomness))).trans hnone
    have hsecond := (h message).freshSecond randomness hfirst
    rw [QueryCache.cacheQuery_self] at hsecond
    contradiction
  · intro hnonempty
    cases hfirst : cache (msgInput sk message randomness) with
    | none => exact False.elim (hnonempty hfirst)
    | some first =>
      have hreject : ¬Landed sk.parameter (blockIndex first) := by
        intro hland
        obtain ⟨last, hlast, _⟩ := (hcache message).accepted randomness first hfirst hland
        rw [hfresh] at hlast
        contradiction
      intro other
      by_cases heq : other = message
      · subst other
        exact reuseInvariant_rejected_second_query sk message prior cache (hcache message)
          randomness first second hfirst hreject
      · exact reuseInvariant_other_message_query sk other message heq prior cache (hcache other)
          randomness 1 second

/-- A single fresh query can break a good cache prefix in exactly these two ways. -/
def ReuseBreakingAnswer (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (input : HashInput) (answer : HashOutput) : Prop :=
  cache input = none ∧
    ((∃ message randomness, input = msgInput sk message randomness ∧
      Landed sk.parameter (blockIndex answer)) ∨
    (∃ message randomness,
      input = Security.digestInput sk.parameter sk.root message randomness 1 ∧
      cache (msgInput sk message randomness) = none))

theorem globalReuseInvariant_fresh_query_iff (sk : Seeded.SecretKey)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (input : HashInput)
    (hfresh : cache input = none) (answer : HashOutput) :
    GlobalReuseInvariant sk prior (cache.cacheQuery input answer) ↔
      ¬ReuseBreakingAnswer sk cache input answer := by
  classical
  constructor
  · intro h ⟨_, hbad⟩
    rcases hbad with ⟨message, randomness, rfl, hland⟩ | ⟨message, randomness, rfl, hnone⟩
    · exact (globalReuseInvariant_fresh_first_iff sk message prior cache hcache randomness
        hfresh answer).1 h hland
    · exact (globalReuseInvariant_fresh_second_iff sk message prior cache hcache randomness
        hfresh answer).1 h hnone
  · intro hgood
    by_cases hfirst : ∃ message randomness, input = msgInput sk message randomness
    · obtain ⟨message, randomness, rfl⟩ := hfirst
      apply (globalReuseInvariant_fresh_first_iff sk message prior cache hcache randomness
        hfresh answer).2
      intro hland
      exact hgood ⟨hfresh, Or.inl ⟨message, randomness, rfl, hland⟩⟩
    · by_cases hsecond : ∃ message randomness,
          input = Security.digestInput sk.parameter sk.root message randomness 1
      · obtain ⟨message, randomness, rfl⟩ := hsecond
        apply (globalReuseInvariant_fresh_second_iff sk message prior cache hcache randomness
          hfresh answer).2
        intro hnone
        exact hgood ⟨hfresh, Or.inr ⟨message, randomness, rfl, hnone⟩⟩
      · apply globalReuseInvariant_unrelated_query sk prior cache hcache input answer
        intro message randomness call heq
        fin_cases call
        · exact hfirst ⟨message, randomness, heq.symm⟩
        · exact hsecond ⟨message, randomness, heq.symm⟩

/-- Exact good-prefix characterization for a supported execution of the actual lazy oracle.
In particular, a cached query cannot create a new defect. -/
theorem query_preserves_globalReuse_iff (sk : Seeded.SecretKey)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (input : HashInput)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((randomOracle (spec := HashSpec) input).run cache)) :
    GlobalReuseInvariant sk prior result.2 ↔
      ¬ReuseBreakingAnswer sk cache input result.1 := by
  cases hc : cache input with
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hresult
    obtain ⟨answer, _, rfl⟩ := hresult
    exact globalReuseInvariant_fresh_query_iff sk prior cache hcache input hc answer
  | some answer =>
    rw [cached_run _ _ _ hc, support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact ⟨fun _ hbad => by have hnone := hbad.1; rw [hc] at hnone; contradiction,
      fun _ => hcache⟩

theorem probEvent_query_breaks_globalReuse (sk : Seeded.SecretKey)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (input : HashInput) :
    Pr[fun result => ¬GlobalReuseInvariant sk prior result.2 |
      (randomOracle (spec := HashSpec) input).run cache] =
    Pr[fun result => ReuseBreakingAnswer sk cache input result.1 |
      (randomOracle (spec := HashSpec) input).run cache] := by
  classical
  apply (probEvent_congr' ?_ rfl)
  intro result hresult
  rw [query_preserves_globalReuse_iff sk prior cache hcache input result hresult, not_not]

theorem probEvent_fresh_first_breaks_globalReuse (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (randomness : Randomness)
    (hfresh : cache (msgInput sk message randomness) = none) :
    Pr[fun result => ¬GlobalReuseInvariant sk prior result.2 |
      (randomOracle (spec := HashSpec) (msgInput sk message randomness)).run cache] =
      ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ := by
  classical
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, probEvent_map]
  have heq : (fun first : HashOutput =>
      ¬GlobalReuseInvariant sk prior (cache.cacheQuery (msgInput sk message randomness) first)) =
      (fun first => Landed sk.parameter (blockIndex first)) := by
    funext first
    exact propext (by rw [globalReuseInvariant_fresh_first_iff sk message prior cache hcache
      randomness hfresh first, not_not])
  change Pr[fun first => ¬GlobalReuseInvariant sk prior
    (cache.cacheQuery (msgInput sk message randomness) first) | ($ᵗ HashOutput : ProbComp HashOutput)] = _
  rw [heq, fresh_landing_probability_inv]

theorem probEvent_fresh_second_breaks_globalReuse (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : GlobalReuseInvariant sk prior cache) (randomness : Randomness)
    (hfresh : cache (Security.digestInput sk.parameter sk.root message randomness 1) = none) :
    Pr[fun result => ¬GlobalReuseInvariant sk prior result.2 |
      (randomOracle (spec := HashSpec)
        (Security.digestInput sk.parameter sk.root message randomness 1)).run cache] =
      if cache (msgInput sk message randomness) = none then 1 else 0 := by
  classical
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, probEvent_map]
  change Pr[fun second => ¬GlobalReuseInvariant sk prior
    (cache.cacheQuery (Security.digestInput sk.parameter sk.root message randomness 1) second) |
    ($ᵗ HashOutput : ProbComp HashOutput)] = _
  have heq : (fun second : HashOutput => ¬GlobalReuseInvariant sk prior
      (cache.cacheQuery (Security.digestInput sk.parameter sk.root message randomness 1) second)) =
      (fun _ => cache (msgInput sk message randomness) = none) := by
    funext second
    exact propext (by rw [globalReuseInvariant_fresh_second_iff sk message prior cache hcache
      randomness hfresh second, not_not])
  rw [heq]
  by_cases hfirst : cache (msgInput sk message randomness) = none <;> simp [hfirst]

/-- The left request signs a message; the right request is a raw adversarial hash call. -/
abbrev InterleavingRequest := Message ⊕ HashInput

noncomputable def auditedInterleavingStep (sk : Seeded.SecretKey)
    (request : InterleavingRequest) (state : DisclosureState) : ProbComp (Bool × DisclosureState) := by
  classical
  exact match request with
    | .inl message => (fun result => (true, result.2)) <$> signWithDisclosures sk message state
    | .inr input => (fun result =>
        (decide (¬ReuseBreakingAnswer sk state.2 input result.1), (state.1, result.2))) <$>
        (randomOracle (spec := HashSpec) input).run state.2

theorem auditedInterleavingStep_preserves (sk : Seeded.SecretKey)
    (request : InterleavingRequest) (state : DisclosureState)
    (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (result : Bool × DisclosureState) (hresult : result ∈ support (auditedInterleavingStep sk request state))
    (hgood : result.1 = true) : GlobalReuseInvariant sk result.2.1 result.2.2 := by
  classical
  cases request with
  | inl message =>
    rw [auditedInterleavingStep, support_map] at hresult
    obtain ⟨signed, hsigned, rfl⟩ := hresult
    exact signWithDisclosures_preserves sk message state hinvariant signed hsigned
  | inr input =>
    rw [auditedInterleavingStep, support_map] at hresult
    obtain ⟨answer, hanswer, rfl⟩ := hresult
    simp only [decide_eq_true_eq] at hgood
    exact (query_preserves_globalReuse_iff sk state.1 state.2 hinvariant input answer hanswer).2 hgood

/-- Execute an adaptive mixture of complete signing calls and raw hash calls, stopping at
the first cache-discipline defect. This stop is bookkeeping, not a claimed security failure. -/
noncomputable def goodInterleavingPrefix {State : Type} (sk : Seeded.SecretKey)
    (choose : State → DisclosureState → ProbComp (InterleavingRequest × State)) :
    Nat → State → DisclosureState → ProbComp (Option (State × DisclosureState))
  | 0, privateState, state => pure (some (privateState, state))
  | n + 1, privateState, state => do
      let choice ← choose privateState state
      let result ← auditedInterleavingStep sk choice.1 state
      if result.1 then goodInterleavingPrefix sk choose n choice.2 result.2 else pure none

theorem goodInterleavingPrefix_preserves {State : Type} (sk : Seeded.SecretKey)
    (choose : State → DisclosureState → ProbComp (InterleavingRequest × State)) :
    ∀ n privateState state, GlobalReuseInvariant sk state.1 state.2 →
      ∀ result ∈ support (goodInterleavingPrefix sk choose n privateState state),
        ∀ final, result = some final → GlobalReuseInvariant sk final.2.1 final.2.2 := by
  intro n
  induction n with
  | zero =>
    intro privateState state hinvariant result hresult final heq
    simp only [goodInterleavingPrefix, support_pure, Set.mem_singleton_iff] at hresult
    rw [hresult] at heq
    cases Option.some.inj heq
    exact hinvariant
  | succ n ih =>
    intro privateState state hinvariant result hresult final heq
    rw [goodInterleavingPrefix, mem_support_bind_iff] at hresult
    obtain ⟨choice, _, hresult⟩ := hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨step, hstep, hresult⟩ := hresult
    by_cases hgood : step.1 = true
    · simp only [hgood, ↓reduceIte] at hresult
      exact ih choice.2 step.2
        (auditedInterleavingStep_preserves sk choice.1 state hinvariant step hstep hgood)
        result hresult final heq
    · simp only [hgood] at hresult
      rw [hresult] at heq
      contradiction

end LeanSphincs.Lifetime
