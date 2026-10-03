import LeanSphincs.LifetimeDisclosureCache
import LeanSphincs.FinishFresh

/-! Actual signing calls with a proof-side record of all accepted digests. The record is updated
before WOTS assembly, including when assembly exhausts and returns no signature. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

variable [Params]

theorem globalReuseInvariant_of_message_cache_eq (sk : Seeded.SecretKey)
    (prior : Finset KeptDigestView) (before after : QueryCache HashSpec)
    (hinvariant : GlobalReuseInvariant sk prior before)
    (heq : ∀ message randomness call,
      after (Security.digestInput sk.parameter sk.root message randomness call) =
        before (Security.digestInput sk.parameter sk.root message randomness call)) :
    GlobalReuseInvariant sk prior after := by
  intro message
  constructor
  · intro randomness first hfirst hland
    rw [heq message randomness 0] at hfirst
    obtain ⟨second, hsecond, hprior⟩ := (hinvariant message).accepted randomness first hfirst hland
    exact ⟨second, (heq message randomness 1).trans hsecond, hprior⟩
  · intro randomness hfirst
    rw [heq message randomness 0] at hfirst
    exact (heq message randomness 1).trans ((hinvariant message).freshSecond randomness hfirst)

theorem finishSignBody_preserves_globalReuse (sk : Seeded.SecretKey) (randomness : Randomness)
    (digest : MessageDigest) (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hinvariant : GlobalReuseInvariant sk prior cache) (result : Option Signature × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ randomOracle (finishSignBody sk randomness digest)).run cache)) :
    GlobalReuseInvariant sk prior result.2 :=
  globalReuseInvariant_of_message_cache_eq sk prior cache result.2 hinvariant
    (fun message rho call => finishSignBody_message_cache_eq sk randomness digest cache result hresult
      sk.parameter sk.root message rho call)

noncomputable def signWithDisclosures (sk : Seeded.SecretKey) (message : Message)
    (state : DisclosureState) : ProbComp (Option Signature × DisclosureState) := do
  let loop ← (simulateQ romImpl (Randomized.signDigestLoop sk message digestAttemptLimit)).run state.2
  match loop.1 with
  | none => pure (none, (state.1, loop.2))
  | some randomness =>
    let digest ← (simulateQ randomOracle
      (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run loop.2
    let result ← (simulateQ randomOracle (finishSignBody sk randomness digest.1)).run digest.2
    pure (result.1, (insert (localDigestView digest.1) state.1, result.2))

/-- Erasing the proof-side set yields exactly the real signer and its final hash cache. -/
theorem signWithDisclosures_forget (sk : Seeded.SecretKey) (message : Message)
    (state : DisclosureState) :
    (fun result => (result.1, result.2.2)) <$> signWithDisclosures sk message state =
      (simulateQ romImpl (Randomized.sign sk message)).run state.2 := by
  rw [signWithDisclosures, map_bind, Randomized.sign, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  rintro ⟨result, cache⟩
  cases result with
  | none => simp only [map_pure, simulateQ_pure, StateT.run_pure]
  | some randomness =>
    rw [simulate_lift_hash, finishSign_eq_digest_body, simulateQ_bind, StateT.run_bind]
    simp only [map_bind, map_pure, Prod.eta, bind_pure]

theorem grindDigestState_none_mem (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache next : QueryCache HashSpec)
    (hloop : (none, next) ∈ support ((simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache)) :
    (none, next) ∈ support (grindDigestState sk message n cache) := by
  rw [grindDigestState, mem_support_bind_iff]
  exact ⟨(none, next), hloop, by simp⟩

theorem grindDigestState_some_mem (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache middle last : QueryCache HashSpec) (randomness : Randomness) (digest : MessageDigest)
    (hloop : (some randomness, middle) ∈ support
      ((simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache))
    (hdigest : (digest, last) ∈ support ((simulateQ randomOracle
      (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run middle)) :
    (some digest, last) ∈ support (grindDigestState sk message n cache) := by
  rw [grindDigestState, mem_support_bind_iff]
  refine ⟨(some randomness, middle), hloop, ?_⟩
  rw [support_map]
  exact ⟨(digest, last), hdigest, rfl⟩

theorem signWithDisclosures_preserves (sk : Seeded.SecretKey) (message : Message)
    (state : DisclosureState) (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (result : Option Signature × DisclosureState)
    (hresult : result ∈ support (signWithDisclosures sk message state)) :
    GlobalReuseInvariant sk result.2.1 result.2.2 := by
  rw [signWithDisclosures, mem_support_bind_iff] at hresult
  obtain ⟨⟨loop, middle⟩, hloop, hresult⟩ := hresult
  cases loop with
  | none =>
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    exact grindDigestState_preserves_global sk message _ state.1 state.2 hinvariant _
      (grindDigestState_none_mem sk message _ state.2 middle hloop)
  | some randomness =>
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨digest, beforeBody⟩, hdigest, hresult⟩ := hresult
    rw [mem_support_bind_iff] at hresult
    obtain ⟨⟨signature, afterBody⟩, hbody, hresult⟩ := hresult
    simp only [support_pure, Set.mem_singleton_iff] at hresult
    subst result
    have hprefix := grindDigestState_preserves_global sk message _ state.1 state.2 hinvariant _
      (grindDigestState_some_mem sk message _ state.2 middle beforeBody randomness digest hloop hdigest)
    exact finishSignBody_preserves_globalReuse sk randomness digest _ beforeBody hprefix
      (signature, afterBody) hbody

/-- Later assembly cannot increase a disclosure event; the digest was recorded before it. -/
theorem signWithDisclosures_le_grinding (sk : Seeded.SecretKey) (message : Message)
    (state : DisclosureState) (event : Finset KeptDigestView → Prop) [DecidablePred event] :
    Pr[fun result => event result.2.1 | signWithDisclosures sk message state] ≤
      Pr[fun result => event (disclosedViewsAfter state.1 result.1) |
        grindDigestState sk message digestAttemptLimit state.2] := by
  rw [signWithDisclosures, grindDigestState, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  rintro ⟨loop, middle⟩
  apply mul_le_mul_right
  cases loop with
  | none => simp only [probEvent_pure, disclosedViewsAfter]; exact le_rfl
  | some randomness =>
    simp only [probEvent_map, Function.comp_def, disclosedViewsAfter]
    apply probEvent_bind_le_probEvent
    intro digest _ hnot
    simp only [bind_pure_comp, probEvent_map, Function.comp_def, hnot, probEvent_False]

noncomputable def signingDisclosureStep (sk : Seeded.SecretKey)
    (request : DisclosureState → Message) (state : DisclosureState) : ProbComp DisclosureState :=
  Prod.snd <$> signWithDisclosures sk (request state) state

theorem signingDisclosureStep_preserves (sk : Seeded.SecretKey) (request : DisclosureState → Message)
    (state : DisclosureState) (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (next : DisclosureState) (hnext : next ∈ support (signingDisclosureStep sk request state)) :
    GlobalReuseInvariant sk next.1 next.2 := by
  rw [signingDisclosureStep, support_map] at hnext
  obtain ⟨result, hresult, rfl⟩ := hnext
  exact signWithDisclosures_preserves sk (request state) state hinvariant result hresult

theorem signingDisclosureStep_le_uniform (sk : Seeded.SecretKey) (request : DisclosureState → Message)
    (state : DisclosureState) (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (event : Finset KeptDigestView → Prop) [DecidablePred event] (hmono : Monotone event) :
    Pr[fun next => event next.1 | signingDisclosureStep sk request state] ≤
      Pr[fun view => event (insert view state.1) | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  rw [signingDisclosureStep, probEvent_map]
  refine (signWithDisclosures_le_grinding sk (request state) state event).trans ?_
  change Pr[(fun result => event (disclosedViewsAfter state.1 result)) ∘ Prod.fst |
    grindDigestState sk (request state) digestAttemptLimit state.2] ≤ _
  rw [← probEvent_map, grindDigestState_fst]
  exact grindDigest_disclosure_step_le_uniform sk (request state) _ state.1 state.2
    (hinvariant (request state)) event hmono

/-- N complete signing calls, including exhausted calls, are dominated by N independent
uniform insertions. Message choices may depend on the entire cache and proof-side history.
Adversarial hash-query interleaving remains outside this experiment. -/
theorem signing_disclosures_le_uniform (sk : Seeded.SecretKey) (request : DisclosureState → Message)
    (n : Nat) (state : DisclosureState) (hinvariant : GlobalReuseInvariant sk state.1 state.2)
    (event : Finset KeptDigestView → Prop) [DecidablePred event] (hmono : Monotone event) :
    Pr[event | disclosureProcess (signingDisclosureStep sk request) Prod.fst n state] ≤
      Pr[event | uniformDisclosureSet n state.1] :=
  disclosureProcess_le_uniform (signingDisclosureStep sk request) Prod.fst
    (fun state => GlobalReuseInvariant sk state.1 state.2)
    (signingDisclosureStep_preserves sk request)
    (signingDisclosureStep_le_uniform sk request) n state hinvariant event hmono

theorem signing_disclosures_after_keygen_le_uniform (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hsupport : result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅))
    (request : DisclosureState → Message) (n : Nat)
    (event : Finset KeptDigestView → Prop) [DecidablePred event] (hmono : Monotone event) :
    Pr[event | disclosureProcess (signingDisclosureStep result.1.2 request) Prod.fst n (∅, result.2)] ≤
      Pr[event | uniformDisclosureSet n ∅] :=
  signing_disclosures_le_uniform result.1.2 request n (∅, result.2)
    (globalReuseInvariant_after_keygen seed result hsupport) event hmono

end LeanSphincs.Lifetime
