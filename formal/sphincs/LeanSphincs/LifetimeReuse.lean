import LeanSphincs.LifetimeGrinding

/-!
Fresh-or-repeat domination for actual randomized grinding. A previously accepted digest may be
cached, provided its complete view is already disclosed. Such a repeat adds no disclosure.
For every event of new views, the next grinding call has mass at most one independent uniform
kept-view sample. Adversary-prequeried accepted digests outside the disclosed set are expressly
excluded by the cache invariant and require a separate security accounting argument.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

variable [Params]

structure ReuseInvariant (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec) : Prop where
  accepted : ∀ randomness first, cache (msgInput sk message randomness) = some first →
    Landed sk.parameter (blockIndex first) → ∃ second,
      cache (Security.digestInput sk.parameter sk.root message randomness 1) = some second ∧
        localDigestView (truncateMessageDigest first second) ∈ prior
  freshSecond : ∀ randomness, cache (msgInput sk message randomness) = none →
    cache (Security.digestInput sk.parameter sk.root message randomness 1) = none

theorem reuseInvariant_of_fresh (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hfresh : ∀ randomness, Security.DigestFresh sk.parameter sk.root message randomness cache) :
    ReuseInvariant sk message prior cache := by
  constructor
  · intro randomness first hfirst
    rw [hfresh randomness 0] at hfirst
    contradiction
  · intro randomness _
    exact hfresh randomness 1

theorem ReuseInvariant.mono_prior (sk : Seeded.SecretKey) (message : Message)
    {prior larger : Finset KeptDigestView} (cache : QueryCache HashSpec)
    (h : ReuseInvariant sk message prior cache) (hsub : prior ⊆ larger) :
    ReuseInvariant sk message larger cache := by
  refine ⟨?_, h.freshSecond⟩
  intro randomness first hfirst hland
  obtain ⟨second, hsecond, hprior⟩ := h.accepted randomness first hfirst hland
  exact ⟨second, hsecond, hsub hprior⟩

theorem reuseInvariant_rejected_cacheQuery (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : ReuseInvariant sk message prior cache) (randomness : Randomness)
    (first : HashOutput) (hreject : ¬Landed sk.parameter (blockIndex first)) :
    ReuseInvariant sk message prior (cache.cacheQuery (msgInput sk message randomness) first) := by
  constructor
  · intro randomness' first' hfirst hland
    by_cases hsame : randomness' = randomness
    · subst randomness'
      rw [QueryCache.cacheQuery_self] at hfirst
      cases Option.some.inj hfirst
      exact False.elim (hreject hland)
    · rw [QueryCache.cacheQuery_of_ne cache first (fun h => hsame (msgInput_inj sk message h))]
        at hfirst
      obtain ⟨second, hsecond, hprior⟩ := hcache.accepted randomness' first' hfirst hland
      refine ⟨second, ?_, hprior⟩
      exact (QueryCache.cacheQuery_of_ne cache first
        (digestInput_calls_ne sk.parameter sk.root message randomness' randomness)).trans hsecond
  · intro randomness' hnew
    have hsame : randomness' ≠ randomness := by
      intro h
      subst randomness'
      rw [QueryCache.cacheQuery_self] at hnew
      contradiction
    rw [QueryCache.cacheQuery_of_ne cache first (fun h => hsame (msgInput_inj sk message h))] at hnew
    exact (QueryCache.cacheQuery_of_ne cache first
      (digestInput_calls_ne sk.parameter sk.root message randomness' randomness)).trans
        (hcache.freshSecond randomness' hnew)

omit [Params] in
theorem run_messageDigest_cached_both (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec)
    (first second : HashOutput)
    (hfirst : cache (Security.digestInput parameter root message randomness 0) = some first)
    (hsecond : cache (Security.digestInput parameter root message randomness 1) = some second) :
    (simulateQ randomOracle
      (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache =
      pure (truncateMessageDigest first second, cache) := by
  simp only [messageDigest, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [randomOracle, QueryImpl.withCaching_run_some _ hfirst, pure_bind,
    QueryImpl.withCaching_run_some _ hsecond]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure]

omit [Params] in
theorem finishGrindingDigest_cached_both (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (first second : HashOutput)
    (hfirst : cache (msgInput sk message randomness) = some first)
    (hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) = some second) :
    finishGrindingDigest sk message randomness cache = pure (some (truncateMessageDigest first second)) := by
  rw [finishGrindingDigest, run_messageDigest_cached_both sk.parameter sk.root message randomness
    cache first second hfirst hsecond, map_pure]
  rfl

theorem probEvent_finishGrindingDigest_local_fresh (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) = none)
    (first : HashOutput) (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[DigestEvent P | finishGrindingDigest sk message randomness
      (cache.cacheQuery (msgInput sk message randomness) first)] =
      Pr[fun second => P (localDigestView (truncateMessageDigest first second)) |
        ($ᵗ HashOutput : ProbComp HashOutput)] := by
  have hsecond' := (QueryCache.cacheQuery_of_ne cache first
    (digestInput_calls_ne sk.parameter sk.root message randomness randomness)).trans hsecond
  rw [finishGrindingDigest, Security.run_messageDigest_cached_first sk.parameter sk.root message
    randomness _ first (QueryCache.cacheQuery_self _ _ _) hsecond']
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, DigestEvent]

theorem fresh_grinding_acceptance_mass_local (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) = none)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    (∑' first : HashOutput, Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed sk.parameter (blockIndex first) then
        Pr[DigestEvent P | finishGrindingDigest sk message randomness
          (cache.cacheQuery (msgInput sk message randomness) first)] else 0)) =
        ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
          Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  simp_rw [probEvent_finishGrindingDigest_local_fresh sk message randomness cache hsecond]
  calc
    _ = Pr[fun digest => Landed sk.parameter (digestIndex digest) ∧ P (localDigestView digest) |
        (do
          let first ← ($ᵗ HashOutput : ProbComp HashOutput)
          let second ← ($ᵗ HashOutput : ProbComp HashOutput)
          pure (truncateMessageDigest first second))] := by
      rw [probEvent_bind_eq_tsum]
      apply tsum_congr
      intro first
      simp only [bind_pure_comp, probEvent_map, Function.comp_def, digestIndex_truncate]
      by_cases h : Landed sk.parameter (blockIndex first) <;>
        simp only [h, ↓reduceIte, true_and, false_and, probEvent_False, mul_zero]
    _ = _ := by
      rw [probEvent_congr' (fun _ _ => Iff.rfl) Security.evalDist_digestBlocks_uniform]
      exact probEvent_landed_localDigest sk.parameter P

omit [Params] in
theorem probEvent_uniform_bind_le {α β : Type} [SampleableType α]
    (next : α → ProbComp β) (P : β → Prop) [DecidablePred P]
    (upper : ℝ≥0∞) (h : ∀ a, Pr[P | next a] ≤ upper) :
    Pr[P | ($ᵗ α : ProbComp α) >>= next] ≤ upper := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * upper :=
      ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a) _)
    _ = (∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)]) * upper := ENNReal.tsum_mul_right
    _ = _ := by rw [tsum_probOutput_eq_one' (probFailure_uniformSample _), one_mul]

omit [Params] in
theorem probEvent_branch_eq {α β : Type} (sample : ProbComp α)
    (test : α → Prop) [DecidablePred test] (accept reject : α → ProbComp β)
    (P : β → Prop) [DecidablePred P] :
    Pr[P | sample >>= fun a => if test a then accept a else reject a] =
      (∑' a, Pr[= a | sample] * (if test a then Pr[P | accept a] else 0)) +
        (∑' a, Pr[= a | sample] * (if test a then 0 else Pr[P | reject a])) := by
  rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  apply tsum_congr
  intro a
  by_cases h : test a <;> simp [h]

theorem fresh_grinding_branch_le_uniform (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec)
    (hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) = none)
    (next : HashOutput → ProbComp (Option MessageDigest))
    (P : KeptDigestView → Prop) [DecidablePred P]
    (hnext : ∀ first, ¬Landed sk.parameter (blockIndex first) →
      Pr[DigestEvent P | next first] ≤ Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)]) :
    Pr[DigestEvent P | ($ᵗ HashOutput : ProbComp HashOutput) >>= fun first =>
      if Landed sk.parameter (blockIndex first) then
        finishGrindingDigest sk message randomness (cache.cacheQuery (msgInput sk message randomness) first)
      else next first] ≤ Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  rw [probEvent_branch_eq, fresh_grinding_acceptance_mass_local sk message randomness cache hsecond P]
  refine (add_le_add le_rfl (ENNReal.tsum_le_tsum (g := fun first : HashOutput =>
    Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed sk.parameter (blockIndex first) then 0 else
        Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)])) ?_)).trans_eq ?_
  · intro first
    apply mul_le_mul_right
    by_cases h : Landed sk.parameter (blockIndex first)
    · simp only [if_pos h]
      exact le_rfl
    · simpa only [if_neg h] using hnext first h
  · simp only [probOutput_uniformSample]
    rw [tsum_uniform_ite]
    simp only [zero_mul, zero_add]
    change _ + _ * digestReject sk.parameter = _
    rw [mul_comm ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹,
      ← mul_add, add_comm _ (digestReject sk.parameter), digestReject_add, mul_one]

/-- A cached complete accepted digest is a repeat and has zero probability of adding a new view. -/
theorem cached_accepted_adds_no_view (sk : Seeded.SecretKey) (message : Message)
    (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : ReuseInvariant sk message prior cache) (randomness : Randomness) (first : HashOutput)
    (hfirst : cache (msgInput sk message randomness) = some first)
    (hland : Landed sk.parameter (blockIndex first))
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[DigestEvent (fun view => view ∉ prior ∧ P view) |
      finishGrindingDigest sk message randomness cache] = 0 := by
  obtain ⟨second, hsecond, hprior⟩ := hcache.accepted randomness first hfirst hland
  rw [finishGrindingDigest_cached_both sk message randomness cache first second hfirst hsecond]
  simp only [probEvent_pure, DigestEvent, hprior, not_true_eq_false, false_and, if_false]

/-- Every event of genuinely new digest views is dominated by one independent uniform sample.
No independence is assumed between calls, and already disclosed accepted digests may repeat. -/
theorem grindDigest_new_view_le_uniform (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n : Nat) (prior : Finset KeptDigestView) (cache : QueryCache HashSpec),
      ReuseInvariant sk message prior cache → ∀ (P : KeptDigestView → Prop) [DecidablePred P],
      Pr[DigestEvent (fun view => view ∉ prior ∧ P view) | grindDigest sk message n cache] ≤
        Pr[fun view => view ∉ prior ∧ P view | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  intro n
  induction n with
  | zero =>
    intro prior cache hcache P _
    simp only [grindDigest_zero, probEvent_pure, DigestEvent, if_false]
    exact bot_le
  | succ n ih =>
    intro prior cache hcache P _
    rw [grindDigest_succ]
    apply probEvent_uniform_bind_le
    intro randomness
    cases hc : cache (msgInput sk message randomness) with
    | some first =>
      rw [cached_run _ _ _ hc, pure_bind]
      by_cases hland : Landed sk.parameter (blockIndex first)
      · rw [if_pos hland]
        change Pr[_ | finishGrindingDigest sk message randomness cache] ≤ _
        rw [cached_accepted_adds_no_view sk message prior cache hcache randomness first hc hland P]
        exact bot_le
      · rw [if_neg hland]
        exact ih prior cache hcache P
    | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      apply fresh_grinding_branch_le_uniform sk message randomness cache (hcache.freshSecond randomness hc)
      intro first hreject
      exact ih prior _ (reuseInvariant_rejected_cacheQuery sk message prior cache hcache
        randomness first hreject) P

/-- Exhaustion keeps the disclosure set unchanged; a returned digest inserts its view. -/
def disclosedViewsAfter (prior : Finset KeptDigestView) : Option MessageDigest → Finset KeptDigestView
  | none => prior
  | some digest => insert (localDigestView digest) prior

/-- One actual grinding call is dominated, for every increasing disclosure event, by inserting
one independent uniform kept digest. Repeats and exhaustion both leave the previous set intact. -/
theorem grindDigest_disclosure_step_le_uniform (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (prior : Finset KeptDigestView) (cache : QueryCache HashSpec)
    (hcache : ReuseInvariant sk message prior cache)
    (event : Finset KeptDigestView → Prop) [DecidablePred event] (hmono : Monotone event) :
    Pr[fun result => event (disclosedViewsAfter prior result) | grindDigest sk message n cache] ≤
      Pr[fun view => event (insert view prior) | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  by_cases halready : event prior
  · have hevent : (fun view : KeptDigestView => event (insert view prior)) = fun _ => True := by
      funext view
      apply propext
      exact ⟨fun _ => trivial, fun _ => hmono (Finset.subset_insert view prior) halready⟩
    rw [hevent, probEvent_True_eq_sub, probFailure_uniformSample, tsub_zero]
    exact probEvent_le_one
  · have hevent : (fun result => event (disclosedViewsAfter prior result)) =
        DigestEvent (fun view => view ∉ prior ∧ event (insert view prior)) := by
      funext result
      apply propext
      cases result with
      | none => simp only [disclosedViewsAfter, DigestEvent, halready]
      | some digest =>
        simp only [disclosedViewsAfter, DigestEvent]
        by_cases hmem : localDigestView digest ∈ prior
        · simp only [Finset.insert_eq_of_mem hmem, halready, hmem, not_true_eq_false, false_and]
        · simp only [hmem, not_false_eq_true, true_and]
    rw [hevent]
    exact (grindDigest_new_view_le_uniform sk message n prior cache hcache
      (fun view => event (insert view prior))).trans (probEvent_mono'' (fun _ h => h.2))

end LeanSphincs.Lifetime
