import LeanSphincs.LifetimeLanding
import LeanSphincs.RandomizedSupport
import LeanSphincs.Fresh

/-! Distributional properties of the actual independent-randomizer grinding loop. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

variable [Params]

/-- Before an accepting trial, all recorded first blocks are rejected. -/
def FirstRejected (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) : Prop :=
  ∀ randomness first, cache (msgInput sk message randomness) = some first →
    ¬Landed sk.parameter (blockIndex first)

def SecondFresh (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) : Prop :=
  ∀ randomness, cache (Security.digestInput sk.parameter sk.root message randomness 1) = none

omit [Params] in
theorem digestInput_calls_ne (parameter : PublicParameter) (root : Digest) (message : Message)
    (left right : Randomness) :
    Security.digestInput parameter root message left 1 ≠
      Security.digestInput parameter root message right 0 := by
  intro h
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [tweakBytes, fieldBytes, bytesLE_length])
  obtain ⟨hfields, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  have hposition := congrArg TweakFields.position (fieldBytes_injective hfields)
  simp [hashDomainFields, tweakFields] at hposition

theorem firstRejected_cacheQuery (sk : Seeded.SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hcache : FirstRejected sk message cache)
    (randomness : Randomness) (first : HashOutput) (hreject : ¬Landed sk.parameter (blockIndex first)) :
    FirstRejected sk message (cache.cacheQuery (msgInput sk message randomness) first) := by
  intro randomness' first' hfirst
  by_cases hsame : randomness' = randomness
  · subst randomness'
    rw [QueryCache.cacheQuery_self] at hfirst
    cases Option.some.inj hfirst
    exact hreject
  · rw [QueryCache.cacheQuery_of_ne cache first (fun h => hsame (msgInput_inj sk message h))]
      at hfirst
    exact hcache randomness' first' hfirst

omit [Params] in
theorem secondFresh_cacheQuery (sk : Seeded.SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hcache : SecondFresh sk message cache)
    (randomness : Randomness) (first : HashOutput) :
    SecondFresh sk message (cache.cacheQuery (msgInput sk message randomness) first) := by
  intro randomness'
  exact (QueryCache.cacheQuery_of_ne cache first
    (digestInput_calls_ne sk.parameter sk.root message randomness' randomness)).trans (hcache randomness')

/-- Repeated randomizers can revisit only rejected answers; a returned randomizer was fresh
relative to the initial cache whenever that cache contained only rejected first blocks. -/
theorem randomizedDigest_accepted_initially_fresh (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache cache' : QueryCache HashSpec) (hcache : FirstRejected sk message cache)
    (randomness : Randomness)
    (hsupport : (some randomness, cache') ∈ support
      ((simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache)) :
    cache (msgInput sk message randomness) = none := by
  obtain ⟨hcacheLe, haccepted⟩ := randomizedDigest_support sk message n cache _ cache' hsupport
  obtain ⟨first, hfirst, hland⟩ := haccepted randomness rfl
  cases hbefore : cache (msgInput sk message randomness) with
  | none => rfl
  | some old =>
    have heq := (hcacheLe hbefore).symm.trans hfirst
    have hreject := hcache randomness old hbefore
    cases Option.some.inj heq
    exact False.elim (hreject hland)

/-- The exact digest-producing prefix of signing: run the real grinding loop, then read both
message blocks using the resulting cache. No new independent digest sampler is introduced. -/
noncomputable def grindDigest (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) : ProbComp (Option MessageDigest) := do
  let result ← (simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache
  match result.1 with
  | none => pure none
  | some randomness =>
    (some ∘ Prod.fst) <$> (simulateQ randomOracle
      (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run
        result.2

theorem grindDigest_zero (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    grindDigest sk message 0 cache = pure none := by
  simp [grindDigest, Randomized.signDigestLoop]

theorem grindDigest_succ (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) :
    grindDigest sk message (n + 1) cache = (do
      let randomness ← ($ᵗ Randomness : ProbComp Randomness)
      let answer ← (randomOracle (spec := HashSpec) (msgInput sk message randomness)).run cache
      if Landed sk.parameter (blockIndex answer.1) then
        (some ∘ Prod.fst) <$> (simulateQ randomOracle
          (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run
            answer.2
      else grindDigest sk message n answer.2) := by
  rw [grindDigest, run_randomizedDigest_succ]
  simp only [bind_assoc]
  apply bind_congr
  intro randomness
  apply bind_congr
  intro answer
  split <;> simp [grindDigest]

def DigestEvent (P : KeptDigestView → Prop) : Option MessageDigest → Prop
  | none => False
  | some digest => P (localDigestView digest)

instance (P : KeptDigestView → Prop) [DecidablePred P] : DecidablePred (DigestEvent P)
  | none => isFalse not_false
  | some digest => inferInstanceAs (Decidable (P (localDigestView digest)))

omit [Params] in
theorem probEvent_bind_factor {α β : Type} (sample : ProbComp α) (next : α → ProbComp β)
    (P Q : β → Prop) [DecidablePred P] [DecidablePred Q] (factor : ℝ≥0∞)
    (h : ∀ a, Pr[P | next a] = Pr[Q | next a] * factor) :
    Pr[P | sample >>= next] = Pr[Q | sample >>= next] * factor := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  rw [h]
  exact (mul_assoc _ _ _).symm

omit [Params] in
theorem probEvent_branch_factor {α β : Type} (sample : ProbComp α)
    (test : α → Prop) [DecidablePred test] (accept reject : α → ProbComp β)
    (P Q : β → Prop) [DecidablePred P] [DecidablePred Q] (factor : ℝ≥0∞)
    (ha : (∑' a, Pr[= a | sample] * (if test a then Pr[P | accept a] else 0)) =
      (∑' a, Pr[= a | sample] * (if test a then Pr[Q | accept a] else 0)) * factor)
    (hr : ∀ a, ¬test a → Pr[P | reject a] = Pr[Q | reject a] * factor) :
    Pr[P | sample >>= fun a => if test a then accept a else reject a] =
      Pr[Q | sample >>= fun a => if test a then accept a else reject a] * factor := by
  have hsplit (R : β → Prop) [DecidablePred R] :
      Pr[R | sample >>= fun a => if test a then accept a else reject a] =
      (∑' a, Pr[= a | sample] * (if test a then Pr[R | accept a] else 0)) +
        (∑' a, Pr[= a | sample] * (if test a then 0 else Pr[R | reject a])) := by
    rw [probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
    apply tsum_congr
    intro a
    by_cases h : test a <;> simp [h]
  have hreject :
      (∑' a, Pr[= a | sample] * (if test a then 0 else Pr[P | reject a])) =
        (∑' a, Pr[= a | sample] * (if test a then 0 else Pr[Q | reject a])) * factor := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro a
    by_cases h : test a
    · simp [h]
    · simp [h, hr a h, mul_assoc]
  rw [hsplit P, hsplit Q, ha, hreject, add_mul]

noncomputable def finishGrindingDigest (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) : ProbComp (Option MessageDigest) :=
  (some ∘ Prod.fst) <$> (simulateQ randomOracle
    (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run cache

theorem probEvent_finishGrindingDigest_cached_first (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (hsecond : SecondFresh sk message cache)
    (first : HashOutput) (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[DigestEvent P | finishGrindingDigest sk message randomness
      (cache.cacheQuery (msgInput sk message randomness) first)] =
      Pr[fun second => P (localDigestView (truncateMessageDigest first second)) |
        ($ᵗ HashOutput : ProbComp HashOutput)] := by
  rw [finishGrindingDigest, Security.run_messageDigest_cached_first sk.parameter sk.root message
    randomness _ first (QueryCache.cacheQuery_self _ _ _)
      (secondFresh_cacheQuery sk message cache hsecond randomness first randomness)]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, DigestEvent]

/-- Averaging all fresh first blocks and the fresh final block gives exactly the accepted
uniform digest mass. The initial cache can contain arbitrary rejected first blocks. -/
theorem fresh_grinding_acceptance_mass (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (hsecond : SecondFresh sk message cache)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    (∑' first : HashOutput, Pr[= first | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed sk.parameter (blockIndex first) then
        Pr[DigestEvent P | finishGrindingDigest sk message randomness
          (cache.cacheQuery (msgInput sk message randomness) first)] else 0)) =
        ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
          Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  simp_rw [probEvent_finishGrindingDigest_cached_first sk message randomness cache hsecond]
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

/-- Any finite grinding budget has a uniform accepted digest marginal. Repeated randomizers
are handled by the consistent cache: a previously rejected randomizer is rejected again. -/
theorem grindDigest_uniform_factor (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n : Nat) (cache : QueryCache HashSpec), FirstRejected sk message cache →
      SecondFresh sk message cache → ∀ (P : KeptDigestView → Prop) [DecidablePred P],
      Pr[DigestEvent P | grindDigest sk message n cache] =
        Pr[DigestEvent (fun _ => True) | grindDigest sk message n cache] *
          Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  intro n
  induction n with
  | zero =>
    intro cache hfirst hsecond P _
    simp only [grindDigest_zero, probEvent_pure, DigestEvent, if_false, zero_mul]
  | succ n ih =>
    intro cache hfirst hsecond P _
    simp only [grindDigest_succ]
    apply probEvent_bind_factor
    intro randomness
    cases hc : cache (msgInput sk message randomness) with
    | some first =>
      rw [cached_run _ _ _ hc]
      simp only [pure_bind, if_neg (hfirst randomness first hc)]
      exact ih cache hfirst hsecond P
    | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
      change Pr[DigestEvent P | ($ᵗ HashOutput : ProbComp HashOutput) >>= fun first =>
        if Landed sk.parameter (blockIndex first) then
          finishGrindingDigest sk message randomness (cache.cacheQuery (msgInput sk message randomness) first)
        else grindDigest sk message n (cache.cacheQuery (msgInput sk message randomness) first)] =
        Pr[DigestEvent (fun _ => True) | ($ᵗ HashOutput : ProbComp HashOutput) >>= fun first =>
          if Landed sk.parameter (blockIndex first) then
            finishGrindingDigest sk message randomness (cache.cacheQuery (msgInput sk message randomness) first)
          else grindDigest sk message n (cache.cacheQuery (msgInput sk message randomness) first)] * _
      apply probEvent_branch_factor
      · rw [fresh_grinding_acceptance_mass sk message randomness cache hsecond P,
          fresh_grinding_acceptance_mass sk message randomness cache hsecond (fun _ => True)]
        simp only [probEvent_True_eq_sub, probFailure_uniformSample, tsub_zero, mul_one]
      · intro first hreject
        exact ih _ (firstRejected_cacheQuery sk message cache hfirst randomness first hreject)
          (secondFresh_cacheQuery sk message cache hsecond randomness first) P

theorem grindDigest_fresh_uniform_factor (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache : QueryCache HashSpec)
    (hfresh : ∀ randomness, Security.DigestFresh sk.parameter sk.root message randomness cache)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[DigestEvent P | grindDigest sk message n cache] =
      Pr[DigestEvent (fun _ => True) | grindDigest sk message n cache] *
        Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  apply grindDigest_uniform_factor sk message n cache
  · intro randomness first hfirst
    have hf := hfresh randomness 0
    rw [hf] at hfirst
    contradiction
  · exact fun randomness => hfresh randomness 1

omit [Params] in
theorem probEvent_uniform_bind_ge {α β : Type} [SampleableType α]
    (next : α → ProbComp β) (P : β → Prop) [DecidablePred P]
    (lower : ℝ≥0∞) (h : ∀ a, lower ≤ Pr[P | next a]) :
    lower ≤ Pr[P | ($ᵗ α : ProbComp α) >>= next] := by
  calc
    lower = (∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)]) * lower := by
      rw [tsum_probOutput_eq_one' (probFailure_uniformSample _), one_mul]
    _ = ∑' a : α, Pr[= a | ($ᵗ α : ProbComp α)] * lower := (ENNReal.tsum_mul_right).symm
    _ ≤ _ := by
      rw [probEvent_bind_eq_tsum]
      exact ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (h a) _)

/-- With at least one attempt and fresh message inputs, success has positive probability:
already the first trial succeeds with the exact subtree-landing probability. -/
theorem grindDigest_success_ge_landing (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache : QueryCache HashSpec)
    (hfresh : ∀ randomness, Security.DigestFresh sk.parameter sk.root message randomness cache) :
    ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ ≤
      Pr[DigestEvent (fun _ => True) | grindDigest sk message (n + 1) cache] := by
  rw [grindDigest_succ]
  apply probEvent_uniform_bind_ge
  intro randomness
  rw [fresh_run _ _ (hfresh randomness 0)]
  have ha := fresh_grinding_acceptance_mass sk message randomness cache
    (fun r => hfresh r 1) (fun _ => True)
  simp only [probEvent_True_eq_sub, probFailure_uniformSample, tsub_zero, mul_one,
    probOutput_uniformSample] at ha
  rw [← ha]
  apply ENNReal.tsum_le_tsum
  intro first
  apply mul_le_mul_right
  by_cases h : Landed sk.parameter (blockIndex first)
  · simp only [if_pos h]
    exact le_rfl
  · simp only [if_neg h]
    exact bot_le

/-- Normalized conditional distribution of the actual finite-budget grinding output. -/
theorem conditional_grindDigest_uniform (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache : QueryCache HashSpec)
    (hfresh : ∀ randomness, Security.DigestFresh sk.parameter sk.root message randomness cache)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[DigestEvent P | grindDigest sk message (n + 1) cache] /
      Pr[DigestEvent (fun _ => True) | grindDigest sk message (n + 1) cache] =
        Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] := by
  have hs : Pr[DigestEvent (fun _ => True) | grindDigest sk message (n + 1) cache] ≠ 0 := by
    have hp : (0 : ℝ≥0∞) < ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ := by
      exact pos_iff_ne_zero.mpr (by simp)
    exact ne_of_gt (hp.trans_le (grindDigest_success_ge_landing sk message n cache hfresh))
  rw [grindDigest_fresh_uniform_factor sk message (n + 1) cache hfresh P, div_eq_mul_inv,
    mul_comm _ (Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)]), mul_assoc,
    ENNReal.mul_inv_cancel hs probEvent_ne_top, mul_one]

/-- Key generation queries neither block of any message-digest input. -/
theorem keygen_message_inputs_fresh (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hsupport : result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅)) :
    ∀ message randomness,
      Security.DigestFresh result.1.2.parameter result.1.2.root message randomness result.2 := by
  intro message randomness call
  exact PreservesFresh.keygenFromSeed
    (structuralFresh_message result.1.2.parameter result.1.2.root message randomness call)
    seed ∅ result hsupport rfl

/-- After actual key generation, conditioning successful grinding yields independent uniform
local index and FORS selectors, with no external message-cache freshness assumption. -/
theorem conditional_grindDigest_after_keygen (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hsupport : result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅))
    (message : Message) (n : Nat) (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr[DigestEvent P | grindDigest result.1.2 message (n + 1) result.2] /
      Pr[DigestEvent (fun _ => True) | grindDigest result.1.2 message (n + 1) result.2] =
        Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)] :=
  conditional_grindDigest_uniform result.1.2 message n result.2
    (keygen_message_inputs_fresh seed result hsupport message) P

end LeanSphincs.Lifetime
