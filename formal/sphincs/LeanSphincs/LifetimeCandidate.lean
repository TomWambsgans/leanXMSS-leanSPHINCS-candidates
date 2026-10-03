import LeanSphincs.LifetimeInterleaving

/-! Exact candidate-search prices for all four cache states. In particular, adversarially
selected cached first blocks retain only ten random digest bits, while a cached second block
fixes the last FORS coordinate. These prices are not replaced by the honest lifetime bound. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

set_option exponentiation.threshold 512

theorem run_messageDigest_cached_second (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec)
    (second : HashOutput)
    (hfirst : cache (Security.digestInput parameter root message randomness 0) = none)
    (hsecond : cache (Security.digestInput parameter root message randomness 1) = some second) :
    (simulateQ randomOracle
      (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache =
    (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second,
        cache.cacheQuery (Security.digestInput parameter root message randomness 0) first)) := by
  simp only [messageDigest, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [randomOracle, QueryImpl.withCaching_run_none _ hfirst]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  apply bind_congr
  intro first
  rw [QueryImpl.withCaching_run_some _ ((QueryCache.cacheQuery_of_ne cache first
    (digestInput_calls_ne parameter root message randomness randomness)).trans hsecond)]
  simp [simulateQ_pure]

variable [Params]

/-- The exact probability of an accepted candidate satisfying `P`, conditional on this cache.
The two asymmetric cached-prefix cases intentionally have different denominators. -/
noncomputable def candidatePrice (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (P : KeptDigestView → Prop) : ℝ≥0∞ := by
  classical
  exact match cache (msgInput sk message randomness),
      cache (Security.digestInput sk.parameter sk.root message randomness 1) with
    | none, none => ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
        Pr[P | ($ᵗ KeptDigestView : ProbComp KeptDigestView)]
    | some first, none => if Landed sk.parameter (blockIndex first) then
        ((Finset.univ.filter (fun suffix : BitVec 10 =>
          P (localDigestView (Security.joinDigest (first, suffix))))).card : ℝ≥0∞) /
          ((2 ^ 10 : Nat) : ℝ≥0∞) else 0
    | none, some second =>
        ((Finset.univ.filter (fun first : HashOutput => Landed sk.parameter (blockIndex first) ∧
          P (localDigestView (truncateMessageDigest first second)))).card : ℝ≥0∞) /
          ((2 ^ 256 : Nat) : ℝ≥0∞)
    | some first, some second => if Landed sk.parameter (blockIndex first) ∧
        P (localDigestView (truncateMessageDigest first second)) then 1 else 0

theorem probEvent_messageDigest_candidate (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (P : KeptDigestView → Prop) :
    Pr[fun result => Landed sk.parameter (digestIndex result.1) ∧ P (localDigestView result.1) |
      (simulateQ randomOracle
        (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest)).run cache] =
      candidatePrice sk message randomness cache P := by
  classical
  cases hfirst : cache (msgInput sk message randomness) with
  | none =>
    cases hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) with
    | none =>
      have hfresh : Security.DigestFresh sk.parameter sk.root message randomness cache := by
        intro call
        fin_cases call
        · exact hfirst
        · exact hsecond
      simpa only [candidatePrice, hfirst, hsecond] using
        probEvent_messageDigest_landed_local sk.parameter sk.root message randomness cache hfresh P
    | some second =>
      rw [run_messageDigest_cached_second sk.parameter sk.root message randomness cache second hfirst hsecond]
      simp only [bind_pure_comp, probEvent_map, Function.comp_def, digestIndex_truncate,
        candidatePrice, hfirst, hsecond]
      rw [probEvent_uniformSample, card_bitVec]
      rfl
  | some first =>
    cases hsecond : cache (Security.digestInput sk.parameter sk.root message randomness 1) with
    | none =>
      rw [Security.run_messageDigest_cached_first sk.parameter sk.root message randomness cache first hfirst hsecond]
      simp only [bind_pure_comp, probEvent_map, Function.comp_def, digestIndex_truncate,
        candidatePrice, hfirst, hsecond]
      by_cases hland : Landed sk.parameter (blockIndex first)
      · simp only [hland, true_and, if_true, Security.truncateMessageDigest_eq_join]
        change Pr[(fun suffix => P (localDigestView (Security.joinDigest (first, suffix)))) ∘
          (fun second : HashOutput => second.extractLsb' 0 10) |
            ($ᵗ HashOutput : ProbComp HashOutput)] = _
        rw [← probEvent_map, probEvent_congr' (fun _ _ => Iff.rfl)
          (evalDist_hashOutput_extract_uniform (width := 10) (by decide)),
          probEvent_uniformSample, card_bitVec]
      · simp only [hland, false_and, if_false, probEvent_False]
    | some second =>
      rw [run_messageDigest_cached_both sk.parameter sk.root message randomness cache first second hfirst hsecond]
      simp only [probEvent_pure, digestIndex_truncate, candidatePrice, hfirst, hsecond]

theorem candidatePrice_le_one (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (P : KeptDigestView → Prop) :
    candidatePrice sk message randomness cache P ≤ 1 := by
  rw [← probEvent_messageDigest_candidate]
  exact probEvent_le_one

/-- The adaptive request and its cache may depend arbitrarily on the past. This identity
exposes the exact conditional prices; it does not impose an unjustified fresh-sample bound. -/
theorem probEvent_adaptive_candidate {Choice : Type} (sk : Seeded.SecretKey)
    (prepare : ProbComp Choice) (message : Choice → Message) (randomness : Choice → Randomness)
    (cache : Choice → QueryCache HashSpec) (P : Choice → KeptDigestView → Prop)
    [∀ choice, DecidablePred (P choice)] :
    Pr[fun result => result = true | (do
      let choice ← prepare
      let digest ← (simulateQ randomOracle
        (messageDigest sk.parameter sk.root (message choice) (randomness choice) :
          OracleComp HashSpec MessageDigest)).run (cache choice)
      pure (decide (Landed sk.parameter (digestIndex digest.1) ∧ P choice (localDigestView digest.1))))] =
      ∑' choice, Pr[= choice | prepare] *
        candidatePrice sk (message choice) (randomness choice) (cache choice) (P choice) := by
  classical
  rw [probEvent_bind_eq_tsum]
  apply tsum_congr
  intro choice
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, decide_eq_true_eq]
  rw [probEvent_messageDigest_candidate]

end LeanSphincs.Lifetime
