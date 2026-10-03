import LeanSphincs.ForsCoverage
import LeanSphincs.Bytes
import LeanSphincs.Search

/-!
The candidate's actual two-call digest in the lazy random oracle. Both block inputs must be
fresh. The hypothesis is deliberately explicit: querying a cached digest is not an independent
uniform trial, and a security reduction must account for such queries separately.

The fixed-table coverage identity is from `ForsCoverage`; the query-cache simulation uses the
same VCVio lazy oracle as the security experiment. Adapted from the leanVM proof methodology.
-/

open OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 512

namespace LeanSphincs.Security
open Concrete

/-- The second hash block contributes only its low ten bits. -/
def joinDigest (blocks : HashOutput × BitVec 10) : MessageDigest :=
  blocks.2 ++ blocks.1

theorem joinDigest_injective : Function.Injective joinDigest := by
  intro x y h
  apply Prod.ext
  · have hlow := congrArg (fun d : MessageDigest => d.extractLsb' 0 256) h
    change (x.2 ++ x.1).extractLsb' 0 hashOutputBits =
      (y.2 ++ y.1).extractLsb' 0 hashOutputBits at hlow
    simpa only [BitVec.extractLsb'_append_eq_right] using hlow
  · have hhigh := congrArg (fun d : MessageDigest => d.extractLsb' 256 10) h
    change (x.2 ++ x.1).extractLsb' hashOutputBits 10 =
      (y.2 ++ y.1).extractLsb' hashOutputBits 10 at hhigh
    simpa only [BitVec.extractLsb'_append_eq_left] using hhigh

theorem joinDigest_bijective : Function.Bijective joinDigest := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨joinDigest_injective, ?_⟩
  simp only [Fintype.card_prod, card_bitVec, ← pow_add]
  rfl

theorem truncateMessageDigest_eq_join (first second : HashOutput) :
    truncateMessageDigest first second = joinDigest (first, second.extractLsb' 0 10) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 266 := hi
  change ((second ++ first).extractLsb' 0 266).getLsbD i =
    ((second.extractLsb' 0 10) ++ first).getLsbD i
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp only [hashOutputBits, Nat.zero_add]
  by_cases hlow : i < 256
  · simp [hlow, hi']
  · have hhigh : i - 256 < 10 := by omega
    simp [hlow, hi', hhigh]

/-- The two independent oracle blocks induce exactly the uniform 266-bit digest law. -/
theorem evalDist_digestBlocks_uniform :
    𝒟[(do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second))] =
      𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  let pairs : ProbComp (HashOutput × BitVec 10) := do
    let first ← ($ᵗ HashOutput : ProbComp HashOutput)
    let second ← ($ᵗ HashOutput : ProbComp HashOutput)
    pure (first, second.extractLsb' 0 10)
  have hpairs : 𝒟[pairs] = 𝒟[($ᵗ (HashOutput × BitVec 10) :
      ProbComp (HashOutput × BitVec 10))] := by
    apply evalDist_ext
    intro pair
    change Pr[= pair | (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure ((id first), second.extractLsb' 0 10))] = _
    rw [probOutput_bind_bind_prod_mk_eq_mul]
    simp only [id_map]
    rw [evalDist_ext_iff.mp
      (evalDist_hashOutput_extract_uniform (width := 10) (by decide)) pair.2]
    simp [ENNReal.mul_inv, Nat.cast_mul]
  have hjoin : (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second)) = joinDigest <$> pairs := by
    simp only [pairs, map_bind, map_pure, truncateMessageDigest_eq_join]
  rw [hjoin, evalDist_map, hpairs, ← evalDist_map]
  exact evalDist_map_bijective_uniform_cross (α := HashOutput × BitVec 10)
    (β := MessageDigest) joinDigest joinDigest_bijective

/-- The exact byte string queried for one block of a message digest. -/
abbrev digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) : HashInput :=
  tweakableHashInput parameter (.message call) (messageDigestPayload root message randomness)

theorem digestInput_injective (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    Function.Injective (digestInput parameter root message randomness) := by
  intro left right h
  have hfields := fieldBytes_injective
    (List.append_cancel_right (List.append_cancel_right h))
  have hposition := congrArg TweakFields.position hfields
  apply Fin.ext
  exact ofNat_inj_of_lt (by have := left.isLt; omega) (by have := right.isLt; omega) hposition

/-- Freshness for both separately tweaked blocks, relative to the history before the trial. -/
def DigestFresh (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) : Prop :=
  ∀ call : Fin 2, cache (digestInput parameter root message randomness call) = none

theorem run_messageDigest_fresh (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec)
    (hfresh : DigestFresh parameter root message randomness cache) :
    (simulateQ randomOracle
      (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache =
    (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second,
        (cache.cacheQuery (digestInput parameter root message randomness 0) first).cacheQuery
          (digestInput parameter root message randomness 1) second)) := by
  have hne : digestInput parameter root message randomness 1 ≠
      digestInput parameter root message randomness 0 := by
    intro h
    have := digestInput_injective parameter root message randomness h
    exact (by decide : (1 : Fin 2) ≠ 0) this
  simp only [messageDigest, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [randomOracle, QueryImpl.withCaching_run_none _ (hfresh 0)]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  apply bind_congr
  intro first
  rw [QueryImpl.withCaching_run_none _
    ((QueryCache.cacheQuery_of_ne cache first hne).trans (hfresh 1))]
  simp [uniformSampleImpl, simulateQ_pure]

/-- Reading a fresh digest from the actual cache has the uniform digest marginal. -/
theorem evalDist_messageDigest_fresh (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec)
    (hfresh : DigestFresh parameter root message randomness cache) :
    𝒟[Prod.fst <$> (simulateQ randomOracle
      (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache] =
      𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  rw [run_messageDigest_fresh parameter root message randomness cache hfresh]
  simpa only [map_bind, map_pure] using evalDist_digestBlocks_uniform

/-- Coverage probability for the concrete two-query digest, after any fixed prior history. -/
theorem probEvent_messageDigest_covered (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec)
    (hfresh : DigestFresh parameter root message randomness cache) (revealed : Disclosures) :
    Pr[fun result => Covered revealed (fullDigestView result.1) |
      (simulateQ randomOracle
        (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache] =
      ((∑ index : Index, ∏ tree : FtsTree, (revealed index tree).card : Nat) : ℝ≥0∞) /
        ((2 ^ 266 : Nat) : ℝ≥0∞) := by
  change Pr[(fun d => Covered revealed (fullDigestView d)) ∘ Prod.fst | _] = _
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_messageDigest_fresh parameter root message randomness cache hfresh)]
  exact fresh_fors_coverage revealed

/-- In the signer's finishing phase, the accepted first block is already cached. Only the
second block is sampled, so conditional uniformity is over ten remaining digest bits. -/
theorem run_messageDigest_cached_first (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec)
    (first : HashOutput)
    (hfirst : cache (digestInput parameter root message randomness 0) = some first)
    (hsecond : cache (digestInput parameter root message randomness 1) = none) :
    (simulateQ randomOracle
      (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache =
    (do
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second,
        cache.cacheQuery (digestInput parameter root message randomness 1) second)) := by
  simp only [messageDigest, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [randomOracle, QueryImpl.withCaching_run_some _ hfirst, pure_bind,
    QueryImpl.withCaching_run_none _ hsecond]
  simp [uniformSampleImpl, simulateQ_pure]

/-- Exact cached-prefix coverage probability. Replacing this by `fresh_fors_coverage` would be
invalid: all but ten of the digest bits have already been fixed by the prior transcript. -/
theorem probEvent_messageDigest_cached_first_covered
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec) (first : HashOutput)
    (hfirst : cache (digestInput parameter root message randomness 0) = some first)
    (hsecond : cache (digestInput parameter root message randomness 1) = none)
    (revealed : Disclosures) :
    Pr[fun result => Covered revealed (fullDigestView result.1) |
      (simulateQ randomOracle
        (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest)).run cache] =
      ((Finset.univ.filter (fun suffix : BitVec 10 =>
        Covered revealed (fullDigestView (joinDigest (first, suffix))))).card : ℝ≥0∞) /
        ((2 ^ 10 : Nat) : ℝ≥0∞) := by
  rw [run_messageDigest_cached_first parameter root message randomness cache first hfirst hsecond]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, truncateMessageDigest_eq_join]
  change Pr[(fun suffix => Covered revealed (fullDigestView (joinDigest (first, suffix)))) ∘
    (fun second : HashOutput => second.extractLsb' 0 10) |
    ($ᵗ HashOutput : ProbComp HashOutput)] = _
  rw [← probEvent_map, probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_hashOutput_extract_uniform (width := 10) (by decide))]
  rw [probEvent_uniformSample, card_bitVec]

end LeanSphincs.Security
