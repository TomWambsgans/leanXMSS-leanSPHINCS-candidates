import LeanSphincs.LifetimeBank
import LeanSphincs.SecuritySeedCoupling

/-! Pair completion is an unobserved random-oracle implementation change. At a query to
either message-digest block the other block is also sampled and cached, without exposing
its answer. The complete actual-world output distribution is unchanged, including any
source-level query counter included in the program's return value. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security.SeedCoupling
set_option backward.isDefEq.respectTransparency false

/-- Decode only the two digest domains for this key. The decision is explicitly classical,
so elaboration never enumerates the enormous finite candidate space. -/
noncomputable def decodeCandidateInput (sk : Seeded.SecretKey) (input : HashInput) :
    Option (DigestCandidate × Fin 2) :=
  @dite _ (∃ position : DigestCandidate × Fin 2,
    candidateInput sk position.1 position.2 = input) (Classical.propDecidable _)
    (fun h => some (Classical.choose h)) (fun _ => none)

theorem candidateInput_position_injective (sk : Seeded.SecretKey) :
    Function.Injective (fun position : DigestCandidate × Fin 2 =>
      candidateInput sk position.1 position.2) := by
  intro left right heq
  apply Prod.ext
  · exact candidateInput_candidate_injective sk left.2 right.2 heq
  · have hc := candidateInput_candidate_injective sk left.2 right.2 heq
    rcases left with ⟨left, i⟩
    rcases right with ⟨right, j⟩
    dsimp only at hc ⊢
    subst right
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim ((digestInput_calls_ne sk.parameter sk.root left.1 left.2 left.2) heq.symm)
    · exact False.elim ((digestInput_calls_ne sk.parameter sk.root left.1 left.2 left.2) heq)
    · rfl

theorem decodeCandidateInput_self (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) : decodeCandidateInput sk (candidateInput sk candidate call) = some (candidate, call) := by
  have h : ∃ position : DigestCandidate × Fin 2,
      candidateInput sk position.1 position.2 = candidateInput sk candidate call := ⟨(candidate, call), rfl⟩
  rw [decodeCandidateInput, dif_pos h]
  exact congrArg some (candidateInput_position_injective sk (Classical.choose_spec h))

theorem decodeCandidateInput_some (sk : Seeded.SecretKey) (input : HashInput)
    (position : DigestCandidate × Fin 2) (h : decodeCandidateInput sk input = some position) :
    candidateInput sk position.1 position.2 = input := by
  unfold decodeCandidateInput at h
  split at h
  · rename_i hexists
    cases Option.some.inj h
    exact Classical.choose_spec hexists
  · cases h

def otherDigestCall (call : Fin 2) : Fin 2 := if call = 0 then 1 else 0

theorem otherDigestCall_ne (call : Fin 2) : otherDigestCall call ≠ call := by
  fin_cases call <;> decide

theorem candidate_other_input_ne (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) : candidateInput sk candidate (otherDigestCall call) ≠ candidateInput sk candidate call :=
  by
    intro h
    have heq : (candidate, otherDigestCall call) = (candidate, call) :=
      candidateInput_position_injective sk h
    exact otherDigestCall_ne call (congrArg Prod.snd heq)

noncomputable def pairedHash (sk : Seeded.SecretKey) :
    QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp) := fun input => do
  let answer ← randomOracle input
  match decodeCandidateInput sk input with
  | none => pure answer
  | some position =>
      let _ ← randomOracle (candidateInput sk position.1 (otherDigestCall position.2))
      pure answer

noncomputable def pairedRom (sk : Seeded.SecretKey) :
    QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + pairedHash sk

/-- Exact observational equivalence, valid from any cache including partially cached pairs.
The final internal cache need not be equal because the new interpreter contains latent blocks. -/
theorem evalDist_pairedRom {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    𝒟[(simulateQ romImpl program).run' cache] =
      𝒟[(simulateQ (pairedRom sk) program).run' cache] := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
  | query_bind input next ih =>
      rw [run'_query_bind]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
      cases input with
      | inl input =>
          change 𝒟[((romImpl (.inl input)).run cache) >>= _] =
            𝒟[((romImpl (.inl input)).run cache) >>= _]
          apply evalDist_bind_congr'
          intro result
          exact ih result.1 result.2
      | inr input =>
          change 𝒟[((randomOracle (spec := HashSpec) input).run cache) >>= _] =
            𝒟[((pairedHash sk input).run cache) >>= _]
          simp only [pairedHash, StateT.run_bind, bind_assoc]
          apply evalDist_bind_congr'
          intro result
          cases hp : decodeCandidateInput sk input with
          | none =>
              simp only [hp, StateT.run_pure, pure_bind]
              exact ih result.1 result.2
          | some position =>
              simp only [hp, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
              change 𝒟[(simulateQ romImpl (next result.1)).run' result.2] =
                𝒟[(randomOracle (spec := HashSpec)
                    (candidateInput sk position.1 (otherDigestCall position.2))).run result.2 >>=
                  fun other => (simulateQ (pairedRom sk) (next result.1)).run' other.2]
              rw [evalDist_presample_query (next result.1) result.2
                (candidateInput sk position.1 (otherDigestCall position.2))]
              apply evalDist_bind_congr'
              intro other
              exact ih result.1 other.2

/-- A queried block and its unobserved partner are returned by two consistent cache lookups. -/
theorem pairedHash_candidate_run (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (cache : QueryCache HashSpec) :
    (pairedHash sk (candidateInput sk candidate call)).run cache = (do
      let first ← (randomOracle (spec := HashSpec) (candidateInput sk candidate call)).run cache
      let second ← (randomOracle (spec := HashSpec)
        (candidateInput sk candidate (otherDigestCall call))).run first.2
      pure (first.1, second.2)) := by
  simp only [pairedHash, decodeCandidateInput_self, StateT.run_bind, StateT.run_pure]

/-- At first touch both full blocks are independent uniforms, whichever block is requested. -/
theorem pairedHash_fresh_run (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (cache : QueryCache HashSpec)
    (hfresh : ∀ i, cache (candidateInput sk candidate i) = none) :
    (pairedHash sk (candidateInput sk candidate call)).run cache = (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (first, (cache.cacheQuery (candidateInput sk candidate call) first).cacheQuery
        (candidateInput sk candidate (otherDigestCall call)) second)) := by
  rw [pairedHash_candidate_run, QueryImpl.withCaching_run_none _ (hfresh call)]
  simp only [bind_map_left]
  apply bind_congr
  intro first
  rw [QueryImpl.withCaching_run_none _ ((QueryCache.cacheQuery_of_ne cache first
    (candidate_other_input_ne sk candidate call)).trans (hfresh (otherDigestCall call)))]
  simp only [bind_map_left]
  rfl

/-- The latent complete digest read from an eagerly paired cache. The default is irrelevant
once either block has been touched, as the paired-cache invariant ensures both entries. -/
def cachedPairDigest (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) : MessageDigest :=
  truncateMessageDigest ((cache (candidateInput sk candidate 0)).getD 0)
    ((cache (candidateInput sk candidate 1)).getD 0)

theorem cachedPairDigest_two_updates (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (cache : QueryCache HashSpec) (first second : HashOutput) :
    cachedPairDigest sk candidate
      ((cache.cacheQuery (candidateInput sk candidate 0) first).cacheQuery
        (candidateInput sk candidate 1) second) = truncateMessageDigest first second := by
  have hne : candidateInput sk candidate 0 ≠ candidateInput sk candidate 1 :=
    (digestInput_calls_ne sk.parameter sk.root candidate.1 candidate.2 candidate.2).symm
  rw [cachedPairDigest, QueryCache.cacheQuery_self,
    QueryCache.cacheQuery_of_ne _ _ hne, QueryCache.cacheQuery_self]
  rfl

/-- Exact conditional uniformity of each newly touched latent digest. No independence of
an adaptively selected cached prefix is asserted: this theorem requires both entries fresh. -/
theorem evalDist_pairedHash_fresh_digest (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (call : Fin 2) (cache : QueryCache HashSpec)
    (hfresh : ∀ i, cache (candidateInput sk candidate i) = none) :
    𝒟[(fun result => cachedPairDigest sk candidate result.2) <$>
        (pairedHash sk (candidateInput sk candidate call)).run cache] =
      𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  rw [pairedHash_fresh_run sk candidate call cache hfresh]
  simp only [map_bind, map_pure]
  fin_cases call
  · change 𝒟[(do
        let first ← ($ᵗ HashOutput : ProbComp HashOutput)
        let second ← ($ᵗ HashOutput : ProbComp HashOutput)
        pure (cachedPairDigest sk candidate
          ((cache.cacheQuery (candidateInput sk candidate 0) first).cacheQuery
            (candidateInput sk candidate 1) second)))] = _
    simp_rw [cachedPairDigest_two_updates]
    exact Security.evalDist_digestBlocks_uniform
  · change 𝒟[(do
        let first ← ($ᵗ HashOutput : ProbComp HashOutput)
        let second ← ($ᵗ HashOutput : ProbComp HashOutput)
        pure (cachedPairDigest sk candidate
          ((cache.cacheQuery (candidateInput sk candidate 1) first).cacheQuery
            (candidateInput sk candidate 0) second)))] = _
    have hcomm (first second : HashOutput) :
        (cache.cacheQuery (candidateInput sk candidate 1) first).cacheQuery
          (candidateInput sk candidate 0) second =
        (cache.cacheQuery (candidateInput sk candidate 0) second).cacheQuery
          (candidateInput sk candidate 1) first :=
      cacheQuery_comm cache _ _
        (digestInput_calls_ne sk.parameter sk.root candidate.1 candidate.2 candidate.2) first second
    simp_rw [hcomm, cachedPairDigest_two_updates]
    rw [evalDist_bind_bind_swap]
    exact Security.evalDist_digestBlocks_uniform

end LeanSphincs.Lifetime
