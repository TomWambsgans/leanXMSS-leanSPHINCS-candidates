import LeanSphincs.LifetimePairedOracle

/-! The paired-cache invariant and an indicator charging a rectangle only when its candidate
is first touched. Repeated block queries and non-digest queries contribute zero. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness
set_option backward.isDefEq.respectTransparency false

/-- Every candidate has either both digest blocks cached, or neither. -/
def PairedCache (sk : Seeded.SecretKey) (cache : QueryCache HashSpec) : Prop :=
  ∀ candidate, cache (candidateInput sk candidate 0) = none ↔
    cache (candidateInput sk candidate 1) = none

theorem PairedCache.empty (sk : Seeded.SecretKey) : PairedCache sk ∅ := fun _ => Iff.rfl

theorem PairedCache.fresh {sk : Seeded.SecretKey} {cache : QueryCache HashSpec}
    (h : PairedCache sk cache) (candidate : DigestCandidate) (call : Fin 2)
    (hfresh : cache (candidateInput sk candidate call) = none) :
    ∀ i, cache (candidateInput sk candidate i) = none := by
  intro i
  fin_cases call <;> fin_cases i
  · exact hfresh
  · exact (h candidate).mp hfresh
  · exact (h candidate).mpr hfresh
  · exact hfresh

theorem decodeCandidateInput_none_ne (sk : Seeded.SecretKey) (input : HashInput)
    (h : decodeCandidateInput sk input = none) (candidate : DigestCandidate) (call : Fin 2) :
    candidateInput sk candidate call ≠ input := by
  intro heq
  rw [← heq, decodeCandidateInput_self] at h
  cases h

theorem pairedHash_support_cache_le (sk : Seeded.SecretKey) (input : HashInput)
    (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((pairedHash sk input).run cache)) : cache ≤ result.2 := by
  simp only [pairedHash, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hrest⟩ := hresult
  have hf := (query_support_cached input cache first.1 first.2 hfirst).1
  cases hp : decodeCandidateInput sk input with
  | none =>
      simp only [hp, StateT.run_pure, mem_support_pure_iff] at hrest
      cases hrest
      exact hf
  | some position =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, mem_support_pure_iff] at hrest
      obtain ⟨second, hsecond, rfl⟩ := hrest
      exact hf.trans (query_support_cached _ _ _ _ hsecond).1

theorem pairedHash_support_paired (sk : Seeded.SecretKey) (input : HashInput)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((pairedHash sk input).run cache)) : PairedCache sk result.2 := by
  simp only [pairedHash, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hrest⟩ := hresult
  cases hp : decodeCandidateInput sk input with
  | none =>
      simp only [hp, StateT.run_pure, mem_support_pure_iff] at hrest
      cases hrest
      intro candidate
      rw [query_other_cache_eq input _ (decodeCandidateInput_none_ne sk input hp candidate 0) cache first hfirst,
        query_other_cache_eq input _ (decodeCandidateInput_none_ne sk input hp candidate 1) cache first hfirst]
      exact hpaired candidate
  | some position =>
      have hinput := decodeCandidateInput_some sk input position hp
      subst input
      simp only [hp, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, mem_support_pure_iff] at hrest
      obtain ⟨second, hsecond, rfl⟩ := hrest
      have hfirstKnown := (query_support_cached _ _ _ _ hfirst).2
      obtain ⟨hsecondExt, hsecondKnown⟩ := query_support_cached _ _ _ _ hsecond
      have hfirstKept := hsecondExt hfirstKnown
      intro candidate
      by_cases heq : candidate = position.1
      · subst candidate
        rcases position with ⟨candidate, call⟩
        fin_cases call
        · have hfirst0 : second.2 (candidateInput sk candidate 0) = some first.1 := hfirstKept
          have hsecond1 : second.2 (candidateInput sk candidate 1) = some second.1 := hsecondKnown
          simp only [hfirst0, hsecond1, reduceCtorEq]
        · have hfirst1 : second.2 (candidateInput sk candidate 1) = some first.1 := hfirstKept
          have hsecond0 : second.2 (candidateInput sk candidate 0) = some second.1 := hsecondKnown
          simp only [hfirst1, hsecond0, reduceCtorEq]
      · have hother (i j : Fin 2) : candidateInput sk candidate i ≠ candidateInput sk position.1 j :=
          fun h => heq (candidateInput_candidate_injective sk i j h)
        have hunchanged (i : Fin 2) : second.2 (candidateInput sk candidate i) =
            cache (candidateInput sk candidate i) := by
          rw [query_other_cache_eq _ _ (hother i (otherDigestCall position.2)) first.2 second hsecond,
            query_other_cache_eq _ _ (hother i position.2) cache first hfirst]
        rw [hunchanged 0, hunchanged 1]
        exact hpaired candidate

/-- A fresh pair contributes its latent digest event exactly once. -/
noncomputable def pairedHit (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (input : HashInput) (before after : QueryCache HashSpec) : Prop :=
  ∃ position, decodeCandidateInput sk input = some position ∧
    before (candidateInput sk position.1 position.2) = none ∧
    event (cachedPairDigest sk position.1 after)

theorem pairedHit_candidate (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (candidate : DigestCandidate) (call : Fin 2) (before after : QueryCache HashSpec) :
    pairedHit sk event (candidateInput sk candidate call) before after ↔
      before (candidateInput sk candidate call) = none ∧ event (cachedPairDigest sk candidate after) := by
  simp only [pairedHit, decodeCandidateInput_self, Option.some.injEq]
  constructor
  · rintro ⟨position, heq, h⟩
    cases heq
    exact h
  · intro h
    exact ⟨(candidate, call), rfl, h⟩

/-- The exact probability of a fresh recorded rectangle hit, conditional on the past cache. -/
theorem pairedHash_hit_probability (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (input : HashInput) (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) :
    Pr[fun result => pairedHit sk event input cache result.2 | (pairedHash sk input).run cache] =
      match decodeCandidateInput sk input with
      | none => 0
      | some position => if cache (candidateInput sk position.1 position.2) = none then
          Pr[event | ($ᵗ MessageDigest : ProbComp MessageDigest)] else 0 := by
  classical
  cases hp : decodeCandidateInput sk input with
  | none => simp only [pairedHit, hp, reduceCtorEq, false_and, exists_false, probEvent_False]
  | some position =>
      have hinput := decodeCandidateInput_some sk input position hp
      subst input
      simp only [decodeCandidateInput_self]
      by_cases hfresh : cache (candidateInput sk position.1 position.2) = none
      · rw [if_pos hfresh]
        have hevent : (fun result : HashOutput × QueryCache HashSpec =>
            pairedHit sk event (candidateInput sk position.1 position.2) cache result.2) =
            event ∘ (fun result => cachedPairDigest sk position.1 result.2) := by
          funext result
          exact propext ((pairedHit_candidate sk event position.1 position.2 cache result.2).trans (and_iff_right hfresh))
        rw [hevent, ← probEvent_map]
        exact probEvent_congr' (fun _ _ => Iff.rfl)
          (evalDist_pairedHash_fresh_digest sk position.1 position.2 cache (hpaired.fresh _ _ hfresh))
      · simp only [hfresh, if_false]
        have hevent : (fun result : HashOutput × QueryCache HashSpec =>
            pairedHit sk event (candidateInput sk position.1 position.2) cache result.2) = fun _ => False := by
          funext result
          exact propext ((pairedHit_candidate sk event position.1 position.2 cache result.2).trans (by simp [hfresh]))
        rw [hevent, probEvent_False]

theorem pairedHash_hit_le (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (input : HashInput) (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) :
    Pr[fun result => pairedHit sk event input cache result.2 | (pairedHash sk input).run cache] ≤
      Pr[event | ($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  rw [pairedHash_hit_probability sk event input cache hpaired]
  split
  · exact bot_le
  · split <;> exact (by first | exact le_rfl | exact bot_le)

theorem pairedRom_support_paired (sk : Seeded.SecretKey) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache)
    (answer : OracleWorld.Range input) (after : QueryCache HashSpec)
    (hmem : (answer, after) ∈ support ((pairedRom sk input).run cache)) :
    PairedCache sk after ∧ cache ≤ after := by
  cases input with
  | inl input =>
      change (answer, after) ∈ support
        ((fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _)) at hmem
      rw [support_map] at hmem
      obtain ⟨_, _, heq⟩ := hmem
      cases heq
      exact ⟨hpaired, le_rfl⟩
  | inr input =>
      exact ⟨pairedHash_support_paired sk input cache hpaired (answer, after) hmem,
        pairedHash_support_cache_le sk input cache (answer, after) hmem⟩

theorem pairedRun_support_paired {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache)
    (result : α) (after : QueryCache HashSpec)
    (hmem : (result, after) ∈ support ((simulateQ (pairedRom sk) program).run cache)) :
    PairedCache sk after ∧ cache ≤ after := by
  induction program using OracleComp.inductionOn generalizing cache result after with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hmem
      cases hmem
      exact ⟨hpaired, le_rfl⟩
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨first, hfirst, hrest⟩ := hmem
      obtain ⟨hmid, hext⟩ := pairedRom_support_paired sk input cache hpaired first.1 first.2 hfirst
      obtain ⟨hlast, hext'⟩ := ih first.1 first.2 hmid result after hrest
      exact ⟨hlast, hext.trans hext'⟩

end LeanSphincs.Lifetime
