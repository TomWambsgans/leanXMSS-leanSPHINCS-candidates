import LeanSphincs.SecurityQueryCharge
import LeanSphincs.SecurityPrimitive

/-!
Actual counted-program bounds for cached matches against fixed input-indexed target sets.
Targets may be chosen from a prepared initial cache. They must be fixed before this continuation;
the initial cache must contain no matching entry. Canonical inputs can be excluded by assigning
them the empty target set, while other inputs at their tweak receive a singleton target.
-/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.CacheMatch

open Completeness

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def Bad (targets : HashInput → Finset Digest) (cache : QueryCache HashSpec) : Prop :=
  ∃ input answer, cache input = some answer ∧ truncateHash answer ∈ targets input

noncomputable def potential (targets : HashInput → Finset Digest)
    (cache : QueryCache HashSpec) : ℝ≥0∞ := by
  classical
  exact if Bad targets cache then 1 else 0

theorem bad_cacheQuery_iff (targets : HashInput → Finset Digest) (cache : QueryCache HashSpec)
    (input : HashInput) (answer : HashOutput) (hfresh : cache input = none) :
    Bad targets (cache.cacheQuery input answer) ↔ Bad targets cache ∨ truncateHash answer ∈ targets input := by
  constructor
  · rintro ⟨other, value, hcache, hhit⟩
    by_cases heq : other = input
    · subst other
      rw [QueryCache.cacheQuery_self] at hcache
      cases Option.some.inj hcache
      exact Or.inr hhit
    · rw [QueryCache.cacheQuery_of_ne _ _ heq] at hcache
      exact Or.inl ⟨other, value, hcache, hhit⟩
  · rintro (⟨other, value, hcache, hhit⟩ | hhit)
    · have hne : other ≠ input := by
        rintro rfl
        rw [hfresh] at hcache
        contradiction
      exact ⟨other, value, (QueryCache.cacheQuery_of_ne _ _ hne).trans hcache, hhit⟩
    · exact ⟨input, answer, QueryCache.cacheQuery_self _ _ _, hhit⟩

theorem probEvent_hash_query_le (targets : HashInput → Finset Digest) (k : Nat)
    (hcard : ∀ input, (targets input).card ≤ k) (input : HashInput) (cache : QueryCache HashSpec) :
    Pr[fun result => Bad targets result.2 | (randomOracle (spec := HashSpec) input).run cache] ≤
      potential targets cache + (k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  by_cases hbad : Bad targets cache
  · exact probEvent_le_one.trans (by simp [potential, hbad])
  · rw [potential, if_neg hbad, zero_add]
    cases hcache : cache input with
    | some answer =>
        rw [QueryImpl.withCaching_run_some _ hcache]
        simp only [probEvent_pure, hbad, if_false]
        exact zero_le
    | none =>
        rw [QueryImpl.withCaching_run_none _ hcache, probEvent_map]
        have hevent :
            Pr[fun answer : HashOutput => Bad targets (cache.cacheQuery input answer) |
              ($ᵗ HashOutput : ProbComp _)] =
            Pr[fun answer : HashOutput => truncateHash answer ∈ targets input |
              ($ᵗ HashOutput : ProbComp _)] :=
          probEvent_ext (fun answer _ => by simp only [bad_cacheQuery_iff _ _ _ _ hcache, hbad, false_or])
        change Pr[fun answer : HashOutput => Bad targets (cache.cacheQuery input answer) |
          ($ᵗ HashOutput : ProbComp _)] ≤ _
        rw [hevent, probEvent_uniform_truncateHash_mem]
        rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
        exact ENNReal.div_le_div_right (by exact_mod_cast hcard input) _

theorem expected_potential_eq_event {α : Type} (targets : HashInput → Finset Digest)
    (process : ProbComp (α × QueryCache HashSpec)) :
    (∑' result, Pr[= result | process] * potential targets result.2) =
      Pr[fun result => Bad targets result.2 | process] := by
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro result
  by_cases h : Bad targets result.2 <;> simp [potential, h]

theorem expected_query_potential_le (targets : HashInput → Finset Digest) (k : Nat)
    (hcard : ∀ input, (targets input).card ≤ k) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (romImpl input).run cache] * potential targets result.2) ≤
      potential targets cache + queryCost input * ((k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128) := by
  cases input with
  | inl input =>
      change (∑' result : unifSpec.Range input × QueryCache HashSpec,
        Pr[= result | ((unifFwdImpl HashSpec) input).run cache] * potential targets result.2) ≤
        potential targets cache + queryCost (.inl input) * ((k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128)
      simp only [queryCost, Nat.cast_zero, zero_mul, add_zero]
      have h := unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp _) cache
      simp only [simulateQ_spec_query] at h
      rw [h, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
  | inr input =>
      change (∑' result : HashOutput × QueryCache HashSpec,
        Pr[= result | (randomOracle (spec := HashSpec) input).run cache] * potential targets result.2) ≤
        potential targets cache + queryCost (.inr input) * ((k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128)
      simp only [queryCost, Nat.cast_one, one_mul]
      rw [expected_potential_eq_event]
      exact probEvent_hash_query_le targets k hcard input cache

/-- The bound uses the exact full experiment hash counter, including repeated and honest
queries. No syntactic query bound or independence between consecutive inputs is required. -/
theorem counted_program_bound {α : Type} (targets : HashInput → Finset Digest) (k : Nat)
    (hcard : ∀ input, (targets input).card ≤ k) (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hclean : ¬Bad targets cache) (q : Nat)
    (hbound : ∀ result ∈ support (countedRun oa cache), result.1.2 ≤ q) :
    Pr[fun result => Bad targets result.2 | (simulateQ romImpl oa).run cache] ≤
      (q : ℝ≥0∞) * k / (2 : ℝ≥0∞) ^ 128 := by
  rw [← expected_potential_eq_event]
  refine (expected_potential_le_hashCost (potential targets)
    ((k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128) (fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun input cache _ => expected_query_potential_le targets k hcard input cache)
    oa cache trivial).trans ?_
  rw [potential, if_neg hclean, zero_add]
  calc
    _ ≤ (q : ℝ≥0∞) * ((k : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128) :=
      mul_le_mul_left (expectedHashCost_le oa cache q hbound) _
    _ = _ := by rw [mul_div_assoc]

end LeanSphincs.Security.CacheMatch
