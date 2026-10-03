import LeanSphincs.LifetimePairedAgreement
import LeanSphincs.LifetimePoolOccupancy
import LeanSphincs.LifetimeSources

/-! Actual complete signing calls under a balanced first-block table. The recorded position
comes from the accepted digest, including calls whose later WOTS assembly exhausts. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable [Params]

theorem poolGrindRandomness_map (parameter : PublicParameter) (pool : IndexPool) (attempts : Nat) :
    (Option.map pool) <$> poolGrindRandomness parameter pool attempts = poolGrind parameter pool attempts := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      simp only [poolGrindRandomness, poolGrind, map_bind]
      apply bind_congr
      intro rho
      split <;> simp only [map_pure, Option.map_some, ih]

theorem poolGrind_support_landed (parameter : PublicParameter) (pool : IndexPool)
    (attempts : Nat) (index : Index) (hmem : some index ∈ support (poolGrind parameter pool attempts)) :
    Landed parameter index := by
  induction attempts with
  | zero => simp only [poolGrind, mem_support_pure_iff, reduceCtorEq] at hmem
  | succ attempts ih =>
      simp only [poolGrind, mem_support_bind_iff] at hmem
      obtain ⟨rho, _, hmem⟩ := hmem
      split at hmem
      · rename_i hland
        simp only [mem_support_pure_iff, Option.some.injEq] at hmem
        cases hmem
        exact hland
      · exact ih hmem

theorem balanced_poolGrind_index_bound_all (parameter : PublicParameter) (pool : IndexPool)
    (hbalanced : PoolBalanced pool) (index : Index) (attempts : Nat) :
    Pr[fun result => result = some index | poolGrind parameter pool attempts] ≤
      ENNReal.ofReal ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ subtreeHeight) := by
  by_cases hland : Landed parameter index
  · have h := balanced_poolGrind_index_bound parameter pool hbalanced index hland attempts
    have hnum : ENNReal.ofReal (1 + (1 : ℝ) / 2 ^ 18) = 1 + (1 : ℝ≥0∞) / 2 ^ 18 := by
      rw [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 18),
        ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 18)]
      norm_num
    simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ subtreeHeight), hnum,
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      Nat.cast_pow, Nat.cast_ofNat] using h
  · have hzero : Pr[fun result => result = some index | poolGrind parameter pool attempts] = 0 := by
      apply probEvent_eq_zero
      intro result hresult heq
      subst result
      exact hland (poolGrind_support_landed parameter pool attempts index hresult)
    rw [hzero]
    exact bot_le

noncomputable def indexedSign (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    ProbComp (Option Index × Option Signature × QueryCache HashSpec) :=
  (fun result => (result.2.1.head?.map (fun record => digestIndex record.digest), result.1, result.2.2)) <$>
    signWithSources sk message ([], cache)

/-- Recording an accepted position leaves the actual response and shared cache unchanged. -/
theorem indexedSign_erase (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    Prod.snd <$> indexedSign sk message cache =
      (simulateQ romImpl (Randomized.sign sk message)).run cache := by
  rw [indexedSign, Functor.map_map]
  exact signWithSources_forget sk message ([], cache)

theorem indexedSign_cache_le (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (result : Option Index × Option Signature × QueryCache HashSpec)
    (hresult : result ∈ support (indexedSign sk message cache)) : cache ≤ result.2.2 := by
  apply world_support_cache_le (Randomized.sign sk message) cache result.2.1 result.2.2
  rw [← indexedSign_erase, support_map]
  exact ⟨result, hresult, rfl⟩

theorem prepared_messageDigest_index (table : FirstPoolTable) (sk : Seeded.SecretKey)
    (message : Message) (rho : Randomness) (cache : QueryCache HashSpec)
    (hcache : firstPoolCache table ≤ cache) (result : MessageDigest × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ randomOracle
      (messageDigest sk.parameter sk.root message rho : OracleComp HashSpec MessageDigest)).run cache)) :
    digestIndex result.1 = firstPoolIndexes table (sk.parameter, sk.root, message) rho := by
  obtain ⟨hext, first, second, hfirst, _, hdigest⟩ := messageDigest_support_source sk message rho cache result hresult
  have htable := hext (hcache (firstPoolCache_apply table ((sk.parameter, sk.root, message), rho)))
  have hinput : firstPoolInput ((sk.parameter, sk.root, message), rho) = candidateInput sk (message, rho) 0 := rfl
  rw [hinput, hfirst] at htable
  have heq := Option.some.inj htable
  rw [hdigest, digestIndex_truncate, heq]
  rfl

/-- The position marginal of the complete actual signer is precisely its grinding pool law. -/
theorem indexedSign_prepared_index (table : FirstPoolTable) (sk : Seeded.SecretKey)
    (message : Message) (cache : QueryCache HashSpec) (hcache : firstPoolCache table ≤ cache)
    (index : Index) :
    Pr[fun result => result.1 = some index | indexedSign sk message cache] =
      Pr[fun result => result = some index |
        poolGrind sk.parameter (firstPoolIndexes table (sk.parameter, sk.root, message)) digestAttemptLimit] := by
  rw [indexedSign, probEvent_map]
  simp only [Function.comp_def, signWithSources,
    run_signDigestLoop_firstPool table sk message digestAttemptLimit cache hcache, bind_map_left]
  rw [← poolGrindRandomness_map, probEvent_map]
  simp only [probEvent_bind_eq_tsum, Function.comp_def]
  rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro loop
  cases loop with
  | none => simp only [probEvent_pure, List.head?_nil, Option.map_none, reduceCtorEq, if_false, mul_zero]
  | some rho =>
      have hfixed : Pr[fun result : MessageDigest × QueryCache HashSpec => digestIndex result.1 = index |
          (simulateQ randomOracle
            (messageDigest sk.parameter sk.root message rho : OracleComp HashSpec MessageDigest)).run cache] =
          if firstPoolIndexes table (sk.parameter, sk.root, message) rho = index then 1 else 0 := by
        trans Pr[fun _ : MessageDigest × QueryCache HashSpec =>
          firstPoolIndexes table (sk.parameter, sk.root, message) rho = index |
            (simulateQ randomOracle
              (messageDigest sk.parameter sk.root message rho : OracleComp HashSpec MessageDigest)).run cache]
        · apply probEvent_congr' _ rfl
          intro result hresult
          rw [prepared_messageDigest_index table sk message rho cache hcache result hresult]
        · rw [probEvent_const, probFailure_of_liftM_PMF, tsub_zero]
      simp only [probEvent_bind_eq_tsum, probEvent_pure, List.head?_cons, Option.map_some, Option.some.injEq]
      have hbody (digest : MessageDigest × QueryCache HashSpec) :
          (∑' result, Pr[= result | (simulateQ randomOracle (finishSignBody sk rho digest.1)).run digest.2] *
            (if digestIndex digest.1 = index then (1 : ℝ≥0∞) else 0)) =
            if digestIndex digest.1 = index then 1 else 0 := by
        rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      simp_rw [hbody]
      simp only [mul_ite, mul_one, mul_zero]
      rw [← probEvent_eq_tsum_ite, hfixed]
      split_ifs <;> simp only [mul_one, mul_zero]

theorem indexedSign_prepared_bound (table : FirstPoolTable) (hbalanced : AllPoolsBalanced (firstPoolIndexes table))
    (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcache : firstPoolCache table ≤ cache) (index : Index) :
    Pr[fun result => result.1 = some index | indexedSign sk message cache] ≤
      ENNReal.ofReal ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ subtreeHeight) := by
  rw [indexedSign_prepared_index table sk message cache hcache index]
  exact balanced_poolGrind_index_bound_all sk.parameter _ (hbalanced _) index _

end LeanSphincs.Lifetime
