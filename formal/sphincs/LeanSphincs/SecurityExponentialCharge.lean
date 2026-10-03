import LeanSphincs.SecurityQueryCharge
import LeanSphincs.SecuritySeedCoupling

/-! Multiplicative probability accounting with the actual source hash-query count. A hidden
monitor may depend on the query answer and cache, while private sampling remains free. -/

namespace LeanSphincs.Security.ExponentialCharge
open OracleComp OracleSpec ENNReal SeedCoupling
set_option backward.isDefEq.respectTransparency false

abbrev HitTest := (input : OracleWorld.Domain) → QueryCache HashSpec →
  OracleWorld.Range input → QueryCache HashSpec → Bool

/-- Return value, original hash calls, monitor hits, and final cache. Internal implementation
queries are deliberately absent from the counter. -/
noncomputable def run {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)) (hit : HitTest)
    (program : OracleComp OracleWorld α) : QueryCache HashSpec →
      ProbComp (α × Nat × Nat × QueryCache HashSpec) :=
  OracleComp.construct (fun value cache => pure (value, 0, 0, cache))
    (fun input _ next cache => do
      let first ← (impl input).run cache
      let last ← next first.1 first.2
      pure (last.1, queryCost input + last.2.1,
        (if hit input cache first.1 first.2 then 1 else 0) + last.2.2.1, last.2.2.2)) program

theorem run_pure {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)) (hit : HitTest)
    (value : α) (cache : QueryCache HashSpec) :
    run impl hit (pure value) cache = pure (value, 0, 0, cache) := rfl

theorem run_query_bind {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)) (hit : HitTest)
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    run impl hit (liftM (OracleWorld.query input) >>= next) cache = (do
      let first ← (impl input).run cache
      let last ← run impl hit (next first.1) first.2
      pure (last.1, queryCost input + last.2.1,
        (if hit input cache first.1 first.2 then 1 else 0) + last.2.2.1, last.2.2.2)) := rfl

/-- The monitor leaves the exact source output/hash-count/cache distribution unchanged. -/
theorem run_erase {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)) (hit : HitTest)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => ((result.1, result.2.1), result.2.2.2)) <$> run impl hit program cache =
      (simulateQ impl (countHashQueries program)).run cache := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [run_pure, countHashQueries, SphincsSecurity.QueryCap.counted_pure,
      simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind input next ih =>
      simp only [run_query_bind, countHashQueries, SphincsSecurity.QueryCap.counted_query_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        map_bind, map_pure]
      apply bind_congr
      intro first
      rw [show (do let last ← run impl hit (next first.1) first.2
                   pure ((last.1, queryCost input + last.2.1), last.2.2.2)) =
          (fun value => ((value.1.1, queryCost input + value.1.2), value.2)) <$>
            ((fun result => ((result.1, result.2.1), result.2.2.2)) <$>
              run impl hit (next first.1) first.2) by
          simp only [Functor.map_map, bind_pure_comp]]
      rw [ih]
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro last
      cases input <;> rfl

/-- Local multiplicative query bounds compose without imposing a bound on private draws. -/
theorem expected_normalized_le {α : Type}
    (impl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp)) (hit : HitTest)
    (base factor : ℝ≥0∞) (hfactor0 : factor ≠ 0) (hfactorTop : factor ≠ ⊤)
    (invariant : QueryCache HashSpec → Prop)
    (hpreserve : ∀ input cache, invariant cache →
      ∀ result ∈ support ((impl input).run cache), invariant result.2)
    (hstep : ∀ input cache, invariant cache →
      (∑' result, Pr[= result | (impl input).run cache] *
        base ^ (if hit input cache result.1 result.2 then 1 else 0)) ≤ factor ^ queryCost input)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hinvariant : invariant cache) :
    (∑' result, Pr[= result | run impl hit program cache] *
      (base ^ result.2.2.1 / factor ^ result.2.1)) ≤ 1 := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [run_pure, tsum_probOutput_pure_mul, pow_zero, div_one, le_rfl]
  | query_bind input next ih =>
      simp only [run_query_bind, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, pow_add]
      have hsplit (first : OracleWorld.Range input × QueryCache HashSpec)
          (last : α × Nat × Nat × QueryCache HashSpec) :
          base ^ (if hit input cache first.1 first.2 then 1 else 0) * base ^ last.2.2.1 /
              (factor ^ queryCost input * factor ^ last.2.1) =
          (base ^ (if hit input cache first.1 first.2 then 1 else 0) / factor ^ queryCost input) *
            (base ^ last.2.2.1 / factor ^ last.2.1) := by
        rw [ENNReal.mul_div_mul_comm (Or.inl (pow_ne_zero _ hfactor0))
          (Or.inl (ENNReal.pow_ne_top hfactorTop))]
      simp_rw [hsplit]
      calc
        _ ≤ ∑' first, Pr[= first | (impl input).run cache] *
            (base ^ (if hit input cache first.1 first.2 then 1 else 0) / factor ^ queryCost input) := by
          apply ENNReal.tsum_le_tsum
          intro first
          by_cases hfirst : first ∈ support ((impl input).run cache)
          · simp_rw [mul_left_comm (Pr[= _ | run impl hit (next first.1) first.2])
              (base ^ (if hit input cache first.1 first.2 then 1 else 0) / factor ^ queryCost input)]
            rw [ENNReal.tsum_mul_left]
            exact mul_le_mul' le_rfl (mul_le_of_le_one_right' (ih first.1 first.2
              (hpreserve input cache hinvariant first hfirst)))
          · rw [probOutput_eq_zero_of_not_mem_support hfirst, zero_mul, zero_mul]
        _ = (∑' first, Pr[= first | (impl input).run cache] *
            base ^ (if hit input cache first.1 first.2 then 1 else 0)) / factor ^ queryCost input := by
          simp only [div_eq_mul_inv, ← mul_assoc]
          rw [ENNReal.tsum_mul_right]
        _ ≤ 1 := by
          exact (ENNReal.div_le_iff (pow_ne_zero _ hfactor0)
            (ENNReal.pow_ne_top hfactorTop)).mpr (by simpa using hstep input cache hinvariant)

/-- A support bound on the actual query counter converts the normalized supermartingale
into an ordinary exponential moment. -/
theorem moment_le_of_normalized {α : Type} (sample : ProbComp α) (cost hits : α → Nat)
    (base factor : ℝ≥0∞) (hfactor : 1 ≤ factor) (hfactor0 : factor ≠ 0)
    (hfactorTop : factor ≠ ⊤) (q : Nat)
    (hcost : ∀ result ∈ support sample, cost result ≤ q)
    (hnormalized : (∑' result, Pr[= result | sample] *
      (base ^ hits result / factor ^ cost result)) ≤ 1) :
    (∑' result, Pr[= result | sample] * base ^ hits result) ≤ factor ^ q := by
  calc
    _ ≤ ∑' result, Pr[= result | sample] *
        ((base ^ hits result / factor ^ cost result) * factor ^ q) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hmem : result ∈ support sample
      · apply mul_le_mul' le_rfl
        calc
          _ = (base ^ hits result / factor ^ cost result) * factor ^ cost result :=
            (ENNReal.div_mul_cancel (pow_ne_zero _ hfactor0) (ENNReal.pow_ne_top hfactorTop)).symm
          _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_right₀ hfactor (hcost result hmem))
      · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = (∑' result, Pr[= result | sample] *
        (base ^ hits result / factor ^ cost result)) * factor ^ q := by
      simp only [← mul_assoc]
      rw [ENNReal.tsum_mul_right]
    _ ≤ factor ^ q := mul_le_of_le_one_left' hnormalized

/-- Markov's inequality in a form avoiding division by the tail threshold. -/
theorem tail_mul_le_moment {α : Type} (sample : ProbComp α) (hits : α → Nat)
    (base : ℝ≥0∞) (hbase : 1 ≤ base) (threshold : Nat) :
    Pr[fun result => threshold ≤ hits result | sample] * base ^ threshold ≤
      ∑' result, Pr[= result | sample] * base ^ hits result := by
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hhit : threshold ≤ hits result
  · simp only [hhit, if_true]
    exact mul_le_mul' le_rfl (pow_le_pow_right₀ hbase hhit)
  · simp only [hhit, if_false, zero_mul]
    exact bot_le

/-- The query-capped tail follows from the normalized local-to-global monitor theorem. -/
theorem tail_le_of_normalized {α : Type} (sample : ProbComp α) (cost hits : α → Nat)
    (base factor : ℝ≥0∞) (hbase : 1 ≤ base) (hbase0 : base ≠ 0) (hbaseTop : base ≠ ⊤)
    (hfactor : 1 ≤ factor) (hfactor0 : factor ≠ 0) (hfactorTop : factor ≠ ⊤) (q threshold : Nat)
    (hcost : ∀ result ∈ support sample, cost result ≤ q)
    (hnormalized : (∑' result, Pr[= result | sample] *
      (base ^ hits result / factor ^ cost result)) ≤ 1) :
    Pr[fun result => threshold ≤ hits result | sample] ≤ factor ^ q / base ^ threshold := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ hbase0))
    (Or.inl (ENNReal.pow_ne_top hbaseTop))).mpr
  exact (tail_mul_le_moment sample hits base hbase threshold).trans
    (moment_le_of_normalized sample cost hits base factor hfactor hfactor0 hfactorTop q hcost hnormalized)

end LeanSphincs.Security.ExponentialCharge
