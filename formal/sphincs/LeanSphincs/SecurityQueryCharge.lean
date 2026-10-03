import LeanSphincs.SecurityGameSupport

/-! Expected query charges for the actual counted candidate experiment. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security

open Completeness

def queryCost : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

theorem countedRun_pure {α : Type} (value : α) (cache : QueryCache HashSpec) :
    countedRun (pure value) cache = pure ((value, 0), cache) := rfl

theorem countedRun_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    countedRun (OracleSpec.query input >>= next) cache =
      (romImpl input).run cache >>= fun first =>
        (fun last => ((last.1.1, queryCost input + last.1.2), last.2)) <$>
          countedRun (next first.1) first.2 := by
  cases input <;>
    simp [countedRun, countedOracle, queryCost, simulateQ_bind,
      QueryImpl.withAddCost, QueryImpl.withCost, QueryImpl.withTraceBefore,
      WriterT.run_bind, StateT.run_bind, romImpl, monad_norm] <;> rfl

theorem world_query_failure (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    Pr[⊥ | (romImpl input).run cache] = 0 := by
  cases input with
  | inl input =>
      have h := unifFwdImpl.simulateQ_run
        (hashSpec := HashSpec) (liftM (unifSpec.query input) : ProbComp _) cache
      simp only [simulateQ_spec_query] at h
      change Pr[⊥ | ((unifFwdImpl HashSpec) input).run cache] = 0
      rw [h]
      simp
  | inr input =>
      change Pr[⊥ | (randomOracle (spec := HashSpec) input).run cache] = 0
      cases h : cache input with
      | none => rw [QueryImpl.withCaching_run_none _ h]; simp
      | some answer => rw [QueryImpl.withCaching_run_some _ h]; simp

theorem world_query_mass (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    (∑' result, Pr[= result | (romImpl input).run cache]) = 1 :=
  tsum_probOutput_eq_one' (world_query_failure input cache)

theorem countedRun_failure {α : Type} (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : Pr[⊥ | countedRun oa cache] = 0 := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value => simp [countedRun_pure]
  | query_bind input next ih =>
      rw [countedRun_query_bind, probFailure_bind_eq_add_tsum, world_query_failure]
      simp only [probFailure_map, ih, mul_zero, tsum_zero, add_zero]

theorem countedRun_mass {α : Type} (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : (∑' result, Pr[= result | countedRun oa cache]) = 1 :=
  tsum_probOutput_eq_one' (countedRun_failure oa cache)

noncomputable def expectedHashCost {α : Type} (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  ∑' result, Pr[= result | countedRun oa cache] * (result.1.2 : ℝ≥0∞)

theorem expectedHashCost_pure {α : Type} (value : α) (cache : QueryCache HashSpec) :
    expectedHashCost (pure value) cache = 0 := by
  simp [expectedHashCost, countedRun_pure]

theorem expectedHashCost_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    expectedHashCost (OracleSpec.query input >>= next) cache = queryCost input +
      ∑' first, Pr[= first | (romImpl input).run cache] * expectedHashCost (next first.1) first.2 := by
  rw [expectedHashCost, countedRun_query_bind, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, Nat.cast_add, mul_add, ENNReal.tsum_add,
    ENNReal.tsum_mul_right, countedRun_mass, one_mul]
  simp only [world_query_mass, one_mul,
    expectedHashCost]

theorem expectedHashCost_le {α : Type} (oa : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ result ∈ support (countedRun oa cache), result.1.2 ≤ q) :
    expectedHashCost oa cache ≤ q := by
  calc
    _ ≤ ∑' result, Pr[= result | countedRun oa cache] * (q : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hmem : result ∈ support (countedRun oa cache)
      · exact mul_le_mul_right (by exact_mod_cast hbound result hmem) _
      · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, countedRun_mass, one_mul]

/-- A local expected increase per charged hash call composes across the entire execution.
Private sampling is free, and arbitrary cache invariants are preserved explicitly. -/
theorem expected_potential_le_hashCost {α : Type}
    (potential : QueryCache HashSpec → ℝ≥0∞) (rate : ℝ≥0∞)
    (invariant : QueryCache HashSpec → Prop)
    (hpreserve : ∀ input cache, invariant cache →
      ∀ result ∈ support ((romImpl input).run cache), invariant result.2)
    (hstep : ∀ input cache, invariant cache →
      (∑' result, Pr[= result | (romImpl input).run cache] * potential result.2) ≤
        potential cache + queryCost input * rate)
    (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hinvariant : invariant cache) :
    (∑' result, Pr[= result | (simulateQ romImpl oa).run cache] * potential result.2) ≤
      potential cache + expectedHashCost oa cache * rate := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure value => simp [expectedHashCost_pure]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        expectedHashCost_query_bind]
      calc
        _ ≤ ∑' first, Pr[= first | (romImpl input).run cache] *
            (potential first.2 + expectedHashCost (next first.1) first.2 * rate) := by
          apply ENNReal.tsum_le_tsum
          intro first
          by_cases hmem : first ∈ support ((romImpl input).run cache)
          · exact mul_le_mul_right (ih first.1 first.2 (hpreserve input cache hinvariant first hmem)) _
          · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul, zero_mul]
        _ = (∑' first, Pr[= first | (romImpl input).run cache] * potential first.2) +
            (∑' first, Pr[= first | (romImpl input).run cache] *
              expectedHashCost (next first.1) first.2) * rate := by
          simp_rw [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
        _ ≤ (potential cache + queryCost input * rate) +
            (∑' first, Pr[= first | (romImpl input).run cache] *
              expectedHashCost (next first.1) first.2) * rate :=
          add_le_add (hstep input cache hinvariant) le_rfl
        _ = _ := by rw [add_mul, add_assoc]

/-- A nonnegative terminal potential that covers every successful support outcome bounds
the success probability by its expectation. -/
theorem probEvent_le_expected_potential {α : Type} (process : ProbComp (α × QueryCache HashSpec))
    (event : α → Prop) [DecidablePred event] (potential : QueryCache HashSpec → ℝ≥0∞)
    (hcover : ∀ result ∈ support process, event result.1 → 1 ≤ potential result.2) :
    Pr[fun result => event result.1 | process] ≤
      ∑' result, Pr[= result | process] * potential result.2 := by
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hmem : result ∈ support process
  · by_cases hevent : event result.1
    · rw [if_pos hevent]
      simpa only [mul_one] using mul_le_mul_right (hcover result hmem hevent) (Pr[= result | process])
    · rw [if_neg hevent]; exact zero_le
  · rw [probOutput_eq_zero_of_not_mem_support hmem, zero_mul]
    simp

variable [Params]

attribute [local irreducible] gameCore

theorem expected_game_hashCost_le (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q) : expectedHashCost (gameCore adversary) ∅ ≤ q := by
  apply expectedHashCost_le
  rintro ⟨⟨result, cost⟩, cache⟩ hmem
  exact hashQueryBound_full_run adversary q hbound result cost cache hmem

/-- The actual security experiment obeys any proved local query-charge argument with a
successful-outcome covering potential. This shares the same counted budget across all events;
constructing such a potential and proving its local bound remain reduction obligations. -/
theorem forgeAdvantage_le_of_potential (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound adversary q)
    (potential : QueryCache HashSpec → ℝ≥0∞) (rate : ℝ≥0∞)
    (invariant : QueryCache HashSpec → Prop) (hinitial : invariant ∅)
    (hzero : potential ∅ = 0)
    (hpreserve : ∀ input cache, invariant cache →
      ∀ result ∈ support ((romImpl input).run cache), invariant result.2)
    (hstep : ∀ input cache, invariant cache →
      (∑' result, Pr[= result | (romImpl input).run cache] * potential result.2) ≤
        potential cache + queryCost input * rate)
    (hcover : ∀ result ∈ support ((simulateQ romImpl (gameCore adversary)).run ∅),
      result.1 = true → 1 ≤ potential result.2) :
    forgeAdvantage adversary ≤ (q : ℝ≥0∞) * rate := by
  rw [forgeAdvantage_eq_uncounted]
  refine (probEvent_le_expected_potential
    ((simulateQ romImpl (gameCore adversary)).run ∅)
    (fun value : Bool => value = true) potential hcover).trans ?_
  refine (expected_potential_le_hashCost potential rate invariant hpreserve hstep
    (gameCore adversary) ∅ hinitial).trans ?_
  rw [hzero, zero_add]
  exact mul_le_mul_left (expected_game_hashCost_le adversary q hbound) rate

end LeanSphincs.Security
