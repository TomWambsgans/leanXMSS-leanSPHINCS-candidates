import LeanSphincs.SecurityDigest

/-!
Adaptive coverage monitoring. A request, including its disclosure table, can depend on the entire
past. The monitor charges a trial only when both of its digest inputs are fresh. Its exact price
is the current fixed-table coverage mass, averaged over the adaptive request distribution.

This separates two obligations of the eventual SUF reduction: bounding that averaged price from
the distribution of honest disclosures, and accounting for cached-block trials. Neither is
assumed to follow from the six lifetime values in this module.
-/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security
open Concrete

/-- All choices fixed before a monitored digest draw. -/
structure CoverageRequest where
  parameter : PublicParameter
  root : Digest
  message : Message
  randomness : Randomness
  revealed : Disclosures

noncomputable def coverageRate (revealed : Disclosures) : ℝ≥0∞ :=
  ((∑ index : Index, ∏ tree : FtsTree, (revealed index tree).card : Nat) : ℝ≥0∞) /
    ((2 ^ 266 : Nat) : ℝ≥0∞)

theorem coverageRate_le_one (revealed : Disclosures) : coverageRate revealed ≤ 1 := by
  rw [coverageRate, ← fresh_fors_coverage]
  exact probEvent_le_one

/-- The monitor ignores trials with a cached block; they belong to a separate exception account.
On a fresh trial it executes the candidate's actual two-query message digest. -/
noncomputable def freshCoverageTrial (request : CoverageRequest) (cache : QueryCache HashSpec) :
    ProbComp (Bool × QueryCache HashSpec) := by
  classical
  exact if DigestFresh request.parameter request.root request.message request.randomness cache then
    (fun result => (decide (Covered request.revealed (fullDigestView result.1)), result.2)) <$>
      (simulateQ randomOracle (messageDigest request.parameter request.root request.message
        request.randomness : OracleComp HashSpec MessageDigest)).run cache
    else pure (false, cache)

/-- Conditional coverage price, zero when the fresh-query account does not apply. -/
noncomputable def freshCoveragePrice (request : CoverageRequest) (cache : QueryCache HashSpec) :
    ℝ≥0∞ := by
  classical
  exact if DigestFresh request.parameter request.root request.message request.randomness cache
    then coverageRate request.revealed else 0

theorem probEvent_freshCoverageTrial (request : CoverageRequest) (cache : QueryCache HashSpec) :
    Pr[fun result => result.1 = true | freshCoverageTrial request cache] =
      freshCoveragePrice request cache := by
  classical
  unfold freshCoverageTrial freshCoveragePrice
  split
  · rename_i hfresh
    simp only [probEvent_map, Function.comp_def, decide_eq_true_eq]
    exact probEvent_messageDigest_covered request.parameter request.root request.message
      request.randomness cache hfresh request.revealed
  · simp

/-- One adaptive phase chooses a request and a new private state after arbitrary earlier work.
The returned cache records that work. It may depend on all previous observations. -/
abbrev CoverageChoice (State : Type) := CoverageRequest × State × QueryCache HashSpec

/-- Exact adaptive law: the one-trial success mass is the expectation of the current price.
There is no independence assumption on the request, disclosure table, or prior cache. -/
theorem probEvent_adaptive_coverage {State : Type} (prepare : ProbComp (CoverageChoice State)) :
    Pr[fun result => result.1 = true |
      prepare >>= fun choice => freshCoverageTrial choice.1 choice.2.2] =
      ∑' choice : CoverageChoice State, Pr[= choice | prepare] *
        freshCoveragePrice choice.1 choice.2.2 := by
  rw [probEvent_bind_eq_tsum]
  exact tsum_congr fun choice => by rw [probEvent_freshCoverageTrial]

/-- An adaptive search for a fresh covered digest. The adversary sees the updated cache before
choosing the next request; its private state is unrestricted. Each phase consumes one trial. -/
noncomputable def adaptiveCoverageSearch {State : Type}
    (prepare : State → QueryCache HashSpec → ProbComp (CoverageChoice State)) :
    Nat → State → QueryCache HashSpec → ProbComp Bool
  | 0, _, _ => pure false
  | n + 1, state, cache => do
      let choice ← prepare state cache
      let result ← freshCoverageTrial choice.1 choice.2.2
      if result.1 then pure true else adaptiveCoverageSearch prepare n choice.2.1 result.2

/-- The adaptive union bound needs an averaged price bound for every reachable history.
This version permits every history, making it convenient to apply under an invariant by
encoding the invariant in the state type. The price hypothesis concerns the explicit finite
disclosure-cardinality formula, rather than an unproved security probability. -/
theorem probEvent_adaptiveCoverageSearch_le {State : Type}
    (prepare : State → QueryCache HashSpec → ProbComp (CoverageChoice State))
    (rate : ℝ≥0∞)
    (hprice : ∀ state cache,
      (∑' choice : CoverageChoice State, Pr[= choice | prepare state cache] *
        freshCoveragePrice choice.1 choice.2.2) ≤ rate) :
    ∀ n state cache,
      Pr[fun result => result = true | adaptiveCoverageSearch prepare n state cache] ≤ n * rate := by
  intro n
  induction n with
  | zero => intro state cache; simp [adaptiveCoverageSearch]
  | succ n ih =>
      intro state cache
      rw [adaptiveCoverageSearch, probEvent_bind_eq_tsum]
      calc
        _ ≤ ∑' choice : CoverageChoice State, Pr[= choice | prepare state cache] *
            (freshCoveragePrice choice.1 choice.2.2 + n * rate) := by
          refine ENNReal.tsum_le_tsum fun choice => mul_le_mul_right ?_ _
          rw [← probEvent_freshCoverageTrial]
          apply probEvent_bind_le_probEvent_add
          intro result _ hresult
          simp only [hresult, if_false]
          exact ih _ _
        _ = (∑' choice : CoverageChoice State, Pr[= choice | prepare state cache] *
            freshCoveragePrice choice.1 choice.2.2) +
            (∑' choice : CoverageChoice State, Pr[= choice | prepare state cache]) * (n * rate) := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ ≤ rate + n * rate := add_le_add (hprice state cache)
          (mul_le_of_le_one_left' tsum_probOutput_le_one)
        _ = (↑(n + 1) : ℝ≥0∞) * rate := by rw [Nat.cast_add, Nat.cast_one]; ring

end LeanSphincs.Security
