import LeanSphincs.SecurityPrefixAllocation
import SphincsSecurity.Proof.Chains.AdaptiveChainCapCost

/-! Transfer each ideal prefix cost back to its real run, paying the explicit factor
`1-q/2^128`. The byte translator preserves the selected-slice count exactly, so later coupling
to a common actual transcript can use the disjoint address allocation. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.Prefix
open SphincsSecurity.Concrete.PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false

private theorem counted_query {I : Type} {spec : OracleSpec I}
    (selected : I → Prop) [DecidablePred selected] (input : I) :
    SphincsSecurity.QueryCap.counted selected (liftM (spec.query input) : OracleComp spec (spec.Range input)) =
      (do let value ← liftM (spec.query input); pure (value, if selected input then 1 else 0)) := rfl

/-- The translated prefix monitor counts exactly those original bytes parsed into this slice. -/
theorem countedPrefix_splitWorld (segment : Segment) (high : Query segment → High)
    {α : Type} (computation : OracleComp OracleWorld α) :
    SphincsSecurity.QueryCap.counted IsPrefixQuery (simulateQ (splitWorld segment high) computation) =
    simulateQ (splitWorld segment high) (SphincsSecurity.QueryCap.counted (SelectedPrefix segment) computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure]
  | query_bind input next ih =>
      cases input with
      | inl sample =>
          simp only [simulateQ_bind, simulateQ_spec_query, splitWorld,
            SphincsSecurity.QueryCap.counted_query_bind, SelectedPrefix, IsPrefixQuery,
            if_false, zero_add, ih, simulateQ_pure]
          rfl
      | inr bytes =>
          cases hparse : parse segment bytes <;>
            simp only [simulateQ_bind, simulateQ_spec_query, splitWorld, hparse,
              SphincsSecurity.QueryCap.counted_bind, counted_query,
              SelectedPrefix, IsPrefixQuery,
              Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
              if_false, if_true, ih, simulateQ_pure, bind_assoc, pure_bind]
          all_goals rfl

/-- The real slice's result/count marginal is exactly the original candidate byte program
under independently sampled transition rows and selected secret. -/
theorem realRun_counted_byte_distribution (segment : Segment) (high : Query segment → High)
    (outside : Digest → QueryImpl HashSpec Id) {α : Type}
    (computation : Digest → OracleComp OracleWorld α) :
    (realRun (fun endpoint => fixedHashWorld (outside endpoint))
      (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (splitWorld segment high) (computation endpoint))) (fun _ _ => none)).map
      (fun result => result.2.1) =
    (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
      (PMF.uniformOfFintype Digest).bind (fun secret =>
        simulateQ (fixedHashWorld (answer segment tables high (outside (evaluate tables secret))))
          (SphincsSecurity.QueryCap.counted (SelectedPrefix segment) (computation (evaluate tables secret))))) := by
  simp only [countedPrefix_splitWorld]
  exact realRun_byte_distribution segment high outside
    (fun endpoint => SphincsSecurity.QueryCap.counted (SelectedPrefix segment) (computation endpoint))

theorem splitWorld_ideal_spent_lower (segment : Segment) (high : Query segment → High)
    {α : Type} (auxiliary : Digest → QueryImpl OracleWorld PMF)
    (computation : Digest → OracleComp OracleWorld α) (cost : α → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support
      (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (splitWorld segment high) (computation endpoint))) → result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary
      (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint))
      (fun _ _ => none)).support, cost result.2.1 ≤ budget) :
    (1 - (budget : ENNReal) / 2 ^ 128) *
      (∑' result, idealRun auxiliary (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery
        (simulateQ (splitWorld segment high) (computation endpoint)) budget)
        (fun _ _ => none) result * (SphincsSecurity.QueryCap.spent budget result.2.1 : ENNReal)) ≤
    ∑' result, realRun auxiliary (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery
      (simulateQ (splitWorld segment high) (computation endpoint)))
      (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have h := idealRun_cap_spent_lower auxiliary
    (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint)) cost budget hcharge hreal
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Cost transfer removes the separate ideal expectation from the adaptive two-edge bound.
The remaining cost is measured by this slice's real execution law. -/
theorem splitWorld_twoEdge_bound_real_cost (segment : Segment) (high : Query segment → High)
    {α : Type} (auxiliary : Digest → QueryImpl OracleWorld PMF)
    (computation : Digest → OracleComp OracleWorld α) (cost : α → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support
      (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (splitWorld segment high) (computation endpoint))) → result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary
      (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint))
      (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < 2 ^ 128) :
    (1 - (budget : ENNReal) / 2 ^ 128) * Pr[fun result => TwoEdgeEvent result.2.2 result.1 |
      realRun auxiliary (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint))
        (fun _ _ => none)] ≤
    twoEdgeRate budget * ∑' result,
      realRun auxiliary (fun endpoint => SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (splitWorld segment high) (computation endpoint)))
        (fun _ _ => none) result * (result.2.1.2 : ENNReal) := by
  have hbound := mul_le_mul_right
    (splitWorld_twoEdge_bound segment high auxiliary computation cost budget hcharge hreal hsmall)
    (1 - (budget : ENNReal) / 2 ^ 128)
  apply hbound.trans
  rw [mul_left_comm]
  exact mul_le_mul_right
    (splitWorld_ideal_spent_lower segment high auxiliary computation cost budget hcharge hreal)
    (twoEdgeRate budget)

end LeanSphincs.Security.Prefix
