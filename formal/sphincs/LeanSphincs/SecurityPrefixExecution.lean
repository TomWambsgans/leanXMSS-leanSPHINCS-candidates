import LeanSphincs.SecurityPrefixSampling
import SphincsSecurity.Proof.Chains.AdaptiveChainCapTwoEdge
import SphincsSecurity.Proof.Chains.AdaptiveChainErasure

/-!
Candidate byte-query translation and adaptive hidden-prefix bounds. Private sampling requests
are forwarded unchanged. Each candidate hash call becomes exactly one outside or prefix query.
The probability theorem applies to a computation supplied only the selected chain endpoint;
proving that the actual signing transcript admits this endpoint-only simulation is separate.
-/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.Prefix
open SphincsSecurity.Concrete.PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false

abbrev World (segment : Segment) := OracleWorld + PrefixSpec segment.digit.val Digest

noncomputable local instance (segment : Segment) : IsUniformSpec (World segment) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable def splitWorld (segment : Segment) (high : Query segment → High) :
    QueryImpl OracleWorld (OracleComp (World segment))
  | .inl sample => liftM ((World segment).query (.inl (.inl sample)))
  | .inr bytes => match parse segment bytes with
    | none => liftM ((World segment).query (.inl (.inr bytes)))
    | some query => do
        let low ← liftM ((World segment).query (.inr query))
        pure (combine low (high query))

/-- Source-side hash calls, excluding private uniform samples. -/
def SourceHash : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance (input : OracleWorld.Domain) : Decidable (SourceHash input) := by
  cases input <;> unfold SourceHash <;> infer_instance

/-- Target-side hash calls count either the outside or the selected-prefix branch once. -/
def SplitHash (segment : Segment) : (World segment).Domain → Prop
  | .inl input => SourceHash input
  | .inr _ => True

instance (segment : Segment) (input : (World segment).Domain) : Decidable (SplitHash segment input) := by
  cases input <;> simp only [SplitHash] <;> infer_instance

theorem splitWorld_hash_step (segment : Segment) (high : Query segment → High)
    (bytes : HashInput) :
    (splitWorld segment high (.inr bytes)).IsQueryBoundP (SplitHash segment) 1 := by
  cases hparse : parse segment bytes <;>
    simp [splitWorld, hparse, SplitHash, SourceHash]

theorem splitWorld_sample_step (segment : Segment) (high : Query segment → High) (sample : Nat) :
    (splitWorld segment high (.inl sample)).IsQueryBoundP (SplitHash segment) 0 := by
  simp [splitWorld, SplitHash, SourceHash]

/-- Translation preserves the source hash-query budget without counting private samples. -/
theorem splitWorld_hash_bound (segment : Segment) (high : Query segment → High)
    {α : Type} (oa : OracleComp OracleWorld α) (budget : Nat)
    (hbound : oa.IsQueryBoundP SourceHash budget) :
    (simulateQ (splitWorld segment high) oa).IsQueryBoundP (SplitHash segment) budget := by
  apply IsQueryBoundP.simulateQ_of_step hbound
  · intro input hinput
    cases input with
    | inl sample => exact False.elim hinput
    | inr bytes => exact splitWorld_hash_step segment high bytes
  · intro input hinput
    cases input with
    | inl sample => exact splitWorld_sample_step segment high sample
    | inr bytes => exact False.elim (hinput trivial)

/-- Only selected-prefix queries are charged by the prefix analysis; all of them are source
hash calls. Outside hashes and private samples remain available to the adaptive computation. -/
theorem splitWorld_prefix_bound (segment : Segment) (high : Query segment → High)
    {α : Type} (oa : OracleComp OracleWorld α) (budget : Nat)
    (hbound : oa.IsQueryBoundP SourceHash budget) :
    (simulateQ (splitWorld segment high) oa).IsQueryBoundP IsPrefixQuery budget := by
  apply IsQueryBoundP.simulateQ_of_step hbound
  · intro input hinput
    cases input with
    | inl sample => exact False.elim hinput
    | inr bytes =>
        cases hparse : parse segment bytes <;> simp [splitWorld, hparse, IsPrefixQuery]
  · intro input hinput
    cases input with
    | inl sample => simp [splitWorld, IsPrefixQuery]
    | inr bytes => exact False.elim (hinput trivial)

/-- The byte-level world interpreter associated to fixed hidden transition tables. -/
noncomputable def tableWorld (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (auxiliary : QueryImpl OracleWorld PMF) : QueryImpl OracleWorld PMF
  | .inl sample => auxiliary (.inl sample)
  | .inr bytes => match parse segment bytes with
    | none => auxiliary (.inr bytes)
    | some query => PMF.pure (combine (tables query.1 query.2) (high query))

theorem fixedImpl_splitWorld (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (auxiliary : QueryImpl OracleWorld PMF) (input : OracleWorld.Domain) :
    simulateQ (fixedImpl auxiliary tables) (splitWorld segment high input) =
      tableWorld segment tables high auxiliary input := by
  cases input with
  | inl sample => simp [splitWorld, tableWorld, fixedImpl]
  | inr bytes =>
      cases hparse : parse segment bytes <;>
        simp [splitWorld, hparse, tableWorld, fixedImpl, ← PMF.monad_pure_eq_pure]

/-- Exact execution equivalence, including private uniform queries and all full hash outputs. -/
theorem simulate_splitWorld (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (auxiliary : QueryImpl OracleWorld PMF) {α : Type} (oa : OracleComp OracleWorld α) :
    simulateQ (fixedImpl auxiliary tables) (simulateQ (splitWorld segment high) oa) =
      simulateQ (tableWorld segment tables high auxiliary) oa := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext input
  exact fixedImpl_splitWorld segment tables high auxiliary input

/-- Fresh private uniform sampling together with a supplied fixed hash function. -/
noncomputable def fixedHashWorld (outside : QueryImpl HashSpec Id) : QueryImpl OracleWorld PMF
  | .inl _sample => PMF.uniformOfFintype _
  | .inr bytes => PMF.pure (outside bytes)

theorem tableWorld_fixedHashWorld (segment : Segment)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (outside : QueryImpl HashSpec Id) :
    tableWorld segment tables high (fixedHashWorld outside) =
      fixedHashWorld (answer segment tables high outside) := by
  funext input
  cases input with
  | inl sample => rfl
  | inr bytes => cases hparse : parse segment bytes <;>
      simp only [tableWorld, fixedHashWorld, answer, hparse]

/-- The real adaptive prefix experiment is exactly independent sampling of the hidden tables
and secret, followed by execution of the original candidate byte program. Only its endpoint
is supplied to the program and the outside oracle; private random sampling remains inside. -/
theorem realRun_byte_distribution (segment : Segment) (high : Query segment → High)
    (outside : Digest → QueryImpl HashSpec Id) {α : Type}
    (computation : Digest → OracleComp OracleWorld α) :
    (realRun (fun endpoint => fixedHashWorld (outside endpoint))
      (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint))
      (fun _ _ => none)).map (fun result => result.2.1) =
    (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
      (PMF.uniformOfFintype Digest).bind (fun secret =>
        simulateQ (fixedHashWorld (answer segment tables high (outside (evaluate tables secret))))
          (computation (evaluate tables secret)))) := by
  rw [realRun_empty_forget]
  simp only [simulate_splitWorld, tableWorld_fixedHashWorld]

private theorem counted_query {ι : Type} {spec : OracleSpec ι}
    (selected : ι → Prop) [DecidablePred selected] (input : ι) :
    SphincsSecurity.QueryCap.counted selected (liftM (spec.query input) : OracleComp spec (spec.Range input)) =
      (do let value ← liftM (spec.query input); pure (value, if selected input then 1 else 0)) := rfl

/-- Exact preservation of the complete hash-call count, including repeated queries. -/
theorem counted_splitWorld (segment : Segment) (high : Query segment → High)
    {α : Type} (oa : OracleComp OracleWorld α) :
    SphincsSecurity.QueryCap.counted (SplitHash segment) (simulateQ (splitWorld segment high) oa) =
      simulateQ (splitWorld segment high) (SphincsSecurity.QueryCap.counted SourceHash oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, SphincsSecurity.QueryCap.counted_pure]
  | query_bind input next ih =>
      cases input with
      | inl sample =>
          simp only [simulateQ_bind, simulateQ_spec_query, splitWorld,
            SphincsSecurity.QueryCap.counted_query_bind, SplitHash, SourceHash,
            if_false, zero_add, ih, simulateQ_pure]
          rfl
      | inr bytes =>
          cases hparse : parse segment bytes <;>
            simp only [simulateQ_bind, simulateQ_spec_query, splitWorld, hparse,
              SphincsSecurity.QueryCap.counted_bind, counted_query,
              SplitHash, SourceHash,
              if_true, ih, simulateQ_pure, bind_assoc, pure_bind]
          all_goals rfl

noncomputable def twoEdgeRate (budget : Nat) : ENNReal :=
  ((3 / 2 : ENNReal) + 4 * ((budget : ENNReal) / 2 ^ 128) +
    2 * ((budget : ENNReal) / 2 ^ 128) ^ 2) / 2 ^ 128

/-- Adaptive two-edge charging for the exact candidate byte translation. The computation and
auxiliary oracle may depend on the disclosed endpoint, but do not take the hidden tables or
secret as inputs. The observed prefix starts empty; existing honest prefix edges cannot be
inserted into it and then counted as a new exceptional event. -/
theorem splitWorld_twoEdge_bound (segment : Segment) (high : Query segment → High)
    {α : Type} (auxiliary : Digest → QueryImpl OracleWorld PMF)
    (computation : Digest → OracleComp OracleWorld α) (cost : α → Nat) (budget : Nat)
    (hcharge : ∀ endpoint result, result ∈ support
      (SphincsSecurity.QueryCap.counted IsPrefixQuery
        (simulateQ (splitWorld segment high) (computation endpoint))) → result.2 ≤ cost result.1)
    (hreal : ∀ result ∈ (realRun auxiliary
      (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint))
      (fun _ _ => none)).support, cost result.2.1 ≤ budget)
    (hsmall : budget < 2 ^ 128) :
    Pr[fun result => TwoEdgeEvent result.2.2 result.1 |
      realRun auxiliary (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint))
        (fun _ _ => none)] ≤
      twoEdgeRate budget * ∑' result,
        idealRun auxiliary (fun endpoint => SphincsSecurity.QueryCap.run IsPrefixQuery
          (simulateQ (splitWorld segment high) (computation endpoint)) budget)
          (fun _ _ => none) result *
            (SphincsSecurity.QueryCap.spent budget result.2.1 : ENNReal) := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have h := realRun_twoEdgeEvent_le_cap_cost auxiliary
    (fun endpoint => simulateQ (splitWorld segment high) (computation endpoint))
    cost budget hcharge hreal (by simpa only [hcard] using hsmall)
  simpa only [twoEdgeRate, hcard, Nat.cast_pow, Nat.cast_ofNat] using h

end LeanSphincs.Security.Prefix
