import LeanSphincs.SecurityPrefixExecution

/-! Relating exact serialized chain witnesses to the observed-prefix event used by the
adaptive probability theorem. The coverage hypothesis concerns queries actually exposed by
the simulated adversary/verifier; it is not filled using internal honest key-generation edges. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open SphincsSecurity.Concrete.PartialChainEndpoint

attribute [local instance] Classical.propDecidable

def Covers (segment : Segment) (observed : Fin segment.digit.val → Digest → Option Digest)
    (f : QueryImpl HashSpec Id) (trace : List HashInput) : Prop :=
  ∀ query, input segment query ∈ trace →
    observed query.1 query.2 = some (truncateHash (f (input segment query)))

noncomputable def observedTrace (segment : Segment) (f : QueryImpl HashSpec Id)
    (trace : List HashInput) : Fin segment.digit.val → Digest → Option Digest :=
  fun step value => if input segment (step, value) ∈ trace then
    some (truncateHash (f (input segment (step, value)))) else none

theorem observedTrace_covers (segment : Segment) (f : QueryImpl HashSpec Id)
    (trace : List HashInput) : Covers segment (observedTrace segment f trace) f trace := by
  intro query hquery
  exact if_pos hquery

/-- A concrete candidate two-edge witness lies in the final observed-prefix event when its
actual input/output pairs were exposed to that observer. No freshness claim is hidden here. -/
theorem twoEdgeEvent_of_covers (segment : Segment)
    (observed : Fin segment.digit.val → Digest → Option Digest)
    (f : QueryImpl HashSpec Id) (trace : List HashInput) (frontier : Digest)
    (hcover : Covers segment observed f trace)
    (hedge : Chain.TwoEdge f segment.parameter segment.lay segment.tree segment.leaf
      segment.chainIdx segment.digit frontier trace) : TwoEdgeEvent observed frontier := by
  obtain ⟨first, second, payload, middle, hnext, hterminal, hfirst, hsecond, houtFirst, houtSecond⟩ := hedge
  rcases segment with ⟨parameter, lay, tree, leaf, chainIdx, ⟨digit, hdigit⟩⟩
  change digit < 4 at hdigit
  change first.val + 1 = second.val at hnext
  change second.val + 1 = digit at hterminal
  interval_cases digit
  · omega
  · omega
  · have hf : first = ⟨0, by decide⟩ := Fin.ext (by change first.val = 0; omega)
    have hs : second = ⟨1, by decide⟩ := Fin.ext (by change second.val = 1; omega)
    subst first; subst second
    refine ⟨payload, middle, ?_, ?_⟩
    · exact (hcover (⟨0, by norm_num⟩, payload) hfirst).trans (congrArg some houtFirst)
    · exact (hcover (⟨1, by norm_num⟩, middle) hsecond).trans (congrArg some houtSecond)
  · have hf : first = ⟨1, by decide⟩ := Fin.ext (by change first.val = 1; omega)
    have hs : second = ⟨2, by decide⟩ := Fin.ext (by change second.val = 2; omega)
    subst first; subst second
    refine ⟨payload, middle, ?_, ?_⟩
    · exact (hcover (⟨1, by norm_num⟩, payload) hfirst).trans (congrArg some houtFirst)
    · exact (hcover (⟨2, by norm_num⟩, middle) hsecond).trans (congrArg some houtSecond)

/-- The byte trace itself determines an observed-prefix event with both linked edges. -/
theorem twoEdgeEvent_observedTrace (segment : Segment) (f : QueryImpl HashSpec Id)
    (trace : List HashInput) (frontier : Digest)
    (hedge : Chain.TwoEdge f segment.parameter segment.lay segment.tree segment.leaf
      segment.chainIdx segment.digit frontier trace) :
    TwoEdgeEvent (observedTrace segment f trace) frontier :=
  twoEdgeEvent_of_covers segment _ f trace frontier (observedTrace_covers segment f trace) hedge

end LeanSphincs.Security.Prefix
