import LeanSphincs.SecurityPrefixCountedSign
import SphincsSecurity.Proof.Reference.QueryAllocation

/-! Disjoint allocation of candidate byte queries to all WOTS chain-prefix slices. Summing the
slice costs charges each actual hash call at most once, independent of the number of leaves. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open Concrete SphincsSecurity.QueryCap

def segmentAt (parameter : PublicParameter) (cutoffs : ChainAddress → Digit)
    (chain : ChainAddress) : Segment :=
  ⟨parameter, chain.1, chain.2.1, chain.2.2.1, chain.2.2.2, cutoffs chain⟩

theorem address_segmentAt (parameter : PublicParameter) (cutoffs : ChainAddress → Digit)
    (chain : ChainAddress) : address (segmentAt parameter cutoffs chain) = chain := by
  rcases chain with ⟨lay, tree, leaf, index⟩
  rfl

/-- Private randomness is outside every hidden-chain slice. -/
def SelectedPrefix (segment : Segment) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr bytes => (parse segment bytes).isSome

noncomputable instance (segment : Segment) (input : OracleWorld.Domain) : Decidable (SelectedPrefix segment input) := by
  cases input <;> unfold SelectedPrefix <;> infer_instance

theorem selectedPrefix_hash (segment : Segment) (input : OracleWorld.Domain)
    (hselected : SelectedPrefix segment input) : SourceHash input := by
  cases input with
  | inl _ => exact False.elim hselected
  | inr _ => trivial

/-- Exact serialized chain addresses make the slices disjoint even when their cutoffs differ. -/
theorem selectedPrefix_unique (parameter : PublicParameter) (cutoffs : ChainAddress → Digit)
    (left right : ChainAddress) (input : OracleWorld.Domain)
    (hleft : SelectedPrefix (segmentAt parameter cutoffs left) input)
    (hright : SelectedPrefix (segmentAt parameter cutoffs right) input) : left = right := by
  cases input with
  | inl _ => exact False.elim hleft
  | inr bytes =>
      obtain ⟨leftQuery, hleftQuery⟩ := Option.isSome_iff_exists.mp hleft
      obtain ⟨rightQuery, hrightQuery⟩ := Option.isSome_iff_exists.mp hright
      have hl := (parse_some_iff _ bytes leftQuery).mp hleftQuery
      have hr := (parse_some_iff _ bytes rightQuery).mp hrightQuery
      have heq := hl.symm.trans hr
      obtain ⟨hlay, htree, hleaf, hchain, _⟩ := chainInput_address heq
      rcases left with ⟨lay, tree, leaf, chain⟩
      rcases right with ⟨lay', tree', leaf', chain'⟩
      change lay = lay' at hlay
      change tree = tree' at htree
      change leaf = leaf' at hleaf
      change chain = chain' at hchain
      cases hlay; cases htree; cases hleaf; cases hchain
      rfl

theorem selectedPrefix_sum_le_hash (parameter : PublicParameter) (cutoffs : ChainAddress → Digit)
    (addresses : Finset ChainAddress) (input : OracleWorld.Domain) :
    (∑ chain ∈ addresses, if SelectedPrefix (segmentAt parameter cutoffs chain) input then 1 else 0) ≤
      if SourceHash input then (1 : Nat) else 0 := by
  by_cases hex : ∃ chain ∈ addresses, SelectedPrefix (segmentAt parameter cutoffs chain) input
  · obtain ⟨chain, hchain, hselected⟩ := hex
    rw [Finset.sum_eq_single chain]
    · rw [if_pos hselected, if_pos (selectedPrefix_hash _ input hselected)]
    · intro other _ hother
      rw [if_neg]
      intro hotherSelected
      exact hother (selectedPrefix_unique parameter cutoffs other chain input hotherSelected hselected)
    · intro hmissing
      exact False.elim (hmissing hchain)
  · have hzero : ∀ chain ∈ addresses, ¬SelectedPrefix (segmentAt parameter cutoffs chain) input := by
      intro chain hchain hselected
      exact hex ⟨chain, hchain, hselected⟩
    simp only [Finset.sum_eq_zero (fun chain hchain => if_neg (hzero chain hchain))]
    exact Nat.zero_le _

/-- Summing all selected prefix-query counts introduces no factor for the number of chains
or leaves. Repeated queries are counted each time they occur in the actual byte transcript. -/
theorem prefix_calls_sum_le_hash (parameter : PublicParameter) (cutoffs : ChainAddress → Digit)
    (addresses : Finset ChainAddress) (inputs : List OracleWorld.Domain) :
    (∑ chain ∈ addresses, calls (SelectedPrefix (segmentAt parameter cutoffs chain)) inputs) ≤
      calls SourceHash inputs :=
  calls_sum_le addresses (fun chain => SelectedPrefix (segmentAt parameter cutoffs chain))
    SourceHash (selectedPrefix_sum_le_hash parameter cutoffs addresses) inputs

/-- Pointwise allocation inside a common supported recorded run, ready for taking expectations
under that run's single probability law. -/
theorem recorded_prefix_calls_sum_le {α : Type} (parameter : PublicParameter)
    (cutoffs : ChainAddress → Digit) (addresses : Finset ChainAddress)
    (computation : OracleComp OracleWorld α) (cost : α → Nat)
    (hcost : ∀ result ∈ support (counted SourceHash computation), result.2 ≤ cost result.1)
    (result : α × List OracleWorld.Domain) (hresult : result ∈ support (recorded computation)) :
    (∑ chain ∈ addresses, calls (SelectedPrefix (segmentAt parameter cutoffs chain)) result.2) ≤
      cost result.1 :=
  (prefix_calls_sum_le_hash parameter cutoffs addresses result.2).trans
    (recorded_calls_le SourceHash computation cost hcost result hresult)

end LeanSphincs.Security.Prefix
