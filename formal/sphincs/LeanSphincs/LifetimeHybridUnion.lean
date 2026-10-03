import LeanSphincs.LifetimeHybridOccupancy
import LeanSphincs.LifetimeLocalizedGain

/-! Summing every real-prefix/uniform-suffix localization error, with the exact requested
lifetimes. A common-space corollary applies only when its projection couplings are supplied. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 512
attribute [local instance] Classical.propDecidable

/-- Numeric reserve for all N+1 possible positions of a hybrid switch. -/
theorem requested_hybrid_union_budget {b n : Nat} (hpair : (b, n) ∈ requestedLifetimePairs) :
    ((n + 1 : Nat) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 400 + 1 / 2 ^ 294) ≤ 1 / 2 ^ 263 := by
  have hn : n ≤ 1200000000 := by
    simp only [requestedLifetimePairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hpair
    rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  calc
    _ ≤ (1200000001 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 400 + 1 / 2 ^ 294) := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast Nat.add_le_add_right hn 1
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_add, ENNReal.toReal_div, ENNReal.toReal_pow]

variable [Params]

/-- The sum bound does not require the hybrids to share their private samples. -/
theorem actual_hybrid_occupancy_sum {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State) :
    (∑ suffix : Fin (n + 1), Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) |
      adaptiveIndexTrace (hybridIndexStep sk interlude update (fun remaining => decide (suffix.val ≤ remaining)))
        n (state, ∅)]) ≤ 1 / (2 : ℝ≥0∞) ^ 263 := by
  calc
    _ ≤ ∑ _suffix : Fin (n + 1), ((1 : ℝ≥0∞) / 2 ^ 400 + 1 / 2 ^ 294) := by
      apply Finset.sum_le_sum
      intro suffix _
      exact actual_hybrid_occupancy sk interlude update _ n hpair state
    _ = ((n + 1 : Nat) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 400 + 1 / 2 ^ 294) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := requested_hybrid_union_budget hpair

/-- For a proposed common experiment, its full index-trace marginal couplings are the only
additional obligation needed to union over every hybrid switch in that experiment. -/
theorem common_hybrid_occupancy {State α : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State)
    (sample : ProbComp α) (traces : Fin (n + 1) → α → List (Option Index))
    (hprojection : ∀ suffix, 𝒟[traces suffix <$> sample] =
      𝒟[adaptiveIndexTrace (hybridIndexStep sk interlude update (fun remaining => decide (suffix.val ≤ remaining)))
        n (state, ∅)]) :
    Pr[fun result => ∃ suffix index, 256 ≤ (traces suffix result).count (some index) | sample] ≤
      1 / (2 : ℝ≥0∞) ^ 263 := by
  have h := probEvent_exists_finset_le_sum Finset.univ sample
    (fun suffix result => ∃ index, 256 ≤ (traces suffix result).count (some index))
  simp only [Finset.mem_univ, true_and] at h
  refine h.trans ?_
  have heq (suffix : Fin (n + 1)) :
      Pr[fun result => ∃ index, 256 ≤ (traces suffix result).count (some index) | sample] =
        Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) |
          adaptiveIndexTrace (hybridIndexStep sk interlude update (fun remaining => decide (suffix.val ≤ remaining)))
            n (state, ∅)] := by
    rw [show (fun result => ∃ index, 256 ≤ (traces suffix result).count (some index)) =
      (fun trace => ∃ index, 256 ≤ trace.count (some index)) ∘ traces suffix from rfl, ← probEvent_map]
    exact probEvent_congr' (fun _ _ => Iff.rfl) (hprojection suffix)
  simp_rw [heq]
  exact actual_hybrid_occupancy_sum sk interlude update n hpair state

/-- Distinct-view occupancy is no larger than the occurrence count of its local index. -/
theorem list_view_count_le (views : List KeptDigestView) (index : Fin (2 ^ subtreeHeight)) :
    (views.toFinset.filter (fun view => view.1 = index)).card ≤ (views.map Prod.fst).count index := by
  have hfilter : views.toFinset.filter (fun view => view.1 = index) =
      (views.filter (fun view => decide (view.1 = index))).toFinset := by
    ext view
    simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  rw [hfilter]
  refine (List.toFinset_card_le _).trans_eq ?_
  clear hfilter
  induction views with
  | nil => rfl
  | cons view views ih =>
      by_cases hindex : view.1 = index
      · simp only [List.filter_cons, hindex, decide_true, ↓reduceIte, List.length_cons,
          List.map_cons, List.count_cons, beq_self_eq_true, ↓reduceIte, ih]
      · simp only [List.filter_cons, hindex, decide_false, ↓reduceIte, List.map_cons,
          List.count_cons, beq_iff_eq, ih, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

/-- A positional cap on the actual plus independent view list implies the cap used by
`futureOverflow`; duplicates in the proof-side view set only reduce its occupancy. -/
theorem viewCap_of_list_counts (views : List KeptDigestView)
    (hcounts : ∀ index, (views.map Prod.fst).count index < 256) : ViewCap 255 views.toFinset := by
  intro index
  have h := (list_view_count_le views index).trans_lt (hcounts index)
  omega

end LeanSphincs.Lifetime
