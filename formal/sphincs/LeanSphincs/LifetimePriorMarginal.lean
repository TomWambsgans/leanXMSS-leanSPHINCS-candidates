import LeanSphincs.LifetimeTransition

/-! The pivotal-disclosure budget holds after every fixed actual history, even one chosen
using cached oracle answers. This is a local self-bound for the changing continuation,
not a replacement of that continuation by the empty-history lifetime formula. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete
attribute [local instance] Classical.propDecidable

variable [Params]

def PriorTreeCovered (target : KeptDigestView) (prior : Finset KeptDigestView)
    (tree : IndexGroup) : Prop :=
  ∃ view ∈ prior, view.1 = target.1 ∧ view.2 tree = target.2 tree

def PriorFunctionCovered {n : Nat} (target : KeptDigestView) (prior : Finset KeptDigestView)
    (word : Fin n → KeptDigestView) : Prop :=
  ∀ tree, PriorTreeCovered target prior tree ∨
    ∃ position, (word position).1 = target.1 ∧ (word position).2 tree = target.2 tree

def PriorPivotalPosition {n : Nat} (target : KeptDigestView) (prior : Finset KeptDigestView)
    (word : Fin n → KeptDigestView) (position : Fin n) : Prop :=
  PriorFunctionCovered target prior word ∧ ∃ tree : IndexGroup,
    ¬PriorTreeCovered target prior tree ∧ ∀ other,
      (word other).1 = target.1 → (word other).2 tree = target.2 tree → other = position

noncomputable def priorPivotalPositions {n : Nat} (target : KeptDigestView)
    (prior : Finset KeptDigestView) (word : Fin n → KeptDigestView) : Finset (Fin n) :=
  Finset.univ.filter (PriorPivotalPosition target prior word)

theorem priorPivotalPositions_card_le {n : Nat} (target : KeptDigestView)
    (prior : Finset KeptDigestView) (word : Fin n → KeptDigestView) :
    (priorPivotalPositions target prior word).card ≤ 24 := by
  let tree (position : {i : Fin n // PriorPivotalPosition target prior word i}) : IndexGroup :=
    Classical.choose position.property.2
  have hinj : Function.Injective tree := by
    intro left right heq
    have hl := Classical.choose_spec left.property.2
    have hr := Classical.choose_spec right.property.2
    have hcovered := left.property.1 (tree left)
    obtain ⟨witness, hindex, hleaf⟩ := hcovered.resolve_left hl.1
    have hleft := hl.2 witness hindex hleaf
    have hright : witness = right.val := by
      apply hr.2 witness hindex
      change (word witness).2 (tree right) = target.2 (tree right)
      rw [← heq]
      exact hleaf
    exact Subtype.ext (hleft.symm.trans hright)
  have hcard := Fintype.card_le_of_injective tree hinj
  rw [Fintype.card_subtype] at hcard
  exact hcard.trans_eq (by decide : Fintype.card IndexGroup = 24)

theorem priorPivotalPositions_card_zero {n : Nat} (target : KeptDigestView)
    (prior : Finset KeptDigestView) (word : Fin n → KeptDigestView)
    (hnot : ¬PriorFunctionCovered target prior word) :
    (priorPivotalPositions target prior word).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro position hmem
  exact hnot (Finset.mem_filter.mp hmem).2.1

theorem priorFunctionCovered_reindex_iff {n : Nat} (target : KeptDigestView)
    (prior : Finset KeptDigestView) (word : Fin n → KeptDigestView)
    (permutation : Equiv.Perm (Fin n)) :
    PriorFunctionCovered target prior (word ∘ permutation) ↔ PriorFunctionCovered target prior word := by
  constructor
  · intro h tree
    rcases h tree with hp | ⟨position, hi, ht⟩
    · exact Or.inl hp
    · exact Or.inr ⟨permutation position, hi, ht⟩
  · intro h tree
    rcases h tree with hp | ⟨position, hi, ht⟩
    · exact Or.inl hp
    · exact Or.inr ⟨permutation.symm position,
        by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi,
        by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using ht⟩

theorem priorPivotalPosition_reindex_iff {n : Nat} (target : KeptDigestView)
    (prior : Finset KeptDigestView) (word : Fin n → KeptDigestView)
    (permutation : Equiv.Perm (Fin n)) (position : Fin n) :
    PriorPivotalPosition target prior (word ∘ permutation) position ↔
      PriorPivotalPosition target prior word (permutation position) := by
  rw [PriorPivotalPosition, PriorPivotalPosition, priorFunctionCovered_reindex_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨tree, hp, htree⟩
    refine ⟨tree, hp, fun other hi ht => ?_⟩
    have h := htree (permutation.symm other)
      (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi)
      (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using ht)
    simpa only [Equiv.apply_symm_apply] using congrArg permutation h
  · rintro ⟨tree, hp, htree⟩
    exact ⟨tree, hp, fun other hi ht => permutation.injective (htree (permutation other) hi ht)⟩

theorem probEvent_priorPivotal_position_eq {n : Nat} (target : KeptDigestView)
    (prior : Finset KeptDigestView) (left right : Fin n) :
    Pr[fun word => PriorPivotalPosition target prior word left | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] =
      Pr[fun word => PriorPivotalPosition target prior word right | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] := by
  let reindex : (Fin n → KeptDigestView) → (Fin n → KeptDigestView) :=
    fun word => word ∘ Equiv.swap left right
  have hinvol : Function.Involutive reindex := by
    intro word
    funext position
    simp only [reindex, Function.comp_apply, Equiv.swap_apply_self]
  have heval := evalDist_map_bijective_uniform_cross (Fin n → KeptDigestView) reindex hinvol.bijective
  calc
    _ = Pr[fun word => PriorPivotalPosition target prior word left |
        reindex <$> ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] :=
      (probEvent_congr' (fun _ _ => Iff.rfl) heval).symm
    _ = _ := by
      rw [probEvent_map]
      exact probEvent_ext fun word _ => by
        simp only [Function.comp_apply, reindex, priorPivotalPosition_reindex_iff, Equiv.swap_apply_left]

/-- Exchangeability is only used for the independent continuation. The preceding set is
arbitrary, so it can be the complete disclosure history of the adaptive actual signer. -/
theorem probEvent_priorPivotal_mul_le {n : Nat} (target : KeptDigestView)
    (prior : Finset KeptDigestView) (position : Fin n) :
    (n : ℝ≥0∞) * Pr[fun word => PriorPivotalPosition target prior word position |
      ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] ≤
        24 * Pr[PriorFunctionCovered target prior | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] := by
  let sample : ProbComp (Fin n → KeptDigestView) := $ᵗ _
  calc
    _ = ∑ i : Fin n, Pr[fun word => PriorPivotalPosition target prior word i | sample] := by
      simp only [probEvent_priorPivotal_position_eq target prior _ position, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sample]
    _ = ∑' word, Pr[= word | sample] * ((priorPivotalPositions target prior word).card : ℝ≥0∞) := by
      simp only [probEvent_eq_tsum_ite]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply tsum_congr
      intro word
      rw [priorPivotalPositions, ← Finset.sum_boole]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ ≤ ∑' word, Pr[= word | sample] * (if PriorFunctionCovered target prior word then 24 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro word
      apply mul_le_mul' le_rfl
      split_ifs with hcovered
      · exact_mod_cast priorPivotalPositions_card_le target prior word
      · rw [priorPivotalPositions_card_zero target prior word hcovered, Nat.cast_zero]
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro word
      split_ifs
      · exact mul_comm _ _
      · simp only [mul_zero]

theorem priorPivotalPosition_zero_iff (n : Nat) (target : KeptDigestView)
    (prior : Finset KeptDigestView) (word : Fin (n + 1) → KeptDigestView) :
    PriorPivotalPosition target prior word 0 ↔ PriorFunctionCovered target prior word ∧
      ¬PriorFunctionCovered target prior (fun position : Fin n => word position.succ) := by
  constructor
  · rintro ⟨hcovered, tree, hp, htree⟩
    refine ⟨hcovered, fun htail => ?_⟩
    rcases htail tree with hprior | ⟨position, hi, ht⟩
    · exact hp hprior
    · exact Fin.succ_ne_zero position (htree position.succ hi ht)
  · rintro ⟨hcovered, htail⟩
    unfold PriorFunctionCovered at htail
    push Not at htail
    obtain ⟨tree, hp, htree⟩ := htail
    refine ⟨hcovered, tree, hp, ?_⟩
    intro other
    refine Fin.cases (by intros; rfl) (fun position hi ht => ?_) other
    exact False.elim (htree position hi ht)

theorem priorFunctionCovered_ofFn_iff (n : Nat) (target : KeptDigestView)
    (prior : Finset KeptDigestView) (word : Fin n → KeptDigestView) :
    ViewCovered target ((List.ofFn word).toFinset ∪ prior) ↔ PriorFunctionCovered target prior word := by
  simp only [ViewCovered, PriorFunctionCovered, PriorTreeCovered, Finset.mem_union,
    List.mem_toFinset, List.mem_ofFn]
  constructor
  · intro h tree
    obtain ⟨view, hv, hi, ht⟩ := h tree
    rcases hv with ⟨position, rfl⟩ | hprior
    · exact Or.inr ⟨position, hi, ht⟩
    · exact Or.inl ⟨view, hprior, hi, ht⟩
  · intro h tree
    rcases h tree with ⟨view, hp, hi, ht⟩ | ⟨position, hi, ht⟩
    · exact ⟨view, Or.inr hp, hi, ht⟩
    · exact ⟨word position, Or.inl ⟨position, rfl⟩, hi, ht⟩

theorem probEvent_uniformDisclosureSet_prior_function (n : Nat) (target : KeptDigestView)
    (prior : Finset KeptDigestView) :
    Pr[ViewCovered target | uniformDisclosureSet n prior] =
      Pr[PriorFunctionCovered target prior | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] := by
  rw [uniformDisclosureSet, probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_sampleWord_uniform_function n)]
  simp only [probEvent_map, Function.comp_def]
  exact probEvent_ext (fun word _ => priorFunctionCovered_ofFn_iff n target prior word)

theorem probEvent_priorPivotal_zero_gain (n : Nat) (target : KeptDigestView)
    (prior : Finset KeptDigestView) :
    Pr[fun word => PriorPivotalPosition target prior word (0 : Fin (n + 1)) |
      ($ᵗ (Fin (n + 1) → KeptDigestView) : ProbComp _)] =
      ∑' source, Pr[= source | ($ᵗ KeptDigestView : ProbComp _)] *
        Pr[CoverageGain target source | uniformDisclosureSet n prior] := by
  rw [← probEvent_congr' (fun _ _ => Iff.rfl)
    (SphincsSecurity.Seeded.evalDist_sequenceFin_uniform (R := KeptDigestView) (n + 1))]
  rw [SphincsSecurity.Concrete.sequenceFin, probEvent_bind_eq_tsum]
  apply tsum_congr
  intro source
  apply congrArg (fun value => Pr[= source | ($ᵗ KeptDigestView : ProbComp _)] * value)
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (SphincsSecurity.Seeded.evalDist_sequenceFin_uniform (R := KeptDigestView) n)]
  rw [uniformDisclosureSet, probEvent_map,
    probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_sampleWord_uniform_function n)]
  simp only [probEvent_map, Function.comp_def]
  apply probEvent_ext
  intro word _
  rw [priorPivotalPosition_zero_iff]
  simp only [Fin.cases_succ]
  rw [← priorFunctionCovered_ofFn_iff, ← priorFunctionCovered_ofFn_iff]
  simp only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ, List.toFinset_cons,
    Finset.insert_union, CoverageGain]
  exact and_comm

/-- The current continuation controls its own independent marginal at every actual prior.
No law for the prior, no fresh-cache condition, and no non-message oracle independence is
needed. The factor is the number of FORS trees, not the size of the preceding history. -/
theorem independentGainMean_mul_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (target : MessageDigest) :
    ((n + 1 : Nat) : ℝ≥0∞) * independentGainMean parameter n prior target ≤
      24 * futureCoverWeight parameter (n + 1) prior target := by
  by_cases hland : Landed parameter (digestIndex target)
  · simp only [independentGainMean, futureCoverageGain, futureCoverWeight, hland, if_true]
    rw [← probEvent_priorPivotal_zero_gain, probEvent_uniformDisclosureSet_prior_function]
    exact probEvent_priorPivotal_mul_le (localDigestView target) prior (0 : Fin (n + 1))
  · simp only [independentGainMean, futureCoverageGain, futureCoverWeight, hland, if_false,
      mul_zero, tsum_zero, le_rfl]

theorem independentGainMean_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (target : MessageDigest) :
    independentGainMean parameter n prior target ≤
      (24 * futureCoverWeight parameter (n + 1) prior target) / (n + 1 : Nat) := by
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))).2
  simpa only [mul_comm] using independentGainMean_mul_le parameter n prior target

/-- Integration against a fixed target bank, its conditional digest forecasts, or a fresh
candidate reserve preserves the local self-bound. The target weight need not be uniform. -/
theorem weighted_independentGainMean_mul_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (weight : MessageDigest → ℝ≥0∞) :
    ((n + 1 : Nat) : ℝ≥0∞) * (∑' target, weight target * independentGainMean parameter n prior target) ≤
      24 * ∑' target, weight target * futureCoverWeight parameter (n + 1) prior target := by
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro target
  simpa only [mul_left_comm] using mul_le_mul' (le_rfl : weight target ≤ weight target)
    (independentGainMean_mul_le parameter n prior target)

end LeanSphincs.Lifetime
