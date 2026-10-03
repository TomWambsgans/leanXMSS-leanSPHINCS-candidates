import LeanSphincs.LifetimeExcludedGain

/-! Exact fixed-feature decomposition of the changing FORS gain. The current history selects
which coordinates remain missing, but the source/target matching feature for a fixed subset
is independent of that history. This identity alone does not make adaptively selected
coefficients independent of the candidate bank. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete
attribute [local instance] Classical.propDecidable

variable [Params]

noncomputable def missingTrees (target : KeptDigestView) (prior : Finset KeptDigestView) : Finset IndexGroup :=
  Finset.univ.filter (fun tree => ¬PriorTreeCovered target prior tree)

def MatchCoordinates (target source : KeptDigestView) (trees : Finset IndexGroup) : Prop :=
  source.1 = target.1 ∧ ∀ tree ∈ trees, source.2 tree = target.2 tree

theorem missingTrees_nonempty_iff (target : KeptDigestView) (prior : Finset KeptDigestView) :
    (missingTrees target prior).Nonempty ↔ ¬ViewCovered target prior := by
  simp only [missingTrees, Finset.nonempty_def, Finset.mem_filter, Finset.mem_univ, true_and]
  change (∃ tree, ¬PriorTreeCovered target prior tree) ↔ ¬∀ tree, PriorTreeCovered target prior tree
  exact not_forall.symm

/-- A source creates coverage precisely when at least one coordinate is still missing and
it supplies all the missing coordinates at the target's retained index. -/
theorem coverageGain_missing_iff (target source : KeptDigestView) (prior : Finset KeptDigestView) :
    CoverageGain target source prior ↔
      (missingTrees target prior).Nonempty ∧ MatchCoordinates target source (missingTrees target prior) := by
  constructor
  · intro hgain
    refine ⟨(missingTrees_nonempty_iff target prior).2 hgain.1,
      coverageGain_index_eq target source prior hgain, ?_⟩
    intro tree htree
    have hmissing := (Finset.mem_filter.mp htree).2
    obtain ⟨view, hview, hi, ht⟩ := hgain.2 tree
    rcases Finset.mem_insert.mp hview with rfl | hprior
    · exact ht
    · exact False.elim (hmissing ⟨view, hprior, hi, ht⟩)
  · rintro ⟨hmissing, hindex, hmatch⟩
    refine ⟨(missingTrees_nonempty_iff target prior).1 hmissing, ?_⟩
    intro tree
    by_cases hprior : PriorTreeCovered target prior tree
    · obtain ⟨view, hview, hi, ht⟩ := hprior
      exact ⟨view, Finset.mem_insert_of_mem hview, hi, ht⟩
    · exact ⟨source, Finset.mem_insert_self _ _, hindex,
        hmatch tree (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprior⟩)⟩

omit [Params] in
theorem coordinateFeature_card : Fintype.card (Finset IndexGroup) = 2 ^ 24 := by
  rw [Fintype.card_finset]
  congr 1

noncomputable def missingTreeWeight (target : KeptDigestView) (n : Nat)
    (prior : Finset KeptDigestView) (trees : Finset IndexGroup) : ℝ≥0∞ :=
  Pr[fun views => missingTrees target views = trees | uniformDisclosureSet n prior]

/-- The weights form an exact probability distribution on the fixed coordinate features.
They can depend on the actual history and therefore must not be treated as predictable at
an earlier candidate-query time. -/
theorem missingTreeWeight_sum (target : KeptDigestView) (n : Nat)
    (prior : Finset KeptDigestView) :
    (∑ trees : Finset IndexGroup, missingTreeWeight target n prior trees) = 1 := by
  have h : (∑' trees : Finset IndexGroup,
      Pr[= trees | missingTrees target <$> uniformDisclosureSet n prior]) = 1 := by
    apply tsum_probOutput_eq_one'
    simp only [probFailure_map, uniformDisclosureSet, probFailure_map]
    induction n with
    | zero => simp [SphincsSecurity.Concrete.sampleUniformProposalWord]
    | succ n _ih => simp [SphincsSecurity.Concrete.sampleUniformProposalWord]
  simpa only [tsum_fintype, probOutput_map, missingTreeWeight] using h

/-- Exact finite conditional mixture, valid for every source and every actual prior. -/
theorem probEvent_coverageGain_coordinates (target source : KeptDigestView) (n : Nat)
    (prior : Finset KeptDigestView) :
    Pr[CoverageGain target source | uniformDisclosureSet n prior] =
      ∑ trees : Finset IndexGroup, missingTreeWeight target n prior trees *
        (if trees.Nonempty ∧ MatchCoordinates target source trees then 1 else 0) := by
  calc
    _ = Pr[fun trees => trees.Nonempty ∧ MatchCoordinates target source trees |
        missingTrees target <$> uniformDisclosureSet n prior] := by
      rw [probEvent_map]
      exact probEvent_ext (fun views _ => coverageGain_missing_iff target source views)
    _ = _ := by
      rw [probEvent_eq_tsum_ite, tsum_fintype]
      apply Finset.sum_congr rfl
      intro trees _
      rw [probOutput_map]
      change (if trees.Nonempty ∧ MatchCoordinates target source trees then
        missingTreeWeight target n prior trees else 0) = _
      split_ifs <;> simp

noncomputable def coordinateGainFeature (parameter : PublicParameter) (trees : Finset IndexGroup)
    (source : KeptDigestView) (target : MessageDigest) : ℝ≥0∞ :=
  if Landed parameter (digestIndex target) ∧ trees.Nonempty ∧
    MatchCoordinates (localDigestView target) source trees then 1 else 0

/-- All dependence on the current disclosure history is isolated in the mixture weights;
the functions `coordinateGainFeature` remain fixed when that history changes. -/
theorem futureCoverageGain_coordinates (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) :
    futureCoverageGain parameter n prior source target =
      ∑ trees : Finset IndexGroup, missingTreeWeight (localDigestView target) n prior trees *
        coordinateGainFeature parameter trees source target := by
  by_cases hland : Landed parameter (digestIndex target)
  · simp only [futureCoverageGain, coordinateGainFeature, hland, if_true, true_and]
    exact probEvent_coverageGain_coordinates (localDigestView target) source n prior
  · simp only [futureCoverageGain, coordinateGainFeature, hland, if_false, false_and,
      mul_zero, Finset.sum_const_zero]

/-- The mixture identity commutes with any source distribution, including the actual
conditional empirical pool. It makes no independence assumption about the history. -/
theorem expected_futureCoverageGain_coordinates {α : Type} (sample : ProbComp α)
    (source : α → KeptDigestView) (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (target : MessageDigest) :
    (∑' value, Pr[= value | sample] * futureCoverageGain parameter n prior (source value) target) =
      ∑ trees : Finset IndexGroup, missingTreeWeight (localDigestView target) n prior trees *
        ∑' value, Pr[= value | sample] * coordinateGainFeature parameter trees (source value) target := by
  simp only [futureCoverageGain_coordinates, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro trees _
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro value
  ring

theorem missingTreeWeight_le_one (target : KeptDigestView) (n : Nat)
    (prior : Finset KeptDigestView) (trees : Finset IndexGroup) :
    missingTreeWeight target n prior trees ≤ 1 := probEvent_le_one

/-- A valid bound even when the current history selects the mixture after seeing all
feature errors. The right side retains every feature's square; replacing it by the variance
of a single previously fixed feature would require an additional argument. -/
theorem adaptive_coordinate_mixture_square_le (target : KeptDigestView) (n : Nat)
    (prior : Finset KeptDigestView) (error : Finset IndexGroup → ℝ) :
    (∑ trees : Finset IndexGroup, (missingTreeWeight target n prior trees).toReal * error trees) ^ 2 ≤
      ∑ trees : Finset IndexGroup, (error trees) ^ 2 := by
  let weight (trees : Finset IndexGroup) : ℝ := (missingTreeWeight target n prior trees).toReal
  have hweight (trees : Finset IndexGroup) : 0 ≤ weight trees := ENNReal.toReal_nonneg
  have hfinite (trees : Finset IndexGroup) : missingTreeWeight target n prior trees ≠ ∞ :=
    ne_of_lt ((missingTreeWeight_le_one target n prior trees).trans_lt (by simp))
  have hsum : ∑ trees, weight trees = 1 := by
    have h := congrArg ENNReal.toReal (missingTreeWeight_sum target n prior)
    rw [ENNReal.toReal_sum (fun trees _ => hfinite trees)] at h
    simpa only [ENNReal.toReal_one] using h
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun trees => weight trees * error trees)
    (f := weight) (g := fun trees => weight trees * error trees ^ 2)
    (fun trees _ => hweight trees)
    (fun trees _ => mul_nonneg (hweight trees) (sq_nonneg _))
    (fun trees _ => by nlinarith [sq_nonneg (weight trees * error trees)])
  rw [hsum, one_mul] at hcs
  refine hcs.trans (Finset.sum_le_sum ?_)
  intro trees _
  have hw : weight trees ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) (missingTreeWeight_le_one target n prior trees))
  nlinarith [sq_nonneg (error trees)]

end LeanSphincs.Lifetime
