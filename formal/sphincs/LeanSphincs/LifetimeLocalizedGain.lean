import LeanSphincs.LifetimeTransition

/-! Localize the exact insertion gain without capping or replacing the signer. The future
pool is unchanged; gains on future pools with more than 255 distinct views at a leaf are
kept as a separate overflow remainder. Thus no insertion can displace a future signature. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete

attribute [local instance] Classical.propDecidable

variable [Params]

set_option exponentiation.threshold 512

def ViewCap (cap : Nat) (views : Finset KeptDigestView) : Prop :=
  ∀ index, (views.filter (fun view => view.1 = index)).card ≤ cap

theorem viewCap_insert {cap : Nat} {views : Finset KeptDigestView} (hcap : ViewCap cap views)
    (source : KeptDigestView) : ViewCap (cap + 1) (insert source views) := by
  intro index
  rw [Finset.filter_insert]
  split_ifs
  · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hcap index) 1)
  · exact (hcap index).trans (Nat.le_succ cap)

theorem coverageGain_index_eq (target source : KeptDigestView) (views : Finset KeptDigestView)
    (hgain : CoverageGain target source views) : source.1 = target.1 := by
  by_contra hne
  apply hgain.1
  intro tree
  obtain ⟨view, hview, hindex, hleaf⟩ := hgain.2 tree
  rcases Finset.mem_insert.mp hview with rfl | hview
  · exact False.elim (hne hindex)
  · exact ⟨view, hview, hindex, hleaf⟩

noncomputable def localizedCoverageGain (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) : ℝ≥0∞ :=
  if Landed parameter (digestIndex target) then
    Pr[fun views => ViewCap 255 views ∧ CoverageGain (localDigestView target) source views |
      uniformDisclosureSet n prior] else 0

noncomputable def overflowCoverageGain (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) : ℝ≥0∞ :=
  if Landed parameter (digestIndex target) then
    Pr[fun views => ¬ViewCap 255 views ∧ CoverageGain (localDigestView target) source views |
      uniformDisclosureSet n prior] else 0

noncomputable def futureOverflow (n : Nat) (prior : Finset KeptDigestView) : ℝ≥0∞ :=
  Pr[fun views => ¬ViewCap 255 views | uniformDisclosureSet n prior]

theorem futureCoverageGain_split (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) :
    futureCoverageGain parameter n prior source target =
      localizedCoverageGain parameter n prior source target + overflowCoverageGain parameter n prior source target := by
  by_cases hland : Landed parameter (digestIndex target)
  · simp only [futureCoverageGain, localizedCoverageGain, overflowCoverageGain, hland, if_true,
      probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
    apply tsum_congr
    intro views
    by_cases hcap : ViewCap 255 views <;>
      simp only [hcap, not_true_eq_false, not_false_eq_true, true_and, false_and, if_false, zero_add, add_zero]
  · simp only [futureCoverageGain, localizedCoverageGain, overflowCoverageGain, hland, if_false, zero_add]

theorem overflowCoverageGain_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) :
    overflowCoverageGain parameter n prior source target ≤ futureOverflow n prior := by
  unfold overflowCoverageGain futureOverflow
  split_ifs
  · exact probEvent_mono'' (fun _ h => h.1)
  · exact bot_le

theorem localizedCoverageGain_le_gain (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) :
    localizedCoverageGain parameter n prior source target ≤ futureCoverageGain parameter n prior source target := by
  rw [futureCoverageGain_split]
  exact le_self_add

theorem localizedCoverageGain_le_one (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) :
    localizedCoverageGain parameter n prior source target ≤ 1 := by
  unfold localizedCoverageGain
  split_ifs
  · exact probEvent_le_one
  · exact zero_le_one

theorem localizedCoverageGain_square_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) :
    localizedCoverageGain parameter n prior source target ^ 2 ≤
      localizedCoverageGain parameter n prior source target := by
  rw [pow_two]
  exact mul_le_of_le_one_right' (localizedCoverageGain_le_one parameter n prior source target)

noncomputable def viewCoordinates (views : Finset KeptDigestView)
    (index : Fin (2 ^ subtreeHeight)) (tree : IndexGroup) : Finset FtsLeaf :=
  (views.filter (fun view => view.1 = index)).image (fun view => view.2 tree)

theorem viewCoordinates_card_le {cap : Nat} {views : Finset KeptDigestView}
    (hcap : ViewCap cap views) (index : Fin (2 ^ subtreeHeight)) (tree : IndexGroup) :
    (viewCoordinates views index tree).card ≤ cap :=
  (Finset.card_image_le).trans (hcap index)

def FixedKeptCovered (index : Fin (2 ^ subtreeHeight)) (leaves : IndexGroup → Finset FtsLeaf)
    (target : KeptDigestView) : Prop := target.1 = index ∧ ∀ tree, target.2 tree ∈ leaves tree

noncomputable def fixedKeptCoveredEquiv (index : Fin (2 ^ subtreeHeight))
    (leaves : IndexGroup → Finset FtsLeaf) :
    ((tree : IndexGroup) → {leaf : FtsLeaf // leaf ∈ leaves tree}) ≃
      {target : KeptDigestView // FixedKeptCovered index leaves target} where
  toFun selected := ⟨(index, fun tree => (selected tree).val), rfl, fun tree => (selected tree).property⟩
  invFun target tree := ⟨target.val.2 tree, target.property.2 tree⟩
  left_inv selected := rfl
  right_inv target := by
    apply Subtype.ext
    exact Prod.ext target.property.1.symm rfl

theorem fixedKeptCovered_card (index : Fin (2 ^ subtreeHeight)) (leaves : IndexGroup → Finset FtsLeaf) :
    (Finset.univ.filter (FixedKeptCovered index leaves)).card = ∏ tree, (leaves tree).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_congr (fixedKeptCoveredEquiv index leaves), Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro tree _
  simp

theorem probEvent_fixedKeptCovered (index : Fin (2 ^ subtreeHeight)) (leaves : IndexGroup → Finset FtsLeaf) :
    Pr[FixedKeptCovered index leaves | ($ᵗ KeptDigestView : ProbComp _)] =
      ((∏ tree, (leaves tree).card : Nat) : ℝ≥0∞) / (((2 ^ subtreeHeight * 1024 ^ 24 : Nat)) : ℝ≥0∞) := by
  rw [probEvent_uniformSample, fixedKeptCovered_card]
  congr 2
  simp only [KeptDigestView, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rfl

/-- Localization at 256 views gives the exact `2^-74` fresh-target mass bound at a single
retained leaf, uniformly over its adaptively chosen coordinate sets. -/
theorem probEvent_landed_fixedKeptCovered_le (parameter : PublicParameter)
    (index : Fin (2 ^ subtreeHeight)) (leaves : IndexGroup → Finset FtsLeaf)
    (hsize : ∀ tree, (leaves tree).card ≤ 256) :
    Pr[fun digest => Landed parameter (digestIndex digest) ∧
      FixedKeptCovered index leaves (localDigestView digest) | ($ᵗ MessageDigest : ProbComp _)] ≤
        (1 : ℝ≥0∞) / 2 ^ 74 := by
  rw [probEvent_landed_localDigest, probEvent_fixedKeptCovered]
  have hnum : (∏ tree, (leaves tree).card) ≤ 256 ^ 24 := by
    calc
      _ ≤ ∏ _tree : IndexGroup, 256 := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun tree _ => hsize tree)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]; rfl
  calc
    _ ≤ ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
        (((256 ^ 24 : Nat) : ℝ≥0∞) / ((2 ^ subtreeHeight * 1024 ^ 24 : Nat) : ℝ≥0∞)) := by
      gcongr
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
        ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_one, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat, totalHeight]
      have hprod : (2 : ℝ) ^ (26 - subtreeHeight) * 2 ^ subtreeHeight = 2 ^ 26 := by
        have hb : subtreeHeight ≤ 26 := Params.subtreeHeight_le
        rw [← pow_add, Nat.sub_add_cancel hb]
      field_simp
      nlinarith only [hprod]

theorem coverageGain_fixedKeptCovered (target source : KeptDigestView) (views : Finset KeptDigestView)
    (hgain : CoverageGain target source views) :
    FixedKeptCovered source.1 (viewCoordinates (insert source views) source.1) target := by
  have hindex := coverageGain_index_eq target source views hgain
  refine ⟨hindex.symm, ?_⟩
  intro tree
  obtain ⟨view, hview, hi, ht⟩ := hgain.2 tree
  exact Finset.mem_image.mpr ⟨view, Finset.mem_filter.mpr ⟨hview, hi.trans hindex.symm⟩, ht⟩

theorem probEvent_landed_coverageGain_le (parameter : PublicParameter)
    (source : KeptDigestView) (views : Finset KeptDigestView) (hcap : ViewCap 255 views) :
    Pr[fun digest => Landed parameter (digestIndex digest) ∧
      CoverageGain (localDigestView digest) source views | ($ᵗ MessageDigest : ProbComp _)] ≤
        (1 : ℝ≥0∞) / 2 ^ 74 := by
  refine (probEvent_mono'' (fun digest h => And.intro h.1
    (coverageGain_fixedKeptCovered _ source views h.2))).trans ?_
  exact probEvent_landed_fixedKeptCovered_le parameter source.1
    (viewCoordinates (insert source views) source.1)
    (fun tree => viewCoordinates_card_le (viewCap_insert hcap source) source.1 tree)

theorem uniform_localizedCoverageGain (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) :
    uniformDigestForecast (localizedCoverageGain parameter n prior source) =
      ∑' views, Pr[= views | uniformDisclosureSet n prior] *
        Pr[fun digest => Landed parameter (digestIndex digest) ∧ ViewCap 255 views ∧
          CoverageGain (localDigestView digest) source views | ($ᵗ MessageDigest : ProbComp _)] := by
  have hweight (digest : MessageDigest) : localizedCoverageGain parameter n prior source digest =
      Pr[fun views => Landed parameter (digestIndex digest) ∧ ViewCap 255 views ∧
        CoverageGain (localDigestView digest) source views | uniformDisclosureSet n prior] := by
    by_cases hland : Landed parameter (digestIndex digest) <;>
      simp only [localizedCoverageGain, hland, if_true, if_false, true_and, false_and, probEvent_False]
  simp only [uniformDigestForecast, hweight, probEvent_eq_tsum_ite]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro views
  apply tsum_congr
  intro digest
  split_ifs <;> simp only [mul_comm, zero_mul]

/-- The changing future kernel satisfies the fixed-source `2^-74` cap used by the
second-moment bank, without any cap or displacement in the actual signing transition. -/
theorem uniform_localizedCoverageGain_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) :
    uniformDigestForecast (localizedCoverageGain parameter n prior source) ≤ (1 : ℝ≥0∞) / 2 ^ 74 := by
  rw [uniform_localizedCoverageGain]
  calc
    _ ≤ ∑' views, Pr[= views | uniformDisclosureSet n prior] * ((1 : ℝ≥0∞) / 2 ^ 74) := by
      apply ENNReal.tsum_le_tsum
      intro views
      apply mul_le_mul' le_rfl
      by_cases hcap : ViewCap 255 views
      · simp only [hcap, true_and]
        exact probEvent_landed_coverageGain_le parameter source views hcap
      · simp [hcap]
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

noncomputable def localizedGainMean (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (target : MessageDigest) : ℝ≥0∞ :=
  ∑' source, Pr[= source | ($ᵗ KeptDigestView : ProbComp _)] * localizedCoverageGain parameter n prior source target

theorem localizedGainMean_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (target : MessageDigest) :
    localizedGainMean parameter n prior target ≤ independentGainMean parameter n prior target :=
  ENNReal.tsum_le_tsum fun source => mul_le_mul' le_rfl
    (localizedCoverageGain_le_gain parameter n prior source target)

/-- The actual complete signer's change of future forecast is its centered localized
insertion gain, plus at most one explicit future-overflow forecast. No cap is imposed on
signing, and the full actual cache bias remains inside the selected-gain expectation. -/
theorem expected_signWithSources_localized_drift (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (n : Nat) (target : MessageDigest) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      futureCoverWeight sk.parameter n (sourcedPrior result.2.1) target) +
        localizedGainMean sk.parameter n (sourcedPrior state.1) target ≤
      futureCoverWeight sk.parameter (n + 1) (sourcedPrior state.1) target +
        (∑' result, Pr[= result | signWithSources sk message state] *
          newSourceDigestWeight state.1 (fun _ digest =>
            localizedCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1) +
        futureOverflow n (sourcedPrior state.1) := by
  refine ((add_le_add le_rfl (localizedGainMean_le sk.parameter n (sourcedPrior state.1) target)).trans_eq
    (expected_signWithSources_centered_gain sk message state n target)).trans ?_
  rw [add_assoc]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | signWithSources sk message state] *
        (newSourceDigestWeight state.1 (fun _ digest =>
          localizedCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1 +
          futureOverflow n (sourcedPrior state.1)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      apply mul_le_mul' le_rfl
      cases hrecords : result.2.1 with
      | nil => simp only [newSourceDigestWeight, zero_add]; exact bot_le
      | cons record rest =>
        simp only [newSourceDigestWeight]
        split_ifs
        · rw [futureCoverageGain_split]
          exact add_le_add le_rfl (overflowCoverageGain_le _ _ _ _ _)
        · simp only [zero_add]; exact bot_le
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, signWithSources_mass, one_mul]

end LeanSphincs.Lifetime
