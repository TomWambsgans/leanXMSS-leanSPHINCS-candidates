import LeanSphincs.LifetimeFutureBank

/-! A single independent disclosure has small average marginal coverage gain. For a fixed
covered target, at most 24 signing positions can be indispensable: each indispensable
position must be the unique witness for one of the 24 FORS coordinates. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete

attribute [local instance] Classical.propDecidable

variable [Params]

def PivotalPosition {n : Nat} (target : KeptDigestView)
    (word : Fin n → KeptDigestView) (position : Fin n) : Prop :=
  FunctionCovered target word ∧ ∃ tree : IndexGroup, ∀ other,
    (word other).1 = target.1 → (word other).2 tree = target.2 tree → other = position

noncomputable def pivotalPositions {n : Nat} (target : KeptDigestView)
    (word : Fin n → KeptDigestView) : Finset (Fin n) :=
  Finset.univ.filter (PivotalPosition target word)

theorem pivotalPositions_card_le {n : Nat} (target : KeptDigestView) (word : Fin n → KeptDigestView) :
    (pivotalPositions target word).card ≤ 24 := by
  let tree (position : {i : Fin n // PivotalPosition target word i}) : IndexGroup :=
    Classical.choose position.property.2
  have hinj : Function.Injective tree := by
    intro left right heq
    have hl := Classical.choose_spec left.property.2
    have hr := Classical.choose_spec right.property.2
    obtain ⟨witness, hindex, hleaf⟩ := left.property.1 (tree left)
    have hleft := hl witness hindex hleaf
    have hright : witness = right.val := by
      apply hr witness hindex
      change (word witness).2 (tree right) = target.2 (tree right)
      rw [← heq]
      exact hleaf
    exact Subtype.ext (hleft.symm.trans hright)
  have hcard := Fintype.card_le_of_injective tree hinj
  rw [Fintype.card_subtype] at hcard
  exact hcard.trans_eq (by decide : Fintype.card IndexGroup = 24)

theorem pivotalPositions_card_eq_zero_of_not_covered {n : Nat} (target : KeptDigestView)
    (word : Fin n → KeptDigestView) (hnot : ¬FunctionCovered target word) :
    (pivotalPositions target word).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro position hmem
  exact hnot (Finset.mem_filter.mp hmem).2.1

theorem functionCovered_reindex_iff {n : Nat} (target : KeptDigestView)
    (word : Fin n → KeptDigestView) (permutation : Equiv.Perm (Fin n)) :
    FunctionCovered target (word ∘ permutation) ↔ FunctionCovered target word := by
  constructor
  · intro h tree
    obtain ⟨position, hi, ht⟩ := h tree
    exact ⟨permutation position, hi, ht⟩
  · intro h tree
    obtain ⟨position, hi, ht⟩ := h tree
    exact ⟨permutation.symm position, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi,
      by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using ht⟩

theorem pivotalPosition_reindex_iff {n : Nat} (target : KeptDigestView)
    (word : Fin n → KeptDigestView) (permutation : Equiv.Perm (Fin n)) (position : Fin n) :
    PivotalPosition target (word ∘ permutation) position ↔
      PivotalPosition target word (permutation position) := by
  rw [PivotalPosition, PivotalPosition, functionCovered_reindex_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨tree, htree⟩
    refine ⟨tree, fun other hi ht => ?_⟩
    have h := htree (permutation.symm other)
      (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi)
      (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using ht)
    simpa only [Equiv.apply_symm_apply] using congrArg permutation h
  · rintro ⟨tree, htree⟩
    exact ⟨tree, fun other hi ht => permutation.injective (htree (permutation other) hi ht)⟩

theorem probEvent_pivotal_position_eq {n : Nat} (target : KeptDigestView) (left right : Fin n) :
    Pr[fun word => PivotalPosition target word left | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] =
      Pr[fun word => PivotalPosition target word right | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] := by
  let reindex : (Fin n → KeptDigestView) → (Fin n → KeptDigestView) :=
    fun word => word ∘ Equiv.swap left right
  have hinvol : Function.Involutive reindex := by
    intro word
    funext position
    simp only [reindex, Function.comp_apply, Equiv.swap_apply_self]
  have heval := evalDist_map_bijective_uniform_cross (Fin n → KeptDigestView) reindex hinvol.bijective
  calc
    _ = Pr[fun word => PivotalPosition target word left |
        reindex <$> ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] :=
      (probEvent_congr' (fun _ _ => Iff.rfl) heval).symm
    _ = _ := by
      rw [probEvent_map]
      exact probEvent_ext fun word _ => by
        simp only [Function.comp_apply, reindex, pivotalPosition_reindex_iff, Equiv.swap_apply_left]

/-- The exact exchangeability charge for an indispensable independent disclosure. This is
the diagonal marginal factor needed before taking a second moment over candidate targets. -/
theorem probEvent_pivotal_mul_le {n : Nat} (target : KeptDigestView) (position : Fin n) :
    (n : ℝ≥0∞) * Pr[fun word => PivotalPosition target word position |
      ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] ≤
        24 * Pr[FunctionCovered target | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] := by
  let sample : ProbComp (Fin n → KeptDigestView) := $ᵗ _
  calc
    _ = ∑ i : Fin n, Pr[fun word => PivotalPosition target word i | sample] := by
      simp only [probEvent_pivotal_position_eq target _ position, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sample]
    _ = ∑' word, Pr[= word | sample] * ((pivotalPositions target word).card : ℝ≥0∞) := by
      simp only [probEvent_eq_tsum_ite]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      apply tsum_congr
      intro word
      rw [pivotalPositions, ← Finset.sum_boole]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ ≤ ∑' word, Pr[= word | sample] * (if FunctionCovered target word then 24 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro word
      apply mul_le_mul' le_rfl
      split_ifs with hcovered
      · exact_mod_cast pivotalPositions_card_le target word
      · rw [pivotalPositions_card_eq_zero_of_not_covered target word hcovered, Nat.cast_zero]
    _ = _ := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro word
      split_ifs
      · exact mul_comm _ _
      · simp only [mul_zero]

theorem pivotalPosition_zero_iff (n : Nat) (target : KeptDigestView)
    (word : Fin (n + 1) → KeptDigestView) :
    PivotalPosition target word 0 ↔ FunctionCovered target word ∧
      ¬FunctionCovered target (fun position : Fin n => word position.succ) := by
  constructor
  · rintro ⟨hcovered, tree, htree⟩
    refine ⟨hcovered, fun htail => ?_⟩
    obtain ⟨position, hi, ht⟩ := htail tree
    exact Fin.succ_ne_zero position (htree position.succ hi ht)
  · rintro ⟨hcovered, htail⟩
    unfold FunctionCovered at htail
    push Not at htail
    obtain ⟨tree, htree⟩ := htail
    refine ⟨hcovered, tree, ?_⟩
    intro other
    refine Fin.cases (by intros; rfl) (fun position hi ht => ?_) other
    exact False.elim (htree position hi ht)

/-- Removing one distinguished independent sample changes coverage with probability at
most `24/(n+1)` times terminal coverage. The multiplied form avoids division side conditions. -/
theorem probEvent_independent_marginal_mul_le (n : Nat) (target : KeptDigestView) :
    ((n + 1 : Nat) : ℝ≥0∞) *
      Pr[fun word : Fin (n + 1) → KeptDigestView => FunctionCovered target word ∧
        ¬FunctionCovered target (fun position : Fin n => word position.succ) | ($ᵗ _ : ProbComp _)] ≤
      24 * SphincsSecurity.Concrete.binomialAverage ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ (n + 1)
        (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24) := by
  have h := probEvent_pivotal_mul_le target (0 : Fin (n + 1))
  have hprice := (probEvent_uniformDisclosureSet_function (n + 1) target).symm.trans
    (probEvent_uniformDisclosureSet_covered (n + 1) target)
  rw [hprice] at h
  have hevent : Pr[fun word => PivotalPosition target word (0 : Fin (n + 1)) |
      ($ᵗ (Fin (n + 1) → KeptDigestView) : ProbComp _)] =
      Pr[fun word : Fin (n + 1) → KeptDigestView => FunctionCovered target word ∧
        ¬FunctionCovered target (fun position : Fin n => word position.succ) | ($ᵗ _ : ProbComp _)] :=
    probEvent_ext fun word _ => pivotalPosition_zero_iff n target word
  rwa [hevent] at h

noncomputable def independentMarginalWeight (parameter : PublicParameter) (n : Nat)
    (digest : MessageDigest) : ℝ≥0∞ :=
  if Landed parameter (digestIndex digest) then
    Pr[fun word : Fin (n + 1) → KeptDigestView => PivotalPosition (localDigestView digest) word 0 |
      ($ᵗ _ : ProbComp _)] else 0

/-- Fresh target price for the one-source diagonal marginal, with the same pruning factor
and exact occupancy price as the six lifetime certificates. -/
theorem initial_independentMarginalWeight_mul_le (parameter : PublicParameter) (n : Nat) :
    ((n + 1 : Nat) : ℝ≥0∞) * uniformDigestForecast (independentMarginalWeight parameter n) ≤
      24 * forsBoundENNReal subtreeHeight (n + 1) := by
  rw [← initial_futureCoverWeight parameter (n + 1), uniformDigestForecast,
    uniformDigestForecast, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro digest
  by_cases hland : Landed parameter (digestIndex digest)
  · simp only [independentMarginalWeight, futureCoverWeight, hland, if_true]
    have h := probEvent_pivotal_mul_le (localDigestView digest) (0 : Fin (n + 1))
    rw [← probEvent_uniformDisclosureSet_function] at h
    calc
      _ = Pr[= digest | ($ᵗ MessageDigest : ProbComp _)] *
          (((n + 1 : Nat) : ℝ≥0∞) * Pr[fun word => PivotalPosition (localDigestView digest) word
            (0 : Fin (n + 1)) | ($ᵗ _ : ProbComp _)]) := by ring
      _ ≤ Pr[= digest | ($ᵗ MessageDigest : ProbComp _)] *
          (24 * Pr[ViewCovered (localDigestView digest) | uniformDisclosureSet (n + 1) ∅]) :=
        mul_le_mul' le_rfl h
      _ = _ := by ring
  · simp only [independentMarginalWeight, futureCoverWeight, hland, if_false, mul_zero, le_rfl]

end LeanSphincs.Lifetime
