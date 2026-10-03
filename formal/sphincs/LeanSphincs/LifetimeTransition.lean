import LeanSphincs.LifetimeConditionalSources
import LeanSphincs.LifetimeMarginal

/-! The exact changing-coverage-kernel identity for an actual complete signing call.
The independent continuation retains every future sample: inserting the accepted source
does not displace a sample. The signer's drift is exactly its selected marginal gain minus
the independent source's mean gain, written without subtraction in `ENNReal`.
Overflow localization is applied to the marginal kernel separately. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

attribute [local instance] Classical.propDecidable

variable [Params]

def CoverageGain (target source : KeptDigestView) (prior : Finset KeptDigestView) : Prop :=
  ¬ViewCovered target prior ∧ ViewCovered target (insert source prior)

theorem uniformDisclosureSet_insert (n : Nat) (prior : Finset KeptDigestView) (source : KeptDigestView) :
    uniformDisclosureSet n (insert source prior) = (insert source) <$> uniformDisclosureSet n prior := by
  simp only [uniformDisclosureSet, Functor.map_map]
  congr 1
  funext word
  exact Finset.union_insert _ _ _

theorem probEvent_coverage_insert (sample : ProbComp (Finset KeptDigestView))
    (target source : KeptDigestView) :
    Pr[fun prior => ViewCovered target (insert source prior) | sample] =
      Pr[ViewCovered target | sample] + Pr[CoverageGain target source | sample] := by
  simp only [probEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  apply tsum_congr
  intro prior
  by_cases hbefore : ViewCovered target prior
  · have hafter := viewCovered_mono target (Finset.subset_insert source prior) hbefore
    simp only [hbefore, hafter, CoverageGain, not_true_eq_false, false_and, if_true, if_false, add_zero]
  · by_cases hafter : ViewCovered target (insert source prior) <;>
      simp only [hbefore, hafter, CoverageGain, not_false_eq_true, true_and, if_true, if_false, zero_add]

noncomputable def futureCoverageGain (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) : ℝ≥0∞ :=
  if Landed parameter (digestIndex target) then
    Pr[CoverageGain (localDigestView target) source | uniformDisclosureSet n prior] else 0

/-- Exact coupled insertion: the same independent future set appears on both sides. -/
theorem futureCoverWeight_insert (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest) :
    futureCoverWeight parameter n (insert source prior) target =
      futureCoverWeight parameter n prior target + futureCoverageGain parameter n prior source target := by
  by_cases hland : Landed parameter (digestIndex target)
  · simp only [futureCoverWeight, futureCoverageGain, hland, if_true,
      uniformDisclosureSet_insert, probEvent_map, Function.comp_def]
    exact probEvent_coverage_insert _ _ _
  · simp only [futureCoverWeight, futureCoverageGain, hland, if_false, zero_add]

noncomputable def independentGainMean (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (target : MessageDigest) : ℝ≥0∞ :=
  ∑' source, Pr[= source | ($ᵗ KeptDigestView : ProbComp _)] * futureCoverageGain parameter n prior source target

/-- The independent continuation spends one sampling slot and pays exactly its average
marginal gain. This is the local martingale identity with the changing kernel. -/
theorem futureCoverWeight_succ_gain (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (target : MessageDigest) :
    futureCoverWeight parameter (n + 1) prior target =
      futureCoverWeight parameter n prior target + independentGainMean parameter n prior target := by
  rw [futureCoverWeight_succ]
  simp only [futureCoverWeight_insert, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
    tsum_probOutput_eq_one' (probFailure_uniformSample _), one_mul, independentGainMean]

theorem signWithSources_mass (sk : Seeded.SecretKey) (message : Message) (state : SourcedState) :
    (∑' result, Pr[= result | signWithSources sk message state]) = 1 := by
  apply tsum_probOutput_eq_one'
  have h := congrArg (fun process => Pr[⊥ | process]) (signWithSources_forget sk message state)
  simp only [probFailure_map] at h
  rw [h, ← Security.erase_countedRun, probFailure_map, Security.countedRun_failure]

/-- Every accepted digest is inserted, including one whose WOTS assembly later exhausts.
Grinding exhaustion leaves the set unchanged and contributes zero marginal gain. -/
theorem signWithSources_future_gain (sk : Seeded.SecretKey) (message : Message) (state : SourcedState)
    (n : Nat) (target : MessageDigest) (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSources sk message state)) :
    futureCoverWeight sk.parameter n (sourcedPrior result.2.1) target =
      futureCoverWeight sk.parameter n (sourcedPrior state.1) target +
        newSourceDigestWeight state.1 (fun _ digest =>
          futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1 := by
  rcases signWithSources_record_shape sk message state result hresult with ⟨_, hsame⟩ | ⟨randomness, digest, hcons⟩
  · simp only [hsame, newSourceDigestWeight_same, add_zero]
  · rw [hcons, sourcedPrior_cons, futureCoverWeight_insert]
    simp only [newSourceDigestWeight, if_true]

/-- Exact centered drift of the actual complete signer with an arbitrary adversarial cache.
No independent-source claim is made: its selected-gain expectation remains the actual one.
The equality isolates precisely the quantity that the centered source bank must control. -/
theorem expected_signWithSources_centered_gain (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (n : Nat) (target : MessageDigest) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      futureCoverWeight sk.parameter n (sourcedPrior result.2.1) target) +
        independentGainMean sk.parameter n (sourcedPrior state.1) target =
      futureCoverWeight sk.parameter (n + 1) (sourcedPrior state.1) target +
        ∑' result, Pr[= result | signWithSources sk message state] *
          newSourceDigestWeight state.1 (fun _ digest =>
            futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1 := by
  have hgain : (∑' result, Pr[= result | signWithSources sk message state] *
      futureCoverWeight sk.parameter n (sourcedPrior result.2.1) target) =
      futureCoverWeight sk.parameter n (sourcedPrior state.1) target +
        ∑' result, Pr[= result | signWithSources sk message state] *
          newSourceDigestWeight state.1 (fun _ digest =>
            futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1 := by
    calc
      _ = ∑' result, Pr[= result | signWithSources sk message state] *
          (futureCoverWeight sk.parameter n (sourcedPrior state.1) target +
            newSourceDigestWeight state.1 (fun _ digest =>
              futureCoverageGain sk.parameter n (sourcedPrior state.1) (localDigestView digest) target) result.2.1) := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (signWithSources sk message state)
        · rw [signWithSources_future_gain sk message state n target result hresult]
        · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      _ = _ := by simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, signWithSources_mass, one_mul]
  rw [hgain, futureCoverWeight_succ_gain]
  ac_rfl

end LeanSphincs.Lifetime
