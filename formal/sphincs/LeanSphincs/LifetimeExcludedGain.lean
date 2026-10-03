import LeanSphincs.LifetimeComparisonTransition

/-! Target-specific source exclusion in the common comparison history. Accepted but failed
signing calls may be included in the proof-side disclosure set, but a target cannot obtain
coverage from its own message/randomizer pair. Each target's prior is a subset of the same
common history, which suffices for simultaneous rectangle localization. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete
attribute [local instance] Classical.propDecidable

variable [Params]

/-- Includes every accepted digest, including failed WOTS assembly, while removing every
record with this target's source label. -/
def excludedPrior (target : DigestCandidate) (records : List SourceRecord) : Finset KeptDigestView :=
  ((records.filter (fun record => record.source ≠ target)).map
    (fun record => localDigestView record.digest)).toFinset

theorem excludedPrior_subset (target : DigestCandidate) (records : List SourceRecord) :
    excludedPrior target records ⊆ sourcedPrior records := by
  intro view hview
  simp only [excludedPrior, List.mem_toFinset, List.mem_map, List.mem_filter] at hview
  obtain ⟨record, ⟨hrecord, _⟩, rfl⟩ := hview
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨record, hrecord, rfl⟩)

/-- The proof-side set includes every eligible actually successful disclosure. -/
theorem sourceExcludedViews_subset_excludedPrior (target : DigestCandidate) (records : List SourceRecord) :
    sourceExcludedViews target records ⊆ excludedPrior target records := by
  intro view hview
  obtain ⟨record, hrecord, rfl⟩ := Finset.mem_image.mp hview
  obtain ⟨hmem, hne, _⟩ := Finset.mem_filter.mp hrecord
  simp only [excludedPrior, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨record, ⟨List.mem_toFinset.mp hmem, hne⟩, rfl⟩

theorem excludedPrior_cons (target : DigestCandidate) (record : SourceRecord) (records : List SourceRecord) :
    excludedPrior target (record :: records) =
      if record.source = target then excludedPrior target records else
        insert (localDigestView record.digest) (excludedPrior target records) := by
  by_cases heq : record.source = target <;>
    simp [excludedPrior, heq]

noncomputable def excludedSourceGain (parameter : PublicParameter) (n : Nat)
    (records : List SourceRecord) (target : DigestCandidate) (targetDigest : MessageDigest)
    (source : DigestCandidate) (sourceDigest : MessageDigest) : ℝ≥0∞ :=
  if source = target then 0 else
    futureCoverageGain parameter n (excludedPrior target records) (localDigestView sourceDigest) targetDigest

/-- The actual selected source contributes zero to its own target, including when WOTS
assembly fails. Other targets receive the same accepted digest insertion as before. -/
theorem signWithSourcesThen_excluded_gain (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix) (state : SourcedState) (n : Nat) (target : DigestCandidate)
    (targetDigest : MessageDigest) (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSourcesThen sk message suffix state)) :
    futureCoverWeight sk.parameter n (excludedPrior target result.2.1) targetDigest =
      futureCoverWeight sk.parameter n (excludedPrior target state.1) targetDigest +
        newSourceDigestWeight state.1 (excludedSourceGain sk.parameter n state.1 target targetDigest) result.2.1 := by
  rcases signWithSourcesThen_record_shape sk message suffix state result hresult with
    ⟨_, hsame⟩ | ⟨randomness, digest, hcons⟩
  · simp only [hsame, newSourceDigestWeight_same, add_zero]
  · rw [hcons, excludedPrior_cons]
    simp only [newSourceDigestWeight, if_true]
    by_cases heq : (message, randomness) = target
    · simp only [heq, if_true, excludedSourceGain, add_zero]
    · simp only [heq, if_false, excludedSourceGain, futureCoverWeight_insert]

/-- The local changing-kernel identity for the actual comparison signer uses the target's
own excluded prior on both sides. It does not require a successful response at that source. -/
theorem expected_signWithSourcesThen_excluded_centered (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix)
    (hmass : ∀ randomness digest cache, (∑' result, Pr[= result | suffix randomness digest cache]) = 1)
    (state : SourcedState) (n : Nat) (target : DigestCandidate) (targetDigest : MessageDigest) :
    (∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
      futureCoverWeight sk.parameter n (excludedPrior target result.2.1) targetDigest) +
        independentGainMean sk.parameter n (excludedPrior target state.1) targetDigest =
      futureCoverWeight sk.parameter (n + 1) (excludedPrior target state.1) targetDigest +
        ∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
          newSourceDigestWeight state.1 (excludedSourceGain sk.parameter n state.1 target targetDigest) result.2.1 := by
  have hgain : (∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
      futureCoverWeight sk.parameter n (excludedPrior target result.2.1) targetDigest) =
      futureCoverWeight sk.parameter n (excludedPrior target state.1) targetDigest +
        ∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
          newSourceDigestWeight state.1 (excludedSourceGain sk.parameter n state.1 target targetDigest) result.2.1 := by
    calc
      _ = ∑' result, Pr[= result | signWithSourcesThen sk message suffix state] *
          (futureCoverWeight sk.parameter n (excludedPrior target state.1) targetDigest +
            newSourceDigestWeight state.1 (excludedSourceGain sk.parameter n state.1 target targetDigest) result.2.1) := by
        apply tsum_congr
        intro result
        by_cases hresult : result ∈ support (signWithSourcesThen sk message suffix state)
        · rw [signWithSourcesThen_excluded_gain sk message suffix state n target targetDigest result hresult]
        · simp only [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]
      _ = _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
          signWithSourcesThen_mass sk message suffix hmass state, one_mul]
  rw [hgain, futureCoverWeight_succ_gain]
  ac_rfl

/-- A gain for a target-specific subhistory still lies in the rectangle built from the
common history. No monotonicity of the gain itself is claimed. -/
theorem coverageGain_subprior_rectangle (target source : KeptDigestView)
    (prior common : Finset KeptDigestView) (hsub : prior ⊆ common)
    (hgain : CoverageGain target source prior) :
    FixedKeptCovered source.1 (viewCoordinates (insert source common) source.1) target := by
  have hindex := coverageGain_index_eq target source prior hgain
  refine ⟨hindex.symm, ?_⟩
  intro tree
  have hcovered := viewCovered_mono target (Finset.insert_subset_insert source hsub) hgain.2
  obtain ⟨view, hview, hi, ht⟩ := hcovered tree
  exact Finset.mem_image.mpr ⟨view, Finset.mem_filter.mpr ⟨hview, hi.trans hindex.symm⟩, ht⟩

noncomputable def excludedBankGain (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (source : DigestCandidate)
    (sourceView : KeptDigestView) (common : Finset KeptDigestView)
    (prior : DigestCandidate → Finset KeptDigestView) : Nat :=
  (bank.filter (fun target => target ≠ source ∧ Landed parameter (digestIndex (digest target)) ∧
    ViewCap 255 common ∧ CoverageGain (localDigestView (digest target)) sourceView (prior target))).card

/-- The one simultaneous event supplies the same pointwise cap when every target excludes
its own source records from the preceding actual history. -/
theorem excludedBankGain_le (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (hsparse : RectangleBankSparse parameter bank digest)
    (source : DigestCandidate) (sourceView : KeptDigestView) (common : Finset KeptDigestView)
    (prior : DigestCandidate → Finset KeptDigestView) (hsub : ∀ target ∈ bank, prior target ⊆ common) :
    excludedBankGain parameter bank digest source sourceView common prior ≤ 2 ^ 56 := by
  by_cases hcap : ViewCap 255 common
  · let rectangle : DigestRectangle := (sourceView.1, viewCoordinates (insert sourceView common) sourceView.1)
    have hsmall : SmallRectangle rectangle :=
      fun tree => viewCoordinates_card_le (viewCap_insert hcap sourceView) sourceView.1 tree
    refine (Finset.card_le_card ?_).trans (hsparse rectangle hsmall).le
    intro target htarget
    obtain ⟨hmem, _, hland, _, hgain⟩ := Finset.mem_filter.mp htarget
    exact Finset.mem_filter.mpr ⟨hmem, hland,
      coverageGain_subprior_rectangle _ sourceView (prior target) common (hsub target hmem) hgain⟩
  · simp only [excludedBankGain, hcap, false_and, and_false, Finset.filter_false, Finset.card_empty]
    exact Nat.zero_le _

theorem excludedBankGain_square_le (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (hsparse : RectangleBankSparse parameter bank digest)
    (source : DigestCandidate) (sourceView : KeptDigestView) (common : Finset KeptDigestView)
    (prior : DigestCandidate → Finset KeptDigestView) (hsub : ∀ target ∈ bank, prior target ⊆ common) :
    (excludedBankGain parameter bank digest source sourceView common prior : ℝ≥0∞) ^ 2 ≤
      (2 : ℝ≥0∞) ^ 56 * excludedBankGain parameter bank digest source sourceView common prior := by
  rw [pow_two]
  apply mul_le_mul' _ le_rfl
  exact_mod_cast excludedBankGain_le parameter bank digest hsparse source sourceView common prior hsub

end LeanSphincs.Lifetime
