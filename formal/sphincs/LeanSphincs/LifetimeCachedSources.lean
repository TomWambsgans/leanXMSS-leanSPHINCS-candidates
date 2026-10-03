import LeanSphincs.LifetimeGrindingCost

/-! Actual contributions of completed adversarial prequeries selected later by the signer.
The contribution is weighted by its cached digest, and zero for already recorded sources.
No claim of uniformity is made for these newly selected cached views. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

def HasRecordedSource (records : List SourceRecord) (source : DigestCandidate) : Prop :=
  ∃ record ∈ records, record.source = source

variable [Params]

noncomputable def cachedUnrecordedSourceCharge (sk : Seeded.SecretKey) (records : List SourceRecord)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) (source : DigestCandidate) : ℝ≥0∞ := by
  classical
  exact if HasRecordedSource records source then 0 else
    match cache (candidateInput sk source 0), cache (candidateInput sk source 1) with
    | some first, some second => if Landed sk.parameter (blockIndex first) then
        weight (truncateMessageDigest first second) else 0
    | _, _ => 0

noncomputable def cachedRecordContribution (sk : Seeded.SecretKey) (records : List SourceRecord)
    (cache : QueryCache HashSpec) (weight : MessageDigest → ℝ≥0∞) (record : SourceRecord) : ℝ≥0∞ := by
  classical
  exact if HasRecordedSource records record.source then 0 else
    if CachedSource sk cache record.source record.digest then weight record.digest else 0

theorem cachedRecordContribution_eq_charge (sk : Seeded.SecretKey) (records : List SourceRecord)
    (before after : QueryCache HashSpec) (hcache : before ≤ after)
    (weight : MessageDigest → ℝ≥0∞) (record : SourceRecord)
    (hrecord : SourceRecordConsistent sk after record) :
    cachedRecordContribution sk records before weight record =
      cachedUnrecordedSourceCharge sk records before weight record.source := by
  classical
  unfold cachedRecordContribution cachedUnrecordedSourceCharge
  by_cases hprevious : HasRecordedSource records record.source
  · simp only [hprevious, if_true]
  · simp only [hprevious, if_false]
    cases hfirst : before (candidateInput sk record.source 0) with
    | none =>
      have hnone : ¬CachedSource sk before record.source record.digest := by
        rintro ⟨first, second, hcached, _, _⟩
        rw [hfirst] at hcached
        contradiction
      simp only [hnone, if_false]
    | some first =>
      cases hsecond : before (candidateInput sk record.source 1) with
      | none =>
        have hnone : ¬CachedSource sk before record.source record.digest := by
          rintro ⟨first, second, _, hcached, _⟩
          rw [hsecond] at hcached
          contradiction
        simp only [hnone, if_false]
      | some second =>
        have hsource : CachedSource sk before record.source (truncateMessageDigest first second) :=
          ⟨first, second, hfirst, hsecond, rfl⟩
        have hdigest := CachedSource.unique sk after record.source record.digest
          (truncateMessageDigest first second) hrecord.1
          (hsource.mono sk before after hcache _ _)
        have hland : Landed sk.parameter (blockIndex first) := by
          simpa only [hdigest, digestIndex_truncate] using hrecord.2.1
        simp only [hdigest, hsource, hland, if_true]

noncomputable def newCachedDisclosureWeight (sk : Seeded.SecretKey) (before : SourcedState)
    (weight : MessageDigest → ℝ≥0∞) (after : List SourceRecord) : ℝ≥0∞ :=
  match after with
  | [] => 0
  | record :: rest => if rest = before.1 then cachedRecordContribution sk before.1 before.2 weight record else 0

omit [Params] in
theorem newCachedDisclosureWeight_same (sk : Seeded.SecretKey) (before : SourcedState)
    (weight : MessageDigest → ℝ≥0∞) : newCachedDisclosureWeight sk before weight before.1 = 0 := by
  cases hrecords : before.1 with
  | nil => rfl
  | cons record rest =>
    simp only [newCachedDisclosureWeight]
    rw [if_neg]
    intro heq
    have hlength := congrArg List.length heq
    rw [hrecords, List.length_cons] at hlength
    omega

/-- Source consistency identifies the actual newly disclosed view with its complete initial
cache entry. Repeated honest sources contribute zero and are not called new uniform samples. -/
theorem newCachedDisclosureWeight_eq_source_weight (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (hrecords : SourcesConsistent sk state.2 state.1)
    (weight : MessageDigest → ℝ≥0∞) (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSources sk message state)) :
    newCachedDisclosureWeight sk state weight result.2.1 =
      newSourceRecordWeight state.1 (cachedUnrecordedSourceCharge sk state.1 state.2 weight) result.2.1 := by
  obtain ⟨hcache, _, hconsistent⟩ := signWithSources_preserves sk message state hrecords result hresult
  rcases signWithSources_record_shape sk message state result hresult with
    ⟨_, hshape⟩ | ⟨randomness, digest, hshape⟩
  · rw [hshape, newCachedDisclosureWeight_same, newSourceRecordWeight_same]
  · rw [hshape] at hconsistent ⊢
    simp only [newCachedDisclosureWeight, newSourceRecordWeight_cons, if_true]
    exact cachedRecordContribution_eq_charge sk state.1 state.2 result.2.2 hcache weight _
      (hconsistent _ List.mem_cons_self)

/-- A concrete cached-source transfer bound for the full actual signer. The remaining price
is an explicit sum over cached digests, divided by the 128-bit randomizer space, and multiplied
only by actual expected grinding message queries. -/
theorem expected_newCachedDisclosureWeight_le (sk : Seeded.SecretKey) (message : Message)
    (state : SourcedState) (hrecords : SourcesConsistent sk state.2 state.1)
    (weight : MessageDigest → ℝ≥0∞) :
    (∑' result, Pr[= result | signWithSources sk message state] *
      newCachedDisclosureWeight sk state weight result.2.1) ≤
      (((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ * ∑ randomness : Randomness,
        cachedUnrecordedSourceCharge sk state.1 state.2 weight (message, randomness)) *
          Security.expectedHashCost (Randomized.signDigestLoop sk message digestAttemptLimit) state.2 := by
  have heq : (∑' result, Pr[= result | signWithSources sk message state] *
      newCachedDisclosureWeight sk state weight result.2.1) =
      ∑' result, Pr[= result | signWithSources sk message state] *
        newSourceRecordWeight state.1 (cachedUnrecordedSourceCharge sk state.1 state.2 weight) result.2.1 := by
    apply tsum_congr
    intro result
    by_cases hresult : result ∈ support (signWithSources sk message state)
    · rw [newCachedDisclosureWeight_eq_source_weight sk message state hrecords weight result hresult]
    · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
  rw [heq]
  simpa only [randomizerAverage_card] using
    expected_signWithSources_weight_le_grinding_cost sk message state
      (cachedUnrecordedSourceCharge sk state.1 state.2 weight)

end LeanSphincs.Lifetime
