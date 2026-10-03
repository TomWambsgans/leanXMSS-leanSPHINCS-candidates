import LeanSphincs.LifetimeGainCoordinates
import LeanSphincs.LifetimeGainBudget

/-! Active candidate accounting. A candidate leaves the FORS bank when its own source is
accepted. Successful own-source forgeries are handled by the strong-forgery primitive branch;
failed assembly at that index is handled by `SecurityReferenceFailure`. Dropping a target
has an explicit prior-forecast cost, rather than being hidden in a martingale claim. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete
attribute [local instance] Classical.propDecidable

variable [Params]

noncomputable def activeFutureWeight (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) : ℝ≥0∞ :=
  ∑ target ∈ bank, futureCoverWeight parameter n prior (digest target)

noncomputable def activeIndependentMean (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) : ℝ≥0∞ :=
  ∑ target ∈ bank, independentGainMean parameter n prior (digest target)

noncomputable def activeSourceGain (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (source : DigestCandidate)
    (sourceDigest : MessageDigest) : ℝ≥0∞ :=
  ∑ target ∈ bank.erase source,
    futureCoverageGain parameter n prior (localDigestView sourceDigest) (digest target)

noncomputable def removedPriorWeight (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (source : DigestCandidate) : ℝ≥0∞ :=
  if source ∈ bank then futureCoverWeight parameter n prior (digest source) else 0

theorem activeFutureWeight_succ (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) :
    activeFutureWeight parameter (n + 1) prior bank digest =
      activeFutureWeight parameter n prior bank digest + activeIndependentMean parameter n prior bank digest := by
  simp only [activeFutureWeight, activeIndependentMean, futureCoverWeight_succ_gain, Finset.sum_add_distrib]

/-- One actual accepted source spends one independent slot, erases its own target, and adds
its digest to the common disclosure history. The removed forecast is accounted separately. -/
theorem activeFutureWeight_insert_erase (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (source : DigestCandidate) (sourceDigest : MessageDigest) :
    activeFutureWeight parameter n (insert (localDigestView sourceDigest) prior) (bank.erase source) digest +
      activeIndependentMean parameter n prior bank digest + removedPriorWeight parameter n prior bank digest source =
        activeFutureWeight parameter (n + 1) prior bank digest +
          activeSourceGain parameter n prior bank digest source sourceDigest := by
  have herase : activeFutureWeight parameter n prior (bank.erase source) digest +
      removedPriorWeight parameter n prior bank digest source = activeFutureWeight parameter n prior bank digest := by
    by_cases hmem : source ∈ bank
    · simpa only [activeFutureWeight, removedPriorWeight, hmem, if_true] using
        Finset.sum_erase_add bank (fun target => futureCoverWeight parameter n prior (digest target)) hmem
    · simp only [activeFutureWeight, removedPriorWeight, hmem, if_false,
        Finset.erase_eq_of_notMem hmem, add_zero]
  rw [activeFutureWeight_succ]
  have hins : activeFutureWeight parameter n (insert (localDigestView sourceDigest) prior) (bank.erase source) digest =
      activeFutureWeight parameter n prior (bank.erase source) digest +
        activeSourceGain parameter n prior bank digest source sourceDigest := by
    simp only [activeFutureWeight, activeSourceGain, futureCoverWeight_insert, Finset.sum_add_distrib]
  rw [hins]
  calc
    _ = (activeFutureWeight parameter n prior (bank.erase source) digest +
        removedPriorWeight parameter n prior bank digest source) +
        activeIndependentMean parameter n prior bank digest +
        activeSourceGain parameter n prior bank digest source sourceDigest := by ac_rfl
    _ = _ := by rw [herase]

theorem activeIndependentMean_mul_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) :
    ((n + 1 : Nat) : ℝ≥0∞) * activeIndependentMean parameter n prior bank digest ≤
      24 * activeFutureWeight parameter (n + 1) prior bank digest := by
  simp only [activeFutureWeight, activeIndependentMean, Finset.mul_sum]
  exact Finset.sum_le_sum (fun target _ => independentGainMean_mul_le parameter n prior (digest target))

/-- A previously covered target has zero insertion gain for every possible source, including
every shared future pool. This permits erased targets to be restored to a fixed kernel bank. -/
theorem futureCoverageGain_zero_of_covered (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (source : KeptDigestView) (target : MessageDigest)
    (hcovered : ViewCovered (localDigestView target) prior) :
    futureCoverageGain parameter n prior source target = 0 := by
  rw [futureCoverageGain]
  split
  · rw [uniformDisclosureSet, probEvent_map]
    calc
      _ = Pr[fun _ : List KeptDigestView => False |
          SphincsSecurity.Concrete.sampleUniformProposalWord KeptDigestView n] := by
        apply probEvent_ext
        intro word _
        exact iff_false_intro (fun hgain => hgain.1
          (viewCovered_mono (localDigestView target) Finset.subset_union_right hcovered))
      _ = 0 := probEvent_False _
  · rfl

theorem viewCovered_self_mem (target : KeptDigestView) (prior : Finset KeptDigestView)
    (hmem : target ∈ prior) : ViewCovered target prior :=
  fun _ => ⟨target, hmem, rfl, rfl⟩

/-- The active bank need not be fixed before oracle queries. Its omitted targets contribute
zero because their own accepted view already belongs to the current common history. -/
theorem activeSourceGain_restore_bank (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (active bank : Finset DigestCandidate)
    (hsub : active ⊆ bank) (digest : DigestCandidate → MessageDigest)
    (homitted : ∀ target ∈ bank, target ∉ active → localDigestView (digest target) ∈ prior)
    (source : DigestCandidate) (sourceDigest : MessageDigest) :
    activeSourceGain parameter n prior active digest source sourceDigest =
      activeSourceGain parameter n prior bank digest source sourceDigest := by
  apply Finset.sum_subset (Finset.erase_subset_erase source hsub)
  intro target hbank hnot
  have ht : target ∉ active := by
    intro hactive
    exact hnot (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hbank).1, hactive⟩)
  exact futureCoverageGain_zero_of_covered parameter n prior (localDigestView sourceDigest) (digest target)
    (viewCovered_self_mem _ prior (homitted target (Finset.mem_erase.mp hbank).2 ht))

noncomputable def activeBankAfter (before after : List SourceRecord) (bank : Finset DigestCandidate) :
    Finset DigestCandidate :=
  match after with
  | [] => bank
  | record :: rest => if rest = before then bank.erase record.source else bank

omit [Params] in
theorem activeBankAfter_same (records : List SourceRecord) (bank : Finset DigestCandidate) :
    activeBankAfter records records bank = bank := by
  cases records with
  | nil => rfl
  | cons record rest =>
    rw [activeBankAfter, if_neg]
    intro h
    have := congrArg List.length h
    simp only [List.length_cons] at this
    omega

/-- The identity applies directly to every supported complete comparison signing call.
It uses the actual randomizer and digest chosen by message grinding; the suffix is arbitrary. -/
theorem signWithSourcesThen_active_identity (sk : Seeded.SecretKey) (message : Message)
    (suffix : SigningSuffix) (state : SourcedState) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (n : Nat) (result : Option Signature × SourcedState)
    (hresult : result ∈ support (signWithSourcesThen sk message suffix state)) :
    activeFutureWeight sk.parameter n (sourcedPrior result.2.1) (activeBankAfter state.1 result.2.1 bank) digest +
      activeIndependentMean sk.parameter n (sourcedPrior state.1) bank digest +
      newSourceDigestWeight state.1 (fun source _ =>
        removedPriorWeight sk.parameter n (sourcedPrior state.1) bank digest source) result.2.1 =
        activeFutureWeight sk.parameter (n + 1) (sourcedPrior state.1) bank digest +
          newSourceDigestWeight state.1
            (activeSourceGain sk.parameter n (sourcedPrior state.1) bank digest) result.2.1 := by
  rcases signWithSourcesThen_record_shape sk message suffix state result hresult with
    ⟨_, hsame⟩ | ⟨randomness, sourceDigest, hcons⟩
  · simp only [hsame, activeBankAfter_same, newSourceDigestWeight_same, add_zero, activeFutureWeight_succ]
  · rw [hcons, sourcedPrior_cons]
    simp only [activeBankAfter, newSourceDigestWeight, if_true]
    exact activeFutureWeight_insert_erase sk.parameter n (sourcedPrior state.1) bank digest
      (message, randomness) sourceDigest

/-- Every active candidate has exactly one randomizer in its message's pool. This sum
therefore charges a removed prior forecast once, with no extra candidate-count factor. -/
theorem sum_removedPriorWeight_le (parameter : PublicParameter) (n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (message : Message) :
    (∑ randomness : Randomness, removedPriorWeight parameter n prior bank digest (message, randomness)) ≤
      activeFutureWeight parameter n prior bank digest := by
  let randomizers : Finset Randomness := Finset.univ.filter (fun randomness => (message, randomness) ∈ bank)
  have hsub : randomizers.image (fun randomness => (message, randomness)) ⊆ bank := by
    intro candidate hcandidate
    obtain ⟨randomness, hmem, rfl⟩ := Finset.mem_image.mp hcandidate
    exact (Finset.mem_filter.mp hmem).2
  calc
    _ = ∑ randomness ∈ randomizers, futureCoverWeight parameter n prior (digest (message, randomness)) := by
      simp only [randomizers, Finset.sum_filter, removedPriorWeight]
    _ = ∑ candidate ∈ randomizers.image (fun randomness => (message, randomness)),
        futureCoverWeight parameter n prior (digest candidate) := by
      rw [Finset.sum_image]
      intro left _ right _ heq
      exact congrArg Prod.snd heq
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

/-- The exact finite-pool grinding law bounds removal by current bank price divided by
accepted-pool size. Repeated draws and finite exhaustion are already included in the sampler.
This is the small removal term in the common-history gain occupation account. -/
theorem expected_pool_removedPriorWeight_le (parameter : PublicParameter) (pool : IndexPool)
    (hpositive : 0 < poolAcceptedCount parameter pool) (attempts n : Nat)
    (prior : Finset KeptDigestView) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (message : Message) :
    (∑ randomness : Randomness, Pr[= some randomness | poolGrindRandomness parameter pool attempts] *
      removedPriorWeight parameter n prior bank digest (message, randomness)) ≤
      activeFutureWeight parameter n prior bank digest / (poolAcceptedCount parameter pool : ℝ≥0∞) := by
  rw [poolGrindRandomness_weighted parameter pool hpositive]
  calc
    _ ≤ ((1 : ℝ≥0∞) / (poolAcceptedCount parameter pool : ℝ≥0∞)) *
        ∑ randomness : Randomness, removedPriorWeight parameter n prior bank digest (message, randomness) := by
      exact mul_le_mul' (ENNReal.div_le_div_right probEvent_le_one _)
        (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    _ ≤ ((1 : ℝ≥0∞) / (poolAcceptedCount parameter pool : ℝ≥0∞)) *
        activeFutureWeight parameter n prior bank digest :=
      mul_le_mul' le_rfl (sum_removedPriorWeight_le parameter n prior bank digest message)
    _ = _ := by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv, mul_comm]

end LeanSphincs.Lifetime
