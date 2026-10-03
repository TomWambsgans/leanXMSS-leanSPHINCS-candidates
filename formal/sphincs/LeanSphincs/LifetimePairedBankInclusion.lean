import LeanSphincs.LifetimePairedBank

/-! Every candidate that becomes known during a paired execution belongs to its first-touch
bank. Consequently a transcript-selected subset inherits the simultaneous rectangle bound. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem pairedHash_candidate_unchanged (sk : Seeded.SecretKey) (input : HashInput)
    (candidate : DigestCandidate) (call : Fin 2) (before : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((pairedHash sk input).run before))
    (hother : ∀ position, decodeCandidateInput sk input = some position → candidate ≠ position.1) :
    result.2 (candidateInput sk candidate call) = before (candidateInput sk candidate call) := by
  simp only [pairedHash, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hrest⟩ := hresult
  cases hp : decodeCandidateInput sk input with
  | none =>
      simp only [hp, StateT.run_pure, mem_support_pure_iff] at hrest
      cases hrest
      exact query_other_cache_eq input _ (decodeCandidateInput_none_ne sk input hp candidate call)
        before first hfirst
  | some position =>
      have hinput := decodeCandidateInput_some sk input position hp
      have hne := hother position hp
      have hneq (i : Fin 2) : candidateInput sk candidate call ≠ candidateInput sk position.1 i :=
        fun h => hne (candidateInput_candidate_injective sk call i h)
      simp only [hp, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, mem_support_pure_iff] at hrest
      obtain ⟨second, hsecond, rfl⟩ := hrest
      rw [query_other_cache_eq _ _ (hneq _) first.2 second hsecond]
      exact query_other_cache_eq input _ (by simpa only [← hinput] using hneq position.2) before first hfirst

theorem paired_query_new_candidate_record (sk : Seeded.SecretKey) (record : QueryRecord)
    (candidate : DigestCandidate) (hpaired : PairedCache sk record.2.1)
    (hrun : (record.2.2.1, record.2.2.2) ∈ support ((pairedRom sk record.1).run record.2.1))
    (hbefore : record.2.1 (candidateInput sk candidate 0) = none)
    (hafter : record.2.2.2 (candidateInput sk candidate 0) ≠ none) :
    freshCandidateRecord sk record = some (candidate, cachedPairDigest sk candidate record.2.2.2) := by
  rcases record with ⟨input, before, answer, after⟩
  cases input with
  | inl input =>
      change (answer, after) ∈ support
        ((fun answer => (answer, before)) <$> (liftM (unifSpec.query input) : ProbComp _)) at hrun
      rw [support_map] at hrun
      obtain ⟨_, _, heq⟩ := hrun
      cases heq
      exact False.elim (hafter hbefore)
  | inr input =>
      have hexists : ∃ position, decodeCandidateInput sk input = some position ∧ candidate = position.1 := by
        by_contra hnone
        push Not at hnone
        exact hafter ((pairedHash_candidate_unchanged sk input candidate 0 before (answer, after) hrun hnone).trans hbefore)
      obtain ⟨position, hposition, hc⟩ := hexists
      subst candidate
      have hfresh : before (candidateInput sk position.1 position.2) = none :=
        hpaired.fresh position.1 0 hbefore position.2
      simp only [freshCandidateRecord, hposition, hfresh, ↓reduceIte]

/-- Cache membership cannot arise without a corresponding first-touch transcript record. -/
theorem traceRun_cached_candidate_mem_bank {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hpaired : PairedCache sk before)
    (result : α × List QueryRecord × QueryCache HashSpec)
    (hresult : result ∈ support (traceRun (pairedRom sk) program before))
    (candidate : DigestCandidate) (hfresh : before (candidateInput sk candidate 0) = none)
    (hknown : result.2.2 (candidateInput sk candidate 0) ≠ none) :
    candidate ∈ traceCandidateBank sk result.2.1 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [traceRun_pure, mem_support_pure_iff] at hresult
      cases hresult
      exact False.elim (hknown hfresh)
  | query_bind input next ih =>
      simp only [traceRun_query_bind, mem_support_bind_iff, mem_support_pure_iff] at hresult
      obtain ⟨first, hfirst, last, hlast, rfl⟩ := hresult
      have hmid := (pairedRom_support_paired sk input before hpaired first.1 first.2 hfirst).1
      by_cases hmiddle : first.2 (candidateInput sk candidate 0) = none
      · have htail := ih first.1 first.2 hmid last hlast hmiddle hknown
        simp only [traceCandidateBank, List.mem_toFinset, List.mem_map] at htail ⊢
        obtain ⟨pair, hpair, hfst⟩ := htail
        exact ⟨pair, List.mem_filterMap.mpr (by
          obtain ⟨record, hrecord, heq⟩ := List.mem_filterMap.mp hpair
          exact ⟨record, List.mem_cons_of_mem _ hrecord, heq⟩), hfst⟩
      · have hrecord := paired_query_new_candidate_record sk ⟨input, before, first.1, first.2⟩
          candidate hpaired hfirst hfresh hmiddle
        simp only [traceCandidateBank, List.mem_toFinset, List.mem_map]
        refine ⟨(candidate, cachedPairDigest sk candidate first.2), ?_, rfl⟩
        exact List.mem_filterMap.mpr ⟨⟨input, before, first.1, first.2⟩, List.mem_cons_self, hrecord⟩

variable [Params]

theorem RectangleBankSparse.mono (parameter : PublicParameter) (small large : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (hsubset : small ⊆ large)
    (hsparse : RectangleBankSparse parameter large digest) : RectangleBankSparse parameter small digest := by
  intro rectangle hsmall
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hsubset)).trans_lt (hsparse rectangle hsmall)

/-- Any finite selection of newly cached candidates lies in the localized first-touch bank. -/
theorem traceRun_selected_bank_sparse {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hpaired : PairedCache sk before)
    (result : α × List QueryRecord × QueryCache HashSpec)
    (hresult : result ∈ support (traceRun (pairedRom sk) program before))
    (bank : Finset DigestCandidate)
    (hfresh : ∀ candidate ∈ bank, before (candidateInput sk candidate 0) = none)
    (hknown : ∀ candidate ∈ bank, result.2.2 (candidateInput sk candidate 0) ≠ none)
    (hsparse : RectangleBankSparse sk.parameter (traceCandidateBank sk result.2.1)
      (fun candidate => cachedPairDigest sk candidate result.2.2)) :
    RectangleBankSparse sk.parameter bank (fun candidate => cachedPairDigest sk candidate result.2.2) := by
  apply RectangleBankSparse.mono sk.parameter bank _ _ _ hsparse
  intro candidate hc
  exact traceRun_cached_candidate_mem_bank sk program before hpaired result hresult candidate
    (hfresh candidate hc) (hknown candidate hc)

/-- The selection may depend on the complete transcript and final cache. -/
theorem probEvent_selected_bank_not_sparse {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hpaired : PairedCache sk before)
    (bank : (α × List QueryRecord × QueryCache HashSpec) → Finset DigestCandidate)
    (hfresh : ∀ result ∈ support (traceRun (pairedRom sk) program before),
      ∀ candidate ∈ bank result, before (candidateInput sk candidate 0) = none)
    (hknown : ∀ result ∈ support (traceRun (pairedRom sk) program before),
      ∀ candidate ∈ bank result, result.2.2 (candidateInput sk candidate 0) ≠ none)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' before), result.2 ≤ q) :
    Pr[fun result => ¬RectangleBankSparse sk.parameter (bank result)
        (fun candidate => cachedPairDigest sk candidate result.2.2) |
      traceRun (pairedRom sk) program before] ≤ (1 : ℝ≥0∞) / 2 ^ 400 := by
  refine le_trans ?_ (probEvent_traceCandidateBank_not_sparse sk program before hpaired q hq hbound)
  apply probEvent_mono
  intro result hresult hbad hsparse
  exact hbad (traceRun_selected_bank_sparse sk program before hpaired result hresult (bank result)
    (hfresh result hresult) (hknown result hresult) hsparse)

end LeanSphincs.Lifetime
