import LeanSphincs.LifetimePairedRectangles

/-! Connecting newly touched digest records with the final paired cache. This lets the
simultaneous rectangle event control a finite candidate bank chosen from the actual transcript. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Both full blocks of a candidate are known. -/
def KnownPair (sk : Seeded.SecretKey) (candidate : DigestCandidate) (cache : QueryCache HashSpec) : Prop :=
  ∀ call, ∃ answer, cache (candidateInput sk candidate call) = some answer

theorem KnownPair.mono {sk : Seeded.SecretKey} {candidate : DigestCandidate}
    {before after : QueryCache HashSpec} (h : KnownPair sk candidate before) (hext : before ≤ after) :
    KnownPair sk candidate after := by
  intro call
  obtain ⟨answer, hanswer⟩ := h call
  exact ⟨answer, hext hanswer⟩

theorem PairedCache.known_of_cached {sk : Seeded.SecretKey} {candidate : DigestCandidate}
    {cache : QueryCache HashSpec} (hpaired : PairedCache sk cache) (call : Fin 2) (answer : HashOutput)
    (hknown : cache (candidateInput sk candidate call) = some answer) : KnownPair sk candidate cache := by
  intro i
  cases hi : cache (candidateInput sk candidate i) with
  | none =>
      have hfresh := hpaired.fresh candidate i hi call
      rw [hknown] at hfresh
      cases hfresh
  | some value => exact ⟨value, rfl⟩

theorem cachedPairDigest_mono (sk : Seeded.SecretKey) (candidate : DigestCandidate)
    (before after : QueryCache HashSpec) (hknown : KnownPair sk candidate before) (hext : before ≤ after) :
    cachedPairDigest sk candidate after = cachedPairDigest sk candidate before := by
  obtain ⟨first, hfirst⟩ := hknown 0
  obtain ⟨second, hsecond⟩ := hknown 1
  simp only [cachedPairDigest, hfirst, hsecond, hext hfirst, hext hsecond]

theorem pairedHash_support_cached (sk : Seeded.SecretKey) (input : HashInput)
    (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hresult : result ∈ support ((pairedHash sk input).run cache)) : result.2 input = some result.1 := by
  simp only [pairedHash, StateT.run_bind, mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hrest⟩ := hresult
  have hknown := (query_support_cached input cache first.1 first.2 hfirst).2
  cases hp : decodeCandidateInput sk input with
  | none =>
      simp only [hp, StateT.run_pure, mem_support_pure_iff] at hrest
      cases hrest
      exact hknown
  | some position =>
      simp only [hp, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, mem_support_pure_iff] at hrest
      obtain ⟨second, hsecond, rfl⟩ := hrest
      exact (query_support_cached _ _ _ _ hsecond).1 hknown

theorem traceRun_support_paired {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hpaired : PairedCache sk before)
    (result : α × List QueryRecord × QueryCache HashSpec)
    (hresult : result ∈ support (traceRun (pairedRom sk) program before)) :
    PairedCache sk result.2.2 ∧ before ≤ result.2.2 := by
  have hm : ((result.1, traceCost result.2.1), result.2.2) ∈ support
      ((simulateQ (pairedRom sk) (countHashQueries program)).run before) := by
    rw [← traceRun_erase, support_map]
    exact ⟨result, hresult, rfl⟩
  exact pairedRun_support_paired sk (countHashQueries program) before hpaired _ _ hm

theorem freshCandidateRecord_sound (sk : Seeded.SecretKey) (record : QueryRecord)
    (hpaired : PairedCache sk record.2.1)
    (hrun : (record.2.2.1, record.2.2.2) ∈ support ((pairedRom sk record.1).run record.2.1))
    (pair : DigestCandidate × MessageDigest) (hrecord : freshCandidateRecord sk record = some pair) :
    KnownPair sk pair.1 record.2.2.2 ∧ cachedPairDigest sk pair.1 record.2.2.2 = pair.2 := by
  rcases record with ⟨input, before, answer, after⟩
  cases input with
  | inl input => simp only [freshCandidateRecord] at hrecord; cases hrecord
  | inr input =>
      cases hp : decodeCandidateInput sk input with
      | none => simp only [freshCandidateRecord, hp] at hrecord; cases hrecord
      | some position =>
          simp only [freshCandidateRecord, hp] at hrecord
          split at hrecord
          · cases Option.some.inj hrecord
            have hafter := (pairedRom_support_paired sk (.inr input) before hpaired answer after hrun).1
            have hcached := pairedHash_support_cached sk input before (answer, after) hrun
            rw [← decodeCandidateInput_some sk input position hp] at hcached
            exact ⟨hafter.known_of_cached position.2 answer hcached, rfl⟩
          · cases hrecord

/-- Every recorded latent digest remains exactly the same in the final shared cache. -/
theorem traceRun_freshCandidates_sound {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hpaired : PairedCache sk before)
    (result : α × List QueryRecord × QueryCache HashSpec)
    (hresult : result ∈ support (traceRun (pairedRom sk) program before)) :
    ∀ pair ∈ freshCandidateTrace sk result.2.1,
      KnownPair sk pair.1 result.2.2 ∧ cachedPairDigest sk pair.1 result.2.2 = pair.2 := by
  induction program using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [traceRun_pure, mem_support_pure_iff] at hresult
      cases hresult
      simp only [freshCandidateTrace, List.filterMap_nil, List.not_mem_nil, false_implies, implies_true]
  | query_bind input next ih =>
      simp only [traceRun_query_bind, mem_support_bind_iff, mem_support_pure_iff] at hresult
      obtain ⟨first, hfirst, last, hlast, rfl⟩ := hresult
      have hmid := (pairedRom_support_paired sk input before hpaired first.1 first.2 hfirst).1
      have hext := (traceRun_support_paired sk (next first.1) first.2 hmid last hlast).2
      have htail := ih first.1 first.2 hmid last hlast
      intro pair hpair
      simp only [freshCandidateTrace, List.filterMap_cons] at hpair
      cases hr : freshCandidateRecord sk ⟨input, before, first.1, first.2⟩ with
      | none =>
          simp only [hr] at hpair
          exact htail pair hpair
      | some head =>
          simp only [hr, List.mem_cons] at hpair
          rcases hpair with rfl | hpair
          · obtain ⟨hknown, hdigest⟩ := freshCandidateRecord_sound sk _ hpaired hfirst pair hr
            exact ⟨hknown.mono hext, (cachedPairDigest_mono sk pair.1 first.2 last.2.2 hknown hext).trans hdigest⟩
          · exact htail pair hpair

noncomputable def traceCandidateBank (sk : Seeded.SecretKey) (trace : List QueryRecord) : Finset DigestCandidate :=
  ((freshCandidateTrace sk trace).map Prod.fst).toFinset

/-- Counting distinct candidates in any final-cache event is bounded by counting its
first-touch records. No independence and no uniqueness assumption on the record list is used. -/
theorem traceCandidateBank_event_le (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (trace : List QueryRecord) (after : QueryCache HashSpec)
    (hagree : ∀ pair ∈ freshCandidateTrace sk trace, cachedPairDigest sk pair.1 after = pair.2) :
    ((traceCandidateBank sk trace).filter (fun candidate => event (cachedPairDigest sk candidate after))).card ≤
      traceHits (pairedWorldHit sk event) trace := by
  let records := freshCandidateTrace sk trace
  let accepted := records.filter (fun pair => decide (event pair.2))
  have hsubset : (traceCandidateBank sk trace).filter (fun candidate => event (cachedPairDigest sk candidate after)) ⊆
      (accepted.map Prod.fst).toFinset := by
    intro candidate hc
    obtain ⟨hbank, hevent⟩ := Finset.mem_filter.mp hc
    rw [traceCandidateBank, List.mem_toFinset, List.mem_map] at hbank
    obtain ⟨pair, hpair, rfl⟩ := hbank
    rw [List.mem_toFinset, List.mem_map]
    refine ⟨pair, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨hpair, by simpa only [decide_eq_true_eq, ← hagree pair hpair] using hevent⟩
  have hlength (values : List (DigestCandidate × MessageDigest)) :
      (values.filter (fun pair => decide (event pair.2))).length =
        (values.map (fun pair => if event pair.2 then 1 else 0)).sum := by
    induction values with
    | nil => rfl
    | cons value values ih =>
        by_cases hevent : event value.2 <;> simp [hevent, ih, Nat.add_comm]
  calc
    _ ≤ (accepted.map Prod.fst).toFinset.card := Finset.card_le_card hsubset
    _ ≤ (accepted.map Prod.fst).length := List.toFinset_card_le _
    _ = traceHits (pairedWorldHit sk event) trace := by
      rw [List.length_map, traceHits_eq_freshCandidateTrace, ← hlength]

variable [Params]

/-- The same simultaneous rectangle event controls the candidate bank as interpreted from
actual final cached digests, for every supported adaptive transcript. -/
theorem traceCandidateBank_sparse_of_trace {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hpaired : PairedCache sk before)
    (result : α × List QueryRecord × QueryCache HashSpec)
    (hresult : result ∈ support (traceRun (pairedRom sk) program before))
    (hrectangles : ∀ rectangle, SmallRectangle rectangle →
      traceHits (pairedWorldHit sk (InRectangle sk.parameter rectangle)) result.2.1 < 2 ^ 56) :
    RectangleBankSparse sk.parameter (traceCandidateBank sk result.2.1)
      (fun candidate => cachedPairDigest sk candidate result.2.2) := by
  intro rectangle hsmall
  exact (traceCandidateBank_event_le sk (InRectangle sk.parameter rectangle) result.2.1 result.2.2
    (fun pair hpair => (traceRun_freshCandidates_sound sk program before hpaired result hresult pair hpair).2)).trans_lt
      (hrectangles rectangle hsmall)

/-- Actual source-query budgets give a sparse bank of latent candidates except2^-400. -/
theorem probEvent_traceCandidateBank_not_sparse {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (before : QueryCache HashSpec) (hpaired : PairedCache sk before)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' before), result.2 ≤ q) :
    Pr[fun result => ¬RectangleBankSparse sk.parameter (traceCandidateBank sk result.2.1)
        (fun candidate => cachedPairDigest sk candidate result.2.2) |
      traceRun (pairedRom sk) program before] ≤ (1 : ℝ≥0∞) / 2 ^ 400 := by
  refine le_trans ?_ (paired_trace_rectangles_negligible sk program before hpaired q hq hbound)
  apply probEvent_mono
  intro result hresult hbad
  by_contra hgood
  push Not at hgood
  exact hbad (traceCandidateBank_sparse_of_trace sk program before hpaired result hresult
    hgood)

end LeanSphincs.Lifetime
