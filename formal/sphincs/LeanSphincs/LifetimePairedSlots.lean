import LeanSphincs.LifetimePairedWordSupport

/-! Distinct candidate labels embed into distinct positions of the common iid digest word.
The statement allows hash collisions: different slots may contain equal digest values. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false

/-- A slot remembers both its candidate label and exact final cached digest. -/
theorem pairedWordJoint_candidate_slot {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q)
    (result : (α × List QueryRecord × QueryCache HashSpec) × List MessageDigest)
    (hresult : result ∈ support (pairedWordJoint sk program cache q))
    (candidate : DigestCandidate) (hmem : candidate ∈ traceCandidateBank sk result.1.2.1) :
    ∃ slot : Fin q,
      (freshCandidateTrace sk result.1.2.1)[slot.val]? =
        some (candidate, cachedPairDigest sk candidate result.1.2.2) ∧
      result.2[slot.val]? = some (cachedPairDigest sk candidate result.1.2.2) := by
  obtain ⟨htrace, hlength, padding, hpadding⟩ := pairedWordJoint_support sk program cache q hbound result hresult
  rw [traceCandidateBank, List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨pair, hpair, hfst⟩ := hmem
  have hdigest := (traceRun_freshCandidates_sound sk program cache hpaired result.1 htrace pair hpair).2
  obtain ⟨slot, hslot, hget⟩ := List.mem_iff_getElem.mp hpair
  have hslotWord : slot < (freshDigestWord sk result.1.2.1).length := by
    simpa only [freshDigestWord, List.length_map] using hslot
  have hslotq : slot < q := by
    have hle := (freshDigestWord_length_le_cost sk result.1.2.1).trans
      (paired_trace_source_cost_le sk program cache q hbound result.1 htrace)
    omega
  refine ⟨⟨slot, hslotq⟩, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem hslot, hget]
    apply congrArg some
    apply Prod.ext
    · exact hfst
    · simpa only [hfst] using hdigest.symm
  · rw [← hpadding, List.getElem?_append_left hslotWord, freshDigestWord,
      List.getElem?_map, List.getElem?_eq_getElem hslot, hget, Option.map_some]
    exact congrArg some (by simpa only [hfst] using hdigest.symm)

/-- All target/exceptional-source candidates can be assigned slots simultaneously. An
injective choice of labels is therefore also an injective choice of iid word coordinates. -/
theorem pairedWordJoint_candidate_embedding {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q)
    (result : (α × List QueryRecord × QueryCache HashSpec) × List MessageDigest)
    (hresult : result ∈ support (pairedWordJoint sk program cache q)) :
    ∃ slots : {candidate // candidate ∈ traceCandidateBank sk result.1.2.1} ↪ Fin q,
      ∀ candidate, result.2[(slots candidate).val]? =
        some (cachedPairDigest sk candidate.val result.1.2.2) := by
  classical
  have hexists (candidate : {candidate // candidate ∈ traceCandidateBank sk result.1.2.1}) :=
    pairedWordJoint_candidate_slot sk program cache hpaired q hbound result hresult candidate.val candidate.property
  let slot (candidate : {candidate // candidate ∈ traceCandidateBank sk result.1.2.1}) : Fin q :=
    Classical.choose (hexists candidate)
  have hslot (candidate) := Classical.choose_spec (hexists candidate)
  have hinjective : Function.Injective slot := by
    intro left right heq
    have hleft := (hslot left).1
    have hright := (hslot right).1
    change (freshCandidateTrace sk result.1.2.1)[(slot left).val]? = _ at hleft
    change (freshCandidateTrace sk result.1.2.1)[(slot right).val]? = _ at hright
    rw [heq, hright] at hleft
    apply Subtype.ext
    exact (congrArg Prod.fst (Option.some.inj hleft)).symm
  exact ⟨⟨slot, hinjective⟩, fun candidate => (hslot candidate).2⟩

end LeanSphincs.Lifetime
