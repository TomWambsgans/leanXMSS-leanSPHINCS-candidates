import LeanSphincs.LifetimePairedWord

/-! Retaining the actual transcript jointly with its iid padded digest word. The original
hash-query budget bounds the number of first-touch records, so padding loses no candidate. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false

private theorem uniformWord_length (n : Nat) (word : List MessageDigest)
    (hword : word ∈ support (SphincsSecurity.Concrete.sampleUniformProposalWord MessageDigest n)) : word.length = n := by
  induction n generalizing word with
  | zero =>
      simp only [SphincsSecurity.Concrete.sampleUniformProposalWord, mem_support_pure_iff] at hword
      subst word
      rfl
  | succ n ih =>
      simp only [SphincsSecurity.Concrete.sampleUniformProposalWord, mem_support_bind_iff,
        mem_support_pure_iff] at hword
      obtain ⟨head, _, rest, hrest, rfl⟩ := hword
      exact congrArg Nat.succ (ih rest hrest)

theorem padDigestWord_length (length : Nat) (values word : List MessageDigest)
    (hword : word ∈ support (padDigestWord length values)) : word.length = length := by
  induction length generalizing values word with
  | zero =>
      simp only [padDigestWord, mem_support_pure_iff] at hword
      subst word
      rfl
  | succ length ih =>
      cases values with
      | nil => exact uniformWord_length _ word hword
      | cons head rest =>
          rw [padDigestWord, support_map] at hword
          obtain ⟨tail, htail, rfl⟩ := hword
          exact congrArg Nat.succ (ih rest tail htail)

/-- If the query bound covers the observed length, every actual candidate is retained. -/
theorem padDigestWord_retains (length : Nat) (values word : List MessageDigest)
    (hlen : values.length ≤ length) (hword : word ∈ support (padDigestWord length values)) :
    ∃ padding, values ++ padding = word := by
  induction values generalizing length word with
  | nil => exact ⟨word, rfl⟩
  | cons head rest ih =>
      cases length with
      | zero => simp only [List.length_cons] at hlen; omega
      | succ length =>
          rw [padDigestWord, support_map] at hword
          obtain ⟨tail, htail, rfl⟩ := hword
          obtain ⟨padding, hpadding⟩ := ih length tail (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hlen) htail
          exact ⟨padding, by simp only [List.cons_append, hpadding]⟩

theorem freshDigestWord_length_le_cost (sk : Seeded.SecretKey) (trace : List QueryRecord) :
    (freshDigestWord sk trace).length ≤ traceCost trace := by
  have hhead (record : QueryRecord) :
      (match freshCandidateRecord sk record with | none => 0 | some _ => 1) ≤ recordCost record := by
    rcases record with ⟨input, before, answer, after⟩
    cases input with
    | inl input => exact Nat.le_refl 0
    | inr input =>
        change (match freshCandidateRecord sk ⟨.inr input, before, answer, after⟩ with
          | none => 0 | some _ => 1) ≤ 1
        cases freshCandidateRecord sk ⟨.inr input, before, answer, after⟩ <;> simp only [Nat.zero_le, le_refl]
  induction trace with
  | nil => exact Nat.le_refl 0
  | cons record trace ih =>
      have hcons : freshDigestWord sk (record :: trace) =
          match freshCandidateRecord sk record with
          | none => freshDigestWord sk trace
          | some pair => pair.2 :: freshDigestWord sk trace := by
        simp only [freshDigestWord, freshCandidateTrace, List.filterMap_cons]
        cases freshCandidateRecord sk record <;> rfl
      have hcost : traceCost (record :: trace) = recordCost record + traceCost trace := rfl
      rw [hcons, hcost]
      have hrecord := hhead record
      cases hr : freshCandidateRecord sk record with
      | none => exact ih.trans (Nat.le_add_left _ _)
      | some pair =>
          simp only [hr] at hrecord
          simp only [List.length_cons]
          omega

theorem paired_trace_source_cost_le {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q)
    (trace : α × List QueryRecord × QueryCache HashSpec)
    (htrace : trace ∈ support (traceRun (pairedRom sk) program cache)) : traceCost trace.2.1 ≤ q := by
  have hm : (trace.1, traceCost trace.2.1) ∈ support
      ((simulateQ (pairedRom sk) (countHashQueries program)).run' cache) := by
    rw [StateT.run'_eq, ← traceRun_erase, Functor.map_map, support_map]
    exact ⟨trace, htrace, rfl⟩
  exact hbound _ ((mem_support_iff_of_evalDist_eq (evalDist_pairedRom sk (countHashQueries program) cache) _).mpr hm)

noncomputable def pairedWordJoint {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (length : Nat) :
    ProbComp ((α × List QueryRecord × QueryCache HashSpec) × List MessageDigest) := do
  let trace ← traceRun (pairedRom sk) program cache
  let word ← padDigestWord length (freshDigestWord sk trace.2.1)
  pure (trace, word)

theorem pairedWordJoint_word {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (length : Nat) :
    Prod.snd <$> pairedWordJoint sk program cache length = pairedWord sk program cache length := by
  simp only [pairedWordJoint, pairedWord, map_bind, map_pure, bind_pure]

theorem evalDist_pairedWordJoint_word {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (length : Nat) :
    𝒟[Prod.snd <$> pairedWordJoint sk program cache length] =
      𝒟[SphincsSecurity.Concrete.sampleUniformProposalWord MessageDigest length] := by
  rw [pairedWordJoint_word]
  exact evalDist_pairedWord sk program cache hpaired length

theorem pairedWordJoint_support {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q)
    (result : (α × List QueryRecord × QueryCache HashSpec) × List MessageDigest)
    (hresult : result ∈ support (pairedWordJoint sk program cache q)) :
    result.1 ∈ support (traceRun (pairedRom sk) program cache) ∧ result.2.length = q ∧
      ∃ padding, freshDigestWord sk result.1.2.1 ++ padding = result.2 := by
  simp only [pairedWordJoint, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨trace, htrace, word, hword, rfl⟩ := hresult
  exact ⟨htrace, padDigestWord_length q _ word hword,
    padDigestWord_retains q _ word ((freshDigestWord_length_le_cost sk trace.2.1).trans
      (paired_trace_source_cost_le sk program cache q hbound trace htrace)) hword⟩

/-- Every candidate in the actual first-touch bank has its exact final cached digest in the
same uniform padded word. Candidate selection itself may depend on the entire transcript. -/
theorem pairedWordJoint_candidate_mem {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (q : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q)
    (result : (α × List QueryRecord × QueryCache HashSpec) × List MessageDigest)
    (hresult : result ∈ support (pairedWordJoint sk program cache q))
    (candidate : DigestCandidate) (hmem : candidate ∈ traceCandidateBank sk result.1.2.1) :
    cachedPairDigest sk candidate result.1.2.2 ∈ result.2 := by
  obtain ⟨htrace, _, padding, hpadding⟩ := pairedWordJoint_support sk program cache q hbound result hresult
  rw [← hpadding]
  apply List.mem_append_left
  rw [traceCandidateBank, List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨pair, hpair, hfst⟩ := hmem
  have hdigest := (traceRun_freshCandidates_sound sk program cache hpaired result.1 htrace pair hpair).2
  rw [freshDigestWord, List.mem_map]
  exact ⟨pair, hpair, by rw [← hdigest, hfst]⟩

end LeanSphincs.Lifetime
