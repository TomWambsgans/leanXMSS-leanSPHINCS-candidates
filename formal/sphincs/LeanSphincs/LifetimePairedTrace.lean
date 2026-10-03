import LeanSphincs.LifetimePairedCharge
import LeanSphincs.SecurityExponentialTrace

/-! Simultaneous candidate-event control on one shared paired-oracle execution trace. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem paired_trace_tail {α : Type} (sk : Seeded.SecretKey)
    (event : MessageDigest → Prop) (offset : Nat) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (q threshold : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q) :
    Pr[fun result => threshold ≤ traceHits (pairedWorldHit sk event) result.2.1 |
      traceRun (pairedRom sk) program cache] ≤
        (1 + (offset : ℝ≥0∞) * Pr[event | ($ᵗ MessageDigest : ProbComp MessageDigest)]) ^ q /
          ((offset + 1 : Nat) : ℝ≥0∞) ^ threshold := by
  have h := paired_monitor_tail sk event offset program cache hpaired q threshold hbound
  rw [run_eq_trace_map, probEvent_map] at h
  exact h

/-- One transcript law supports the finite-class union. The events may later be selected
adaptively from the transcript because every member of the class is controlled at once. -/
theorem paired_trace_family_tail {α κ : Type} (sk : Seeded.SecretKey)
    (family : Finset κ) (event : κ → MessageDigest → Prop) (rate : ℝ≥0∞)
    (hprice : ∀ key ∈ family, Pr[event key | ($ᵗ MessageDigest : ProbComp MessageDigest)] ≤ rate)
    (offset : Nat) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (q threshold : Nat)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q) :
    Pr[fun result => ∃ key ∈ family,
        threshold ≤ traceHits (pairedWorldHit sk (event key)) result.2.1 |
      traceRun (pairedRom sk) program cache] ≤
        (family.card : ℝ≥0∞) * ((1 + (offset : ℝ≥0∞) * rate) ^ q /
          ((offset + 1 : Nat) : ℝ≥0∞) ^ threshold) := by
  have h := probEvent_exists_finset_le_sum family (traceRun (pairedRom sk) program cache)
    (fun key result => threshold ≤ traceHits (pairedWorldHit sk (event key)) result.2.1)
  refine h.trans ?_
  calc
    _ ≤ ∑ _key ∈ family, (1 + (offset : ℝ≥0∞) * rate) ^ q /
        ((offset + 1 : Nat) : ℝ≥0∞) ^ threshold := by
      apply Finset.sum_le_sum
      intro key hkey
      refine (paired_trace_tail sk (event key) offset program cache hpaired q threshold hbound).trans ?_
      gcongr
      exact hprice key hkey
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A new candidate and its full latent digest, extracted from one source-level query record. -/
noncomputable def freshCandidateRecord (sk : Seeded.SecretKey) (record : QueryRecord) :
    Option (DigestCandidate × MessageDigest) := by
  classical
  exact match record.1 with
  | .inl _ => none
  | .inr input => match decodeCandidateInput sk input with
    | none => none
    | some position => if record.2.1 (candidateInput sk position.1 position.2) = none then
        some (position.1, cachedPairDigest sk position.1 record.2.2.2) else none

noncomputable def freshCandidateTrace (sk : Seeded.SecretKey) (trace : List QueryRecord) :
    List (DigestCandidate × MessageDigest) := trace.filterMap (freshCandidateRecord sk)

/-- The exponential monitor counts exactly the recorded newly touched latent digests. -/
theorem recordHit_eq_freshCandidateRecord (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (record : QueryRecord) :
    recordHit (pairedWorldHit sk event) record =
      match freshCandidateRecord sk record with
      | none => 0
      | some pair => if event pair.2 then 1 else 0 := by
  classical
  rcases record with ⟨input, before, answer, after⟩
  cases input with
  | inl input => rfl
  | inr input =>
      cases hp : decodeCandidateInput sk input with
      | none =>
          simp only [recordHit, pairedWorldHit, freshCandidateRecord, hp, pairedHit,
            reduceCtorEq, false_and, exists_false, decide_false, Bool.false_eq_true, if_false]
      | some position =>
          have hinput := decodeCandidateInput_some sk input position hp
          subst input
          simp only [recordHit, pairedWorldHit, freshCandidateRecord, decodeCandidateInput_self,
            decide_eq_true_eq, pairedHit_candidate]
          by_cases hfresh : before (candidateInput sk position.1 position.2) = none
          · simp only [hfresh, true_and, if_true]
          · simp only [hfresh, false_and, if_false]

theorem traceHits_eq_freshCandidateTrace (sk : Seeded.SecretKey) (event : MessageDigest → Prop)
    (trace : List QueryRecord) :
    traceHits (pairedWorldHit sk event) trace =
      ((freshCandidateTrace sk trace).map (fun pair => if event pair.2 then 1 else 0)).sum := by
  classical
  induction trace with
  | nil => rfl
  | cons record trace ih =>
      simp only [traceHits, List.map_cons, List.sum_cons, recordHit_eq_freshCandidateRecord,
        freshCandidateTrace, List.filterMap_cons] at *
      cases hrecord : freshCandidateRecord sk record <;> simp [hrecord, ih]

end LeanSphincs.Lifetime
