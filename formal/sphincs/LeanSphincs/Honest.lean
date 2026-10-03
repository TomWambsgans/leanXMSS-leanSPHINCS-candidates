import LeanSphincs.Complete
import LeanSphincs.RandomizedSupport
import LeanSphincs.Statement

/-! End-to-end completeness of a generated key, signing, and verification in one shared ROM. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Completeness

variable [Params]

/-- The honest completeness experiment; exhaustion counts as failure. -/
noncomputable def honestExperiment (message : Message) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let some signature ← Randomized.sign sk message | return false
  liftM (Concrete.verify pk message signature : OracleComp HashSpec Bool)

attribute [local irreducible] Seeded.keygenFromSeed Randomized.sign

/-- Every failure in the actual honest sign-and-verify experiment is an exhaustion case.
All oracle freshness conditions are discharged by the key-generation proof. -/
theorem honest_completeness (message : Message) :
    Pr[fun r => r.1 = false | (simulateQ romImpl (honestExperiment message)).run ∅]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) + (2⁻¹ : ℝ≥0∞) ^ (2 ^ 22) := by
  rw [honestExperiment, simulateQ_bind, StateT.run_bind, run_lift_prob]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply probEvent_bind_le_of_forall_le
  intro seed _
  rw [simulateQ_bind, StateT.run_bind, simulate_lift_hash]
  apply probEvent_bind_le_of_forall_le
  intro key hkey
  obtain ⟨hencoding, hmessage⟩ := keygen_fresh seed key hkey
  rw [simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent (p := fun r => r.1 = none) ?_).trans
    (randomized_sign_exhaustion_bound key.1.2 message key.2 hencoding (hmessage message))
  intro signed hsigned hsome
  cases h : signed.1 with
  | none => exact False.elim (hsome h)
  | some signature =>
      rw [simulate_lift_hash]
      apply probEvent_eq_zero
      intro verified hverified hfalse
      have hsign : (some signature, signed.2) ∈ support
          ((simulateQ romImpl (Randomized.sign key.1.2 message)).run key.2) := by
        simpa only [← h] using hsigned
      have htrue := verify_of_keygen_sign_support seed key.1.1 key.1.2 message signature
        verified.1 ∅ key.2 signed.2 verified.2 hkey hsign hverified
      simp [htrue] at hfalse

/-- Uniform negligible bound for all six requested pruning heights. -/
theorem honest_completeness_negligible (hb : 10 ≤ subtreeHeight) (message : Message) :
    Pr[fun r => r.1 = false | (simulateQ romImpl (honestExperiment message)).run ∅]
      ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 := by
  refine (honest_completeness message).trans ?_
  have he : 2 ^ 15 ≤ (2 : Nat) ^ (subtreeHeight + 5) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact (add_le_add (inv_two_pow_anti he) (inv_two_pow_anti (by decide))).trans_eq
    (inv_two_pow_succ_add 32767)

/-- The sum of honest failure probabilities over the entire 256-bit message space is ≤2^-256.
This is the same all-message union-bound form used by the leanVM completeness theorem. -/
theorem honest_completeness_all_messages (hb : 10 ≤ subtreeHeight) :
    (∑' message : Message,
      Pr[fun r => r.1 = false | (simulateQ romImpl (honestExperiment message)).run ∅])
      ≤ (2⁻¹ : ℝ≥0∞) ^ 256 := by
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _message : Message, (2⁻¹ : ℝ≥0∞) ^ 512 := by
      apply Finset.sum_le_sum
      intro message _
      exact (honest_completeness_negligible hb message).trans (inv_two_pow_anti (by decide))
    _ = (2 : ℝ≥0∞) ^ 256 * (2⁻¹ : ℝ≥0∞) ^ 512 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        show Fintype.card Message = 2 ^ 256 by simp [messageBits], Nat.cast_pow, Nat.cast_ofNat]
    _ = (2⁻¹ : ℝ≥0∞) ^ 256 := by
      rw [← ENNReal.inv_pow, ← div_eq_mul_inv]
      exact two_pow_div_two_pow 256 256

end LeanSphincs.Completeness

namespace LeanSphincs.Lifetimes

open Completeness

/-- All requested parameter instances meet the concrete honest completeness bound. -/
theorem requested_completeness (message : Message) :
    Pr[fun r => r.1 = false | (simulateQ romImpl (@honestExperiment full message)).run ∅]
        ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 ∧
    Pr[fun r => r.1 = false | (simulateQ romImpl (@honestExperiment pruned20 message)).run ∅]
        ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 ∧
    Pr[fun r => r.1 = false | (simulateQ romImpl (@honestExperiment pruned13 message)).run ∅]
        ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 ∧
    Pr[fun r => r.1 = false | (simulateQ romImpl (@honestExperiment pruned14 message)).run ∅]
        ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 ∧
    Pr[fun r => r.1 = false | (simulateQ romImpl (@honestExperiment pruned12 message)).run ∅]
        ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 ∧
    Pr[fun r => r.1 = false | (simulateQ romImpl (@honestExperiment pruned10 message)).run ∅]
        ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 :=
  ⟨@honest_completeness_negligible full (by decide) message,
   @honest_completeness_negligible pruned20 (by decide) message,
   @honest_completeness_negligible pruned13 (by decide) message,
   @honest_completeness_negligible pruned14 (by decide) message,
   @honest_completeness_negligible pruned12 (by decide) message,
   @honest_completeness_negligible pruned10 (by decide) message⟩

end LeanSphincs.Lifetimes
